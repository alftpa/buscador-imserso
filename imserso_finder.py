#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Buscador de viajes IMSERSO (turismosocial.es + mundicolor.es).

Busca por HOTEL o por LOCALIDAD y muestra desde qué ORÍGENES (ciudades de
salida) se ofrece, con fechas, estado (disponible / lista de espera), precio
y ficha del hotel.

Solo usa la librería estándar de Python 3 (sin pip). Arranca un pequeño
servidor local y abre el navegador.  Uso por terminal: --help
"""
import concurrent.futures as cf
import difflib
import http.cookiejar
import http.server
import json
import os
import re
import socket
import sys
import threading
import time
import unicodedata
import urllib.error
import urllib.request
import uuid
import webbrowser
from html import unescape

PRODUCT_TYPES = ["CIRCUITOS", "COSTAS", "ISLAS"]
STAYS = {"S4": "4 días", "S5": "5 días", "S6": "6 días", "S8": "8 días",
         "S10": "10 días", "S15": "15 días", "PACKAGE": "Combinado (15 días)"}
SUBTYPES = {"CC": "Circuito cultural", "ISL": "Islas", "COS": "Costa", "CN": "Turismo de naturaleza",
            "CP": "Capital de provincia", "CA": "Ciudad autónoma"}
SIN_TRANSPORTE = "SIN TRANSPORTE"
CACHE_DIR = os.path.join(os.path.expanduser("~"), "Library", "Application Support", "ImsersoFinder")
INDEX_TTL = 7 * 24 * 3600      # catálogo de hoteles
CONFIG_TTL = 24 * 3600         # opciones por origen
RESULT_TTL = 2 * 86400          # calendarios y búsquedas de fechas
WORKERS = int(os.environ.get("WORKERS", 3))          # hilos simultáneos contra la web
MIN_GAP = float(os.environ.get("MIN_GAP", 0.35))     # segundos mínimos entre peticiones a la misma web
WAF_WAIT = int(os.environ.get("WAF_WAIT", 0))        # >0: ante bloqueo, esperar y reintentar (scrapeo programado)


def origin_match(filt, name):
    """'CASTELLON' y 'CASTELLON DE LA PLANA' son el mismo origen en las dos webs."""
    a, b = norm(filt), norm(name)
    return a in b or b in a


class WafBlocked(Exception):
    """La web ha activado la verificación anti-robots (AWS WAF)."""


def norm(s):
    s = unicodedata.normalize("NFKD", s or "")
    s = "".join(c for c in s if not unicodedata.combining(c))
    return re.sub(r"\s+", " ", s).strip().upper()


def strip_tags(h):
    h = re.sub(r"<script.*?</script>", "", h, flags=re.S)
    h = re.sub(r"<[^>]+>", " ", h)
    return re.sub(r"\s+", " ", unescape(h)).strip()


def log(*a):
    print(time.strftime("%H:%M:%S"), *a, flush=True)


def _status(td):
    m = re.search(r'id="product-list-item-\d+"[^>]*>(.*?)</span>', td, re.S)
    return strip_tags(m.group(1)) if m else strip_tags(td).split("Número")[0].strip()


MESES = {"ENERO": 1, "FEBRERO": 2, "MARZO": 3, "ABRIL": 4, "MAYO": 5, "JUNIO": 6, "JULIO": 7, "AGOSTO": 8,
         "SEPTIEMBRE": 9, "OCTUBRE": 10, "NOVIEMBRE": 11, "DICIEMBRE": 12}


def parse_days(html):
    """Días con estado (disponible / lista-espera / completo); los deshabilitados no se listan."""
    return [(d, cls) for cls, d in re.findall(
        r'<td class="day (completo|disponible|lista-espera)"[^>]*>.*?calendar-tooltip-(\d{4}-\d{2}-\d{2})', html, re.S)]


def load_json(path, ttl):
    try:
        with open(path, encoding="utf-8") as f:
            d = json.load(f)
        if time.time() - d.get("ts", 0) < ttl:
            return d["data"]
    except Exception:
        pass
    return None


def save_json(path, data):
    os.makedirs(CACHE_DIR, exist_ok=True)
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump({"ts": time.time(), "data": data}, f, ensure_ascii=False)
    os.replace(tmp, path)


# --------------------------------------------------------------------------- #
#  Cliente de un sitio (turismosocial / mundicolor)
# --------------------------------------------------------------------------- #
class Site:
    def __init__(self, key, host, label):
        self.key = key
        self.host = host
        self.label = label
        self.base = "https://" + host
        self.jar = http.cookiejar.CookieJar()
        self.opener = urllib.request.build_opener(urllib.request.HTTPCookieProcessor(self.jar))
        self.opener.addheaders = [
            ("User-Agent", "Mozilla/5.0 (Macintosh; Intel Mac OS X 14_0) AppleWebKit/537.36 (KHTML, like Gecko) Safari/537.36"),
            ("Referer", self.base + "/scheduler"),
            ("Accept-Language", "es-ES,es;q=0.9"),
        ]
        self.lock = threading.Lock()
        self.rate_lock = threading.Lock()
        self.last_req = 0.0
        self.origins = []          # [(code, name)]
        self.origin_by_norm = {}   # norm(name) -> code
        self.towns = {}            # town_code -> dict
        self.town_codes_by_norm = {}
        self.config_path = os.path.join(CACHE_DIR, f"config_{key}.json")
        self._config_cache = load_json(self.config_path, CONFIG_TTL) or {}
        self.result_path = os.path.join(CACHE_DIR, f"resultados_{key}.json")
        self._result_cache = load_json(self.result_path, 10 ** 9) or {}   # cada entrada lleva su propia fecha
        self._dirty = False
        self._hotel_cache = {}
        self.loaded = False

    # -- http --------------------------------------------------------------
    def _pace(self):
        with self.rate_lock:
            wait = self.last_req + MIN_GAP - time.time()
            if wait > 0:
                time.sleep(wait)
            self.last_req = time.time()

    def _check_waf(self, html):
        if "Human Verification" in html or "awswaf" in html:
            raise WafBlocked(
                f"{self.host} ha activado la verificación anti-robots para este ordenador "
                "(demasiadas consultas seguidas). Espera 15-30 minutos y vuelve a intentarlo.")

    def _get(self, path):
        self._pace()
        try:
            with self.opener.open(self.base + path, timeout=60) as r:
                html = r.read().decode("utf-8", "ignore")
        except urllib.error.HTTPError as e:
            if e.code == 405:
                raise WafBlocked(f"{self.host} ha bloqueado temporalmente las consultas (405). Espera 15-30 minutos.")
            raise
        self._check_waf(html)
        return html

    def _post_json(self, path, payload, retries=4):
        waits = 0
        while True:
            try:
                return self._post_json_once(path, payload, retries)
            except WafBlocked:
                if not WAF_WAIT or waits >= 8:
                    raise
                waits += 1
                log(f"bloqueo anti-robots en {self.host}: espero {WAF_WAIT // 60} min (intento {waits})")
                time.sleep(WAF_WAIT)

    def _post_json_once(self, path, payload, retries=4):
        data = json.dumps(payload, ensure_ascii=False).encode("utf-8")
        for attempt in range(retries + 1):
            self._pace()
            try:
                req = urllib.request.Request(
                    self.base + "/" + path, data=data,
                    headers={"Content-Type": "application/json", "X-Requested-With": "XMLHttpRequest"})
                with self.opener.open(req, timeout=90) as r:
                    html = r.read().decode("utf-8", "ignore")
                self._check_waf(html)
                if "Error en el proceso" in html and attempt < retries:
                    raise RuntimeError("error de la web")
                return html
            except urllib.error.HTTPError as e:
                if e.code == 405:
                    raise WafBlocked(f"{self.host} ha bloqueado temporalmente las consultas (405). Espera 15-30 minutos.")
                if attempt == retries:
                    raise
                time.sleep(2 * (attempt + 1))
            except WafBlocked:
                raise
            except Exception:
                if attempt == retries:
                    raise
                time.sleep(2 * (attempt + 1))

    # -- carga inicial -----------------------------------------------------
    def load(self):
        if self.loaded:
            return
        with self.lock:
            if self.loaded:
                return
            html = self._get("/scheduler")
            m = re.search(r'<select[^>]*id="origin-scheduler"[^>]*>(.*?)</select>', html, re.S)
            for code, name in re.findall(r'<option[^>]*value="([^"]*)"[^>]*>([^<]*)', m.group(1)):
                if code and code != "-":
                    name = unescape(name.strip())
                    self.origins.append((code, name))
                    self.origin_by_norm.setdefault(norm(name), code)
            m = re.search(r"destinations\s*:\s*(\[.*?\])\s*,?\s*\n\s*\}\);", html, re.S)
            for d in json.loads(m.group(1)):
                for p in d["provinces"]:
                    for t in p["towns"]:
                        self.towns[t["code"]] = dict(
                            code=t["code"], name=t["name"], province=p["code"], provinceName=p["name"],
                            destination=d["code"], destinationName=d["name"],
                            subType=t.get("productSubType") or d["productSubType"])
                        self.town_codes_by_norm.setdefault(norm(t["name"]), []).append(t["code"])
            self.loaded = True
            log(self.key, "cargado:", len(self.origins), "orígenes,", len(self.towns), "localidades")

    # -- API ---------------------------------------------------------------
    def config(self, origin, force=False):
        """Opciones (destino/provincia/localidad/estancia) para un origen (None = sin transporte). Caché 24 h."""
        key = origin or "_"
        hit = self._config_cache.get(key)
        if hit is not None and not force:
            return hit
        payload = {"criteria": {"productTypes": PRODUCT_TYPES, "origin": origin,
                                "transportIncluded": origin is not None, "petsAllowed": None}}
        opts = json.loads(self._post_json("api-product-searcher-config", payload)).get("productOptions") or []
        with self.lock:
            self._config_cache[key] = opts
            save_json(self.config_path, self._config_cache)
        return opts

    def _criteria(self, origin, town=None, destination=None, sub_type=None, province=None, stay=None):
        c = {"paxes": [{"documentNumber": 1}], "origin": origin, "transportIncluded": origin is not None,
             "productTypes": PRODUCT_TYPES, "petsAllowed": None, "stay": stay}
        if town:
            t = self.towns[town]
            c.update(town=town, province=t["province"], destination=t["destination"], productSubType=t["subType"])
        elif province and not destination:
            t = self.province_info(province)
            c.update(province=province, destination=t["destination"], productSubType=t["subType"])
        else:
            c.update(destination=destination, productSubType=sub_type, province=province)
        return c

    def _cached(self, key, fn, force=False):
        ent = self._result_cache.get(key)
        if ent and not force and time.time() - ent["ts"] < RESULT_TTL:
            return ent["v"]
        v = fn()
        with self.lock:
            self._result_cache[key] = {"ts": time.time(), "v": v}
            self._dirty = True
        return v

    def flush(self):
        if self._dirty:
            with self.lock:
                cutoff = time.time() - RESULT_TTL
                self._result_cache = {k: e for k, e in self._result_cache.items() if e["ts"] > cutoff}
                save_json(self.result_path, self._result_cache)
                self._dirty = False

    def calendar_days(self, force=False, **kw):
        """(celdas, completos, días): celdas = [(estado, fecha, [códigos])]; días = [(fecha, estado)] incluidos completos."""
        crit = self._criteria(**kw)
        key = "cal:" + json.dumps(crit, sort_keys=True, ensure_ascii=False)

        def fetch():
            html = self._post_json("api-scheduler-calendar", {"searcherCriteria": crit})
            cells = [(st, d, [c for c in codes.split(";") if c]) for st, d, codes in
                     re.findall(r'<td class="day ([\w-]+)" data-date="([^"]+)" data-codes="([^"]*)"', html)]
            return [cells, len(re.findall(r'<td class="day completo"', html)), parse_days(html)]

        cells, completos, days = self._cached(key, fetch, force)
        return [tuple(c) for c in cells], completos, [tuple(d) for d in days]

    def calendar(self, **kw):
        cells, completos, _ = self.calendar_days(**kw)
        return cells, completos

    @staticmethod
    def _products_json(html):
        """Array JSON de productos que la web incrusta en Imserso.Avail.init(cfg, [...])."""
        i = html.find("Imserso.Avail.init(")
        if i < 0:
            return None
        seg = html[i:]
        m = re.search(r"\},\s*\[", seg)
        if not m:
            return None
        k = m.end() - 1
        depth, instr, esc_ = 0, False, False
        for idx in range(k, len(seg)):
            ch = seg[idx]
            if instr:
                if esc_:
                    esc_ = False
                elif ch == "\\":
                    esc_ = True
                elif ch == '"':
                    instr = False
                continue
            if ch == '"':
                instr = True
            elif ch == "[":
                depth += 1
            elif ch == "]":
                depth -= 1
                if depth == 0:
                    try:
                        return json.loads(seg[k:idx + 1])
                    except Exception:
                        return None
        return None

    def search(self, date, codes, force=False, **kw):
        """Viajes concretos para una fecha (uno por producto; un circuito puede tener varios hoteles). Caché 6 h."""
        c = self._criteria(**kw)
        c.update(startDate=date, productCodes=sorted(codes))
        key = "srch:" + json.dumps(c, sort_keys=True, ensure_ascii=False)
        return self._cached(key, lambda: self._search_live(c, date), force)

    def _search_live(self, c, date):
        html = self._post_json("api-scheduler-search", {"searcherCriteria": c})
        arr = self._products_json(html)
        if arr is None:
            return self._search_html(html, date)
        rows = []
        for p in arr:
            st = {"CONFIRMED": "Disponible", "WAITINGLIST": "Lista de espera", "COMPLETE": "Completo"}.get(p.get("status"), p.get("status") or "")
            hour = ""
            for sh in p.get("shuttles") or []:
                d = (sh.get("routeOrigin") or {}).get("date")
                if sh.get("departure") and d:
                    hour = d[11:16]
                    break
            tr = {"BUS": "Bus", "TRAIN": "Tren", "PLANE": "Avión", "FLIGHT": "Avión", "SHIP": "Barco"}.get(p.get("transportType")) or (p.get("transportType") or ("Bus" if p.get("withTransport") else ""))
            hotels = [dict(name=h.get("name") or "", code=str(h.get("code")) if h.get("code") else None, category=h.get("category") or "",
                           town=h.get("townName") or "", meal=h.get("mealPlan") or "") for h in (p.get("hotels") or [])]
            price = p.get("totalPrice")
            town = p.get("town") or {}
            rows.append(dict(
                site=self.key, date=p.get("startDate") or date, endDate=p.get("endDate") or "", status=st,
                waiting=p.get("waitingListSize"), town=town.get("name") or (hotels[0]["town"] if hotels else ""),
                townCode=town.get("code"), stay=p.get("stay"), days=STAYS.get(p.get("stay"), p.get("stay") or ""),
                hour=hour, transport=tr if p.get("withTransport") else "", hotel=" + ".join(h["name"] for h in hotels),
                hotelCode=hotels[0]["code"] if hotels else None, hotels=hotels, zone=(p.get("province") or {}).get("code"),
                pets="Sí" if p.get("petsAllowed") else "No", price=f"{price:.2f} €".replace(".", ",") if isinstance(price, (int, float)) else "",
                priceNum=price if isinstance(price, (int, float)) else None, subType=p.get("productSubType"), productCode=p.get("code")))
        return rows

    def _search_html(self, html, date):
        """Respaldo: parseo de la tabla HTML (formato de costas)."""
        rows = []
        m = re.search(r"<table.*?</table>", html, re.S)
        if not m:
            return rows
        for tr in re.findall(r"<tr.*?</tr>", m.group(0), re.S):
            tds = re.findall(r"<td[^>]*>(.*?)</td>", tr, re.S)
            if len(tds) < 9:
                continue
            hm = re.search(r'data-hotel-code="([^"]*)"', tds[5])
            zm = re.search(r'data-zone-code="([^"]*)"', tds[6])
            wl = re.search(r"lista de espera:\s*(\d+)", tds[0])
            name = strip_tags(tds[5])
            rows.append(dict(
                site=self.key, date=date, endDate="", status=_status(tds[0]), waiting=int(wl.group(1)) if wl else None,
                town=strip_tags(tds[1]), townCode=None, stay=None, days=strip_tags(tds[2]), hour=strip_tags(tds[3]),
                transport=strip_tags(tds[4]), hotel=name, hotelCode=hm.group(1) if hm else None,
                hotels=[dict(name=name, code=hm.group(1) if hm else None, category="", town=strip_tags(tds[1]), meal="")],
                zone=zm.group(1) if zm else None, pets=strip_tags(tds[7]), price=strip_tags(tds[8]), priceNum=None, subType=None, productCode=None))
        return rows

    def hotel_info(self, code):
        """Ficha del hotel: nombre, fotos, datos, servicios, mapa."""
        if code in self._hotel_cache:
            return self._hotel_cache[code]
        html = self._post_json("api/hotel-info", int(code))
        if "redirectErrorForm" in html or "Error en el proceso" in html:
            raise RuntimeError("La web no devuelve la ficha de este hotel.")
        title = re.search(r'id="myModalHotelCard-title"[^>]*>(.*?)</div>', html, re.S)
        images = re.findall(r'<img[^>]*alt="Imagen del hotel"[^>]*src="([^"]+)"', html)
        paras, maps = [], None
        i = html.find('<div class="col-md-8">')
        if i >= 0:
            block = html[i + 22:]
            for stop in ('<div class="tab-pane"', "<script"):
                j = block.find(stop)
                if j >= 0:
                    block = block[:j]
            im = re.search(r'<iframe[^>]*src="([^"]+)"', block)
            if im:
                maps = unescape(im.group(1))
            block = re.sub(r"<iframe.*?</iframe>", "", block, flags=re.S)
            block = re.sub(r'<span class="sr-only">.*?</span>', "", block, flags=re.S)
            for piece in re.split(r"</?p>", block):
                piece = re.sub(r'<a\s[^>]*href="([^"]+)"[^>]*>', r'<a href="\1" target="_blank" rel="noopener">', piece)
                piece = re.sub(r"<(?!/?(b|a|br|i|strong|em)\b)[^>]+>", "", piece)   # solo etiquetas inofensivas
                piece = re.sub(r"\s+", " ", piece).strip()
                if strip_tags(piece):
                    paras.append(piece)
        fac = re.search(r'id="facilities">(.*?)</div>', html, re.S)
        services = [strip_tags(s) for s in re.findall(r"<li>\s*(.*?)\s*</li>", fac.group(1), re.S)] if fac else []
        name = strip_tags(re.sub(r"</?c:[^>]*>", "", title.group(1))) if title else ""
        info = dict(name=name, images=[unescape(i) for i in images], paras=paras, services=services, maps=maps,
                    site=self.key, host=self.host)
        self._hotel_cache[code] = info
        return info

    # -- utilidades --------------------------------------------------------
    def origin_name(self, code):
        if code is None:
            return SIN_TRANSPORTE
        for c, n in self.origins:
            if c == code:
                return n
        return code

    def province_info(self, province_code):
        for t in self.towns.values():
            if t["province"] == province_code:
                return t
        raise KeyError(province_code)

    def place(self, code):
        """Datos de un lugar: código de localidad, 'P:<provincia>' o 'D:<destino>'."""
        if code.startswith("D:"):
            t = next(t for t in self.towns.values() if t["destination"] == code[2:])
            return dict(code=code, name=t["destinationName"] + " (zona)", province=None, provinceName="",
                        destination=t["destination"], destinationName=t["destinationName"], subType=t["subType"])
        if code.startswith("P:"):
            t = self.province_info(code[2:])
            return dict(code=code, name=t["provinceName"] + " (provincia)", province=t["province"], provinceName=t["provinceName"],
                        destination=t["destination"], destinationName=t["destinationName"], subType=t["subType"])
        return self.towns[code]


SITES = {"turismosocial": Site("turismosocial", "www.turismosocial.es", "Turismo Social (península)"),
         "mundicolor": Site("mundicolor", "www.mundicolor.es", "Mundicolor (Baleares y Canarias)")}


# --------------------------------------------------------------------------- #
#  Catálogo de hoteles (hotel -> localidades) — se construye una vez y se cachea
# --------------------------------------------------------------------------- #
class HotelIndex:
    def __init__(self):
        self.path = os.path.join(CACHE_DIR, "hoteles.json")
        self.data = load_json(self.path, INDEX_TTL)   # {site: {hotel: {"towns": {code: name}, "code": hotelCode}}}
        if self.data is None:   # arranque en limpio (p. ej. Render): catálogo incluido en el repo
            seed = load_json(os.path.join(os.path.dirname(os.path.abspath(__file__)), "seed_hoteles.json"), 10 ** 10)
            self.data = seed
        self.lock = threading.Lock()
        if self.data:
            log("catálogo de hoteles cargado de caché:", sum(len(v) for v in self.data.values()), "hoteles")

    def ready(self):
        return self.data is not None

    def build(self, progress=lambda *a: None, force=False):
        with self.lock:
            if self.data is not None and not force:
                return self.data
            hotels = {k: dict(v) for k, v in (self.data or {}).items()}
            for site in SITES.values():
                site.load()
                hotels.setdefault(site.key, {})
                origins = [None]   # sin transporte + orígenes grandes cubren el catálogo entero
                for name in ("MADRID", "BARCELONA", "VALENCIA", "SEVILLA"):
                    code = site.origin_by_norm.get(name)
                    if code:
                        origins.append(code)
                jobs = []
                for o in origins:
                    dests = {}
                    for opt in site.config(o):
                        dests[(opt["destinationCode"], opt["productSubType"])] = True
                    jobs += [(o, d, st) for (d, st) in dests]
                progress(f"{site.host}: leyendo calendarios ({len(jobs)} destinos)")
                done = [0]

                def do_job(job):
                    o, d, st = job
                    try:
                        cells, _ = site.calendar(origin=o, destination=d, sub_type=st)
                    except WafBlocked:
                        raise
                    except Exception as e:  # noqa
                        log("catálogo: calendario falló", site.key, job, e)
                        cells = []
                    seen, picks = set(), []   # mínimo de fechas que cubren todos los productos
                    for status, date, codes in sorted(cells, key=lambda c: -len(c[2])):
                        new = [c for c in codes if c not in seen]
                        if new:
                            picks.append((date, codes))
                            seen.update(new)
                    found = []
                    for date, codes in picks:
                        try:
                            for r in site.search(date, codes, origin=o, destination=d, sub_type=st):
                                r["subType"], r["dest"] = st, d
                                found.append(r)
                        except WafBlocked:
                            raise
                        except Exception as e:  # noqa
                            log("catálogo: búsqueda falló", site.key, job, date, e)
                    done[0] += 1
                    progress(f"{site.host}: {done[0]}/{len(jobs)} destinos leídos")
                    return found

                with cf.ThreadPoolExecutor(WORKERS) as ex:
                    for rows in ex.map(do_job, jobs):
                        self._merge(site, hotels[site.key], rows)
            self.data = hotels
            save_json(self.path, hotels)
            log("catálogo construido:", {k: len(v) for k, v in hotels.items()})
            return hotels

    @staticmethod
    def _merge(site, hs, rows):
        for r in rows:
            for hh in (r.get("hotels") or ([dict(name=r["hotel"], code=r.get("hotelCode"))] if r.get("hotel") else [])):
                if not hh.get("name"):
                    continue
                h = hs.setdefault(hh["name"], {"towns": {}, "code": hh.get("code")})
                h["code"] = h.get("code") or hh.get("code")
                if r.get("townCode") and r["townCode"] in site.towns:
                    h["towns"][r["townCode"]] = r["town"]
                    continue
                HotelIndex._merge_by_name(site, h, r)

    @staticmethod
    def _merge_by_name(site, h, r):
        if True:
            cands = site.town_codes_by_norm.get(norm(r["town"]), [])
            if not cands and r.get("dest"):   # erratas en la web ("GUADAJAJARA")
                pool = {norm(t["name"]): tc for tc, t in site.towns.items() if t["destination"] == r["dest"]}
                close = difflib.get_close_matches(norm(r["town"]), list(pool), n=1, cutoff=0.75)
                cands = [pool[close[0]]] if close else []
            if r.get("zone"):
                cands = [tc for tc in cands if site.towns[tc]["province"] == r["zone"]] or cands
            if r.get("subType"):
                cands = [tc for tc in cands if site.towns[tc]["subType"] == r["subType"]] or cands
            if cands:
                h["towns"][cands[0]] = r["town"]
            elif r.get("zone"):
                h["towns"]["P:" + r["zone"]] = r["town"]
            elif r.get("dest"):
                h["towns"]["D:" + r["dest"]] = r["town"]

    def learn(self, site, rows, place=None):
        """Aprende hoteles nuevos de cualquier búsqueda normal."""
        if self.data is None or not rows:
            return
        with self.lock:
            hs = self.data.setdefault(site.key, {})
            before = len(hs)
            rows = [dict(r, subType=(site.place(place)["subType"] if place else None)) for r in rows]
            self._merge(site, hs, rows)
            if len(hs) != before:
                save_json(self.path, self.data)
                log("catálogo: aprendidos", len(hs) - before, "hoteles nuevos en", site.key)

    def catalog(self):
        """Listas para los desplegables."""
        hotels, towns = [], {}
        for sk, hs in (self.data or {}).items():
            s = SITES[sk]
            if not s.loaded:
                continue
            for name, info in sorted(hs.items()):
                tl = []
                for tc in info["towns"]:
                    p = s.place(tc)
                    entry = dict(site=sk, code=tc, name=p["name"], province=p["provinceName"],
                                 zone=p["destinationName"], subType=SUBTYPES.get(p["subType"], p["subType"]))
                    tl.append(entry)
                    towns[(sk, tc)] = entry
                hotels.append(dict(site=sk, name=name, code=info.get("code"), towns=tl))
        towns = sorted(towns.values(), key=lambda t: (norm(t["name"]), t["site"]))
        return hotels, towns


INDEX = HotelIndex()
WARM = {"done": False, "error": None}


def warm_configs():
    """Lee (o recupera de caché) las opciones de todos los orígenes de las dos webs."""
    try:
        for site in SITES.values():
            site.load()
            with cf.ThreadPoolExecutor(WORKERS) as ex:
                list(ex.map(site.config, [None] + [c for c, _ in site.origins]))
    except Exception as e:  # noqa
        WARM["error"] = str(e)
        log("warm error", e)
    WARM["done"] = True
    log("opciones de todos los orígenes listas")


PRE = {"data": {}, "ts": 0, "running": False, "done": 0, "total": 0}
PRE_PATH = os.path.join(CACHE_DIR, "disponibilidad.json")
PRE_TTL = 2 * 86400


def _estado_of(site, origin, code, stay=None, force=False):
    if code.startswith("D:"):
        kw = dict(destination=code[2:], sub_type=site.place(code)["subType"])
    elif code.startswith("P:"):
        kw = dict(province=code[2:])
    else:
        kw = dict(town=code)
    cells, completos = site.calendar(origin=origin, stay=stay, force=force, **kw)
    disp = sorted(c[1] for c in cells if c[0] == "disponible")
    wl = sorted(c[1] for c in cells if c[0] != "disponible")
    return dict(fechas=len(cells), disponibles=len(disp), espera=len(wl), completos=completos,
                primera=min((c[1] for c in cells), default=None), ultima=max((c[1] for c in cells), default=None),
                disp=disp, wl=wl)


def precache_loop():
    """Comprueba en segundo plano la disponibilidad de TODAS las combinaciones origen × localidad."""
    d = load_json(PRE_PATH, 10 ** 10)
    if d:
        PRE["data"], PRE["ts"] = d.get("data", {}), d.get("ts", 0)
        log("disponibilidad cargada de disco:", len(PRE["data"]), "combinaciones")
    while True:
        if time.time() - PRE["ts"] > PRE_TTL:
            try:
                precache_once()
            except Exception as e:  # noqa
                log("precache error", e)
                time.sleep(600)
        time.sleep(300)


def precache_once():
    jobs = []
    for site in SITES.values():
        site.load()
        for o in [None] + [c for c, _ in site.origins]:
            for tc in sorted({x["townCode"] for x in site.config(o, force=True) if x["townCode"] in site.towns}):
                jobs.append((site, o, tc))
    PRE.update(running=True, done=0, total=len(jobs))
    log("precache: comprobando", len(jobs), "combinaciones")
    new = {}

    def one(j):
        site, o, tc = j
        try:
            new[f"{site.key}|{o or '_'}|{tc}"] = _estado_of(site, o, tc, force=True)
        except WafBlocked:
            raise
        except Exception as e:  # noqa
            log("precache fallo", site.key, o, tc, e)
        PRE["done"] += 1
        if PRE["done"] % 200 == 0:
            for s_ in SITES.values():
                s_.flush()

    try:
        with cf.ThreadPoolExecutor(WORKERS) as ex:
            list(ex.map(one, jobs))
    except WafBlocked as e:
        log("precache interrumpido:", e)
        PRE["data"].update(new)
        PRE["running"] = False
        time.sleep(1800)
        return
    PRE.update(data=new, ts=time.time(), running=False)
    os.makedirs(CACHE_DIR, exist_ok=True)
    with open(PRE_PATH, "w", encoding="utf-8") as f:
        json.dump({"ts": PRE["ts"], "data": new}, f, ensure_ascii=False)
    for s_ in SITES.values():
        s_.flush()
    log("precache completo:", sum(1 for v in new.values() if v["disponibles"]), "con plaza de", len(new))


SNAP = {"ts": 0, "fechas": {}, "src": None}
SNAPSHOT_URL = os.environ.get("SNAPSHOT_URL", "https://raw.githubusercontent.com/alftpa/buscador-imserso/data/snapshot.json.gz")
SNAP_LOCAL = os.path.join(os.path.dirname(os.path.abspath(__file__)), "snapshot.json.gz")


def apply_snapshot(d, src):
    import gzip  # noqa
    if not d or d.get("ts", 0) <= SNAP["ts"]:
        return False
    PRE["data"], PRE["ts"] = d.get("estado", {}), d["ts"]
    SNAP.update(ts=d["ts"], fechas=d.get("fechas", {}), src=src)
    for sk, cfg in (d.get("config") or {}).items():
        if sk in SITES:
            SITES[sk]._config_cache = cfg
    if d.get("hoteles"):
        INDEX.data = d["hoteles"]
    enrich_from_fechas()
    log("snapshot aplicado de", src, "·", len(PRE["data"]), "combinaciones,", len(SNAP["fechas"]), "con fechas")
    return True


EXTRA = {}   # key -> {desde, desdeWl, hotels}


def enrich_from_fechas():
    for k, d in SNAP["fechas"].items():
        rows = d.get("rows") or []
        pd = [r["priceNum"] for r in rows if r.get("priceNum") and r.get("status") == "Disponible"]
        pw = [r["priceNum"] for r in rows if r.get("priceNum")]
        hs = sorted({h["name"] for r in rows for h in (r.get("hotels") or []) if h.get("name")})
        by = {}
        for r in rows:
            for h in (r.get("hotels") or []):
                e = by.setdefault(h.get("name") or "", {"disp": set(), "wl": set(), "desde": None, "stays": set()})
                if r.get("status") == "Disponible":
                    e["disp"].add(r["date"])
                elif r.get("status") == "Lista de espera":
                    e["wl"].add(r["date"])
                if r.get("stay"):
                    e["stays"].add(r["stay"])
                if r.get("status") == "Disponible" and r.get("priceNum") and (e["desde"] is None or r["priceNum"] < e["desde"]):
                    e["desde"] = r["priceNum"]
        byHotel = {n: dict(disp=sorted(e["disp"]), wl=sorted(e["wl"] - e["disp"]), desde=e["desde"], stays=sorted(e["stays"]))
                   for n, e in by.items() if n}
        trips = []
        for r in rows:
            st = 1 if r.get("status") == "Disponible" else 2 if r.get("status") == "Lista de espera" else 0
            if st:
                trips.append([r["date"], st, r.get("stay") or "", [h.get("name") for h in (r.get("hotels") or []) if h.get("name")], r.get("priceNum")])
        EXTRA[k] = dict(desde=min(pd) if pd else None, desdeTodo=min(pw) if pw else None, hotels=hs, byHotel=byHotel, trips=trips)


def all_rows():
    """Listado completo precalculado (todas las combinaciones con su disponibilidad)."""
    out = []
    for key, est in PRE["data"].items():
        if not est or not est.get("fechas"):
            continue
        sk, o, tc = key.split("|", 2)
        site = SITES.get(sk)
        if not site or tc not in site.towns:
            continue
        t = site.towns[tc]
        stays = sorted({x["stay"] for x in site._config_cache.get(o, []) if x["townCode"] == tc},
                       key=lambda k: list(STAYS).index(k) if k in STAYS else 99)
        ex = EXTRA.get(key, {})
        out.append(dict(site=sk, origin=None if o == "_" else o, originName=site.origin_name(None if o == "_" else o),
                        place=tc, placeName=t["name"], province=t["provinceName"], zone=t["destinationName"],
                        subType=SUBTYPES.get(t["subType"], t["subType"]), stays=[STAYS.get(k, k) for k in stays],
                        stayCodes=stays, estado=est, desde=ex.get("desde"), desdeTodo=ex.get("desdeTodo"),
                        hotels=ex.get("hotels") or [], trips=ex.get("trips")))
    return out


def snapshot_loop():
    import gzip
    try:
        with gzip.open(SNAP_LOCAL, "rt", encoding="utf-8") as f:
            apply_snapshot(json.load(f), "fichero local")
    except Exception:
        pass
    while True:
        try:
            req = urllib.request.Request(SNAPSHOT_URL + f"?t={int(time.time() // 600)}", headers={"User-Agent": "ImsersoFinder"})
            raw = urllib.request.urlopen(req, timeout=60).read()
            apply_snapshot(json.loads(gzip.decompress(raw).decode("utf-8")), "GitHub")
        except Exception as e:  # noqa
            log("snapshot no disponible:", e)
        time.sleep(900)


def build_snapshot(path, progress=log):
    """Scrapeo completo (lo ejecuta GitHub Actions): disponibilidad + fechas/precios de todo lo que tiene plaza."""
    import gzip
    precache_once()
    fechas = {}
    keys = [k for k, v in PRE["data"].items() if v and v.get("disponibles")]
    progress(f"snapshot: leyendo fechas de {len(keys)} combinaciones")
    done = [0]

    def one(k):
        sk, o, tc = k.split("|", 2)
        try:
            r = dates_for(SITES[sk], None if o == "_" else o, tc)
            fechas[k] = dict(rows=r["rows"], completos=r["completos"], fechas=r["fechas"], days=r["days"])
        except WafBlocked:
            raise
        except Exception as e:  # noqa
            log("snapshot fallo", k, e)
        done[0] += 1
        if done[0] % 50 == 0:
            progress(f"snapshot: {done[0]}/{len(keys)}")

    try:
        with cf.ThreadPoolExecutor(WORKERS) as ex:
            list(ex.map(one, keys))
    except WafBlocked as e:
        log("snapshot parcial por bloqueo:", e)
    d = dict(ts=time.time(), estado=PRE["data"], fechas=fechas, hoteles=INDEX.data,
             config={k: s_._config_cache for k, s_ in SITES.items()})
    with gzip.open(path, "wt", encoding="utf-8") as f:
        json.dump(d, f, ensure_ascii=False, separators=(",", ":"))
    log("snapshot escrito:", path, os.path.getsize(path) // 1024, "KB,", len(fechas), "combinaciones con fechas")


def keep_awake():
    """Render free se duerme sin tráfico: un aviso cada 10 min lo mantiene despierto."""
    url = os.environ.get("RENDER_EXTERNAL_URL")
    while url:
        time.sleep(600)
        try:
            urllib.request.urlopen(url + "/ping", timeout=30).read()
        except Exception:
            pass


def meta():
    towns, offers, origins = {}, {}, []
    for s in SITES.values():
        if not s.loaded:
            continue
        origins.append(dict(site=s.key, code="_", name=SIN_TRANSPORTE))
        origins += [dict(site=s.key, code=c, name=n) for c, n in s.origins]
        offers[s.key] = {}
        for key, opts in s._config_cache.items():
            offers[s.key][key] = sorted({o["townCode"] + "|" + o["stay"] for o in opts if o["townCode"] in s.towns})
            for o in opts:
                tc = o["townCode"]
                if tc in s.towns and (s.key, tc) not in towns:
                    t = s.towns[tc]
                    towns[(s.key, tc)] = dict(site=s.key, code=tc, name=t["name"], province=t["provinceName"],
                                              zone=t["destinationName"], subType=SUBTYPES.get(t["subType"], t["subType"]))
    hotels, htowns = INDEX.catalog()
    for h in hotels:
        for t in h["towns"]:
            towns.setdefault((h["site"], t["code"]), t)
    return dict(origins=origins, stays=STAYS, towns=sorted(towns.values(), key=lambda t: (norm(t["name"]), t["site"])),
                hotels=[dict(site=h["site"], name=h["name"], code=h["code"], towns=[t["code"] for t in h["towns"]]) for h in hotels],
                offers=offers, warm=WARM["done"], warmError=WARM["error"],
                pre=dict(n=len(PRE["data"]), ts=PRE["ts"], running=PRE["running"], done=PRE["done"], total=PRE["total"]))


# --------------------------------------------------------------------------- #
#  Consultas
# --------------------------------------------------------------------------- #
def origins_for_place(site, code, stay=None, progress=lambda *a: None):
    """Desde qué orígenes se ofrece un lugar. [{origin, originName, stays}]"""
    site.load()
    origins = [None] + [c for c, _ in site.origins]
    done = [0]

    def one(o):
        opts = site.config(o)
        if code.startswith("D:"):
            sel = [x for x in opts if x["destinationCode"] == code[2:]]
        elif code.startswith("P:"):
            sel = [x for x in opts if x["provinceCode"] == code[2:]]
        else:
            sel = [x for x in opts if x["townCode"] == code]
        stays = sorted({x["stay"] for x in sel if not stay or x["stay"] == stay},
                       key=lambda s: list(STAYS).index(s) if s in STAYS else 99)
        done[0] += 1
        progress(f"{site.host}: consultando orígenes {done[0]}/{len(origins)}")
        return o, stays

    result = []
    with cf.ThreadPoolExecutor(WORKERS) as ex:
        for o, stays in ex.map(one, origins):
            if stays:
                result.append(dict(origin=o, originName=site.origin_name(o), stays=[STAYS.get(s, s) for s in stays]))
    return result


def dates_for(site, origin, code, stay=None, hotel_filter=None, progress=lambda *a: None, force=False):
    """Fechas + hoteles + precios para (origen, lugar)."""
    site.load()
    if code.startswith("D:"):
        kw = dict(destination=code[2:], sub_type=site.place(code)["subType"])
    elif code.startswith("P:"):
        kw = dict(province=code[2:])
    else:
        kw = dict(town=code)
    cells, completos, days = site.calendar_days(origin=origin, stay=stay, force=force, **kw)
    done = [0]

    def one(cell):
        status, date, codes = cell
        r = site.search(date, codes, origin=origin, stay=stay, force=force, **kw)
        done[0] += 1
        progress(f"{site.host} / {site.origin_name(origin)}: leyendo fechas {done[0]}/{len(cells)}")
        return r

    rows = []
    with cf.ThreadPoolExecutor(WORKERS) as ex:
        for r in ex.map(one, cells):
            rows.extend(r)
    INDEX.learn(site, rows, code)
    if hotel_filter:
        n = norm(hotel_filter)
        rows = [r for r in rows if any(n in norm(h["name"]) for h in r.get("hotels") or [dict(name=r["hotel"])])]
    rows.sort(key=lambda r: (r["date"], r["hotel"]))
    return dict(rows=rows, completos=completos, fechas=len(cells), days=days)


# --------------------------------------------------------------------------- #
#  Trabajos en segundo plano (progreso en la web)
# --------------------------------------------------------------------------- #
JOBS = {}


def start_job(fn):
    if len(JOBS) > 300:
        for k in list(JOBS)[:150]:
            if JOBS[k]["done"]:
                JOBS.pop(k, None)
    jid = uuid.uuid4().hex
    JOBS[jid] = {"progress": "Iniciando…", "done": False, "result": None, "error": None}

    def run():
        try:
            JOBS[jid]["result"] = fn(lambda msg: JOBS[jid].__setitem__("progress", msg))
        except WafBlocked as e:
            JOBS[jid]["error"] = str(e)
        except Exception as e:  # noqa
            import traceback
            traceback.print_exc()
            JOBS[jid]["error"] = f"Error: {e}"
        for s_ in SITES.values():
            s_.flush()
        JOBS[jid]["done"] = True

    threading.Thread(target=run, daemon=True).start()
    return jid


def job_buscar(p):
    """Hotel y/o localidad -> orígenes que lo ofrecen."""
    hotel = (p.get("hotel") or "").strip()           # "site|nombre" (desplegable) o texto libre (terminal)
    localidad = (p.get("localidad") or "").strip()   # "site|code" (desplegable) o texto libre (terminal)
    stay = p.get("stay") or None
    origin_filter = norm(p.get("origen") or "")
    site_filter = p.get("site") or ""

    def run(progress):
        for s in SITES.values():
            s.load()
        if not hotel and not localidad:
            return browse_origin(progress)
        if hotel and not INDEX.ready():
            progress("Leyendo el catálogo de hoteles (solo la primera vez, 2-3 min)…")
            INDEX.build(progress)
        targets = {}   # (site, code) -> set(hoteles)
        if hotel:
            if "|" in hotel:
                sk, name = hotel.split("|", 1)
                info = INDEX.data.get(sk, {}).get(name)
                matches = [dict(site=sk, hotel=name, towns=info["towns"])] if info else []
            else:
                n = norm(hotel)
                matches = [dict(site=sk, hotel=hn, towns=i["towns"]) for sk, hs in INDEX.data.items()
                           for hn, i in hs.items() if n in norm(hn)]
            if not matches:
                return dict(rows=[], msg=f"Ningún hotel del catálogo se llama «{hotel}».")
            loc_site, loc_code = (localidad.split("|", 1) if "|" in localidad else (None, None))
            for m in matches:
                for tc in m["towns"]:
                    if loc_code and (m["site"] != loc_site or tc != loc_code):
                        continue
                    if localidad and not loc_code and norm(localidad) not in norm(SITES[m["site"]].place(tc)["name"]):
                        continue
                    targets.setdefault((m["site"], tc), set()).add(m["hotel"])
        elif "|" in localidad:
            sk, code = localidad.split("|", 1)
            targets[(sk, code)] = set()
        else:
            n = norm(localidad)
            for s in SITES.values():
                for tn, codes in s.town_codes_by_norm.items():
                    if n in tn:
                        for tc in codes:
                            targets[(s.key, tc)] = set()
        if site_filter:
            targets = {k: v for k, v in targets.items() if k[0] == site_filter}
        if not targets:
            return dict(rows=[], msg="No hay nada en la programación que cumpla esos filtros.")
        rows = []
        for i, ((sk, tc), hotels) in enumerate(targets.items(), 1):
            s = SITES[sk]
            t = s.place(tc)
            progress(f"[{i}/{len(targets)}] {t['name']} ({s.host})")
            for o in origins_for_place(s, tc, stay, progress):
                if origin_filter and not origin_match(origin_filter, o["originName"]):
                    continue
                rows.append(dict(site=sk, host=s.host, siteLabel=s.label, origin=o["origin"], originName=o["originName"],
                                 place=tc, placeName=t["name"], province=t["provinceName"], zone=t["destinationName"],
                                 subType=SUBTYPES.get(t["subType"], t["subType"]), stays=o["stays"], hotels=sorted(hotels)))
        rows.sort(key=lambda r: (norm(r["placeName"]), r["originName"] == SIN_TRANSPORTE, norm(r["originName"]), r["site"]))
        msg = "" if rows else "Existe en el catálogo, pero ahora mismo no se ofrece desde ningún origen con esos filtros."
        return dict(rows=rows, msg=msg, hotelMatches=sorted({h for hs in targets.values() for h in hs}))

    def browse_origin(progress):
        """Sin hotel ni localidad: todo lo que sale desde el origen elegido (o desde todos)."""
        rows = []
        for s in SITES.values():
            if site_filter and s.key != site_filter:
                continue
            origins = [None] + [c for c, _ in s.origins]
            if origin_filter:
                origins = [o for o in origins if origin_match(origin_filter, s.origin_name(o))]
            for i, o in enumerate(origins, 1):
                progress(f"{s.host}: {s.origin_name(o)} ({i}/{len(origins)})")
                by_town = {}
                for x in s.config(o):
                    if stay and x["stay"] != stay:
                        continue
                    by_town.setdefault(x["townCode"], set()).add(x["stay"])
                for tc, stays in by_town.items():
                    if tc not in s.towns:
                        continue
                    t = s.towns[tc]
                    st = sorted(stays, key=lambda k: list(STAYS).index(k) if k in STAYS else 99)
                    rows.append(dict(site=s.key, host=s.host, siteLabel=s.label, origin=o, originName=s.origin_name(o),
                                     place=tc, placeName=t["name"], province=t["provinceName"], zone=t["destinationName"],
                                     subType=SUBTYPES.get(t["subType"], t["subType"]), stays=[STAYS.get(k, k) for k in st], hotels=[]))
        rows.sort(key=lambda r: (r["originName"] == SIN_TRANSPORTE, norm(r["originName"]), norm(r["placeName"]), r["site"]))
        msg = "" if rows else "No hay nada programado con esos filtros."
        return dict(rows=rows, msg=msg, hotelMatches=[])

    return start_job(run)


def from_snapshot(p):
    k = f"{p['site']}|{p.get('origin') or '_'}|{p['place']}"
    d = SNAP["fechas"].get(k)
    if d is None or p.get("force"):
        return None
    rows = d["rows"]
    stay = p.get("stay")
    if stay:
        rows = [r for r in rows if r.get("stay") == stay]
    if p.get("hotel"):
        n = norm(p["hotel"])
        rows = [r for r in rows if any(n in norm(h["name"]) for h in r.get("hotels") or [dict(name=r["hotel"])])]
    return dict(rows=rows, completos=d["completos"], fechas=d["fechas"], days=d["days"], snapshot=SNAP["ts"])


def job_fechas(p):
    hit = from_snapshot(p)
    if hit is not None:
        jid = uuid.uuid4().hex
        JOBS[jid] = {"progress": "", "done": True, "result": hit, "error": None}
        return jid
    site = SITES[p["site"]]
    return start_job(lambda progress: dates_for(site, p.get("origin") or None, p["place"], p.get("stay") or None,
                                                p.get("hotel") or None, progress, force=bool(p.get("force"))))


def job_listado(p):
    """Combinaciones (web, origen, localidad) a partir de los filtros ya resueltos en la página."""
    towns = set(p.get("towns") or [])       # "site|code"
    origins = set(p.get("origins") or [])   # "site|code" ("_" = sin transporte)
    stay = p.get("stay") or None

    def run(progress):
        rows = []
        for s in SITES.values():
            s.load()
            for ok in [None] + [c for c, _ in s.origins]:
                key = ok or "_"
                if origins and f"{s.key}|{key}" not in origins:
                    continue
                by_town = {}
                for x in s.config(ok):
                    if stay and x["stay"] != stay:
                        continue
                    if towns and f"{s.key}|{x['townCode']}" not in towns:
                        continue
                    if x["townCode"] in s.towns:
                        by_town.setdefault(x["townCode"], set()).add(x["stay"])
                for tc, stays in by_town.items():
                    t = s.towns[tc]
                    st = sorted(stays, key=lambda k: list(STAYS).index(k) if k in STAYS else 99)
                    rows.append(dict(site=s.key, host=s.host, origin=ok, originName=s.origin_name(ok), place=tc, placeName=t["name"],
                                     province=t["provinceName"], zone=t["destinationName"],
                                     subType=SUBTYPES.get(t["subType"], t["subType"]), stays=[STAYS.get(k, k) for k in st],
                                     estado=None if stay else PRE["data"].get(f"{s.key}|{key}|{tc}")))
        rows.sort(key=lambda r: (norm(r["placeName"]), r["originName"] == SIN_TRANSPORTE, norm(r["originName"]), r["site"]))
        return dict(rows=rows)

    return start_job(run)


def job_estado(p):
    """Para cada combinación (site, origin, place): cuántas salidas hay y en qué estado."""
    rows = p.get("rows") or []
    stay = p.get("stay") or None

    def run(progress):
        done = [0]

        def one(r):
            site = SITES[r["site"]]
            code = r["place"]
            pre = PRE["data"].get(f"{r['site']}|{r.get('origin') or '_'}|{code}")
            if pre is not None and not stay:
                done[0] += 1
                return pre
            try:
                est = _estado_of(site, r.get("origin") or None, code, stay=stay)
            except WafBlocked:
                raise
            except Exception as e:  # noqa
                log("estado error", r, e)
                est = None
            done[0] += 1
            progress(f"Comprobando salidas {done[0]}/{len(rows)}")
            return est

        with cf.ThreadPoolExecutor(WORKERS) as ex:
            return dict(estados=list(ex.map(one, rows)))

    return start_job(run)


def job_reindex(p):
    return start_job(lambda progress: {"ok": True, "n": sum(len(v) for v in INDEX.build(progress, force=True).values())})


# --------------------------------------------------------------------------- #
#  Página web
# --------------------------------------------------------------------------- #
HTML = r"""<!doctype html>
<html lang="es"><head><meta charset="utf-8"><title>Buscador IMSERSO</title>
<meta name="viewport" content="width=device-width,initial-scale=1">
<link href="https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700;800&display=swap" rel="stylesheet">
<style>
:root{--bg:#f3f5f9;--card:#fff;--ink:#0f172a;--mut:#64748b;--acc:#0e5c8a;--acc2:#1a9bd7;--ok:#15803d;--okbg:#dcfce7;--warn:#b45309;--warnbg:#fef3c7;--bad:#b91c1c;--badbg:#fee2e2;--line:#e2e8f0;--ts:#0e5c8a;--mc:#7c3aed;--r:14px}
*{box-sizing:border-box}html{scroll-behavior:smooth}
body{margin:0;font:15px/1.45 Inter,-apple-system,"Helvetica Neue",Arial,sans-serif;background:var(--bg);color:var(--ink)}
.hero{background:radial-gradient(1200px 400px at 10% -20%,#1a9bd7 0%,#0e5c8a 45%,#0b3f61 100%);color:#fff;padding:26px 24px 70px}
.hero .in{max-width:1240px;margin:0 auto;display:flex;align-items:center;gap:16px}
.hero .logo{width:52px;height:52px;border-radius:14px;background:rgba(255,255,255,.15);display:grid;place-items:center;font-size:28px}
.hero h1{margin:0;font-size:24px;font-weight:800;letter-spacing:-.01em}.hero small{display:block;opacity:.85;font-size:13px;margin-top:2px}
.hero .st{margin-left:auto;font-size:12px;background:rgba(255,255,255,.14);padding:6px 12px;border-radius:20px;display:flex;gap:8px;align-items:center}
.dot{width:8px;height:8px;border-radius:50%;background:#fbbf24}.dot.ok{background:#4ade80}
main{max-width:1240px;margin:-48px auto 0;padding:0 16px 80px}
.card{background:var(--card);border:1px solid var(--line);border-radius:var(--r);padding:20px;margin-bottom:18px;box-shadow:0 10px 30px -18px rgba(2,20,40,.35)}
.filters{display:grid;grid-template-columns:repeat(4,1fr);gap:14px}.filters button{padding:11px 12px}
label{display:block;font-size:11px;color:var(--mut);margin-bottom:6px;text-transform:uppercase;letter-spacing:.08em;font-weight:700}
select,input{width:100%;padding:11px 12px;border:1px solid var(--line);border-radius:10px;font-size:15px;background:#fff;color:var(--ink);font-family:inherit;appearance:none;-webkit-appearance:none}
select{background-image:url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='12' height='8'%3E%3Cpath d='M1 1l5 5 5-5' stroke='%2364748b' stroke-width='1.8' fill='none'/%3E%3C/svg%3E");background-repeat:no-repeat;background-position:right 12px center;padding-right:32px}
select:focus,input:focus{outline:3px solid #bfe3f7;border-color:var(--acc2)}
select.set{border-color:var(--acc2);background-color:#f0f8fd;font-weight:600}
.row{display:flex;gap:10px;align-items:center;margin-top:16px;flex-wrap:wrap}
button{padding:11px 18px;border:0;border-radius:10px;background:var(--acc);color:#fff;font-size:15px;cursor:pointer;font-weight:600;font-family:inherit;transition:.15s}
button:hover{background:var(--acc2)}button.sec{background:#eef2f7;color:var(--ink)}button.sec:hover{background:#e2e8f0}
button.mini{padding:7px 12px;font-size:13px;border-radius:8px}button:disabled{opacity:.45;cursor:default}
.tog{display:flex;align-items:center;gap:8px;font-size:13.5px;color:var(--mut);cursor:pointer;user-select:none}.tog input{width:auto}
#status{color:var(--mut);font-size:13.5px;display:flex;align-items:center;gap:8px;margin-left:auto}
.spin{width:16px;height:16px;border:2px solid #cbd5e1;border-top-color:var(--acc);border-radius:50%;animation:sp .8s linear infinite;display:none}.busy .spin{display:inline-block}
@keyframes sp{to{transform:rotate(360deg)}}
.bar{height:4px;background:#e2e8f0;border-radius:4px;overflow:hidden;margin-top:12px;display:none}.bar i{display:block;height:100%;width:0;background:linear-gradient(90deg,var(--acc),var(--acc2));transition:width .3s}
.help{font-size:13px;color:var(--mut);margin-top:12px}
.err{padding:12px 14px;background:var(--badbg);border:1px solid #fca5a5;border-radius:10px;margin-bottom:12px;color:#7f1d1d}
.msg{padding:12px 14px;background:var(--warnbg);border:1px solid #fcd34d;border-radius:10px;margin-bottom:12px}
h2{font-size:18px;margin:0 0 4px;font-weight:800;letter-spacing:-.01em}.sub{color:var(--mut);font-size:13.5px;margin-bottom:14px}
.kpis{display:flex;gap:10px;flex-wrap:wrap;margin-bottom:14px}.kpi{background:#f8fafc;border:1px solid var(--line);border-radius:12px;padding:10px 14px;min-width:120px}.kpi b{display:block;font-size:22px;font-weight:800}.kpi span{font-size:11px;color:var(--mut);text-transform:uppercase;letter-spacing:.06em;font-weight:600}
.place{border:1px solid var(--line);border-radius:12px;margin-bottom:12px;overflow:hidden}
.place .ph{display:flex;align-items:center;gap:12px;padding:12px 14px;background:#f8fafc;border-bottom:1px solid var(--line);flex-wrap:wrap}
.place .ph .nm{font-weight:800;font-size:16px}.place .ph .wh{color:var(--mut);font-size:13px}.place .ph .hot{margin-left:auto;font-size:13px;color:var(--mut)}
.site{font-size:11px;font-weight:700;padding:3px 8px;border-radius:6px;color:#fff;white-space:nowrap;letter-spacing:.02em}.site.ts{background:var(--ts)}.site.mc{background:var(--mc)}
.tag{display:inline-block;padding:2px 9px;border-radius:20px;font-size:12px;background:#eef2f7;margin:1px 3px 1px 0;white-space:nowrap;font-weight:500}
.tag.p{background:#e0f2fe;color:#075985}
table{width:100%;border-collapse:collapse;font-size:14px}td,th{padding:10px 12px;border-bottom:1px solid var(--line);text-align:left;vertical-align:middle}
th{font-size:11px;color:var(--mut);text-transform:uppercase;letter-spacing:.06em;font-weight:700;background:#fff}
tr:last-child td{border-bottom:0}tr.r:hover td{background:#f5f9fd}
.pill{display:inline-flex;align-items:center;gap:6px;padding:3px 10px;border-radius:20px;font-size:12.5px;font-weight:700}
.pill.ok{background:var(--okbg);color:var(--ok)}.pill.warn{background:var(--warnbg);color:var(--warn)}.pill.bad{background:var(--badbg);color:var(--bad)}.pill.g{background:#eef2f7;color:var(--mut)}
.st-ok{color:var(--ok);font-weight:700}.st-warn{color:var(--warn);font-weight:700}.st-bad{color:var(--bad);font-weight:700}
.hl{color:var(--acc);cursor:pointer;font-weight:600;text-decoration:underline dotted;text-underline-offset:3px}.hl:hover{color:var(--acc2)}
.mut{color:var(--mut)}
.chips{display:flex;gap:8px;flex-wrap:wrap;margin:0 0 12px}.chip{padding:6px 13px;border-radius:20px;border:1px solid var(--line);background:#fff;cursor:pointer;font-size:13px;font-weight:600;color:var(--ink)}.chip.on{background:var(--acc);color:#fff;border-color:var(--acc)}
/* modales */
.ov{position:fixed;inset:0;background:rgba(2,12,27,.6);backdrop-filter:blur(3px);display:none;align-items:center;justify-content:center;z-index:50;padding:16px}.ov.open{display:flex}
#ov{z-index:60}
.md{background:#fff;border-radius:18px;max-width:980px;width:100%;max-height:92vh;overflow:auto;box-shadow:0 30px 80px rgba(0,0,0,.4);animation:up .18s ease-out}.md.wide{max-width:1240px}
@keyframes up{from{transform:translateY(12px);opacity:0}to{transform:none;opacity:1}}
.md .mh{position:sticky;top:0;z-index:2;padding:16px 20px;display:flex;align-items:center;gap:12px;background:linear-gradient(90deg,var(--acc),var(--acc2));color:#fff}
.md .mh h1{font-size:19px;margin:0;font-weight:800}.md .mh small{display:block;opacity:.85;font-size:13px}.md .x{margin-left:auto;background:rgba(255,255,255,.2);border-radius:50%;width:36px;height:36px;padding:0;font-size:18px}
.mpad{padding:20px}
.mgrid{display:grid;grid-template-columns:minmax(300px,1.1fr) 2fr;gap:20px}
.cal{display:grid;grid-template-columns:repeat(auto-fill,minmax(200px,1fr));gap:12px}
.mon{border:1px solid var(--line);border-radius:12px;padding:10px}.mon h4{margin:0 0 6px;font-size:13px;text-align:center;text-transform:capitalize;font-weight:700}
.dow,.days{display:grid;grid-template-columns:repeat(7,1fr);gap:2px}.dow span{font-size:10px;color:var(--mut);text-align:center;font-weight:700}
.d{aspect-ratio:1;display:grid;place-items:center;font-size:12px;border-radius:7px;color:#94a3b8}
.d.ok{background:var(--okbg);color:var(--ok);font-weight:700;cursor:pointer}.d.warn{background:var(--warnbg);color:var(--warn);font-weight:700;cursor:pointer}.d.bad{background:var(--badbg);color:var(--bad);text-decoration:line-through}
.d.sel{outline:2px solid var(--acc);outline-offset:-2px}
.leg{display:flex;gap:14px;font-size:12px;color:var(--mut);margin:10px 0 0;flex-wrap:wrap}.leg i{display:inline-block;width:12px;height:12px;border-radius:4px;vertical-align:-2px;margin-right:4px}
.hbody{display:grid;grid-template-columns:1fr 1.3fr;gap:20px;padding:20px}.hbody p{margin:0 0 9px}
.gal img.big{width:100%;aspect-ratio:4/3;object-fit:cover;border-radius:12px;background:#eee}
.thumbs{display:flex;gap:6px;flex-wrap:wrap;margin-top:8px}.thumbs img{width:64px;height:48px;object-fit:cover;border-radius:6px;cursor:pointer;opacity:.65;border:2px solid transparent}.thumbs img.on,.thumbs img:hover{opacity:1;border-color:var(--acc2)}
.svc{columns:2;font-size:14px;padding-left:18px;margin:6px 0 0}.mfoot{padding:0 20px 20px;display:flex;gap:10px;flex-wrap:wrap}
@media(max-width:900px){.filters{grid-template-columns:1fr 1fr}.mgrid,.hbody{grid-template-columns:1fr}.svc{columns:1}}
@media(max-width:560px){.filters{grid-template-columns:1fr}}
</style></head><body>
<div class="hero"><div class="in"><div class="logo">🏖️</div><div><h1>Buscador IMSERSO</h1><small>Turismo Social (península) · Mundicolor (Baleares y Canarias)</small></div><div class="st"><span class="dot" id="dot"></span><span id="dott">Preparando…</span></div></div></div>
<main>
<div class="card">
 <div class="filters">
  <div><label>Web</label><select id="site"><option value="">Las dos</option><option value="turismosocial">Turismo Social (península)</option><option value="mundicolor">Mundicolor (islas)</option></select></div>
  <div><label>Zona / destino</label><select id="zona"><option value="">Todas las zonas</option></select></div>
  <div><label>Provincia / isla</label><select id="prov"><option value="">Todas</option></select></div>
  <div><label>Localidad</label><select id="localidad"><option value="">Todas las localidades</option></select></div>
  <div><label>Hotel</label><select id="hotel"><option value="">Cualquier hotel</option></select></div>
  <div><label>Origen (ciudad de salida)</label><select id="origen"><option value="">Todos los orígenes</option></select></div>
  <div><label>Estancia</label><select id="stay"><option value="">Todas</option></select></div>
  <div><label>&nbsp;</label><button class="sec" id="limpiar" style="width:100%">Limpiar filtros</button></div>
 </div>
 <div class="row">
  <button id="buscar">🔎 Buscar viajes</button>
  <a href="https://github.com/alftpa/buscador-imserso/actions/workflows/snapshot.yml" target="_blank" rel="noopener" title="Abre GitHub: pulsa «Run workflow» y en ~1 h todos los datos estarán actualizados"><button class="sec" type="button">⟳ Relanzar scrapeo completo</button></a>
  <button class="sec" id="reindex" title="Vuelve a leer el catálogo de hoteles (2-3 min)">↻ Catálogo</button>
  <label class="tog"><input type="checkbox" id="incwl"> incluir solo lista de espera</label>
  <span id="status"><span class="spin"></span><span id="stxt"></span></span>
 </div>
 <div class="bar" id="bar"><i></i></div>
 <div class="help" id="help">Los desplegables se filtran entre sí: elige por ejemplo la zona <b>Canarias</b> y el resto solo mostrará lo que exista allí. Pulsa <b>Buscar viajes</b> y verás, por localidad, desde qué ciudades sale y cuántas fechas tienen plaza.</div>
</div>
<div id="errbox"></div>
<div class="card" id="res1" style="display:none">
 <h2>Resultados</h2><div class="sub" id="sub1"></div>
 <div class="kpis" id="kpis"></div>
 <div id="msg1"></div>
 <div id="list"></div>
</div>
</main>

<div class="ov" id="ov2"><div class="md wide" role="dialog" aria-modal="true">
 <div class="mh"><div><h1 id="t2">Fechas y precios</h1><small id="t2s"></small></div><button class="sec mini" id="refresh2" style="margin-left:auto" title="Volver a consultar la web ahora mismo">↻ Actualizar</button><button class="x" id="mclose2" aria-label="Cerrar" style="margin-left:8px">✕</button></div>
 <div class="mpad">
  <div class="kpis" id="sum2"></div>
  <div id="msg2"></div>
  <div class="mgrid">
   <div><div class="cal" id="cal"></div><div class="leg"><span><i style="background:var(--okbg)"></i>Disponible</span><span><i style="background:var(--warnbg)"></i>Lista de espera</span><span><i style="background:var(--badbg)"></i>Completo</span> · pulsa un día para filtrar</div></div>
   <div>
    <div class="chips" id="chips"></div>
    <div style="overflow:auto;max-height:62vh"><table><thead><tr><th>Fecha</th><th>Estado</th><th>Hotel</th><th>Días</th><th>Salida</th><th>Precio</th></tr></thead><tbody id="tb2"></tbody></table></div>
   </div>
  </div>
 </div>
</div></div>

<div class="ov" id="ov"><div class="md" role="dialog" aria-modal="true">
 <div class="mh"><div><h1 id="mtitle">Hotel</h1><small id="msub"></small></div><button class="x" id="mclose" aria-label="Cerrar">✕</button></div>
 <div class="hbody" id="mbody"></div><div class="mfoot" id="mfoot"></div>
</div></div>
<script>
const $=s=>document.querySelector(s);
const esc=s=>String(s??'').replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
const N=s=>(s||'').normalize('NFD').replace(/[̀-ͯ]/g,'').toUpperCase().trim();
const siteTag=s=>`<span class="site ${s==='mundicolor'?'mc':'ts'}">${s==='mundicolor'?'Mundicolor':'Turismo Social'}</span>`;
const fmtDate=d=>d.split('-').reverse().join('/');
const MES=['enero','febrero','marzo','abril','mayo','junio','julio','agosto','septiembre','octubre','noviembre','diciembre'];
let META={hotels:[],towns:[],origins:[],stays:{},offers:{}},rows=[],rows2=[],days2=[],filt2='',day2='';
async function api(path,body){const r=await fetch(path,{method:body?'POST':'GET',headers:{'Content-Type':'application/json'},body:body?JSON.stringify(body):undefined});return r.json();}
async function runJob(path,body){
  const {job}=await api(path,body);
  while(true){await new Promise(r=>setTimeout(r,500));const j=await api('/api/job/'+job);
    $('#stxt').textContent=j.progress||'';const m=(j.progress||'').match(/(\d+)\/(\d+)/);if(m){$('#bar').style.display='block';$('#bar i').style.width=(100*m[1]/m[2])+'%';}
    if(j.done){ if(j.error) throw new Error(j.error); return j.result; }}
}
function busy(b){document.body.classList.toggle('busy',b);document.querySelectorAll('main button').forEach(x=>x.disabled=b);if(!b){$('#stxt').textContent='';$('#bar').style.display='none';$('#bar i').style.width='0';}}
function showErr(m){$('#errbox').innerHTML=m?`<div class="err">⚠️ ${esc(m)}</div>`:'';}
const originName=n=>N(n).replace(' DE LA PLANA','').replace(', A','');   // CASTELLÓN ≡ CASTELLÓN DE LA PLANA
// ---------- filtros en cascada ----------
function sel(id){return $('#'+id).value;}
function offersOf(site,okey){return META.offers[site]&&META.offers[site][okey]||[];}
function townKey(t){return t.site+'|'+t.code;}
const NL=s=>N(s).replace(/\bPTO\.?\s/,'PUERTO ').replace(/\bSTA\.?\s/,'SANTA ').replace(/^SANTA CRUZ DE TENERIFE$/,'TENERIFE').replace(/[.,]/g,'').replace(/\s+/g,' ').trim();
const locKey=t=>NL(t.name)+'|'+NL(t.province||t.zone);
function currentTowns(ignore){
  // localidades compatibles con todos los filtros salvo el indicado en `ignore`
  const site=sel('site'),zona=sel('zona'),prov=sel('prov'),loc=sel('localidad'),hot=sel('hotel'),ori=sel('origen'),stay=sel('stay');
  const h=hot&&ignore!=='hotel'?META.hotels.find(x=>x.site+'|'+x.name===hot):null;
  let ts=META.towns.filter(t=>(!site||t.site===site)&&(ignore==='zona'||!zona||t.zone===zona)&&(ignore==='prov'||!prov||t.province===prov)
     &&(ignore==='localidad'||!loc||locKey(t)===loc)&&(!h||(h.site===t.site&&h.towns.includes(t.code))));
  if(ori&&ignore!=='origen'){const ok=new Set();for(const o of META.origins.filter(o=>originName(o.name)===ori))for(const x of offersOf(o.site,o.code)){const [tc,st]=x.split('|');if(!stay||st===stay)ok.add(o.site+'|'+tc);}ts=ts.filter(t=>ok.has(townKey(t)));}
  else if(stay){const ok=new Set();for(const s in META.offers)for(const k in META.offers[s])for(const x of META.offers[s][k]){const [tc,st]=x.split('|');if(st===stay)ok.add(s+'|'+tc);}ts=ts.filter(t=>ok.has(townKey(t)));}
  return ts;
}
function fill(id,opts,first){const e=$('#'+id),v=e.value;e.innerHTML=`<option value="">${first}</option>`+opts.map(o=>`<option value="${esc(o.v)}">${esc(o.l)}</option>`).join('');e.value=[...e.options].some(o=>o.value===v)?v:'';e.classList.toggle('set',!!e.value);}
function cascade(){
  const site=sel('site');
  const tz=currentTowns('zona');fill('zona',[...new Set(tz.map(t=>t.zone))].sort().map(z=>({v:z,l:z})),'Todas las zonas');
  const tp=currentTowns('prov');fill('prov',[...new Set(tp.map(t=>t.province).filter(Boolean))].sort().map(p=>({v:p,l:p})),'Todas');
  const tl=currentTowns('localidad'),lm=new Map();tl.forEach(t=>{const k=locKey(t);if(!lm.has(k))lm.set(k,{v:k,l:`${t.name} (${t.province||t.zone})`});});
  fill('localidad',[...lm.values()].sort((a,b)=>a.l.localeCompare(b.l)),'Todas las localidades');
  const th=currentTowns('hotel'),thk=new Set(th.map(townKey));
  fill('hotel',META.hotels.filter(h=>h.towns.some(c=>thk.has(h.site+'|'+c))).map(h=>({v:h.site+'|'+h.name,l:h.name+' — '+h.towns.map(c=>(META.towns.find(t=>t.site===h.site&&t.code===c)||{}).name||'').filter(Boolean).join(' / ')})).sort((a,b)=>a.l.localeCompare(b.l)),'Cualquier hotel');
  const to=currentTowns('origen'),tok=new Set(to.map(townKey)),stay=sel('stay'),names=new Map();
  for(const o of META.origins){if(site&&o.site!==site)continue;if(offersOf(o.site,o.code).some(x=>{const [tc,st]=x.split('|');return tok.has(o.site+'|'+tc)&&(!stay||st===stay);})){const k=originName(o.name);if(!names.has(k))names.set(k,o.name);}}
  fill('origen',[...names.entries()].sort((a,b)=>a[0]==='SIN TRANSPORTE'?1:b[0]==='SIN TRANSPORTE'?-1:a[1].localeCompare(b[1])).map(([k,n])=>({v:k,l:n==='SIN TRANSPORTE'?'Sin transporte (voy por mi cuenta)':n})),'Todos los orígenes');
  $('#site').classList.toggle('set',!!site);$('#stay').classList.toggle('set',!!stay);
}
async function loadMeta(){
  META=await api('/api/meta');const first=!$('#stay').options.length||$('#stay').options.length===1;
  $('#stay').innerHTML='<option value="">Todas</option>'+Object.entries(META.stays).map(([k,v])=>`<option value="${k}">${esc(v)}</option>`).join('');
  cascade();if(first){loadF();cascade();}
  $('#dot').classList.toggle('ok',META.warm);const P=META.pre||{};$('#dott').textContent=!META.warm?'Leyendo orígenes…':P.running&&!P.n?`Precargando disponibilidad ${P.done}/${P.total}`:`${META.hotels.length} hoteles · ${META.towns.length} localidades`+(P.ts?` · plazas al ${new Date(P.ts*1000).toLocaleString('es-ES',{day:'2-digit',month:'2-digit',hour:'2-digit',minute:'2-digit'})}`:'');
  $('#dot').classList.toggle('ok',META.warm&&!!P.n);
  if(!META.hotels.length)$('#help').innerHTML='<b>Primera vez:</b> pulsa <b>↻ Catálogo</b> para leer los hoteles de las dos webs (2-3 min).';
  if(!META.warm||(P.running&&!P.n))setTimeout(loadMeta,5000);
}
['site','zona','prov','localidad','hotel','origen','stay'].forEach(id=>$('#'+id).addEventListener('change',()=>{cascade();saveF();}));
function saveF(){try{localStorage.setItem('imserso.f',JSON.stringify(Object.fromEntries(['site','zona','prov','localidad','hotel','origen','stay','incwl'].map(id=>[id,id==='incwl'?$('#incwl').checked:sel(id)]))));}catch(e){}}
function loadF(){try{const f=JSON.parse(localStorage.getItem('imserso.f')||'{}');['site','zona','prov','localidad','hotel','origen','stay'].forEach(id=>{if(f[id]!=null)$('#'+id).value=f[id];});$('#incwl').checked=!!f.incwl;}catch(e){}}
// ---------- búsqueda ----------
async function buscar(){
  showErr('');busy(true);$('#res1').style.display='none';
  try{
    const towns=currentTowns().map(townKey);
    if(!towns.length)throw new Error('No hay ninguna localidad que cumpla esos filtros.');
    const ori=sel('origen'),site=sel('site');
    const origins=ori?META.origins.filter(o=>originName(o.name)===ori&&(!site||o.site===site)).map(o=>o.site+'|'+o.code):[];
    if(towns.length>60&&!ori)throw new Error(`Son ${towns.length} localidades: acota con zona, provincia, localidad, hotel u origen para no lanzar cientos de consultas.`);
    const r=await runJob('/api/listado',{towns,origins,stay:sel('stay')});
    rows=r.rows;
    if(!rows.length){$('#res1').style.display='';$('#list').innerHTML='';$('#kpis').innerHTML='';$('#msg1').innerHTML='<div class="msg">No hay nada programado con esos filtros.</div>';return;}
    checked=false;$('#msg1').innerHTML='';
    const pend=rows.map((x,i)=>[x,i]).filter(([x])=>!x.estado);
    if(pend.length){
      $('#stxt').textContent=`Comprobando plazas de ${pend.length} combinaciones…`;
      const e=await runJob('/api/estado',{rows:pend.map(([x])=>({site:x.site,origin:x.origin,place:x.place})),stay:sel('stay')});
      e.estados.forEach((st,k)=>rows[pend[k][1]].estado=st);
    }
    checked=true;$('#res1').style.display='';render1(true);
    $('#res1').scrollIntoView({behavior:'smooth',block:'start'});
  }catch(e){showErr(e.message)}finally{busy(false)}
}
let checked=false;
function keep(x){if(!x.estado)return !checked;return x.estado.disponibles>0||($('#incwl').checked&&x.estado.espera>0);}
function render1(done){
  const hot=sel('hotel'),hname=hot?hot.split('|')[1]:'';
  const vis=rows.filter(keep);
  const groups=new Map();
  vis.forEach(x=>{const k=NL(x.placeName)+'|'+NL(x.province||x.zone);if(!groups.has(k))groups.set(k,{x,list:[],places:new Set()});groups.get(k).list.push(x);groups.get(k).places.add(x.site+'|'+x.place);});
  if(done){
    const fail=rows.filter(x=>!x.estado).length,hid=rows.length-vis.length-fail,disp=vis.reduce((a,x)=>a+(x.estado?x.estado.disponibles:0),0),wl=vis.reduce((a,x)=>a+(x.estado?x.estado.espera:0),0);
    $('#sub1').textContent=`${groups.size} localidades · ${vis.length} combinaciones con plaza`+(hid?` · ${hid} descartadas por no tener plazas`:'')+(fail?` · ${fail} no se pudieron comprobar`:'')+(hname?` · hotel: ${hname}`:'');
    $('#kpis').innerHTML=`<div class="kpi"><b>${groups.size}</b><span>localidades</span></div><div class="kpi"><b>${vis.length}</b><span>origen × localidad</span></div><div class="kpi"><b class="st-ok">${disp}</b><span>fechas disponibles</span></div><div class="kpi"><b class="st-warn">${wl}</b><span>fechas lista espera</span></div>`;
    if(!vis.length)$('#msg1').innerHTML='<div class="msg">Todo lo que cumple los filtros está completo ahora mismo. Prueba a marcar «incluir solo lista de espera» o cambia de fechas/estancia.</div>';
  }
  $('#list').innerHTML=[...groups.values()].map(({x,list,places})=>{
    const hs=META.hotels.filter(h=>h.towns.some(c=>places.has(h.site+'|'+c))&&(!hname||h.name===hname));
    const sites=[...new Set(list.map(y=>y.site))];
    return `<div class="place"><div class="ph">${sites.map(siteTag).join(' ')}<span class="nm">${esc(x.placeName)}</span><span class="wh">${esc(x.province)}${x.zone&&x.zone!==x.province?' · '+esc(x.zone):''}</span>${hs.length?`<span class="hot">🏨 ${hs.map(h=>`<span class="hl" data-s="${esc(h.site)}" data-c="${esc(h.code||'')}" data-h="${esc(h.name)}">${esc(h.name)}</span>`).join(' · ')}</span>`:''}</div>
    <table><thead><tr><th>Origen</th><th>Programa</th><th>Estancias</th><th>Plazas</th><th>Primera · última salida</th><th></th></tr></thead><tbody>${list.sort((a,b)=>(a.originName==='SIN TRANSPORTE')-(b.originName==='SIN TRANSPORTE')||a.originName.localeCompare(b.originName)).map(y=>{
      const e=y.estado,i=rows.indexOf(y);
      const pl=!e?'<span class="pill g">comprobando…</span>':`${e.disponibles?`<span class="pill ok">● ${e.disponibles} disponible${e.disponibles>1?'s':''}</span> `:''}${e.espera?`<span class="pill warn">◐ ${e.espera} lista espera</span> `:''}${e.completos?`<span class="pill bad">✕ ${e.completos} completos</span>`:''}`;
      return `<tr class="r"><td><b>${esc(y.originName==='SIN TRANSPORTE'?'Sin transporte':y.originName)}</b>${y.originName==='SIN TRANSPORTE'?'<br><span class="mut" style="font-size:12px">voy por mi cuenta</span>':''}</td><td><span class="tag p">${esc(y.subType)}</span>${sites.length>1?'<br>'+siteTag(y.site):''}</td><td>${y.stays.map(s=>`<span class="tag">${esc(s)}</span>`).join('')}</td><td>${pl}</td><td>${e&&e.primera?`${fmtDate(e.primera)} · ${fmtDate(e.ultima)}`:'—'}</td><td style="text-align:right"><button class="mini fechas" data-i="${i}" ${e?'':'disabled'}>Ver fechas y precios</button></td></tr>`;}).join('')}</tbody></table></div>`;}).join('');
  document.querySelectorAll('.fechas').forEach(b=>b.onclick=()=>fechas(rows[b.dataset.i]));
  document.querySelectorAll('#list .hl').forEach(e=>e.onclick=()=>openHotel(e.dataset.s,e.dataset.c,e.dataset.h));
}
// ---------- modal fechas ----------
function stClass(s){s=(s||'').toLowerCase();return s.includes('disponible')?'st-ok':s.includes('espera')?'st-warn':'st-bad';}
function renderCal(){
  const by={};days2.forEach(([d,st])=>{by[d]=st;});
  const months=[...new Set(days2.map(d=>d[0].slice(0,7)))].sort();
  $('#cal').innerHTML=months.map(m=>{const [y,mo]=m.split('-').map(Number);const first=new Date(y,mo-1,1);const off=(first.getDay()+6)%7;const n=new Date(y,mo,0).getDate();
    let cells='';for(let i=0;i<off;i++)cells+='<span></span>';
    for(let d=1;d<=n;d++){const k=`${m}-${String(d).padStart(2,'0')}`;const st=by[k];const c=st==='disponible'?'ok':st==='lista-espera'?'warn':st==='completo'?'bad':'';cells+=`<span class="d ${c} ${day2===k?'sel':''}" data-d="${k}" title="${st?st.replace('-',' de '):''}">${d}</span>`;}
    return `<div class="mon"><h4>${MES[mo-1]} ${y}</h4><div class="dow"><span>L</span><span>M</span><span>X</span><span>J</span><span>V</span><span>S</span><span>D</span></div><div class="days">${cells}</div></div>`;}).join('')||'<span class="mut">Sin calendario</span>';
  document.querySelectorAll('.d.ok,.d.warn').forEach(e=>e.onclick=()=>{day2=day2===e.dataset.d?'':e.dataset.d;renderCal();render2();});
}
function render2(){
  const list=rows2.filter(y=>(!filt2||stClass(y.status)===filt2)&&(!day2||y.date===day2));
  $('#tb2').innerHTML=list.map(y=>`<tr class="r"><td><b>${esc(fmtDate(y.date))}</b>${y.endDate?`<br><span class="mut" style="font-size:12px">hasta ${esc(fmtDate(y.endDate))}</span>`:''}</td><td class="${stClass(y.status)}">${esc(y.status)}${y.waiting!=null?`<br><span class="mut" style="font-weight:400;font-size:12px">${y.waiting} en lista</span>`:''}</td><td>${(y.hotels&&y.hotels.length?y.hotels:[{name:y.hotel,code:y.hotelCode}]).map(h=>`<span class="hl" data-s="${esc(y.site)}" data-c="${esc(h.code||'')}" data-h="${esc(h.name)}">${esc(h.name)}</span>`).join(' + ')}<br><span class="mut" style="font-size:12px">${esc(y.town)} · ${esc(y.transport)||'sin transporte'} · mascotas: ${esc(y.pets)}</span></td><td>${esc(y.days)}</td><td>${esc(y.hour)||'—'}</td><td><b>${esc(y.price)}</b></td></tr>`).join('')||`<tr><td colspan="6" class="mut">Nada para ${day2?'el día '+fmtDate(day2):'este filtro'}.</td></tr>`;
  document.querySelectorAll('#tb2 .hl').forEach(e=>e.onclick=()=>openHotel(e.dataset.s,e.dataset.c,e.dataset.h));
}
let cur2=null;
async function fechas(x,force){cur2=x;
  showErr('');busy(true);rows2=[];days2=[];filt2='';day2='';$('#tb2').innerHTML='';$('#cal').innerHTML='';$('#msg2').innerHTML='<p class="mut">Leyendo fechas y precios…</p>';$('#sum2').innerHTML='';$('#chips').innerHTML='';
  $('#t2').textContent=`${x.placeName} · desde ${x.originName==='SIN TRANSPORTE'?'sin transporte':x.originName}`;$('#t2s').textContent=`${x.province||''}${x.zone&&x.zone!==x.province?' · '+x.zone:''} · ${x.subType} · ${x.host}`;
  $('#ov2').classList.add('open');
  try{
    const hot=sel('hotel'),hname=hot?hot.split('|')[1]:'';
    const r=await runJob('/api/fechas',{site:x.site,origin:x.origin,place:x.place,stay:sel('stay'),hotel:hname,force:!!force});
    rows2=r.rows;days2=r.days||[];filt2=$('#incwl').checked?'':'st-ok';
    const ok=rows2.filter(y=>stClass(y.status)==='st-ok').length,wl=rows2.filter(y=>stClass(y.status)==='st-warn').length;
    const prices=rows2.map(y=>parseFloat((y.price||'').replace(',','.'))).filter(n=>!isNaN(n));
    $('#sum2').innerHTML=`<div class="kpi"><b>${r.fechas}</b><span>fechas con salida</span></div><div class="kpi"><b class="st-ok">${ok}</b><span>viajes disponibles</span></div><div class="kpi"><b class="st-warn">${wl}</b><span>lista de espera</span></div><div class="kpi"><b class="st-bad">${r.completos}</b><span>días completos</span></div>${prices.length?`<div class="kpi"><b>${Math.min(...prices).toFixed(2)} €</b><span>desde</span></div>`:''}`;
    $('#chips').innerHTML=`<span class="chip ${filt2===''?'on':''}" data-f="">Todo (${rows2.length})</span><span class="chip ${filt2==='st-ok'?'on':''}" data-f="st-ok">Disponible (${ok})</span><span class="chip ${filt2==='st-warn'?'on':''}" data-f="st-warn">Lista de espera (${wl})</span>`;
    document.querySelectorAll('.chip').forEach(c=>c.onclick=()=>{filt2=c.dataset.f;document.querySelectorAll('.chip').forEach(d=>d.classList.toggle('on',d===c));render2();});
    $('#msg2').innerHTML=`<div class="mut" style="margin-bottom:10px">${hname?`Solo el hotel «${esc(hname)}». `:''}${r.snapshot?`Datos del ${new Date(r.snapshot*1000).toLocaleString('es-ES',{day:'2-digit',month:'2-digit',hour:'2-digit',minute:'2-digit'})} · pulsa ↻ Actualizar para consultar ahora.`:'Consultado ahora mismo.'}</div>`;
    renderCal();render2();
  }catch(e){$('#msg2').innerHTML=`<div class="err">⚠️ ${esc(e.message)}</div>`}finally{busy(false)}
}
// ---------- modal hotel ----------
async function openHotel(site,code,name){
  $('#mtitle').textContent=name;$('#msub').textContent='';$('#mbody').innerHTML='<p class="mut">Cargando ficha…</p>';$('#mfoot').innerHTML='';$('#ov').classList.add('open');
  const h=META.hotels.find(x=>x.site===site&&x.name===name);
  const where=h?h.towns.map(c=>{const t=META.towns.find(t=>t.site===site&&t.code===c);return t?`${t.name} (${t.province||t.zone}) · ${t.subType}`:c;}).join(' · '):'';
  $('#msub').textContent=where;if(!code&&h)code=h.code;
  try{
    if(!code)throw new Error('sin código de hotel');
    const r=await api('/api/hotel',{site,code});if(r.error)throw new Error(r.error);
    const gal=r.images.length?`<div class="gal"><img class="big" id="big" src="${esc(r.images[0])}" alt=""><div class="thumbs">${r.images.map((u,i)=>`<img src="${esc(u)}" class="${i?'':'on'}" data-u="${esc(u)}" alt="">`).join('')}</div></div>`:'<div class="mut">Sin fotos</div>';
    $('#mbody').innerHTML=gal+`<div>${r.paras.map(p=>`<p>${p}</p>`).join('')}${r.services.length?`<p><b>Servicios</b></p><ul class="svc">${r.services.map(s=>`<li>${esc(s)}</li>`).join('')}</ul>`:''}</div>`;
    document.querySelectorAll('.thumbs img').forEach(t=>t.onclick=()=>{$('#big').src=t.dataset.u;document.querySelectorAll('.thumbs img').forEach(x=>x.classList.toggle('on',x===t));});
    $('#mfoot').innerHTML=(r.maps?`<a href="${esc(r.maps)}" target="_blank" rel="noopener"><button class="sec mini">🗺 Ver mapa</button></a>`:'')+`<a href="https://${esc(r.host)}/scheduler" target="_blank" rel="noopener"><button class="sec mini">Abrir ${esc(r.host)}</button></a>`;
  }catch(e){$('#mbody').innerHTML=`<p class="mut">No se ha podido cargar la ficha: ${esc(e.message)}</p><p>${esc(where)}</p>`;}
}
$('#mclose').onclick=()=>$('#ov').classList.remove('open');$('#ov').onclick=e=>{if(e.target.id==='ov')$('#ov').classList.remove('open')};
$('#mclose2').onclick=()=>$('#ov2').classList.remove('open');$('#refresh2').onclick=()=>{if(cur2)fechas(cur2,true);};$('#ov2').onclick=e=>{if(e.target.id==='ov2')$('#ov2').classList.remove('open')};
document.addEventListener('keydown',e=>{if(e.key==='Escape'){if($('#ov').classList.contains('open'))$('#ov').classList.remove('open');else $('#ov2').classList.remove('open');}});
$('#buscar').onclick=buscar;
$('#limpiar').onclick=()=>{['site','zona','prov','localidad','hotel','origen','stay'].forEach(id=>$('#'+id).value='');$('#incwl').checked=false;cascade();saveF();$('#res1').style.display='none';showErr('');};
$('#reindex').onclick=async()=>{showErr('');busy(true);try{const r=await runJob('/api/reindex',{});await loadMeta();$('#help').textContent=`Catálogo actualizado: ${r.n} hoteles.`;}catch(e){showErr(e.message)}finally{busy(false)}};
$('#incwl').onchange=()=>{saveF();if(rows.length)render1(true);};
loadMeta();
</script></body></html>
"""


AUTH_USER = os.environ.get("IMSERSO_USER", "imserso")
AUTH_PASS = os.environ.get("IMSERSO_PASS", "")


class Handler(http.server.BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def _authed(self):
        if not AUTH_PASS:
            return True
        import base64
        import hmac
        h = self.headers.get("Authorization") or ""
        if h.startswith("Basic "):
            try:
                u, _, pw = base64.b64decode(h[6:]).decode("utf-8").partition(":")
                if hmac.compare_digest(u, AUTH_USER) and hmac.compare_digest(pw, AUTH_PASS):
                    return True
            except Exception:
                pass
        self.send_response(401)
        self.send_header("WWW-Authenticate", 'Basic realm="Buscador IMSERSO", charset="UTF-8"')
        self.send_header("Content-Length", "0")
        self.end_headers()
        return False

    def _send(self, b, ctype, code=200, cache=None):
        import gzip
        if len(b) > 1400 and "gzip" in (self.headers.get("Accept-Encoding") or ""):
            b = gzip.compress(b, 6)
            enc = True
        else:
            enc = False
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        if enc:
            self.send_header("Content-Encoding", "gzip")
        if cache:
            self.send_header("Cache-Control", cache)
        self.send_header("Content-Length", str(len(b)))
        self.end_headers()
        self.wfile.write(b)

    def _json(self, obj, code=200):
        self._send(json.dumps(obj, ensure_ascii=False, separators=(",", ":")).encode("utf-8"), "application/json; charset=utf-8", code)

    def do_GET(self):
        if self.path == "/ping":
            self.send_response(204)
            self.end_headers()
            return
        if not self._authed():
            return
        if self.path == "/" or self.path.startswith("/index") or self.path.startswith("/?"):
            ui = os.path.join(os.path.dirname(os.path.abspath(__file__)), "ui.html")
            try:
                with open(ui, encoding="utf-8") as f:
                    page = f.read()
            except OSError:
                page = HTML
            self._send(page.encode("utf-8"), "text/html; charset=utf-8", cache="no-cache")
        elif self.path == "/api/all":
            self._json(dict(ts=PRE["ts"], rows=all_rows()))
        elif self.path == "/api/meta":
            for s in SITES.values():
                try:
                    s.load()
                except Exception as e:  # noqa
                    log("no se pudo cargar", s.host, e)
            self._json(meta())
        elif self.path.startswith("/api/job/"):
            self._json(JOBS.get(self.path.rsplit("/", 1)[1]) or {"done": True, "error": "trabajo desconocido"})
        else:
            self.send_error(404)

    def do_POST(self):
        if not self._authed():
            return
        n = int(self.headers.get("Content-Length") or 0)
        p = json.loads(self.rfile.read(n) or b"{}")
        try:
            if self.path == "/api/listado":
                self._json({"job": job_listado(p)})
            elif self.path == "/api/buscar":
                self._json({"job": job_buscar(p)})
            elif self.path == "/api/fechas":
                self._json({"job": job_fechas(p)})
            elif self.path == "/api/estado":
                self._json({"job": job_estado(p)})
            elif self.path == "/api/reindex":
                self._json({"job": job_reindex(p)})
            elif self.path == "/api/hotel":
                self._json(SITES[p["site"]].hotel_info(p["code"]))
            else:
                self.send_error(404)
        except Exception as e:  # noqa
            self._json({"error": str(e)}, 200)


def free_port(pref=8765):
    for port in range(pref, pref + 20):
        with socket.socket() as s:
            s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            try:
                s.bind(("127.0.0.1", port))
                return port
            except OSError:
                continue
    return 0


# --------------------------------------------------------------------------- #
#  Terminal:  python3 imserso_finder.py --hotel "villa naranjos" --fechas
# --------------------------------------------------------------------------- #
def cli(args):
    import argparse
    ap = argparse.ArgumentParser(description="Buscador IMSERSO por hotel / localidad")
    ap.add_argument("--hotel", help="nombre (o parte) del hotel")
    ap.add_argument("--localidad", help="nombre (o parte) de la localidad")
    ap.add_argument("--origen", help="filtrar por origen (nombre)")
    ap.add_argument("--stay", choices=list(STAYS), help="estancia")
    ap.add_argument("--site", choices=list(SITES), help="solo una web")
    ap.add_argument("--fechas", action="store_true", help="además, fechas y precios de cada origen")
    ap.add_argument("--reindex", action="store_true", help="reconstruir el catálogo de hoteles")
    a = ap.parse_args(args)

    def wait(jid):
        while not JOBS[jid]["done"]:
            print("\r" + JOBS[jid]["progress"][:110].ljust(110), end="", flush=True)
            time.sleep(0.5)
        print("\r" + " " * 110 + "\r", end="")
        if JOBS[jid]["error"]:
            sys.exit(JOBS[jid]["error"])
        return JOBS[jid]["result"]

    if a.reindex:
        print("Catálogo:", wait(job_reindex({}))["n"], "hoteles")
        if not (a.hotel or a.localidad):
            return
    r = wait(job_buscar(vars(a)))
    if r.get("msg"):
        print(r["msg"])
    if r.get("hotelMatches"):
        print("Hotel:", " · ".join(r["hotelMatches"]))
    for x in r["rows"]:
        print(f"{x['host']:<22} {x['placeName']:<28} {x['originName']:<24} {', '.join(x['stays'])}")
        if a.fechas:
            d = dates_for(SITES[x["site"]], x["origin"], x["place"], a.stay, a.hotel)
            for y in d["rows"]:
                print(f"    {y['date']}  {y['status']:<16} {y['hotel']:<45} {y['days']:<8} {y['price']}")


def main():
    if len(sys.argv) > 2 and sys.argv[1] == "--snapshot":
        for s_ in SITES.values():
            s_.load()
        if not INDEX.ready():
            INDEX.build()
        return build_snapshot(sys.argv[2])
    if len(sys.argv) > 1:
        return cli(sys.argv[1:])
    port = int(os.environ.get("PORT") or 0) or free_port()
    on_cloud = bool(os.environ.get("RENDER"))
    srv = http.server.ThreadingHTTPServer((os.environ.get("HOST", "0.0.0.0" if on_cloud else "127.0.0.1"), port), Handler)
    url = f"http://127.0.0.1:{port}/"
    log("Buscador IMSERSO en", url, "— cierra esta ventana para parar")
    if not (os.environ.get("HEADLESS") or on_cloud):
        threading.Thread(target=lambda: (time.sleep(0.6), webbrowser.open(url)), daemon=True).start()
    threading.Thread(target=warm_configs, daemon=True).start()
    threading.Thread(target=snapshot_loop, daemon=True).start()
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
