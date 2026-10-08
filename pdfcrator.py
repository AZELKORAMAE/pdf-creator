"""
PDF Merger Pro V3.0 — Safran Engineering Services
Éditeur de page façon pdfFiller :
  • Détection automatique de TOUS les textes de la page
  • Modification directe sur la page (clic → saisie → Entrée)
  • Remplacement RÉEL du texte (le copier-coller donne le nouveau texte)
  • Police, taille, gras, italique, couleur et arrière-plan d'origine conservés
  • Déplacement, rotation du texte, pipette de couleur, ajout de texte

pip install PyPDF2 PyMuPDF Pillow
"""

import tkinter as tk
from tkinter import filedialog, messagebox, ttk, colorchooser
from tkinter import font as tkfont
from pathlib import Path
import threading
import copy
import hashlib
import math
import re
import struct
import subprocess
import sys
import tempfile
import os

try:
    import fitz
    HAS_FITZ = True
except ImportError:
    HAS_FITZ = False

try:
    from PIL import Image, ImageTk
    HAS_PIL = True
except ImportError:
    HAS_PIL = False

try:
    import PyPDF2
    HAS_PYPDF2 = True
except ImportError:
    HAS_PYPDF2 = False

C = {
    "navy":      "#00356B",  "navy2":     "#002855",
    "blue":      "#0078BE",  "blue_h":    "#005A9E",
    "blue_lt":   "#E0EEF8",  "orange":    "#E8540A",
    "white":     "#FFFFFF",  "bg":        "#F2F5FA",
    "bg2":       "#E6ECF5",  "line":      "#CDD4E0",
    "mid":       "#8A95AA",  "text":      "#1E2D45",
    "ok":        "#1A7F4B",  "warn":      "#C0390B",
    "drop":      "#BEDCF4",  "selected":  "#0078BE",
    "sel_bg":    "#D6E9F7",  "edit_sel":  "#E8540A",
    "char_sel":  "#3B82F6",  # bleu Word-like pour sélection caractères
    "char_sel_bg": "#BFDBFE",
    "handle":    "#0078BE",  # poignées de redimensionnement
}

THUMB_W = 118
THUMB_H = 155
CARD_W  = THUMB_W + 12
CARD_H  = THUMB_H + 60
PAD_X   = 12
PAD_Y   = 14

# ══════════════════════════════════════════════════════════════════════════════
#  MOTEUR TEXTE  —  détection des textes, polices, remplacement réel
# ══════════════════════════════════════════════════════════════════════════════
LINE_H = 1.2

_STYLE_SUFFIXES = ("bolditalic", "boldoblique", "semibold", "demibold", "extrabold",
                   "bold", "italic", "oblique", "regular", "medium", "normal",
                   "book", "mt", "ps")

FAMILY_ALIASES = {
    "helvetica":     ["arial", "liberationsans", "nimbussans", "freesans", "dejavusans"],
    "arial":         ["helvetica", "liberationsans", "nimbussans", "freesans", "dejavusans"],
    "times":         ["timesnewroman", "liberationserif", "nimbusroman", "freeserif", "dejavuserif"],
    "timesnewroman": ["times", "liberationserif", "nimbusroman", "freeserif", "dejavuserif"],
    "courier":       ["couriernew", "liberationmono", "nimbusmono", "freemono", "dejavusansmono"],
    "couriernew":    ["courier", "liberationmono", "nimbusmono", "freemono", "dejavusansmono"],
    "calibri":       ["carlito", "arial", "liberationsans"],
    "cambria":       ["caladea", "timesnewroman", "liberationserif"],
}


def font_family_key(name):
    """'ABCDEF+Arial-BoldMT' -> 'arial' ; 'Times New Roman Bold' -> 'timesnewroman'."""
    if not name:
        return ""
    n = name.split("+", 1)[-1]
    n = re.split(r"[-,]", n, maxsplit=1)[0]
    n = re.sub(r"[^a-z0-9]", "", n.lower())
    changed = True
    while changed:
        changed = False
        for suf in _STYLE_SUFFIXES:
            if n.endswith(suf) and len(n) > len(suf) + 1:
                n = n[: -len(suf)]
                changed = True
                break
    return n


def font_display_name(name):
    """Nom lisible d'une police : 'ABCDEF+TimesNewRomanPS-BoldMT' -> 'Times New Roman'."""
    if not name:
        return ""
    n = name.split("+", 1)[-1]
    n = re.split(r"[-,]", n, maxsplit=1)[0]
    n = re.sub(r"(?i)\s+(bold|italic|oblique|regular|semibold|medium)\b.*$", "", n).strip()
    n = re.sub(r"(PSMT|MT|PS)$", "", n)
    if " " not in n:
        n = re.sub(r"(?<=[a-z])(?=[A-Z])", " ", n)
    return n.strip() or name


def base14_name(fam_key, bold, italic):
    if any(t in fam_key for t in ("courier", "mono", "consol")):
        base = "cour"
    elif "sans" not in fam_key and any(t in fam_key for t in
            ("times", "roman", "serif", "georgia", "garamond", "cambria", "book", "palatino")):
        base = "tiro"
    else:
        base = "helv"
    table = {
        ("helv", False, False): "helv", ("helv", True, False): "hebo",
        ("helv", False, True): "heit",  ("helv", True, True): "hebi",
        ("tiro", False, False): "tiro", ("tiro", True, False): "tibo",
        ("tiro", False, True): "tiit",  ("tiro", True, True): "tibi",
        ("cour", False, False): "cour", ("cour", True, False): "cobo",
        ("cour", False, True): "coit",  ("cour", True, True): "cobi",
    }
    return table[(base, bool(bold), bool(italic))]


def _sfnt_info(path):
    """(famille, gras, italique) lus dans les tables 'name' et 'OS/2' d'un .ttf/.otf
    (sans PyMuPDF, qui n'est pas thread-safe)."""
    with open(path, "rb") as f:
        header = f.read(12)
        if len(header) < 12:
            return None
        num = struct.unpack(">H", header[4:6])[0]
        if not 0 < num < 200:
            return None
        directory = f.read(16 * num)
        tables = {}
        for i in range(num):
            tag, _, off, length = struct.unpack(">4sIII", directory[i * 16:(i + 1) * 16])
            tables[tag] = (off, length)
        if b"name" not in tables:
            return None
        off, length = tables[b"name"]
        f.seek(off)
        table = f.read(length)
        _, count, str_off = struct.unpack(">HHH", table[:6])
        names = {}
        for i in range(count):
            rec = table[6 + i * 12: 18 + i * 12]
            if len(rec) < 12:
                break
            pid, eid, lid, nid, ln, so = struct.unpack(">HHHHHH", rec)
            if nid not in (1, 2):
                continue
            raw = table[str_off + so: str_off + so + ln]
            try:
                if pid == 3:
                    text, rank = raw.decode("utf-16-be"), (0 if lid == 0x409 else 1)
                elif pid == 1 and eid == 0:
                    text, rank = raw.decode("latin-1"), 2
                else:
                    continue
            except UnicodeDecodeError:
                continue
            if nid not in names or rank < names[nid][0]:
                names[nid] = (rank, text)
        family = names.get(1, (0, ""))[1].strip()
        sub = names.get(2, (0, ""))[1].lower()
        bold = any(w in sub for w in ("bold", "black", "heavy"))
        italic = "italic" in sub or "oblique" in sub
        if b"OS/2" in tables and tables[b"OS/2"][1] >= 64:
            f.seek(tables[b"OS/2"][0] + 62)
            fs = struct.unpack(">H", f.read(2))[0]
            bold = bold or bool(fs & 0x20)
            italic = italic or bool(fs & 0x01)
        return (family, bold, italic) if family else None


class FontManager:
    """Index des polices installées sur le poste (Windows / macOS / Linux)."""
    _index = None
    _display = {}
    _lock = threading.Lock()
    _fonts = {}

    @staticmethod
    def _font_dirs():
        dirs = []
        if sys.platform.startswith("win"):
            dirs.append(os.path.join(os.environ.get("WINDIR", r"C:\Windows"), "Fonts"))
            local = os.environ.get("LOCALAPPDATA")
            if local:
                dirs.append(os.path.join(local, "Microsoft", "Windows", "Fonts"))
        elif sys.platform == "darwin":
            dirs += ["/System/Library/Fonts", "/Library/Fonts",
                     os.path.expanduser("~/Library/Fonts")]
        else:
            dirs += ["/usr/share/fonts", "/usr/local/share/fonts",
                     os.path.expanduser("~/.fonts"), os.path.expanduser("~/.local/share/fonts")]
        return [d for d in dirs if os.path.isdir(d)]

    @classmethod
    def index(cls):
        with cls._lock:
            if cls._index is None:
                idx = {}
                for d in cls._font_dirs():
                    for root, _, files in os.walk(d):
                        for f in files:
                            if not f.lower().endswith((".ttf", ".otf")):
                                continue
                            path = os.path.join(root, f)
                            try:
                                info = _sfnt_info(path)
                            except (OSError, struct.error):
                                continue
                            if not info:
                                continue
                            name, bold, italic = info
                            fam = font_family_key(name)
                            if not fam:
                                continue
                            idx.setdefault(fam, []).append((path, bold, italic))
                            cls._display.setdefault(fam, name)
                cls._index = idx
            return cls._index

    @classmethod
    def display(cls, fam_key):
        cls.index()
        return cls._display.get(fam_key, fam_key)

    @classmethod
    def families(cls):
        idx = cls.index()
        names = {cls._display.get(k, k) for k in idx}
        names.update(("Helvetica", "Times", "Courier"))
        return sorted(names, key=str.lower)

    @classmethod
    def find_file(cls, fam_key, bold, italic):
        idx = cls.index()
        for key in [fam_key] + FAMILY_ALIASES.get(fam_key, []):
            cands = idx.get(key)
            if cands:
                best = max(cands, key=lambda c: (c[1] == bool(bold)) * 2 + (c[2] == bool(italic)))
                return best[0]
        return None

    @classmethod
    def font(cls, key, path=None, buffer=None, base14=None):
        f = cls._fonts.get(key)
        if f is None:
            if path:
                f = fitz.Font(fontfile=path)
            elif buffer:
                f = fitz.Font(fontbuffer=buffer)
            else:
                f = fitz.Font(base14)
            cls._fonts[key] = f
        return f


def _covers(font, text):
    """Vrai si la police contient un vrai glyphe pour chaque caractère du texte
    (les polices 'subset' des PDF n'ont souvent que les lettres déjà utilisées)."""
    try:
        for ch in set(text):
            if ch.isspace():
                continue
            if not font.has_glyph(ord(ch)):
                return False
            if font.glyph_bbox(ord(ch)).is_empty:
                return False
        return True
    except Exception:
        return False


def _embedded_font_buffer(page, orig_font):
    target = (orig_font or "").split("+", 1)[-1]
    try:
        for f in page.get_fonts(full=True):
            xref, ext, ftype, basefont = f[0], f[1], f[2], f[3]
            if ext == "n/a" or ftype == "Type3":
                continue
            if basefont.split("+", 1)[-1] == target:
                buf = page.parent.extract_font(xref)[3]
                if buf:
                    return buf
    except Exception:
        pass
    return None


def resolve_font(page, ed, cache=None):
    """Choisit la police à utiliser pour écrire ed.text, par ordre de fidélité :
    1. la police intégrée au PDF (si style inchangé et tous les glyphes présents)
    2. la même famille installée sur le poste (Arial, Calibri, Times…)
    3. la police PDF standard la plus proche.
    Renvoie (kind, value, fitz.Font, key) avec kind in 'buffer' | 'file' | 'base14'."""
    cache = {} if cache is None else cache
    text = ed.text or ""
    ck = ("res", ed.family, ed.orig_font, bool(ed.bold), bool(ed.italic), ed.orig_style, text)
    if ck in cache:
        return cache[ck]
    res = None
    fam = font_family_key(ed.family)
    same_style = (ed.orig_font and ed.family == ed.orig_font
                  and ed.orig_style == (bool(ed.bold), bool(ed.italic)))
    if same_style and page is not None:
        bk = ("emb", ed.orig_font)
        if bk not in cache:
            cache[bk] = _embedded_font_buffer(page, ed.orig_font)
        buf = cache[bk]
        if buf:
            key = "emb:" + hashlib.md5(buf).hexdigest()
            try:
                font = FontManager.font(key, buffer=buf)
                if _covers(font, text):
                    res = ("buffer", buf, font, key)
            except Exception:
                pass
    if res is None:
        path = FontManager.find_file(fam, ed.bold, ed.italic)
        if path:
            try:
                font = FontManager.font(path, path=path)
                if _covers(font, text):
                    res = ("file", path, font, path)
            except Exception:
                pass
    if res is None:
        b14 = base14_name(fam, ed.bold, ed.italic)
        res = ("base14", b14, FontManager.font(b14, base14=b14), b14)
    cache[ck] = res
    return res


def text_rect(font, text, size, origin, angle=0.0):
    lines = (text or " ").split("\n")
    width = max(font.text_length(line, fontsize=size) for line in lines)
    asc = font.ascender or 0.9
    desc = font.descender or -0.25
    x, y = origin
    r = fitz.Rect(x, y - asc * size, x + max(width, size * 0.5),
                  y - desc * size + (len(lines) - 1) * size * LINE_H)
    if angle:
        # insert_text's morph works in PDF space (y up), Rect.morph in page space (y down)
        r = r.morph(fitz.Point(origin), fitz.Matrix(-angle)).rect
    return r


def _span_style(span):
    fname = span.get("font", "") or ""
    low = fname.lower()
    flags = span.get("flags", 0)
    bold = bool(flags & 16) or any(w in low for w in ("bold", "black", "heavy", "semibold", "demi"))
    italic = bool(flags & 2) or "italic" in low or "oblique" in low
    c = span.get("color", 0)
    rgb = (((c >> 16) & 255) / 255.0, ((c >> 8) & 255) / 255.0, (c & 255) / 255.0)
    return fname, round(span.get("size", 11.0), 2), rgb, bold, italic


def _erase_rects(chars, size, angle):
    """Zones de redaction qui touchent toutes les lettres du segment (et ses
    espaces de bord) mais aucune lettre voisine : MuPDF supprime tout caractère
    que la zone touche, d'où le retrait de 30 % aux extrémités."""
    vis = [c for c in chars if not c["c"].isspace()]
    if not vis:
        return []
    if angle == 0.0:
        first, last = chars[0]["bbox"], chars[-1]["bbox"]
        oy = vis[0]["origin"][1]
        x0 = first[0] + 0.3 * max(0.2, first[2] - first[0])
        x1 = last[2] - 0.3 * max(0.2, last[2] - last[0])
        if x1 <= x0:
            x1 = x0 + 0.1
        return [(x0, oy - size * 0.5, x1, oy - size * 0.2)]
    out = []
    h = max(0.2, size * 0.08)
    for c in vis:
        b = c["bbox"]
        cx, cy = (b[0] + b[2]) / 2, (b[1] + b[3]) / 2
        out.append((cx - h, cy - h, cx + h, cy + h))
    return out


def extract_segments(page):
    """Détecte tous les textes de la page, découpés en segments de style homogène
    (même police, taille, couleur, gras, italique) — comme pdfFiller."""
    flags = fitz.TEXT_PRESERVE_WHITESPACE | fitz.TEXT_MEDIABOX_CLIP
    raw = page.get_text("rawdict", flags=flags)
    segs = []

    def flush(cur):
        if not cur:
            return
        chars = cur["chars"]
        lead, trail = list(cur["lead"]), []
        while chars and chars[0]["c"].isspace():
            lead.append(chars.pop(0))
        while chars and chars[-1]["c"].isspace():
            trail.insert(0, chars.pop())
        if not chars:
            return
        fname, size, rgb, bold, italic = cur["style"]
        bb = fitz.Rect(chars[0]["bbox"])
        for c in chars[1:]:
            bb |= fitz.Rect(c["bbox"])
        o = chars[0]["origin"]
        segs.append({
            "key": len(segs),
            "text": "".join(c["c"] for c in chars),
            "bbox": tuple(bb),
            "origin": (o[0], o[1]),
            "size": size, "font": fname, "bold": bold, "italic": italic,
            "color": rgb, "angle": cur["angle"],
            "erase": _erase_rects(lead + chars + trail, size, cur["angle"]),
            "chars": [tuple(c["bbox"]) for c in chars],
        })

    for block in raw.get("blocks", []):
        if block.get("type", 0) != 0:
            continue
        for line in block.get("lines", []):
            dx, dy = line.get("dir", (1.0, 0.0))
            angle = round(math.degrees(math.atan2(-dy, dx)), 2)
            if abs(angle) < 0.05:
                angle = 0.0
            cur = None
            pending = []
            for span in line.get("spans", []):
                style = _span_style(span)
                size = style[1]
                for ch in span.get("chars", []):
                    is_space = ch["c"].isspace()
                    wide_gap = is_space and (ch["bbox"][2] - ch["bbox"][0]) > size * 1.2
                    if cur is not None:
                        prev = cur["chars"][-1]
                        gap = ch["bbox"][0] - prev["bbox"][2] if angle == 0.0 else 0
                        if cur["style"] != style or wide_gap or gap > size * 1.2:
                            flush(cur)
                            cur = None
                    if cur is None:
                        if is_space:
                            pending = [] if wide_gap else pending + [ch]
                            continue
                        cur = {"style": style, "angle": angle, "chars": [], "lead": pending}
                        pending = []
                    cur["chars"].append(ch)
            flush(cur)
    return segs


def _apply_redactions(page):
    images = getattr(fitz, "PDF_REDACT_IMAGE_NONE", 0)
    try:
        page.apply_redactions(images=images,
                              graphics=getattr(fitz, "PDF_REDACT_LINE_ART_NONE", 0))
    except TypeError:
        page.apply_redactions(images=images)


def apply_edits_to_page(page, edits, cache=None):
    """Applique les édits : suppression RÉELLE du texte d'origine (sans toucher
    à l'arrière-plan), puis écriture du nouveau texte au même endroit."""
    if not edits:
        return
    cache = {} if cache is None else cache
    rot = page.rotation
    if rot:
        page.set_rotation(0)
    try:
        writes = [(ed, resolve_font(page, ed, cache)) for ed in edits
                  if ed.kind in ("replace", "add") and (ed.text or "").strip()]
        n = 0
        for ed in edits:
            if ed.kind in ("replace", "delete"):
                for r in ed.erase or []:
                    page.add_redact_annot(fitz.Rect(r), fill=False)
                    n += 1
        if n:
            _apply_redactions(page)
        inserted = set()
        for ed, (kind, value, font, key) in writes:
            origin = fitz.Point(ed.origin)
            morph = (origin, fitz.Matrix(ed.angle)) if ed.angle else None
            if ed.bg is not None:
                r = text_rect(font, ed.text, ed.size, ed.origin)
                r = fitz.Rect(r.x0 - 1.5, r.y0 - 1, r.x1 + 1.5, r.y1 + 1)
                page.draw_rect(r, color=None, fill=ed.bg, width=0, morph=morph)
            try:
                if kind == "base14":
                    fontname = value
                else:
                    fontname = "F" + hashlib.md5(str(key).encode()).hexdigest()[:10]
                    if fontname not in inserted:
                        if kind == "buffer":
                            page.insert_font(fontname=fontname, fontbuffer=value)
                        else:
                            page.insert_font(fontname=fontname, fontfile=value)
                        inserted.add(fontname)
                page.insert_text(origin, ed.text, fontname=fontname, fontsize=ed.size,
                                 color=ed.color, lineheight=LINE_H, morph=morph)
            except Exception:
                page.insert_text(origin, ed.text,
                                 fontname=base14_name(font_family_key(ed.family), ed.bold, ed.italic),
                                 fontsize=ed.size, color=ed.color, lineheight=LINE_H, morph=morph)
    finally:
        if rot:
            page.set_rotation(rot)


class Edit:
    """Une modification de texte sur une page.
    kind : 'replace' (texte détecté modifié), 'delete' (texte détecté supprimé),
           'add' (nouveau texte). bg=None conserve l'arrière-plan d'origine."""
    __slots__ = ("kind", "text", "family", "orig_font", "orig_style", "bold", "italic",
                 "size", "color", "bg", "angle", "origin", "erase", "seg_key", "orig", "uid",
                 "pinned")

    def __init__(self, kind, text="", family="Helvetica", size=11.0, color=(0, 0, 0),
                 bg=None, bold=False, italic=False, angle=0.0, origin=(0.0, 0.0),
                 erase=None, seg_key=None, orig_font=None, orig_style=None, uid=None):
        self.kind = kind
        self.text = text
        self.family = family
        self.orig_font = orig_font
        self.orig_style = orig_style
        self.bold = bold
        self.italic = italic
        self.size = size
        self.color = tuple(color)
        self.bg = None if bg is None else tuple(bg)
        self.angle = angle
        self.origin = tuple(origin)
        self.erase = erase or []
        self.seg_key = seg_key
        self.orig = None
        self.uid = uid
        self.pinned = False   # positioned by hand: never shifted by line reflow

    @classmethod
    def from_segment(cls, seg):
        ed = cls("replace", text=seg["text"], family=seg["font"], size=seg["size"],
                 color=seg["color"], bold=seg["bold"], italic=seg["italic"],
                 angle=seg["angle"], origin=seg["origin"], erase=list(seg["erase"]),
                 seg_key=seg["key"], orig_font=seg["font"],
                 orig_style=(seg["bold"], seg["italic"]))
        ed.orig = ed.state()
        return ed

    def state(self):
        return (self.kind, self.text, self.family, bool(self.bold), bool(self.italic),
                round(float(self.size), 2), tuple(round(c, 3) for c in self.color),
                None if self.bg is None else tuple(round(c, 3) for c in self.bg),
                round(float(self.angle), 2),
                (round(self.origin[0], 2), round(self.origin[1], 2)))

    def is_noop(self):
        return self.kind == "replace" and self.orig is not None and self.state() == self.orig


def _hex(rgb):
    return "#{:02x}{:02x}{:02x}".format(*(max(0, min(255, int(round(c * 255)))) for c in rgb))


class Page:
    __slots__ = ("path", "fname", "pg_idx", "photo", "rotation", "edits", "thumb")

    def __init__(self, path, fname, pg_idx):
        self.path     = path
        self.fname    = fname
        self.pg_idx   = pg_idx
        self.photo    = None
        self.rotation = 0
        self.edits    = []
        self.thumb    = None

    def __deepcopy__(self, memo):
        # photo is a Tk image (not copyable); thumb is never mutated, so share it
        p = Page(self.path, self.fname, self.pg_idx)
        p.rotation = self.rotation
        p.edits = copy.deepcopy(self.edits, memo)
        p.thumb = self.thumb
        return p


# ══════════════════════════════════════════════════════════════════════════════
#  MAIN APP
# ══════════════════════════════════════════════════════════════════════════════
class PDFMergerPro:
    def __init__(self, root):
        self.root = root
        self.root.title("PDF Merger Pro V3.0 — Safran Engineering Services")
        self.root.geometry("1240x780")
        self.root.minsize(800, 520)
        self.root.configure(bg=C["navy2"])

        self.pages = []
        self._raw_thumbs = {}
        self._drag_src = None
        self._drag_slot = None
        self._ghost_win = None
        self._dragging = False
        self._selected = None
        self._history = []
        self._hist_idx = -1
        self._max_hist = 50

        self._build_ui()
        self._snapshot()

        for seq, fn in (("<Control-z>", self.undo), ("<Control-Z>", self.undo),
                        ("<Control-y>", self.redo), ("<Control-Y>", self.redo),
                        ("<Control-Shift-Z>", self.redo), ("<Delete>", self.delete_selected)):
            self.root.bind_all(seq, lambda e, fn=fn: self._main_window_shortcut(e, fn))

        if HAS_FITZ:
            threading.Thread(target=FontManager.index, daemon=True).start()

    def _main_window_shortcut(self, event, fn):
        # bind_all also fires in the editor/print windows: only act on the main window
        try:
            if event.widget.winfo_toplevel() is not self.root:
                return
        except (AttributeError, tk.TclError):
            return
        fn()

    # ── UI ──
    def _build_ui(self):
        self._build_header()
        self._build_toolbar()
        self._build_canvas()
        self._build_footer()

    def _build_header(self):
        hdr = tk.Frame(self.root, bg=C["navy2"], height=60)
        hdr.pack(fill=tk.X)
        hdr.pack_propagate(False)
        tk.Frame(hdr, bg=C["orange"], width=6).pack(side=tk.LEFT, fill=tk.Y)
        tk.Label(hdr, text="SAFRAN", font=("Helvetica", 17, "bold"),
                 fg=C["white"], bg=C["navy2"], padx=16).pack(side=tk.LEFT, anchor="w", pady=10)
        tk.Frame(hdr, bg=C["blue"], width=1).pack(side=tk.LEFT, fill=tk.Y, pady=12)
        tk.Label(hdr, text="  PDF Merger Pro  ·  V2.2", font=("Helvetica", 12),
                 fg="#A8CCE8", bg=C["navy2"]).pack(side=tk.LEFT)
        tk.Button(hdr, text="⬇  Fusionner & Exporter", command=self.merge_pdfs,
                  font=("Helvetica", 9, "bold"), bg=C["orange"], fg=C["white"],
                  relief="flat", activebackground=C["warn"],
                  activeforeground=C["white"], cursor="hand2", padx=14, pady=5
                  ).pack(side=tk.RIGHT, padx=18, pady=10)
        # Bouton impression désactivé temporairement
        # tk.Button(hdr, text="🖨  Imprimer", command=self.print_document, ...).pack(...)
        tk.Button(hdr, text="✕  Tout vider", command=self.clear_all,
                  font=("Helvetica", 9), bg="#1A3560", fg="#A8CCE8",
                  relief="flat", cursor="hand2", padx=10, pady=5
                  ).pack(side=tk.RIGHT, padx=4, pady=10)

    def _build_toolbar(self):
        tb = tk.Frame(self.root, bg=C["bg2"], height=44)
        tb.pack(fill=tk.X)
        tb.pack_propagate(False)

        def tbtn(text, cmd, bold=False, accent=False, color=None):
            b = tk.Button(tb, text=text, command=cmd,
                          font=("Helvetica", 8, "bold" if bold else "normal"),
                          bg=color or (C["blue"] if accent else C["white"]),
                          fg=C["white"] if (accent or color) else C["text"],
                          relief="flat", bd=0, activebackground=C["blue_lt"],
                          cursor="hand2", padx=10, pady=4, highlightthickness=1,
                          highlightbackground=C["line"])
            b.pack(side=tk.LEFT, padx=3, pady=7)
            return b

        tbtn("➕  Ajouter PDF", self.add_files, bold=True, accent=True)
        tk.Frame(tb, bg=C["line"], width=1).pack(side=tk.LEFT, fill=tk.Y, pady=8, padx=4)
        self.btn_undo = tbtn("↶  Annuler", self.undo)
        self.btn_redo = tbtn("↷  Rétablir", self.redo)
        tk.Frame(tb, bg=C["line"], width=1).pack(side=tk.LEFT, fill=tk.Y, pady=8, padx=4)
        tbtn("⬆  Monter",    lambda: self._move_selected(-1))
        tbtn("⬇  Descendre", lambda: self._move_selected(+1))
        tk.Frame(tb, bg=C["line"], width=1).pack(side=tk.LEFT, fill=tk.Y, pady=8, padx=4)
        tbtn("⟲  90°", lambda: self._rotate_selected(-90))
        tbtn("⟳  90°", lambda: self._rotate_selected(90))
        tk.Frame(tb, bg=C["line"], width=1).pack(side=tk.LEFT, fill=tk.Y, pady=8, padx=4)
        tbtn("✏  Éditer page", self.edit_selected, bold=True, color=C["orange"])
        tbtn("🗑  Supprimer", self.delete_selected)

        self.lbl_info = tk.Label(tb, text="0 page(s) · 0 fichier(s)",
                                 font=("Helvetica", 8), bg=C["bg2"], fg=C["mid"])
        self.lbl_info.pack(side=tk.RIGHT, padx=14)
        self.lbl_hint = tk.Label(tb,
            text="Clic = sélectionner  ·  Double-clic = éditer  ·  Glisser = réorganiser",
            font=("Helvetica", 8), bg=C["bg2"], fg=C["blue"])
        self.lbl_hint.pack(side=tk.RIGHT, padx=8)

    def _build_canvas(self):
        wrap = tk.Frame(self.root, bg=C["bg"])
        wrap.pack(fill=tk.BOTH, expand=True)
        vsb = tk.Scrollbar(wrap, orient=tk.VERTICAL)
        vsb.pack(side=tk.RIGHT, fill=tk.Y)
        self.canvas = tk.Canvas(wrap, bg=C["bg"], bd=0, highlightthickness=0,
                                yscrollcommand=vsb.set)
        self.canvas.pack(fill=tk.BOTH, expand=True)
        vsb.config(command=self.canvas.yview)
        self.grid = tk.Frame(self.canvas, bg=C["bg"])
        self._cwin = self.canvas.create_window((0, 0), window=self.grid, anchor="nw")
        self.grid.bind("<Configure>",
            lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all")))
        self.canvas.bind("<Configure>", self._on_canvas_cfg)
        self.canvas.bind("<Button-1>", lambda e: self._clear_selection())
        for seq, delta in (("<MouseWheel>", None), ("<Button-4>", 1), ("<Button-5>", -1)):
            self.canvas.bind(seq,
                lambda e, d=delta: self.canvas.yview_scroll(
                    -(e.delta // 120) if d is None else d, "units"))
        self.lbl_empty = tk.Label(self.canvas,
            text="Aucune page à afficher\n\nCliquez sur  ➕ Ajouter PDF  pour commencer",
            font=("Helvetica", 13), fg=C["mid"], bg=C["bg"], justify=tk.CENTER)
        self._eid = self.canvas.create_window(600, 300, window=self.lbl_empty, anchor="center")

    def _build_footer(self):
        self.status_var = tk.StringVar(
            value="Prêt  ·  Cliquez une page pour la sélectionner  ·  Ctrl+Z / Ctrl+Y")
        f = tk.Frame(self.root, bg=C["navy2"], height=26)
        f.pack(fill=tk.X, side=tk.BOTTOM)
        f.pack_propagate(False)
        self.lbl_st = tk.Label(f, textvariable=self.status_var, font=("Helvetica", 8),
                               fg="#A8CCE8", bg=C["navy2"], padx=14)
        self.lbl_st.pack(side=tk.LEFT, pady=3)
        if not HAS_FITZ or not HAS_PIL:
            tk.Label(f, text="⚠ Installez PyMuPDF + Pillow pour l'édition complète",
                     font=("Helvetica", 8), fg=C["orange"],
                     bg=C["navy2"], padx=14).pack(side=tk.RIGHT, pady=3)

    def _on_canvas_cfg(self, e):
        self.canvas.itemconfig(self._cwin, width=e.width)
        self.canvas.coords(self._eid, e.width // 2, e.height // 2)

    def _st(self, msg, warn=False, ok=False):
        self.status_var.set(msg)
        self.lbl_st.config(fg=C["warn"] if warn else (C["ok"] if ok else "#A8CCE8"))

    def _upd_info(self):
        nf = len({p.path for p in self.pages})
        edits = sum(len(p.edits) for p in self.pages)
        rots  = sum(1 for p in self.pages if p.rotation)
        extra = ""
        if edits or rots:
            extra = f"  ·  {edits} édit(s)  ·  {rots} rotation(s)"
        sel_txt = ""
        if self._selected is not None:
            sel_txt = f"  ·  Sél: page #{self._selected + 1}"
        self.lbl_info.config(text=f"{len(self.pages)} page(s) · {nf} fichier(s){extra}{sel_txt}")
        self.btn_undo.config(state="normal" if self._hist_idx > 0 else "disabled")
        self.btn_redo.config(
            state="normal" if self._hist_idx < len(self._history) - 1 else "disabled")

    # ── Undo/Redo global ──
    def _snapshot(self):
        self._history = self._history[: self._hist_idx + 1]
        self._history.append(copy.deepcopy(self.pages))
        if len(self._history) > self._max_hist:
            self._history.pop(0)
        else:
            self._hist_idx += 1
        self._upd_info()

    def undo(self):
        if self._hist_idx <= 0:
            self._st("Rien à annuler", warn=True)
            return
        self._hist_idx -= 1
        self.pages = copy.deepcopy(self._history[self._hist_idx])
        for p in self.pages:
            p.photo = None
        self._selected = None
        self._render_grid()
        self._upd_info()
        self._st("↶  Action annulée")

    def redo(self):
        if self._hist_idx >= len(self._history) - 1:
            self._st("Rien à rétablir", warn=True)
            return
        self._hist_idx += 1
        self.pages = copy.deepcopy(self._history[self._hist_idx])
        for p in self.pages:
            p.photo = None
        self._selected = None
        self._render_grid()
        self._upd_info()
        self._st("↷  Action rétablie")

    # ── Loading ──
    def add_files(self):
        paths = filedialog.askopenfilenames(
            title="Sélectionner des fichiers PDF",
            filetypes=[("Fichiers PDF", "*.pdf"), ("Tous les fichiers", "*.*")])
        if not paths:
            return
        new = [p for p in paths if p not in self._raw_thumbs]
        if not new:
            self._st("Ces fichiers sont déjà présents.", warn=True)
            return
        self._st("⏳  Chargement…")
        threading.Thread(target=self._load_thread, args=(new,), daemon=True).start()

    def _load_thread(self, paths):
        new_pages = []
        for path in paths:
            fname = Path(path).name
            try:
                if HAS_FITZ and HAS_PIL:
                    doc  = fitz.open(path)
                    imgs = []
                    for i in range(doc.page_count):
                        pg  = doc[i]
                        pix = pg.get_pixmap(matrix=fitz.Matrix(0.30, 0.30), alpha=False)
                        img = Image.frombytes("RGB", [pix.width, pix.height], pix.samples)
                        img = img.resize((THUMB_W, THUMB_H), Image.LANCZOS)
                        imgs.append(img)
                        new_pages.append(Page(path, fname, i))
                    self._raw_thumbs[path] = imgs
                    doc.close()
                elif HAS_PYPDF2:
                    with open(path, "rb") as fh:
                        r = PyPDF2.PdfReader(fh)
                        for i in range(len(r.pages)):
                            new_pages.append(Page(path, fname, i))
                    self._raw_thumbs[path] = []
                else:
                    self.root.after(0, lambda: self._st("PyPDF2 non installé.", warn=True))
                    return
            except Exception as e:
                self.root.after(0, lambda e=e, n=fname:
                    self._st(f"⚠  {n}: {e}", warn=True))
        self.root.after(0, lambda: self._on_loaded(new_pages))

    def _on_loaded(self, new_pages):
        self.pages.extend(new_pages)
        self._render_grid()
        self._snapshot()
        nf = len({p.path for p in new_pages})
        self._st(f"✔  {len(new_pages)} page(s) depuis {nf} fichier(s)", ok=True)
        self._upd_info()

    # ── Grid ──
    def _render_grid(self):
        for w in self.grid.winfo_children():
            w.destroy()
        self.canvas.itemconfig(self._eid,
            state="normal" if not self.pages else "hidden")
        if not self.pages:
            return
        total_w = self.canvas.winfo_width() or 900
        cols = max(1, total_w // (CARD_W + PAD_X * 2))
        for pos, page in enumerate(self.pages):
            col = pos % cols
            row = pos // cols
            card = self._make_card(page, pos)
            card.grid(row=row, column=col, padx=PAD_X, pady=PAD_Y, sticky="n")
        self.grid.update_idletasks()
        self.canvas.configure(scrollregion=self.canvas.bbox("all"))

    def _get_thumb_image(self, page):
        raw = self._raw_thumbs.get(page.path, [])
        if not HAS_PIL:
            return None
        if page.thumb is not None:
            base_img = page.thumb
        elif page.pg_idx < len(raw):
            base_img = raw[page.pg_idx]
        else:
            return None
        if page.rotation:
            img = base_img.rotate(-page.rotation, expand=True)
            img.thumbnail((THUMB_W, THUMB_H), Image.LANCZOS)
            canvas_img = Image.new("RGB", (THUMB_W, THUMB_H), "white")
            x = (THUMB_W - img.width) // 2
            y = (THUMB_H - img.height) // 2
            canvas_img.paste(img, (x, y))
            return ImageTk.PhotoImage(canvas_img)
        return ImageTk.PhotoImage(base_img)

    def _make_card(self, page, pos):
        is_selected = (self._selected == pos)
        card_bg = C["sel_bg"] if is_selected else C["white"]
        border  = C["selected"] if is_selected else C["line"]
        thick   = 3 if is_selected else 2
        card = tk.Frame(self.grid, bg=card_bg, width=CARD_W, height=CARD_H,
                        highlightthickness=thick, highlightbackground=border,
                        cursor="hand2")
        card.pack_propagate(False)
        page.photo = self._get_thumb_image(page)
        if page.photo:
            lbl_img = tk.Label(card, image=page.photo, bg=card_bg, bd=0)
        else:
            lbl_img = tk.Label(card, text="📄", font=("Helvetica", 30),
                               bg=C["bg2"], fg=C["blue"],
                               width=THUMB_W // 8, height=THUMB_H // 18)
        lbl_img.pack(padx=5, pady=(5, 2))
        badge_pg = tk.Label(card, text=f"p.{page.pg_idx + 1}",
                            font=("Helvetica", 7, "bold"),
                            bg=C["navy"], fg=C["white"], padx=4, pady=1)
        badge_pg.place(x=7, y=7)
        badge_pos_color = C["selected"] if is_selected else C["orange"]
        badge_pos = tk.Label(card, text=f"#{pos + 1}",
                             font=("Helvetica", 7, "bold"),
                             bg=badge_pos_color, fg=C["white"], padx=4, pady=1)
        badge_pos.place(relx=1.0, x=-7, y=7, anchor="ne")
        flags = []
        if page.rotation: flags.append(f"⟳{page.rotation}°")
        if page.edits: flags.append(f"✏{len(page.edits)}")
        if flags:
            tk.Label(card, text=" ".join(flags), font=("Helvetica", 7, "bold"),
                     bg=C["edit_sel"], fg=C["white"], padx=4, pady=1
                     ).place(x=7, y=THUMB_H - 8)
        if is_selected:
            tk.Label(card, text="● SÉLECTIONNÉE", font=("Helvetica", 6, "bold"),
                     bg=C["selected"], fg=C["white"], padx=4, pady=1
                     ).place(relx=1.0, x=-7, y=THUMB_H - 8, anchor="ne")
        short = page.fname if len(page.fname) <= 18 else page.fname[:15] + "…"
        fname_bar = tk.Label(card, text=short, font=("Helvetica", 7, "bold"),
                             bg=C["selected"] if is_selected else C["navy"],
                             fg=C["white"], anchor="center", pady=3)
        fname_bar.pack(fill=tk.X, side=tk.BOTTOM)
        pos_lbl = tk.Label(card, text=f"position {pos + 1}", font=("Helvetica", 6),
                           bg=C["bg2"], fg=C["mid"], anchor="center")
        pos_lbl.pack(fill=tk.X, side=tk.BOTTOM)
        all_w = [card, lbl_img, badge_pg, badge_pos, fname_bar, pos_lbl]
        for w in all_w:
            w.bind("<ButtonPress-1>",   lambda e, p=pos: self._on_card_press(e, p))
            w.bind("<B1-Motion>",       self._on_card_motion)
            w.bind("<ButtonRelease-1>", self._on_card_release)
            w.bind("<Double-Button-1>", lambda e, p=pos: self._on_card_dclick(e, p))
        return card

    # ── Click/drag cards ──
    def _on_card_press(self, event, pos):
        self._drag_src = pos
        self._drag_slot = pos
        self._dragging = False
        self._press_x = event.x_root
        self._press_y = event.y_root

    def _on_card_motion(self, event):
        if self._drag_src is None:
            return
        if not self._dragging:
            dx = abs(event.x_root - self._press_x)
            dy = abs(event.y_root - self._press_y)
            if dx < 5 and dy < 5:
                return
            self._dragging = True
            self._start_ghost(event)
        if self._ghost_win:
            rx = event.x_root - CARD_W // 2
            ry = event.y_root - CARD_H // 2
            self._ghost_win.geometry(f"+{rx}+{ry}")
            cx = event.x_root - self.canvas.winfo_rootx()
            cy = (event.y_root - self.canvas.winfo_rooty()
                  + int(self.canvas.canvasy(0)))
            slot = self._slot_from_xy(cx, cy)
            if slot is not None and slot != self._drag_slot:
                self._drag_slot = slot
                self._highlight_drop_slot(slot)

    def _on_card_release(self, event):
        if self._drag_src is None:
            return
        if self._dragging:
            if self._ghost_win:
                self._ghost_win.destroy()
                self._ghost_win = None
            src  = self._drag_src
            slot = self._drag_slot
            moved = False
            if src is not None and slot is not None and src != slot:
                page = self.pages.pop(src)
                self.pages.insert(slot, page)
                self._selected = slot
                moved = True
            self._drag_src = None
            self._drag_slot = None
            self._dragging = False
            self._render_grid()
            self._upd_info()
            if moved:
                self._snapshot()
        else:
            pos = self._drag_src
            self._drag_src = None
            self._drag_slot = None
            self._select_page(pos)

    def _on_card_dclick(self, event, pos):
        if self._ghost_win:
            self._ghost_win.destroy()
            self._ghost_win = None
        self._drag_src = None
        self._drag_slot = None
        self._dragging = False
        self._select_page(pos)
        self.open_editor(pos)
        return "break"

    def _select_page(self, pos):
        if pos < 0 or pos >= len(self.pages):
            return
        if self._selected == pos:
            return
        self._selected = pos
        self._render_grid()
        page = self.pages[pos]
        self._st(f"✔  Page sélectionnée : #{pos + 1}  ·  {page.fname}  ·  p.{page.pg_idx + 1}", ok=True)
        self._upd_info()

    def _clear_selection(self):
        if self._selected is not None:
            self._selected = None
            self._render_grid()
            self._upd_info()
            self._st("Sélection annulée")

    def _require_selection(self):
        if self._selected is None:
            self._st("⚠  Cliquez d'abord sur une page pour la sélectionner", warn=True)
            return None
        if self._selected >= len(self.pages):
            self._selected = None
            return None
        return self._selected

    def _start_ghost(self, event):
        page = self.pages[self._drag_src]
        ghost = tk.Toplevel(self.root)
        ghost.overrideredirect(True)
        ghost.attributes("-alpha", 0.72)
        ghost.attributes("-topmost", True)
        ghost.configure(bg=C["blue"])
        rx = event.x_root - CARD_W // 2
        ry = event.y_root - CARD_H // 2
        ghost.geometry(f"{CARD_W}x{CARD_H}+{rx}+{ry}")
        photo = self._get_thumb_image(page)
        if photo:
            self._ghost_photo = photo
            tk.Label(ghost, image=photo, bg=C["blue"], bd=0).pack(padx=5, pady=5)
        else:
            tk.Label(ghost, text="📄", font=("Helvetica", 28),
                     bg=C["blue"], fg=C["white"]).pack(pady=20)
        short = page.fname if len(page.fname) <= 18 else page.fname[:15] + "…"
        tk.Label(ghost, text=short, font=("Helvetica", 7, "bold"),
                 bg=C["blue_h"], fg=C["white"]).pack(fill=tk.X)
        self._ghost_win = ghost
        cards = self.grid.winfo_children()
        if self._drag_src < len(cards):
            cards[self._drag_src].config(highlightbackground=C["orange"],
                                          highlightthickness=3)

    def _slot_from_xy(self, cx, cy):
        total_w = self.canvas.winfo_width() or 900
        cols    = max(1, total_w // (CARD_W + PAD_X * 2))
        cell_w  = CARD_W + PAD_X * 2
        cell_h  = CARD_H + PAD_Y * 2
        col = max(0, min(cols - 1, int(cx // cell_w)))
        row = max(0, int(cy // cell_h))
        idx = row * cols + col
        return min(idx, max(0, len(self.pages) - 1))

    def _highlight_drop_slot(self, slot):
        for i, c in enumerate(self.grid.winfo_children()):
            if i == slot:
                c.config(highlightbackground=C["drop"], highlightthickness=3)
            elif i != self._drag_src:
                is_sel = (self._selected == i)
                c.config(highlightbackground=C["selected"] if is_sel else C["line"],
                         highlightthickness=3 if is_sel else 2)

    # ── Actions ──
    def _move_selected(self, delta):
        p = self._require_selection()
        if p is None:
            return
        np = p + delta
        if 0 <= np < len(self.pages):
            self.pages[p], self.pages[np] = self.pages[np], self.pages[p]
            self._selected = np
            self._render_grid()
            self._upd_info()
            self._snapshot()

    def _rotate_selected(self, delta):
        p = self._require_selection()
        if p is None:
            return
        page = self.pages[p]
        page.rotation = (page.rotation + delta) % 360
        page.photo = None
        self._render_grid()
        self._upd_info()
        self._snapshot()
        self._st(f"⟳  Page #{p + 1} pivotée à {page.rotation}°", ok=True)

    def edit_selected(self):
        p = self._require_selection()
        if p is None:
            return
        self.open_editor(p)

    def delete_selected(self):
        p = self._require_selection()
        if p is None:
            return
        fname = self.pages[p].fname
        del self.pages[p]
        self._selected = None
        self._render_grid()
        self._upd_info()
        self._snapshot()
        self._st(f"🗑  Page supprimée ({fname})")

    def clear_all(self):
        if not self.pages:
            return
        if not messagebox.askyesno("Confirmer", "Vider toutes les pages ?"):
            return
        self.pages.clear()
        self._raw_thumbs.clear()
        self._selected = None
        self._render_grid()
        self._upd_info()
        self._snapshot()
        self._st("Liste vidée")

    def open_editor(self, pos):
        if not HAS_FITZ:
            messagebox.showerror("Module manquant",
                "L'éditeur nécessite PyMuPDF :\npip install PyMuPDF Pillow")
            return
        if pos < 0 or pos >= len(self.pages):
            return
        PageEditor(self, pos)

    def on_editor_save(self, pos, rotation, edits, thumb=None):
        page = self.pages[pos]
        page.rotation = rotation
        page.edits    = edits
        page.thumb    = thumb
        page.photo    = None
        self._render_grid()
        self._upd_info()
        self._snapshot()
        self._st(f"✔  Modifications enregistrées ({len(edits)} édit(s))", ok=True)

    # ── Print ──
    def print_document(self):
        if not self.pages:
            messagebox.showwarning("Vide", "Ajoutez des fichiers PDF d'abord.")
            return
        if not HAS_FITZ:
            messagebox.showerror("Module manquant",
                "L'impression nécessite PyMuPDF :\npip install PyMuPDF")
            return
        PrintDialog(self)

    # ── Merge ──
    def merge_pdfs(self):
        if not self.pages:
            messagebox.showwarning("Vide", "Ajoutez des fichiers PDF d'abord.")
            return
        if not HAS_FITZ:
            messagebox.showerror("Module manquant",
                "Le merge nécessite PyMuPDF :\npip install PyMuPDF")
            return
        out = filedialog.asksaveasfilename(
            title="Enregistrer le PDF fusionné", defaultextension=".pdf",
            filetypes=[("Fichiers PDF", "*.pdf")])
        if not out:
            return
        self._st("⏳  Fusion en cours…")
        self.root.update()
        try:
            out_doc = fitz.open()
            src_docs = {}
            for page in self.pages:
                if page.path not in src_docs:
                    src_docs[page.path] = fitz.open(page.path)
                src = src_docs[page.path]
                out_doc.insert_pdf(src, from_page=page.pg_idx, to_page=page.pg_idx)
                new_pg = out_doc[-1]
                self._apply_edits(new_pg, page.edits)
                if page.rotation:
                    new_pg.set_rotation(page.rotation)
            self._subset_fonts(out_doc, self.pages)
            out_doc.save(out, garbage=4, deflate=True)
            out_doc.close()
            for d in src_docs.values():
                d.close()
            nf = len({p.path for p in self.pages})
            ne = sum(len(p.edits) for p in self.pages)
            msg = (f"PDF exporté avec succès !\n\n"
                   f"Fichier : {out}\n"
                   f"Pages : {len(self.pages)}  ·  Sources : {nf}\n"
                   f"Édits appliqués : {ne}")
            self._st(f"✔  Exporté — {len(self.pages)} pages, {ne} édits", ok=True)
            messagebox.showinfo("Succès", msg)
        except Exception as e:
            self._st("⚠  Erreur lors de la fusion", warn=True)
            messagebox.showerror("Erreur de fusion", str(e))

    def _apply_edits(self, fitz_page, edits):
        apply_edits_to_page(fitz_page, edits)

    @staticmethod
    def _subset_fonts(doc, pages):
        # Fonts embedded for edited text are full files: keep only the used glyphs
        if not any(p.edits for p in pages):
            return
        try:
            doc.subset_fonts()
        except Exception:
            pass


# ══════════════════════════════════════════════════════════════════════════════
#  PAGE EDITOR  —  V3 (édition directe façon pdfFiller)
# ══════════════════════════════════════════════════════════════════════════════
class PageEditor:
    """Tous les textes de la page sont détectés et modifiables directement sur
    la page, en conservant police, taille, gras, couleur et arrière-plan."""

    ZOOMS = (0.6, 0.8, 1.0, 1.25, 1.5, 1.75, 2.0, 2.5, 3.0)
    MARGIN = 16
    PALETTE = ("#000000", "#434343", "#666666", "#999999", "#CCCCCC", "#FFFFFF",
               "#FF0000", "#FF8C00", "#FFD700", "#008000", "#00CED1", "#1E90FF",
               "#0000CD", "#00356B", "#8A2BE2", "#FF69B4", "#8B4513", "#E8540A")
    INPUT_WIDGETS = (tk.Entry, tk.Spinbox, tk.Text, ttk.Entry)

    def __init__(self, app, pos):
        self.app = app
        self.pos = pos
        self.page = app.pages[pos]
        self.rotation = self.page.rotation
        self.edits = copy.deepcopy(self.page.edits)
        self._next_uid = max([(e.uid or 0) for e in self.edits], default=0) + 1

        self._hist, self._hist_idx, self._max_hist = [], -1, 60
        self._zoom_idx = 4
        self._sel = None            # ("seg", key) | ("add", uid)
        self._hover = None
        self._mode = "select"       # "select" | "add"
        self._eyedropper = None     # "text" | "bg"
        self._press = None
        self._inline = None
        self._render_after = None
        self._loading = False
        self._fcache = {}
        self._items = []
        self._color = (0.0, 0.0, 0.0)
        self._bg = None
        self._tk_fams = None
        self._families = None

        self._doc = fitz.open(self.page.path)
        self._fpg = self._doc[self.page.pg_idx]
        self._src_rot = self._fpg.rotation
        if self._src_rot:
            self._fpg.set_rotation(0)
        self._segments = extract_segments(self._fpg)
        self._seg_by_key = {s["key"]: s for s in self._segments}

        self._build_window()
        self._render()
        self._snap()
        self._update_panel()

    # ── UI ──────────────────────────────────────────────────────────────────
    def _build_window(self):
        self.win = tk.Toplevel(self.app.root)
        self.win.title(f"Éditeur — {self.page.fname}  ·  page {self.page.pg_idx + 1}")
        self.win.geometry("1360x860")
        self.win.minsize(960, 640)
        self.win.configure(bg=C["bg"])
        self.win.transient(self.app.root)
        self.win.protocol("WM_DELETE_WINDOW", self._on_cancel)

        hdr = tk.Frame(self.win, bg=C["navy2"], height=46)
        hdr.pack(fill=tk.X)
        hdr.pack_propagate(False)
        tk.Frame(hdr, bg=C["orange"], width=4).pack(side=tk.LEFT, fill=tk.Y)
        tk.Label(hdr, text="✏  Éditeur de page", font=("Helvetica", 12, "bold"),
                 fg=C["white"], bg=C["navy2"], padx=14).pack(side=tk.LEFT)
        tk.Label(hdr, text=f"  {self.page.fname}  ·  page {self.page.pg_idx + 1}",
                 font=("Helvetica", 9), fg="#A8CCE8", bg=C["navy2"]).pack(side=tk.LEFT)
        tk.Button(hdr, text="✔  Enregistrer", command=self._on_save,
                  font=("Helvetica", 9, "bold"), bg=C["ok"], fg=C["white"],
                  relief="flat", activebackground="#0F6238",
                  cursor="hand2", padx=14, pady=4).pack(side=tk.RIGHT, padx=10, pady=8)
        tk.Button(hdr, text="✕  Annuler", command=self._on_cancel,
                  font=("Helvetica", 9), bg="#1A3560", fg="#A8CCE8",
                  relief="flat", cursor="hand2", padx=10, pady=4
                  ).pack(side=tk.RIGHT, padx=4, pady=8)

        tb = tk.Frame(self.win, bg=C["bg2"], height=40)
        tb.pack(fill=tk.X)
        tb.pack_propagate(False)

        def tbtn(text, cmd, color=None):
            return tk.Button(tb, text=text, command=cmd, font=("Helvetica", 8),
                             bg=color or C["white"],
                             fg=C["white"] if color else C["text"],
                             relief="flat", bd=0, activebackground=C["blue_lt"],
                             cursor="hand2", padx=10, pady=4, highlightthickness=1,
                             highlightbackground=C["line"])

        def sep():
            tk.Frame(tb, bg=C["line"], width=1).pack(side=tk.LEFT, fill=tk.Y, pady=8, padx=4)

        self.btn_select = tbtn("✏  Modifier le texte", lambda: self._set_mode("select"))
        self.btn_select.pack(side=tk.LEFT, padx=3, pady=6)
        self.btn_add = tbtn("➕  Ajouter du texte", lambda: self._set_mode("add"))
        self.btn_add.pack(side=tk.LEFT, padx=3, pady=6)
        sep()
        tbtn("⟲ 90°", lambda: self._rotate(-90)).pack(side=tk.LEFT, padx=3, pady=6)
        tbtn("⟳ 90°", lambda: self._rotate(90)).pack(side=tk.LEFT, padx=3, pady=6)
        tbtn("⟳ 180°", lambda: self._rotate(180)).pack(side=tk.LEFT, padx=3, pady=6)
        sep()
        self.btn_eundo = tbtn("↶  Annuler", self._undo)
        self.btn_eundo.pack(side=tk.LEFT, padx=3, pady=6)
        self.btn_eredo = tbtn("↷  Rétablir", self._redo)
        self.btn_eredo.pack(side=tk.LEFT, padx=3, pady=6)
        sep()
        tbtn("🗑  Supprimer", self._delete_selected, color=C["warn"]
             ).pack(side=tk.LEFT, padx=3, pady=6)
        sep()
        tbtn("－", lambda: self._set_zoom(-1)).pack(side=tk.LEFT, padx=(3, 0), pady=6)
        self.lbl_zoom = tk.Label(tb, text="", width=6, font=("Helvetica", 8, "bold"),
                                 bg=C["bg2"], fg=C["text"])
        self.lbl_zoom.pack(side=tk.LEFT)
        tbtn("＋", lambda: self._set_zoom(1)).pack(side=tk.LEFT, padx=(0, 3), pady=6)

        self.lbl_mode = tk.Label(tb, text="", font=("Helvetica", 8, "bold"),
                                 bg=C["bg2"], fg=C["blue"])
        self.lbl_mode.pack(side=tk.RIGHT, padx=14)

        ft = tk.Frame(self.win, bg=C["navy2"], height=24)
        ft.pack(fill=tk.X, side=tk.BOTTOM)
        ft.pack_propagate(False)
        self._st_var = tk.StringVar()
        tk.Label(ft, textvariable=self._st_var, font=("Helvetica", 8),
                 fg="#A8CCE8", bg=C["navy2"], padx=14).pack(side=tk.LEFT, pady=3)

        body = tk.Frame(self.win, bg=C["bg"])
        body.pack(fill=tk.BOTH, expand=True)
        self._build_side_panel(body)

        cwrap = tk.Frame(body, bg=C["bg"])
        cwrap.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        vsb = tk.Scrollbar(cwrap, orient=tk.VERTICAL)
        vsb.pack(side=tk.RIGHT, fill=tk.Y)
        hsb = tk.Scrollbar(cwrap, orient=tk.HORIZONTAL)
        hsb.pack(side=tk.BOTTOM, fill=tk.X)
        self.canvas = tk.Canvas(cwrap, bg="#8A8F98", yscrollcommand=vsb.set,
                                xscrollcommand=hsb.set, highlightthickness=0,
                                takefocus=1)
        self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        vsb.config(command=self.canvas.yview)
        hsb.config(command=self.canvas.xview)

        cv = self.canvas
        cv.bind("<Motion>", self._on_motion)
        cv.bind("<Leave>", self._on_leave)
        cv.bind("<ButtonPress-1>", self._on_press)
        cv.bind("<B1-Motion>", self._on_drag)
        cv.bind("<ButtonRelease-1>", self._on_release)
        cv.bind("<ButtonPress-3>", lambda e: self._on_escape())
        cv.bind("<MouseWheel>", self._on_wheel)
        cv.bind("<Shift-MouseWheel>", lambda e: self._on_wheel(e, horizontal=True))
        cv.bind("<Control-MouseWheel>", lambda e: self._set_zoom(1 if e.delta > 0 else -1))
        cv.bind("<Button-4>", lambda e: cv.yview_scroll(-3, "units"))
        cv.bind("<Button-5>", lambda e: cv.yview_scroll(3, "units"))
        cv.bind("<Control-Button-4>", lambda e: self._set_zoom(1))
        cv.bind("<Control-Button-5>", lambda e: self._set_zoom(-1))

        self._bind_key("<Control-z>", self._undo)
        self._bind_key("<Control-Z>", self._undo)
        self._bind_key("<Control-y>", self._redo)
        self._bind_key("<Control-Y>", self._redo)
        self._bind_key("<Control-s>", self._on_save, in_inputs=True)
        self._bind_key("<Escape>", self._on_escape, in_inputs=True)
        self._bind_key("<Delete>", self._delete_selected)
        self._bind_key("<BackSpace>", self._delete_selected)
        self._bind_key("<Return>", self._edit_selected)
        for key, dx, dy in (("Left", -1, 0), ("Right", 1, 0), ("Up", 0, -1), ("Down", 0, 1)):
            self._bind_key(f"<{key}>", lambda dx=dx, dy=dy: self._nudge(dx, dy))
            self._bind_key(f"<Shift-{key}>", lambda dx=dx, dy=dy: self._nudge(dx * 10, dy * 10))
        self._set_mode("select")

    def _bind_key(self, seq, fn, in_inputs=False):
        # "break" also stops the main window's bind_all shortcuts from firing here
        def handler(e):
            if in_inputs or not isinstance(e.widget, self.INPUT_WIDGETS):
                fn()
            return "break"
        self.win.bind(seq, handler)

    def _build_side_panel(self, parent):
        side = tk.Frame(parent, bg=C["white"], width=330,
                        highlightthickness=1, highlightbackground=C["line"])
        side.pack(side=tk.RIGHT, fill=tk.Y)
        side.pack_propagate(False)
        tk.Label(side, text="PROPRIÉTÉS DU TEXTE", font=("Helvetica", 9, "bold"),
                 bg=C["navy"], fg=C["white"], pady=7).pack(fill=tk.X)
        inner = tk.Frame(side, bg=C["white"])
        inner.pack(fill=tk.BOTH, expand=True, padx=14, pady=8)

        def label(text, pady=(6, 1)):
            tk.Label(inner, text=text, font=("Helvetica", 8, "bold"),
                     bg=C["white"], fg=C["text"], anchor="w").pack(fill=tk.X, pady=pady)

        def small_btn(parent, text, cmd):
            return tk.Button(parent, text=text, command=cmd, font=("Helvetica", 8),
                             bg=C["white"], relief="flat", highlightthickness=1,
                             highlightbackground=C["line"], cursor="hand2", padx=6)

        self.lbl_sel = tk.Label(inner, text="", font=("Helvetica", 8), bg=C["bg2"],
                                fg=C["mid"], justify=tk.LEFT, anchor="w",
                                wraplength=290, padx=8, pady=8)
        self.lbl_sel.pack(fill=tk.X, pady=(0, 4))

        label("Police :")
        self.var_font = tk.StringVar()
        self.cb_font = ttk.Combobox(inner, textvariable=self.var_font, state="readonly",
                                    height=24, font=("Helvetica", 9))
        self.cb_font.pack(fill=tk.X)
        self.cb_font.bind("<<ComboboxSelected>>", lambda e: self._on_prop("family"))

        rowf = tk.Frame(inner, bg=C["white"])
        rowf.pack(fill=tk.X, pady=(8, 0))
        tk.Label(rowf, text="Taille :", font=("Helvetica", 8, "bold"),
                 bg=C["white"], fg=C["text"]).pack(side=tk.LEFT)
        self.var_size = tk.StringVar(value="11")
        self.sp_size = tk.Spinbox(rowf, from_=4, to=200, increment=0.5, width=6,
                                  textvariable=self.var_size, font=("Helvetica", 9),
                                  command=lambda: self._on_prop("size"))
        self.sp_size.pack(side=tk.LEFT, padx=6)
        self.sp_size.bind("<KeyRelease>", lambda e: self._on_prop("size"))
        self.var_bold = tk.BooleanVar(value=False)
        self.var_italic = tk.BooleanVar(value=False)
        self.chk_bold = tk.Checkbutton(rowf, text="G", variable=self.var_bold,
                                       indicatoron=False, width=3,
                                       font=("Helvetica", 9, "bold"),
                                       selectcolor=C["blue_lt"], cursor="hand2",
                                       command=lambda: self._on_prop("bold"))
        self.chk_bold.pack(side=tk.LEFT, padx=(8, 2))
        self.chk_italic = tk.Checkbutton(rowf, text="I", variable=self.var_italic,
                                         indicatoron=False, width=3,
                                         font=("Times", 10, "italic"),
                                         selectcolor=C["blue_lt"], cursor="hand2",
                                         command=lambda: self._on_prop("italic"))
        self.chk_italic.pack(side=tk.LEFT, padx=2)

        label("Couleur du texte :", pady=(10, 1))
        rowc = tk.Frame(inner, bg=C["white"])
        rowc.pack(fill=tk.X)
        self.swatch_text = tk.Frame(rowc, width=26, height=20, bg="#000000",
                                    highlightthickness=1, highlightbackground=C["mid"])
        self.swatch_text.pack(side=tk.LEFT)
        self.btn_text_more = small_btn(rowc, "Autre…", lambda: self._pick_color("text"))
        self.btn_text_more.pack(side=tk.LEFT, padx=6)
        self.btn_text_drop = small_btn(rowc, "💧 Pipette", lambda: self._start_eyedropper("text"))
        self.btn_text_drop.pack(side=tk.LEFT)
        self._palette(inner, lambda rgb: self._set_text_color(rgb))

        label("Arrière-plan :", pady=(10, 1))
        self.var_bgmode = tk.StringVar(value="orig")
        self.rb_bg_orig = tk.Radiobutton(inner, text="Conserver l'arrière-plan d'origine",
                                         variable=self.var_bgmode, value="orig",
                                         font=("Helvetica", 8), bg=C["white"],
                                         anchor="w", command=self._on_bgmode)
        self.rb_bg_orig.pack(fill=tk.X)
        rowb = tk.Frame(inner, bg=C["white"])
        rowb.pack(fill=tk.X)
        self.rb_bg_color = tk.Radiobutton(rowb, text="Couleur de fond :",
                                          variable=self.var_bgmode, value="color",
                                          font=("Helvetica", 8), bg=C["white"],
                                          command=self._on_bgmode)
        self.rb_bg_color.pack(side=tk.LEFT)
        self.swatch_bg = tk.Frame(rowb, width=26, height=20, bg=C["white"],
                                  highlightthickness=1, highlightbackground=C["mid"])
        self.swatch_bg.pack(side=tk.LEFT, padx=4)
        self.btn_bg_more = small_btn(rowb, "Autre…", lambda: self._pick_color("bg"))
        self.btn_bg_more.pack(side=tk.LEFT, padx=2)
        self.btn_bg_drop = small_btn(rowb, "💧", lambda: self._start_eyedropper("bg"))
        self.btn_bg_drop.pack(side=tk.LEFT, padx=2)
        self._palette(inner, lambda rgb: self._set_bg_color(rgb))
        tk.Label(inner, text="« Couleur de fond » active la pipette : cliquez sur la page.",
                 font=("Helvetica", 7, "italic"), bg=C["white"], fg=C["mid"],
                 anchor="w").pack(fill=tk.X)

        rowa = tk.Frame(inner, bg=C["white"])
        rowa.pack(fill=tk.X, pady=(10, 0))
        tk.Label(rowa, text="Rotation du texte (°) :", font=("Helvetica", 8, "bold"),
                 bg=C["white"], fg=C["text"]).pack(side=tk.LEFT)
        self.var_angle = tk.StringVar(value="0")
        self.sp_angle = tk.Spinbox(rowa, from_=-360, to=360, increment=15, width=6,
                                   textvariable=self.var_angle, font=("Helvetica", 9),
                                   command=lambda: self._on_prop("angle"))
        self.sp_angle.pack(side=tk.LEFT, padx=6)
        self.sp_angle.bind("<KeyRelease>", lambda e: self._on_prop("angle"))

        tk.Frame(inner, bg=C["line"], height=1).pack(fill=tk.X, pady=10)
        self.btn_edit = tk.Button(inner, text="✏  Modifier ce texte", command=self._edit_or_commit,
                                  font=("Helvetica", 9, "bold"), bg=C["ok"], fg=C["white"],
                                  relief="flat", activebackground="#0F6238",
                                  cursor="hand2", pady=6)
        self.btn_edit.pack(fill=tk.X, pady=(0, 5))
        self.btn_revert = tk.Button(inner, text="↺  Rétablir le texte d'origine",
                                    command=self._revert_selected, font=("Helvetica", 8),
                                    bg=C["white"], fg=C["text"], relief="flat",
                                    highlightthickness=1, highlightbackground=C["line"],
                                    cursor="hand2", pady=4)
        self.btn_revert.pack(fill=tk.X, pady=(0, 5))
        self.btn_delete = tk.Button(inner, text="🗑  Supprimer ce texte",
                                    command=self._delete_selected, font=("Helvetica", 8),
                                    bg=C["white"], fg=C["warn"], relief="flat",
                                    highlightthickness=1, highlightbackground=C["line"],
                                    cursor="hand2", pady=4)
        self.btn_delete.pack(fill=tk.X)

        tk.Frame(inner, bg=C["line"], height=1).pack(fill=tk.X, pady=10)
        self.var_showboxes = tk.BooleanVar(value=True)
        tk.Checkbutton(inner, text="Afficher les zones de texte détectées",
                       variable=self.var_showboxes, font=("Helvetica", 8),
                       bg=C["white"], anchor="w",
                       command=self._draw_overlays).pack(fill=tk.X)
        self.lbl_stats = tk.Label(inner, text="", font=("Helvetica", 8), bg=C["white"],
                                  fg=C["mid"], justify=tk.LEFT, anchor="w")
        self.lbl_stats.pack(fill=tk.X, pady=(4, 0))

        self._prop_widgets = (self.cb_font, self.sp_size, self.chk_bold, self.chk_italic,
                              self.btn_text_more, self.btn_text_drop, self.rb_bg_orig,
                              self.rb_bg_color, self.btn_bg_more, self.btn_bg_drop,
                              self.sp_angle, self.btn_edit, self.btn_revert, self.btn_delete)

    def _palette(self, parent, callback):
        pal = tk.Frame(parent, bg=C["white"])
        pal.pack(fill=tk.X, pady=(4, 0))
        for i, hex_col in enumerate(self.PALETTE):
            rgb = tuple(int(hex_col[j:j + 2], 16) / 255 for j in (1, 3, 5))
            sw = tk.Frame(pal, width=14, height=14, bg=hex_col, cursor="hand2",
                          highlightthickness=1, highlightbackground="#888")
            sw.grid(row=0, column=i, padx=1)
            sw.bind("<Button-1>", lambda e, c=rgb: callback(c))

    # ── Helpers ─────────────────────────────────────────────────────────────
    def _status(self, msg):
        self._st_var.set(msg)

    def _zoom(self):
        return self.ZOOMS[self._zoom_idx]

    def _eff_rotation(self):
        return self.rotation if self.rotation else self._src_rot

    def _pdf_to_cv(self, x, y):
        p = fitz.Point(x, y) * self._mat
        return p.x + self.MARGIN, p.y + self.MARGIN

    def _cv_to_pdf(self, cx, cy):
        p = fitz.Point(cx - self.MARGIN, cy - self.MARGIN) * self._imat
        return p.x, p.y

    def _rect_to_cv(self, r):
        rr = fitz.Rect(r) * self._mat
        m = self.MARGIN
        return rr.x0 + m, rr.y0 + m, rr.x1 + m, rr.y1 + m

    def _event_cv(self, e):
        return self.canvas.canvasx(e.x), self.canvas.canvasy(e.y)

    def _edit_for_seg(self, key):
        return next((e for e in self.edits
                     if e.seg_key == key and e.kind in ("replace", "delete")), None)

    def _get_edit(self, item, create=False):
        if item is None:
            return None
        kind, k = item
        if kind == "add":
            return next((e for e in self.edits if e.kind == "add" and e.uid == k), None)
        ed = self._edit_for_seg(k)
        if ed is None and create:
            ed = Edit.from_segment(self._seg_by_key[k])
            self.edits.append(ed)
        return ed

    def _props(self, item):
        ed = self._get_edit(item)
        if ed is None and item is not None and item[0] == "seg":
            ed = Edit.from_segment(self._seg_by_key[item[1]])
        return ed

    def _is_edited(self, item):
        return item[0] == "add" or self._edit_for_seg(item[1]) is not None

    def _edit_rect(self, ed):
        font = resolve_font(self._fpg, ed, self._fcache)[2]
        return text_rect(font, ed.text, ed.size, ed.origin, ed.angle)

    def _item_rect(self, item):
        if item[0] == "seg":
            ed = self._edit_for_seg(item[1])
            if ed is None:
                return fitz.Rect(self._seg_by_key[item[1]]["bbox"])
            return self._edit_rect(ed)
        ed = self._get_edit(item)
        return self._edit_rect(ed) if ed else fitz.Rect()

    def _compute_items(self):
        items = []
        for e in self.edits:
            if e.kind == "add":
                items.append((("add", e.uid), self._edit_rect(e)))
        for s in self._segments:
            ed = self._edit_for_seg(s["key"])
            if ed is not None and ed.kind == "delete":
                continue
            rect = self._edit_rect(ed) if ed else fitz.Rect(s["bbox"])
            items.append((("seg", s["key"]), rect))
        return items

    def _hit(self, px, py):
        best, best_area = None, None
        pt = fitz.Point(px, py)
        for item, r in self._items:
            rr = fitz.Rect(r.x0 - 1.5, r.y0 - 1.5, r.x1 + 1.5, r.y1 + 1.5)
            if rr.contains(pt):
                area = r.width * r.height * (0.5 if item[0] == "add" else 1)
                if best is None or area < best_area:
                    best, best_area = item, area
        return best

    def _prune(self):
        self.edits = [e for e in self.edits if not e.is_noop()]

    def _reflow_line(self, key):
        """Comme Word : quand un texte s'allonge ou raccourcit, la suite de la
        ligne (textes collés sur la même ligne de base) se décale d'autant."""
        seg = self._seg_by_key.get(key)
        if seg is None or seg["angle"] != 0.0:
            return
        oy = seg["origin"][1]
        line = sorted((s for s in self._segments if s["angle"] == 0.0
                       and abs(s["origin"][1] - oy) < seg["size"] * 0.2),
                      key=lambda s: s["bbox"][0])
        shift, prev = 0.0, None
        for s in line:
            ed = self._edit_for_seg(s["key"])
            attached = prev is not None and \
                s["bbox"][0] - prev["bbox"][2] <= max(s["size"], prev["size"])
            if not attached:
                shift = 0.0
            if ed is not None and ed.pinned:
                shift = 0.0
                prev = s
                continue
            if ed is not None:
                ed.origin = (s["origin"][0] + shift, ed.origin[1])
            elif abs(shift) > 0.01:
                cand = Edit.from_segment(s)
                # only shift text that can be rewritten without changing its look
                if resolve_font(self._fpg, cand, self._fcache)[0] == "base14":
                    shift = 0.0
                    prev = s
                    continue
                cand.origin = (s["origin"][0] + shift, cand.origin[1])
                self.edits.append(cand)
                ed = cand
            if ed is not None:
                if ed.kind == "delete":
                    shift -= s["bbox"][2] - s["bbox"][0]
                elif "\n" in ed.text:
                    shift = 0.0
                else:
                    font = resolve_font(self._fpg, ed, self._fcache)[2]
                    shift += (font.text_length(ed.text, fontsize=ed.size)
                              - font.text_length(s["text"], fontsize=s["size"]))
            prev = s

    def _families_list(self):
        if self._families is None:
            self._families = FontManager.families()
        return self._families

    def _orig_label(self, ed):
        return f"★ Police d'origine — {font_display_name(ed.orig_font)}"

    def _family_label(self, ed):
        if ed.orig_font and ed.family == ed.orig_font:
            return self._orig_label(ed)
        return font_display_name(ed.family)

    def _default_family(self):
        idx = FontManager.index()
        for key in ("arial", "liberationsans", "helvetica"):
            if key in idx:
                return FontManager.display(key)
        return "Helvetica"

    def _tk_family(self, name):
        if self._tk_fams is None:
            self._tk_fams = {f.lower(): f for f in tkfont.families(self.win)}
        key = font_family_key(name or "")
        disp = font_display_name(name or "")
        for cand in [disp, disp.replace(" ", "")] + \
                [FontManager.display(k) for k in FAMILY_ALIASES.get(key, [])]:
            if cand and cand.lower() in self._tk_fams:
                return self._tk_fams[cand.lower()]
        return {"helv": "Helvetica", "tiro": "Times", "cour": "Courier"}[
            base14_name(key, False, False)[:4]]

    def _pixel(self, cx, cy):
        x, y = int(cx - self.MARGIN), int(cy - self.MARGIN)
        if 0 <= x < self._pil.width and 0 <= y < self._pil.height:
            r, g, b = self._pil.getpixel((x, y))[:3]
            return (r / 255.0, g / 255.0, b / 255.0)
        return None

    def _bg_under(self, rect):
        x0, y0, x1, y1 = self._rect_to_cv(rect)
        my = (y0 + y1) / 2
        probes = [(x0 - 3, my), (x1 + 3, my), ((x0 + x1) / 2, y0 - 3),
                  ((x0 + x1) / 2, y1 + 3), (x0 - 3, y0 - 3), (x1 + 3, y1 + 3)]
        samples = [p for p in (self._pixel(x, y) for x, y in probes) if p]
        if not samples:
            return "#FFFFFF"
        samples.sort(key=sum)
        return _hex(samples[len(samples) // 2])

    # ── Rendu (aperçu exact = même moteur que l'export) ─────────────────────
    def _render(self):
        if self._render_after:
            self.win.after_cancel(self._render_after)
            self._render_after = None
        self._prune()
        z = self._zoom()
        tmp = fitz.open()
        try:
            tmp.insert_pdf(self._doc, from_page=self.page.pg_idx, to_page=self.page.pg_idx)
            tp = tmp[0]
            if tp.rotation:
                tp.set_rotation(0)
            try:
                apply_edits_to_page(tp, self.edits, self._fcache)
            except Exception as ex:
                self._status(f"⚠  Aperçu partiel : {ex}")
            tp.set_rotation(self._eff_rotation())
            pix = tp.get_pixmap(matrix=fitz.Matrix(z, z), alpha=False)
            self._mat = tp.rotation_matrix * fitz.Matrix(z, z)
        finally:
            tmp.close()
        self._imat = ~self._mat
        self._pil = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
        self._photo = ImageTk.PhotoImage(self._pil)
        m = self.MARGIN
        self.canvas.delete("page")
        self.canvas.create_rectangle(m + 3, m + 3, m + pix.width + 3, m + pix.height + 3,
                                     fill="#5E636B", outline="", tags="page")
        self.canvas.create_image(m, m, image=self._photo, anchor="nw", tags="page")
        self.canvas.tag_lower("page")
        self.canvas.config(scrollregion=(0, 0, pix.width + 2 * m, pix.height + 2 * m))
        self.lbl_zoom.config(text=f"{int(z * 100)} %")
        self._items = self._compute_items()
        self._draw_overlays()
        self._update_stats()

    def _schedule_render(self, snap=False):
        if self._render_after:
            self.win.after_cancel(self._render_after)

        def run():
            self._render_after = None
            if self._inline is None:
                self._render()
            if snap:
                self._snap()
        self._render_after = self.win.after(120, run)

    def _draw_overlays(self):
        cv = self.canvas
        cv.delete("ov")
        show = self.var_showboxes.get()
        for item, r in self._items:
            if self._inline and self._inline["item"] == item:
                continue
            x0, y0, x1, y1 = self._rect_to_cv(r)
            x0, y0, x1, y1 = x0 - 2, y0 - 2, x1 + 2, y1 + 2
            if item == self._sel:
                cv.create_rectangle(x0, y0, x1, y1, outline=C["blue"], width=2, tags="ov")
            elif item == self._hover:
                cv.create_rectangle(x0, y0, x1, y1, outline=C["char_sel"], width=1,
                                    dash=(4, 2), tags="ov")
            elif self._is_edited(item):
                cv.create_rectangle(x0, y0, x1, y1, outline=C["orange"], width=1,
                                    dash=(3, 3), tags="ov")
            elif show:
                cv.create_rectangle(x0, y0, x1, y1, outline="#9DC3E6", width=1,
                                    dash=(2, 3), tags="ov")

    # ── Souris ──────────────────────────────────────────────────────────────
    def _on_motion(self, e):
        cx, cy = self._event_cv(e)
        if self._eyedropper:
            self._draw_dropper(cx, cy)
            return
        if self._mode == "add":
            return
        item = self._hit(*self._cv_to_pdf(cx, cy))
        if item != self._hover:
            self._hover = item
            self._draw_overlays()
        if item is None:
            self.canvas.config(cursor="arrow")
        else:
            self.canvas.config(cursor="fleur" if item == self._sel else "xterm")

    def _on_leave(self, e):
        self.canvas.delete("dropper")
        if self._hover is not None:
            self._hover = None
            self._draw_overlays()

    def _on_wheel(self, e, horizontal=False):
        step = -1 if e.delta > 0 else 1
        if abs(e.delta) >= 120:
            step *= 3
        if horizontal:
            self.canvas.xview_scroll(step, "units")
        else:
            self.canvas.yview_scroll(step, "units")

    def _on_press(self, e):
        self.canvas.focus_set()
        cx, cy = self._event_cv(e)
        if self._eyedropper:
            self._pick_from_page(cx, cy)
            return
        px, py = self._cv_to_pdf(cx, cy)
        if self._mode == "add":
            self._close_inline(True)
            self._set_mode("select")
            self._create_text_at(px, py)
            return
        if self._inline:
            self._close_inline(True)
        item = self._hit(px, py)
        self._press = {"item": item, "cx": cx, "cy": cy, "px": px, "py": py, "moved": False}
        if item != self._sel:
            self._sel = item
            self._update_panel()
            self._draw_overlays()

    def _on_drag(self, e):
        p = self._press
        if not p or p["item"] is None or self._eyedropper:
            return
        cx, cy = self._event_cv(e)
        if not p["moved"] and abs(cx - p["cx"]) + abs(cy - p["cy"]) < 4:
            return
        p["moved"] = True
        x0, y0, x1, y1 = self._rect_to_cv(self._item_rect(p["item"]))
        dx, dy = cx - p["cx"], cy - p["cy"]
        self.canvas.delete("ghost")
        self.canvas.create_rectangle(x0 + dx - 2, y0 + dy - 2, x1 + dx + 2, y1 + dy + 2,
                                     outline=C["blue"], width=2, dash=(5, 3), tags="ghost")
        self.canvas.config(cursor="fleur")

    def _on_release(self, e):
        p, self._press = self._press, None
        self.canvas.delete("ghost")
        if not p or self._eyedropper:
            return
        if p["item"] is None:
            if self._sel is not None:
                self._sel = None
                self._update_panel()
                self._draw_overlays()
            return
        if p["moved"]:
            px, py = self._cv_to_pdf(*self._event_cv(e))
            ed = self._get_edit(p["item"], create=True)
            ed.origin = (ed.origin[0] + px - p["px"], ed.origin[1] + py - p["py"])
            ed.pinned = True
            if p["item"][0] == "seg":
                self._reflow_line(p["item"][1])
            self._render()
            self._snap()
            self._update_panel()
            self._status("✔  Texte déplacé  ·  flèches du clavier pour ajuster finement")
        else:
            self._open_inline(p["item"], click_pdf=(p["px"], p["py"]))

    # ── Édition directe sur la page ─────────────────────────────────────────
    def _tk_font(self, ed):
        px = max(5, int(round(ed.size * self._zoom())))
        return tkfont.Font(root=self.win, family=self._tk_family(ed.family), size=-px,
                           weight="bold" if ed.bold else "normal",
                           slant="italic" if ed.italic else "roman")

    def _place_inline(self):
        inl = self._inline
        ed = self._props(inl["item"])
        if self._eff_rotation() == 0 and not ed.angle:
            bx, by = self._pdf_to_cv(*ed.origin)
            left, top = bx - 2, by - inl["font"].metrics("ascent") - 1
        else:
            x0, y0, _, _ = self._rect_to_cv(self._item_rect(inl["item"]))
            left, top = x0 - 2, y0 - 2
        self.canvas.coords(inl["id"], left, top)

    def _open_inline(self, item, click_pdf=None, select_all=False):
        if item is None:
            return
        self._close_inline(True)
        self._cancel_eyedropper()
        self._sel = item
        ed = self._props(item)
        rect = self._item_rect(item)
        x0, y0, x1, y1 = self._rect_to_cv(rect)
        font = self._tk_font(ed)
        fg = _hex(ed.color)
        bg = _hex(ed.bg) if ed.bg is not None else self._bg_under(rect)
        w = tk.Text(self.canvas, font=font, fg=fg, bg=bg, insertbackground=fg,
                    insertwidth=2, relief="flat", bd=0, highlightthickness=1,
                    highlightbackground=C["blue"], highlightcolor=C["blue"],
                    wrap="none", undo=True, padx=1, pady=0,
                    selectbackground=C["char_sel_bg"], selectforeground="#000000")
        w.insert("1.0", ed.text)
        w.edit_reset()
        # Keep the toplevel/global shortcuts (Delete, Ctrl+Z…) out of the text field
        w.bindtags((str(w), "Text"))
        w.bind("<Return>", self._inline_enter)
        w.bind("<KP_Enter>", self._inline_enter)
        w.bind("<Shift-Return>", lambda ev: None)
        w.bind("<Escape>", lambda ev: (self._close_inline(False), "break")[1])
        w.bind("<Tab>", self._inline_enter)
        w.bind("<KeyRelease>", lambda ev: self._inline_autosize())
        w.bind("<Control-a>", lambda ev: (w.tag_add("sel", "1.0", "end-1c"), "break")[1])
        w.bind("<Control-s>", lambda ev: (self._on_save(), "break")[1])
        wid = self.canvas.create_window(x0, y0, window=w, anchor="nw", tags="inline")
        self._inline = {"w": w, "id": wid, "item": item, "font": font,
                        "orig_text": ed.text, "min_w": x1 - x0 + 8}
        self._place_inline()
        self._inline_autosize()
        index = "end-1c"
        if click_pdf and item[0] == "seg" and self._edit_for_seg(item[1]) is None:
            seg = self._seg_by_key[item[1]]
            if seg["angle"] == 0.0 and self._eff_rotation() == 0:
                n = sum(1 for b in seg["chars"] if (b[0] + b[2]) / 2 < click_pdf[0])
                index = f"1.{n}"
        w.mark_set("insert", index)
        if select_all:
            w.tag_add("sel", "1.0", "end-1c")
        w.focus_set()
        self._update_panel()
        self._draw_overlays()
        self._status("✏  Saisissez votre texte  ·  Entrée : valider  ·  "
                     "Maj+Entrée : nouvelle ligne  ·  Échap : annuler")

    def _inline_enter(self, e=None):
        self._close_inline(True)
        return "break"

    def _inline_autosize(self):
        inl = self._inline
        if not inl:
            return
        font = inl["font"]
        lines = inl["w"].get("1.0", "end-1c").split("\n")
        width = max([font.measure(line) for line in lines] + [0]) + font.measure("  ") + 6
        width = max(width, inl["min_w"], 30)
        height = len(lines) * font.metrics("linespace") + 4
        self.canvas.itemconfig(inl["id"], width=width, height=height)

    def _restyle_inline(self):
        inl = self._inline
        if not inl:
            return
        ed = self._props(inl["item"])
        font = self._tk_font(ed)
        fg = _hex(ed.color)
        bg = _hex(ed.bg) if ed.bg is not None else self._bg_under(self._item_rect(inl["item"]))
        inl["w"].config(font=font, fg=fg, insertbackground=fg, bg=bg)
        inl["font"] = font
        self._place_inline()
        self._inline_autosize()

    def _close_inline(self, commit=True, render=True):
        inl = self._inline
        if not inl:
            return False
        self._inline = None
        text = inl["w"].get("1.0", "end-1c")
        try:
            self.canvas.delete(inl["id"])
            inl["w"].destroy()
        except tk.TclError:
            pass
        item = inl["item"]
        if commit and text != inl["orig_text"]:
            if item[0] == "add":
                ed = self._get_edit(item)
                if ed is not None:
                    if text.strip():
                        ed.text = text
                    else:
                        self.edits.remove(ed)
                        self._sel = None
            else:
                ed = self._get_edit(item, create=True)
                if text.strip():
                    ed.kind, ed.text = "replace", text
                else:
                    ed.kind, ed.text = "delete", ""
                    self._sel = None
                self._reflow_line(item[1])
        if render:
            self._render()
            self._snap()
            self._update_panel()
            self._status("✔  Texte mis à jour" if commit else "Modification annulée")
        self.canvas.focus_set()
        return True

    def _edit_selected(self):
        if self._sel is not None and self._inline is None:
            self._open_inline(self._sel)

    def _edit_or_commit(self):
        if self._inline:
            self._close_inline(True)
        else:
            self._edit_selected()

    def _create_text_at(self, px, py):
        try:
            size = float(self.var_size.get().replace(",", "."))
        except ValueError:
            size = 12.0
        size = min(max(size, 4.0), 200.0)
        family = self.var_font.get()
        if not family or family.startswith("★"):
            family = self._default_family()
        ed = Edit("add", text="Nouveau texte", family=family, size=size,
                  color=self._color, bg=self._bg, bold=self.var_bold.get(),
                  italic=self.var_italic.get(), origin=(px, py + size * 0.35),
                  uid=self._next_uid)
        self._next_uid += 1
        self.edits.append(ed)
        self._sel = ("add", ed.uid)
        self._render()
        self._snap()
        self._open_inline(self._sel, select_all=True)

    # ── Propriétés ──────────────────────────────────────────────────────────
    def _update_panel(self):
        self._loading = True
        try:
            item = self._sel
            ed = self._props(item) if item else None
            values = ([self._orig_label(ed)] if ed is not None and ed.orig_font else []) \
                + self._families_list()
            self.cb_font.config(values=values)
            if ed is None:
                self.lbl_sel.config(
                    text=f"{len(self._segments)} zones de texte détectées sur cette page.\n"
                         "Cliquez sur n'importe quel texte pour le modifier directement, "
                         "glissez-le pour le déplacer.",
                    bg=C["bg2"], fg=C["mid"])
                for w in self._prop_widgets:
                    w.config(state="disabled")
                return
            for w in self._prop_widgets:
                w.config(state="normal")
            self.cb_font.config(state="readonly")
            if item[0] == "seg":
                seg = self._seg_by_key[item[1]]
                state = "modifié" if self._edit_for_seg(item[1]) else "original"
                style = ", ".join(x for x in ("gras" if seg["bold"] else "",
                                              "italique" if seg["italic"] else "") if x)
                warn = ""
                kind = resolve_font(self._fpg, ed, self._fcache)[0]
                if kind == "base14" and font_family_key(ed.family) not in (
                        "helvetica", "times", "courier", "symbol", "zapfdingbats"):
                    warn = ("\n⚠ Police non installée sur ce poste : "
                            "une police proche sera utilisée pour le texte modifié.")
                self.lbl_sel.config(
                    text=f"Texte détecté ({state})\nPolice d'origine : "
                         f"{font_display_name(seg['font']) or '?'}  ·  {seg['size']:g} pt"
                         + (f"  ·  {style}" if style else "") + warn,
                    bg=C["blue_lt"], fg=C["orange"] if warn else C["navy"])
                self.btn_revert.config(
                    state="normal" if self._edit_for_seg(item[1]) else "disabled")
            else:
                self.lbl_sel.config(text="Texte ajouté\nGlissez-le pour le déplacer.",
                                    bg=C["blue_lt"], fg=C["navy"])
                self.btn_revert.config(state="disabled")
            self.btn_edit.config(text="✔  Valider le texte" if self._inline
                                 else "✏  Modifier ce texte")
            self.var_font.set(self._family_label(ed))
            self.var_size.set(f"{ed.size:g}")
            self.var_bold.set(bool(ed.bold))
            self.var_italic.set(bool(ed.italic))
            self._color = tuple(ed.color)
            self.swatch_text.config(bg=_hex(ed.color))
            self._bg = ed.bg
            self.var_bgmode.set("orig" if ed.bg is None else "color")
            self.swatch_bg.config(bg=_hex(ed.bg) if ed.bg is not None else C["white"])
            self.var_angle.set(f"{ed.angle:g}")
        finally:
            self._loading = False
            self._update_stats()

    def _on_prop(self, field):
        if self._loading or self._sel is None:
            return
        ed = self._get_edit(self._sel, create=True)
        if field == "family":
            value = self.var_font.get()
            ed.family = ed.orig_font if value.startswith("★") and ed.orig_font else value
        elif field in ("size", "angle"):
            var = self.var_size if field == "size" else self.var_angle
            try:
                value = float(var.get().replace(",", "."))
            except ValueError:
                return
            if field == "size":
                if not 2 <= value <= 400:
                    return
                ed.size = value
            else:
                ed.angle = ((value + 180.0) % 360.0) - 180.0 if abs(value) > 180 else value
        elif field == "bold":
            ed.bold = self.var_bold.get()
        elif field == "italic":
            ed.italic = self.var_italic.get()
        self._after_prop_change()

    def _after_prop_change(self):
        if self._sel is not None and self._sel[0] == "seg":
            self._reflow_line(self._sel[1])
        if self._inline:
            self._restyle_inline()
        self._schedule_render(snap=True)

    def _set_text_color(self, rgb):
        self._color = tuple(rgb)
        self.swatch_text.config(bg=_hex(rgb))
        if self._sel is not None and not self._loading:
            self._get_edit(self._sel, create=True).color = tuple(rgb)
            self._after_prop_change()

    def _set_bg_color(self, rgb):
        self._bg = tuple(rgb)
        self.var_bgmode.set("color")
        self.swatch_bg.config(bg=_hex(rgb))
        if self._sel is not None and not self._loading:
            self._get_edit(self._sel, create=True).bg = tuple(rgb)
            self._after_prop_change()

    def _on_bgmode(self):
        if self.var_bgmode.get() == "orig":
            if self._eyedropper == "bg":
                self._cancel_eyedropper()
            self._bg = None
            self.swatch_bg.config(bg=C["white"])
            if self._sel is not None:
                self._get_edit(self._sel, create=True).bg = None
                self._after_prop_change()
        else:
            self._start_eyedropper("bg")

    def _pick_color(self, which):
        cur = self._color if which == "text" else (self._bg or (1, 1, 1))
        rgb, _ = colorchooser.askcolor(color=_hex(cur), parent=self.win)
        if rgb:
            rgb = tuple(c / 255.0 for c in rgb)
            if which == "text":
                self._set_text_color(rgb)
            else:
                self._set_bg_color(rgb)

    # ── Pipette ─────────────────────────────────────────────────────────────
    def _start_eyedropper(self, which):
        self._eyedropper = which
        self.canvas.config(cursor="crosshair")
        target = "du texte" if which == "text" else "de fond"
        self._status(f"💧  Pipette : cliquez sur la page pour prélever la couleur {target}"
                     "  ·  Échap ou clic droit pour annuler")

    def _cancel_eyedropper(self):
        if not self._eyedropper:
            return
        which, self._eyedropper = self._eyedropper, None
        self.canvas.delete("dropper")
        self.canvas.config(cursor="arrow")
        if which == "bg" and self._bg is None:
            self.var_bgmode.set("orig")
        self._status("Pipette annulée")

    def _draw_dropper(self, cx, cy):
        self.canvas.delete("dropper")
        rgb = self._pixel(cx, cy)
        if rgb is None:
            return
        x, y = cx + 18, cy + 18
        self.canvas.create_rectangle(x, y, x + 34, y + 34, fill=_hex(rgb),
                                     outline="#000000", width=2, tags="dropper")
        self.canvas.create_rectangle(x, y + 36, x + 64, y + 52, fill="#FFFFFF",
                                     outline="#888888", tags="dropper")
        self.canvas.create_text(x + 32, y + 44, text=_hex(rgb).upper(),
                                font=("Helvetica", 8), tags="dropper")

    def _pick_from_page(self, cx, cy):
        rgb = self._pixel(cx, cy)
        which, self._eyedropper = self._eyedropper, None
        self.canvas.delete("dropper")
        self.canvas.config(cursor="arrow")
        if rgb is None:
            if which == "bg" and self._bg is None:
                self.var_bgmode.set("orig")
            self._status("⚠  Cliquez sur la page pour prélever une couleur")
            return
        if which == "text":
            self._set_text_color(rgb)
        else:
            self._set_bg_color(rgb)
        self._status(f"💧  Couleur prélevée : {_hex(rgb).upper()}")

    # ── Actions ─────────────────────────────────────────────────────────────
    def _set_mode(self, mode):
        if mode == "add":
            self._close_inline(True)
        self._mode = mode
        self.lbl_mode.config(text="Mode : " + ("Ajout de texte" if mode == "add"
                                               else "Modification du texte"))
        self.btn_select.config(bg=C["blue"] if mode == "select" else C["white"],
                               fg=C["white"] if mode == "select" else C["text"])
        self.btn_add.config(bg=C["blue"] if mode == "add" else C["white"],
                            fg=C["white"] if mode == "add" else C["text"])
        if mode == "add":
            self.canvas.config(cursor="crosshair")
            self._status("➕  Cliquez sur la page à l'endroit où ajouter le texte")
        else:
            self.canvas.config(cursor="arrow")
            self._status("Cliquez sur un texte pour le modifier  ·  glissez pour le déplacer"
                         "  ·  Suppr pour l'effacer  ·  Ctrl+Z / Ctrl+Y")

    def _on_escape(self):
        if self._eyedropper:
            self._cancel_eyedropper()
        elif self._inline:
            self._close_inline(False)
        elif self._mode == "add":
            self._set_mode("select")
        elif self._sel is not None:
            self._sel = None
            self._update_panel()
            self._draw_overlays()

    def _delete_selected(self):
        item = self._sel
        if item is None:
            self._status("⚠  Sélectionnez d'abord un texte")
            return
        self._close_inline(False, render=False)
        if item[0] == "add":
            ed = self._get_edit(item)
            if ed is not None:
                self.edits.remove(ed)
        else:
            ed = self._get_edit(item, create=True)
            ed.kind, ed.text = "delete", ""
            self._reflow_line(item[1])
        self._sel = None
        self._render()
        self._snap()
        self._update_panel()
        self._status("🗑  Texte supprimé  ·  Ctrl+Z pour annuler")

    def _revert_selected(self):
        item = self._sel
        if item is None or item[0] != "seg":
            return
        self._close_inline(False, render=False)
        self.edits = [e for e in self.edits if e.seg_key != item[1]]
        self._reflow_line(item[1])
        self._render()
        self._snap()
        self._update_panel()
        self._status("↺  Texte d'origine rétabli")

    def _nudge(self, dx, dy):
        if self._inline or self._sel is None:
            return
        m = self._imat
        dpx, dpy = dx * m.a + dy * m.c, dx * m.b + dy * m.d
        ed = self._get_edit(self._sel, create=True)
        ed.origin = (ed.origin[0] + dpx, ed.origin[1] + dpy)
        ed.pinned = True
        if self._sel[0] == "seg":
            self._reflow_line(self._sel[1])
        self._items = self._compute_items()
        self._draw_overlays()
        self._schedule_render(snap=True)

    def _rotate(self, delta):
        self._close_inline(True, render=False)
        self.rotation = (self._eff_rotation() + delta) % 360
        self._render()
        self._snap()
        self._status(f"⟳  Rotation de la page : {self._eff_rotation()}°")

    def _set_zoom(self, delta):
        idx = min(max(self._zoom_idx + delta, 0), len(self.ZOOMS) - 1)
        if idx == self._zoom_idx:
            return
        self._close_inline(True, render=False)
        self._zoom_idx = idx
        self._render()

    def _update_stats(self):
        n_rep = sum(1 for e in self.edits if e.kind == "replace")
        n_del = sum(1 for e in self.edits if e.kind == "delete")
        n_add = sum(1 for e in self.edits if e.kind == "add")
        self.lbl_stats.config(
            text=f"Zones détectées : {len(self._segments)}\n"
                 f"Modifiés : {n_rep}  ·  Supprimés : {n_del}  ·  Ajoutés : {n_add}\n"
                 f"Rotation de la page : {self._eff_rotation()}°")

    # ── Annuler / Rétablir ──────────────────────────────────────────────────
    def _signature(self):
        return (self.rotation, tuple(e.state() + (e.uid, e.seg_key) for e in self.edits))

    def _snap(self):
        sig = self._signature()
        if self._hist and self._hist[self._hist_idx]["sig"] == sig:
            self._upd_btns()
            return
        self._hist = self._hist[: self._hist_idx + 1]
        self._hist.append({"sig": sig, "rotation": self.rotation,
                           "edits": copy.deepcopy(self.edits)})
        if len(self._hist) > self._max_hist:
            self._hist.pop(0)
        else:
            self._hist_idx += 1
        self._upd_btns()
        self._update_stats()

    def _restore(self, idx, msg):
        self._close_inline(False, render=False)
        self._hist_idx = idx
        s = self._hist[idx]
        self.rotation = s["rotation"]
        self.edits = copy.deepcopy(s["edits"])
        self._sel = None
        self._render()
        self._update_panel()
        self._upd_btns()
        self._status(msg)

    def _undo(self):
        if self._inline:
            self._close_inline(True)
        if self._hist_idx <= 0:
            self._status("Rien à annuler")
            return
        self._restore(self._hist_idx - 1, "↶  Annulé")

    def _redo(self):
        if self._hist_idx >= len(self._hist) - 1:
            self._status("Rien à rétablir")
            return
        self._restore(self._hist_idx + 1, "↷  Rétabli")

    def _upd_btns(self):
        self.btn_eundo.config(state="normal" if self._hist_idx > 0 else "disabled")
        self.btn_eredo.config(
            state="normal" if self._hist_idx < len(self._hist) - 1 else "disabled")

    # ── Enregistrer / fermer ────────────────────────────────────────────────
    def _make_thumb(self):
        tmp = fitz.open()
        try:
            tmp.insert_pdf(self._doc, from_page=self.page.pg_idx, to_page=self.page.pg_idx)
            tp = tmp[0]
            tp.set_rotation(0)
            apply_edits_to_page(tp, self.edits, self._fcache)
            tp.set_rotation(self._src_rot)
            pix = tp.get_pixmap(matrix=fitz.Matrix(0.30, 0.30), alpha=False)
            img = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
            return img.resize((THUMB_W, THUMB_H), Image.LANCZOS)
        except Exception:
            return None
        finally:
            tmp.close()

    def _on_save(self):
        self._close_inline(True, render=False)
        self._prune()
        thumb = self._make_thumb() if self.edits else None
        self.app.on_editor_save(self.pos, self.rotation, self.edits, thumb)
        self._close()

    def _on_cancel(self):
        typing = self._inline and self._inline["w"].get("1.0", "end-1c") != self._inline["orig_text"]
        if self._hist_idx > 0 or typing:
            if not messagebox.askyesno("Confirmer",
                                       "Fermer sans enregistrer les modifications ?",
                                       parent=self.win):
                return
        self._close()

    def _close(self):
        if self._render_after:
            self.win.after_cancel(self._render_after)
            self._render_after = None
        try:
            self._doc.close()
        except Exception:
            pass
        self.win.destroy()


# ══════════════════════════════════════════════════════════════════════════════
#  PRINT DIALOG  — style PDFCreator
# ══════════════════════════════════════════════════════════════════════════════
class PrintDialog:
    """Dialogue d'impression style Word/Excel/Adobe avec détection CUPS,
    aperçu réel de la page et toutes les options standard."""

    PAPER_SIZES = {
        "A4  (210 × 297 mm)":     ("A4",      210, 297),
        "A3  (297 × 420 mm)":     ("A3",      297, 420),
        "A5  (148 × 210 mm)":     ("A5",      148, 210),
        "Letter  (216 × 279 mm)": ("Letter",  216, 279),
        "Legal  (216 × 356 mm)":  ("Legal",   216, 356),
        "Tabloid  (279 × 432 mm)":("Tabloid", 279, 432),
        "B4  (257 × 364 mm)":     ("B4",      257, 364),
        "B5  (176 × 250 mm)":     ("B5",      176, 250),
        "Enveloppe DL (110×220)": ("DL",      110, 220),
    }
    SIDES = {
        "Imprimer sur une face":           "one-sided",
        "Recto-verso (bord long)":         "two-sided-long-edge",
        "Recto-verso (bord court)":        "two-sided-short-edge",
    }
    RANGE_LABELS = {
        "Toutes les pages":       "all",
        "Page sélectionnée":      "current",
        "Pages paires":           "even",
        "Pages impaires":         "odd",
        "Plage personnalisée…":   "custom",
    }
    QUALITY_MAP = {
        "Brouillon (rapide)":     "3",
        "Normale":                "4",
        "Haute qualité":          "5",
    }
    SCALE_OPTS = ["Ajuster à la page", "100 %", "75 %", "50 %", "125 %", "150 %"]

    def __init__(self, app):
        self.app = app
        self._tmp_pdf = None
        self._printers_info = {}   # name -> {status, location, is_default}
        self._preview_page_idx = 0
        self._preview_photo = None

        self.win = tk.Toplevel(app.root)
        self.win.title("Imprimer")
        self.win.geometry("900x660")
        self.win.minsize(820, 580)
        self.win.configure(bg="#F0F0F0")
        self.win.transient(app.root)
        self.win.grab_set()
        self.win.protocol("WM_DELETE_WINDOW", self._cancel)
        self._build_ui()
        self._load_printers_async()

    # ─── Construction UI (style Word) ─────────────────────────────────────────
    def _build_ui(self):
        # ── Titre ──
        hdr = tk.Frame(self.win, bg="#2B579A", height=54)
        hdr.pack(fill=tk.X)
        hdr.pack_propagate(False)
        tk.Frame(hdr, bg="#E8A000", width=5).pack(side=tk.LEFT, fill=tk.Y)
        tk.Label(hdr, text="Imprimer", font=("Helvetica", 16, "bold"),
                 fg="white", bg="#2B579A", padx=18).pack(side=tk.LEFT, pady=10)
        n_pages = len(self.app.pages)
        tk.Label(hdr, text=f"{n_pages} page(s)",
                 font=("Helvetica", 9), fg="#BDD7EE", bg="#2B579A").pack(side=tk.LEFT)
        tk.Button(hdr, text="✕", command=self._cancel,
                  font=("Helvetica", 11), bg="#2B579A", fg="#BDD7EE",
                  relief="flat", cursor="hand2", padx=10, pady=4,
                  activebackground="#1a3f7a", activeforeground="white"
                  ).pack(side=tk.RIGHT, padx=6, pady=8)

        # ── Corps principal : gauche (paramètres) + droite (aperçu) ──
        body = tk.Frame(self.win, bg="#F0F0F0")
        body.pack(fill=tk.BOTH, expand=True)

        # ── Colonne gauche ──
        left_outer = tk.Frame(body, bg="#F0F0F0", width=380)
        left_outer.pack(side=tk.LEFT, fill=tk.Y)
        left_outer.pack_propagate(False)

        # Bouton Imprimer + Copies (comme Word, tout en haut)
        top_bar = tk.Frame(left_outer, bg="#F0F0F0")
        top_bar.pack(fill=tk.X, padx=20, pady=(16, 8))
        self.btn_print = tk.Button(top_bar, text="Imprimer",
                  command=self._do_print,
                  font=("Helvetica", 10, "bold"), bg="#2B579A", fg="white",
                  relief="flat", activebackground="#1a3f7a", activeforeground="white",
                  cursor="hand2", padx=20, pady=7, width=10)
        self.btn_print.pack(side=tk.LEFT)
        tk.Label(top_bar, text="Copies :", font=("Helvetica", 9),
                 bg="#F0F0F0", fg="#333").pack(side=tk.LEFT, padx=(16, 4))
        self.var_copies = tk.IntVar(value=1)
        copies_frame = tk.Frame(top_bar, bg="white",
                                highlightthickness=1, highlightbackground="#AAA")
        copies_frame.pack(side=tk.LEFT)
        tk.Button(copies_frame, text="−", command=lambda: self._adj_copies(-1),
                  font=("Helvetica", 10, "bold"), bg="white", fg="#333",
                  relief="flat", cursor="hand2", padx=6, pady=2,
                  activebackground="#E8E8E8").pack(side=tk.LEFT)
        self.lbl_copies = tk.Label(copies_frame, textvariable=self.var_copies,
                                   font=("Helvetica", 10), bg="white", fg="#333",
                                   width=3, anchor="center")
        self.lbl_copies.pack(side=tk.LEFT)
        tk.Button(copies_frame, text="+", command=lambda: self._adj_copies(+1),
                  font=("Helvetica", 10, "bold"), bg="white", fg="#333",
                  relief="flat", cursor="hand2", padx=6, pady=2,
                  activebackground="#E8E8E8").pack(side=tk.LEFT)

        # Séparateur
        tk.Frame(left_outer, bg="#CCCCCC", height=1).pack(fill=tk.X, padx=20, pady=4)

        # Zone défilable pour les paramètres
        scroll_frame = tk.Frame(left_outer, bg="#F0F0F0")
        scroll_frame.pack(fill=tk.BOTH, expand=True, padx=20)

        # ── Imprimante ──
        self._wlabel(scroll_frame, "Imprimante")
        printer_box = tk.Frame(scroll_frame, bg="white",
                               highlightthickness=1, highlightbackground="#AAAAAA")
        printer_box.pack(fill=tk.X, pady=(2, 0))
        self.var_printer = tk.StringVar(value="Recherche des imprimantes…")
        self.cb_printer = ttk.Combobox(printer_box, textvariable=self.var_printer,
                                       state="readonly", font=("Helvetica", 9),
                                       width=32)
        self.cb_printer.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=4, pady=4)
        self.cb_printer.bind("<<ComboboxSelected>>", self._on_printer_change)
        tk.Button(printer_box, text="⟳", command=self._load_printers_async,
                  font=("Helvetica", 9), bg="white", relief="flat",
                  cursor="hand2", padx=6, pady=3,
                  activebackground="#E8E8E8").pack(side=tk.RIGHT, padx=2)

        # Info imprimante (état, localisation)
        self.lbl_printer_info = tk.Label(scroll_frame,
                text="", font=("Helvetica", 8, "italic"),
                bg="#F0F0F0", fg="#666", anchor="w", justify=tk.LEFT)
        self.lbl_printer_info.pack(fill=tk.X, pady=(2, 0))

        tk.Button(scroll_frame, text="Propriétés de l'imprimante…",
                  command=self._open_printer_props,
                  font=("Helvetica", 8), bg="#F0F0F0", fg="#2B579A",
                  relief="flat", cursor="hand2", anchor="w",
                  activeforeground="#1a3f7a").pack(anchor="w", pady=(2, 8))

        tk.Frame(scroll_frame, bg="#CCCCCC", height=1).pack(fill=tk.X, pady=4)

        # ── Paramètres (style Word : dropdowns) ──
        self._wlabel(scroll_frame, "Paramètres")

        # Plage de pages
        self.var_range_label = tk.StringVar(value="Toutes les pages")
        self._wdroprow(scroll_frame, "🔢", self.var_range_label,
                       list(self.RANGE_LABELS.keys()),
                       self._on_range_change)
        # Plage personnalisée (cachée par défaut)
        self.custom_range_frame = tk.Frame(scroll_frame, bg="#F0F0F0")
        tk.Label(self.custom_range_frame, text="  Pages :", font=("Helvetica", 8),
                 bg="#F0F0F0", fg="#333").pack(side=tk.LEFT)
        self.var_custom_pages = tk.StringVar(value="1")
        tk.Entry(self.custom_range_frame, textvariable=self.var_custom_pages,
                 font=("Helvetica", 9), width=14,
                 highlightthickness=1, highlightbackground="#AAA"
                 ).pack(side=tk.LEFT, padx=6)
        tk.Label(self.custom_range_frame,
                 text="ex: 1,3,5-8", font=("Helvetica", 7, "italic"),
                 bg="#F0F0F0", fg="#888").pack(side=tk.LEFT)

        # Impression recto/recto-verso
        self.var_sides_label = tk.StringVar(value="Imprimer sur une face")
        self._wdroprow(scroll_frame, "📄", self.var_sides_label,
                       list(self.SIDES.keys()))

        # Assemblage
        self.var_collate_label = tk.StringVar(value="Assemblé  1,2,3  1,2,3")
        self._wdroprow(scroll_frame, "📋", self.var_collate_label,
                       ["Assemblé  1,2,3  1,2,3", "Non assemblé  1,1,1  2,2,2"])

        # Orientation
        self.var_orient_label = tk.StringVar(value="Portrait")
        self._wdroprow(scroll_frame, "↕", self.var_orient_label,
                       ["Portrait", "Paysage"],
                       lambda: self._refresh_preview())

        # Format papier
        self.var_paper = tk.StringVar(value="A4  (210 × 297 mm)")
        self._wdroprow(scroll_frame, "📐", self.var_paper,
                       list(self.PAPER_SIZES.keys()),
                       lambda: self._refresh_preview())

        # Marges
        self.var_margins = tk.StringVar(value="Marges normales")
        self._wdroprow(scroll_frame, "⊞", self.var_margins,
                       ["Marges normales", "Marges étroites", "Marges larges",
                        "Marges personnalisées…"])

        # Pages par feuille / Mise à l'échelle
        self.var_scale = tk.StringVar(value="Ajuster à la page")
        self._wdroprow(scroll_frame, "⊡", self.var_scale, self.SCALE_OPTS)

        tk.Frame(scroll_frame, bg="#CCCCCC", height=1).pack(fill=tk.X, pady=4)

        # ── Options avancées (pliables) ──
        self._wlabel(scroll_frame, "Options avancées")
        adv = tk.Frame(scroll_frame, bg="#F0F0F0")
        adv.pack(fill=tk.X, pady=(2, 6))

        # Qualité
        tk.Label(adv, text="Qualité :", font=("Helvetica", 8),
                 bg="#F0F0F0", fg="#555").grid(row=0, column=0, sticky="w", pady=2)
        self.var_quality = tk.StringVar(value="Normale")
        ttk.Combobox(adv, textvariable=self.var_quality,
                     values=list(self.QUALITY_MAP.keys()),
                     state="readonly", font=("Helvetica", 8), width=18
                     ).grid(row=0, column=1, sticky="w", padx=8, pady=2)

        # Couleur
        tk.Label(adv, text="Couleur :", font=("Helvetica", 8),
                 bg="#F0F0F0", fg="#555").grid(row=1, column=0, sticky="w", pady=2)
        self.var_color_mode = tk.StringVar(value="Couleur")
        ttk.Combobox(adv, textvariable=self.var_color_mode,
                     values=["Couleur", "Niveaux de gris", "Noir pur"],
                     state="readonly", font=("Helvetica", 8), width=18
                     ).grid(row=1, column=1, sticky="w", padx=8, pady=2)

        # Barre de statut bas
        self.lbl_status = tk.Label(left_outer, text="",
                                   font=("Helvetica", 8), bg="#F0F0F0",
                                   fg="#555", anchor="w", padx=20)
        self.lbl_status.pack(fill=tk.X, pady=(4, 8))

        # ── Colonne droite : aperçu ──
        right = tk.Frame(body, bg="#E0E0E0")
        right.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)

        # Header aperçu
        tk.Label(right, text="Aperçu", font=("Helvetica", 9, "bold"),
                 bg="#D0D0D0", fg="#333", pady=6, anchor="center"
                 ).pack(fill=tk.X)

        # Canvas aperçu
        self.preview_canvas = tk.Canvas(right, bg="#808080",
                                        highlightthickness=0)
        self.preview_canvas.pack(fill=tk.BOTH, expand=True, padx=20, pady=12)

        # Navigation pages
        nav = tk.Frame(right, bg="#E0E0E0")
        nav.pack(pady=(0, 10))
        tk.Button(nav, text="◀", command=self._prev_preview,
                  font=("Helvetica", 9), bg="#E0E0E0", relief="flat",
                  cursor="hand2", padx=8).pack(side=tk.LEFT)
        self.lbl_preview_num = tk.Label(nav,
                text=f"Page 1 sur {max(1, len(self.app.pages))}",
                font=("Helvetica", 8), bg="#E0E0E0", fg="#333", padx=8)
        self.lbl_preview_num.pack(side=tk.LEFT)
        tk.Button(nav, text="▶", command=self._next_preview,
                  font=("Helvetica", 9), bg="#E0E0E0", relief="flat",
                  cursor="hand2", padx=8).pack(side=tk.LEFT)

        # Affichage différé de l'aperçu
        self.win.after(200, self._refresh_preview)

    def _wlabel(self, parent, text):
        tk.Label(parent, text=text, font=("Helvetica", 8, "bold"),
                 bg="#F0F0F0", fg="#555", anchor="w", pady=4
                 ).pack(fill=tk.X)

    def _wdroprow(self, parent, icon, var, values, callback=None):
        row = tk.Frame(parent, bg="white",
                       highlightthickness=1, highlightbackground="#CCCCCC")
        row.pack(fill=tk.X, pady=1)
        tk.Label(row, text=icon, font=("Helvetica", 11),
                 bg="white", fg="#444", padx=8, pady=5).pack(side=tk.LEFT)
        cb = ttk.Combobox(row, textvariable=var, values=values,
                          state="readonly", font=("Helvetica", 9))
        cb.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=4)
        if callback:
            cb.bind("<<ComboboxSelected>>", lambda e: callback())
        return cb

    def _adj_copies(self, delta):
        v = max(1, min(999, self.var_copies.get() + delta))
        self.var_copies.set(v)

    # ─── Chargement imprimantes ────────────────────────────────────────────────
    def _load_printers_async(self):
        self.var_printer.set("Recherche des imprimantes…")
        self.lbl_printer_info.config(text="Interrogation de CUPS…", fg="#888")
        self.win.after(80, lambda: threading.Thread(
            target=self._fetch_printers, daemon=True).start())

    def _fetch_printers(self):
        info = self._query_cups()
        self.win.after(0, lambda: self._populate_printers(info))

    def _query_cups(self):
        """Interroge CUPS via cups Python module, ou lpstat en fallback."""
        printers = {}
        # 1) Essai avec le module cups (plus riche)
        try:
            import cups as cups_mod
            conn = cups_mod.Connection()
            dests = conn.getDests()
            default_name = None
            try:
                default_name = conn.getDefault()
            except Exception:
                pass
            for (name, instance), dest in dests.items():
                if name is None:
                    continue
                attrs = {}
                try:
                    attrs = conn.getPrinterAttributes(name)
                except Exception:
                    pass
                state_map = {3: "Prête", 4: "Impression…", 5: "Erreur"}
                state_int = attrs.get("printer-state", 3)
                if isinstance(state_int, list):
                    state_int = state_int[0]
                state = state_map.get(state_int, "Inconnue")
                location = attrs.get("printer-location", "")
                if isinstance(location, list):
                    location = location[0] if location else ""
                make = attrs.get("printer-make-and-model", "")
                if isinstance(make, list):
                    make = make[0] if make else ""
                printers[name] = {
                    "status":   state,
                    "location": location,
                    "model":    make,
                    "default":  (name == default_name),
                }
            return printers
        except Exception:
            pass

        # 2) Fallback: lpstat
        try:
            r = subprocess.run(["lpstat", "-l", "-p"],
                               capture_output=True, text=True, timeout=8)
            current = None
            for line in r.stdout.splitlines():
                # "printer HP_LaserJet is idle."
                if line.startswith("printer ") or line.startswith("imprimante "):
                    parts = line.split()
                    if len(parts) > 1:
                        current = parts[1]
                        status = "Prête"
                        if "idle" in line.lower() or "disponible" in line.lower():
                            status = "Prête"
                        elif "processing" in line.lower():
                            status = "Impression…"
                        elif "stopped" in line.lower() or "arrêtée" in line.lower():
                            status = "Arrêtée"
                        printers[current] = {"status": status, "location": "",
                                             "model": "", "default": False}
                elif current and "\tLocation:" in line:
                    printers[current]["location"] = line.split(":", 1)[1].strip()
                elif current and "\tDescription:" in line:
                    printers[current]["model"] = line.split(":", 1)[1].strip()
        except Exception:
            pass

        # Défaut
        try:
            r = subprocess.run(["lpstat", "-d"],
                               capture_output=True, text=True, timeout=5)
            for line in r.stdout.splitlines():
                if ":" in line:
                    dname = line.split(":", 1)[1].strip()
                    if dname in printers:
                        printers[dname]["default"] = True
        except Exception:
            pass

        # 3) Si rien, chercher via lpstat -a
        if not printers:
            try:
                r = subprocess.run(["lpstat", "-a"],
                                   capture_output=True, text=True, timeout=5)
                for line in r.stdout.splitlines():
                    parts = line.split()
                    if parts:
                        n = parts[0]
                        if n and n not in printers:
                            printers[n] = {"status": "Inconnue", "location": "",
                                           "model": "", "default": False}
            except Exception:
                pass

        # Toujours ajouter "Imprimer en PDF"
        printers["Imprimer en PDF (fichier)"] = {
            "status": "Disponible", "location": "", "model": "PDF virtuel",
            "default": False,
        }
        return printers

    def _populate_printers(self, info):
        self._printers_info = info
        names = [n for n in info if n != "Imprimer en PDF (fichier)"]
        # Mettre le défaut en premier
        default = next((n for n, v in info.items() if v.get("default")), None)
        if default and default in names:
            names.remove(default)
            names.insert(0, default)
        names.append("Imprimer en PDF (fichier)")

        self.cb_printer["values"] = names
        if names:
            chosen = default if (default and default in names) else names[0]
            self.var_printer.set(chosen)
            self._on_printer_change()
        else:
            self.var_printer.set("Aucune imprimante trouvée")
            self.lbl_printer_info.config(
                text="⚠  Aucune imprimante — vérifiez CUPS / pilotes",
                fg="#C0390B")

    def _on_printer_change(self, event=None):
        name = self.var_printer.get()
        info = self._printers_info.get(name, {})
        status   = info.get("status", "")
        location = info.get("location", "")
        model    = info.get("model", "")
        is_def   = info.get("default", False)
        parts = []
        if status:
            icon = "●" if status in ("Prête", "Disponible") else "⚠"
            col  = "#1A7F4B" if status in ("Prête", "Disponible") else "#C0390B"
            parts.append((f"{icon} {status}", col))
        if location:
            parts.append((f"  ·  {location}", "#666"))
        if model:
            parts.append((f"  ·  {model}", "#666"))
        if is_def:
            parts.append(("  [Défaut]", "#2B579A"))
        if parts:
            text = "".join(p[0] for p in parts)
            self.lbl_printer_info.config(text=text, fg=parts[0][1])
        else:
            self.lbl_printer_info.config(text="", fg="#666")

    def _open_printer_props(self):
        """Ouvre les propriétés de l'imprimante (interface CUPS web ou dialog système)."""
        try:
            subprocess.Popen(["xdg-open", "http://localhost:631"])
        except Exception:
            messagebox.showinfo("Propriétés",
                "Ouvrez http://localhost:631 dans votre navigateur\n"
                "pour gérer les imprimantes CUPS.",
                parent=self.win)

    # ─── Plage de pages ────────────────────────────────────────────────────────
    def _on_range_change(self):
        label = self.var_range_label.get()
        if label == "Plage personnalisée…":
            self.custom_range_frame.pack(fill=tk.X, pady=(0, 4),
                                         after=self.custom_range_frame.master.children.get(
                                             list(self.custom_range_frame.master.children)[-2], None
                                         ) or self.custom_range_frame)
        else:
            self.custom_range_frame.pack_forget()

    # ─── Aperçu ────────────────────────────────────────────────────────────────
    def _refresh_preview(self):
        if not self.app.pages:
            self._draw_blank_preview()
            return
        idx = max(0, min(self._preview_page_idx, len(self.app.pages) - 1))
        page = self.app.pages[idx]
        self.lbl_preview_num.config(
            text=f"Page {idx + 1} sur {len(self.app.pages)}")
        if HAS_FITZ and HAS_PIL:
            try:
                doc = fitz.open(page.path)
                fpg = doc[page.pg_idx]
                mat = fitz.Matrix(0.8, 0.8)
                pix = fpg.get_pixmap(matrix=mat, alpha=False)
                img = Image.frombytes("RGB", [pix.width, pix.height], pix.samples)
                doc.close()
                # Rotation aperçu
                orient_label = self.var_orient_label.get() if hasattr(self, "var_orient_label") else "Portrait"
                if orient_label == "Paysage":
                    img = img.rotate(90, expand=True)
                # Ajuster au canvas
                self.win.update_idletasks()
                cw = max(self.preview_canvas.winfo_width(), 200)
                ch = max(self.preview_canvas.winfo_height(), 260)
                ratio = min((cw - 40) / img.width, (ch - 40) / img.height)
                nw = int(img.width * ratio)
                nh = int(img.height * ratio)
                img = img.resize((nw, nh), Image.LANCZOS)
                self._preview_photo = ImageTk.PhotoImage(img)
                self.preview_canvas.delete("all")
                cx, cy = cw // 2, ch // 2
                # Ombre
                self.preview_canvas.create_rectangle(
                    cx - nw//2 + 4, cy - nh//2 + 4,
                    cx + nw//2 + 4, cy + nh//2 + 4,
                    fill="#444", outline="")
                # Image
                self.preview_canvas.create_image(cx, cy,
                    image=self._preview_photo, anchor="center")
                return
            except Exception:
                pass
        self._draw_blank_preview()

    def _draw_blank_preview(self):
        self.preview_canvas.delete("all")
        self.win.update_idletasks()
        cw = max(self.preview_canvas.winfo_width(), 200)
        ch = max(self.preview_canvas.winfo_height(), 260)
        orient = (self.var_orient_label.get()
                  if hasattr(self, "var_orient_label") else "Portrait")
        if orient == "Paysage":
            pw = int(min(cw, ch) * 0.80)
            ph = int(pw * 0.71)
        else:
            ph = int(min(cw, ch) * 0.80)
            pw = int(ph * 0.71)
        ox = (cw - pw) // 2
        oy = (ch - ph) // 2
        self.preview_canvas.create_rectangle(
            ox+4, oy+4, ox+pw+4, oy+ph+4, fill="#555", outline="")
        self.preview_canvas.create_rectangle(
            ox, oy, ox+pw, oy+ph, fill="white", outline="#333", width=1)
        for i in range(7):
            lw = int(pw * (0.3 + 0.5 * ((i * 53 + 11) % 17) / 17))
            ly = oy + 24 + i * int(ph / 9)
            self.preview_canvas.create_line(
                ox+14, ly, ox+14+lw, ly, fill="#DDDDDD", width=3)

    def _prev_preview(self):
        if self._preview_page_idx > 0:
            self._preview_page_idx -= 1
            self._refresh_preview()

    def _next_preview(self):
        if self._preview_page_idx < len(self.app.pages) - 1:
            self._preview_page_idx += 1
            self._refresh_preview()

    # ─── Impression ────────────────────────────────────────────────────────────
    def _cancel(self):
        if self._tmp_pdf and os.path.exists(self._tmp_pdf):
            try:
                os.unlink(self._tmp_pdf)
            except Exception:
                pass
        self.win.destroy()

    def _do_print(self):
        printer = self.var_printer.get()
        if not printer or "Recherche" in printer:
            messagebox.showwarning("Imprimante",
                "Sélectionnez une imprimante valide.", parent=self.win)
            return

        self.btn_print.config(state="disabled", text="En cours…")
        self.lbl_status.config(text="⏳  Génération du document…", fg="#555")
        self.win.update()

        # Générer PDF temporaire
        try:
            tmp = tempfile.NamedTemporaryFile(suffix=".pdf", delete=False)
            tmp.close()
            self._tmp_pdf = tmp.name
            out_doc = fitz.open()
            src_docs = {}
            pages_idx = self._get_pages_to_print()
            for idx in pages_idx:
                pg = self.app.pages[idx]
                if pg.path not in src_docs:
                    src_docs[pg.path] = fitz.open(pg.path)
                src = src_docs[pg.path]
                out_doc.insert_pdf(src, from_page=pg.pg_idx, to_page=pg.pg_idx)
                new_pg = out_doc[-1]
                self.app._apply_edits(new_pg, pg.edits)
                if pg.rotation:
                    new_pg.set_rotation(pg.rotation)
            out_doc.save(self._tmp_pdf, garbage=4, deflate=True)
            out_doc.close()
            for d in src_docs.values():
                d.close()
        except Exception as e:
            messagebox.showerror("Erreur",
                f"Impossible de générer le PDF :\n{e}", parent=self.win)
            self.btn_print.config(state="normal", text="Imprimer")
            self.lbl_status.config(text="")
            return

        # Impression vers PDF virtuel → Enregistrer sous
        if printer == "Imprimer en PDF (fichier)":
            dest = filedialog.asksaveasfilename(
                title="Enregistrer en PDF", defaultextension=".pdf",
                filetypes=[("PDF", "*.pdf")], parent=self.win)
            if dest:
                import shutil
                shutil.copy2(self._tmp_pdf, dest)
                messagebox.showinfo("PDF enregistré",
                    f"Fichier enregistré :\n{dest}", parent=self.win)
                self._cancel()
            else:
                self.btn_print.config(state="normal", text="Imprimer")
                self.lbl_status.config(text="")
            return

        # Construire la commande lp
        copies = max(1, self.var_copies.get())
        paper_key = self.PAPER_SIZES.get(self.var_paper.get(),
                                         ("A4", 210, 297))
        paper_id = paper_key[0] if isinstance(paper_key, tuple) else "A4"
        sides_key = self.SIDES.get(self.var_sides_label.get(), "one-sided")
        orient_val = ("3" if self.var_orient_label.get() == "Portrait" else "4")
        quality_val = self.QUALITY_MAP.get(self.var_quality.get(), "4")
        collate = "True" if "Assemblé" in self.var_collate_label.get() else "False"
        color_val = self.var_color_mode.get()

        cmd = ["lp", "-d", printer, "-n", str(copies),
               "-o", f"media={paper_id}",
               "-o", f"sides={sides_key}",
               "-o", f"orientation-requested={orient_val}",
               "-o", f"print-quality={quality_val}",
               "-o", f"Collate={collate}",
        ]
        if color_val in ("Niveaux de gris", "Noir pur"):
            cmd += ["-o", "ColorModel=Gray"]

        scale = self.var_scale.get()
        if scale == "Ajuster à la page":
            cmd += ["-o", "fit-to-page"]
        elif scale.endswith("%"):
            try:
                pct = int(scale.replace("%", "").strip())
                cmd += ["-o", f"scaling={pct}"]
            except ValueError:
                pass

        cmd.append(self._tmp_pdf)

        self.lbl_status.config(text=f"⏳  Envoi vers {printer}…", fg="#555")
        self.win.update()

        try:
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
            if result.returncode == 0:
                job_id = result.stdout.strip()
                messagebox.showinfo(
                    "Impression envoyée",
                    f"Document envoyé avec succès !\n\n"
                    f"Imprimante : {printer}\n"
                    f"Pages imprimées : {len(pages_idx)}\n"
                    f"Copies : {copies}\n"
                    f"Format : {self.var_paper.get()}\n\n"
                    f"{job_id}",
                    parent=self.win)
                self._cancel()
            else:
                err = (result.stderr.strip() or result.stdout.strip() or
                       "Erreur inconnue")
                messagebox.showerror("Erreur d'impression",
                    f"La commande lp a échoué :\n\n{err}\n\n"
                    f"Commande : {' '.join(cmd[:5])} …",
                    parent=self.win)
                self.btn_print.config(state="normal", text="Imprimer")
                self.lbl_status.config(text="⚠  Erreur — vérifiez l'imprimante",
                                       fg="#C0390B")
        except FileNotFoundError:
            messagebox.showerror(
                "CUPS introuvable",
                "La commande 'lp' n'est pas installée.\n\n"
                "Installez CUPS :\n  sudo apt install cups\n"
                "ou utilisez 'Imprimer en PDF (fichier)'.",
                parent=self.win)
            self.btn_print.config(state="normal", text="Imprimer")
        except subprocess.TimeoutExpired:
            messagebox.showerror("Timeout",
                "L'envoi à l'imprimante a pris trop de temps.",
                parent=self.win)
            self.btn_print.config(state="normal", text="Imprimer")

    def _get_pages_to_print(self):
        label = self.var_range_label.get()
        mode = self.RANGE_LABELS.get(label, "all")
        n = len(self.app.pages)
        if mode == "all":
            return list(range(n))
        elif mode == "current":
            sel = self.app._selected
            return [sel] if sel is not None and 0 <= sel < n else list(range(n))
        elif mode == "even":
            return [i for i in range(n) if (i + 1) % 2 == 0]
        elif mode == "odd":
            return [i for i in range(n) if (i + 1) % 2 == 1]
        elif mode == "custom":
            return self._parse_custom_range(self.var_custom_pages.get(), n)
        return list(range(n))

    def _parse_custom_range(self, expr, n):
        """Parse '1,3,5-8,10' → [0,2,4,5,6,7,9]"""
        pages = set()
        for part in expr.split(","):
            part = part.strip()
            if "-" in part:
                a, _, b = part.partition("-")
                try:
                    for i in range(int(a.strip()), int(b.strip()) + 1):
                        if 1 <= i <= n:
                            pages.add(i - 1)
                except ValueError:
                    pass
            else:
                try:
                    i = int(part)
                    if 1 <= i <= n:
                        pages.add(i - 1)
                except ValueError:
                    pass
        return sorted(pages) if pages else list(range(n))


# ─── Main ─────────────────────────────────────────────────────────────────────
if __name__ == "__main__":
    root = tk.Tk()
    PDFMergerPro(root)
    root.mainloop()