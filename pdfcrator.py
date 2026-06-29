"""
PDF Merger Pro V2.2 — Safran Engineering Services
Nouvelles fonctionnalités :
  • Édition de texte en TEMPS RÉEL (l'overlay se met à jour pendant la frappe)
  • Texte ajouté DÉPLAÇABLE et REDIMENSIONNABLE après création
  • Sélection CARACTÈRE PAR CARACTÈRE par glisser-souris (comme Word)
  • Tout le reste de la V2.1 conservé

pip install PyPDF2 PyMuPDF Pillow
"""

import tkinter as tk
from tkinter import filedialog, messagebox, ttk, colorchooser
from pathlib import Path
import threading
import copy
import io
import subprocess
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

FONT_MAP = {
    "helvetica":   "helv", "arial":     "helv", "arialmt":   "helv",
    "times":       "tiro", "timesnew":  "tiro", "timesroman":"tiro",
    "courier":     "cour", "couriernew":"cour", "consolas":  "cour",
}


def map_font(font_name: str, is_bold: bool, is_italic: bool):
    if not font_name:
        return "helv", False
    fn = font_name.lower().replace("-", "").replace(" ", "")
    base = "helv"
    matched = False
    for key, val in FONT_MAP.items():
        if key in fn:
            base = val
            matched = True
            break
    if not is_bold and ("bold" in fn or "black" in fn or "heavy" in fn):
        is_bold = True
    if not is_italic and ("italic" in fn or "oblique" in fn):
        is_italic = True
    full_map = {
        ("helv", False, False): "helv", ("helv", True,  False): "hebo",
        ("helv", False, True ): "heit", ("helv", True,  True ): "hebi",
        ("tiro", False, False): "tiro", ("tiro", True,  False): "tibo",
        ("tiro", False, True ): "tiit", ("tiro", True,  True ): "tibi",
        ("cour", False, False): "cour", ("cour", True,  False): "cobo",
        ("cour", False, True ): "coit", ("cour", True,  True ): "cobi",
    }
    return full_map.get((base, is_bold, is_italic), base), matched


class Edit:
    """Une opération d'édition appliquée à une page.
    Pour les édits 'add', un id unique permet de les identifier (déplaçables).
    """
    __slots__ = ("kind", "bbox", "text", "font", "size", "color", "bg", "uid")

    def __init__(self, kind, bbox=None, text="", font="helv",
                 size=11, color=(0, 0, 0), bg=(1, 1, 1), uid=None):
        self.kind = kind
        self.bbox = bbox
        self.text = text
        self.font = font
        self.size = size
        self.color = color
        self.bg = bg
        self.uid = uid


class Page:
    __slots__ = ("path", "fname", "pg_idx", "photo", "rotation", "edits")

    def __init__(self, path, fname, pg_idx):
        self.path     = path
        self.fname    = fname
        self.pg_idx   = pg_idx
        self.photo    = None
        self.rotation = 0
        self.edits    = []


# ══════════════════════════════════════════════════════════════════════════════
#  MAIN APP
# ══════════════════════════════════════════════════════════════════════════════
class PDFMergerPro:
    def __init__(self, root):
        self.root = root
        self.root.title("PDF Merger Pro V2.2 — Safran Engineering Services")
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

        self.root.bind_all("<Control-z>", lambda e: self.undo())
        self.root.bind_all("<Control-Z>", lambda e: self.undo())
        self.root.bind_all("<Control-y>", lambda e: self.redo())
        self.root.bind_all("<Control-Y>", lambda e: self.redo())
        self.root.bind_all("<Control-Shift-Z>", lambda e: self.redo())
        self.root.bind_all("<Delete>", lambda e: self.delete_selected())

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
        if not (HAS_PIL and page.pg_idx < len(raw)):
            return None
        base_img = raw[page.pg_idx]
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

    def on_editor_save(self, pos, rotation, edits):
        page = self.pages[pos]
        page.rotation = rotation
        page.edits    = edits
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
        for ed in edits:
            if ed.kind in ("delete", "replace"):
                if ed.bbox:
                    rect = fitz.Rect(*ed.bbox)
                    # Extend whiteout rect to cover potential overflow
                    page_rect = fitz_page.rect
                    extended = fitz.Rect(
                        max(page_rect.x0, rect.x0 - 2),
                        max(page_rect.y0, rect.y0 - 2),
                        min(page_rect.x1, rect.x1 + 2),
                        min(page_rect.y1, rect.y1 + 2),
                    )
                    fitz_page.draw_rect(extended, color=ed.bg, fill=ed.bg, width=0)
            if ed.kind in ("add", "replace"):
                if ed.bbox and ed.text:
                    rect = fitz.Rect(*ed.bbox)
                    # Ensure rect is tall enough for the font (at least 1.5× font size)
                    min_h = ed.size * 1.5
                    if rect.height < min_h:
                        rect = fitz.Rect(rect.x0, rect.y0, rect.x1, rect.y0 + min_h)
                    try:
                        rc = fitz_page.insert_textbox(
                            rect, ed.text, fontname=ed.font, fontsize=ed.size,
                            color=ed.color, align=0)
                        # rc < 0 means text didn't fit — fall back to insert_text
                        if rc < 0:
                            raise ValueError("text overflow")
                    except Exception:
                        # insert_text never clips: baseline at y0 + size
                        fitz_page.insert_text(
                            (rect.x0, rect.y0 + ed.size), ed.text,
                            fontname=ed.font, fontsize=ed.size, color=ed.color)


# ══════════════════════════════════════════════════════════════════════════════
#  PAGE EDITOR  —  V2.2
# ══════════════════════════════════════════════════════════════════════════════
class PageEditor:
    """Éditeur avancé : sélection caractère par caractère, édition temps réel,
    déplacement/redimensionnement des textes ajoutés."""

    RENDER_DPI = 1.8
    HANDLE_SIZE = 8  # taille des poignées en pixels

    def __init__(self, app, pos):
        self.app  = app
        self.pos  = pos
        self.page = app.pages[pos]
        self.rotation = self.page.rotation
        self.edits    = copy.deepcopy(self.page.edits)
        self._next_uid = max([(e.uid or 0) for e in self.edits], default=0) + 1

        self._hist     = []
        self._hist_idx = -1
        self._max_hist = 30

        # Caractères individuels (pour sélection Word-like)
        self._chars = []  # list of dict {bbox, text, font, size, color, flags, line_idx}
        self._lines = []  # group chars by visual line: list of (y_center, [char_idx, ...])

        # Sélection caractères : (start_idx, end_idx) inclusif, ordonné
        self._char_sel = None

        # Drag de sélection
        self._sel_dragging = False
        self._sel_anchor = None  # index du char où on a commencé le drag

        # Édit (add) sélectionné pour déplacement
        self._added_sel_uid = None
        self._added_drag_mode = None  # "move" | "resize-XY" (XY: nw, ne, sw, se, n, s, e, w)
        self._added_drag_start = None  # (mouse_pdf_x, mouse_pdf_y, original_bbox)

        # Mode courant
        self._mode = "select"  # "select" | "add"
        self._draw_start = None

        # Édition temps réel : on garde le bbox du span en cours d'édition
        self._editing_bbox = None  # tuple (x0,y0,x1,y1) du dernier span/sélection éditée

        # Throttle pour temps réel
        self._realtime_after = None

        self._open_doc()
        self._build_window()
        self._render_page()
        self._snap()

    def _open_doc(self):
        self._doc  = fitz.open(self.page.path)
        self._fpg  = self._doc[self.page.pg_idx]

    # ── UI ──
    def _build_window(self):
        self.win = tk.Toplevel(self.app.root)
        self.win.title(f"Éditeur — {self.page.fname}  ·  page {self.page.pg_idx + 1}")
        self.win.geometry("1320x820")
        self.win.minsize(900, 600)
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

        # Toolbar
        tb = tk.Frame(self.win, bg=C["bg2"], height=40)
        tb.pack(fill=tk.X)
        tb.pack_propagate(False)

        def tbtn(parent, text, cmd, bold=False, accent=False, color=None):
            return tk.Button(parent, text=text, command=cmd,
                             font=("Helvetica", 8, "bold" if bold else "normal"),
                             bg=color or (C["blue"] if accent else C["white"]),
                             fg=C["white"] if (accent or color) else C["text"],
                             relief="flat", bd=0, activebackground=C["blue_lt"],
                             cursor="hand2", padx=10, pady=4, highlightthickness=1,
                             highlightbackground=C["line"])

        self.btn_select = tbtn(tb, "🖱  Sélection", lambda: self._set_mode("select"), bold=True)
        self.btn_select.pack(side=tk.LEFT, padx=3, pady=6)
        self.btn_add = tbtn(tb, "➕  Ajouter texte", lambda: self._set_mode("add"))
        self.btn_add.pack(side=tk.LEFT, padx=3, pady=6)
        tk.Frame(tb, bg=C["line"], width=1).pack(side=tk.LEFT, fill=tk.Y, pady=8, padx=4)
        tbtn(tb, "⟲ 90°", lambda: self._rotate(-90)).pack(side=tk.LEFT, padx=3, pady=6)
        tbtn(tb, "⟳ 90°", lambda: self._rotate(90)).pack(side=tk.LEFT, padx=3, pady=6)
        tbtn(tb, "⟳ 180°", lambda: self._rotate(180)).pack(side=tk.LEFT, padx=3, pady=6)
        tk.Frame(tb, bg=C["line"], width=1).pack(side=tk.LEFT, fill=tk.Y, pady=8, padx=4)
        self.btn_eundo = tbtn(tb, "↶  Annuler", self._undo)
        self.btn_eundo.pack(side=tk.LEFT, padx=3, pady=6)
        self.btn_eredo = tbtn(tb, "↷  Rétablir", self._redo)
        self.btn_eredo.pack(side=tk.LEFT, padx=3, pady=6)
        tk.Frame(tb, bg=C["line"], width=1).pack(side=tk.LEFT, fill=tk.Y, pady=8, padx=4)
        tbtn(tb, "🗑  Supprimer sél.", self._delete_selected, color=C["warn"]
             ).pack(side=tk.LEFT, padx=3, pady=6)

        self.lbl_mode = tk.Label(tb, text="Mode : Sélection",
                                 font=("Helvetica", 8, "bold"),
                                 bg=C["bg2"], fg=C["blue"])
        self.lbl_mode.pack(side=tk.RIGHT, padx=14)

        # Body
        body = tk.Frame(self.win, bg=C["bg"])
        body.pack(fill=tk.BOTH, expand=True)
        self._build_side_panel(body)

        cwrap = tk.Frame(body, bg=C["bg"])
        cwrap.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        vsb = tk.Scrollbar(cwrap, orient=tk.VERTICAL)
        vsb.pack(side=tk.RIGHT, fill=tk.Y)
        hsb = tk.Scrollbar(cwrap, orient=tk.HORIZONTAL)
        hsb.pack(side=tk.BOTTOM, fill=tk.X)
        self.canvas = tk.Canvas(cwrap, bg="#888", yscrollcommand=vsb.set,
                                xscrollcommand=hsb.set, highlightthickness=0)
        self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        vsb.config(command=self.canvas.yview)
        hsb.config(command=self.canvas.xview)

        self.canvas.bind("<Motion>",          self._on_motion)
        self.canvas.bind("<ButtonPress-1>",   self._on_press)
        self.canvas.bind("<B1-Motion>",       self._on_drag)
        self.canvas.bind("<ButtonRelease-1>", self._on_release)

        # Footer
        ft = tk.Frame(self.win, bg=C["navy2"], height=24)
        ft.pack(fill=tk.X, side=tk.BOTTOM)
        ft.pack_propagate(False)
        self._st_var = tk.StringVar(
            value="Glissez pour sélectionner du texte (lettre par lettre)  ·  Ctrl+Z / Ctrl+Y")
        tk.Label(ft, textvariable=self._st_var, font=("Helvetica", 8),
                 fg="#A8CCE8", bg=C["navy2"], padx=14).pack(side=tk.LEFT, pady=3)

        self.win.bind("<Control-z>", lambda e: self._undo())
        self.win.bind("<Control-Z>", lambda e: self._undo())
        self.win.bind("<Control-y>", lambda e: self._redo())
        self.win.bind("<Control-Y>", lambda e: self._redo())
        self.win.bind("<Escape>",    lambda e: self._set_mode("select"))
        self.win.bind("<Delete>",    lambda e: self._delete_selected())

    def _build_side_panel(self, parent):
        side = tk.Frame(parent, bg=C["white"], width=320,
                        highlightthickness=1, highlightbackground=C["line"])
        side.pack(side=tk.RIGHT, fill=tk.Y)
        side.pack_propagate(False)
        tk.Label(side, text="PROPRIÉTÉS DU TEXTE", font=("Helvetica", 9, "bold"),
                 bg=C["navy"], fg=C["white"], pady=8).pack(fill=tk.X)
        inner = tk.Frame(side, bg=C["white"])
        inner.pack(fill=tk.BOTH, expand=True, padx=14, pady=12)

        self.lbl_sel = tk.Label(inner,
            text="Aucun texte sélectionné\n\nGlissez la souris\nsur du texte\npour sélectionner\nlettre par lettre",
            font=("Helvetica", 9), bg=C["bg2"], fg=C["mid"],
            justify=tk.CENTER, pady=20)
        self.lbl_sel.pack(fill=tk.X, pady=(0, 12))

        tk.Label(inner, text="Texte :", font=("Helvetica", 8, "bold"),
                 bg=C["white"], fg=C["text"], anchor="w").pack(fill=tk.X)
        self.txt_widget = tk.Text(inner, height=5, font=("Helvetica", 9),
                                  bg=C["bg"], fg=C["text"],
                                  highlightthickness=1, highlightbackground=C["line"],
                                  wrap=tk.WORD)
        self.txt_widget.pack(fill=tk.X, pady=(2, 4))

        # ⚡ TEMPS RÉEL : binding sur la frappe
        self.txt_widget.bind("<KeyRelease>", self._on_text_change)

        tk.Label(inner, text="⚡  Aperçu en temps réel pendant la frappe",
                 font=("Helvetica", 7, "italic"),
                 bg=C["white"], fg=C["ok"], anchor="w").pack(fill=tk.X, pady=(0, 8))

        tk.Label(inner, text="Police :", font=("Helvetica", 8, "bold"),
                 bg=C["white"], fg=C["text"], anchor="w").pack(fill=tk.X)
        self.var_font = tk.StringVar(value="Helvetica")
        self.cb_font = ttk.Combobox(inner, textvariable=self.var_font,
                                    values=["Helvetica", "Helvetica Bold",
                                            "Helvetica Italic", "Helvetica Bold Italic",
                                            "Times", "Times Bold", "Times Italic",
                                            "Times Bold Italic",
                                            "Courier", "Courier Bold", "Courier Italic"],
                                    state="readonly", font=("Helvetica", 9))
        self.cb_font.pack(fill=tk.X, pady=(2, 4))
        self.cb_font.bind("<<ComboboxSelected>>", self._on_text_change)

        self.lbl_font_orig = tk.Label(inner, text="", font=("Helvetica", 7, "italic"),
                                      bg=C["white"], fg=C["mid"], anchor="w")
        self.lbl_font_orig.pack(fill=tk.X, pady=(0, 8))

        rowf = tk.Frame(inner, bg=C["white"])
        rowf.pack(fill=tk.X, pady=(0, 10))
        tk.Label(rowf, text="Taille :", font=("Helvetica", 8, "bold"),
                 bg=C["white"], fg=C["text"]).pack(side=tk.LEFT)
        self.var_size = tk.DoubleVar(value=11)
        sp = tk.Spinbox(rowf, from_=4, to=72, increment=0.5,
                        textvariable=self.var_size, width=8,
                        font=("Helvetica", 9), command=self._on_text_change)
        sp.pack(side=tk.LEFT, padx=8)
        sp.bind("<KeyRelease>", self._on_text_change)

        # Palette de couleurs rapide (swatches cliquables)
        PALETTE = [
            "#000000", "#434343", "#666666", "#999999", "#CCCCCC", "#FFFFFF",
            "#FF0000", "#FF4500", "#FF8C00", "#FFD700", "#ADFF2F", "#008000",
            "#00CED1", "#1E90FF", "#0000CD", "#8A2BE2", "#FF69B4", "#8B4513",
        ]

        rowc = tk.Frame(inner, bg=C["white"])
        rowc.pack(fill=tk.X, pady=(0, 4))
        tk.Label(rowc, text="Couleur texte :", font=("Helvetica", 8, "bold"),
                 bg=C["white"], fg=C["text"]).pack(side=tk.LEFT)
        self.color_text = (0, 0, 0)
        self.swatch_text = tk.Frame(rowc, width=24, height=20, bg="#000000",
                                    highlightthickness=1, highlightbackground=C["line"])
        self.swatch_text.pack(side=tk.LEFT, padx=8)
        tk.Button(rowc, text="…", command=lambda: self._pick_color("text"),
                  font=("Helvetica", 8), bg=C["white"], relief="flat",
                  highlightthickness=1, highlightbackground=C["line"],
                  cursor="hand2", padx=6).pack(side=tk.LEFT)

        # Palette rapide couleur texte
        pal_text = tk.Frame(inner, bg=C["white"])
        pal_text.pack(fill=tk.X, pady=(0, 10))
        for i, hex_col in enumerate(PALETTE):
            r = int(hex_col[1:3], 16) / 255
            g = int(hex_col[3:5], 16) / 255
            b = int(hex_col[5:7], 16) / 255
            btn = tk.Frame(pal_text, width=16, height=16, bg=hex_col,
                           highlightthickness=1, highlightbackground="#888",
                           cursor="hand2")
            btn.grid(row=i // 9, column=i % 9, padx=1, pady=1)
            btn.bind("<Button-1>",
                lambda e, n=(r, g, b), h=hex_col: self._apply_color("text", n, h))

        rowb = tk.Frame(inner, bg=C["white"])
        rowb.pack(fill=tk.X, pady=(0, 4))
        tk.Label(rowb, text="Couleur de fond :", font=("Helvetica", 8, "bold"),
                 bg=C["white"], fg=C["text"]).pack(side=tk.LEFT)
        self.color_bg = (1, 1, 1)
        self.swatch_bg = tk.Frame(rowb, width=24, height=20, bg="#FFFFFF",
                                  highlightthickness=1, highlightbackground=C["line"])
        self.swatch_bg.pack(side=tk.LEFT, padx=8)
        tk.Button(rowb, text="…", command=lambda: self._pick_color("bg"),
                  font=("Helvetica", 8), bg=C["white"], relief="flat",
                  highlightthickness=1, highlightbackground=C["line"],
                  cursor="hand2", padx=6).pack(side=tk.LEFT)

        # Palette rapide couleur fond
        pal_bg = tk.Frame(inner, bg=C["white"])
        pal_bg.pack(fill=tk.X, pady=(0, 6))
        for i, hex_col in enumerate(PALETTE):
            r = int(hex_col[1:3], 16) / 255
            g = int(hex_col[3:5], 16) / 255
            b = int(hex_col[5:7], 16) / 255
            btn = tk.Frame(pal_bg, width=16, height=16, bg=hex_col,
                           highlightthickness=1, highlightbackground="#888",
                           cursor="hand2")
            btn.grid(row=i // 9, column=i % 9, padx=1, pady=1)
            btn.bind("<Button-1>",
                lambda e, n=(r, g, b), h=hex_col: self._apply_color("bg", n, h))

        tk.Label(inner, text="(efface le texte d'origine)",
                 font=("Helvetica", 7, "italic"),
                 bg=C["white"], fg=C["mid"], anchor="w").pack(fill=tk.X)

        sep = tk.Frame(inner, bg=C["line"], height=1)
        sep.pack(fill=tk.X, pady=14)

        self.btn_apply = tk.Button(inner, text="✔  Valider la modification",
                                    command=self._commit_text_edit,
                                    font=("Helvetica", 9, "bold"),
                                    bg=C["ok"], fg=C["white"], relief="flat",
                                    activebackground="#0F6238",
                                    cursor="hand2", pady=8)
        self.btn_apply.pack(fill=tk.X, pady=(0, 6))

        self.btn_revert = tk.Button(inner, text="↺  Réinitialiser ce texte",
                                     command=self._revert_selection,
                                     font=("Helvetica", 8),
                                     bg=C["white"], fg=C["text"], relief="flat",
                                     highlightthickness=1, highlightbackground=C["line"],
                                     cursor="hand2", pady=6)
        self.btn_revert.pack(fill=tk.X)

        sep2 = tk.Frame(inner, bg=C["line"], height=1)
        sep2.pack(fill=tk.X, pady=14)

        self.lbl_stats = tk.Label(inner, text="", font=("Helvetica", 8),
                                   bg=C["white"], fg=C["mid"],
                                   justify=tk.LEFT, anchor="w")
        self.lbl_stats.pack(fill=tk.X)
        self._enable_controls(False)

    def _enable_controls(self, enabled):
        state = "normal" if enabled else "disabled"
        self.txt_widget.config(state=state)
        self.cb_font.config(state="readonly" if enabled else "disabled")
        self.btn_apply.config(state=state)
        self.btn_revert.config(state=state)

    def _apply_color(self, which, normalized, hexv):
        """Applique une couleur choisie (depuis palette ou chooser) immédiatement."""
        if which == "text":
            self.color_text = normalized
            self.swatch_text.config(bg=hexv)
        else:
            self.color_bg = normalized
            self.swatch_bg.config(bg=hexv)
        # Apply immediately without throttle
        if self._realtime_after:
            self.win.after_cancel(self._realtime_after)
            self._realtime_after = None
        self._do_realtime_update()

    def _pick_color(self, which):
        cur = self.color_text if which == "text" else self.color_bg
        hex_cur = "#{:02x}{:02x}{:02x}".format(
            int(cur[0]*255), int(cur[1]*255), int(cur[2]*255))
        rgb, hexv = colorchooser.askcolor(color=hex_cur, parent=self.win)
        if rgb:
            normalized = (rgb[0]/255, rgb[1]/255, rgb[2]/255)
            self._apply_color(which, normalized, hexv)

    def _set_mode(self, mode):
        self._mode = mode
        labels = {"select": "Sélection", "add": "Ajout de texte"}
        self.lbl_mode.config(text=f"Mode : {labels.get(mode, mode)}")
        self.btn_select.config(bg=C["blue"] if mode == "select" else C["white"],
                               fg=C["white"] if mode == "select" else C["text"])
        self.btn_add.config(bg=C["blue"] if mode == "add" else C["white"],
                            fg=C["white"] if mode == "add" else C["text"])
        if mode == "add":
            self.canvas.config(cursor="crosshair")
            self._st_var.set("Tracez un rectangle où ajouter le texte")
        else:
            self.canvas.config(cursor="arrow")
            self._st_var.set("Glissez la souris pour sélectionner du texte")

    # ── RENDER ──
    def _render_page(self):
        original_rotation = self._fpg.rotation
        self._fpg.set_rotation(self.rotation)
        mat = fitz.Matrix(self.RENDER_DPI, self.RENDER_DPI)
        pix = self._fpg.get_pixmap(matrix=mat, alpha=False)
        img_data = pix.tobytes("ppm")
        img = Image.open(io.BytesIO(img_data))
        self._photo = ImageTk.PhotoImage(img)
        self._scale = self.RENDER_DPI
        self.canvas.delete("all")
        self._img_id = self.canvas.create_image(0, 0, image=self._photo, anchor="nw")
        self.canvas.config(scrollregion=(0, 0, img.width, img.height))

        # Extraction CARACTÈRES (rawdict) pour sélection lettre par lettre
        self._chars = []
        d = self._fpg.get_text("rawdict")
        for block in d.get("blocks", []):
            if block.get("type", 0) != 0:
                continue
            for line in block.get("lines", []):
                for span in line.get("spans", []):
                    font = span.get("font", "")
                    size = span.get("size", 11)
                    color = self._int_to_rgb(span.get("color", 0))
                    flags = span.get("flags", 0)
                    for ch in span.get("chars", []):
                        c_text = ch.get("c", "")
                        bbox = ch.get("bbox")
                        if not c_text or not bbox:
                            continue
                        self._chars.append({
                            "bbox":  bbox,
                            "text":  c_text,
                            "font":  font,
                            "size":  size,
                            "color": color,
                            "flags": flags,
                        })

        # Grouper en lignes pour faciliter la sélection
        self._build_lines()
        self._fpg.set_rotation(original_rotation)
        self._redraw_overlays()
        self._update_stats()

    def _build_lines(self):
        """Groupe les caractères par ligne visuelle (même y_center à tolérance)."""
        self._lines = []
        if not self._chars:
            return
        # Tri par y puis x
        sorted_idx = sorted(range(len(self._chars)),
                            key=lambda i: (self._chars[i]["bbox"][1],
                                           self._chars[i]["bbox"][0]))
        current_line = []
        current_y = None
        TOLERANCE = 3.0  # pts PDF
        for i in sorted_idx:
            ch = self._chars[i]
            y_center = (ch["bbox"][1] + ch["bbox"][3]) / 2
            if current_y is None or abs(y_center - current_y) <= TOLERANCE:
                current_line.append(i)
                current_y = y_center if current_y is None else current_y
            else:
                # Trier la ligne par x
                current_line.sort(key=lambda i: self._chars[i]["bbox"][0])
                self._lines.append((current_y, current_line))
                current_line = [i]
                current_y = y_center
        if current_line:
            current_line.sort(key=lambda i: self._chars[i]["bbox"][0])
            self._lines.append((current_y, current_line))

    def _redraw_overlays(self):
        """Redessine tous les overlays (édits, sélection, poignées)."""
        for tag in ("edit_overlay", "selection", "char_sel", "draw_temp",
                    "added_box", "handle"):
            self.canvas.delete(tag)

        # Édits
        for ed in self.edits:
            if not ed.bbox:
                continue
            x0, y0, x1, y1 = [v * self._scale for v in ed.bbox]

            # Whiteout pour delete et replace
            if ed.kind in ("delete", "replace"):
                bg_hex = "#{:02x}{:02x}{:02x}".format(
                    int(ed.bg[0]*255), int(ed.bg[1]*255), int(ed.bg[2]*255))
                self.canvas.create_rectangle(x0, y0, x1, y1,
                    fill=bg_hex, outline="", tags="edit_overlay")

            # Texte (replace ou add)
            if ed.kind in ("add", "replace") and ed.text:
                fg_hex = "#{:02x}{:02x}{:02x}".format(
                    int(ed.color[0]*255), int(ed.color[1]*255), int(ed.color[2]*255))
                fsize = max(6, int(ed.size * self._scale * 0.75))
                self.canvas.create_text(x0 + 2, y0 + 2,
                    text=ed.text, anchor="nw", fill=fg_hex,
                    font=("Helvetica", fsize), width=(x1 - x0),
                    tags="edit_overlay")

            # Cadre orange (replace) ou bleu (add)
            outline_color = C["selected"] if ed.kind == "add" else C["orange"]
            self.canvas.create_rectangle(x0, y0, x1, y1,
                outline=outline_color, width=2, dash=(4, 2),
                tags=("edit_overlay", f"added_{ed.uid}" if ed.uid else "edit_overlay"))

            # Poignées si "add" sélectionné
            if ed.kind == "add" and ed.uid == self._added_sel_uid:
                self._draw_handles(x0, y0, x1, y1)

        # Sélection caractères (style Word)
        if self._char_sel:
            start, end = self._char_sel
            for line_y, line_chars in self._lines:
                # Trouver les chars de cette ligne dans la sélection
                in_sel = [i for i in line_chars if start <= i <= end]
                if not in_sel:
                    continue
                # Bbox englobant de la sélection sur cette ligne
                xs0 = min(self._chars[i]["bbox"][0] for i in in_sel)
                xs1 = max(self._chars[i]["bbox"][2] for i in in_sel)
                ys0 = min(self._chars[i]["bbox"][1] for i in in_sel)
                ys1 = max(self._chars[i]["bbox"][3] for i in in_sel)
                self.canvas.create_rectangle(
                    xs0 * self._scale, ys0 * self._scale,
                    xs1 * self._scale, ys1 * self._scale,
                    fill=C["char_sel_bg"], stipple="gray50",
                    outline=C["char_sel"], width=1, tags="char_sel")

    def _draw_handles(self, x0, y0, x1, y1):
        """Dessine 8 poignées de redimensionnement autour d'un rect."""
        s = self.HANDLE_SIZE
        positions = [
            ("nw", x0, y0), ("n", (x0+x1)/2, y0), ("ne", x1, y0),
            ("w",  x0, (y0+y1)/2),                ("e", x1, (y0+y1)/2),
            ("sw", x0, y1), ("s", (x0+x1)/2, y1), ("se", x1, y1),
        ]
        for name, hx, hy in positions:
            self.canvas.create_rectangle(
                hx - s/2, hy - s/2, hx + s/2, hy + s/2,
                fill=C["handle"], outline=C["white"], width=1,
                tags=("handle", f"handle_{name}"))

    def _int_to_rgb(self, color_int):
        r = ((color_int >> 16) & 0xFF) / 255.0
        g = ((color_int >> 8) & 0xFF) / 255.0
        b = (color_int & 0xFF) / 255.0
        return (r, g, b)

    # ── Coords ──
    def _canvas_to_pdf(self, cx, cy):
        cx = self.canvas.canvasx(cx)
        cy = self.canvas.canvasy(cy)
        return cx / self._scale, cy / self._scale

    # ── Char hit-testing ──
    def _find_char_at(self, px, py):
        """Trouve le char le plus proche de (px, py). On accepte un peu de
        tolérance verticale pour faciliter la sélection (Word-like)."""
        # 1) Trouver la ligne la plus proche
        if not self._lines:
            return None
        best_line = None
        best_dy = float("inf")
        for y_center, line_chars in self._lines:
            ymin = min(self._chars[i]["bbox"][1] for i in line_chars)
            ymax = max(self._chars[i]["bbox"][3] for i in line_chars)
            if ymin <= py <= ymax:
                return self._char_in_line(line_chars, px)
            # Sinon, distance au centre
            dy = min(abs(py - ymin), abs(py - ymax))
            if dy < best_dy:
                best_dy = dy
                best_line = line_chars
        # Si pas de hit direct mais ligne proche (< 8pt), accepter
        if best_line and best_dy < 8:
            return self._char_in_line(best_line, px)
        return None

    def _char_in_line(self, line_chars, px):
        """Dans une ligne, trouve le char dont le centre est le plus proche de px."""
        if not line_chars:
            return None
        # Si px avant le premier char → premier char
        first_x0 = self._chars[line_chars[0]]["bbox"][0]
        if px < first_x0:
            return line_chars[0]
        # Si après le dernier → dernier
        last_x1 = self._chars[line_chars[-1]]["bbox"][2]
        if px > last_x1:
            return line_chars[-1]
        # Sinon char qui contient px, ou le plus proche
        for i in line_chars:
            x0, _, x1, _ = self._chars[i]["bbox"]
            if x0 <= px <= x1:
                return i
        # Fallback
        return min(line_chars,
                   key=lambda i: abs((self._chars[i]["bbox"][0] +
                                      self._chars[i]["bbox"][2]) / 2 - px))

    # ── Hit-test edits "add" ──
    def _find_added_at(self, px, py):
        """Renvoie l'Edit 'add' sous (px,py), ou None."""
        for ed in self.edits:
            if ed.kind == "add" and ed.bbox:
                x0, y0, x1, y1 = ed.bbox
                if x0 <= px <= x1 and y0 <= py <= y1:
                    return ed
        return None

    def _find_handle_at(self, cx_screen, cy_screen):
        """Renvoie le nom de la poignée sous le curseur (en coords écran), ou None."""
        if self._added_sel_uid is None:
            return None
        # Trouver l'édit sélectionné
        ed = next((e for e in self.edits if e.uid == self._added_sel_uid), None)
        if not ed or not ed.bbox:
            return None
        x0, y0, x1, y1 = [v * self._scale for v in ed.bbox]
        s = self.HANDLE_SIZE
        # Convertir cx_screen, cy_screen en canvas coords
        ccx = self.canvas.canvasx(cx_screen)
        ccy = self.canvas.canvasy(cy_screen)
        positions = [
            ("nw", x0, y0), ("n", (x0+x1)/2, y0), ("ne", x1, y0),
            ("w",  x0, (y0+y1)/2),                ("e", x1, (y0+y1)/2),
            ("sw", x0, y1), ("s", (x0+x1)/2, y1), ("se", x1, y1),
        ]
        for name, hx, hy in positions:
            if hx - s <= ccx <= hx + s and hy - s <= ccy <= hy + s:
                return name
        return None

    # ── Mouse events principaux ──
    def _on_motion(self, event):
        if self._mode != "select":
            return

        # Curseur de redimensionnement si sur poignée
        handle = self._find_handle_at(event.x, event.y)
        if handle:
            cursors = {
                "nw": "size_nw_se", "se": "size_nw_se",
                "ne": "size_ne_sw", "sw": "size_ne_sw",
                "n": "size_ns", "s": "size_ns",
                "e": "size_we", "w": "size_we",
            }
            self.canvas.config(cursor=cursors.get(handle, "arrow"))
            return

        px, py = self._canvas_to_pdf(event.x, event.y)

        # Sur un texte ajouté ?
        added = self._find_added_at(px, py)
        if added:
            self.canvas.config(cursor="fleur")
            return

        # Sur du texte existant ?
        ch_idx = self._find_char_at(px, py)
        if ch_idx is not None:
            self.canvas.config(cursor="xterm")
        else:
            self.canvas.config(cursor="arrow")

    def _on_press(self, event):
        if self._mode == "add":
            cx = self.canvas.canvasx(event.x)
            cy = self.canvas.canvasy(event.y)
            self._draw_start = (cx, cy)
            return

        # Mode select
        # 1) Poignée de redimensionnement ?
        handle = self._find_handle_at(event.x, event.y)
        if handle and self._added_sel_uid is not None:
            ed = next((e for e in self.edits if e.uid == self._added_sel_uid), None)
            if ed:
                px, py = self._canvas_to_pdf(event.x, event.y)
                self._added_drag_mode = f"resize-{handle}"
                self._added_drag_start = (px, py, tuple(ed.bbox))
                return

        px, py = self._canvas_to_pdf(event.x, event.y)

        # 2) Clic sur texte ajouté → sélectionne pour déplacement
        added = self._find_added_at(px, py)
        if added:
            self._added_sel_uid = added.uid
            self._char_sel = None
            self._added_drag_mode = "move"
            self._added_drag_start = (px, py, tuple(added.bbox))
            self._load_added_into_panel(added)
            self._redraw_overlays()
            return

        # 3) Sinon : début de sélection caractères
        self._added_sel_uid = None
        ch_idx = self._find_char_at(px, py)
        if ch_idx is not None:
            self._sel_dragging = True
            self._sel_anchor = ch_idx
            self._char_sel = (ch_idx, ch_idx)
            self._redraw_overlays()
        else:
            # Clic dans le vide → désélectionner
            self._char_sel = None
            self._added_sel_uid = None
            self._load_span_into_panel()
            self._redraw_overlays()

    def _on_drag(self, event):
        # Mode add → tracé de rectangle
        if self._mode == "add" and self._draw_start:
            cx = self.canvas.canvasx(event.x)
            cy = self.canvas.canvasy(event.y)
            self.canvas.delete("draw_temp")
            self.canvas.create_rectangle(
                self._draw_start[0], self._draw_start[1], cx, cy,
                outline=C["edit_sel"], width=2, dash=(3, 2), tags="draw_temp")
            return

        px, py = self._canvas_to_pdf(event.x, event.y)

        # Déplacement / redimensionnement d'un édit ajouté
        if self._added_drag_mode and self._added_drag_start:
            ed = next((e for e in self.edits if e.uid == self._added_sel_uid), None)
            if ed:
                start_px, start_py, orig_bbox = self._added_drag_start
                dx = px - start_px
                dy = py - start_py
                ox0, oy0, ox1, oy1 = orig_bbox

                if self._added_drag_mode == "move":
                    ed.bbox = (ox0 + dx, oy0 + dy, ox1 + dx, oy1 + dy)
                elif self._added_drag_mode == "resize-nw":
                    ed.bbox = (min(ox0 + dx, ox1 - 5), min(oy0 + dy, oy1 - 5), ox1, oy1)
                elif self._added_drag_mode == "resize-ne":
                    ed.bbox = (ox0, min(oy0 + dy, oy1 - 5), max(ox1 + dx, ox0 + 5), oy1)
                elif self._added_drag_mode == "resize-sw":
                    ed.bbox = (min(ox0 + dx, ox1 - 5), oy0, ox1, max(oy1 + dy, oy0 + 5))
                elif self._added_drag_mode == "resize-se":
                    ed.bbox = (ox0, oy0, max(ox1 + dx, ox0 + 5), max(oy1 + dy, oy0 + 5))
                elif self._added_drag_mode == "resize-n":
                    ed.bbox = (ox0, min(oy0 + dy, oy1 - 5), ox1, oy1)
                elif self._added_drag_mode == "resize-s":
                    ed.bbox = (ox0, oy0, ox1, max(oy1 + dy, oy0 + 5))
                elif self._added_drag_mode == "resize-w":
                    ed.bbox = (min(ox0 + dx, ox1 - 5), oy0, ox1, oy1)
                elif self._added_drag_mode == "resize-e":
                    ed.bbox = (ox0, oy0, max(ox1 + dx, ox0 + 5), oy1)

                self._redraw_overlays()
            return

        # Sélection caractères en cours
        if self._sel_dragging and self._sel_anchor is not None:
            ch_idx = self._find_char_at(px, py)
            if ch_idx is not None:
                lo = min(self._sel_anchor, ch_idx)
                hi = max(self._sel_anchor, ch_idx)
                if self._char_sel != (lo, hi):
                    self._char_sel = (lo, hi)
                    self._redraw_overlays()

    def _on_release(self, event):
        # Mode add → finaliser le rectangle
        if self._mode == "add" and self._draw_start:
            cx = self.canvas.canvasx(event.x)
            cy = self.canvas.canvasy(event.y)
            x0 = min(self._draw_start[0], cx) / self._scale
            y0 = min(self._draw_start[1], cy) / self._scale
            x1 = max(self._draw_start[0], cx) / self._scale
            y1 = max(self._draw_start[1], cy) / self._scale
            self._draw_start = None
            self.canvas.delete("draw_temp")
            if (x1 - x0) > 4 and (y1 - y0) > 4:
                self._add_text_at_bbox((x0, y0, x1, y1))
            self._set_mode("select")
            return

        # Fin de drag édit ajouté
        if self._added_drag_mode:
            self._added_drag_mode = None
            self._added_drag_start = None
            self._snap()
            self._st_var.set("✔  Position/taille mise à jour")
            return

        # Fin de sélection caractères
        if self._sel_dragging:
            self._sel_dragging = False
            if self._char_sel:
                start, end = self._char_sel
                if start == end:
                    # Clic simple sur 1 char : sélectionner toute la ligne ou
                    # juste ce char ? On garde le char seul.
                    pass
                self._load_span_into_panel()

    # ── Panel pour sélection texte existant ──
    def _load_span_into_panel(self):
        if not self._char_sel:
            self.lbl_sel.config(
                text="Aucun texte sélectionné\n\nGlissez la souris\nsur du texte\npour sélectionner",
                bg=C["bg2"], fg=C["mid"])
            self.lbl_font_orig.config(text="")
            self._enable_controls(False)
            self._editing_bbox = None
            return

        start, end = self._char_sel
        sel_chars = self._chars[start:end + 1]
        sel_text = "".join(c["text"] for c in sel_chars)

        # Bbox englobant
        x0 = min(c["bbox"][0] for c in sel_chars)
        y0 = min(c["bbox"][1] for c in sel_chars)
        x1 = max(c["bbox"][2] for c in sel_chars)
        y1 = max(c["bbox"][3] for c in sel_chars)
        self._editing_bbox = (x0, y0, x1, y1)

        self._enable_controls(True)
        self.lbl_sel.config(
            text=f"✓ {len(sel_text)} caractère(s) sélectionné(s)",
            bg=C["blue_lt"], fg=C["navy"])

        self.txt_widget.delete("1.0", tk.END)
        self.txt_widget.insert("1.0", sel_text)

        # Attributs du PREMIER char
        first = sel_chars[0]
        is_bold   = bool(first["flags"] & 16)
        is_italic = bool(first["flags"] & 2)
        mapped, matched = map_font(first["font"], is_bold, is_italic)
        display_map = {
            "helv": "Helvetica", "hebo": "Helvetica Bold",
            "heit": "Helvetica Italic", "hebi": "Helvetica Bold Italic",
            "tiro": "Times", "tibo": "Times Bold",
            "tiit": "Times Italic", "tibi": "Times Bold Italic",
            "cour": "Courier", "cobo": "Courier Bold",
            "coit": "Courier Italic",
        }
        self.var_font.set(display_map.get(mapped, "Helvetica"))
        orig = first["font"] or "(inconnue)"
        if matched:
            self.lbl_font_orig.config(
                text=f"Police d'origine : {orig}  →  approximée", fg=C["mid"])
        else:
            self.lbl_font_orig.config(
                text=f"⚠  Police d'origine : {orig}  →  fallback", fg=C["orange"])
        self.var_size.set(round(first["size"], 1))
        r, g, b = first["color"]
        self.color_text = (r, g, b)
        self.swatch_text.config(bg="#{:02x}{:02x}{:02x}".format(
            int(r*255), int(g*255), int(b*255)))
        self._detect_bg_color((x0, y0, x1, y1))

    def _load_added_into_panel(self, ed):
        """Charge un édit 'add' dans le panneau pour édition."""
        self._editing_bbox = tuple(ed.bbox)
        self._enable_controls(True)
        self.lbl_sel.config(
            text=f"✓ Texte ajouté sélectionné\n(déplaçable / redimensionnable)",
            bg=C["blue_lt"], fg=C["navy"])
        self.txt_widget.delete("1.0", tk.END)
        self.txt_widget.insert("1.0", ed.text)
        display_map = {
            "helv": "Helvetica", "hebo": "Helvetica Bold",
            "heit": "Helvetica Italic", "hebi": "Helvetica Bold Italic",
            "tiro": "Times", "tibo": "Times Bold",
            "tiit": "Times Italic", "tibi": "Times Bold Italic",
            "cour": "Courier", "cobo": "Courier Bold",
            "coit": "Courier Italic",
        }
        self.var_font.set(display_map.get(ed.font, "Helvetica"))
        self.lbl_font_orig.config(text="(texte ajouté manuellement)", fg=C["mid"])
        self.var_size.set(round(ed.size, 1))
        r, g, b = ed.color
        self.color_text = (r, g, b)
        self.swatch_text.config(bg="#{:02x}{:02x}{:02x}".format(
            int(r*255), int(g*255), int(b*255)))
        r, g, b = ed.bg
        self.color_bg = (r, g, b)
        self.swatch_bg.config(bg="#{:02x}{:02x}{:02x}".format(
            int(r*255), int(g*255), int(b*255)))

    def _detect_bg_color(self, bbox):
        try:
            x0, y0, x1, y1 = bbox
            sample_y = max(0, y0 - 2)
            sample_x = (x0 + x1) / 2
            mat = fitz.Matrix(2, 2)
            pix = self._fpg.get_pixmap(matrix=mat,
                clip=fitz.Rect(sample_x - 1, sample_y - 1,
                               sample_x + 1, sample_y + 1))
            if pix.samples:
                r = pix.samples[0] / 255.0
                g = pix.samples[1] / 255.0
                b = pix.samples[2] / 255.0
                self.color_bg = (r, g, b)
                self.swatch_bg.config(bg="#{:02x}{:02x}{:02x}".format(
                    int(r*255), int(g*255), int(b*255)))
                return
        except Exception:
            pass
        self.color_bg = (1, 1, 1)
        self.swatch_bg.config(bg="#FFFFFF")

    def _font_display_to_key(self, display):
        mapping = {
            "Helvetica": "helv", "Helvetica Bold": "hebo",
            "Helvetica Italic": "heit", "Helvetica Bold Italic": "hebi",
            "Times": "tiro", "Times Bold": "tibo",
            "Times Italic": "tiit", "Times Bold Italic": "tibi",
            "Courier": "cour", "Courier Bold": "cobo",
            "Courier Italic": "coit",
        }
        return mapping.get(display, "helv")

    # ── Édition TEMPS RÉEL ──
    def _on_text_change(self, event=None):
        """Appelée à chaque frappe / changement de paramètre.
        Met à jour l'overlay sans snapshotter (on snapshotte au commit).
        Throttle pour éviter de saturer."""
        if self._editing_bbox is None:
            return
        # Annuler le précédent throttle
        if self._realtime_after:
            self.win.after_cancel(self._realtime_after)
        self._realtime_after = self.win.after(80, self._do_realtime_update)

    def _do_realtime_update(self):
        """Construit l'édit en cours et met à jour l'overlay live."""
        self._realtime_after = None
        if self._editing_bbox is None:
            return
        try:
            new_text = self.txt_widget.get("1.0", "end-1c")
            font = self._font_display_to_key(self.var_font.get())
            size = float(self.var_size.get())
        except Exception:
            return

        # Si c'est un édit 'add' sélectionné, on modifie l'édit existant
        if self._added_sel_uid is not None:
            ed = next((e for e in self.edits if e.uid == self._added_sel_uid), None)
            if ed:
                ed.text  = new_text
                ed.font  = font
                ed.size  = size
                ed.color = self.color_text
                ed.bg    = self.color_bg
                self._redraw_overlays()
            return

        # Sinon, c'est une sélection de texte existant → édit "preview"
        # On crée/met à jour l'édit replace pour visualiser
        ed = self._find_edit_by_bbox(self._editing_bbox)
        if ed is None:
            ed = Edit(
                kind="replace", bbox=self._editing_bbox, text=new_text,
                font=font, size=size, color=self.color_text, bg=self.color_bg,
            )
            self.edits.append(ed)
        else:
            ed.text  = new_text
            ed.font  = font
            ed.size  = size
            ed.color = self.color_text
            ed.bg    = self.color_bg
        self._redraw_overlays()

    def _find_edit_by_bbox(self, bbox):
        for ed in self.edits:
            if ed.bbox == bbox and ed.kind in ("replace", "delete"):
                return ed
        return None

    def _commit_text_edit(self):
        """Validation explicite (snapshot pour undo)."""
        if self._editing_bbox is None:
            return
        # S'assurer que l'édit reflète bien l'état actuel
        self._do_realtime_update()
        self._snap()
        self._st_var.set("✔  Modification validée")

    def _delete_selected(self):
        """Supprime soit la sélection caractères, soit le texte ajouté."""
        # Texte ajouté sélectionné → on supprime l'édit
        if self._added_sel_uid is not None:
            self.edits = [e for e in self.edits if e.uid != self._added_sel_uid]
            self._added_sel_uid = None
            self._editing_bbox = None
            self._load_span_into_panel()
            self._redraw_overlays()
            self._snap()
            self._st_var.set("🗑  Texte ajouté supprimé")
            return

        if self._char_sel is None:
            self._st_var.set("⚠  Rien à supprimer")
            return

        start, end = self._char_sel
        sel_chars = self._chars[start:end + 1]
        x0 = min(c["bbox"][0] for c in sel_chars)
        y0 = min(c["bbox"][1] for c in sel_chars)
        x1 = max(c["bbox"][2] for c in sel_chars)
        y1 = max(c["bbox"][3] for c in sel_chars)
        self._detect_bg_color((x0, y0, x1, y1))
        # Retirer un éventuel édit replace existant sur ce bbox
        self.edits = [e for e in self.edits if e.bbox != (x0, y0, x1, y1)]
        ed = Edit(kind="delete", bbox=(x0, y0, x1, y1), bg=self.color_bg)
        self.edits.append(ed)
        self._char_sel = None
        self._editing_bbox = None
        self._load_span_into_panel()
        self._redraw_overlays()
        self._snap()
        self._st_var.set("🗑  Texte supprimé")

    def _add_text_at_bbox(self, bbox):
        """Crée immédiatement un édit 'add' déplaçable, sans dialogue."""
        uid = self._next_uid
        self._next_uid += 1
        ed = Edit(
            kind="add", bbox=bbox, text="Nouveau texte",
            font=self._font_display_to_key(self.var_font.get()),
            size=float(self.var_size.get()),
            color=self.color_text, bg=(1, 1, 1), uid=uid,
        )
        self.edits.append(ed)
        self._added_sel_uid = uid
        self._char_sel = None
        self._load_added_into_panel(ed)
        self._redraw_overlays()
        self._snap()
        self._st_var.set("➕  Texte ajouté — Modifiez-le dans le panneau, déplacez-le ou redimensionnez-le")
        # Focus sur la zone de texte pour modif immédiate
        self.txt_widget.focus_set()
        self.txt_widget.tag_add(tk.SEL, "1.0", tk.END)

    def _revert_selection(self):
        """Annule l'édit sur la sélection actuelle."""
        if self._added_sel_uid is not None:
            self.edits = [e for e in self.edits if e.uid != self._added_sel_uid]
            self._added_sel_uid = None
            self._editing_bbox = None
            self._load_span_into_panel()
            self._redraw_overlays()
            self._snap()
            self._st_var.set("↺  Texte ajouté supprimé")
            return
        if self._editing_bbox is None:
            return
        before = len(self.edits)
        self.edits = [e for e in self.edits if e.bbox != self._editing_bbox]
        if len(self.edits) != before:
            self._redraw_overlays()
            self._snap()
            self._st_var.set("↺  Modification annulée pour ce texte")

    def _rotate(self, delta):
        self.rotation = (self.rotation + delta) % 360
        self._char_sel = None
        self._added_sel_uid = None
        self._editing_bbox = None
        self._render_page()
        self._load_span_into_panel()
        self._snap()
        self._st_var.set(f"⟳  Rotation appliquée : {self.rotation}°")

    def _update_stats(self):
        n_del = sum(1 for e in self.edits if e.kind == "delete")
        n_rep = sum(1 for e in self.edits if e.kind == "replace")
        n_add = sum(1 for e in self.edits if e.kind == "add")
        self.lbl_stats.config(
            text=(f"État de la page :\n"
                  f"  • Rotation : {self.rotation}°\n"
                  f"  • Suppressions : {n_del}\n"
                  f"  • Modifications : {n_rep}\n"
                  f"  • Ajouts : {n_add}\n"
                  f"  • Total édits : {len(self.edits)}\n"
                  f"  • Caractères extraits : {len(self._chars)}"))

    # ── Undo/Redo locaux ──
    def _snap(self):
        self._hist = self._hist[: self._hist_idx + 1]
        self._hist.append({
            "rotation": self.rotation,
            "edits":    copy.deepcopy(self.edits),
        })
        if len(self._hist) > self._max_hist:
            self._hist.pop(0)
        else:
            self._hist_idx += 1
        self._upd_btns()
        self._update_stats()

    def _undo(self):
        if self._hist_idx <= 0:
            self._st_var.set("Rien à annuler")
            return
        self._hist_idx -= 1
        s = self._hist[self._hist_idx]
        rotation_changed = (s["rotation"] != self.rotation)
        self.rotation = s["rotation"]
        self.edits    = copy.deepcopy(s["edits"])
        self._char_sel = None
        self._added_sel_uid = None
        self._editing_bbox = None
        if rotation_changed:
            self._render_page()
        else:
            self._redraw_overlays()
        self._load_span_into_panel()
        self._upd_btns()
        self._update_stats()
        self._st_var.set("↶  Annulé")

    def _redo(self):
        if self._hist_idx >= len(self._hist) - 1:
            self._st_var.set("Rien à rétablir")
            return
        self._hist_idx += 1
        s = self._hist[self._hist_idx]
        rotation_changed = (s["rotation"] != self.rotation)
        self.rotation = s["rotation"]
        self.edits    = copy.deepcopy(s["edits"])
        self._char_sel = None
        self._added_sel_uid = None
        self._editing_bbox = None
        if rotation_changed:
            self._render_page()
        else:
            self._redraw_overlays()
        self._load_span_into_panel()
        self._upd_btns()
        self._update_stats()
        self._st_var.set("↷  Rétabli")

    def _upd_btns(self):
        self.btn_eundo.config(
            state="normal" if self._hist_idx > 0 else "disabled")
        self.btn_eredo.config(
            state="normal" if self._hist_idx < len(self._hist) - 1 else "disabled")

    def _on_save(self):
        # Commit any pending real-time edit before saving
        if self._realtime_after:
            self.win.after_cancel(self._realtime_after)
            self._realtime_after = None
        if self._editing_bbox is not None:
            self._do_realtime_update()
        self.app.on_editor_save(self.pos, self.rotation, self.edits)
        self._doc.close()
        self.win.destroy()

    def _on_cancel(self):
        if self.edits != self.page.edits or self.rotation != self.page.rotation:
            if not messagebox.askyesno("Confirmer",
                "Annuler les modifications non enregistrées ?",
                parent=self.win):
                return
        self._doc.close()
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