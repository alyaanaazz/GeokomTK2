"""
CSCE604045 Geometri Komputasional - Tugas Pemrograman 2
Implementasi Algoritma Fortune untuk Diagram Voronoi
+ clipping ke bounding box + lingkaran kosong terbesar
+ input file & mouse (tkinter)

Cara jalan:  python fortune_voronoi.py
"""

import math
import heapq
import tkinter as tk
from tkinter import filedialog, messagebox

EPS = 1e-9

# =====================================================================
# 1. STRUKTUR DATA DASAR
# =====================================================================

class Site:
    """Titik site (fokus parabola)."""
    __slots__ = ("x", "y")
    def __init__(self, x, y):
        self.x, self.y = float(x), float(y)
    def __repr__(self):
        return f"Site({self.x:.1f},{self.y:.1f})"


class Arc:
    """
    Busur pada beach line. Tiap busur 'dimiliki' satu site.
    prev/next membentuk doubly-linked list (pengganti BST).
    event = circle event yang mungkin menghapus busur ini (atau None).
    """
    __slots__ = ("site", "prev", "next", "event", "edge_left", "edge_right")
    def __init__(self, site):
        self.site = site
        self.prev = self.next = None
        self.event = None
        self.edge_left = None   # half-edge di sisi kiri busur
        self.edge_right = None  # half-edge di sisi kanan busur


class HalfEdge:
    """
    Half-edge. Pasangan (twin) membentuk satu edge Voronoi penuh.
    start  = titik awal (vertex Voronoi) atau None (menuju infinity)
    end    = titik akhir (vertex Voronoi) atau None (menuju infinity)
    direction = vektor arah (dipakai untuk clipping bila end None)
    """
    __slots__ = ("start", "end", "twin", "direction", "site")
    def __init__(self):
        self.start = self.end = self.twin = None
        self.direction = None
        self.site = None


class Event:
    """
    Event pada priority queue.
    kind = 'site'   -> site event (sweep mencapai sebuah site)
    kind = 'circle' -> circle event (3 busur bertemu)
    """
    __slots__ = ("y", "x", "kind", "arc", "site", "valid")
    def __init__(self, y, x, kind, arc=None, site=None):
        self.y, self.x, self.kind = y, x, kind
        self.arc, self.site = arc, site
        self.valid = True
    def __lt__(self, other):
        # sweep bergerak dari y besar ke y kecil (atas -> bawah layar)
        if abs(self.y - other.y) > EPS:
            return self.y > other.y
        return self.x < other.x


# =====================================================================
# 2. ALGORITMA FORTUNE
# =====================================================================

class FortuneVoronoi:
    def __init__(self, sites, bbox):
        """
        sites : list Site
        bbox  : (xmin, ymin, xmax, ymax) bounding box untuk clipping
        """
        self.sites = sites
        self.bbox = bbox
        self.events = []          # priority queue
        self.beach = None          # kepala linked-list busur
        self.edges = []            # semua half-edge
        self.vertices = []         # (x, y, radius, (site1,site2,site3)) hasil circle event
        self.sweep_y = 0.0

    # ---------- util parabola ----------
    @staticmethod
    def _parabola_x(p, y, sweep_y):
        """x pada parabola dengan fokus p di ketinggian y."""
        if abs(p.y - sweep_y) < EPS:
            return p.x
        d = y - sweep_y
        return p.x + (d * d) / (2.0 * (p.y - sweep_y))

    @staticmethod
    def _intersection(p, q, sweep_y):
        """
        x-intersection antara parabola fokus p dan q pada sweep_y.
        Mengembalikan (x_kiri, x_kanan). Kedua busur bertemu di sini.
        """
        if abs(p.y - q.y) < EPS:
            return (p.x + q.x) / 2.0, (p.x + q.x) / 2.0
        # rumus standar Fortune (lihat de Berg et al.)
        a = q.x - p.x
        b = q.y - p.y
        # selesaikan d = y - sweep_y
        # x = ( (p.x+q.x) +- sqrt( ... ) ) / 2
        # versi sederhana: cari akar dengan formula kuadrat
        # persamaan: (x-p.x)^2/(2(p.y-s)) + p.y = (x-q.x)^2/(2(q.y-s)) + q.y
        # -> koefisien kuadrat A x^2 + B x + C = 0
        s = sweep_y
        A = (q.y - p.y)
        B = 2.0 * (p.x * (q.y - s) - q.x * (p.y - s))
        C = (p.y - s) * (q.x * q.x + q.y * q.y - s * s) \
            - (q.y - s) * (p.x * p.x + p.y * p.y - s * s)
        # A x^2 + B x + C = 0 dengan A = 2(q.y-p.y)
        A = 2.0 * A
        if abs(A) < EPS:
            return (p.x + q.x) / 2.0, (p.x + q.x) / 2.0
        disc = B * B - 4.0 * A * C
        if disc < 0:
            disc = 0.0
        sq = math.sqrt(disc)
        x1 = (-B - sq) / (2.0 * A)
        x2 = (-B + sq) / (2.0 * A)
        return (min(x1, x2), max(x1, x2))

    # ---------- circumcenter (untuk circle event) ----------
    @staticmethod
    def _circumcenter(a, b, c):
        ax, ay = a.x, a.y
        bx, by = b.x, b.y
        cx, cy = c.x, c.y
        d = 2.0 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
        if abs(d) < EPS:
            return None
        ux = ((ax*ax + ay*ay) * (by - cy) +
              (bx*bx + by*by) * (cy - ay) +
              (cx*cx + cy*cy) * (ay - by)) / d
        uy = ((ax*ax + ay*ay) * (cx - bx) +
              (bx*bx + by*by) * (ax - cx) +
              (cx*cx + cy*cy) * (bx - ax)) / d
        return ux, uy

    # ---------- cek circle event pada sebuah busur ----------
    def _check_circle(self, arc):
        if arc.prev is None or arc.next is None:
            return
        a, b, c = arc.prev.site, arc.site, arc.next.site
        cc = self._circumcenter(a, b, c)
        if cc is None:
            return
        cx, cy = cc
        # event hanya valid bila titik terendah lingkaran di bawah sweep line
        r = math.hypot(cx - a.x, cy - a.y)
        # titik terendah circle: (cx, cy + r); harus di bawah sweep (y > sweep_y)
        if cy + r <= self.sweep_y + EPS:
            return
        ev = Event(cy + r, cx, "circle", arc=arc)
        arc.event = ev
        heapq.heappush(self.events, ev)

    def _invalidate(self, arc):
        if arc and arc.event:
            arc.event.valid = False
            arc.event = None

    # ---------- helper linked-list busur ----------
    def _insert_arc_after(self, arc, new_arc):
        new_arc.next = arc.next
        new_arc.prev = arc
        if arc.next:
            arc.next.prev = new_arc
        arc.next = new_arc

    def _remove_arc(self, arc):
        if arc.prev:
            arc.prev.next = arc.next
        if arc.next:
            arc.next.prev = arc.prev
        if self.beach is arc:
            self.beach = arc.next

    # ---------- site event ----------
    def _handle_site(self, ev):
        site = ev.site
        self.sweep_y = ev.y
        # jika beach line kosong
        if self.beach is None:
            self.beach = Arc(site)
            return
        # cari busur yang "ditimpa" site (x site berada di busur itu)
        arc = self.beach
        while arc is not None:
            if arc.next is None:
                break
            xk, xkn = self._intersection(arc.site, arc.next.site, self.sweep_y)
            if site.x <= xkn:
                break
            arc = arc.next
        # jika site tepat di atas busur dengan y sama (degenerate) -> skip
        if abs(arc.site.y - site.y) < EPS:
            return
        # buat dua half-edge baru (sepasang twin) di sekitar busur
        e1 = HalfEdge(); e2 = HalfEdge()
        e1.twin, e2.twin = e2, e1
        e1.direction = (0, 0)  # akan diisi saat clip
        e2.direction = (0, 0)
        e1.site, e2.site = arc.site, site
        self.edges.extend([e1, e2])
        # sisipkan dua busur baru
        split = Arc(site)
        split.edge_left = e1
        split.edge_right = e2
        old_right = arc.next
        arc.next = None
        self._insert_arc_after(arc, split)
        new_right = Arc(arc.site)
        new_right.edge_left = e2
        new_right.edge_right = e1
        self._insert_arc_after(split, new_right)
        if old_right:
            new_right.next = old_right
            old_right.prev = new_right
        # invalidate event lama pada arc
        self._invalidate(arc)
        # cek event pada busur baru
        self._check_circle(arc)
        self._check_circle(split)
        self._check_circle(new_right)

    # ---------- circle event ----------
    def _handle_circle(self, ev):
        arc = ev.arc
        if not ev.valid or arc is None or arc.prev is None or arc.next is None:
            return
        a, b, c = arc.prev, arc, arc.next
        # vertex Voronoi
        cc = self._circumcenter(a.site, b.site, c.site)
        if cc is None:
            return
        vx, vy = cc
        r = math.hypot(vx - a.site.x, vy - a.site.y)
        self.vertices.append((vx, vy, r, (a.site, b.site, c.site)))
        self.sweep_y = ev.y
        # sambungkan half-edge kiri & kanan busur
        el = arc.edge_left
        er = arc.edge_right
        if el:
            el.end = (vx, vy)
        if er:
            er.end = (vx, vy)
        # buat edge baru antara a.site dan c.site
        e_new1 = HalfEdge(); e_new2 = HalfEdge()
        e_new1.twin, e_new2.twin = e_new2, e_new1
        e_new1.start = e_new2.start = (vx, vy)
        e_new1.site, e_new2.site = a.site, c.site
        # arah edge baru: tegak lurus garis a.site-c.site
        dx = c.site.x - a.site.x
        dy = c.site.y - a.site.y
        norm = math.hypot(dx, dy) or 1.0
        e_new1.direction = (dy / norm, -dx / norm)
        e_new2.direction = (-dy / norm, dx / norm)
        if a.edge_right: a.edge_right = e_new1
        if c.edge_left: c.edge_left = e_new2
        self.edges.extend([e_new1, e_new2])
        # hapus busur b
        self._remove_arc(b)
        # invalidate event
        self._invalidate(a)
        self._invalidate(c)
        # cek ulang
        self._check_circle(a)
        self._check_circle(c)

    # ---------- sweep ----------
    def sweep(self):
        # isi site event (urut dari y besar ke kecil)
        for s in self.sites:
            heapq.heappush(self.events, Event(s.y, s.x, "site", site=s))
        while self.events:
            ev = heapq.heappop(self.events)
            if ev.kind == "site":
                self._handle_site(ev)
            else:
                self._handle_circle(ev)
        return self.edges, self.vertices

    # ---------- clipping ke bounding box ----------
    def clip(self):
        xmin, ymin, xmax, ymax = self.bbox
        clipped = []
        for e in self.edges:
            if e.start is None and e.end is None:
                continue
            p0 = e.start
            p1 = e.end
            # jika salah satu ujung None -> pakai direction untuk hitung titik jauh
            if p0 is None and p1 is not None and e.direction:
                dx, dy = e.direction
                p0 = (p1[0] - dx * 1e5, p1[1] - dy * 1e5)
            if p1 is None and p0 is not None and e.direction:
                dx, dy = e.direction
                p1 = (p0[0] + dx * 1e5, p0[1] + dy * 1e5)
            if p0 is None or p1 is None:
                continue
            seg = _clip_segment(p0, p1, xmin, ymin, xmax, ymax)
            if seg:
                clipped.append(seg)
        return clipped

    # ---------- lingkaran kosong terbesar ----------
    def largest_empty_circles(self):
        best = []
        for (cx, cy, r, sites3) in self.vertices:
            # validasi: tidak ada site lain di dalam lingkaran
            ok = True
            for s in self.sites:
                if (s.x - cx) ** 2 + (s.y - cy) ** 2 < (r - 1e-6) ** 2:
                    ok = False
                    break
            if not ok:
                continue
            if not best or r > best[0][0] + 1e-6:
                best = [(r, cx, cy)]
            elif abs(r - best[0][0]) <= 1e-6:
                best.append((r, cx, cy))
        return best


# =====================================================================
# 3. CLIPPING SEGMEN (Liang-Barsky)
# =====================================================================

def _clip_segment(p0, p1, xmin, ymin, xmax, ymax):
    x0, y0 = p0
    x1, y1 = p1
    dx, dy = x1 - x0, y1 - y0
    p = [-dx, dx, -dy, dy]
    q = [x0 - xmin, xmax - x0, y0 - ymin, ymax - y0]
    u1, u2 = 0.0, 1.0
    for pi, qi in zip(p, q):
        if abs(pi) < EPS:
            if qi < 0:
                return None
        else:
            t = qi / pi
            if pi < 0:
                if t > u2: return None
                if t > u1: u1 = t
            else:
                if t < u1: return None
                if t < u2: u2 = t
    return (x0 + u1 * dx, y0 + u1 * dy, x0 + u2 * dx, y0 + u2 * dy)


# =====================================================================
# 4. GUI
# =====================================================================

class VoronoiGUI:
    def __init__(self, root):
        self.root = root
        self.root.title("Fortune Voronoi - Tugas TP2")
        self.W, self.H = 900, 650
        self.canvas = tk.Canvas(root, width=self.W, height=self.H, bg="white")
        self.canvas.pack(side=tk.TOP)
        self.sites = []
        self.circle_items = []

        # toolbar
        bar = tk.Frame(root); bar.pack(side=tk.TOP, fill=tk.X)
        tk.Button(bar, text="Load File", command=self.load_file).pack(side=tk.LEFT)
        tk.Button(bar, text="Clear", command=self.clear).pack(side=tk.LEFT)
        tk.Button(bar, text="Show Largest Empty Circles",
                  command=self.show_circles).pack(side=tk.LEFT)
        tk.Button(bar, text="Hide Circles",
                  command=self.hide_circles).pack(side=tk.LEFT)
        tk.Button(bar, text="Redraw", command=self.redraw).pack(side=tk.LEFT)

        self.canvas.bind("<Button-1>", self.on_click)

    # ---------- interaksi ----------
    def on_click(self, event):
        self.sites.append(Site(event.x, event.y))
        self.redraw()

    def load_file(self):
        path = filedialog.askopenfilename(filetypes=[("Text", "*.txt")])
        if not path:
            return
        try:
            with open(path) as f:
                for line in f:
                    line = line.strip()
                    if not line or line.startswith("#"):
                        continue
                    parts = line.replace(",", " ").split()
                    if len(parts) < 2:
                        continue
                    self.sites.append(Site(float(parts[0]), float(parts[1])))
        except Exception as e:
            messagebox.showerror("Error", str(e))
            return
        self.redraw()

    def clear(self):
        self.sites.clear()
        self.canvas.delete("all")
        self.circle_items.clear()

    def hide_circles(self):
        for it in self.circle_items:
            self.canvas.delete(it)
        self.circle_items.clear()

    # ---------- gambar ----------
    def redraw(self):
        self.canvas.delete("all")
        self.circle_items.clear()
        if len(self.sites) < 3:
            for s in self.sites:
                self.canvas.create_oval(s.x-3, s.y-3, s.x+3, s.y+3, fill="black")
            return
        bbox = (0, 0, self.W, self.H)
        fv = FortuneVoronoi(self.sites, bbox)
        fv.sweep()
        segs = fv.clip()
        for (x0, y0, x1, y1) in segs:
            self.canvas.create_line(x0, y0, x1, y1, fill="#333", width=1)
        for s in self.sites:
            self.canvas.create_oval(s.x-3, s.y-3, s.x+3, s.y+3,
                                    fill="black", outline="")
        # simpan hasil untuk show_circles
        self._fv = fv

    def show_circles(self):
        if not hasattr(self, "_fv"):
            return
        self.hide_circles()
        circles = self._fv.largest_empty_circles()
        if not circles:
            messagebox.showinfo("Info", "Tidak ada lingkaran kosong ditemukan.")
            return
        for (r, cx, cy) in circles:
            it = self.canvas.create_oval(cx-r, cy-r, cx+r, cy+r,
                                         outline="orange", width=2)
            self.circle_items.append(it)


# =====================================================================
# 5. MAIN
# =====================================================================

if __name__ == "__main__":
    root = tk.Tk()
    app = VoronoiGUI(root)
    root.mainloop()