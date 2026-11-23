"""
CSCE604045 Geometri Komputasional - Tugas Pemrograman 2
Algoritma Fortune (sweep line) untuk Diagram Voronoi
+ clipping ke bounding box
+ lingkaran kosong terbesar (pusat di dalam convex hull)
+ input file & mouse (tkinter)

Cara jalan:  python fortune_voronoi.py

Konvensi koordinat: koordinat layar (y membesar ke bawah).
Sweep line horizontal bergerak dari ATAS (y kecil) ke BAWAH (y besar).
Beach line = batas bawah gabungan parabola; parabola terbuka ke atas layar.
"""

import math
import heapq
import itertools

try:
    import tkinter as tk
    from tkinter import filedialog, messagebox
except ImportError:          # supaya algoritma tetap bisa diimport/ditest tanpa tkinter
    tk = None

EPS = 1e-9
BIG = 1e6                    # panjang "tak hingga" untuk edge tak terbatas


# =====================================================================
# 1. STRUKTUR DATA
# =====================================================================

class Site:
    """Titik site (fokus parabola)."""
    __slots__ = ("x", "y")

    def __init__(self, x, y):
        self.x, self.y = float(x), float(y)

    def __repr__(self):
        return f"Site({self.x:g},{self.y:g})"


class Arc:
    """Busur pada beach line (milik satu site). event = circle event yang akan menghapusnya."""
    __slots__ = ("site", "event")

    def __init__(self, site):
        self.site = site
        self.event = None


class Edge:
    """
    Setengah edge Voronoi yang dijejak oleh sebuah breakpoint.
    left, right : site pada sisi kiri / kanan breakpoint
    start       : titik awal (selalu ada)
    end         : titik akhir (None = edge menuju tak hingga)
    Arah jejak breakpoint = vektor (right-left) diputar 90 derajat (koordinat layar).
    """
    __slots__ = ("left", "right", "start", "end")

    def __init__(self, left, right, start):
        self.left, self.right, self.start, self.end = left, right, start, None

    def direction(self):
        dx = self.right.x - self.left.x
        dy = self.right.y - self.left.y
        n = math.hypot(dx, dy) or 1.0
        return (-dy / n, dx / n)


class Event:
    """kind = 'site' atau 'circle'. Untuk circle: arc = busur yang hilang, triple = (a,b,c)."""
    __slots__ = ("y", "x", "kind", "site", "arc", "triple", "valid")

    def __init__(self, y, x, kind, site=None, arc=None, triple=None):
        self.y, self.x, self.kind = y, x, kind
        self.site, self.arc, self.triple = site, arc, triple
        self.valid = True


# =====================================================================
# 2. ALGORITMA FORTUNE
# =====================================================================

class FortuneVoronoi:
    def __init__(self, sites, bbox):
        """sites: list Site ; bbox: (xmin, ymin, xmax, ymax)"""
        seen, uniq = set(), []
        for s in sites:                       # buang site duplikat
            key = (round(s.x, 9), round(s.y, 9))
            if key not in seen:
                seen.add(key)
                uniq.append(s)
        self.sites = uniq
        self.bbox = bbox
        self.arcs = []        # beach line: busur kiri -> kanan
        self.bps = []         # bps[i] = edge yang dijejak breakpoint antara arcs[i] dan arcs[i+1]
        self.edges = []
        self.vertices = []    # (x, y, r, (a, b, c))
        self.sweep_y = 0.0
        self._heap = []
        self._cnt = itertools.count()

    # ---------- geometri ----------
    @staticmethod
    def _breakpoint(p, q, l):
        """
        x dari breakpoint antara busur p (kiri) dan q (kanan) untuk directrix y = l.
        Parabola fokus p: y = ((x-px)^2 + py^2 - l^2) / (2 (py - l)).
        """
        dp = 2.0 * (p.y - l)
        dq = 2.0 * (q.y - l)
        if abs(dp) < EPS:          # p tepat di sweep line -> parabola = garis vertikal
            return p.x
        if abs(dq) < EPS:
            return q.x
        a = dq - dp
        if abs(a) < EPS:           # y sama -> titik tengah
            return (p.x + q.x) / 2.0
        b = 2.0 * (q.x * dp - p.x * dq)
        c = dq * (p.x ** 2 + p.y ** 2 - l * l) - dp * (q.x ** 2 + q.y ** 2 - l * l)
        disc = max(b * b - 4.0 * a * c, 0.0)
        sq = math.sqrt(disc)
        r1 = (-b - sq) / (2.0 * a)
        r2 = (-b + sq) / (2.0 * a)
        lo, hi = min(r1, r2), max(r1, r2)
        # q lebih dekat ke directrix (y lebih besar) -> akar kecil, selain itu akar besar
        return lo if q.y > p.y else hi

    @staticmethod
    def _parabola_y(p, x, l):
        return ((x - p.x) ** 2 + p.y ** 2 - l * l) / (2.0 * (p.y - l))

    @staticmethod
    def _circumcenter(a, b, c):
        d = 2.0 * (a.x * (b.y - c.y) + b.x * (c.y - a.y) + c.x * (a.y - b.y))
        if abs(d) < EPS:
            return None
        a2, b2, c2 = a.x ** 2 + a.y ** 2, b.x ** 2 + b.y ** 2, c.x ** 2 + c.y ** 2
        ux = (a2 * (b.y - c.y) + b2 * (c.y - a.y) + c2 * (a.y - b.y)) / d
        uy = (a2 * (c.x - b.x) + b2 * (a.x - c.x) + c2 * (b.x - a.x)) / d
        return ux, uy

    # ---------- circle event ----------
    def _check_circle(self, i):
        """Cek apakah busur arcs[i] akan menghilang; jika ya, jadwalkan circle event."""
        if i <= 0 or i >= len(self.arcs) - 1:
            return
        arc = self.arcs[i]
        if arc.event is not None:
            arc.event.valid = False
            arc.event = None
        a, b, c = self.arcs[i - 1].site, arc.site, self.arcs[i + 1].site
        if a is c:
            return
        # breakpoint kiri & kanan hanya bertemu bila belok searah (koordinat layar: cross > 0)
        cross = (b.x - a.x) * (c.y - b.y) - (b.y - a.y) * (c.x - b.x)
        if cross <= EPS:
            return
        cc = self._circumcenter(a, b, c)
        if cc is None:
            return
        cx, cy = cc
        r = math.hypot(cx - b.x, cy - b.y)
        ey = cy + r                           # titik terbawah lingkaran = saat busur hilang
        if ey < self.sweep_y - 1e-7:
            return
        ev = Event(ey, cx, "circle", arc=arc, triple=(a, b, c))
        arc.event = ev
        heapq.heappush(self._heap, (ey, 0, cx, next(self._cnt), ev))

    # ---------- site event ----------
    def _handle_site(self, site):
        y = site.y
        self.sweep_y = y
        if not self.arcs:
            self.arcs.append(Arc(site))
            return

        # cari busur yang berada tepat di atas site baru
        i = 0
        while i < len(self.arcs) - 1 and \
                site.x >= self._breakpoint(self.arcs[i].site, self.arcs[i + 1].site, y):
            i += 1
        arc = self.arcs[i]

        if abs(arc.site.y - y) < EPS:
            # degenerate: y sama dengan site pada busur -> busur baru di kanan,
            # edge-nya berupa garis vertikal yang datang dari tak hingga (atas)
            mx = (arc.site.x + site.x) / 2.0
            e = Edge(arc.site, site, (mx, y - BIG))
            self.edges.append(e)
            self.arcs.insert(i + 1, Arc(site))
            self.bps.insert(i, e)
            self._check_circle(i)
            self._check_circle(i + 1)
            return

        # kasus umum: pecah busur menjadi kiri - baru - kanan
        if arc.event is not None:
            arc.event.valid = False
            arc.event = None
        py = self._parabola_y(arc.site, site.x, y)
        start = (site.x, py)
        e_left = Edge(arc.site, site, start)    # breakpoint (lama, baru)
        e_right = Edge(site, arc.site, start)   # breakpoint (baru, lama)
        self.edges.extend([e_left, e_right])

        left, mid, right = Arc(arc.site), Arc(site), Arc(arc.site)
        self.arcs[i:i + 1] = [left, mid, right]
        self.bps.insert(i, e_left)
        self.bps.insert(i + 1, e_right)

        self._check_circle(i)        # left
        self._check_circle(i + 2)    # right

    # ---------- circle event ----------
    def _handle_circle(self, ev):
        arc = ev.arc
        arc.event = None
        try:
            i = self.arcs.index(arc)
        except ValueError:
            return
        if i <= 0 or i >= len(self.arcs) - 1:
            return
        a, b, c = self.arcs[i - 1].site, arc.site, self.arcs[i + 1].site
        if (a, b, c) != ev.triple:
            return
        cc = self._circumcenter(a, b, c)
        if cc is None:
            return
        vx, vy = cc
        r = math.hypot(vx - b.x, vy - b.y)
        self.sweep_y = ev.y
        self.vertices.append((vx, vy, r, (a, b, c)))

        # dua edge yang bertemu berakhir di vertex ini
        self.bps[i - 1].end = (vx, vy)
        self.bps[i].end = (vx, vy)
        # edge baru antara a dan c mulai dari vertex
        e_new = Edge(a, c, (vx, vy))
        self.edges.append(e_new)
        self.bps[i - 1:i + 1] = [e_new]
        del self.arcs[i]

        self._check_circle(i - 1)
        self._check_circle(i)

    # ---------- sweep ----------
    def sweep(self):
        self.arcs, self.bps, self.edges, self.vertices = [], [], [], []
        self._heap = []
        for s in self.sites:
            heapq.heappush(self._heap,
                           (s.y, 1, s.x, next(self._cnt), Event(s.y, s.x, "site", site=s)))
        while self._heap:
            ev = heapq.heappop(self._heap)[-1]
            if ev.kind == "site":
                self._handle_site(ev.site)
            elif ev.valid:
                self._handle_circle(ev)
        return self.edges, self.vertices

    # ---------- segmen mentah & clipping ----------
    def raw_segments(self):
        """Semua edge Voronoi sebagai segmen (edge tak hingga dipanjangkan sejauh BIG)."""
        segs = []
        for e in self.edges:
            p0 = e.start
            p1 = e.end
            if p1 is None:
                dx, dy = e.direction()
                p1 = (p0[0] + dx * 2 * BIG, p0[1] + dy * 2 * BIG)
            segs.append((p0, p1))
        return segs

    def clip(self):
        xmin, ymin, xmax, ymax = self.bbox
        out = []
        for p0, p1 in self.raw_segments():
            seg = _clip_segment(p0, p1, xmin, ymin, xmax, ymax)
            if seg:
                out.append(seg)
        return out

    # ---------- lingkaran kosong terbesar ----------
    def largest_empty_circles(self):
        """
        Lingkaran kosong terbesar dengan pusat di dalam convex hull site.
        Kandidat pusat: (1) vertex Voronoi di dalam hull,
                        (2) titik potong edge Voronoi dengan sisi convex hull.
        Jari-jari = jarak ke site terdekat.
        """
        if len(self.sites) < 3:
            return []
        hull = convex_hull([(s.x, s.y) for s in self.sites])
        if len(hull) < 3:
            return []
        cands = [(vx, vy) for (vx, vy, _r, _t) in self.vertices
                 if _inside_convex(hull, vx, vy)]
        for p0, p1 in self.raw_segments():
            for k in range(len(hull)):
                q = _seg_intersect(p0, p1, hull[k], hull[(k + 1) % len(hull)])
                if q:
                    cands.append(q)
        best, res = -1.0, []
        for (cx, cy) in cands:
            r = min(math.hypot(cx - s.x, cy - s.y) for s in self.sites)
            if r > best + 1e-6:
                best, res = r, [(r, cx, cy)]
            elif abs(r - best) <= 1e-6 and \
                    all(math.hypot(cx - c[1], cy - c[2]) > 1e-6 for c in res):
                res.append((r, cx, cy))
        return res


# =====================================================================
# 3. GEOMETRI PENDUKUNG
# =====================================================================

def _clip_segment(p0, p1, xmin, ymin, xmax, ymax):
    """Liang-Barsky."""
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
                if t > u2:
                    return None
                u1 = max(u1, t)
            else:
                if t < u1:
                    return None
                u2 = min(u2, t)
    return (x0 + u1 * dx, y0 + u1 * dy, x0 + u2 * dx, y0 + u2 * dy)


def convex_hull(points):
    """Monotone chain. Mengembalikan list titik hull (tanpa duplikat)."""
    pts = sorted(set(points))
    if len(pts) <= 2:
        return pts

    def cross(o, a, b):
        return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])

    lower = []
    for p in pts:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], p) <= 0:
            lower.pop()
        lower.append(p)
    upper = []
    for p in reversed(pts):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], p) <= 0:
            upper.pop()
        upper.append(p)
    return lower[:-1] + upper[:-1]


def _inside_convex(hull, x, y, tol=1e-7):
    pos = neg = False
    for k in range(len(hull)):
        a, b = hull[k], hull[(k + 1) % len(hull)]
        c = (b[0] - a[0]) * (y - a[1]) - (b[1] - a[1]) * (x - a[0])
        if c > tol:
            pos = True
        elif c < -tol:
            neg = True
        if pos and neg:
            return False
    return True


def _seg_intersect(p0, p1, q0, q1):
    rx, ry = p1[0] - p0[0], p1[1] - p0[1]
    sx, sy = q1[0] - q0[0], q1[1] - q0[1]
    den = rx * sy - ry * sx
    if abs(den) < 1e-12:
        return None
    t = ((q0[0] - p0[0]) * sy - (q0[1] - p0[1]) * sx) / den
    u = ((q0[0] - p0[0]) * ry - (q0[1] - p0[1]) * rx) / den
    if -1e-9 <= t <= 1 + 1e-9 and -1e-9 <= u <= 1 + 1e-9:
        return (p0[0] + t * rx, p0[1] + t * ry)
    return None


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
        self._fv = None

        bar = tk.Frame(root)
        bar.pack(side=tk.TOP, fill=tk.X)
        tk.Button(bar, text="Load File", command=self.load_file).pack(side=tk.LEFT)
        tk.Button(bar, text="Clear", command=self.clear).pack(side=tk.LEFT)
        tk.Button(bar, text="Show Largest Empty Circles",
                  command=self.show_circles).pack(side=tk.LEFT)
        tk.Button(bar, text="Hide Circles", command=self.hide_circles).pack(side=tk.LEFT)
        tk.Button(bar, text="Redraw", command=self.redraw).pack(side=tk.LEFT)
        self.status = tk.Label(bar, text="Klik canvas untuk menambah site", anchor="w")
        self.status.pack(side=tk.LEFT, padx=8)

        self.canvas.bind("<Button-1>", self.on_click)

    def on_click(self, event):
        self.sites.append(Site(event.x, event.y))
        self.redraw()

    def load_file(self):
        path = filedialog.askopenfilename(filetypes=[("Text", "*.txt")])
        if not path:
            return
        new_sites = []
        try:
            with open(path) as f:
                for line in f:
                    line = line.strip()
                    if not line or line.startswith("#"):
                        continue
                    parts = line.replace(",", " ").split()
                    if len(parts) < 2:
                        continue
                    new_sites.append(Site(float(parts[0]), float(parts[1])))
        except Exception as e:
            messagebox.showerror("Error", str(e))
            return
        self.sites = new_sites           # file MENGGANTI site yang ada
        self.redraw()

    def clear(self):
        self.sites.clear()
        self._fv = None
        self.canvas.delete("all")
        self.circle_items.clear()
        self.status.config(text="Klik canvas untuk menambah site")

    def hide_circles(self):
        for it in self.circle_items:
            self.canvas.delete(it)
        self.circle_items.clear()

    def redraw(self):
        self.canvas.delete("all")
        self.circle_items.clear()
        self._fv = None
        if len(self.sites) >= 2:
            fv = FortuneVoronoi(self.sites, (0, 0, self.W, self.H))
            fv.sweep()
            for (x0, y0, x1, y1) in fv.clip():
                self.canvas.create_line(x0, y0, x1, y1, fill="#333", width=1)
            self._fv = fv
        for s in self.sites:
            self.canvas.create_oval(s.x - 3, s.y - 3, s.x + 3, s.y + 3,
                                    fill="black", outline="")
        self.status.config(text=f"{len(self.sites)} site")

    def show_circles(self):
        if self._fv is None:
            return
        self.hide_circles()
        circles = self._fv.largest_empty_circles()
        if not circles:
            messagebox.showinfo("Info", "Tidak ada lingkaran kosong ditemukan.")
            return
        for (r, cx, cy) in circles:
            self.circle_items.append(self.canvas.create_oval(
                cx - r, cy - r, cx + r, cy + r, outline="orange", width=2))
            self.circle_items.append(self.canvas.create_oval(
                cx - 3, cy - 3, cx + 3, cy + 3, fill="orange", outline=""))
        r, cx, cy = circles[0]
        self.status.config(text=f"Lingkaran terbesar: r={r:.2f}, pusat=({cx:.1f}, {cy:.1f})")


# =====================================================================
# 5. MAIN
# =====================================================================

if __name__ == "__main__":
    root = tk.Tk()
    app = VoronoiGUI(root)
    root.mainloop()