#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = ["shapely>=2", "pyproj>=3", "uharfbuzz>=0.40"]
# ///
"""Generate a laser-cut wedding money gift: a world map board for banknotes.

Two A5 boards of 3 mm plywood: the front has the world map cut out (banknotes
show through), the back is plain. Cords run through the four holes and tie
both together.

  red  (#e01b24) = cut
  blue (#3584e4) = engrave

The map uses the Equal Earth projection: an equal-area ("true size") world map,
so Africa is not dwarfed by Greenland as in Mercator.

Usage:  uv run make_gift.py --names "Hildegard & Waldemar" --date "12. Juni 2027"
"""
import argparse
import json
import math
import urllib.request
from pathlib import Path

import pyproj
import uharfbuzz as hb
from shapely import affinity
from shapely.geometry import LineString, MultiPolygon, Point, Polygon, box, shape
from shapely.ops import unary_union

HERE = Path(__file__).parent

# --- Default text --------------------------------------------------------------
PHRASE = "Die schönste Reise beginnt zu zweit"
NAMES = "Hildegard & Waldemar"

# --- Dimensions (mm) -------------------------------------------------------------
W, H = 210.0, 148.0      # A5 landscape
CORNER_R = 3.0
HOLE_D = 4.0             # holes for the cord (suede cord ~3 mm)
HOLE_INSET = 10.0        # hole centre distance from the side and top/bottom edge
MAP_W = 152.0            # map width
MAP_TOP = 27.0
MAP_DX = 0.0             # shift the map sideways
CENTER_LON = 11.0        # map centre (Europe in the middle)
MIN_WOOD = 1.5           # no wood (sea) narrower than this: straits get widened, inlets filled
WIDEN_STEP = 0.25        # straits are widened in steps of this much per side
MIN_CUT_AREA = 0.8       # smaller islands (mm²) are left out
CLEARANCE = 0.8          # engraving stays this far from cut lines
HATCH_SPACING = 0.2      # line spacing of filled engravings
COMPASS_X, COMPASS_Y, COMPASS_R = 26.0, 118.0, 9.0

CUT = "fill:none;stroke:#e01b24;stroke-width:0.2;stroke-linecap:round;stroke-linejoin:round"
ENGRAVE = "fill:none;stroke:#3584e4;stroke-width:0.28125;stroke-linecap:round;stroke-linejoin:round"

# Fonts and map data are not part of this repo; they are downloaded on the first run.
DOWNLOADS = HERE / "downloads"
GOOGLE_FONTS = "https://raw.githubusercontent.com/google/fonts/main/ofl"
SOURCES = {
    "DancingScript.ttf": f"{GOOGLE_FONTS}/dancingscript/DancingScript%5Bwght%5D.ttf",       # SIL OFL
    "Roboto.ttf": f"{GOOGLE_FONTS}/roboto/Roboto%5Bwdth,wght%5D.ttf",                      # SIL OFL
    "ne_50m_land.geojson": "https://raw.githubusercontent.com/nvkelso/natural-earth-vector/"
                           "master/geojson/ne_50m_land.geojson",                           # public domain
}


def fetch(name):
    """Local path of a downloaded source file, downloading it if needed."""
    path = DOWNLOADS / name
    if not path.exists():
        print(f"downloading {SOURCES[name]}")
        DOWNLOADS.mkdir(exist_ok=True)
        tmp = path.with_suffix(".part")
        urllib.request.urlretrieve(SOURCES[name], tmp)
        tmp.rename(path)
    return path


DANCING = fetch("DancingScript.ttf")
ROBOTO = fetch("Roboto.ttf")

HOLES = [(x, y) for x in (HOLE_INSET, W - HOLE_INSET) for y in (HOLE_INSET, H - HOLE_INSET)]


# --- Geometry helpers ----------------------------------------------------------------
def polys(geom):
    if geom.is_empty:
        return []
    return list(geom.geoms) if hasattr(geom, "geoms") else [geom]


def rings_of(geom):
    for p in polys(geom):
        yield p.exterior.coords
        yield from (i.coords for i in p.interiors)


def to_path(coords):
    pts = list(coords)
    return "M " + " L ".join(f"{x:.3f},{y:.3f}" for x, y in pts[:-1]) + " Z"


def hatch(geom, spacing=HATCH_SPACING):
    """Fill polygons with horizontal engrave lines."""
    if geom.is_empty:
        return []
    x0, y0, x1, y1 = geom.bounds
    lines, y = [], y0 + spacing / 2
    while y < y1:
        cut = geom.intersection(LineString([(x0 - 1, y), (x1 + 1, y)]))
        for seg in (cut.geoms if hasattr(cut, "geoms") else [cut]):
            if isinstance(seg, LineString) and seg.length > 0.05:
                (a, _), (b, _) = seg.coords[0], seg.coords[-1]
                lines.append(f"M {a:.3f},{y:.3f} H {b:.3f}")
        y += spacing
    return lines


# --- Text -------------------------------------------------------------------------------
class OutlinePen:
    """Collects glyph outlines as flattened point lists (font units)."""

    def __init__(self, steps=8):
        self.steps, self.contours, self.cur = steps, [], []

    def moveTo(self, p):
        self.cur = [p]

    def lineTo(self, p):
        self.cur.append(p)

    def qCurveTo(self, c, p):
        (x0, y0), (cx, cy), (x1, y1) = self.cur[-1], c, p
        for i in range(1, self.steps + 1):
            t = i / self.steps
            u = 1 - t
            self.cur.append((u * u * x0 + 2 * u * t * cx + t * t * x1,
                             u * u * y0 + 2 * u * t * cy + t * t * y1))

    def curveTo(self, c1, c2, p):
        (x0, y0), (ax, ay), (bx, by), (x1, y1) = self.cur[-1], c1, c2, p
        for i in range(1, self.steps + 1):
            t = i / self.steps
            u = 1 - t
            self.cur.append((u**3 * x0 + 3 * u * u * t * ax + 3 * u * t * t * bx + t**3 * x1,
                             u**3 * y0 + 3 * u * u * t * ay + 3 * u * t * t * by + t**3 * y1))

    def closePath(self):
        if len(self.cur) > 2:
            self.contours.append(self.cur)
        self.cur = []

    endPath = closePath


def glyph_shape(contours):
    """Non-zero fill: outer contours (clockwise in TrueType) minus the holes inside them."""
    outer, holes = [], []
    for c in contours:
        p = Polygon(c).buffer(0)
        if p.is_empty:
            continue
        area = sum((x0 * y1 - x1 * y0) for (x0, y0), (x1, y1) in zip(c, c[1:] + c[:1]))
        (outer if area < 0 else holes).append(p)
    return unary_union([o.difference(unary_union([h for h in holes if o.contains(h.representative_point())]))
                        for o in outer])


def text_shape(text, font_path, size, cx, baseline, variations=None, max_width=None):
    """Shaped text as a shapely geometry in page mm, centred on cx. size = em size in mm.
    Text wider than max_width is scaled down to fit."""
    blob = hb.Blob.from_file_path(str(font_path))
    font = hb.Font(hb.Face(blob))
    if variations:
        font.set_variations(variations)
    buf = hb.Buffer()
    buf.add_str(text)
    buf.guess_segment_properties()
    hb.shape(font, buf)
    pieces, x = [], 0
    for info, pos in zip(buf.glyph_infos, buf.glyph_positions):
        pen = OutlinePen()
        font.draw_glyph_with_pen(info.codepoint, pen)
        g = glyph_shape(pen.contours)
        pieces.append(affinity.translate(g, x + pos.x_offset, pos.y_offset))
        x += pos.x_advance
    s = size / font.face.upem
    if max_width and x * s > max_width:
        s = max_width / x
    geom = affinity.scale(unary_union(pieces), s, -s, origin=(0, 0))
    return affinity.translate(geom, cx - x * s / 2, baseline)


# --- Map ----------------------------------------------------------------------------------
def world_map():
    """Land masses to cut out, in page mm (Equal Earth)."""
    to_ee = pyproj.Transformer.from_crs("EPSG:4326", f"+proj=eqearth +lon_0={CENTER_LON:g}", always_xy=True)
    land = []
    for f in json.loads(fetch("ne_50m_land.geojson").read_text())["features"]:
        for p in polys(shape(f["geometry"])):
            if p.bounds[3] < -60:            # no Antarctica
                continue
            lons, lats = zip(*p.exterior.coords)               # interiors would be loose wood
            if p.centroid.x < CENTER_LON - 180:                 # e.g. Chukotka: move to the right edge
                lons = [lon + 360 for lon in lons]
            xs, ys = to_ee.transform(lons, lats)
            land.append(Polygon(zip(xs, ys)).buffer(0))
    land = unary_union(land)
    # fit the map to the big land masses; Pacific specks would only shrink it
    x0, y0, x1, y1 = unary_union([p for p in polys(land) if p.area > 5e10]).bounds
    s = MAP_W / (x1 - x0)
    land = affinity.scale(land, s, -s, origin=(0, 0))
    land = affinity.translate(land, (W - MAP_W) / 2 + MAP_DX - x0 * s, MAP_TOP + y1 * s)

    land = enforce_min_wood(land)

    cut = [p for p in polys(land) if p.area >= MIN_CUT_AREA]
    cut = MultiPolygon([Polygon(p.exterior) for p in cut])
    return cut


def enforce_min_wood(land):
    """Make sure no wood between the cut-outs is thinner than MIN_WOOD.

    Thin sea is either an inlet (fjord, bay of one land mass: filled, it becomes part of
    the cut-out) or a strait between two land masses or between two seas (Channel,
    Gibraltar, Bosporus, Red Sea: widened into the land, so it stays as a wood bridge
    and no sea is left floating loose)."""
    r = MIN_WOOD / 2
    sheet = box(-5, -5, W + 5, H + 5)
    for _ in range(int(r / WIDEN_STEP) + 2):
        wood = sheet.difference(land)
        seas = polys(wood.buffer(-r).buffer(r))
        thin = [t for t in polys(wood.difference(unary_union(seas)).buffer(-0.01).buffer(0.01))
                if t.area > 0.001]
        lands = polys(land)
        fill, widen = [], []
        for t in thin:
            g = t.buffer(0.02)
            n_land = sum(1 for p in lands if g.intersects(p))
            n_sea = sum(1 for q in seas if g.intersects(q))
            (widen if n_land >= 2 or n_sea >= 2 else fill).append(t)
        if not widen and not fill:
            break
        land = unary_union([land] + [t.buffer(0.02) for t in fill])
        if widen:
            land = land.difference(unary_union(widen).buffer(WIDEN_STEP))
    # enclosed sea left over would fall out as loose wood: fill it
    return unary_union([Polygon(p.exterior) for p in polys(land)]).buffer(-0.05).buffer(0.05)


# --- Compass rose --------------------------------------------------------------------------
def compass(cx, cy, r):
    """8-point star; one half of every point is filled, letters N/O/S/W (German)."""
    filled, outline = [], []
    for k in range(8):
        a = math.radians(k * 45)
        length = r if k % 2 == 0 else r * 0.55
        w = r * 0.14
        tip = (cx + length * math.sin(a), cy - length * math.cos(a))
        left = (cx + w * math.sin(a - math.pi / 2), cy - w * math.cos(a - math.pi / 2))
        right = (cx + w * math.sin(a + math.pi / 2), cy - w * math.cos(a + math.pi / 2))
        filled.append(Polygon([(cx, cy), tip, right]))
        outline.append(Polygon([(cx, cy), left, tip, right]))
    letters = []
    for text, a in (("N", 0), ("O", 90), ("S", 180), ("W", 270)):
        d = r + 2.6
        lx, ly = cx + d * math.sin(math.radians(a)), cy - d * math.cos(math.radians(a))
        letters.append(text_shape(text, ROBOTO, 3.4, lx, ly + 1.2, {"wght": 400}))
    return unary_union(outline), unary_union(filled), unary_union(letters)


# --- Panels ---------------------------------------------------------------------------------
def rounded_rect(x, y, w, h, r):
    k = 0.5523 * r
    return (f"M {x + r:.3f},{y:.3f} H {x + w - r:.3f} "
            f"C {x + w - r + k:.3f},{y:.3f} {x + w:.3f},{y + r - k:.3f} {x + w:.3f},{y + r:.3f} "
            f"V {y + h - r:.3f} "
            f"C {x + w:.3f},{y + h - r + k:.3f} {x + w - r + k:.3f},{y + h:.3f} {x + w - r:.3f},{y + h:.3f} "
            f"H {x + r:.3f} "
            f"C {x + r - k:.3f},{y + h:.3f} {x:.3f},{y + h - r + k:.3f} {x:.3f},{y + h - r:.3f} "
            f"V {y + r:.3f} "
            f"C {x:.3f},{y + r - k:.3f} {x + r - k:.3f},{y:.3f} {x + r:.3f},{y:.3f} Z")


def panel_cut(dx, dy):
    out = [f'    <path style="{CUT}" d="{rounded_rect(dx, dy, W, H, CORNER_R)}" />']
    out += [f'    <circle style="{CUT}" cx="{x + dx:.3f}" cy="{y + dy:.3f}" r="{HOLE_D / 2:g}" />'
            for x, y in HOLES]
    return out


def front_engravings(phrase, names, date):
    """All engraved shapes of the front board, as (name, geometry, filled)."""
    side = HOLE_INSET + HOLE_D / 2 + 4                  # keep clear of the cord holes
    beside_compass = 2 * (W / 2 - COMPASS_X - COMPASS_R - 8)
    items = [("phrase", text_shape(phrase, DANCING, 13.0, W / 2, 19.5, {"wght": 500}, W - 2 * side), True),
             ("names", text_shape(names, DANCING, 14.0, W / 2, 130.0, {"wght": 600}, beside_compass), True)]
    if date:
        items.append(("date", text_shape(date, ROBOTO, 5.0, W / 2, 139.5, {"wght": 300}, beside_compass), True))
    star, star_fill, letters = compass(COMPASS_X, COMPASS_Y, COMPASS_R)
    items += [("compass", star, False), ("compass-fill", star_fill, True), ("compass-letters", letters, True)]
    return items


def svg_doc(title, body):
    return f"""<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<!-- {title}. Generated by make_gift.py -->
<svg width="{W:g}mm" height="{H:g}mm" viewBox="0 0 {W:g} {H:g}" version="1.1"
   xmlns="http://www.w3.org/2000/svg">
{chr(10).join(body)}
</svg>
"""


def geom_path(geom, style):
    d = " ".join(to_path(r) for r in rings_of(geom))
    return f'  <path style="{style}" fill-rule="evenodd" d="{d}" />'


def preview(land_cut, engravings):
    """Coloured picture of the finished front board (for the README), not for the laser."""
    body = [f'  <path style="fill:#e3c79a;stroke:#a87b4f;stroke-width:0.4" d="{rounded_rect(0, 0, W, H, CORNER_R)}" />',
            geom_path(land_cut, "fill:#6f8f72;stroke:#3d2a1a;stroke-width:0.25")]
    body += [f'  <circle style="fill:#ffffff;stroke:#3d2a1a;stroke-width:0.25" cx="{x:g}" cy="{y:g}" r="{HOLE_D / 2:g}" />'
             for x, y in HOLES]
    for _, geom, filled in engravings:
        style = "fill:#7a4b25" if filled else "fill:none;stroke:#7a4b25;stroke-width:0.25"
        body.append(geom_path(geom, style))
    return body


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--names", default=NAMES, help=f'names engraved under the map (default: "{NAMES}")')
    ap.add_argument("--date", help='date engraved under the names, e.g. "12. Juni 2027" (default: none)')
    ap.add_argument("--phrase", default=PHRASE, help=f'line above the map (default: "{PHRASE}")')
    ap.add_argument("--out", type=Path, default=HERE / "output", help="output directory (default: output/)")
    args = ap.parse_args()

    land_cut = world_map()
    keep_out = unary_union([land_cut.buffer(CLEARANCE)] +
                           [Point(p).buffer(HOLE_D / 2 + 2) for p in HOLES])

    engravings = front_engravings(args.phrase, args.names, args.date)
    for name, geom, _ in engravings:
        clash = geom.intersection(keep_out)
        if clash.area > 0.01:
            raise SystemExit(f"{name} runs into the map or a cord hole ({clash.area:.2f} mm²)")

    front = []
    engrave = lambda d: f'    <path style="{ENGRAVE}" d="{d}" />'
    for name, geom, filled in engravings:
        front.append(f'  <g id="engrave-{name}">')
        front += [engrave(to_path(r)) for r in rings_of(geom)]
        if filled:
            front.append(engrave(" ".join(hatch(geom))))
        front.append("  </g>")
    cut_front = panel_cut(0, 0) + [f'    <path style="{CUT}" d="{to_path(p.exterior.coords)}" />'
                                   for p in polys(land_cut)]

    title = f"Wedding money gift for {args.names}"
    files = {
        "front_3mm.svg": svg_doc(f"{title}, front board. red = cut, blue = engrave, 3 mm plywood",
                                 front + ['  <g id="cut">', *cut_front, "  </g>"]),
        "back_3mm.svg": svg_doc(f"{title}, back board. red = cut, 3 mm plywood",
                                ['  <g id="cut">', *panel_cut(0, 0), "  </g>"]),
        "preview.svg": svg_doc(f"{title}, preview of the finished front board", preview(land_cut, engravings)),
    }
    args.out.mkdir(parents=True, exist_ok=True)
    for name, svg in files.items():
        (args.out / name).write_text(svg)
        print(f"wrote {args.out / name}")


if __name__ == "__main__":
    main()
