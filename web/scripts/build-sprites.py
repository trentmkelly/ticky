#!/usr/bin/env python3
"""Slices the entity graphics the circuit view draws out of a Factorio install.

usage: web/scripts/build-sprites.py [FACTORIO_DATA_DIR]
  (default: ~/.local/share/Steam/steamapps/common/Factorio/data)

Writes web/public/sprites/: one PNG per sheet, cropped to the frames used, and sprites.json
with where each frame goes. Positions are in tiles relative to the entity's centre, read from
the game's own prototype definitions (sprite shifts, display symbols and wire connection
points), so the pictures sit as they do in game. The output is checked in; CI doesn't need the
game. Graphics © Wube Software, used as fan content.
"""
import json
import os
import re
import sys

from PIL import Image

DATA = sys.argv[1] if len(sys.argv) > 1 else os.path.expanduser("~/.local/share/Steam/steamapps/common/Factorio/data")
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "public", "sprites")
TILE = 32  # `util.by_pixel` units per tile
DIRS = ["north", "east", "south", "west"]


# --- A reader for the Lua tables in prototype files ---------------------------------------

TOKEN = re.compile(r"""\s*(?:--\[\[.*?\]\]|--[^\n]*|(?P<tok>"(?:[^"\\]|\\.)*"|'[^']*'|\d+(?:\.\d+)?|[A-Za-z_][\w.:]*|\S))""", re.S)
NUMBER = re.compile(r"\d+(\.\d+)?")


class Reader:
    """Parses one Lua value: tables, numbers, strings, `util.by_pixel(x, y)` (→ tiles) and
    wrappers like `util.draw_as_glow{...}` (→ the table). Other calls and names are None."""

    def __init__(self, src, pos):
        self.src, self.pos = src, pos
        self.buf = []

    def peek(self, k=0):
        while len(self.buf) <= k:
            m = TOKEN.match(self.src, self.pos)
            if not m:
                return None
            self.pos = m.end()
            if m.group("tok") is not None:
                self.buf.append(m.group("tok"))
        return self.buf[k]

    def take(self):
        self.peek()
        return self.buf.pop(0)

    def value(self):
        t = self.take()
        if t == "{":
            return self.table()
        if t == "-":
            return -self.value()
        if t[0] in "\"'":
            return t[1:-1]
        if NUMBER.fullmatch(t):
            x = float(t)
            while self.peek() in ("+", "-") and NUMBER.fullmatch(self.peek(1) or ""):  # 34+3
                sign = 1 if self.take() == "+" else -1
                x += sign * float(self.take())
            return x
        if t in ("true", "false"):
            return t == "true"
        if self.peek() == "{":  # f{...}
            self.take()
            return self.table()
        if self.peek() != "(":
            return None
        self.take()
        args = []
        while self.peek() != ")":
            args.append(self.value())
            if self.peek() == ",":
                self.take()
        self.take()
        if t == "util.by_pixel":
            return [args[0] / TILE, args[1] / TILE]
        if t == "util.by_pixel_hr":
            return [args[0] / (2 * TILE), args[1] / (2 * TILE)]
        return args[0] if len(args) == 1 and isinstance(args[0], (dict, list)) else None

    def table(self):
        items, named = [], {}
        while self.peek() != "}":
            if self.peek(1) == "=" and re.fullmatch(r"\w+", self.peek()):
                key = self.take()
                self.take()
                named[key] = self.value()
            else:
                items.append(self.value())
            if self.peek() in (",", ";"):
                self.take()
        self.take()
        if named and items:
            named["_items"] = items
        return named if named else items


def read(path, key, start=0):
    """The value assigned to `key` (e.g. `combinator.sprites`) at or after offset `start`."""
    with open(path, encoding="utf-8") as fh:
        src = fh.read()
    m = re.compile(re.escape(key) + r"\s*=").search(src, start)
    if not m:
        raise SystemExit(f"{key} not found in {path}")
    return Reader(src, m.end()).value()


def offset(path, needle):
    with open(path, encoding="utf-8") as fh:
        return fh.read().index(needle)


# --- Building the sheets --------------------------------------------------------------------

def image(filename):
    return Image.open(filename.replace("__base__", os.path.join(DATA, "base")).replace("__core__", os.path.join(DATA, "core"))).convert("RGBA")


sheets = {}  # file name in public/sprites → image
frames = {}  # key → {file, x, y, w, h, dx, dy, dw, dh}: source rect and where it lands (tiles)


def add(key, layer, x=None, y=None, frame=0):
    """One frame of a sprite layer; sheets are kept whole and named after the game's file."""
    name = os.path.basename(layer["filename"])
    if name not in sheets:
        sheets[name] = image(layer["filename"])
    w, h = int(layer["width"]), int(layer["height"])
    sx = int(layer.get("x", 0) if x is None else x) + frame * w
    sy = int(layer.get("y", 0) if y is None else y)
    scale = layer.get("scale", 1)
    shift = layer.get("shift") or [0, 0]
    dw, dh = w * scale / TILE, h * scale / TILE  # scale 0.5: 64 px per tile
    frames[key] = {"file": name, "x": sx, "y": sy, "w": w, "h": h,
                   "dx": shift[0] - dw / 2, "dy": shift[1] - dh / 2, "dw": dw, "dh": dh}


ENT = os.path.join(DATA, "base", "prototypes", "entity")
PICS = os.path.join(ENT, "combinator-pictures.lua")
connections = {}

SYMBOLS = {
    "arithmetic": ["plus", "minus", "multiply", "divide", "modulo", "power", "left_shift", "right_shift", "and", "or", "xor"],
    "decider": ["greater", "less", "equal", "not_equal", "less_or_equal", "greater_or_equal"],
    "constant": [],
    "selector": ["max", "min", "count", "random", "quality", "stack_size", "rocket_capacity"],
}
for kind, symbols in SYMBOLS.items():
    at = offset(PICS, f"function generate_{kind}_combinator")
    body, shadow = read(PICS, "combinator.sprites", at)["layers"]
    for d in range(4):
        add(f"{kind}-combinator/{d}", body, frame=d)
        add(f"{kind}-combinator/{d}/shadow", shadow, frame=d)
    for sym in symbols:
        name = f"combinator.{sym}_symbol_sprites" if sym not in ("stack_size", "rocket_capacity") else f"combinator.{sym}_sprites"
        table = read(PICS, name, at)
        for d, dname in enumerate(DIRS):
            add(f"{kind}-combinator/{d}/{sym}", table[dname])
    if kind == "constant":
        pts = read(PICS, "combinator.circuit_wire_connection_points", at)
        connections[f"{kind}-combinator"] = {"": [p["wire"] for p in pts]}
    else:
        connections[f"{kind}-combinator"] = {
            "in": [p["wire"] for p in read(PICS, "combinator.input_connection_points", at)],
            "out": [p["wire"] for p in read(PICS, "combinator.output_connection_points", at)],
        }

ENTITIES = os.path.join(ENT, "entities.lua")
at = offset(ENTITIES, 'name = "medium-electric-pole"')
pole = read(ENTITIES, "pictures", at)["layers"]
add("medium-electric-pole/0", pole[0])
add("medium-electric-pole/0/shadow", pole[1])
connections["medium-electric-pole"] = {"": [read(ENTITIES, "connection_points", at)[0]["wire"]] * 4}

at = offset(ENTITIES, 'name = "small-lamp"')
lamp = read(ENTITIES, "picture_off", at)["layers"]
add("small-lamp/0", lamp[0])
add("small-lamp/0/shadow", lamp[1])

CN = os.path.join(ENT, "circuit-network.lua")
at = offset(CN, 'name = "programmable-speaker"')
speaker = read(CN, "sprite", at)["layers"]
add("programmable-speaker/0", speaker[0])
add("programmable-speaker/0/shadow", speaker[1])

at = offset(CN, 'name = "display-panel"')
panel = read(CN, "sprites", at)["layers"]
for d in range(4):
    add(f"display-panel/{d}", panel[0], frame=d)
    add(f"display-panel/{d}/shadow", panel[1], frame=d)
connections["display-panel"] = {"": [p["points"]["wire"] for p in read(CN, "circuit_connector", at)]}

# Crop each sheet to the frames used.
os.makedirs(OUT, exist_ok=True)
for name, im in sheets.items():
    used = [f for f in frames.values() if f["file"] == name]
    x0, y0 = min(f["x"] for f in used), min(f["y"] for f in used)
    x1, y1 = max(f["x"] + f["w"] for f in used), max(f["y"] + f["h"] for f in used)
    im.crop((x0, y0, x1, y1)).save(os.path.join(OUT, name), optimize=True)
    for f in used:
        f["x"] -= x0
        f["y"] -= y0
with open(os.path.join(OUT, "sprites.json"), "w", encoding="utf-8") as fh:
    json.dump({"frames": frames, "connections": connections}, fh, separators=(",", ":"))
total = sum(os.path.getsize(os.path.join(OUT, n)) for n in os.listdir(OUT))
print(f"{len(frames)} frames from {len(sheets)} sheets, {total // 1024} KiB in {os.path.relpath(OUT)}")
