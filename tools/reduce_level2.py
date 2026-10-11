#!/usr/bin/env python3
"""Shrinks a failing tools/fuzz_level2.py program: removes statements and replaces
expressions with a child or 0/1 while Ticky still disagrees with Python.

usage: tools/reduce_level2.py PROGRAM.ticky X Y      (TICKY=./target/debug/ticky)
Prints the reduced program; the last candidate is left in /tmp/reduce-cur.ticky (or REDUCE_CUR).
With REDUCE_ERROR=TEXT, shrinks a compile failure instead: keeps candidates (that Python
still runs) whose compile error contains TEXT.
"""
import ast
import copy
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fuzz_level2 import run_python  # pylint: disable=wrong-import-position

T = os.environ.get("TICKY", "./target/debug/ticky")
path, x, y = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
lines = open(path).read().splitlines()
head = [l for l in lines if l.startswith(('input', 'output'))]
# An `every` program (fuzz_level2's 30%): reduce its block's body, written back indented.
EVERY = next((l for l in lines if l.startswith('every ')), None)
if EVERY:
    head.append(EVERY)
    lines = [l[4:] if l.startswith('    ') else l for l in lines if l != EVERY]
tail = [l for l in lines if re.match(r'^(o\d = |done = )', l)]
body = "\n".join(l for l in lines if l not in head and l not in tail)

def legal(src):
    try:
        ast.parse(src)
    except SyntaxError:
        return False
    for n in ast.walk(ast.parse(src)):
        if isinstance(n, ast.Subscript):
            sl = n.slice
            if isinstance(sl, ast.Constant) or (isinstance(sl, ast.UnaryOp) and isinstance(sl.operand, ast.Constant)):
                continue
            if not (isinstance(sl, ast.BinOp) and isinstance(sl.op, ast.Mod) and isinstance(sl.right, ast.Constant) and sl.right.value == 4):
                return False
    return True

ERROR = os.environ.get("REDUCE_ERROR")
CUR = os.environ.get("REDUCE_CUR", "/tmp/reduce-cur.ticky")

def program(b):
    """The full program around body lines `b`."""
    if EVERY:
        return "\n".join(head + ["    " + l for l in b + tail]) + "\n"
    return "\n".join(head + b + tail) + "\n"

def bad(src):
    if not legal(src):
        return False
    if ERROR:
        # Still a valid program: Python runs it.
        try:
            if run_python([f"x = {x}", f"y = {y}"] + src.splitlines()) is None:
                return False
        except Exception:
            return False
        open(CUR, 'w').write(program(src.splitlines()))
        out = subprocess.run([T, 'check', CUR], capture_output=True, text=True)
        return ERROR in out.stderr
    b = src.splitlines()
    try:
        want = run_python([f"x = {x}", f"y = {y}"] + b)
    except Exception:
        return False
    if want is None:
        return False
    open(CUR, 'w').write(program(b))
    out = subprocess.run([T, 'sim', CUR, '--ticks', '30000', f'--set=x={x}', f'--set=y={y}'], capture_output=True, text=True)
    if out.returncode != 0:
        return False
    last = [int(v) for v in out.stdout.strip().splitlines()[-1].split()[1:]]
    return tuple(last[:7]) != want

def variants(tree):
    """Yield modified copies: each expression node replaced by a child or 0/1; statements removed."""
    nodes = [n for n in ast.walk(tree)]
    for i, n in enumerate(nodes):
        if isinstance(n, ast.expr) and not isinstance(n, (ast.Name, ast.Constant)):
            subs = [c for c in ast.iter_child_nodes(n) if isinstance(c, ast.expr)] + [ast.Constant(0), ast.Constant(1)]
            for s in subs:
                t2 = copy.deepcopy(tree)
                target = [m for m in ast.walk(t2)][i]
                for parent in ast.walk(t2):
                    for field, val in ast.iter_fields(parent):
                        if val is target:
                            setattr(parent, field, copy.deepcopy(s) if not isinstance(s, ast.Constant) else ast.Constant(s.value))
                            yield t2
                        elif isinstance(val, list) and any(v is target for v in val):
                            setattr(parent, field, [copy.deepcopy(s) if v is target else v for v in val])
                            yield t2

src = ast.unparse(ast.parse(body))
assert bad(src), "not reproducible after unparse"
changed = True
while changed:
    changed = False
    # statements
    ls = src.splitlines()
    for i in range(len(ls)):
        if i < len(ls):
            cand = "\n".join(ls[:i] + ls[i+1:])
            if bad(cand):
                ls = cand.splitlines(); src = cand; changed = True
    for v in variants(ast.parse(src)):
        cand = ast.unparse(v)
        if len(cand) < len(src) and bad(cand):
            src = cand; changed = True
            break
print(src)
bad(src)
if not ERROR:
    print("python:", run_python([f"x = {x}", f"y = {y}"] + src.splitlines()))
