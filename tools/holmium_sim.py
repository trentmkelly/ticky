"""Time-stepped model of the holmium factory under examples/holmium-generator.ticky's policy.

Machines take a craft's inputs from stock when their group is enabled (the belt is left out:
anything released comes back), fluids are capped per tank, jelly rots into destabilized
matter and then dream, and cubes rot both ways. `policy` mirrors the .ticky by hand; keep
them in step.
usage: python3 tools/holmium_sim.py [hours] [plants] [starting cubes per plant]
"""
import sys
from collections import deque

from holmium_econ import R as ECON

# Group letter -> recipe in holmium_econ.R (the controller's groups A..U). holmium_econ lists
# the charged cubes a recipe uses or makes but not the dormant ones it gives back or takes:
# those are added here.
CUBE_USE = {'holmium': 10, 'cu-ore': 1, 'fe-ore': 1, 'amplify': 1, 'reconst': 1, 'sf-hope': 1,
            'jelly': 1}
CUBE_CHARGE = {'aggravate': 1, 'hope-spoil': 1, 'sf-massage': 1, 'steam-bath': 1}
GROUPS = dict(zip('ABCDEFGHIJKLMNOPQRSTUV', [
    'holmium', 'cu-ore', 'fe-ore', 'amplify', 'aggravate', 'smelt-cu', 'smelt-fe', 'steel',
    'awaken', 'fear-inv', 'anger-crk', 'reconst', 'emo-crk', 'tar', 'dream-conc', 'liq-dream',
    'hope-spoil', 'sf-hope', 'sf-massage', 'steam-bath', 'jelly', 'rot']))
RECIPES = dict(ECON)
RECIPES['jelly'] = (1, {}, {'j': 2})
RECIPES['rot'] = (480, {'j': 10}, {'dream': 10})   # the rot chest, 10 jelly per "machine"
FLUIDS = {'dc', 'ld', 'hope', 'fear', 'courage', 'anger', 'hate', 'disgust', 'tar', 'oil',
          'water', 'steam'}
TANK = 25000
SPEED = {'smelt-cu': 2, 'smelt-fe': 2, 'steel': 2}  # electric furnaces; the rest speed 1


def machines(plants):
    """Machines per group, from the steady-state ratios with some headroom."""
    from holmium_econ import solve  # pylint: disable=import-outside-toplevel
    runs = solve()
    out = {}
    for g, r in GROUPS.items():
        if r in ('jelly', 'rot'):
            out[g] = 1 if r == 'jelly' else 2000
            continue
        per_s = runs[r] * plants / 120          # runs per second for `plants` holmium plants
        out[g] = max(1, round(per_s * RECIPES[r][0] / SPEED.get(r, 1) * 1.3 + 0.49))
    out['A'] = plants
    return out


def policy(st, plants):
    """The controller: which groups run. Mirrors holmium-generator.ticky."""
    g = st.get
    reserve = 10 * plants
    spare = g('e', 0) > reserve
    owed = g('cu', 0) + g('cuore', 0) - 2 * g('d', 0)
    dreaming = g('dream', 0) + g('destab', 0) + g('rotting', 0)
    want_v = dreaming < 600 * plants
    jelly_goal = 50 * plants + 200 + (200 * plants if want_v else 0)
    full = 20000
    e, j = g('e', 0), g('j', 0)
    steel, fe = g('steel', 0), g('fe', 0)
    hope, disgust = g('hope', 0), g('disgust', 0)
    inv, courage, fear = g('inv', 0), g('courage', 0), g('fear', 0)
    want = {
        'A': (True, steel >= 50 and e >= 10 and inv >= 12 and j >= 50 and g('dc', 0) >= 350
              and hope >= 550),
        'B': (owed < 200, e >= 1 and j >= 50 + (50 * plants if spare else 0)),
        'C': (steel + (fe + g('feore', 0)) // 5 < 100 * plants and owed >= 200,
              spare and j >= 50 + 50 * plants),
        'D': (j < jelly_goal, j >= 10 and (spare or (j < 50 and e >= 1))),
        'E': (g('d', 0) > 10, g('cu', 0) >= 2),
        'F': (g('cu', 0) < 2000, g('cuore', 0) > 0),
        'G': (fe < 1000, g('feore', 0) > 0),
        'H': (steel < 100 * plants, fe >= 5),
        'I': (inv < 20 * plants, g('invd', 0) >= 1 and fear >= 100 and courage >= 100),
        'J': (courage < 3000, inv >= 1 and fear >= 1000),
        'K': (fear < full and g('hate', 0) < full, g('ld', 0) >= 50 and g('anger', 0) >= 100),
        'L': (g('anger', 0) < full, (spare or g('hate', 0) > 10000) and e >= 1
                                    and disgust >= 700 and g('hate', 0) >= 1000),
        'M': (hope < full and g('anger', 0) < 15000 and disgust < full,
              g('tar', 0) >= 100 and g('water', 0) >= 35),
        'N': (g('tar', 0) < full, g('oil', 0) >= 35 and g('dc', 0) >= 35 + 350 * plants),
        'O': (g('dc', 0) < 1000 * plants, g('ld', 0) >= 1100),
        'P': (g('ld', 0) < full, g('dream', 0) >= 3 and g('water', 0) >= 200),
        'Q': (hope > 10000 or disgust > 10000,
              g('d', 0) >= 1 and disgust >= 2000 and hope >= 600 + 550 * plants),
        'R': (hope > 10000 and g('sf', 0) < 200, spare and g('ld', 0) >= 150),
        'S': (g('sf', 0) >= 20, g('d', 0) >= 1),
        'T': (g('steam', 0) >= 500, g('d', 0) >= 1),
        'U': (j < 10, e >= 1),
        'V': (want_v, j >= 50 + 50 * plants),
    }
    return {k for k, (w, h) in want.items() if w and h}


def run(hours=4.0, plants=4, seed=None, log=600, cubes=50):
    """Simulate; returns (holmium made, history of stocks every `log` seconds)."""
    st = {'e': cubes * plants, 'inv': 30 * plants, 'water': 10**9, 'oil': 10**9}
    st.update(seed or {})
    jelly = deque()      # (time made, count): rots after 180 s
    destab = deque()     # rots after 300 s
    n = machines(plants)
    busy = {g: [] for g in GROUPS}   # finish times of crafts in progress
    made, hist = 0, []
    on = set()
    use = {g: 0 for g in GROUPS}      # machine-seconds busy
    for t in range(int(hours * 3600)):
        # Rot.
        while jelly and jelly[0][0] <= t - 180:
            _, c = jelly.popleft()
            st['j'] -= c
            destab.append((t, c))
            st['destab'] = st.get('destab', 0) + c
        while destab and destab[0][0] <= t - 300:
            _, c = destab.popleft()
            st['destab'] -= c
            st['dream'] = st.get('dream', 0) + c
        for a, b, life in (('e', 'd', 1800), ('d', 'e', 3600)):
            k = st.get(a, 0) // life + (1 if t % life < st.get(a, 0) % life else 0)
            st[a] = st.get(a, 0) - k
            st[b] = st.get(b, 0) + k
        # Finish crafts.
        for g, r in GROUPS.items():
            done = [x for x in busy[g] if x <= t]
            busy[g] = [x for x in busy[g] if x > t]
            for _ in done:
                _, _, outs = RECIPES[r]
                for k, v in outs.items():
                    if k == 'j':
                        jelly.append((t, v))
                    if k == 'ho':
                        made += v
                    st[k] = st.get(k, 0) + v
                st['d'] = st.get('d', 0) + CUBE_USE.get(r, 0)
                if r == 'rot':
                    st['rotting'] -= 10
                if r == 'holmium':
                    st['invd'] = st.get('invd', 0) + 10
                if r == 'fear-inv':
                    st['invd'] = st.get('invd', 0) + 1
        on = policy(st, plants)
        for g in GROUPS:
            use[g] += len(busy[g])
        # Start crafts.
        for g in sorted(on):
            r = GROUPS[g]
            _, ins, outs = RECIPES[r]
            ins = dict(ins)
            if r == 'jelly':
                ins['e'] = 1
            if CUBE_CHARGE.get(r):
                ins['d'] = ins.get('d', 0) + CUBE_CHARGE[r]
            if r == 'awaken':
                ins['invd'] = 1
            while len(busy[g]) < n[g]:
                if any(st.get(k, 0) < v for k, v in ins.items()):
                    break
                if any(k in FLUIDS and st.get(k, 0) + v > TANK for k, v in outs.items()):
                    break
                for k, v in ins.items():
                    st[k] -= v
                    if k == 'j':
                        take(jelly, v)
                if r == 'rot':
                    st['rotting'] = st.get('rotting', 0) + 10
                busy[g].append(t + RECIPES[r][0] / SPEED.get(r, 1))
        if log and t % log == 0:
            hist.append((t, made, {k: v for k, v in st.items() if k not in ('water', 'oil') and v}))
    secs = hours * 3600
    run.use = {g: round(use[g] / (secs * n[g]), 2) for g in GROUPS}
    return made, hist


def take(q, v):
    """Take v jelly, oldest first."""
    while v > 0 and q:
        t, c = q[0]
        if c <= v:
            q.popleft()
            v -= c
        else:
            q[0] = (t, c - v)
            v = 0


def main():
    """Simulate and print stocks over time."""
    hours = float(sys.argv[1]) if len(sys.argv) > 1 else 4
    plants = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    cubes = int(sys.argv[3]) if len(sys.argv) > 3 else 50
    print('machines:', machines(plants))
    made, hist = run(hours, plants, cubes=cubes)
    for t, m, s in hist:
        print(f'{t / 60:6.0f} min  holmium {m:6}  ', s)
    ideal = 20 * plants * hours * 3600 / 120
    print('utilisation:', run.use)
    print(f'holmium: {made} in {hours} h ({made / ideal:.0%} of {plants} plants flat out)')


if __name__ == '__main__':
    main()
