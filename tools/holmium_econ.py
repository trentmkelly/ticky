# Steady-state model of the Cubium holmium factory (examples/holmium-generator.ticky): how many
# runs of each recipe one "Holmium plate ex Dream" craft needs, with everything made in the
# loop except water and light oil. Cubes are conserved (every recipe returns the cube it
# uses, charged or not), so only energized and inverted cubes are balanced; the dormant kinds
# follow. Dream is jelly left to rot (3 + 5 minutes). Passive cube recovery (dormant ->
# energized after 60 min) isn't counted: it only makes things cheaper.
# usage: python3 tools/holmium_econ.py
import numpy as np

R = {  # name: (time s at speed 1, ingredients, products)
    'holmium':   (120, {'steel': 50, 'e': 10, 'inv': 10, 'j': 50, 'dc': 350, 'hope': 550},
                  {'ho': 20}),
    'cu-ore':    (9, {'e': 1, 'j': 50}, {'cuore': 41}),
    'fe-ore':    (10, {'e': 1, 'j': 50}, {'feore': 41}),
    'amplify':   (3, {'e': 1, 'j': 10}, {'j': 17}),
    'aggravate': (10, {'cu': 2}, {'e': 1}),
    'smelt-cu':  (3.2, {'cuore': 1}, {'cu': 1}),
    'smelt-fe':  (3.2, {'feore': 1}, {'fe': 1}),
    'steel':     (16, {'fe': 5}, {'steel': 1}),
    'awaken':    (3, {'fear': 100, 'courage': 100}, {'inv': 1, 'steam': 50}),
    'fear-inv':  (35, {'inv': 1, 'fear': 1000}, {'courage': 1000}),
    'anger-crk': (5, {'ld': 50, 'anger': 100}, {'hate': 30, 'fear': 100}),
    'reconst':   (35, {'e': 1, 'disgust': 700, 'hate': 1000}, {'anger': 1300}),
    'emo-crk':   (5, {'tar': 100, 'water': 35}, {'hope': 55, 'anger': 35, 'disgust': 35}),
    'tar':       (3, {'dc': 35, 'oil': 35}, {'tar': 70}),
    'dream-conc': (17, {'ld': 100}, {'dc': 50}),
    'liq-dream': (3, {'dream': 3, 'water': 200}, {'ld': 200}),
    'rot':       (480, {'j': 1}, {'dream': 1}),
    'hope-spoil': (35, {'disgust': 600, 'hope': 600}, {'e': 1, 'spoilage': 15}),
    'sf-hope':   (10, {'e': 1, 'hope': 150, 'ld': 150}, {'sf': 5}),
    'sf-massage': (10, {'sf': 20}, {'e': 1}),
    'steam-bath': (50, {'steam': 500}, {'e': 1}),
}
EXTERNAL = {'water', 'oil', 'ho', 'spoilage'}  # supplied or taken away


def net(r, k):
    """What one run of recipe r makes (+) or uses (-) of k."""
    return R[r][2].get(k, 0) - R[r][1].get(k, 0)


def solve():
    """Runs of each recipe per holmium craft."""
    names = [n for n in R if n != 'holmium']
    res = sorted({k for _, i, o in R.values() for k in (*i, *o)} - EXTERNAL)
    a = np.array([[net(r, k) for r in names] for k in res], float)
    b = np.array([-net('holmium', k) for k in res], float)
    x, *_ = np.linalg.lstsq(a, b, rcond=None)
    assert np.allclose(a @ x, b), 'no exact balance'
    out = {'holmium': 1.0, **dict(zip(names, x))}
    assert all(v > -1e-9 for v in out.values()), out
    return out


def main():
    """Print runs and machine time per holmium craft, and the external flows."""
    runs = solve()
    print(f"{'recipe':12} {'runs':>8} {'machine-s':>10}   (per holmium craft = 20 plates, speed 1)")
    for r, v in runs.items():
        print(f"{r:12} {v:8.2f} {v * R[r][0]:10.0f}")
    ext = {k: sum(v * net(r, k) for r, v in runs.items()) for k in EXTERNAL}
    print('external:', {k: round(v) for k, v in ext.items()})


if __name__ == '__main__':
    main()
