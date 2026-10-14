# Steady-state model of a Cubium ammo plant: cannon shells and piercing rounds magazines made
# from microcubes alone (plus water from melted ice). Cubes are conserved (every recipe returns
# the cube it uses), so only charges are balanced: a charge is one energized cube used and
# recharged by metallic aggravation (2 copper plates). Sulfur, carbon and the steel's iron come
# from cube jelly left to spoil into destabilized cube matter (3 min), recycled within 5 min.
#
# Fixed machines with productivity modules: PROD_ASM on assemblers (Cubium ore, amplification
# and plastic; not aggravation, ammo, or the recycler), PROD_CHEM on furnaces and chemical
# plants. Productivity never applies to the returned cube, and amplification's and
# scaffolding's only to the jelly they add.
#
# An LP picks recipe rates for the target output with the least machine time; surplus
# byproducts (ice, carbon, ore) are allowed and go to the trash chute.
# usage: python3 tools/ammo_econ.py [shells/s] [magazines/s] [assembler modules]
import sys

import numpy as np
from scipy.optimize import linprog

SHELLS = float(sys.argv[1]) if len(sys.argv) > 1 else 5.0
MAGS = float(sys.argv[2]) if len(sys.argv) > 2 else 5.0
ASM_MODULES = int(sys.argv[3]) if len(sys.argv) > 3 else 4
MODULE_PROD = 0.13            # legendary productivity module 2
MODULE_SPEED = -0.10          # speed penalties aren't improved by quality
CHEM_MODULES = 3
SCAFFOLD = True               # carbonic scaffolding may turn spare carbon into jelly

PA = ASM_MODULES * MODULE_PROD
PC = CHEM_MODULES * MODULE_PROD
SA = max(0.2, 1 + ASM_MODULES * MODULE_SPEED)   # speed multipliers (floor: -80%)
SC = max(0.2, 1 + CHEM_MODULES * MODULE_SPEED)

# name: (machine kind, seconds per run at crafting speed 1 after modules, ingredients, products)
R = {
    'cu-ore':     ('asm', 9 / SA, {'e': 1, 'j': 50}, {'cuore': 41 * (1 + PA)}),
    'fe-ore':     ('asm', 10 / SA, {'e': 1, 'j': 50}, {'feore': 41 * (1 + PA)}),
    'amplify':    ('asm', 3 / SA, {'e': 1, 'j': 10}, {'j': 17 + 7 * PA}),
    'aggravate':  ('asm-plain', 10, {'cu': 2}, {'e': 1}),
    'plastic':    ('asm', 50 / SA, {'e': 1, 'j': 50, 'c': 20}, {'plastic': 75 * (1 + PA)}),
    'scaffold':   ('asm', 10 / SA, {'e': 1, 'j': 12, 'c': 15}, {'j': 75 + 55 * PA}),
    'rot':        ('chest', 0, {'j': 1}, {'dcm': 1}),
    'recycle':    ('recycler', 1, {'dcm': 2},
                   {'c': 0.2, 's': 0.05, 'ice': 1.5, 'feore': 0.5, 'cuore': 0.2}),
    'smelt-cu':   ('furnace', 3.2 / SC, {'cuore': 1}, {'cu': 1 + PC}),
    'smelt-fe':   ('furnace', 3.2 / SC, {'feore': 1}, {'fe': 1 + PC}),
    'steel':      ('furnace', 16 / SC, {'fe': 5}, {'steel': 1 + PC}),
    'coal':       ('chem', 2 / SC, {'c': 5, 's': 1, 'water': 10}, {'coal': 1 + PC}),
    'explosives': ('chem', 4 / SC, {'s': 1, 'coal': 1, 'water': 10}, {'expl': 2 * (1 + PC)}),
    'melt':       ('chem', 1 / SC, {'ice': 1}, {'water': 20 * (1 + PC)}),
    'firearm':    ('asm-plain', 1, {'fe': 4}, {'firearm': 1}),
    'piercing':   ('asm-plain', 6, {'firearm': 2, 'steel': 1, 'cu': 2}, {'mag': 2}),
    'shell':      ('asm-plain', 8, {'steel': 2, 'plastic': 2, 'expl': 1}, {'shell': 1}),
}
if not SCAFFOLD:
    del R['scaffold']
TARGET = {'shell': SHELLS, 'mag': MAGS}


def net(r, k):
    """What one run of recipe r makes (+) or uses (-) of k."""
    return R[r][3].get(k, 0) - R[r][2].get(k, 0)


def solve():
    """Runs per second of each recipe, least machine time first."""
    names = list(R)
    res = sorted({k for _, _, i, o in R.values() for k in (*i, *o)})
    # net(k) >= target(k) for every resource (surplus is trashed)
    a_ub = np.array([[-net(r, k) for r in names] for k in res])
    b_ub = np.array([-TARGET.get(k, 0) for k in res])
    cost = np.array([R[r][1] + 1e-6 for r in names])
    sol = linprog(cost, A_ub=a_ub, b_ub=b_ub, bounds=(0, None), method='highs')
    assert sol.success, sol.message
    return dict(zip(names, sol.x)), res


def main():
    runs, res = solve()
    print(f'{SHELLS}/s cannon shells, {MAGS}/s piercing magazines; '
          f'assemblers +{PA:.0%} prod x{SA:.2f} speed, furnaces/chem +{PC:.0%} x{SC:.2f}')
    print(f"{'recipe':11} {'runs/s':>8} {'machines@1':>11}   kind")
    for r, v in runs.items():
        if v > 1e-9:
            print(f'{r:11} {v:8.3f} {v * R[r][1]:11.1f}   {R[r][0]}')
    surplus = {k: sum(v * net(r, k) for r, v in runs.items()) - TARGET.get(k, 0) for k in res}
    print('surplus/s:', {k: round(float(v), 2) for k, v in surplus.items() if v > 1e-6})
    charges = sum(v * R[r][2].get('e', 0) for r, v in runs.items())
    print(f"charges/s: {charges:.1f}   jelly into the rot chest/s: {runs['rot']:.1f} "
          f"(holds ~{runs['rot'] * 180:.0f} jelly while it spoils)")
    print(f"recyclers (speed 0.5): {runs['recycle'] * 1 / 0.5:.1f}")


if __name__ == '__main__':
    main()
