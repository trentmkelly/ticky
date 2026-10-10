# Rough Cubium factory model for examples/cubium-generator.ticky: 4 rows x N crafters, a
# warehouse, ore smelted after 20 s. `old`/`new` mirror the controller policy before and after
# the 2026-10-10 copper-first rework (keep `new` in step with the .ticky by hand).
# usage: python3 -c "import sys; sys.path.insert(0, 'tools'); import cubium_econ as e; print(e.run(e.new, {'N': 20, 'goal': 10000}, {'e': 50, 'cu': 100})[0])"
# Rough factory model: 4 rows x N crafters, warehouse, ore->plate delay. Policy mirrors the .ticky.
import sys
N = 20
R = {  # recipe: (time s, ins, outs)
 'cu':  (9,  {'e':1,'j':50}, {'cuore':41,'d':1}),
 'fe':  (10, {'e':1,'j':50}, {'feore':41,'d':1}),
 'jel': (1,  {'e':1}, {'j':2,'d':1}),
 'amp': (3,  {'e':1,'j':10}, {'j':17,'d':1}),
 'chg': (10, {'d':1,'cu':2}, {'e':1}),
}
def run(policy, P, w, secs=7200, log=False):
    w = dict(w); rows=[None]*4; since=[999]*4; crafters=[[0]*N for _ in range(4)]  # remaining time
    smelt=[]  # (t_done, kind, n)
    turn=0; hist=[]
    for t in range(secs*2):  # half-second steps
        ts=t/2
        # smelting
        for x in [x for x in smelt if x[0]<=ts]:
            w[x[1]]=w.get(x[1],0)+x[2]; smelt.remove(x)
        # crafters
        working=[0]*4
        for r in range(4):
            rec=rows[r]
            for i in range(N):
                if crafters[r][i]>0 and rec_of[r][i]!=rec:
                    for k,v in R[rec_of[r][i]][1].items(): w[k]=w.get(k,0)+v
                    crafters[r][i]=0
                if crafters[r][i]>0:
                    crafters[r][i]-=0.5
                    if crafters[r][i]<=0:
                        for k,v in R[rec_of[r][i]][2].items():
                            if k in('cuore','feore'): smelt.append((ts+20,'cu' if k=='cuore' else 'fe',v))
                            else: w[k]=w.get(k,0)+v
                    else: working[r]+=1
                if crafters[r][i]<=0 and rec:
                    tm,ins,_=R[rec]
                    if all(w.get(k,0)>=v for k,v in ins.items()):
                        for k,v in ins.items(): w[k]-=v
                        crafters[r][i]=tm; rec_of[r][i]=rec; working[r]+=1
        if t%1==0:  # controller every 30 ticks
            rows[turn],since[turn]=policy(P,w,rows,since,turn,working[turn])
            since=[min(s+0.5,999) for s in since]; turn=(turn+1)%4
        if t%120==0: hist.append((int(ts),dict(w),list(rows)))
    return w,hist
rec_of=[[None]*20 for _ in range(4)]

def score(want, r, cur, rows):
    others = sum(1 for x in rows if x == r) - (1 if cur == r else 0)
    return want - P_SHARE * others if want > 0 else 0
P_SHARE = 300

def old(P, w, rows, since, turn, working):
    cu, fe, j, e, d = (w.get(k,0) for k in ('cu','fe','j','e','d'))
    ore_score = lambda p: max(1, (10000 - min(p, 10000)) * 1000 // 10000)
    ore_ok = e > 0 and j >= 50
    need = (400 - j) * 1000 // 400 if j < 400 and e > 2 else 0
    wants = {'cu': ore_score(cu) if ore_ok else 0, 'fe': ore_score(fe) if ore_ok else 0,
             'jel': need if j < 30 else 0, 'amp': need if j >= 30 else 0,
             'chg': d * 1000 // (d + e) if d > 0 and cu >= 2 else 0}
    stop_j = j > 800 or e <= 2
    cur = rows[turn]
    busy = working > 0 or since[turn] < 10
    stop = (cur == 'amp' and stop_j) or (cur == 'jel' and (stop_j or j >= 30))
    if cur is None or not busy or stop:
        best, top = None, 0
        for r in ('cu', 'fe', 'jel', 'amp', 'chg'):
            s = score(wants[r], r, cur, rows)
            if s > top: best, top = r, s
        if best != cur: return best, 0
    return cur, since[turn]

def new(P, w, rows, since, turn, working):
    cu, fe, j, e, d = (w.get(k,0) for k in ('cu','fe','j','e','d'))
    N = P['N']
    jelly_goal = 50 * N            # one row of ore crafts
    reserve = N                    # cubes for one row of ore crafts
    floor = 16 * N                 # copper to recharge one row of ore crafts' cubes
    owed = cu - 2 * d              # copper left after recharging every dormant cube
    ore_score = lambda p: min(2000, max(1, (P['goal'] - p) * 1000 // P['goal']))
    ore_ok = e > 0 and j >= 50
    can_jelly = e > reserve or j < 50
    need = (jelly_goal - j) * 1000 // jelly_goal if j < jelly_goal and can_jelly else 0
    wants = {'cu': ore_score(owed) if ore_ok else 0,
             'fe': ore_score(fe) if ore_ok and cu >= floor else 0,
             'jel': need if j < 30 else 0, 'amp': need if j >= 30 else 0,
             'chg': d * 1000 // (d + e) if d > 0 and cu >= 2 else 0}
    cur = rows[turn]
    busy = working > 0 or since[turn] < 10
    stop = (cur in ('amp', 'jel') and (j >= jelly_goal or not can_jelly)) or (cur == 'jel' and j >= 30) \
        or (cur == 'fe' and cu < floor // 2)
    if cur is None or not busy or stop:
        best, top = None, 0
        for r in ('cu', 'fe', 'jel', 'amp', 'chg'):
            s = score(wants[r], r, cur, rows)
            if s > top: best, top = r, s
        if best != cur: return best, 0
    return cur, since[turn]
