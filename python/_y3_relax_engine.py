"""r80-Y3: THE DECISIVE census --- the ANCESTRY-ONLY relaxed engine on RT_PS.

In the T_PS target, at R = Red^2 M the ONLY facts that transport are ANCESTRY
(y3w_Red_le0) plus the index arithmetic:
    m <= m',  m' < Lng R - 1,  le0 R m m',  le0 R m' (Lng R - 1)
`adm R m'` does NOT transport (y3z_C4_false).  So the engine we must prove is:

  RELAXED ENGINE (ancestry-only, NO adm, NO Marked):
    N in RT_PS, m <= m' < Lng N - 1, le0 N m m', le0 N m' (Lng N -1)
      ==> EX! sb. scb_decomp (Mark (Pred N) m) s (flatBT (Mark (Pred N) m')) b
               /\ scb_decomp (Mark N m)        s (flatBT (Mark N m'))        b

We census that GOAL and each intermediate lemma of the frozen engine, so we learn
WHICH sub-lemma (if any) actually needs adm:

  NEST  : (Mark N m,        Mark N m')        in MarkedB      [Mark_MarkedB_nest]
  NESTP : (Mark (Pred N) m, Mark (Pred N) m') in MarkedB
  TMP   : EX! sb over (Trans (Pred N), Trans N) vs Mark .. m  [m_7_4_Trans_Mark_Pred]
  GOAL  : the engine conclusion itself

Every count printed is NON-VACUOUS (hypotheses hold) and BOUNDS are stated.
Also reports how many exercises have adm(N,m') FALSE -- those are exactly the
cases the dead route could not reach, and the ones that decide this route.
"""
import sys, itertools, random
sys.setrecursionlimit(100000)
from red_model import Lng, le0, Pred, fmt
from trans_model import Mark, Trans, flatBT, scb_decomps, reduced, adm, ZB

_mk = {}
def mark(N, m):
    k = (tuple(N), m)
    if k not in _mk: _mk[k] = Mark(list(N), m)
    return _mk[k]
_tr = {}
def trans(N):
    k = tuple(N)
    if k not in _tr: _tr[k] = Trans(list(N))
    return _tr[k]

def dset(t, c):
    return set((tuple(s), tuple(b)) for s, b in scb_decomps(t, c))

def nest(N, m, mp):
    return len(scb_decomps(mark(N, m), flatBT(mark(N, mp)))) > 0

def tmp_ex1(N, m):
    P = Pred(N)
    a = dset(trans(P), flatBT(mark(P, m)))
    b = dset(trans(N), flatBT(mark(N, m)))
    return len(a & b) == 1

def goal(N, m, mp):
    P = Pred(N)
    a = dset(mark(P, m), flatBT(mark(P, mp)))
    b = dset(mark(N, m), flatBT(mark(N, mp)))
    return len(a & b) == 1

def gen_reduced(maxe, maxl):
    cols = [(a, b) for a in range(maxe + 1) for b in range(maxe + 1)]
    out = []
    def rec(M):
        if len(M) >= 2: out.append(list(M))
        if len(M) == maxl: return
        for c in cols:
            M.append(c)
            if reduced(M): rec(M)
            M.pop()
    rec([])
    return out

def rand_reduced(maxe, maxl, n, seed=4242):
    r = random.Random(seed)
    out = []
    tries = 0
    while len(out) < n and tries < n * 3000:
        tries += 1
        L = r.randint(2, maxl)
        M = [(r.randint(0, maxe), r.randint(0, maxe)) for _ in range(L)]
        if reduced(M): out.append(M)
    return out

def run(Ns, label):
    tot = 0
    f_goal = f_nest = f_nestp = f_tmp = 0
    n_nadm_mp = n_nadm_m = n_refl = 0
    cex = []
    for N in Ns:
        n = Lng(N)
        if n < 2: continue
        last = n - 1
        for mp in range(last):                     # m' < Lng N - 1
            if not le0(N, mp, last): continue      # le0 N m' (Lng N -1)
            for m in range(mp + 1):                # m <= m'
                if not le0(N, m, mp): continue     # le0 N m m'
                tot += 1
                if m == mp: n_refl += 1
                if not adm(N, mp): n_nadm_mp += 1
                if not adm(N, m): n_nadm_m += 1
                try:
                    g = goal(N, m, mp)
                    nn = nest(N, m, mp)
                    npp = nest(Pred(N), m, mp)
                    tt = tmp_ex1(N, m)
                except (RecursionError, AssertionError, IndexError):
                    tot -= 1
                    continue
                if not nn: f_nest += 1
                if not npp: f_nestp += 1
                if not tt: f_tmp += 1
                if not g:
                    f_goal += 1
                    if len(cex) < 6:
                        cex.append((fmt(N), m, mp, adm(N, m), adm(N, mp), nn, npp, tt))
    print(f"[{label}]")
    print(f"  NON-VACUOUS exercises (ancestry-only hyps): {tot}")
    print(f"    of these: reflexive m=m' : {n_refl}")
    print(f"              adm(N,m') FALSE: {n_nadm_mp}   <-- unreachable by the dead route")
    print(f"              adm(N,m)  FALSE: {n_nadm_m}")
    print(f"  FAILURES:  GOAL {f_goal} | NEST {f_nest} | NESTP {f_nestp} | TMP {f_tmp}")
    for c in cex:
        print("   GOAL-CEX  N=%s m=%s m'=%s adm_m=%s adm_mp=%s nest=%s nestp=%s tmp=%s" % c)
    return f_goal

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'full':
        e, l = int(sys.argv[2]), int(sys.argv[3])
        Ns = gen_reduced(e, l)
        print(f"# reduced N (entries<={e}, Lng<={l}): {len(Ns)}", flush=True)
        run(Ns, f"FULL RT_PS entries<={e} Lng<={l}")
    else:
        e, l, n = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        Ns = rand_reduced(e, l, n)
        print(f"# random reduced N sampled: {len(Ns)}", flush=True)
        run(Ns, f"RANDOM RT_PS entries<={e} Lng<={l} n={len(Ns)}")
