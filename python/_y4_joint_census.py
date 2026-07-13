"""r81-Y4: what does the JOINT nesting really need?

For N reduced (RT_PS), y4c gives UNCONDITIONALLY, for every j <= j0:
    EX! sbN.  scb_decomp (Mark N j)        sbN  (flatBT (Mark N j0))        -- N-side
and, since Pred N is reduced too, also
    EX! sbP.  scb_decomp (Mark (Pred N) j) sbP  (flatBT (Mark (Pred N) j0)) -- Pred-side

JOINT  :=  sbN = sbP   (the two unique positions COINCIDE).
That -- and nothing else -- is the content of y4d / the article's Sec 7.4 engine.

This census asks: under which hypothesis on (N,j,j0) is JOINT true?
Candidate hypotheses tested (all read off N, all available to the Sec 7.4 caller):
  MK0   : (N,j0) in Marked                   = adm N j0 /\ leR N 0 j0 (Lng N -1)
  ADM0  : adm N j0
  LE0   : le0 N j j0
  JM1   : j0 <= transJm1 N = Adm N (parent N 0 (Lng N -1))     [monoT, t1 /= 0 only]
  SURG0 : (Mark (Pred N) j0, c1) in MarkedB  [the raw surgery-guard at column j0]
BOUNDS PRINTED, only NON-VACUOUS (j <= j0 < Lng N - 1) exercises counted.
"""
import sys, itertools
sys.setrecursionlimit(20000)
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-y4/python')
from red_model import Lng, le0, leR, entry, monoT, parent, P, fmt
from trans_model import (Mark, Trans, Pred, flatBT, scb_decomps, reduced, adm,
                         Adm, ZB, bpHeadV, bpHeadT)

_mk = {}
def mark(N, m):
    k = (tuple(N), m)
    if k not in _mk:
        _mk[k] = Mark(list(N), m)
    return _mk[k]

def uniq_pos(t, c):
    """the unique (s,b) decomposing t with core c, or None."""
    d = scb_decomps(t, c)
    if len(d) != 1:
        return ('MULTI', len(d))
    return (tuple(d[0][0]), tuple(d[0][1]))

def marked(N, j0):
    return adm(N, j0) and leR(N, 0, j0, Lng(N) - 1)

def jm1_of(N):
    """transJm1 N, defined only in the monoT / t1 /= 0 regime."""
    j1 = Lng(N) - 1
    if j1 == 0 or not monoT(N):
        return None
    if Trans(Pred(N)) == ZB:
        return None
    return Adm(N, parent(N, 0, j1))

def surg_guard(N, k):
    """(Mark (Pred N) k, c1) in MarkedB -- the raw guard the Mark recursion tests."""
    j1 = Lng(N) - 1
    if j1 == 0 or not monoT(N) or Trans(Pred(N)) == ZB:
        return None
    c1 = mark(Pred(N), Adm(N, parent(N, 0, j1)))
    return bool(scb_decomps(mark(Pred(N), k), flatBT(c1)))

def regime(N):
    j1 = Lng(N) - 1
    if j1 == 0:
        return 'len1'
    if not monoT(N):
        return 'multi'
    if Trans(Pred(N)) == ZB:
        return 'mono/t1=0'
    return 'mono/t1!=0'

def gen_reduced(maxe, maxl):
    cols = [(a, b) for a in range(maxe + 1) for b in range(maxe + 1)]
    out = []
    def rec(M):
        if M:
            out.append(list(M))
        if len(M) == maxl:
            return
        for c in cols:
            M.append(c)
            if reduced(M):
                rec(M)
            M.pop()
    rec([])
    return out

def run(Ns, label):
    tot = 0
    joint_ok = 0
    fails = []
    # contingency: hypothesis -> [n_hyp_true, n_hyp_true_and_JOINT_fails,
    #                             n_hyp_false, n_hyp_false_and_JOINT_holds]
    HYPS = ['MK0', 'ADM0', 'LE0', 'JM1', 'SURG0']
    cont = {h: [0, 0, 0, 0] for h in HYPS}
    reg_tot, reg_fail = {}, {}
    n_multi_N = n_multi_P = 0
    for N in Ns:
        n = Lng(N)
        if n < 2:
            continue
        Pn = Pred(N)
        reg = regime(N)
        jm1 = jm1_of(N)
        for j0 in range(n - 1):          # j0 < Lng N - 1 : the corollary's setting
            for j in range(j0 + 1):
                try:
                    mj, mj0 = mark(N, j), mark(N, j0)
                    pj, pj0 = mark(Pn, j), mark(Pn, j0)
                except (RecursionError, AssertionError, IndexError, ValueError):
                    continue
                posN = uniq_pos(mj, flatBT(mj0))
                posP = uniq_pos(pj, flatBT(pj0))
                if posN[0] == 'MULTI':
                    n_multi_N += 1
                if posP[0] == 'MULTI':
                    n_multi_P += 1
                tot += 1
                reg_tot[reg] = reg_tot.get(reg, 0) + 1
                ok = (posN == posP)
                if ok:
                    joint_ok += 1
                else:
                    reg_fail[reg] = reg_fail.get(reg, 0) + 1
                h = {
                    'MK0':   marked(N, j0),
                    'ADM0':  adm(N, j0),
                    'LE0':   le0(N, j, j0) or j == j0,
                    'JM1':   (jm1 is not None and j0 <= jm1),
                    'SURG0': bool(surg_guard(N, j0)),
                }
                for k in HYPS:
                    if h[k]:
                        cont[k][0] += 1
                        if not ok:
                            cont[k][1] += 1
                    else:
                        cont[k][2] += 1
                        if ok:
                            cont[k][3] += 1
                if not ok and len(fails) < 10:
                    fails.append((fmt(N), j, j0, reg, h, posN != posP,
                                  mj == pj, mj0 == pj0))
    print(f"[{label}]")
    print(f"  NON-VACUOUS exercises (N reduced, j <= j0 < Lng N - 1): {tot}")
    print(f"  JOINT (unique N-position == unique Pred-position) HOLDS: {joint_ok}"
          f"   FAILS: {tot - joint_ok}")
    print(f"  sanity: uniqueness of the N-position violated {n_multi_N} times, "
          f"of the Pred-position {n_multi_P} times  (y4c says 0)")
    print("  by regime (exercises / JOINT-failures):")
    for r in sorted(reg_tot):
        print(f"     {r:12s}  {reg_tot[r]:7d} / {reg_fail.get(r,0):7d}")
    print("  hypothesis screening  [H true | H true & JOINT FAILS | H false | "
          "H false & JOINT holds]")
    for k in HYPS:
        c = cont[k]
        verdict = "SUFFICIENT" if c[1] == 0 else f"NOT sufficient ({c[1]} cex)"
        sharp = "and SHARP (never over-strong)" if c[3] == 0 else \
                f"but over-strong ({c[3]} JOINT-true cases it rejects)"
        print(f"     {k:6s} {c[0]:7d} | {c[1]:7d} | {c[2]:7d} | {c[3]:7d}   "
              f"-> {verdict}, {sharp}")
    for f in fails:
        print("   JOINT-CEX N=%s j=%s j0=%s reg=%s H=%s Mj=Pj?%s Mj0=Pj0?%s"
              % (f[0], f[1], f[2], f[3], f[4], f[6], f[7]))
    return tot - joint_ok

if __name__ == '__main__':
    e, l = int(sys.argv[1]), int(sys.argv[2])
    Ns = gen_reduced(e, l)
    print(f"# reduced N with entries<={e}, Lng<={l}: {len(Ns)}", flush=True)
    run(Ns, f"FULL reduced census  entries<={e}  Lng<={l}")
