"""r81-Y4 (sharpening): WHICH hypothesis makes the JOINT nesting true on a reduced N?

Setting.  N in RT_PS, j <= j0 < Lng N - 1.  y4c already gives, UNCONDITIONALLY,
a UNIQUE position sbN of Mark N j0 inside Mark N j, and (Pred N being reduced too)
a UNIQUE position sbP of Mark (Pred N) j0 inside Mark (Pred N) j.
      JOINT  :=  sbN = sbP.
Everything the Sec 7.4 corollary needs beyond y4c is exactly JOINT.

Checked implications (each printed with its witness count):
  I1 : MK0   => JOINT           MK0  = (N,j0) in Marked = adm N j0 /\ leR N 0 j0 (Lng N-1)
  I2 : JM1   => JOINT           JM1  = mono /\ t1/=0 /\ j0 <= transJm1 N = Adm N (parent N 0 j1)
  I3 : SURG0 => JOINT           SURG0= mono /\ t1/=0 /\ (Mark (Pred N) j0, transC1 N) in MarkedB
  I4 : JM1 <=> SURG0            (the free-nesting y4b identification of the surgery guard)
  I5 : MK0 /\ mono /\ t1/=0 => JM1
  I6 : LE0 => JOINT             LE0  = le0 N j j0        <-- expected FALSE
  I7 : ADM0 => JOINT            ADM0 = adm N j0          <-- expected FALSE
  I8 : ADM0 /\ LE0 => JOINT                              <-- expected FALSE
BOUNDS PRINTED.  Only NON-VACUOUS exercises counted; each implication reports the
number of exercises where its premise HOLDS (0 would mean a vacuous pass).
"""
import sys
sys.setrecursionlimit(20000)
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-y4/python')
from red_model import Lng, le0, leR, monoT, parent, fmt
from trans_model import (Mark, Trans, Pred, flatBT, scb_decomps, reduced, adm,
                         Adm, ZB)

_mk = {}
def mark(N, m):
    k = (tuple(N), m)
    if k not in _mk:
        _mk[k] = Mark(list(N), m)
    return _mk[k]

def uniq_pos(t, c):
    d = scb_decomps(t, c)
    if len(d) != 1:
        return ('MULTI', len(d))
    return (tuple(d[0][0]), tuple(d[0][1]))

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

IMPS = ['I1 MK0=>JOINT', 'I2 JM1=>JOINT', 'I3 SURG0=>JOINT', 'I4 JM1<=>SURG0',
        'I5 MK0&mono&t1!=0=>JM1', 'I6 LE0=>JOINT', 'I7 ADM0=>JOINT',
        'I8 ADM0&LE0=>JOINT']

def run(Ns, label):
    tot = joint_ok = 0
    prem = {k: 0 for k in IMPS}
    bad = {k: 0 for k in IMPS}
    cex = {k: [] for k in IMPS}
    nmultiN = nmultiP = 0
    for N in Ns:
        n = Lng(N)
        if n < 2:
            continue
        Pn = Pred(N)
        j1 = n - 1
        mono = monoT(N)
        t1nz = mono and Trans(Pn) != ZB
        jm1 = Adm(N, parent(N, 0, j1)) if t1nz else None
        c1 = mark(Pn, jm1) if t1nz else None
        for j0 in range(n - 1):
            for j in range(j0 + 1):
                try:
                    mj, mj0 = mark(N, j), mark(N, j0)
                    pj, pj0 = mark(Pn, j), mark(Pn, j0)
                except (RecursionError, AssertionError, IndexError, ValueError):
                    continue
                posN = uniq_pos(mj, flatBT(mj0))
                posP = uniq_pos(pj, flatBT(pj0))
                if posN[0] == 'MULTI':
                    nmultiN += 1
                if posP[0] == 'MULTI':
                    nmultiP += 1
                tot += 1
                JOINT = (posN == posP)
                joint_ok += JOINT
                MK0 = adm(N, j0) and leR(N, 0, j0, j1)
                ADM0 = adm(N, j0)
                LE0 = le0(N, j, j0) or j == j0
                JM1 = bool(t1nz and j0 <= jm1)
                SURG0 = bool(t1nz and scb_decomps(pj0, flatBT(c1)))
                tests = {
                    'I1 MK0=>JOINT':          (MK0, JOINT),
                    'I2 JM1=>JOINT':          (JM1, JOINT),
                    'I3 SURG0=>JOINT':        (SURG0, JOINT),
                    'I4 JM1<=>SURG0':         (t1nz, JM1 == SURG0),
                    'I5 MK0&mono&t1!=0=>JM1': (MK0 and t1nz, JM1),
                    'I6 LE0=>JOINT':          (LE0, JOINT),
                    'I7 ADM0=>JOINT':         (ADM0, JOINT),
                    'I8 ADM0&LE0=>JOINT':     (ADM0 and LE0, JOINT),
                }
                for k, (p, c) in tests.items():
                    if p:
                        prem[k] += 1
                        if not c:
                            bad[k] += 1
                            if len(cex[k]) < 3:
                                cex[k].append((fmt(N), j, j0,
                                               'mono/t1!=0' if t1nz else
                                               ('mono/t1=0' if mono else 'multi')))
    print(f"[{label}]")
    print(f"  NON-VACUOUS exercises (N reduced, j <= j0 < Lng N - 1): {tot}")
    print(f"  JOINT holds {joint_ok} / fails {tot - joint_ok}")
    print(f"  y4c sanity: N-position non-unique {nmultiN}x, Pred-position non-unique {nmultiP}x")
    for k in IMPS:
        v = 'HOLDS ' if bad[k] == 0 else 'FAILS '
        vac = '  (VACUOUS!)' if prem[k] == 0 else ''
        print(f"  {v} {k:24s} premise true on {prem[k]:7d} exercises, "
              f"violations {bad[k]:6d}{vac}")
        for c in cex[k]:
            print(f"            cex N=%s j=%s j0=%s reg=%s" % c)
    return tot

if __name__ == '__main__':
    e, l = int(sys.argv[1]), int(sys.argv[2])
    Ns = gen_reduced(e, l)
    print(f"# reduced N enumerated EXHAUSTIVELY, entries<={e}, Lng<={l}: {len(Ns)}",
          flush=True)
    run(Ns, f"EXHAUSTIVE reduced census  entries<={e}  Lng<={l}")
