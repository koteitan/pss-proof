"""r81-Y4 WIDE census: what does the JOINT nesting really need on a reduced N?

Same experiment as _y4_joint_sharp.py, with memoised Trans/Mark/le0 so the
required bounds (entries <= 8, Lng <= 6) are reachable.

Setting.  N in RT_PS, j <= j0 < Lng N - 1.  y4c gives UNCONDITIONALLY a UNIQUE
position sbN of Mark N j0 inside Mark N j; and, Pred N being reduced too, a
UNIQUE position sbP of Mark (Pred N) j0 inside Mark (Pred N) j.
      JOINT  :=  sbN = sbP     (the two unique positions COINCIDE)
JOINT is exactly what the Sec 7.4 corollary needs beyond y4c.

Implications screened (premise-count printed, so a pass is never vacuous):
  I1 MK0   => JOINT      MK0   = (N,j0) in Marked = adm N j0 /\ leR N 0 j0 (Lng N -1)
  I2 JM1   => JOINT      JM1   = monoT N /\ t1 /= 0 /\ j0 <= transJm1 N
                                 (transJm1 N = Adm N (parent N 0 (Lng N -1)))
  I3 SURG0 => JOINT      SURG0 = monoT N /\ t1 /= 0
                                 /\ (Mark (Pred N) j0, transC1 N) in MarkedB
  I4 JM1  <=> SURG0      (y4b free-nesting identification of the surgery guard)
  I5 MK0 /\ monoT /\ t1/=0 => JM1
  I6 LE0   => JOINT      LE0   = le0 N j j0                      -- expected FALSE
  I7 ADM0  => JOINT      ADM0  = adm N j0                        -- expected FALSE
  I8 ADM0 /\ LE0 => JOINT                                        -- expected FALSE
"""
import sys, random
sys.setrecursionlimit(30000)
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-y4/python')
import _y4_fastcache      # noqa: F401  (must be first)
import _y4_fastcache2     # noqa: F401
import red_model as rm
import trans_model as tm
from red_model import Lng, fmt

le0, leR, monoT, parent = rm.le0, rm.leR, rm.monoT, rm.parent
Mark, Trans, scb_decomps = tm.Mark, tm.Trans, tm.scb_decomps
Pred, flatBT, reduced, adm, Adm, ZB = (tm.Pred, tm.flatBT, tm.reduced, tm.adm,
                                       tm.Adm, tm.ZB)


def uniq_pos(t, c):
    d = scb_decomps(t, c)
    if len(d) != 1:
        return ('MULTI', len(d))
    return (tuple(d[0][0]), tuple(d[0][1]))


def gen_reduced(maxe, maxl):
    """EXHAUSTIVE: every reduced N with entries <= maxe and 1 <= Lng N <= maxl.
    `reduced` is prefix-closed, so pruning is sound."""
    cols = [(a, b) for a in range(maxe + 1) for b in range(maxe + 1)]
    out = []
    def rec(M):
        if M:
            out.append(tuple(M))
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
    reg_tot, reg_fail = {}, {}
    for N in Ns:
        N = list(N)
        n = Lng(N)
        if n < 2:
            continue
        Pn = Pred(N)
        j1 = n - 1
        mono = monoT(N)
        t1nz = mono and Trans(Pn) != ZB
        jm1 = Adm(N, parent(N, 0, j1)) if t1nz else None
        c1 = Mark(Pn, jm1) if t1nz else None
        reg = 'mono/t1!=0' if t1nz else ('mono/t1=0' if mono else 'multi')
        for j0 in range(n - 1):                       # j0 < Lng N - 1
            for j in range(j0 + 1):                   # j <= j0
                try:
                    mj, mj0 = Mark(N, j), Mark(N, j0)
                    pj, pj0 = Mark(Pn, j), Mark(Pn, j0)
                except (RecursionError, AssertionError, IndexError, ValueError):
                    continue
                posN = uniq_pos(mj, flatBT(mj0))
                posP = uniq_pos(pj, flatBT(pj0))
                nmultiN += posN[0] == 'MULTI'
                nmultiP += posP[0] == 'MULTI'
                tot += 1
                reg_tot[reg] = reg_tot.get(reg, 0) + 1
                JOINT = (posN == posP)
                joint_ok += JOINT
                if not JOINT:
                    reg_fail[reg] = reg_fail.get(reg, 0) + 1
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
                                cex[k].append((fmt(N), j, j0, reg))
    print(f"[{label}]")
    print(f"  NON-VACUOUS exercises (N reduced, j <= j0 < Lng N - 1): {tot}")
    print(f"  JOINT holds {joint_ok}   /   JOINT FAILS {tot - joint_ok}")
    print(f"  y4c sanity: N-position non-unique {nmultiN}x, "
          f"Pred-position non-unique {nmultiP}x   (y4c predicts 0 and 0)")
    print("  by regime (exercises / JOINT-failures):")
    for r in sorted(reg_tot):
        print(f"     {r:12s} {reg_tot[r]:9d} / {reg_fail.get(r, 0):9d}")
    for k in IMPS:
        v = 'HOLDS' if bad[k] == 0 else 'FAILS'
        vac = '   <-- VACUOUS, ignore' if prem[k] == 0 else ''
        print(f"  {v}  {k:24s} premise true on {prem[k]:9d} exercises, "
              f"violations {bad[k]:8d}{vac}")
        for c in cex[k]:
            print("            cex  N=%s  j=%s  j0=%s  regime=%s" % c)
    sys.stdout.flush()


def rand_reduced(maxe, maxl, n, seed=8106):
    """Random walk in the (prefix-closed) tree of reduced sequences: at each step
    pick uniformly among the columns that keep the sequence reduced.  EVERY sample
    is reduced, so this actually reaches Lng = maxl at entries = maxe -- which naive
    rejection sampling essentially never does at these bounds."""
    r = random.Random(seed)
    cols = [(a, b) for a in range(maxe + 1) for b in range(maxe + 1)]
    out, seen, tries = [], set(), 0
    while len(out) < n and tries < n * 200:
        tries += 1
        L = r.randint(2, maxl)
        M = []
        for _ in range(L):
            r.shuffle(cols)
            for c in cols:
                M.append(c)
                if reduced(M):
                    break
                M.pop()
            else:
                break
        if len(M) >= 2 and tuple(M) not in seen:
            seen.add(tuple(M))
            out.append(tuple(M))
    return out


if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'full':
        e, l = int(sys.argv[2]), int(sys.argv[3])
        Ns = gen_reduced(e, l)
        print(f"# EXHAUSTIVE: all reduced N with entries<={e}, 1<=Lng<={l}: "
              f"{len(Ns)} sequences", flush=True)
        run(Ns, f"EXHAUSTIVE  entries<={e}  Lng<={l}")
    else:
        e, l, n = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        Ns = rand_reduced(e, l, n)
        print(f"# RANDOM: distinct reduced N sampled uniformly from "
              f"entries<={e}, 2<=Lng<={l}: {len(Ns)} sequences", flush=True)
        run(Ns, f"RANDOM  entries<={e}  Lng<={l}  n={len(Ns)}")
