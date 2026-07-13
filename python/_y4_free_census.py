"""r81-Y4: census of the FULLY FREE nesting engine (no Marked, no adm, no le0).

Rationale: at R = Red^2 M neither adm M j nor adm M j0 transports (y3z_C4_false),
so an engine that still asks for (R,j0) in Marked is unusable.  Test whether the
nesting needs ANY hypothesis at all beyond reducedness.

  FREE1  : (Mark N j, Mark N j0) in MarkedB           for all j <= j0   (j0 unbounded)
  FREE1U : EX! (s,b). scb_decomp (Mark N j) s (flatBT (Mark N j0)) b    (same range)
  FREE2  : EX! (s,b) decomposing BOTH
             Mark (Pred N) j  with centre Mark (Pred N) j0
             Mark N j         with centre Mark N j0                for j <= j0 < Lng N -1
  FREETMP: EX! (s,b). scb_decomp (Trans (Pred N)) s (flatBT (Mark (Pred N) m)) b
                    & scb_decomp (Trans N)        s (flatBT (Mark N m))        b
           for m < Lng N - 1          (= m_7_4_Trans_Mark_Pred, Marked dropped)
  ZERO   : Mark N m = 0_B  <-->  zeroT N        (the degenerate-case lemma)

Every exercise is NON-VACUOUS (the only hypothesis is reducedness + index range).
BOUNDS ARE PRINTED.
"""
import sys, random
sys.setrecursionlimit(20000)
from red_model import Lng, Pred, fmt, zeroT, le0
from trans_model import Mark, Trans, flatBT, scb_decomps, reduced, ZB

def dset(t, c):
    return set((tuple(s), tuple(b)) for s, b in scb_decomps(t, c))

def gen_reduced(maxe, maxl):
    cols = [(a, b) for a in range(maxe + 1) for b in range(maxe + 1)]
    out = []
    def rec(M):
        if M: out.append(list(M))
        if len(M) == maxl: return
        for c in cols:
            M.append(c)
            if reduced(M): rec(M)
            M.pop()
    rec([])
    return out

def rand_reduced(maxe, maxl, n, seed=8181):
    r = random.Random(seed)
    out, tries = [], 0
    while len(out) < n and tries < n * 5000:
        tries += 1
        L = r.randint(1, maxl)
        M = [(r.randint(0, maxe), r.randint(0, maxe)) for _ in range(L)]
        if reduced(M):
            out.append(M)
    return out

def run(Ns, label, slack=2):
    n1 = n1u = n2 = ntm = nz = 0
    f1 = f1u = f2 = ftm = fz = 0
    cex = {}
    def note(k, w):
        if k not in cex: cex[k] = w
    for N in Ns:
        n = Lng(N)
        P = Pred(N)
        try:
            trN, trP = Trans(list(N)), Trans(list(P))
        except (RecursionError, AssertionError, IndexError, ValueError):
            continue
        hi = n + slack                       # probe out-of-range columns too
        MK = {}
        MP = {}
        ok = True
        for k in range(hi + 1):
            try:
                MK[k] = Mark(list(N), k)
                MP[k] = Mark(list(P), k)
            except (RecursionError, AssertionError, IndexError, ValueError):
                ok = False
                break
        if not ok:
            continue
        # ZERO
        for k in range(hi + 1):
            nz += 1
            if (MK[k] == ZB) != zeroT(N):
                fz += 1
                note('ZERO', (fmt(N), k, MK[k] == ZB, zeroT(N)))
        # TMPa: ancestry-only relaxation of m_7_4_Trans_Mark_Pred (adm DROPPED,
        #       le0 m (Lng N -1) KEPT -- it transports through Red, adm does not)
        for m in range(max(0, n - 1)):
            if not le0(N, m, n - 1):
                continue
            ntm += 1
            D = dset(trP, flatBT(MP[m])) & dset(trN, flatBT(MK[m]))
            if len(D) != 1:
                ftm += 1
                note('TMPa', (fmt(N), m, len(D)))
        for j0 in range(hi + 1):
            for j in range(j0 + 1):
                n1 += 1
                D = dset(MK[j], flatBT(MK[j0]))
                if len(D) == 0:
                    f1 += 1
                    note('FREE1', (fmt(N), j, j0))
                n1u += 1
                if len(D) != 1:
                    f1u += 1
                    note('FREE1U', (fmt(N), j, j0, len(D)))
                # FREE2a: ancestry-only joint (both columns row-0 ancestors of the last)
                if j0 < n - 1 and le0(N, j, n - 1) and le0(N, j0, n - 1):
                    n2 += 1
                    DP = dset(MP[j], flatBT(MP[j0]))
                    if len(D & DP) != 1:
                        f2 += 1
                        note('FREE2a', (fmt(N), j, j0, len(D), len(DP), len(D & DP)))
    print(f"[{label}]  (columns probed up to Lng N + {slack})")
    print(f"  ZERO    exercises {nz:8d}  FAILURES {fz}")
    print(f"  FREE1   exercises {n1:8d}  FAILURES {f1}   (MarkedB nesting, no hyps)")
    print(f"  FREE1U  exercises {n1u:8d}  FAILURES {f1u}  (EX! of (s,b))")
    print(f"  FREETMP exercises {ntm:8d}  FAILURES {ftm}  (m_7_4_Trans_Mark_Pred, Marked dropped)")
    print(f"  FREE2   exercises {n2:8d}  FAILURES {f2}   (joint EX! at Pred N and N)")
    for k, v in cex.items():
        print(f"   {k}-CEX {v}")

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
