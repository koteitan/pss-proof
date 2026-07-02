#!/usr/bin/env python3
"""r16-E2: empirical validation of p_8_2_condV_terminal_slice_Trans
(補題（条件(V)の下での終切片とTransの関係）, pss_paper 1604, article 3664)
and every intermediate transport of the planned Isabelle proof.

STATEMENT (target): M in RT_PS cap PT_PS, Br M != [], j1 = Lng M - 1,
J1 = Lng(Br M)-1, j0' = Joints M!J1, j1' = FirstNodes M!J1, M' = seg M m j1;
HYP: m < j0'  OR  (m = j0' and M_{0,j1'} = M_{1,j1'} and descending (Br M)).
CLAIM: unique t1 with Trans M = D_{M_{1,0}} t1 and Trans M' = D_{M_{1,m}} t1.
Equivalent check (existence side):
  MAIN: Trans M, Trans M' both principal, heads e1(M,0)/e1(M,m),
        bpHeadT (Trans M') == bpHeadT (Trans M).

INTERMEDIATES (proof plan, r16-E2):
  I1  trunk: j <= TrMax M  ==>  M!j = (M10+j, M10+j)  (and M00=M10)
  I2  adm positions <= TrMax M are exactly {0, TrMax M}
  I3  j0 := parent M 0 j1 satisfies j0' <= j0; (m<j0 or e0j1=e1j1);
      m=j0 ==> j0 < TrMax  (this is m_8_2_condV_rightmost_parent, proven)
  I4  STEP case (j1 > TrMax+1), m>0: jm1 := Adm M j0 satisfies
      jm1 > m  or  jm1 == 0   (jm1 in (0,m] impossible)
  I5  STEP, jm1 > m: Adm M' (j0-m) = jm1-m  and
      Mark (Pred M) jm1 == Mark (Pred M') (jm1-m)   (c1 EQUAL as terms)
  I6  STEP, jm1 == 0 < m: Adm M' (j0-m) = 0,
      c1^M = Trans(Pred M) (root mark), c1^M' = Trans(Pred M') (root mark),
      scb decomposition of (t1,c1) is ([],[]) on both sides
  I7  cond-branch match: branch(M)==branch(M') in {1:(I|III|V),2:VI,
      3:t2=0-surgery,4:else-surgery}; c2 relation:
        jm1>m  : c2^M == c2^M'
        jm1=0<m: c2^M = D_{M10} X, c2^M' = D_{M1m} X (same X)
  I8  HYP transfer: j1-1 > TrMax ==> Br(Pred M) != [] and HYP(Pred M, m)
      (with the same m; Pred M' = seg (Pred M) m (Lng(Pred M)-1))
  B1  BASE case (j1 = TrMax+1): M = diagSeq(M10, M10+TrMax) ++ [(w',w)];
      records which of the 4 m_8_1_Pred_diagSeq_Trans cases fires for M/M',
      m=TrMax (length-2 M') occurrences counted separately.

Pools: (A) GENUINE = oper-BFS closure of diagSeq seeds (subset of ST_PS),
filtered to reduced & monoT & Br != [];  (B) WIDE = exhaustive small reduced
monoT sequences (RT_PS-level regime; includes non-adm j0 / cond II,IV
configurations unreachable in ST_PS pools) + the six r15 deep-condIV miners.
Every claim is reported as ok/total per pool.

Run: python3 _r16_e2_validate.py [timelimit_A] [timelimit_B]
"""
import sys, time, signal, random, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s5/python')
from red_model import (Lng, entry, parent, hasParent, oper, seg, diagSeq,
                       monoT, zeroT, Br, Joints, FirstNodes, TrMax, P)
import red_model as rm
from trans_model import (Trans, Mark, Pred, adm, Adm, Dpt, addBT, PB,
                         bpHeadV, bpHeadT, flatBT, scb_decomps, ZB, reduced,
                         _c2, condI, condIII, condV, condVI)

class TimeoutErr(Exception): pass
def _handler(signum, frame): raise TimeoutErr()
signal.signal(signal.SIGALRM, _handler)

def descending(Q):
    n = len(Q)
    for J0 in range(n):
        for J1 in range(J0, n):
            a0, a1 = entry(Q[J0], 0, 0), entry(Q[J0], 1, 0)
            b0, b1 = entry(Q[J1], 0, 0), entry(Q[J1], 1, 0)
            if not (a0 >= b0 and (a0 != b0 or a1 >= b1)):
                return False
    return True

def hyp(M, m):
    """the article hypothesis for (M, m); assumes Br M != []."""
    br = Br(M)
    J1 = len(br) - 1
    j0p, j1p = Joints(M)[J1], FirstNodes(M)[J1]
    if m < j0p: return True
    return (m == j0p and entry(M, 0, j1p) == entry(M, 1, j1p)
            and descending(br))

def principal(t):
    return len(t[1]) == 1

def branch_of(M, t2):
    if condI(M) or condIII(M) or condV(M): return 1
    if condVI(M): return 2
    if t2 == ZB: return 3
    return 4

class Stat:
    def __init__(s): s.ok = 0; s.bad = 0; s.cex = []
    def rec(s, good, info):
        if good: s.ok += 1
        else:
            s.bad += 1
            if len(s.cex) < 4: s.cex.append(info)
    def __str__(s): return f"{s.ok}/{s.ok+s.bad}"

def check_instance(M, m, S, note):
    j1 = Lng(M) - 1
    Mp = seg(M, m, j1)
    tr = TrMax(M)
    M10 = entry(M, 1, 0)
    # ---- MAIN ----
    TM = Trans(M); TMp = Trans(Mp)
    okm = (principal(TM) and principal(TMp)
           and bpHeadV(TM) == M10 and bpHeadV(TMp) == entry(M, 1, m)
           and bpHeadT(TM) == bpHeadT(TMp))
    S['MAIN'].rec(okm, (M, m, note))
    # ---- I1 trunk ----
    ok1 = all(M[j] == (M10 + j, M10 + j) for j in range(tr + 1))
    S['I1'].rec(ok1, (M, m))
    # ---- I2 adm on trunk ----
    admset = [j for j in range(tr + 1) if adm(M, j)]
    S['I2'].rec(admset == sorted({0, tr}), (M, admset))
    # ---- I3 rightmost parent ----
    j0 = parent(M, 0, j1)
    br = Br(M); J1 = len(br) - 1
    j0p = Joints(M)[J1]
    ok3 = (j0p <= j0 and (m < j0 or entry(M, 0, j1) == entry(M, 1, j1))
           and (m != j0 or j0 < tr))
    S['I3'].rec(ok3, (M, m, j0, j0p, tr))
    if j1 == tr + 1:
        # ---- BASE ----
        okb = M[:tr+1] == diagSeq(M10, M10 + tr)
        S['B1'].rec(okb, (M, m))
        w1, w = M[j1]
        u, up, v = M10, M10 + m, M10 + tr
        def case_of(uu):
            if w1 == v + 1 and uu < w <= v: return 1
            if uu < w1 <= v and w == w1: return 2
            if uu + 1 < w1 <= v and w < w1: return 3
            if uu + 1 == w1 and w < w1: return 4
            return 0
        cM, cMp = case_of(u), (5 if m == tr else case_of(up))
        S.setdefault('BASEDIST', {}).setdefault((cM, cMp), 0)
        S['BASEDIST'][(cM, cMp)] += 1
        S['B2'].rec(cM != 0 and (cMp != 0 or m == tr), (M, m, cM, cMp))
        return
    # ---- STEP ----
    if m == 0: return
    jm1 = Adm(M, j0)
    S['I4'].rec(jm1 > m or jm1 == 0, (M, m, j0, jm1))
    PredM, PredMp = Pred(M), Pred(Mp)
    t1M, t1Mp = Trans(PredM), Trans(PredMp)
    c1M = Mark(PredM, jm1)
    jm1p = Adm(Mp, j0 - m)
    c1Mp = Mark(PredMp, jm1p)
    if jm1 > m:
        S['I5a'].rec(jm1p == jm1 - m, (M, m, jm1, jm1p))
        S['I5b'].rec(c1M == c1Mp, (M, m, jm1))
    elif jm1 == 0:
        S['I6a'].rec(jm1p == 0, (M, m, jm1p))
        S['I6b'].rec(c1M == t1M and c1Mp == t1Mp, (M, m))
        dsM = scb_decomps(t1M, flatBT(c1M))
        dsMp = scb_decomps(t1Mp, flatBT(c1Mp))
        S['I6c'].rec(dsM == [([], [])] and dsMp == [([], [])], (M, m))
    # cond-branch and c2
    t2M, t2Mp = bpHeadT(c1M), bpHeadT(c1Mp)
    bM, bMp = branch_of(M, t2M), branch_of(Mp, t2Mp)
    S['I7a'].rec(bM == bMp, (M, m, bM, bMp))
    c2M = _c2(M, j1, j0, bpHeadV(c1M), t2M)
    c2Mp = _c2(Mp, j1 - m, j0 - m, bpHeadV(c1Mp), t2Mp)
    if jm1 > m:
        S['I7b'].rec(c2M == c2Mp, (M, m))
    elif jm1 == 0:
        okc = (principal(c2M) and principal(c2Mp)
               and bpHeadV(c2M) == M10 and bpHeadV(c2Mp) == entry(M, 1, m)
               and bpHeadT(c2M) == bpHeadT(c2Mp))
        S['I7c'].rec(okc, (M, m))
    # ---- I8 hyp transfer ----
    okp = (Br(PredM) != [] and hyp(PredM, m)
           and PredMp == seg(PredM, m, Lng(PredM) - 1))
    S['I8'].rec(okp, (M, m))

# ------------------------------------------------------------------ pools
def pool_genuine(tlimit, maxlen=14, seed=20260702):
    rng = random.Random(seed)
    seen, out, work = set(), [], []
    for u in range(0, 3):
        for v in range(u + 1, u + 5):
            work.append(diagSeq(u, v))
    t0 = time.time()
    while work and time.time() - t0 < tlimit:
        i = rng.randrange(len(work))
        M = work.pop(i)
        k = tuple(M)
        if k in seen: continue
        seen.add(k)
        out.append(M)
        if Lng(M) > maxlen: continue
        for n in (1, 2, 3):
            Mn = oper(M, n)
            if Lng(Mn) <= maxlen + 4 and tuple(Mn) not in seen:
                work.append(Mn)
    return out

def pool_wide(maxlen=6, maxv=3):
    """exhaustive small sequences, filtered to reduced & monoT below."""
    cols = [(x, y) for x in range(maxv + 1) for y in range(x + 1)]
    out = []
    for a in range(2):
        first = (a, a)
        for L in range(2, maxlen + 1):
            for rest in itertools.product(cols, repeat=L - 1):
                out.append([first] + list(rest))
    return out

R15_DEEP = [
    [(0,0),(1,1),(2,2),(3,3),(3,2),(4,1),(5,2),(6,3),(6,1)],
]

def run_pool(name, Ms, S, tlimit):
    t0 = time.time()
    inst = 0; timeouts = 0
    seen_nonadm = 0
    for M in Ms:
        if time.time() - t0 > tlimit: break
        try:
            signal.alarm(20)
            if not (reduced(M) and monoT(M) and Br(M) != []):
                signal.alarm(0); continue
            j1 = Lng(M) - 1
            j0 = parent(M, 0, j1)
            if not adm(M, j0): seen_nonadm += 1
            ms = [m for m in range(0, j1) if hyp(M, m)]
            signal.alarm(0)
        except (TimeoutErr, Exception):
            signal.alarm(0); timeouts += 1; continue
        for m in ms:
            try:
                signal.alarm(25)
                check_instance(M, m, S, name)
                inst += 1
                signal.alarm(0)
            except TimeoutErr:
                signal.alarm(0); timeouts += 1
            except Exception as e:
                signal.alarm(0)
                S['ERR'].rec(False, (M, m, repr(e)))
    return inst, timeouts, seen_nonadm

def main():
    tA = int(sys.argv[1]) if len(sys.argv) > 1 else 240
    tB = int(sys.argv[2]) if len(sys.argv) > 2 else 240
    keys = ['MAIN','I1','I2','I3','I4','I5a','I5b','I6a','I6b','I6c',
            'I7a','I7b','I7c','I8','B1','B2','ERR']
    for name, mk, tl in (('GENUINE', lambda: pool_genuine(min(tA//3, 90)), tA),
                         ('WIDE', lambda: pool_wide() + R15_DEEP, tB)):
        S = {k: Stat() for k in keys}
        Ms = mk()
        inst, tmo, nonadm = run_pool(name, Ms, S, tl)
        print(f"== pool {name}: {len(Ms)} candidates, {inst} (M,m) instances, "
              f"{tmo} timeouts, {nonadm} non-adm-j0 hosts ==")
        for k in keys:
            s = S[k]
            if s.ok + s.bad:
                print(f"  {k:5s} {s}" + ("" if not s.bad else f"  CEX: {s.cex[:2]}"))
        if 'BASEDIST' in S:
            print(f"  base-case (caseM,caseM') dist: {S['BASEDIST']}")
        sys.stdout.flush()

if __name__ == '__main__':
    main()
