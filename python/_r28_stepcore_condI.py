#!/usr/bin/env python3
r"""r28-STEPCORE: deep validation of the condI j0>0 marking-nesting closed form
(the lhsCF residual of m_8_1_stepT_j0pos_of_lhs_closed) AND of every internal
identity of the planned Isar induction step, over brute-force straddle hosts
(Lng 3..6) plus DEEP hosts (Lng 7..10, random reduced/monoT/condI/j0>0).

Notation (host M, j1 = Lng-1, j0 = parent M 0 j1 > 0, w = j1-j0):
  jm1  = Adm M j0 (= j0, since condI => adm j0)
  j0'  = parent M 0 j0,  jm1' = Adm M j0'
  c1   = Mark(Pred M, jm1);   v0 = entry M 1 j0  (c1 = D_v0 t2)
  caseA <=> jm1' = j0' or entry M 1 j0' + 1 = v0
  caseB <=> jm1' < j0' and entry M 1 j0' >= v0     (exhaustive+exclusive?)
  X_n   = caseA: D_va(tau + c1*n)                     [va = entry M 1 jm1']
          caseB: D_va(t3 + D_vb(t4 + c1*n))           [vb = entry M 1 j0']
  (s',b') = the scb of Trans(Pred M) at flat(Mark(Pred M, jm1'))

INVARIANT INV(n), n=1..NMAX:
  (i)  Mark(M[n], jm1') == X_n
  (ii) flat(Trans(M[n])) == s' + flat(X_n) + b'
STEP internals (n>=2), N = M[n][0:idx+1], idx = j0+(n-1)w:
  (a) Pred N == M[n-1] (list eq)     (b) N reduced+monoT
  (c) transJ0 N == j0', transJm1 N == jm1'
  (d) caseA -> N in condI/III/V ; caseB -> c2-4th-branch w/ leftDj0
  (e) Trans N == unflat(s' + flat(c2N)) + b'), c2N as designed
  (f) w>=2: Mark(M[n], idx) == c1  and  M[n][idx:] == M[j0:j1] (block eq)
      w==1: t2 == 0 (c1 = D_v0 0)
  (g) (M[n], jm1') in Marked ;  le0 M jm1' j0'
  (h) jm1'==0 -> (s',b') == ([],[])
Also: hasParent M 0 j0 (j0>0), reduced coefficient bound v0 <= e(j0')+1.
"""
import sys, os, itertools, random, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import trans_model as tm
from red_model import (Lng, parent, oper, fmt, entry, monoT, zeroT, reduced,
                       hasParent, Adm, adm, le0, marked, seg, Pred)
from trans_model import (flatBT, Dpt, addBT, ZB, unflatBT, scb_decomps,
                         bpHeadV, bpHeadT, PB, SigmaB,
                         condI as tcondI, condIII as tcondIII,
                         condV as tcondV, condVI as tcondVI)

_Torig, _Morig = tm.Trans, tm.Mark
_Tc, _Mc = {}, {}
def _Tmemo(M, depth=0):
    k = tuple(M)
    r = _Tc.get(k)
    if r is None:
        r = _Torig(list(M)); _Tc[k] = r
    return r
def _Mmemo(M, m, depth=0):
    k = (tuple(M), m)
    r = _Mc.get(k)
    if r is None:
        r = _Morig(list(M), m); _Mc[k] = r
    return r
tm.Trans, tm.Mark = _Tmemo, _Mmemo
def T(M): return tm.Trans(list(M))
def MK(M, m): return tm.Mark(list(M), m)
def pr(*a): print(*a, flush=True)

def multBT(t, n):
    r = ZB
    for _ in range(n): r = addBT(r, t)
    return r

def isj(M):
    if Lng(M) < 3 or zeroT(M) or entry(M, 1, Lng(M) - 1) != 0: return False
    if not monoT(M): return False
    j1 = Lng(M) - 1
    if not hasParent(M, 0, j1): return False
    j0 = parent(M, 0, j1)
    if not (j0 is not None and j1 > 1 and tcondI(M) and j0 > 0): return False
    return reduced(M)

def gen_brute():
    hosts = []
    for L in range(3, 7):
        n = 0; checked = 0
        cols = [(a, b) for a in range(min(L,4)+1) for b in range(min(L,4)+1)]
        for tail in itertools.product(cols, repeat=L-1):
            checked += 1
            if checked > (300_000 if L < 6 else 700_000): break
            M = [(0, 0)] + list(tail)
            if entry(M, 1, L-1) != 0: continue
            if not isj(M): continue
            hosts.append(M); n += 1
            if n >= 70: break
    return hosts

def _prefilter(M):
    L = Lng(M)
    if zeroT(M) or entry(M, 1, L-1) != 0: return None
    if not monoT(M): return None
    j1 = L - 1
    if not hasParent(M, 0, j1): return None
    j0 = parent(M, 0, j1)
    if j0 is None or j1 <= 1 or j0 == 0: return None
    if not tcondI(M): return None
    if not hasParent(M, 0, j0): return None
    return j0

def gen_deep(seed, budget=120.0, count=45, lo=7, hi=10, want_caseB=False):
    rnd = random.Random(seed)
    hosts = []; t0 = time.time()
    while time.time() - t0 < budget and len(hosts) < count:
        L = rnd.randint(lo, hi)
        M = [(0, 0)]
        for j in range(1, L):
            a = rnd.randint(0, min(j, 4)); b = rnd.randint(0, 3)
            M.append((a, b))
        M[-1] = (M[-1][0], 0)
        j0 = _prefilter(M)
        if j0 is None: continue
        if want_caseB:
            j0p = parent(M, 0, j0); jm1p = Adm(M, j0p)
            if not (jm1p < j0p and entry(M, 1, j0p) >= entry(M, 1, j0)):
                continue
        if not reduced(M): continue
        hosts.append(M)
    return hosts

NMAX = 5

def run(hosts, tag):
    stats = {k: 0 for k in
             ('host', 'excl_bad', 'exh_bad', 'hp_bad', 'coefbad',
              'caseA', 'caseB', 'init_bad', 'sb_none', 'sb_multi',
              'i_bad', 'ii_bad', 'a_bad', 'b_bad', 'c_bad', 'd_bad',
              'e_bad', 'f_bad', 'g_bad', 'h_bad', 'jm1p0', 'w1',
              'exch_bad', 'invn')}
    cex = []
    for M in hosts:
        stats['host'] += 1
        j1 = Lng(M) - 1; j0 = parent(M, 0, j1); w = j1 - j0
        if w == 1: stats['w1'] += 1
        if not hasParent(M, 0, j0):
            stats['hp_bad'] += 1; cex.append(('hp', fmt(M))); continue
        j0p = parent(M, 0, j0); jm1p = Adm(M, j0p)
        v0 = entry(M, 1, j0); va = entry(M, 1, jm1p); vb = entry(M, 1, j0p)
        if jm1p == 0: stats['jm1p0'] += 1
        # coefficient bound
        if not v0 <= vb + 1:
            stats['coefbad'] += 1; cex.append(('coef', fmt(M))); continue
        caseA = (jm1p == j0p) or (vb + 1 == v0)
        caseB = (jm1p < j0p) and (vb >= v0)
        if caseA and caseB and not ((jm1p == j0p or vb+1 == v0) and caseB):
            pass
        if caseA and caseB:
            # possible overlap? vb+1==v0 and jm1p<j0p and vb>=v0 impossible;
            # jm1p==j0p and vb>=v0: exclusive check fails only if both guards
            stats['excl_bad'] += 1  # overlap: jm1p==j0p & vb>=v0 & vb+1==v0? record
        if not (caseA or caseB):
            stats['exh_bad'] += 1; cex.append(('exh', fmt(M))); continue
        if caseA: stats['caseA'] += 1
        else: stats['caseB'] += 1
        c1 = MK(Pred(M), Adm(M, j0)); t2 = bpHeadT(c1)
        mpj = MK(Pred(M), jm1p)
        # INIT forms + extract tau / t3,t4
        if caseA:
            # mpj = D_va(tau + c1): last principal of body must be c1's principal
            ok = (len(mpj[1]) == 1 and mpj[1][0][1] == va
                  and len(mpj[1][0][2][1]) >= 1
                  and mpj[1][0][2][1][-1:] == c1[1])
            if not ok:
                stats['init_bad'] += 1; cex.append(('initA', fmt(M))); continue
            tau = ('T', mpj[1][0][2][1][:-1])
        else:
            ok = (len(mpj[1]) == 1 and mpj[1][0][1] == va
                  and len(mpj[1][0][2][1]) >= 1)
            inner = ('T', mpj[1][0][2][1][-1:])
            ok = ok and (inner[1][0][1] == vb
                         and inner[1][0][2][1][-1:] == c1[1])
            if not ok:
                stats['init_bad'] += 1; cex.append(('initB', fmt(M))); continue
            t3 = ('T', mpj[1][0][2][1][:-1])
            t4 = ('T', inner[1][0][2][1][:-1])
        def Xn(n):
            if caseA: return Dpt(va, addBT(tau, multBT(c1, n)))
            return Dpt(va, addBT(t3, Dpt(vb, addBT(t4, multBT(c1, n)))))
        # (s',b')
        decs = scb_decomps(T(Pred(M)), flatBT(mpj))
        if len(decs) == 0:
            stats['sb_none'] += 1; cex.append(('sbnone', fmt(M))); continue
        if len(decs) > 1:
            stats['sb_multi'] += 1; cex.append(('sbmulti', fmt(M)))
        sp, bp = decs[0]
        if jm1p == 0 and (sp, bp) != ([], []):
            stats['h_bad'] += 1; cex.append(('h', fmt(M)))
        # w=1 check (f)
        if w == 1 and t2 != ZB:
            stats['f_bad'] += 1; cex.append(('f-w1', fmt(M)))
        allok = True
        for n in range(1, NMAX + 1):
            Mn = oper(M, n)
            # (i)
            if MK(Mn, jm1p) != Xn(n):
                stats['i_bad'] += 1; cex.append(('i', fmt(M), n)); allok = False; break
            # (ii)
            if flatBT(T(Mn)) != sp + flatBT(Xn(n)) + bp:
                stats['ii_bad'] += 1; cex.append(('ii', fmt(M), n)); allok = False; break
            # (g)
            if not (marked(Mn, jm1p) and le0(M, jm1p, j0p)):
                stats['g_bad'] += 1; cex.append(('g', fmt(M), n)); allok = False; break
            if n < 2: continue
            idx = j0 + (n - 1) * w
            N = Mn[:idx + 1]
            # (a)
            if N[:-1] != oper(M, n - 1):
                stats['a_bad'] += 1; cex.append(('a', fmt(M), n)); allok = False; break
            # (b)
            if not (reduced(N) and monoT(N)):
                stats['b_bad'] += 1; cex.append(('b', fmt(M), n)); allok = False; break
            # (c)
            jN1 = Lng(N) - 1
            if not (hasParent(N, 0, jN1) and parent(N, 0, jN1) == j0p
                    and Adm(N, j0p) == jm1p):
                stats['c_bad'] += 1; cex.append(('c', fmt(M), n)); allok = False; break
            # (d)+(e): compute c2N per design and check Trans N
            c1N = Xn(n - 1)
            if caseA:
                okd = tcondI(N) or tcondIII(N) or tcondV(N)
                c2N = Dpt(va, addBT(addBT(tau, multBT(c1, n - 1)),
                                    Dpt(v0, ZB)))
            else:
                okd = not (tcondI(N) or tcondIII(N) or tcondV(N) or tcondVI(N))
                t2N = bpHeadT(c1N)
                okd = okd and t2N != ZB
                pj = PB(t2N)[-1] if t2N[1] else None
                okd = okd and pj is not None and bpHeadV(pj) == vb
                c2N = Dpt(va, addBT(t3, Dpt(vb, addBT(addBT(t4, multBT(c1, n - 1)),
                                                      Dpt(v0, ZB)))))
            if not okd:
                stats['d_bad'] += 1; cex.append(('d', fmt(M), n)); allok = False; break
            if flatBT(T(N)) != sp + flatBT(c2N) + bp:
                stats['e_bad'] += 1; cex.append(('e', fmt(M), n)); allok = False; break
            # (f)
            if w >= 2:
                if MK(Mn, idx) != c1 or Mn[idx:] != M[j0:j1]:
                    stats['f_bad'] += 1; cex.append(('f', fmt(M), n)); allok = False; break
        if allok: stats['invn'] += 1
    pr(f"[{tag}] hosts={stats['host']} caseA={stats['caseA']} caseB={stats['caseB']} "
       f"w1={stats['w1']} jm1p0={stats['jm1p0']} ALL_OK={stats['invn']}")
    bad = {k: v for k, v in stats.items() if v and k not in
           ('host', 'caseA', 'caseB', 'w1', 'jm1p0', 'invn')}
    pr(f"[{tag}] bad={bad if bad else 'NONE'}")
    if cex: pr(f"[{tag}] CEX(first 10):", cex[:10])
    return bad

def main():
    t0 = time.time()
    hb = gen_brute()
    pr(f"brute hosts: {len(hb)} ({round(time.time()-t0,1)}s)")
    bad1 = run(hb, 'BRUTE 3-6')
    t1 = time.time()
    hcb = gen_deep(7, budget=100.0, count=50, lo=5, hi=9, want_caseB=True)
    pr(f"caseB hosts: {len(hcb)} Lng={sorted(set(Lng(M) for M in hcb))} "
       f"({round(time.time()-t1,1)}s)")
    bad2 = run(hcb, 'CASEB 5-9')
    t2 = time.time()
    hd = gen_deep(42, budget=100.0, count=45) + gen_deep(99, budget=100.0, count=45)
    pr(f"deep hosts: {len(hd)} Lng={sorted(set(Lng(M) for M in hd))} "
       f"({round(time.time()-t2,1)}s)")
    bad3 = run(hd, 'DEEP 7-10')
    pr(f"total_s={round(time.time()-t0,1)}  VERDICT="
       + ("PASS" if not bad1 and not bad2 and not bad3 else "FAIL"))

if __name__ == '__main__':
    main()
