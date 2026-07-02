#!/usr/bin/env python3
"""r15-VX shared lib for the A28 index-shift propagation / exchange-shape audit.

Components (all previously validated in round 14, consolidated here):
  * operB / domB / xseq / numBT / multBT  -- Buchholz-side fundamental sequence,
    faithful to pss_paper.thy 744-777 in the A23 form (tbvIdx branch), the exact
    model _r14_s5_scbdec.py validated (2295/2295 vs the proven closed form).
  * lessBT / leBT -- pss_paper.thy 629-637, the model _r14_f7_dispatcher_check.py
    used for the 6439-pair descent validation.
  * condII / condIV (trans_model has I/III/V/VI).
  * internals(M) -- the SS 7.3 Trans-recursion locals (j1 j0 jm1 t1 c1 v t2 c2
    s1 b1 leftDj0 t3 t4), faithful to pss_paper.thy 1145-1176.
  * memoized Trans/Mark (patched INTO trans_model so inner recursion hits the
    memo; pure functions, semantics unchanged).
  * genuine ST_PS pools: diagSeq seeds closed under oper (the ST_PS inductive
    definition, pss_defs.thy 439-441); mono_hosts adds mono P-components of
    multi members (in ST_PS by m_6_7_standard_P_components).
  * SIGALRM guard helpers.
"""
import sys, os, signal
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, P, monoT, zeroT, multiT, seg, diagSeq,
                       parent, hasParent, oper, fmt)
import red_model as rm
import trans_model as tm
from trans_model import (Dpt, addBT, PB, SigmaB, bpHeadV, bpHeadT, flatBT,
                         unflatBT, scb_decomps, ZB, adm, Adm, Pred, reduced,
                         condI, condIII, condV, condVI, isPTB_str)

INF = float('inf')

# ---------------- SIGALRM guard ----------------
class TO(Exception): pass
def _alrm(sig, frm): raise TO()
signal.signal(signal.SIGALRM, _alrm)

SKIP = object()   # sentinel: timed out / diverged (outside model reach)

def guarded(f, *a, budget=10):
    signal.alarm(budget)
    try:
        r = f(*a)
        signal.alarm(0)
        return r
    except (TO, RecursionError, RuntimeError):
        signal.alarm(0)
        return SKIP
    finally:
        signal.alarm(0)

# ---------------- memoized Trans/Mark (patched into trans_model) ----------------
_tmemo, _mmemo = {}, {}
_Trans0, _Mark0 = tm.Trans, tm.Mark

def Trans(M, depth=0):
    k = tuple(M)
    r = _tmemo.get(k)
    if r is None:
        r = _Trans0(M, depth)
        _tmemo[k] = r
    return r

def Mark(M, m, depth=0):
    k = (tuple(M), m)
    r = _mmemo.get(k)
    if r is None:
        r = _Mark0(M, m, depth)
        _mmemo[k] = r
    return r

tm.Trans, tm.Mark = Trans, Mark    # inner recursive calls hit the memo

# ---------------- missing cond predicates ----------------
def condII(M):
    j1 = Lng(M) - 1
    jp = parent(M, 0, j1)
    return jp is not None and entry(M, 1, j1) == 0 and not adm(M, jp)

def condIV(M):
    j1 = Lng(M) - 1
    jp = parent(M, 0, j1)
    return (jp is not None and entry(M, 1, j1) > 0
            and entry(M, 1, jp) >= entry(M, 1, j1) and not adm(M, jp))

# ---------------- Buchholz ordering (pss_paper.thy 629-637) ----------------
def lessBP(p, q):
    return p[1] < q[1] or (p[1] == q[1] and lessBT(p[2], q[2]))

def lessBT(a, b):
    ps, qs = a[1], b[1]
    if not ps: return bool(qs)
    if not qs: return False
    return lessBP(ps[0], qs[0]) or (ps[0] == qs[0]
                                    and lessBT(('T', ps[1:]), ('T', qs[1:])))

def leBT(a, b): return a == b or lessBT(a, b)

# ---------------- operB model (pss_paper.thy 744-777, A23 form) ----------------
def numBT(n): return ('T', [('D', 0, ZB)] * n)
def numNat(z): return len(z[1])

def multBT(a, n):
    out = ZB
    for _ in range(n): out = addBT(out, a)
    return out

def domB(a):
    ps = a[1]
    if not ps: return 'EMPTY'
    if len(ps) == 1:
        _, v, b = ps[0]
        if b == ZB:
            if v == 0: return 'ZERO'          # {0} = {Trm []}
            if v == INF: return 'NAT'
            return ('TB', v - 1)
        db = domB(b)
        if db == 'ZERO': return 'NAT'
        if isinstance(db, tuple) and db[0] == 'TB' and v <= db[1]: return 'NAT'
        return db
    return domB(('T', [ps[-1]]))

def operB(a, z):
    ps = a[1]
    if not ps: return ZB
    if len(ps) == 1:
        _, v, b = ps[0]
        if b == ZB:
            if v == 0: return ZB
            if v == INF: return Dpt(numNat(z) + 1, ZB)
            return z
        db = domB(b)
        if db == 'ZERO':
            return multBT(Dpt(v, operB(b, ZB)), numNat(z) + 1)
        if isinstance(db, tuple) and db[0] == 'TB' and v <= db[1]:
            return Dpt(v, xseq(b, db[1], numNat(z)))
        return Dpt(v, operB(b, z))
    return addBT(('T', ps[:-1]), operB(('T', [ps[-1]]), z))

def xseq(b, u, i):
    if i == 0: return Dpt(u, ZB)
    return operB(b, Dpt(u, xseq(b, u, i - 1)))

def operB_iter0(t, k):
    """t[0]^k -- k-fold iterate of (lambda a. operB a (numBT 0))."""
    for _ in range(k): t = operB(t, numBT(0))
    return t

# ---------------- Trans-recursion internals (pss_paper.thy 1145-1176) ----------------
def internals(M):
    """Locals of the mono/t1!=0 branch of the Trans recursion for reduced mono M.
    Returns None if the branch does not apply (M not reduced/mono, j1=0, t1=0)."""
    if not reduced(M) or not monoT(M): return None
    j1 = Lng(M) - 1
    if j1 == 0: return None
    t1 = Trans(Pred(M))
    if t1 == ZB: return None
    j0 = parent(M, 0, j1)
    jm1 = Adm(M, j0)
    c1 = Mark(Pred(M), jm1)
    v = bpHeadV(c1); t2 = bpHeadT(c1)
    Pt2 = PB(t2)
    if Pt2:
        J1b = len(Pt2) - 1
        pj = Pt2[J1b]
        leftDj0 = (bpHeadV(pj) == entry(M, 1, j0))
        t3 = SigmaB(Pt2[:J1b]) if leftDj0 else t2
        t4 = bpHeadT(pj) if leftDj0 else t2
    else:
        leftDj0 = False
        t3 = t4 = ZB
    c2 = tm._c2(M, j1, j0, v, t2)
    ds1 = scb_decomps(t1, flatBT(c1))
    s1, b1 = (ds1[0] if ds1 else (None, None))
    return dict(j1=j1, j0=j0, jm1=jm1, t1=t1, c1=c1, v=v, t2=t2, c2=c2,
                leftDj0=leftDj0, t3=t3, t4=t4, s1=s1, b1=b1, n_ds1=len(ds1))

# ---------------- principal-pair scb search (p_8_4_oper_basic (3)) ----------------
def principal_pair_exists(t_small, t_big):
    """EX s c1 c2 b: c1,c2 principal, lessBT c1 c2,
       scb_decomp t_small s (flat c1) b  and  scb_decomp t_big s (flat c2) b."""
    f1, f2 = flatBT(t_small), flatBT(t_big)
    n1, n2 = len(f1), len(f2)
    # b must consist of ')' only, hence a run of trailing ')' of f1 (and of f2)
    tr1 = 0
    while tr1 < n1 and f1[n1 - 1 - tr1] == ')': tr1 += 1
    tr2 = 0
    while tr2 < n2 and f2[n2 - 1 - tr2] == ')': tr2 += 1
    cp = 0                       # common-prefix length of f1/f2 (s must fit here)
    while cp < min(n1, n2) and f1[cp] == f2[cp]: cp += 1
    for kb in range(min(tr1, tr2) + 1):
        for i in range(min(n1 - kb, cp + 1)):
            if not (isinstance(f1[i], tuple) and f1[i][0] == 'D'):
                continue
            if i >= n2 - kb: break
            c1f = f1[i:n1 - kb]
            c2f = f2[i:n2 - kb]
            if not (isPTB_str(c1f) and isPTB_str(c2f)): continue
            c1t = unflatBT(c1f); c2t = unflatBT(c2f)
            if len(c1t[1]) != 1 or len(c2t[1]) != 1: continue
            if lessBT(c1t, c2t):
                return (f1[:i], c1t, c2t, [')'] * kb)
    return None

# ---------------- genuine ST_PS pools ----------------
def gen_pool(maxlen=9, maxn=4, maxseed=3, cap=6000, oper_budget=3):
    """BFS closure of diagSeq seeds under oper = literal ST_PS members."""
    seen = set(); frontier = []
    for u in range(maxseed):
        for v in range(u, u + maxseed + 1):
            M = tuple(diagSeq(u, v))
            if M not in seen:
                seen.add(M); frontier.append(list(M))
    pool = list(frontier)
    while frontier and len(pool) < cap:
        nxt = []
        for M in frontier:
            if Lng(M) <= 1: continue
            for n in range(1, maxn + 1):
                N = guarded(oper, M, n, budget=oper_budget)
                if N is SKIP: continue
                if Lng(N) > maxlen: continue
                t = tuple(N)
                if t not in seen:
                    seen.add(t); nxt.append(N); pool.append(N)
                    if len(pool) >= cap: break
            if len(pool) >= cap: break
        frontier = nxt
    return pool

def mono_hosts(pool):
    """Mono ST_PS hosts: mono pool members + mono P-components of multi members
    (ST_PS by m_6_7_standard_P_components).  Deduplicated."""
    seen = set(); hosts = []
    for M in pool:
        cands = [M] if monoT(M) else ([c for c in P(M) if monoT(c)] if multiT(M) else [])
        for c in cands:
            t = tuple(c)
            if t not in seen:
                seen.add(t); hosts.append(c)
    return hosts

# ---------------- counters / reporting ----------------
class Tally:
    """Per-conclusion pass/fail/skip counters with minimal-CEX tracking."""
    def __init__(self):
        self.ok = {}; self.tot = {}; self.skip = {}; self.cex = {}
    def add(self, key, verdict, inst=None):
        if verdict is SKIP or verdict is None:
            self.skip[key] = self.skip.get(key, 0) + 1
            return
        self.tot[key] = self.tot.get(key, 0) + 1
        if verdict:
            self.ok[key] = self.ok.get(key, 0) + 1
        elif inst is not None:
            M, n = inst
            sz = (Lng(M), max(max(a, b) for (a, b) in M), n)
            if key not in self.cex or sz < self.cex[key][0]:
                self.cex[key] = (sz, inst)
    def report(self, hdr=''):
        lines = []
        if hdr: lines.append(hdr)
        for key in sorted(set(list(self.tot) + list(self.skip))):
            ok = self.ok.get(key, 0); tot = self.tot.get(key, 0)
            sk = self.skip.get(key, 0)
            tag = 'PASS' if ok == tot and tot > 0 else ('FAIL' if tot > 0 else 'n/a ')
            line = f'  [{tag}] {key}: {ok}/{tot}' + (f'  (skip {sk})' if sk else '')
            if key in self.cex:
                (_, (M, n)) = self.cex[key]
                try:
                    line += f'  minCEX M={fmt(M)} n={n}'
                except Exception:
                    line += f'  minCEX {M!r} n={n}'
            lines.append(line)
        return '\n'.join(lines)
