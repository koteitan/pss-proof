#!/usr/bin/env python3
# r29a-CONDII probe: the condII (kind-0, non-adm j0) marking-nesting closed form.
# EMPIRICAL-FIRST for the c2sx_ front:
#  [H] host basics: w>=2, j0>0, jm1<j0, run arithmetic, t2 != 0, c1 = D_va t2
#  [W] THE TAIL BRICK: W := Trans(seg M j0 (j1-1)) == Dpt(v0, t4)  (per leftDj0 branch)
#  [I] double-track invariant for n=1..NMAX:
#        Mark(M[n], jm1) == X_n := D_va(t3 + (D_v0 t4) x cnt_n), cnt_n = n (leftDj0) / n-1
#        Trans(M[n]) == s1' X_n b1'  with (s1',b1') = scb of c1 in t1 (FIXED)
#  [N] N-facts at n>=2: Pred N = M[n-1]; parent(N,0,idx)=j0-1; Adm(N,j0-1)=jm1;
#        N reduced+mono+condV; entry(N,1,idx)=v0; tail slice = seg M j0 (j1-1);
#        Marked(M[n], idx); Marked(M[n], jm1); Mark(M[n], idx) == W
#  [R] route probe for W: Ltil := Red(seg M jm1 (j1-1)), R := Red(seg M jm1 j1):
#        Ltil == Pred R?; Joints(Ltil)!last == d?; per-branch guard class of Ltil
#        (cfbx_reg d Ltil: d < Joints!last | d = Joints!last & diag & desc | trunk);
#        entry(Ltil,1,d) == v0; Trans(seg Ltil d end) == W-shape D_v0(t1'+t2')
#  [B] brute-force straddle: same checks on RT_PS-not-ST hosts (expect W may fail)
import sys, time, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4a/python')
from red_model import (Lng, entry, monoT, reduced, seg, parent, Adm, adm, nadm,
                       oper, diagSeq, le0, le1, leR, Br, FirstNodes, Joints, Red,
                       hasParent, fmt, TrMax, marked, Pred, is_standard)
import trans_model as tm
from trans_model import Dpt, ZB, bpHeadT, bpHeadV, addBT, PB, SigmaB, flatBT, unflatBT

def pr(*a): print(*a, flush=True)

_tmemo = {}
def Ts(M):
    t = tuple(M)
    if t in _tmemo: return _tmemo[t]
    try: v = tm.Trans(M)
    except Exception: v = None
    _tmemo[t] = v
    return v

_mkmemo = {}
def Mk(M, m):
    t = (tuple(M), m)
    if t in _mkmemo: return _mkmemo[t]
    try: v = tm.Mark(M, m)
    except Exception: v = None
    _mkmemo[t] = v
    return v

_rmemo = {}
def RedM(M):
    t = tuple(M)
    if t in _rmemo: return _rmemo[t]
    v = Red(M); _rmemo[t] = v
    return v

def is_reduced(M): return RedM(list(M)) == list(M)

def mult(t, n): return ('T', t[1]*n)

def transJ0(M): return parent(M, 0, Lng(M)-1)

def condII(M):
    n = Lng(M)
    if n < 3: return False
    if not hasParent(M, 0, n-1): return False
    j0 = transJ0(M)
    return entry(M,1,n-1) == 0 and not adm(M, j0)

def genuine(M):
    if not condII(M): return False
    if Lng(M)-1 <= 1: return False
    if not monoT(M): return False
    return is_reduced(M)

def descending(bs):
    for J0 in range(len(bs)):
        for J1 in range(J0, len(bs)):
            a0, b0 = bs[J0][0]; a1, b1 = bs[J1][0]
            if not (a0 >= a1 and (a0 != a1 or b0 >= b1)): return False
    return True

def guard_class(R, d):
    # cfbx_reg d R (the m < j0' | m = j0' diag desc branch) or trunk
    if not (is_reduced(R) and monoT(R)): return 'RnotRedMono'
    b = Br(R)
    if not b:
        return 'trunk' if TrMax(R) == Lng(R)-1 else 'BrEmpty-nontrunk'
    jl = Joints(R)[len(b)-1]
    if jl is None: return 'jointNone'
    if d < jl: return 'reg-lt'
    if d == jl:
        fn = FirstNodes(R)[len(b)-1]
        if entry(R,0,fn) == entry(R,1,fn) and descending(b): return 'reg-eqdiag'
        return 'eq-BAD'
    return 'joint-below-d'

NMAX = 4
LENCAP = 34

def check_host(M, st, exs, deepn=True):
    n0 = Lng(M); j1 = n0-1; j0 = transJ0(M); jm1 = Adm(M, j0)
    d = j0 - jm1; w = j1 - j0
    va = entry(M,1,jm1); v0 = entry(M,1,j0)
    st['hosts'] += 1
    if n0 >= 10: st['deep'] += 1
    st['runs'][d] = st['runs'].get(d,0)+1
    st['ws'][w] = st['ws'].get(w,0)+1
    def bad(tag, *info):
        st['bad'][tag] = st['bad'].get(tag,0)+1
        if len(exs) < 30: exs.append((tag, fmt(M)) + info)
    # [H] host basics
    if not (w >= 2): bad('H-w2', w)
    if not (j0 > 0): bad('H-j0pos')
    if not (jm1 < j0): bad('H-jm1lt')
    if not (entry(M,1,j0-1)+1 == entry(M,1,j0)): bad('H-e1run')
    if not (entry(M,0,j0-1)+1 == entry(M,0,j0)): bad('H-e0run')
    if v0 <= 0: bad('H-v0pos')
    t1 = Ts(Pred(M))
    if t1 is None or t1 == ZB: bad('H-t1'); return
    c1 = Mk(Pred(M), jm1)
    if c1 is None: bad('H-c1None'); return
    if not (len(c1[1]) == 1 and bpHeadV(c1) == va): bad('H-c1shape', c1); return
    t2 = bpHeadT(c1)
    if t2 == ZB: bad('H-t2zero'); return
    Pt2 = PB(t2); J1b = len(Pt2)-1; pj = Pt2[J1b]
    ldj = (bpHeadV(pj) == v0)
    t3 = SigmaB(Pt2[:J1b]) if ldj else t2
    t4 = bpHeadT(pj) if ldj else t2
    st['ldj'][ldj] = st['ldj'].get(ldj,0)+1
    # [W] the tail brick
    W = Ts(seg(M, j0, j1-1))
    if W is None: bad('W-None'); return
    okW = (W == Dpt(v0, t4))
    st['Wok'][(ldj, okW)] = st['Wok'].get((ldj, okW),0)+1
    if not okW: bad('W-MAIN', 'ldj=%s'%ldj, 'W=%r'%(W,), 't4=%r'%(t4,), j0, jm1)
    # transfer check (expected: holds iff not ldj)
    tr = (bpHeadT(W) == t2)
    st['W2n'][(ldj, tr)] = st['W2n'].get((ldj, tr),0)+1
    # [I] invariant; the fixed scb pair
    ds = tm.scb_decomps(t1, flatBT(c1))
    if not ds: bad('I-noscb'); return
    s1p, b1p = ds[0]
    prevMn = None
    for n in range(1, NMAX+1):
        Mn = oper(M, n)
        if Lng(Mn) > LENCAP: break
        cnt = n if ldj else n-1
        Xn = Dpt(va, addBT(t3, mult(Dpt(v0,t4), cnt)))
        mk = Mk(Mn, jm1)
        if mk != Xn: bad('I-mark', n, 'ldj=%s'%ldj, 'mk=%r'%(mk,), 'Xn=%r'%(Xn,))
        tn = Ts(Mn)
        if tn is None: bad('I-TransNone', n); continue
        try:
            rhs = unflatBT(list(s1p) + flatBT(Xn) + list(b1p))
        except Exception:
            rhs = None
        if tn != rhs: bad('I-trans', n, 'ldj=%s'%ldj)
        # [N] facts
        if n >= 2:
            idx = j0 + (n-1)*w
            N = seg(Mn, 0, idx)
            if Pred(N) != oper(M, n-1): bad('N-pred', n)
            if not (is_reduced(N) and monoT(N)): bad('N-redmono', n)
            if not (hasParent(N,0,idx) and parent(N,0,idx) == j0-1): bad('N-parent', n)
            if Adm(N, j0-1) != jm1: bad('N-adm', n, Adm(N,j0-1), jm1)
            if entry(N,1,idx) != v0: bad('N-e1idx', n)
            # condV of N
            cV = (entry(N,1,idx) > 0 and entry(N,1,j0-1)+1 == entry(N,1,idx)
                  and (j0-1)+1 < idx)
            if not cV: bad('N-condV', n)
            if seg(Mn, idx, Lng(Mn)-1) != seg(M, j0, j1-1): bad('N-tail', n)
            if not marked(Mn, idx): bad('N-mkidx', n)
            if not marked(Mn, jm1): bad('N-mkjm1', n)
            mki = Mk(Mn, idx)
            if mki != W: bad('N-markW', n, 'mki=%r'%(mki,))
    # [R] route probe
    Lt = RedM(seg(M, jm1, j1-1))
    R = RedM(seg(M, jm1, j1))
    if Lt != Pred(R): bad('R-predR')
    if not le0(M, j0, j1-1): bad('R-le0j0')
    if not le0(M, jm1, j1-1): bad('R-le0jm1')
    g = guard_class(Lt, d)
    st['guard'][(ldj, g)] = st['guard'].get((ldj, g),0)+1
    if entry(Lt,1,d) != v0: bad('R-e1d')
    bL = Br(Lt)
    jlast = Joints(Lt)[len(bL)-1] if bL else None
    st['jld'][(ldj, jlast == d)] = st['jld'].get((ldj, jlast == d),0)+1
    # R-side (slice to j1) m84 structure
    bR = Br(R)
    okm84 = bool(bR) and Joints(R)[len(bR)-1] == d and FirstNodes(R)[len(bR)-1] == Lng(R)-1
    if not okm84: bad('R-m84')
    # W in Ltil coordinates
    WL = Ts(seg(Lt, d, Lng(Lt)-1))
    st['WL'][(ldj, WL == W)] = st['WL'].get((ldj, WL == W),0)+1

def newst():
    return dict(hosts=0, deep=0, runs={}, ws={}, ldj={}, Wok={}, W2n={}, guard={},
                jld={}, WL={}, bad={})

def report(tag, st, exs):
    pr(f"[{tag}] hosts={st['hosts']} deep={st['deep']}")
    pr(f"[{tag}] runs={st['runs']} ws={st['ws']} ldj={st['ldj']}")
    pr(f"[{tag}] Wok={st['Wok']}")
    pr(f"[{tag}] W2n(transfer)={st['W2n']}")
    pr(f"[{tag}] guard={st['guard']}")
    pr(f"[{tag}] jointlast==d: {st['jld']}  WL-match={st['WL']}")
    pr(f"[{tag}] BAD={st['bad']}")
    for e in exs: pr("   ", e)

def gen_oper(maxlen, maxn, maxseed, cap, budget):
    t0=time.time(); seen=set(); frontier=[]
    for u in range(maxseed):
        for v in range(u, u+maxseed+2):
            M=tuple(diagSeq(u,v))
            if Lng(M)<=maxlen and M not in seen: seen.add(M); frontier.append(list(M))
    pool=list(frontier)
    while frontier and len(pool)<cap and time.time()-t0<budget:
        nxt=[]
        for M in frontier:
            if Lng(M)<=1: continue
            for n in range(1, maxn+1):
                N=oper(M,n)
                if Lng(N)>maxlen: continue
                t=tuple(N)
                if t not in seen: seen.add(t); nxt.append(N); pool.append(N)
            if len(pool)>=cap or time.time()-t0>budget: break
        frontier=nxt
    return pool

def main():
    t0=time.time()
    pool = gen_oper(maxlen=13, maxn=4, maxseed=4, cap=30000, budget=180)
    pr(f"[genA] pool={len(pool)} t={time.time()-t0:.0f}s")
    st=newst(); exs=[]
    nge=0
    for M in pool:
        if genuine(M):
            nge+=1
            check_host(M, st, exs)
    pr(f"[genA] genuineCondII={nge} t={time.time()-t0:.0f}s")
    report('OPER', st, exs)

    # brute straddle: RT_PS (reduced+mono+condII) but NOT restricted to pool/ST
    stB=newst(); exsB=[]
    budget=240.0; t1=time.time(); hit=False
    cells=[(a,b) for a in range(4) for b in range(4)]
    for L in range(4, 8):
        if time.time()-t1>budget: hit=True; break
        for tup in itertools.product(cells, repeat=L-1):
            if time.time()-t1>budget: hit=True; break
            M=[(0,0)]+list(tup)
            if not genuine(M): continue
            check_host(M, stB, exsB)
        pr(f"[BRUTE] L={L} done hosts={stB['hosts']} t={time.time()-t0:.0f}s")
    pr(f"[BRUTE] budget_hit={hit}")
    report('BRUTE', stB, exsB)
    pr(f"total t={time.time()-t0:.0f}s")

if __name__ == '__main__':
    main()
