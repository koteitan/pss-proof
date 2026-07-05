#!/usr/bin/env python3
# r43 READOFF deep validation of rdx_bridgesU_readoff over GENUINE vg7x_reg4 hosts.
# Doctrine (r37/r39/r40/r41/r42 lesson): the host corpus must be the TRUE closure,
# NOT a shallow seed set. Seeds = diagSeq(u,v) with u>0 INCLUDED. BFS oper-closure,
# intermediate length up to Lmax(default 15). Per-conjunct pass fractions.
#
# Residual (exact):  given vg7x_reg4 N and
#    f: Trans N = D_{N_1,0}(t1 + D_{N_1,j0'}(tau)),   j0' = Joints N ! (Lng(Br N)-1)
# conclude
#   (1) Trans(seg N 0 (FirstNodes N ! LastStep N - 1)) = D_{N_1,0} t1
#   (3) bpHeadT(Trans(seg N j0' (Lng N-1))) = tau
#   (split) tau = t1 + t2, t2 != 0.
# check_bridges checks (1), the STRONGER (3) [full slice = D_{e1j0'} tau], and split.
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4a/python')
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
from red_model import (Lng, entry, monoT, seg, parent, Adm, adm, oper,
                       diagSeq, Br, FirstNodes, Joints, Red, TrMax)
from trans_model import Trans, Dpt, bpHeadT
import _r36_bridges as B

def pr(*a): print(*a, flush=True)
def norm(M): return [tuple(p) for p in M]
def is_reduced(M):
    Mt = norm(M); return norm(Red(Mt)) == Mt

def descending(bs):
    for J0 in range(len(bs)):
        for J1 in range(J0, len(bs)):
            a0, b0 = bs[J0][0]; a1, b1 = bs[J1][0]
            if not (a0 >= a1 and (a0 != a1 or b0 >= b1)): return False
    return True

def in_reg7x_full(M):
    # vg7x_reg4 = reduced & monoT & Br!=[] & Lng-1>1 & guard & 0<j0'<TrMax & descending(Br)
    # CHEAP checks first, Red (is_reduced) LAST.
    if Lng(M)-1 <= 1: return False
    if not monoT(M): return False
    b = Br(M)
    if not b: return False
    J1 = len(b)-1
    fn = FirstNodes(M); jt = Joints(M)
    j1p = fn[J1]; j0p = jt[J1]
    if j1p is None or j0p is None: return False
    if not (entry(M,1,j1p) < entry(M,0,j1p)): return False       # guard
    if not (0 < j0p and j0p < TrMax(M)): return False            # 0<j0'<TrMax
    if not descending(b): return False
    if not is_reduced(M): return False                           # expensive last
    return True

def has_form(M):
    # does Trans M actually factor as D_{e10}(t1 + D_{e1j0'} tau)?  (f-hypothesis)
    r = B.check_bridges(M)
    return r[0] != 'formfail-outer' and not str(r[0]).startswith('formfail')

def branch_of(M):
    b = Br(M); J1 = len(b)-1
    j1p = FirstNodes(M)[J1]; j1 = Lng(M)-1
    return 'BASE' if j1p == j1 else 'STEP'

def gen_hosts_depth(Lmax, cap, seeds, seencap=600000):
    seen = {}; out = []; frontier = []
    for s in seeds:
        k = tuple(map(tuple, s)); seen[k] = 0; frontier.append((k, 0))
    dmax = 0
    while frontier and len(out) < cap:
        nxt = []
        for st, d in frontier:
            dmax = max(dmax, d)
            M = [list(p) for p in st]
            if Lng(M) <= Lmax and in_reg7x_full(M):
                out.append((M, d))
            for n in range(2, 6):
                try: M2 = oper(M, n)
                except Exception: continue
                if Lng(M2) > Lmax: continue
                key = tuple(map(tuple, M2))
                if key not in seen:
                    seen[key] = d+1; nxt.append((key, d+1))
            if len(seen) > seencap: break
        if len(seen) > seencap: break
        frontier = nxt
    return out, dmax, len(seen)

def main():
    t0=time.time()
    Lmax = int(sys.argv[1]) if len(sys.argv)>1 else 15
    cap  = int(sys.argv[2]) if len(sys.argv)>2 else 120000
    # seeds: diagSeq(u,v) for u>=0, INCLUDING u>0 (the r40 lesson).
    seeds=[]
    for u in range(0,4):
        for v in range(u+1, 8):
            seeds.append(diagSeq(u,v))
    hosts, dmax, nseen = gen_hosts_depth(Lmax, cap, seeds, seencap=200000)
    tot={'BASE':[0,0], 'STEP':[0,0]}
    c1=c3=csplit=0; formed=0; noform=0; deep=0; deep_ok=0
    lens={}; fails=[]
    for M,d in hosts:
        lens[Lng(M)]=lens.get(Lng(M),0)+1
        if not has_form(M):
            noform+=1; continue    # f-hypothesis vacuous
        formed+=1
        br=branch_of(M)
        r=B.check_bridges(M)
        isdeep = (Lng(M)>=10 or d>=8)
        if isdeep: deep+=1
        if r[0]=='ok':
            tot[br][0]+=1; c1+=1; c3+=1; csplit+=1
            if isdeep: deep_ok+=1
        else:
            tot[br][1]+=1
            # per-conjunct: parse the 'okN= okMpSlice= okSplit=' string
            s = r[2] if len(r)>2 else ''
            if 'okN=True' in s: c1+=1
            if 'okMpSlice=True' in s: c3+=1
            if 'okSplit=True' in s: csplit+=1
            if len(fails)<25: fails.append((br,d,Lng(M),r))
    pr("="*70)
    pr(f"[r43 readoff deep] hosts(reg7x)={len(hosts)} formed(f-holds)={formed} "
       f"noform={noform} Lmax={Lmax} maxLng={max(lens) if lens else 0} "
       f"operDepthMax={dmax} seen={nseen} t={time.time()-t0:.0f}s")
    pr(f"[per-conjunct over formed={formed}] (1)front={c1} (3)term={c3} split={csplit}")
    pr(f"[BASE j1'=j1] ok={tot['BASE'][0]} fail={tot['BASE'][1]}")
    pr(f"[STEP j1'<j1] ok={tot['STEP'][0]} fail={tot['STEP'][1]}")
    pr(f"[deep subset Lng>=10 or d>=8] n={deep} ok={deep_ok}")
    pr(f"[host Lng dist] {dict(sorted(lens.items()))}")
    if fails:
        pr("FAILURES (CEX candidates):")
        for f in fails: pr("  ", f)
    else:
        pr("NO FAILURES: all 3 conjuncts hold on every formed genuine host.")

if __name__=='__main__':
    main()
