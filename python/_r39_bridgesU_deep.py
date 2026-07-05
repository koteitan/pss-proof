#!/usr/bin/env python3
# r39 BRIDGESU deep validation over the FULL vg7x_reg4 domain (BASE j1'=j1 AND
# STEP j1'<j1), NOT just the Adm0 base.  Doctrine (r37 lesson): oper-BFS deep,
# intermediate length >= 12, branch-specific counts, track oper-depth.
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4a/python')
from red_model import (Lng, entry, monoT, seg, parent, Adm, adm, oper,
                       diagSeq, Br, FirstNodes, Joints, Red, TrMax)
from trans_model import Trans
import _r36_bridges as B

def pr(*a): print(*a, flush=True)
def norm(M): return [tuple(p) for p in M]
def is_reduced(M):
    Mt = norm(M)
    return norm(Red(Mt)) == Mt

def descending(bs):
    for J0 in range(len(bs)):
        for J1 in range(J0, len(bs)):
            a0, b0 = bs[J0][0]; a1, b1 = bs[J1][0]
            if not (a0 >= a1 and (a0 != a1 or b0 >= b1)): return False
    return True

def in_reg7x_full(M):
    # vg7x_reg4 = reduced & monoT & Br!=[] & guard(entry1 j1'<entry0 j1')
    #             & 0<j0'<TrMax & descending(Br).   (NO Adm0, NO cfbx_j1p base.)
    if not is_reduced(M): return False
    if not monoT(M): return False
    b = Br(M)
    if not b: return False
    if Lng(M)-1 <= 1: return False
    J1 = len(b)-1
    fn = FirstNodes(M); jt = Joints(M)
    j1p = fn[J1]; j0p = jt[J1]
    if j1p is None or j0p is None: return False
    if not (entry(M,1,j1p) < entry(M,0,j1p)): return False       # guard
    if not (0 < j0p and j0p < TrMax(M)): return False            # 0<j0'<TrMax
    if not descending(b): return False
    return True

def branch_of(M):
    # BASE = j1' = j1 (last column reaches the end); STEP = j1' < j1.
    b = Br(M); J1 = len(b)-1
    j1p = FirstNodes(M)[J1]; j1 = Lng(M)-1
    return 'BASE' if j1p == j1 else 'STEP'

def gen_hosts_depth(Lmax, cap, seeds):
    # BFS over oper-orbit, tracking depth; collect vg7x_reg4 hosts (any branch).
    seen = {}; out = []
    frontier = []
    for s in seeds:
        k = tuple(map(tuple, s)); seen[k] = 0; frontier.append((k, 0))
    max_depth_explored = 0
    while frontier and len(out) < cap:
        nxt = []
        for st, d in frontier:
            max_depth_explored = max(max_depth_explored, d)
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
                    if len(seen) > 400000: break
        frontier = nxt
    return out, max_depth_explored

def main():
    t0=time.time()
    Lmax = int(sys.argv[1]) if len(sys.argv)>1 else 12
    cap  = int(sys.argv[2]) if len(sys.argv)>2 else 60000
    seeds=[diagSeq(0,k) for k in range(1,8)]
    hosts, dmax = gen_hosts_depth(Lmax, cap, seeds)
    tot={'BASE':[0,0], 'STEP':[0,0]}   # [ok, fail]
    depthmax_host=0; lens={}; deep_ok=0; fails=[]
    for M,d in hosts:
        br = branch_of(M)
        r = B.check_bridges(M)
        depthmax_host=max(depthmax_host,d)
        lens[Lng(M)]=lens.get(Lng(M),0)+1
        if r[0]=='ok':
            tot[br][0]+=1
            if d>=9 or Lng(M)>=8: deep_ok+=1
        else:
            tot[br][1]+=1
            if len(fails)<30: fails.append((br,d,r))
    pr("="*64)
    pr(f"[r39 bridgesU FULL vg7x_reg4] hosts={len(hosts)} Lmax={Lmax} "
       f"maxLngHost={max(lens) if lens else 0} maxOperDepthExplored={dmax} "
       f"maxHostDepth={depthmax_host} t={time.time()-t0:.0f}s")
    pr(f"[BASE (j1'=j1)] ok={tot['BASE'][0]} fail={tot['BASE'][1]}")
    pr(f"[STEP (j1'<j1)] ok={tot['STEP'][0]} fail={tot['STEP'][1]}")
    pr(f"[deep subset d>=9 or Lng>=8] ok={deep_ok}")
    pr(f"[host Lng distribution] {dict(sorted(lens.items()))}")
    if fails:
        pr("FAILURES:")
        for f in fails: pr("  ", f)
    else:
        pr("NO FAILURES.")

if __name__=='__main__':
    main()
