#!/usr/bin/env python3
# r36 BRIDGES enum: reliable exhaustive check + print passing hosts.
import sys, time, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4a/python')
from red_model import Lng, fmt
import _r36_bridges as B

def pr(*a): print(*a, flush=True)

def main():
    t0=time.time()
    Lmax = int(sys.argv[1]) if len(sys.argv)>1 else 6
    vmax = int(sys.argv[2]) if len(sys.argv)>2 else 4
    budget = int(sys.argv[3]) if len(sys.argv)>3 else 1500
    ok=fail=0; fails=[]; oks=[]
    cells=[(a,b) for a in range(vmax) for b in range(vmax)]
    for L in range(4, Lmax+1):
        if time.time()-t0>budget: pr("[budget]"); break
        cnt=0
        for tup in itertools.product(cells, repeat=L-1):
            if time.time()-t0>budget: break
            M=[(0,0)]+list(tup)
            if not B.in_reg4_base(M): continue
            cnt+=1
            r=B.check_bridges(M)
            if r[0]=='ok':
                ok+=1
                if len(oks)<8: oks.append(fmt(M))
            else:
                fail+=1
                if len(fails)<15: fails.append(r)
        pr(f"[L={L}] regime-hosts={cnt} ok={ok} fail={fail} t={time.time()-t0:.0f}s")
    pr("="*60)
    pr(f"[ENUM total] ok={ok} fail={fail}")
    pr("[sample OK hosts]")
    for h in oks: pr("   ", h)
    for f in fails: pr("  FAIL:", f)

if __name__=='__main__':
    main()
