#!/usr/bin/env python3
# r36 BRIDGES deep-only: genuine oper-BFS hosts, DEEP.
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4a/python')
from red_model import diagSeq, Lng, oper
import _r36_bridges as B

def pr(*a): print(*a, flush=True)

def main():
    t0=time.time()
    Lmax = int(sys.argv[1]) if len(sys.argv)>1 else 11
    cap  = int(sys.argv[2]) if len(sys.argv)>2 else 30000
    seeds=[diagSeq(0,k) for k in range(1,7)]
    hosts=B.gen_hosts(Lmax, cap, seeds)
    dok=dfail=0; dmax=0; fails=[]; lens={}
    for M in hosts:
        r=B.check_bridges(M)
        dmax=max(dmax,Lng(M)); lens[Lng(M)]=lens.get(Lng(M),0)+1
        if r[0]=='ok': dok+=1
        else:
            dfail+=1
            if len(fails)<25: fails.append(r)
    pr("="*60)
    pr(f"[DEEP oper-BFS] hosts={len(hosts)} ok={dok} fail={dfail} maxLng={dmax} t={time.time()-t0:.0f}s")
    pr(f"[host Lng distribution] {dict(sorted(lens.items()))}")
    for f in fails: pr("  FAIL:", f)

if __name__=='__main__':
    main()
