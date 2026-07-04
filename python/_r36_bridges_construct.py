#!/usr/bin/env python3
# r36 BRIDGES deep-constructive: build reduced-monoT condII/IV Adm0 base hosts
# with LARGE trunks (TrMax up to ~7) by appending branch columns to a diagonal
# trunk, then validate brN/brMp EXACTLY.
import sys, time, itertools, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4a/python')
from red_model import Lng, fmt, diagSeq, TrMax
import _r36_bridges as B

def pr(*a): print(*a, flush=True)

def main():
    t0=time.time()
    ok=fail=0; fails=[]; maxL=0; maxTr=0; byTr={}
    random.seed(1)
    # trunk diagSeq 0 T, then append k columns with row0 in {T-1,T}, row1 in 0..T
    for T in range(2, 8):
        trunk = diagSeq(0, T)
        for k in range(1, 9):
            if time.time()-t0 > 700: break
            # random sampling of appended-column tails of length k
            tries = 0
            for _ in range(4000):
                tries += 1
                tail = [(random.choice([T-1, T]), random.randint(0, T)) for _ in range(k)]
                M = trunk + tail
                if not B.in_reg4_base(M): continue
                r = B.check_bridges(M)
                maxL=max(maxL,Lng(M)); maxTr=max(maxTr,TrMax(M))
                byTr[TrMax(M)]=byTr.get(TrMax(M),0)+1
                if r[0]=='ok': ok+=1
                else:
                    fail+=1
                    if len(fails)<20: fails.append(r)
        pr(f"[T={T}] cum ok={ok} fail={fail} maxLng={maxL} maxTrMax={maxTr} t={time.time()-t0:.0f}s")
    pr("="*60)
    pr(f"[CONSTRUCT] brN&brMp ok={ok} fail={fail} maxLng={maxL} maxTrMax={maxTr}")
    pr(f"[hosts by TrMax] {dict(sorted(byTr.items()))}")
    for f in fails: pr("  FAIL:", f)

if __name__=='__main__':
    main()
