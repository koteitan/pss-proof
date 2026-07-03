#!/usr/bin/env python3
"""Front B empirical bridge checks for §6.5 Red_le.

(a) RedCondA M ==> leR M == leR (Red M) over standard T_PS  (expect 0 fail)
(b) anchored_slice M ==> RedCondA M  (report rate; anchored_slice from gen_std S, seg a b with le0 S a b)
(c) row-0 fragment le0 M == le0 (Red M) under RedCondA  (expect 0 fail)
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, le0, le1, leR, Red, monoT, multiT, zeroT,
                       hasParent, parent, reduced, is_standard, seg, fmt, nextR)
from d1pos_j0j1red_search import gen_std

def RedCondA(M):
    n=Lng(M)
    for i in (0,1):
        for j1 in range(n):
            if hasParent(M,i,j1):
                p=parent(M,i,j1)
                if entry(M,i,p)+1 != entry(M,i,j1):
                    return False
    return True

def red_le_eq(M):
    """returns (ok, first_fail) comparing leR M vs leR(Red M)."""
    R=Red(M)
    if Lng(R)!=Lng(M): return (False,('LNGMM',fmt(R)))
    n=Lng(M)
    for i in (0,1):
        for j0 in range(n):
            for j1 in range(n):
                if leR(M,i,j0,j1)!=leR(R,i,j0,j1):
                    return (False,(i,j0,j1,fmt(R)))
    return (True,None)

def le0_eq(M):
    R=Red(M); n=Lng(M)
    if Lng(R)!=n: return (False,('LNGMM',fmt(R)))
    for j0 in range(n):
        for j1 in range(n):
            if le0(M,j0,j1)!=le0(R,j0,j1):
                return (False,(j0,j1,fmt(R)))
    return (True,None)

def le1_eq(M):
    R=Red(M); n=Lng(M)
    if Lng(R)!=n: return (False,('LNGMM',fmt(R)))
    for j0 in range(n):
        for j1 in range(n):
            if le1(M,j0,j1)!=le1(R,j0,j1):
                return (False,(j0,j1,fmt(R)))
    return (True,None)

def main():
    maxlen,maxval,KMAX = (int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])) if len(sys.argv)>3 else (9,4,6)
    Ms = gen_std(maxlen,maxval,KMAX)
    print(f"# standard T_PS sample size={len(Ms)} (maxlen={maxlen},maxval={maxval},KMAX={KMAX})")

    # (a) RedCondA ==> red_le over standard T_PS
    condA = [M for M in Ms if RedCondA(M)]
    t=f=0; ces=[]
    for M in condA:
        ok,first=red_le_eq(M)
        if ok: t+=1
        else:
            f+=1
            if len(ces)<8: ces.append((fmt(M),first))
    print(f"(a) RedCondA ==> leR M = leR(Red M): TRUE={t} FALSE={f}  (|condA|={len(condA)})")
    for c in ces: print("    CE(a):",c)

    # (a') the converse-context: among ALL standard M, how many satisfy red_le; does RedCondA capture it?
    allt=allf=0
    rle_but_notA=0; A_but_notrle=0
    for M in Ms:
        ok,_=red_le_eq(M); a=RedCondA(M)
        if ok: allt+=1
        else: allf+=1
        if ok and not a: rle_but_notA+=1
        if a and not ok: A_but_notrle+=1
    print(f"(a') over ALL standard: red_le TRUE={allt} FALSE={allf}; "
          f"red_le&¬RedCondA={rle_but_notA}; RedCondA&¬red_le={A_but_notrle}")

    # (c) le0 fragment under RedCondA
    t=f=0; ces=[]
    for M in condA:
        ok,first=le0_eq(M)
        if ok: t+=1
        else:
            f+=1
            if len(ces)<8: ces.append((fmt(M),first))
    print(f"(c) RedCondA ==> le0 M = le0(Red M): TRUE={t} FALSE={f}")
    for c in ces: print("    CE(c):",c)

    # (c1) le1 fragment under RedCondA
    t=f=0; ces=[]
    for M in condA:
        ok,first=le1_eq(M)
        if ok: t+=1
        else:
            f+=1
            if len(ces)<8: ces.append((fmt(M),first))
    print(f"(c1) RedCondA ==> le1 M = le1(Red M): TRUE={t} FALSE={f}")
    for c in ces: print("    CE(c1):",c)

    # (b) anchored_slice ==> RedCondA
    # anchored_slice = seg S a b for S in ST_PS (or RT&PT), a<=b<Lng S, le0 S a b.
    # Use standard S (covers ST_PS branch); also include reduced+mono S.
    t=f=0; ces=[]; total_slices=0
    seen=set()
    for S in Ms:
        nS=Lng(S)
        for a in range(nS):
            for b in range(a,nS):
                if not le0(S,a,b): continue
                M=seg(S,a,b)
                k=fmt(M)
                if k in seen: continue
                seen.add(k)
                total_slices+=1
                if RedCondA(M): t+=1
                else:
                    f+=1
                    if len(ces)<12: ces.append((fmt(S),a,b,fmt(M)))
    print(f"(b) anchored_slice(std S) ==> RedCondA: TRUE={t} FALSE={f}  (distinct slices={total_slices})")
    for c in ces: print("    CE(b):",c)

    # (b') for the slices that FAIL RedCondA, does red_le still hold for them?
    if ces:
        print("    -- of failing-RedCondA slices, red_le status:")
        cnt_ok=cnt_bad=0
        seen2=set()
        for S in Ms:
            nS=Lng(S)
            for a in range(nS):
                for b in range(a,nS):
                    if not le0(S,a,b): continue
                    M=seg(S,a,b); k=fmt(M)
                    if k in seen2: continue
                    seen2.add(k)
                    if not RedCondA(M):
                        ok,_=red_le_eq(M)
                        if ok: cnt_ok+=1
                        else: cnt_bad+=1
        print(f"    failing-RedCondA slices: red_le TRUE={cnt_ok} FALSE={cnt_bad}")

if __name__=='__main__':
    main()
