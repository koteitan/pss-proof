#!/usr/bin/env python3
# r33 VE34: is vg2x_VE34 TRUE over vg2x_reg2 (RT_PS & PT_PS & Br!=[]; NO guard,
# NO descending)?  Check at BASE (cfbx_j1p == Lng-1) and generally, and whether
# it needs the guard (entry0 j1' > entry1 j1') and/or descending (=> DT_PS).
import sys, itertools
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-s4a/python')
import red_model as rm
from red_model import (Lng, entry, monoT, Red, Br, FirstNodes, Joints, TrMax,
                       seg, fmt)
import trans_model as tm
from trans_model import Trans, bpHeadT, Dpt

def is_reduced(M): return Red(list(M))==list(M)
def LastStep(M):
    b=Br(M)
    if not b: return 0
    J1=len(b)-1
    h0=entry(b[J1],0,0); h1=entry(b[J1],1,0)
    if h0==h1: return J1
    cand=[J for J in range(len(b)) if entry(b[J1],0,0)==entry(b[J],0,0) and entry(b[J],1,0)<entry(b[J],0,0)]
    return min(cand)
def descending_br(b):
    for a in range(len(b)):
        for c in range(a,len(b)):
            x0,y0=entry(b[a],0,0),entry(b[a],1,0); x1,y1=entry(b[c],0,0),entry(b[c],1,0)
            if not(x0>=x1 and (x0!=x1 or y0>=y1)): return False
    return True
def blist(t): return t[1]  # PB-list
def is_prefix(A,B):  # A list prefix of B list
    return len(A)<=len(B) and B[:len(A)]==A
def ve34_holds(M):
    n=Lng(M); b=Br(M)
    J1=len(b)-1
    j0p=Joints(M)[J1]
    J0=LastStep(M)
    m1=FirstNodes(M)[J0]-1
    Mp=seg(M,j0p,n-1)
    N=seg(M,0,m1)
    A=bpHeadT(Trans(N)); B=bpHeadT(Trans(Mp)); C=bpHeadT(Trans(M))
    v=entry(M,1,j0p)
    # VE3: B = A +_B t2, t2!=0  <=>  A proper prefix of B
    ve3 = is_prefix(blist(A),blist(B)) and len(blist(A))<len(blist(B))
    # VE4: C list == A list ++ [('D', v, B)]
    ve4 = (blist(C) == blist(A) + [('D', v, B)])
    return ve3, ve4
def cfbx_j1p(M): return FirstNodes(M)[len(Br(M))-1]

def main():
    GRID=[(x,y) for x in range(4) for y in range(4)]
    base_ve3=base_ve4=base_n=0
    gen_ve3=gen_ve4=gen_n=0
    # split by guard and descending
    cats={}
    cexb=[]; cexg=[]
    for L in range(3,6):
        for tup in itertools.product(GRID,repeat=L-1):
            M=[(0,0)]+list(tup)
            if not (monoT(M) and is_reduced(M)): continue
            b=Br(M)
            if not b: continue
            n=Lng(M); J1=len(b)-1
            j0p=Joints(M)[J1]
            if not (0<j0p<TrMax(M)): continue   # matches vgx j0pos/j0lt geometry
            j1p=FirstNodes(M)[J1]
            guard = entry(M,0,j1p) > entry(M,1,j1p)
            desc = descending_br(b)
            try:
                ve3,ve4=ve34_holds(M)
            except Exception as e:
                continue
            key=(guard,desc); c=cats.setdefault(key,[0,0,0]); c[0]+=1; c[1]+=ve3 and ve4;
            isbase = (j1p==n-1)
            gen_n+=1; gen_ve3+=ve3; gen_ve4+=ve4
            if not(ve3 and ve4) and len(cexg)<10:
                cexg.append((fmt(M),'base' if isbase else 'step','g' if guard else '.','d' if desc else '.',ve3,ve4))
            if isbase:
                base_n+=1; base_ve3+=ve3; base_ve4+=ve4
                if not(ve3 and ve4) and len(cexb)<10:
                    cexb.append((fmt(M),'g' if guard else '.','d' if desc else '.',ve3,ve4))
    print(f"[BASE cfbx_j1p==Lng-1]  n={base_n} ve3={base_ve3} ve4={base_ve4} both={min(base_ve3,base_ve4)}")
    print(f"[ALL vg2x_reg2 geom]    n={gen_n} ve3={gen_ve3} ve4={gen_ve4}")
    print("by (guard,desc): count, both-ok:")
    for k in sorted(cats): print(f"   guard={k[0]} desc={k[1]}: n={cats[k][0]} both={cats[k][1]}")
    print("--- BASE cex (M,guard,desc,ve3,ve4) ---")
    for x in cexb: print("  ",x)
    print("--- ALL cex (M,base/step,guard,desc,ve3,ve4) ---")
    for x in cexg: print("  ",x)

if __name__=='__main__': main()
