import sys, itertools
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-s4a/python')
from red_model import (Lng, entry, monoT, seg, Br, FirstNodes, Joints, Red, TrMax, fmt)
def is_reduced(M): return Red(list(M))==list(M)
def descending(bs):
    for a in range(len(bs)):
        for b in range(a,len(bs)):
            x0,y0=bs[a][0]; x1,y1=bs[b][0]
            if not(x0>=x1 and (x0!=x1 or y0>=y1)): return False
    return True
def in_DT(M): return is_reduced(M) and monoT(M) and descending(Br(M))
allj_ok=allj_bad=0; fn_ok=fn_bad=0; comp_red=comp_notred=0; bad=[]
for L in range(3,6):
    for tup in itertools.product([(a,b) for a in range(4) for b in range(4)],repeat=L-1):
        M=[(0,0)]+list(tup)
        if not (monoT(M) and is_reduced(M)): continue
        b=Br(M)
        if not b or not descending(b): continue
        # (a) all j row1<=row0
        for j in range(Lng(M)):
            if entry(M,1,j)<=entry(M,0,j): allj_ok+=1
            else:
                allj_bad+=1
                if len(bad)<5: bad.append((fmt(M),'allj',j))
        # (b) firstnodes
        for J in range(len(b)):
            fn=FirstNodes(M)[J]
            if entry(M,1,fn)<=entry(M,0,fn): fn_ok+=1
            else: fn_bad+=1
        # (c) branch comp reduced
        for J in range(len(b)):
            if is_reduced(b[J]): comp_red+=1
            else: comp_notred+=1
print(f"allj row1<=row0: ok={allj_ok} bad={allj_bad}")
print(f"firstnode row1<=row0: ok={fn_ok} bad={fn_bad}")
print(f"branch comp reduced: yes={comp_red} no={comp_notred}")
for x in bad: print("  BAD",x)
