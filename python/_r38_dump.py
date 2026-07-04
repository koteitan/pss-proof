#!/usr/bin/env python3
# Dump precise geometry of a non-anc host: children of jm2, the peeled first
# row-0 edge toward j1, and the sibling comparison.
import sys
sys.path.insert(0,'python')
from red_model import (Lng, entry, le0, nextrel0, nextrel1, hasParent, parent, fmt, seg,
                       TrMax, Br, FirstNodes, P, monoT)
import red_model as rm

def hasParent_i(M,i,j): return sum(1 for j0 in range(Lng(M)) if rm.nextR(M,i,j0,j))==1
def parent_i(M,i,j):
    for j0 in range(Lng(M)):
        if rm.nextR(M,i,j0,j): return j0
    return None

def dump(Mstr):
    # parse "(a,b)(c,d)..."
    import re
    M=[tuple(map(int,p.split(','))) for p in re.findall(r'\(([^)]*)\)',Mstr)]
    L=Lng(M); j1=L-1
    jm2=parent_i(M,1,j1); j0=parent_i(M,0,j1)
    print("M",fmt(M),"L",L)
    print("row0",[entry(M,0,k) for k in range(L)])
    print("row1",[entry(M,1,k) for k in range(L)])
    print("j1",j1,"jm2",jm2,"j0",j0,"le0(jm2,j1)",le0(M,jm2,j1),
          "le0(jm2+1,j1)",le0(M,jm2+1,j1))
    print("entry1 jm2",entry(M,1,jm2),"entry1 jm2+1",entry(M,1,jm2+1),"entry1 j1",entry(M,1,j1))
    # row-0 children of jm2 (nextrel0 jm2 c) and whether le0 c j1
    kids=[c for c in range(L) if nextrel0(M,jm2,c)]
    print("row0-children of jm2:",[(c,entry(M,0,c),entry(M,1,c),'le0j1',le0(M,c,j1)) for c in kids])
    # first child toward j1 = smallest kid with le0(c,j1)
    path_kids=[c for c in kids if le0(M,c,j1)]
    print("path-children (le0 to j1):",path_kids)
    if path_kids:
        a=min(path_kids)
        print("a(first path child)",a,"entry0",entry(M,0,a),"entry1",entry(M,1,a),
              "cmp: jm2+1<a?",jm2+1<a)
    # slice N = seg M jm2 j1
    N=seg(M,jm2,j1)
    print("N monoT",monoT(N),"TrMax N",TrMax(N),"Lng N",Lng(N))
    print("N row0",[entry(N,0,k) for k in range(Lng(N))])
    print("N row1",[entry(N,1,k) for k in range(Lng(N))])
    if monoT(N):
        br=Br(N); fn=FirstNodes(N)
        print("Br N leftends (row0,row1):",[(entry(b,0,0),entry(b,1,0)) for b in br])
        print("FirstNodes N (N-index):",fn," -> M-index:",[jm2+f for f in fn])
    print("---")

for s in sys.argv[1:]:
    dump(s)
