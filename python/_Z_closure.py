import itertools, sys
from red_model import *

# Build a BROAD ST_PS closure: diag bases + oper closure, depth>=5.
# ST_PS membership here is the closure under diag/oper as instructed
# (NOT is_standard).  base u 0..3, v u..6, maxlen 14..16.

def diag_base(u,v):
    # diagonal pair sequence (u,u),(u+1,u+1),...,(v,v)
    return [(j,j) for j in range(u,v+1)]

def build_closure(depth=5, maxlen=16):
    pool=set()
    frontier=[]
    for u in range(0,4):
        for v in range(u,7):
            M=diag_base(u,v)
            if 1<=Lng(M)<=maxlen:
                t=tuple(M);
                if t not in pool:
                    pool.add(t); frontier.append(M)
    for d in range(depth):
        newf=[]
        for M in frontier:
            for n in range(1,5):
                try:
                    Mn=oper(M,n)
                except Exception:
                    continue
                if not (1<=Lng(Mn)<=maxlen): continue
                t=tuple(Mn)
                if t not in pool:
                    pool.add(t); newf.append(Mn)
        frontier=newf
        if not frontier: break
    return [list(t) for t in pool]

if __name__=="__main__":
    P=build_closure()
    print("closure size:", len(P))
    # length distribution
    from collections import Counter
    c=Counter(Lng(M) for M in P)
    print("len dist:", dict(sorted(c.items())))
