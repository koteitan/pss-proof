import itertools, sys
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng, entry, P, monoT, TrMax, Br, parent, FirstNodes, Joints)
from trans_model import (Trans, Mark, Pred, reduced, adm, Adm, ZB, Dpt, addBT, PB, bpHeadV, bpHeadT,
                         _c2, condI, condIII, condV, condVI, flatBT, scb_decomps, unflatBT)
import collections
def enum(ml, me):
    cols=[(a,b) for a in range(me+1) for b in range(me+1)]
    for L in range(2,ml+1):
        for M in itertools.product(cols,repeat=L): yield list(M)
def transJ0(M): return parent(M,0,Lng(M)-1)
def transJm1(M): return Adm(M,transJ0(M))

# For Admpos: compute c1, c2, the scb decomp s1/b1, and check:
#   Trans(Pred M) = unflat(s1 @ flat c1 @ b1)  (by defn of scb)
#   Trans M       = unflat(s1 @ flat c2 @ b1)  (Trans recursion)
# clause 3/4 shape:  D_e10(A + D_ev B), D_e10(A + D_ev C).
# We want to know: what is c1 vs c2 structurally?  Is c2 = c1 with its innermost tail replaced?
stats=collections.Counter()
for M in enum(5,3):
    if not (entry(M,0,0)==0 and entry(M,1,0)==0): continue
    if not (monoT(M) and reduced(M)): continue
    if Br(M)==[]: continue
    j1=Lng(M)-1
    if not (j1>1): continue
    if transJm1(M)==0: continue
    tP=Trans(Pred(M))
    jp=parent(M,0,j1)
    c1=Mark(Pred(M), Adm(M,jp))
    v=bpHeadV(c1); t2=bpHeadT(c1)
    c2=_c2(M,j1,jp,v,t2)
    ds=scb_decomps(tP, flatBT(c1))
    if not ds: stats['NO_SCB']+=1; continue
    s1,b1=ds[0]
    # check Trans(Pred M) = unflat(s1 @ flat c1 @ b1)
    rec=unflatBT(s1+flatBT(c1)+b1)
    ok1=(rec==tP)
    # c1 head, c2 head
    h1=(c1[1][0][1] if c1[1] else None)
    h2=(c2[1][0][1] if c2[1] else None)
    stats[('headv_eq', h1==h2, h1==v)]+=1
    stats[('rec_ok', ok1)]+=1
for k,vv in sorted(stats.items(), key=lambda x:str(x[0])): print(k, vv)
