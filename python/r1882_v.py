import itertools, sys
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng, entry, monoT, TrMax, Br, parent, FirstNodes, Joints)
from trans_model import (Trans, Mark, Pred, reduced, adm, Adm, ZB, Dpt, PB, bpHeadV, bpHeadT, _c2, flatBT, scb_decomps, unflatBT)
import collections
def enum(ml,me):
    cols=[(a,b) for a in range(me+1) for b in range(me+1)]
    for L in range(2,ml+1):
        for M in itertools.product(cols,repeat=L): yield list(M)
def transJ0(M): return parent(M,0,Lng(M)-1)
def transJm1(M): return Adm(M,transJ0(M))
st=collections.Counter()
for M in enum(5,3):
    if not (entry(M,0,0)==0 and entry(M,1,0)==0): continue
    if not (monoT(M) and reduced(M)): continue
    if Br(M)==[]: continue
    j1=Lng(M)-1
    if not (j1>1): continue
    if transJm1(M)==0: continue
    e10=entry(M,1,0)
    jp=parent(M,0,j1)
    c1=Mark(Pred(M),Adm(M,jp))
    v=bpHeadV(c1)
    tP=Trans(Pred(M))
    ds=scb_decomps(tP,flatBT(c1))
    s1,b1=ds[0]
    # is s1 empty?  is flatBT c1 = whole bodyP after D_e10?
    st[('v_eq_e10', v==e10)]+=1
    st[('s1_empty', s1==[])]+=1
    st[('b1_empty', b1==[])]+=1
    st[('s1_len', len(s1))]+=1
    # c1 in clause shape itself?  c1 = D_e10(...)?  Actually c1=Mark(Pred M)(Adm M jp)
    # relationship of c1's flat to Trans(Pred M)'s flat
for k,vv in sorted(st.items(),key=lambda x:str(x[0])): print(k,vv)
