import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import Lng, entry, monoT, parent
import red_model as rm
from _r15_vx_lib import (gen_pool, mono_hosts, guarded, SKIP, condVI, internals, Trans, flatBT)
from trans_model import (adm, Adm, Pred, reduced, ZB)
def transJ0(M): return parent(M,0,Lng(M)-1)
def zeroT(M): return Lng(M)==1 and entry(M,1,0)==0 and entry(M,0,0)==0
def gb(ml,mv):
    o=[]
    for L in range(3,ml+1):
        cs=[(a,b) for a in range(mv+1) for b in range(mv+1)]
        for r in itertools.product(cs,repeat=L-1):
            M=[(0,0)]+list(r)
            if monoT(M) and reduced(M): o.append(tuple(M))
    return o
# brute with value up to 4 to catch len-3 hosts
allh=gb(5,4)
nadm=[M for M in allh if Lng(M)-1>1 and guarded(condVI,M,budget=5) is not SKIP
      and condVI(M) and not adm(M,transJ0(M))]
print(f"brute nadm-condVI hosts (Lng<=5,val<=4): {len(nadm)}")
if nadm:
    print("min Lng:", min(Lng(M) for M in nadm))
    lng3=[M for M in nadm if Lng(M)==3]
    print(f"Lng==3 hosts: {len(lng3)}")
    for M in lng3[:6]: print("  ",rm.fmt(M),"j0=",transJ0(M))
    # check transT1(Pred M) = Trans(Pred(Pred M)) == 0 (i.e. PPM zeroT)
    bad=[M for M in nadm if Trans(tuple(Pred(Pred(list(M)))))==ZB]
    print(f"hosts with Trans(Pred(Pred M))==0: {len(bad)}")
    for M in bad[:6]: print("  T1PredM=0:",rm.fmt(M),"Lng=",Lng(M))
# ST_PS oper closure min Lng
pool=gen_pool(maxlen=12,maxn=6,maxseed=4,cap=15000,oper_budget=5)
snadm=[M for M in mono_hosts(pool) if Lng(M)-1>1 and reduced(M)
       and guarded(condVI,M,budget=5) is not SKIP and condVI(M) and not adm(M,transJ0(M))]
print(f"\nST_PS nadm-condVI (any Lng>=3): {len(snadm)}  min Lng: {min(Lng(M) for M in snadm) if snadm else '-'}")
sbad=[M for M in snadm if Trans(tuple(Pred(Pred(list(M)))))==ZB]
print(f"  ST_PS hosts with Trans(Pred(Pred M))==0: {len(sbad)}")
