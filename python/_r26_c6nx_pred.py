import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import Lng, entry, monoT, parent, oper
import red_model as rm
from _r15_vx_lib import (gen_pool, mono_hosts, guarded, SKIP, condVI, internals)
from trans_model import (adm, Adm, Pred, reduced)
def transJ0(M): return parent(M,0,Lng(M)-1)
def rowpreds(M,i,j): return [a for a in range(j) if rm.nextR(M,i,a,j)]
def run(hosts,label):
    st=dict(h=0, jp0_adj=0, u_pos=0, e_incr=0, hasP1_j0=0, admj0m1=0); bad=[]
    for M0 in hosts:
        M=list(M0)
        if internals(M) is None: continue
        j0=transJ0(M); u=entry(M,1,j0)
        st['h']+=1
        jp0=parent(M,0,j0)
        st['jp0_adj']+=(jp0==j0-1)
        st['u_pos']+=(u>0)
        st['e_incr']+=(entry(M,1,j0-1)+1==u)
        ps1=rowpreds(M,1,j0)
        st['hasP1_j0']+=(len(ps1)==1)
        st['admj0m1']+=adm(M,j0-1)
        if not(jp0==j0-1 and u>0 and entry(M,1,j0-1)+1==u):
            bad.append((rm.fmt(M),f"j0={j0} jp0={jp0} u={u} e(j0-1)={entry(M,1,j0-1)} ps1={ps1}"))
    h=st['h']; print(f"\n=== {label}: {h} hosts ===")
    for k in ('jp0_adj','u_pos','e_incr','hasP1_j0','admj0m1'): print(f"  {k:9s}: {st[k]}/{h}")
    for b in bad[:8]: print("  BAD:",b)
pool=gen_pool(maxlen=12,maxn=6,maxseed=4,cap=20000,oper_budget=5)
nadm=[M for M in mono_hosts(pool) if Lng(M)>=4 and Lng(M)-1>1 and reduced(M)
      and guarded(condVI,M,budget=5) is not SKIP and condVI(M) and not adm(M,transJ0(M))]
run(nadm[:120],"ST_PS deep")
def gb(ml,mv):
    o=[]
    for L in range(4,ml+1):
        cs=[(a,b) for a in range(mv+1) for b in range(mv+1)]
        for r in itertools.product(cs,repeat=L-1):
            M=[(0,0)]+list(r)
            if monoT(M) and reduced(M): o.append(tuple(M))
    return o
bn=[M for M in gb(6,2) if Lng(M)-1>1 and guarded(condVI,M,budget=5) is not SKIP
    and condVI(M) and not adm(M,transJ0(M))]
run(bn,"BRUTE")
