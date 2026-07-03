#!/usr/bin/env python3
"""r26: is transV M < entry M 1 (Lng M -1) a GENERAL fact for monoT reduced
hosts (j1>0, t1!=0)? And transV M <= entry M 1 (transJ0 M)?"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import Lng, entry, monoT, parent, oper
import red_model as rm
from _r15_vx_lib import (Trans, gen_pool, mono_hosts, guarded, SKIP, internals)
from trans_model import (ZB, adm, Adm, Pred, reduced)
def transJ0(M): return parent(M,0,Lng(M)-1)
def run(hosts,label):
    st=dict(h=0, v_lt_j1=0, v_le_j0=0, v_lt_j0=0); bad=[]
    for M0 in hosts:
        M=list(M0); info=internals(M)
        if info is None: continue
        j1=Lng(M)-1; j0=transJ0(M); v=info['v']
        e_j1=entry(M,1,j1); e_j0=entry(M,1,j0)
        st['h']+=1
        st['v_lt_j1']+=(v<e_j1); st['v_le_j0']+=(v<=e_j0); st['v_lt_j0']+=(v<e_j0)
        if not (v<e_j1): bad.append(('vLTj1',rm.fmt(M),f"v={v} e_j1={e_j1}"))
    h=st['h']; print(f"\n=== {label}: {h} monoT hosts (j1>0,t1!=0) ===")
    for k in ('v_lt_j1','v_le_j0','v_lt_j0'): print(f"  {k:9s}: {st[k]}/{h}")
    for b in bad[:8]: print("  BAD:",b)
pool=gen_pool(maxlen=12,maxn=6,maxseed=4,cap=20000,oper_budget=5)
hosts=[M for M in mono_hosts(pool) if reduced(M) and Lng(M)-1>0]
run(hosts,"ST_PS all monoT (deep)")
def gen_brute(maxlen,maxval):
    out=[]
    for L in range(3,maxlen+1):
        cols=[(a,b) for a in range(maxval+1) for b in range(maxval+1)]
        for rest in itertools.product(cols,repeat=L-1):
            M=[(0,0)]+list(rest)
            if monoT(M) and reduced(M): out.append(tuple(M))
    return out
run([M for M in gen_brute(6,3) if Lng(M)-1>0],"BRUTE all monoT reduced")
