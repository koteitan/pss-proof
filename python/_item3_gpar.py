import sys,functools,os,subprocess,itertools
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng,entry,monoT,parent,TrMax,Br,oper)
import red_model as rm
from trans_model import (Trans,ZB,PB,bpHeadT,condI,condIII,condV,condVI)
BMS=os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),"tmp","yaBMS","c","bms")
@functools.lru_cache(None)
def is_std(t): return subprocess.run([BMS,"-s",rm.fmt(list(t))],capture_output=True,text=True).stdout.strip()=="1"
def cond(M):
    try: return 'I' if condI(M) else 'III' if condIII(M) else 'V' if condV(M) else 'VI' if condVI(M) else 'o'
    except: return '?'
def gp(M): j1=Lng(M)-1; return parent(M,0,j1)>TrMax(M) if j1>0 else False
def spineLeaf(T):
    h=bpHeadT(T);pb=PB(h);return None if not pb else bpHeadT(pb[-1])
# find MORE condV+gpar (deepen) standard seeds at L=5,6
seeds=[]; cols=[(a,b) for a in range(5) for b in range(4)]
for L in (5,6):
  for tM in itertools.product(cols,repeat=L):
    M=list(tM)
    if not(M[0]==(0,0) and entry(M,1,1)>0):continue
    if not(monoT(M) and condV(M) and gp(M)):continue
    if not is_std(tuple(M)):continue
    seeds.append(M)
    if len(seeds)>=8:break
  if len(seeds)>=8:break
print("=== condV+gpar (DEEPEN) seeds: cond(M[1..4]) + endpoint ep(q1) ===")
for M in seeds:
    row=[]
    for q in range(1,5):
        Mq=oper(M,q)
        if Lng(Mq)>12: row.append('-');continue
        row.append(cond(Mq) if is_std(tuple(Mq)) else 'ns')
    ep='?'
    try:
        Y=oper(M,1);N=oper(M,2)
        if Lng(N)<=12 and is_std(tuple(Y)) and is_std(tuple(N)):
            ep=(spineLeaf(Trans(N))==bpHeadT(Trans(Y)))
    except: ep='err'
    print("  %-26s iters=%s ep(q1)=%s"%(rm.fmt(M),row,ep))
print("count:",len(seeds))
