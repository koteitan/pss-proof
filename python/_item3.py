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
# ALL standard condV seeds (gpar or not); classify iterates + endpoint
seeds=[]; cols=[(a,b) for a in range(4) for b in range(3)]
for L in (3,4):
  for tM in itertools.product(cols,repeat=L):
    M=list(tM)
    if not(M[0]==(0,0) and entry(M,1,1)>0):continue
    if not(monoT(M) and condV(M) and is_std(tuple(M))):continue
    seeds.append(M)
    if len(seeds)>=14:break
  if len(seeds)>=14:break
print("=== ITEM 3: all standard condV seeds; gpar(M); cond(M[1..5]); endpoint q=2 ===")
for M in seeds:
    row=[]
    for q in range(1,6):
        Mq=oper(M,q)
        if Lng(Mq)>13: row.append('-');continue
        row.append(cond(Mq) if is_std(tuple(Mq)) else 'ns')
    # endpoint at q=2 (M[2] vs M[3]) if computable
    ep='?'
    try:
        Mq=oper(M,2);Msq=oper(M,3)
        if Lng(Msq)<=12 and is_std(tuple(Mq)) and is_std(tuple(Msq)):
            ep=(spineLeaf(Trans(Msq))==bpHeadT(Trans(Mq)))
    except: ep='err'
    allV=all(c=='V' for c in row if c not in('-','ns'))
    print("  %-22s gpar=%-5s iters=%s allV=%s ep(q2)=%s"%(rm.fmt(M),gp(M),row,allV,ep))
