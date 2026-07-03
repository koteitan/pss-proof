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
def gpar1(M): j1=Lng(M)-1; return parent(M,0,j1)>TrMax(M) if j1>0 else False
def spineLeaf(T):
    h=bpHeadT(T);pb=PB(h);return None if not pb else bpHeadT(pb[-1])
def sf(T):
    if T==ZB:return '0'
    return '('+','.join('D%s%s'%(p[1],sf(p[2])) for p in T[1])+')' if len(T[1])>1 else 'D%s%s'%(T[1][0][1],sf(T[1][0][2]))
# ITEM 3: regime closure - classify cond(M[1..5]) for condV-deepen seeds
print("=== ITEM 3: cond(M[q]) q=1..5 for standard condV-deepen seeds ===")
seeds=[]; cols=[(a,b) for a in range(4) for b in range(3)]
for L in (3,4,5):
  for tM in itertools.product(cols,repeat=L):
    M=list(tM)
    if not(M[0]==(0,0) and entry(M,1,1)>0):continue
    if not(monoT(M) and condV(M) and gpar1(M) and is_std(tuple(M))):continue
    seeds.append(M)
    if len(seeds)>=10:break
  if len(seeds)>=10:break
crack=[]
for M in seeds:
    row=[]
    for q in range(1,6):
        Mq=oper(M,q)
        if Lng(Mq)>13: row.append('-');continue
        c=cond(Mq) if is_std(tuple(Mq)) else 'nonstd'
        row.append(c)
    print("  %s -> %s"%(rm.fmt(M),row))
    if any(c=='VI' for c in row): crack.append(M)
print("  CRACK seeds (condV seed -> some condVI iterate):",[rm.fmt(m) for m in crack])
# ITEM 1: endpoint at depth q=3,4,5 for two condV families (with condV iterates)
print("\n=== ITEM 1: endpoint at depth (spineLeaf(Trans M[q+1]) vs bpHeadT(Trans M[q])) ===")
fams=[[(0,0),(1,1),(1,1),(1,1)],[(0,0),(1,1),(1,1),(1,2)]]
for M in fams:
    print(" family M=%s"%rm.fmt(M))
    for q in range(3,6):
        Mq=oper(M,q); Msq=oper(M,q+1)
        if Lng(Msq)>16: print("   q=%d skip(len %d)"%(q,Lng(Msq)));continue
        try:
            sl=spineLeaf(Trans(Msq)); bh=bpHeadT(Trans(Mq))
        except Exception as e: print("   q=%d err %s"%(q,e));continue
        eq=(sl==bh)
        if q==3:
            print("   q=3 cond(M[3])=%s cond(M[4])=%s"%(cond(Mq),cond(Msq)))
            print("        spineLeaf(Trans M[4]) = %s"%sf(sl))
            print("        bpHeadT  (Trans M[3]) = %s"%sf(bh))
            print("        EQUAL = %s"%eq)
        else:
            print("   q=%d EQUAL=%s"%(q,eq))
