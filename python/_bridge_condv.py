import sys,functools,os,subprocess,itertools
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import oper,Lng,entry,parent,TrMax,monoT,Br,seg
import red_model as rm
from trans_model import Trans,Mark,Adm,ZB,PB,bpHeadT,condV
BMS=os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),"tmp","yaBMS","c","bms")
@functools.lru_cache(None)
def is_std(t): return subprocess.run([BMS,"-s",rm.fmt(list(t))],capture_output=True,text=True).stdout.strip()=="1"
def sf(T):
    if T==ZB:return '0'
    return '('+','.join('D%s%s'%(p[1],sf(p[2])) for p in T[1])+')' if len(T[1])>1 else 'D%s%s'%(T[1][0][1],sf(T[1][0][2]))
def spineLeaf(T):
    h=bpHeadT(T);pb=PB(h);return None if not pb else bpHeadT(pb[-1])
def transJm1(M): return Adm(M,parent(M,0,Lng(M)-1))
def deepen(N): j1=Lng(N)-1; return j1>1 and Br(N)!=[] and monoT(N) and parent(N,0,j1)>TrMax(N)
# genuine condV-deepen instances: N standard, condV(N), deepen(N), spineLeaf(Trans(butlast N)) != 0
import collections
st=collections.Counter(); egs=[]
cols=[(a,b) for a in range(5) for b in range(4)]
for L in (4,5,6):
  for tN in itertools.product(cols,repeat=L):
    N=list(tN)
    if not(N[0]==(0,0) and entry(N,1,1)>0):continue
    if not(monoT(N) and condV(N) and deepen(N)):continue
    if not is_std(tuple(N)):continue
    X=N[:-1]
    if Lng(X)<2 or not monoT(X):continue
    try:
      a=spineLeaf(Trans(X)); j=transJm1(X); mk=bpHeadT(Mark(X,j))
    except: st['ERR']+=1; continue
    if a==ZB: st['a=0 (degenerate)']+=1; continue
    ok=(a==mk)
    st[('NONDEG-condV bridge a==bpHeadT(Mark X jm1)',ok)]+=1
    if not ok and len(egs)<6: egs.append((N,X,a,mk,j))
print("genuine condV-deepen, NON-degenerate bridge check:")
for k,v in sorted(st.items(),key=lambda x:str(x[0])):print("   ",k,v)
print("counterexamples (if any):")
for N,X,a,mk,j in egs: print("  X=%s jm1=%d a=%s mk=%s"%(rm.fmt(X),j,sf(a),sf(mk)))
