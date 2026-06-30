import sys,functools,os,subprocess,itertools,collections
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng,entry,monoT,parent,TrMax,Br,seg,oper)
import red_model as rm
from trans_model import (Trans,Mark,Pred,reduced,Adm,ZB,PB,bpHeadT,condV)
BMS=os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),"tmp","yaBMS","c","bms")
@functools.lru_cache(None)
def is_std(t): return subprocess.run([BMS,"-s",rm.fmt(list(t))],capture_output=True,text=True).stdout.strip()=="1"
def spineLeaf(T):
    h=bpHeadT(T);pb=PB(h);return None if not pb else bpHeadT(pb[-1])
def transJm1(M): return Adm(M,parent(M,0,Lng(M)-1))
def deepen(N):
    j1=Lng(N)-1; return j1>1 and Br(N)!=[] and monoT(N) and parent(N,0,j1)>TrMax(N)
st=collections.Counter(); cex=[]; deep_ok=[]
cols=[(a,b) for a in range(4) for b in range(3)]
seeds=[]
for L in (4,5):
  for tM in itertools.product(cols,repeat=L):
    M=list(tM)
    if not(M[0]==(0,0) and entry(M,1,1)>0):continue
    if not(monoT(M) and condV(M) and parent(M,0,Lng(M)-1)>TrMax(M)):continue
    if not is_std(tuple(M)):continue
    seeds.append(M)
    if len(seeds)>=12:break
  if len(seeds)>=12:break
for M in seeds:
  for q in (2,3):
    N=oper(M,q)
    if Lng(N)<3 or Lng(N)>11:continue
    try:
      if not(monoT(N) and deepen(N) and is_std(tuple(N))):continue
      X=N[:-1]
      if Lng(X)<2 or not monoT(X):continue
      tX=Trans(X); a=spineLeaf(tX); jm1=transJm1(X); mk=bpHeadT(Mark(X,jm1))
    except Exception:
      st['ERR']+=1;continue
    nondeg=(a!=ZB and mk!=ZB); ok=(a==mk)
    st[('q',q,'nondeg',nondeg,'ok',ok)]+=1
    if nondeg and ok and len(deep_ok)<6: deep_ok.append((M,q,X,a,jm1))
    if nondeg and not ok and len(cex)<8: cex.append((M,q,X,a,mk,jm1))
print("seeds:",len(seeds))
for k,v in sorted(st.items(),key=lambda x:str(x[0])):print("   ",k,v)
def sf(T):
    if T==ZB:return '0'
    return '('+','.join('D%s%s'%(p[1],sf(p[2])) for p in T[1])+')' if len(T[1])>1 else 'D%s%s'%(T[1][0][1],sf(T[1][0][2]))
print("NONDEG TRUE egs:")
for M,q,X,a,jm1 in deep_ok: print("  M=%s q=%d X=%s jm1=%d a=%s"%(rm.fmt(M),q,rm.fmt(X),jm1,sf(a)))
print("NONDEG CEX:")
for M,q,X,a,mk,jm1 in cex: print("  M=%s q=%d X=%s jm1=%d a=%s mk=%s"%(rm.fmt(M),q,rm.fmt(X),jm1,sf(a),sf(mk)))
