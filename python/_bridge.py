import sys,functools,os,subprocess,itertools,collections
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng,entry,monoT,parent,TrMax,Br,FirstNodes,Joints,seg)
import red_model as rm
from trans_model import (Trans,Mark,Pred,reduced,Adm,ZB,PB,bpHeadV,bpHeadT)
BMS=os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),"tmp","yaBMS","c","bms")
@functools.lru_cache(None)
def is_std(t): return subprocess.run([BMS,"-s",rm.fmt(list(t))],capture_output=True,text=True).stdout.strip()=="1"
def spineLeaf(T):
    h=bpHeadT(T);pb=PB(h);return None if not pb else bpHeadT(pb[-1])
def transJ0(M): return parent(M,0,Lng(M)-1)
def transJm1(M): return Adm(M,transJ0(M))
def dom(M):
    try:return reduced(M) and Lng(M)>=1
    except:return False
def deepen(N):
    j1=Lng(N)-1
    return j1>1 and Br(N)!=[] and monoT(N) and parent(N,0,j1)>TrMax(N)
pat=collections.Counter(); found=0; egs=[]
cols=[(a,b) for a in range(5) for b in range(4)]
for L in range(4,7):
  if found>=40:break
  for tN in itertools.product(cols,repeat=L):
    N=list(tN)
    if not(N[0]==(0,0) and entry(N,1,1)>0):continue
    if not monoT(N) or not deepen(N):continue
    if not is_std(tuple(N)):continue
    X=N[:-1]
    if Lng(X)<2 or not(dom(X) and monoT(X)):continue
    try:
      tX=Trans(X); a=spineLeaf(tX)
    except:continue
    if a is None:continue
    found+=1
    # search inner slice Z=seg X i j with bpHeadT(Trans Z)==a
    jm1X=transJm1(X) if Lng(X)>1 else 0
    fnX=FirstNodes(X); jnX=Joints(X)
    matches=[]
    for i in range(Lng(X)):
      for j in range(i,Lng(X)):
        Z=seg(X,i,j)
        try:
          if bpHeadT(Trans(Z))==a: matches.append((i,j))
        except:pass
    # classify the smallest/most-natural match against structural indices
    tag='NONE'
    for (i,j) in matches:
      if j==Lng(X)-1:
        if i==jm1X: tag='Z=seg X jm1X end'
        elif i==transJ0(X): tag='Z=seg X j0X end'
        elif jnX and i==jnX[-1]: tag='Z=seg X Joints[-1] end'
        elif fnX and i==fnX[-1]: tag='Z=seg X FirstNodes[-1] end'
        else: tag='Z=seg X %d end'%i
        break
    pat[tag]+=1
    if len(egs)<6:
      egs.append((N,X,a,matches,jm1X,transJ0(X),fnX,jnX))
print("deepen instances:",found)
print("inner-slice Z pattern (a==bpHeadT(Trans Z)):")
for k,v in sorted(pat.items(),key=lambda x:-x[1]):print("   ",k,v)
print("\nexamples:")
for N,X,a,matches,jm1,j0,fn,jn in egs:
  print("  N=%s X=%s a=%r"%(rm.fmt(N),rm.fmt(X),a))
  print("     jm1X=%d j0X=%d FN=%s Joints=%s | Z-matches(i,j)=%s"%(jm1,j0,fn,jn,matches[:6]))
