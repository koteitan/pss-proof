import sys,itertools,collections,functools
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng,entry,monoT,zeroT,parent,TrMax,Br)
import red_model as rm
from trans_model import (Trans,Mark,Pred,reduced,Adm,ZB,Dpt,PB,bpHeadV,bpHeadT,_c2,
                         condI,condIII,condV,condVI,flatBT,scb_decomps,unflatBT)
import os,subprocess
BMS=os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),"tmp","yaBMS","c","bms")
@functools.lru_cache(maxsize=None)
def is_std(t):
    out=subprocess.run([BMS,"-s",rm.fmt(list(t))],capture_output=True,text=True).stdout.strip()
    return out=="1"
def transC1(M):
    jp=parent(M,0,Lng(M)-1);return Mark(Pred(M),Adm(M,jp))
def transC2(M):
    j1=Lng(M)-1;jp=parent(M,0,j1);c1=transC1(M)
    return _c2(M,j1,jp,bpHeadV(c1),bpHeadT(c1))
def scbSubst(c1,c2,x):
    ds=scb_decomps(x,flatBT(c1));return None if not ds else unflatBT(ds[0][0]+flatBT(c2)+ds[0][1])
def spineLeaf(T):
    h=bpHeadT(T);pb=PB(h);return None if not pb else bpHeadT(pb[-1])
def kind(M):
    return 'I' if condI(M) else 'III' if condIII(M) else 'V' if condV(M) else 'VI' if condVI(M) else 'o'
st=collections.Counter(); egs=[]; cexs=[]; seen=0
cols=[(a,b) for a in range(4) for b in range(3)]
for L in range(3,6):
  for tN in itertools.product(cols,repeat=L):
    N=list(tN)
    if not(entry(N,0,0)==0 and entry(N,1,0)==0):continue
    if not monoT(N):continue
    if not is_std(tuple(tN)):continue
    seen+=1
    try:tNt=Trans(N)
    except:continue
    for k in range(2,L):
      Y=N[:k];B=N[k:]
      if not monoT(Y) or not is_std(tuple(Y)):continue
      try:tY=Trans(Y)
      except:continue
      if tY==ZB:continue
      hosts_ok=all(is_std(tuple(Y+B[:m+1])) for m in range(len(B)))
      ep=(spineLeaf(tNt)==bpHeadT(tY))
      ks=tuple(kind(Y+B[:m+1]) for m in range(len(B)))
      st[('ep',ep,'hosts_std',hosts_ok)]+=1
      if ep and hosts_ok and len(egs)<6: egs.append((N,Y,B,ks,tY,tNt))
      if (not ep) and hosts_ok and len(cexs)<6:
        cexs.append((N,Y,B,ks,tY,tNt))
print("standard monoT N scanned:",seen)
for k,v in sorted(st.items(),key=lambda x:str(x[0])):print("  ",k,v)
print("\nendpoint=TRUE (hosts standard) examples:")
for N,Y,B,ks,tY,tN in egs:
    print("  N=%s Y=%s B=%s kinds=%s ep=True"%(rm.fmt(N),rm.fmt(Y),rm.fmt(B),ks))
print("\nendpoint=FALSE with ALL hosts standard (would be cex):")
for N,Y,B,ks,tY,tN in cexs:
    print("  N=%s Y=%s B=%s kinds=%s"%(rm.fmt(N),rm.fmt(Y),rm.fmt(B),ks))
    print("      TY=",tY)
    print("      TN=",tN)
    print("      spineLeaf(TN)=",spineLeaf(tN)," bpHeadT(TY)=",bpHeadT(tY))
