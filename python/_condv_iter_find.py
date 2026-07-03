import sys,functools,os,subprocess,itertools
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import oper,Lng,entry,parent,TrMax,monoT,Br,seg
import red_model as rm
from trans_model import Trans,Mark,Adm,ZB,PB,bpHeadT,condV,condVI,condI,condIII
BMS=os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),"tmp","yaBMS","c","bms")
@functools.lru_cache(None)
def is_std(t): return subprocess.run([BMS,"-s",rm.fmt(list(t))],capture_output=True,text=True).stdout.strip()=="1"
def sf(T):
    if T==ZB:return '0'
    return '('+','.join('D%s%s'%(p[1],sf(p[2])) for p in T[1])+')' if len(T[1])>1 else 'D%s%s'%(T[1][0][1],sf(T[1][0][2]))
def spineLeaf(T):
    h=bpHeadT(T);pb=PB(h);return None if not pb else bpHeadT(pb[-1])
# find seeds M whose iterate oper(M,2) is condV (non-adjacent parent), standard
found=0
cols=[(a,b) for a in range(4) for b in range(3)]
for L in (3,4):
  for tM in itertools.product(cols,repeat=L):
    M=list(tM)
    if not(M[0]==(0,0) and entry(M,1,1)>0):continue
    if not monoT(M):continue
    ok=True
    iters={}
    for q in (1,2,3):
      Mq=oper(M,q)
      if Lng(Mq)<3 or Lng(Mq)>11: ok=False;break
      iters[q]=Mq
    if not ok: continue
    # require condV at q=2 and q=3 (genuine condV iterate regime)
    if not (condV(iters[2]) and condV(iters[3])): continue
    if not (is_std(tuple(iters[2])) and is_std(tuple(iters[3])) and is_std(tuple(iters[1]))): continue
    found+=1
    print("M=%s : iterates condV"%rm.fmt(M))
    for q in (1,2,3):
      mq=iters[q]
      print("   q=%d M[q]=%s Trans=%s"%(q,rm.fmt(mq),sf(Trans(mq))))
    # endpoint q->q+1 (full iterate) and surgery form
    for q in (1,2):
      tY=Trans(iters[q]); tN=Trans(iters[q+1])
      ep=(spineLeaf(tN)==bpHeadT(tY))
      print("   ENDPOINT q=%d: spineLeaf(Trans M[%d])=%s vs bpHeadT(Trans M[%d])=%s -> %s"%(q,q+1,sf(spineLeaf(tN)),q,sf(bpHeadT(tY)),ep))
    if found>=4: break
  if found>=4: break
print("condV-iterate families found:",found)
