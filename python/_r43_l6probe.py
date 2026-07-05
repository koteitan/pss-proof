import sys, itertools, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-s4a/python')
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-s4b/python')
from red_model import Lng, entry, monoT, Br, FirstNodes, Joints, Red, TrMax
import _r36_bridges as B
def norm(x): return [tuple(p) for p in x]
def isred(x): return norm(Red(norm(x)))==norm(x)
def descending(bs):
    for J0 in range(len(bs)):
        for J1 in range(J0,len(bs)):
            a0,b0=bs[J0][0]; a1,b1=bs[J1][0]
            if not (a0>=a1 and (a0!=a1 or b0>=b1)): return False
    return True
def reg7x(M):
    if Lng(M)-1<=1: return False
    if not monoT(M): return False
    b=Br(M)
    if not b: return False
    J1=len(b)-1; fn=FirstNodes(M); jt=Joints(M)
    if fn[J1] is None or jt[J1] is None: return False
    if not (entry(M,1,fn[J1])<entry(M,0,fn[J1])): return False
    if not (0<jt[J1] and jt[J1]<TrMax(M)): return False
    if not descending(b): return False
    if not isred(M): return False
    return True
t0=time.time(); found=0; ok=0; c1=c3=csplit=0; tried=0
cells=[(a,b) for a in range(4) for b in range(3)]
for L in (6,7):
  for tup in itertools.product(cells, repeat=L-1):
    tried+=1
    if tried%50000==0: print("tried",tried,"found",found,"ok",ok,"t=%.0f"%(time.time()-t0),flush=True)
    M=[(0,0)]+list(tup)
    if not monoT(M): continue
    if not Br(M): continue
    if not reg7x(M): continue
    found+=1
    r=B.check_bridges(M)
    if r[0]=='ok': ok+=1; c1+=1; c3+=1; csplit+=1
    else:
        s=r[2] if len(r)>2 else ''
        c1 += 1 if 'okN=True' in s else 0
        c3 += 1 if 'okMpSlice=True' in s else 0
        csplit += 1 if 'okSplit=True' in s else 0
        print("FAIL", r, flush=True)
    if found<=8: print("HOST#%d Lng%d %s -> %s"%(found,Lng(M),M,r[0]),flush=True)
  print("L=%d cum found=%d ok=%d (1)=%d (3)=%d split=%d t=%.0f"%(L,found,ok,c1,c3,csplit,time.time()-t0),flush=True)
print("DONE tried=%d found=%d ok=%d per-conjunct (1)=%d (3)=%d split=%d"%(tried,found,ok,c1,c3,csplit),flush=True)
