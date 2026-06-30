import sys,functools,os,subprocess
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng,entry,monoT,parent,TrMax,Br)
import red_model as rm
from trans_model import (Trans,ZB,PB,bpHeadT)
BMS=os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),"tmp","yaBMS","c","bms")
def is_std(M): return subprocess.run([BMS,"-s",rm.fmt(M)],capture_output=True,text=True).stdout.strip()=="1"
def spineLeaf(T):
    h=bpHeadT(T);pb=PB(h);return None if not pb else bpHeadT(pb[-1])
def sf(T):
    if T==ZB:return '0'
    return '('+','.join('D%s%s'%(p[1],sf(p[2])) for p in T[1])+')' if len(T[1])>1 else 'D%s%s'%(T[1][0][1],sf(T[1][0][2]))
Y=[(0,0),(1,0)]; B=[(2,0),(3,0)]; N=Y+B
print("=== m_8_5_surgery_fullprefix hypotheses for Y=%s B=%s ==="%(rm.fmt(Y),rm.fmt(B)))
print("Nst: Y@B in ST_PS         :", is_std(N))
print("Npt: monoT(Y@B) (=>PT_PS) :", monoT(N), " std:",is_std(N))
print("YL2: 1<Lng Y              :", Lng(Y)>1)
tY=Trans(Y)
print("prev: Trans Y             :", sf(tY)," = Dpt 0 (0 +B Dpt 0 0): e10=0,t2=0,vm1=0,z=0")
print("e10v: entry Y 1 0 = e10=0 :", entry(Y,1,0)==0)
for m in range(len(B)):
    h=Y+B[:m+1]; j1=Lng(h)-1
    print("  col %d host=%s : gBrne Br!=[]=%s  gpar par(%d)>TrMax(%d)=%s  std=%s monoT=%s j1>1=%s"%(
       m,rm.fmt(h),Br(h)!=[],parent(h,0,j1),TrMax(h),parent(h,0,j1)>TrMax(h),is_std(h),monoT(h),j1>1))
tN=Trans(N)
print("CONCLUSION/endpoint: spineLeaf(Trans(Y@B))=%s  vs bpHeadT(Trans Y)=%s"%(sf(spineLeaf(tN)),sf(bpHeadT(tY))))
print("  Trans(Y@B)=",sf(tN)," => endpoint HOLDS:", spineLeaf(tN)==bpHeadT(tY))
print("  (B=(2,0)(3,0) is TWO oper periods => TWO C-wraps; scaffold gives no single-period constraint)")
