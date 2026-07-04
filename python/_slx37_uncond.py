import sys, itertools, random
from functools import lru_cache
sys.path.insert(0,'python')
import red_model as R
_orig=R.is_standard
@lru_cache(maxsize=None)
def _cs(f): return _orig(list(f))
def is_std(M): return _cs(tuple(M))
def condIIIorIV(M):
    j1=R.Lng(M)-1
    if not R.hasParent(M,0,j1): return False
    j0=R.parent(M,0,j1)
    return R.entry(M,1,j1)>0 and R.entry(M,1,j0)>=R.entry(M,1,j1)
# Test WITHOUT d=jlp guard: over the brne corpus (condIII/IV, jm3<jm2, hasParent, Br RNp != [])
st={'brne':0,'nextR_M_1_jm2_Lm2':0,'nextR_RNp_1_d_Tp':0,'eqd':0,'eqd_and_nextRNp':0,
    'noguard_but_nextRNp':0,'noguard_not_nextRNp':0}
cex=[]
def check(M):
    L=R.Lng(M); j1=L-1
    if not(1<j1): return
    if not R.hasParent(M,1,j1): return
    if not R.hasParent(M,0,j1): return
    if not condIIIorIV(M): return
    jm2=R.parent(M,1,j1); jm3=R.Adm(M,jm2)
    if not(jm3<jm2): return
    d=jm2-jm3
    N=R.seg(M,jm3,j1)
    try: RNp=R.Red(R.Pred(N))
    except Exception: return
    brp=R.Br(RNp)
    if len(brp)==0: return
    if not is_std(M): return
    st['brne']+=1
    lastp=len(brp)-1; jlp=R.Joints(RNp)[lastp]; fnp=R.FirstNodes(RNp)[lastp]
    Tp=R.Lng(RNp)-1
    nm=R.nextR(M,1,jm2,L-2); nr=R.nextR(RNp,1,d,Tp)
    if nm: st['nextR_M_1_jm2_Lm2']+=1
    if nr: st['nextR_RNp_1_d_Tp']+=1
    iseq=(d==jlp)
    if iseq: st['eqd']+=1
    if iseq and nr: st['eqd_and_nextRNp']+=1
    if (not iseq) and nr: st['noguard_but_nextRNp']+=1
    if (not iseq) and (not nr): st['noguard_not_nextRNp']+=1
    if iseq and not nr:
        if len(cex)<8: cex.append(('EQD_NO_nextRNp',R.fmt(M),'d',d,'Tp',Tp,'RNp',R.fmt(RNp)))
V=5
cols=[(a,b) for a in range(0,V+1) for b in range(0,a+1)]
for base_len in range(2,6):
    base=R.diagSeq(0,base_len-1)
    for t in range(1,4):
        for tail in itertools.product(cols,repeat=t):
            M=base+list(tail)
            if R.Lng(M)>10: continue
            try: check(M)
            except Exception: pass
random.seed(4)
V2=9
cols2=[(a,b) for a in range(0,V2+1) for b in range(0,a+1)]
for _ in range(20000):
    bl=random.randint(2,8); base=R.diagSeq(0,bl-1)
    t=random.randint(1,8)
    M=base+[random.choice(cols2) for _ in range(t)]
    if R.Lng(M)<4 or R.Lng(M)>12: continue
    try: check(M)
    except Exception: pass
print("UNCOND",st)
for c in cex: print("CEX",c)
