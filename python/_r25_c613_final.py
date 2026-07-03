import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _r15_vx_lib import Trans, operB, numBT, lessBT, gen_pool, mono_hosts, guarded, SKIP
from red_model import Lng, entry, parent, oper, fmt
from trans_model import adm
def condVI(M):
    j1=Lng(M)-1; jp=parent(M,0,j1)
    if jp is None: return False
    return entry(M,1,j1)>0 and entry(M,1,jp)+1==entry(M,1,j1) and jp+1==j1
def j0(M): return parent(M,0,Lng(M)-1)
pool=gen_pool(maxlen=11,maxn=6,maxseed=4,cap=8000,oper_budget=4)
hosts=mono_hosts(pool)
cvi=[]; seen=set()
for M in hosts:
    if Lng(M)-1>1 and condVI(M) and tuple(M) not in seen:
        seen.add(tuple(M)); cvi.append(M)
adm_h=[M for M in cvi if adm(M,j0(M))]; nadm_h=[M for M in cvi if not adm(M,j0(M))]
def TT(M): return guarded(Trans,M,budget=8)
def Toper(M,n): 
    Mn=guarded(oper,M,n,budget=6)
    return None if Mn is SKIP else guarded(Trans,Mn,budget=8)
def OB(TM,k): return guarded(lambda a,z:operB(a,z),TM,numBT(k),budget=6)
# adm conclusions
def test(hs, tag, strict_idx, eq_idx, shift_idx, eq_from, strict_from, shift_from):
    s1=s1t=e2=e2t=s3=s3t=0
    for M in hs:
        TM=TT(M)
        if TM is SKIP: continue
        for n in range(1,7):
            TMn=Toper(M,n)
            if TMn is None: continue
            # strict(1): lessBT(Trans(M[n]))(operB(TM,numBT strict_idx(n)))
            if n>=strict_from:
                o=OB(TM,strict_idx(n))
                if o is not SKIP: s1t+=1; s1+= (lessBT(TMn,o))
            # eq(2)
            if n>=eq_from:
                o=OB(TM,eq_idx(n))
                if o is not SKIP: e2t+=1; e2+= (TMn==o)
            # shift(3): lessBT(operB(TM,numBT shift_idx(n)))(Trans(M[n+1]))
            if n>=shift_from:
                TMn1=Toper(M,n+1)
                o=OB(TM,shift_idx(n))
                if TMn1 is not None and o is not SKIP:
                    s3t+=1; s3+= (lessBT(o,TMn1))
    print(f"{tag}: strict(1) {s1}/{s1t}  eq(2) {e2}/{e2t}  shift(3) {s3}/{s3t}")
# adm: strict numBT(n-1) n>=1; eq numBT(n-2) n>=2; shift numBT(n-2) n>=2
test(adm_h,"ADM ", lambda n:n-1, lambda n:n-2, lambda n:n-2, 2, 1, 2)
# nadm: strict numBT(n) n>=1; eq numBT(n-1) n>=1; shift numBT(n-1) n>=1
test(nadm_h,"NADM", lambda n:n, lambda n:n-1, lambda n:n-1, 1, 1, 1)
