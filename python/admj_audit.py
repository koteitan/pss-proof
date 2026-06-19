"""A18 empirical check: for reduced M with a unique NextAdm-parent j0 of
j1=Lng-1, are there row-0 ancestors j<=_M j0 that are NOT M-admissible?
(Yes -> p_7_4_Mark_nextAdm needs (M,j) in Marked, correction A18.)"""
from fast_pss import Lng, entry, le0, nextrel1, enum_reduced_tiling
def nadm(M,j):
    n=Lng(M)
    if j>n: return True
    if j-1<0: return False
    return nextrel1(M,j-1,j) and nextrel1(M,j,j+1)
def adm(M,j): return not nadm(M,j)
def nextAdm0(M,j0,j1):
    if not (le0(M,j0,j1) and j0<j1 and adm(M,j0)): return False
    return all((not le0(M,j,j1)) or (not adm(M,j)) for j in range(j0+1,j1))
if __name__=='__main__':
    cnt=uniq=0; viol=[]
    for M in enum_reduced_tiling(maxlen=5,maxe=3):
        n=Lng(M)
        if n<2: continue
        cnt+=1; j1=n-1
        ps=[j0 for j0 in range(j1) if nextAdm0(M,j0,j1)]
        if len(ps)!=1: continue
        uniq+=1; j0=ps[0]
        for j in range(j0+1):
            if le0(M,j,j0) and not adm(M,j): viol.append((M,j0,j)); break
    print(f"reduced>=2={cnt}, unique-nextAdm={uniq}, non-adm-ancestor violations={len(viol)}")
