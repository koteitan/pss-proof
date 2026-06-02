"""Empirical check of 補題（条件(A)と(B)と係数の基本性質） (content.md 1096-1126).
EXACT statements (as in pss_paper p_6_6_condAB_coeff / m_6_6_condAB_coeff):
  Hyp: M in T_PS (nonempty), entry M 0 0 = 0, entry M 1 0 = 0, RedCondA M.
  (1) forall j <= Lng M - 1. entry M 0 j <= j
  (2) RedCondB M --> forall j <= Lng M - 1. entry M 0 j >= entry M 1 j
  (3) forall i<=1. (i=0 or (i=1 and RedCondB M)) -->
        forall j <= Lng M - 1.
          (EX j0' j1'. ~leR M i j0' j1' and j0' < j1' and j1' <= j) --> entry M i j < j
RedCondA M  := forall i<=1. forall j1'. hasParent M i j1' --> entry M i (parent M i j1')+1 = entry M i j1'
RedCondB M  := forall j1'. (~hasParent M 0 j1' and j1' <= Lng M -1) --> entry M 0 j1' = entry M 1 j1'
"""
import random, itertools
import red_model as R
from red_model import entry, Lng, hasParent, parent, leR

def RedCondA(M):
    n=Lng(M)
    for i in (0,1):
        for j1 in range(n):
            if hasParent(M,i,j1):
                if entry(M,i,parent(M,i,j1))+1 != entry(M,i,j1):
                    return False
    return True

def RedCondB(M):
    n=Lng(M)
    for j1 in range(n):
        if (not hasParent(M,0,j1)) and j1 <= n-1:
            if entry(M,0,j1) != entry(M,1,j1):
                return False
    return True

def check_part1(M):
    n=Lng(M)
    for j in range(n):  # j <= Lng M -1
        if not (entry(M,0,j) <= j): return False,(j,)
    return True,None

def check_part2(M):
    if not RedCondB(M): return True,None  # vacuous
    n=Lng(M)
    for j in range(n):
        if not (entry(M,0,j) >= entry(M,1,j)): return False,(j,)
    return True,None

def gap_exists(M,i,j):
    # EX j0' j1'. ~leR M i j0' j1' and j0'<j1' and j1'<=j
    n=Lng(M)
    for j1p in range(0,j+1):
        for j0p in range(0,j1p):
            if not leR(M,i,j0p,j1p):
                return True
    return False

def check_part3(M):
    n=Lng(M)
    cb=RedCondB(M)
    for i in (0,1):
        if not (i==0 or (i==1 and cb)): continue
        for j in range(n):
            if gap_exists(M,i,j):
                if not (entry(M,i,j) < j): return False,(i,j)
    return True,None

def gen_random(maxlen, maxval):
    n=random.randint(1,maxlen)
    M=[(0,0)]
    for _ in range(1,n):
        M.append((random.randint(0,maxval), random.randint(0,maxval)))
    return M

def gen_reduced_like(maxlen, maxval):
    # bias toward sequences likely satisfying RedCondA: build coefficients that
    # often look like parent+1. Start diagonal then small perturbations.
    n=random.randint(2,maxlen)
    M=[(0,0)]
    for j in range(1,n):
        a=random.randint(0,min(j,maxval)); b=random.randint(0,min(j,maxval))
        M.append((a,b))
    return M

def run(N=200000, maxlen=14, maxval=6):
    total_A=0          # M satisfying all hyps (T_PS, M00=M10=0, RedCondA)
    wit1=wit2=wit3=0   # witnesses where the respective non-vacuous condition fires
    fail=0
    randgens=[gen_random, gen_reduced_like]
    for t in range(N):
        g=random.choice(randgens)
        M=g(maxlen,maxval)
        if Lng(M)==0: continue
        if entry(M,0,0)!=0 or entry(M,1,0)!=0: continue
        if not RedCondA(M): continue
        total_A+=1
        # witness counts
        n=Lng(M)
        if any(entry(M,0,j)==j and j>0 for j in range(n)): wit1+=1
        if RedCondB(M): wit2+=1
        for i in (0,1):
            if (i==0 or (i==1 and RedCondB(M))) and any(gap_exists(M,i,j) for j in range(n)):
                wit3+=1; break
        ok1,e1=check_part1(M)
        ok2,e2=check_part2(M)
        ok3,e3=check_part3(M)
        if not (ok1 and ok2 and ok3):
            fail+=1
            if fail<=5:
                print("FAIL", R.fmt(M), "p1",ok1,e1,"p2",ok2,e2,"p3",ok3,e3,
                      "condB",RedCondB(M))
    print(f"trials={N} hyp-satisfying(total_A)={total_A} "
          f"wit1={wit1} wit2(condB)={wit2} wit3(gap)={wit3} FAILURES={fail}")
    return total_A,wit1,wit2,wit3,fail

if __name__=="__main__":
    random.seed(20260601)
    # main random pass
    run(N=300000, maxlen=14, maxval=6)
    # exhaustive small pass for completeness (len up to 5, vals up to 3)
    print("--- exhaustive small (len<=5, val<=3) ---")
    total_A=wit1=wit2=wit3=fail=0
    vals=range(4)
    for n in range(1,6):
        for tail in itertools.product(itertools.product(vals,vals), repeat=n-1):
            M=[(0,0)]+list(tail)
            if not RedCondA(M): continue
            total_A+=1
            nn=Lng(M)
            if any(entry(M,0,j)==j and j>0 for j in range(nn)): wit1+=1
            if RedCondB(M): wit2+=1
            for i in (0,1):
                if (i==0 or (i==1 and RedCondB(M))) and any(gap_exists(M,i,j) for j in range(nn)):
                    wit3+=1; break
            ok1,_=check_part1(M); ok2,_=check_part2(M); ok3,_=check_part3(M)
            if not(ok1 and ok2 and ok3):
                fail+=1
                if fail<=5: print("EXH FAIL",R.fmt(M))
    print(f"exhaustive total_A={total_A} wit1={wit1} wit2={wit2} wit3={wit3} FAILURES={fail}")
