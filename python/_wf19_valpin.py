import itertools, sys
from red_model import *

def npJ(M,J):
    b=Br(M); fn=FirstNodes(M)
    if entry(b[J],1,0)==0: return 0
    par=THE_nextR(M,1,fn[J])
    return par+1

def NJ(M,J):
    b=Br(M); jn=Joints(M); m00=entry(M,0,0); m10=entry(M,1,0)
    return [(m00+jn[J]+1, m10+npJ(M,J))]+b[J][1:]

def RedCondA(M):
    for i in range(2):
        for j1 in range(Lng(M)):
            if hasParent(M,i,j1):
                p=parent(M,i,j1)
                if entry(M,i,p)+1 != entry(M,i,j1):
                    return False
    return True

def RedCondB(M):
    for j1 in range(Lng(M)):
        if not hasParent(M,0,j1) and j1<=Lng(M)-1:
            if entry(M,0,j1)!=entry(M,1,j1):
                return False
    return True

def gen_cores(maxlen, maxval):
    seqs=[]
    for L in range(2,maxlen+1):
        for body in itertools.product(range(maxval+1), repeat=2*L):
            M=[(body[2*j],body[2*j+1]) for j in range(L)]
            if M[0]!=(0,0): continue
            try:
                if not monoT(M): continue
                if Red(M)!=M: continue
                if TrMax(M)==Lng(M)-1: continue
            except Exception:
                continue
            seqs.append(M)
    return seqs

def main():
    cores=gen_cores(5,3)
    print("reduced monoT nontrunk cores:", len(cores))
    ncase=0
    f_goal=f_ekk=f_q_eq_p=f_RedCondA_N=f_entry_Nq=f_no_par_kk=0
    f_Nred=0
    f_qrange=0
    exs=[]
    for M in cores:
        Jstar=len(Br(M))-1
        blks=[]
        for J in range(Jstar):
            np=npJ(M,J); jn=Joints(M)[J]; eJ=jn+1-np
            blks+=funpow(IncrFirst,eJ,Red(NJ(M,J)))
        off=1+TrMax(M)+len(blks)
        j1=Lng(M)-1
        i=1
        if not hasParent(M,i,j1): continue
        p=parent(M,i,j1)
        if p>=off: continue  # in-block; not our case
        Rs=Red(NJ(M,Jstar))
        kk=Lng(NJ(M,Jstar))-1
        if kk==0: continue   # only kk>0
        ncase+=1
        # value at last col of Rs row1
        eRs1kk = entry(Rs,1,kk)
        # build N
        d = eRs1kk-1 if eRs1kk>0 else None
        if eRs1kk>0:
            N = diagSeq(0,d)+Rs
        else:
            N = Rs
        # checks
        ok_goal = (entry(M,1,j1)==entry(M,1,p)+1)
        ok_ekk  = (eRs1kk==p+1)
        # diagonal parent index q
        q = eRs1kk-1
        # last column index in N
        lastN = Lng(N)-1
        # row1 value at lastN
        eN1last = entry(N,1,lastN)
        # parent of lastN in N row1
        hp = hasParent(N,1,lastN)
        parN = parent(N,1,lastN) if hp else None
        ok_entry_Nq = (entry(N,1,q)==q) if eRs1kk>0 else True
        # RedCondA N at last col gives entry N 1 (parent) +1 = eN1last
        # check that parent == q (the diagonal column)
        ok_parN_q = (parN==q) if (eRs1kk>0 and hp) else (not (eRs1kk>0))
        ok_q_eq_p = (q==p)
        ok_Nred = RedCondA(N) and RedCondB(N)
        # check Rs has NO row1 parent at kk
        no_par_kk = not hasParent(Rs,1,kk)
        if not ok_goal: f_goal+=1
        if not ok_ekk: f_ekk+=1
        if not ok_q_eq_p: f_q_eq_p+=1
        if not ok_entry_Nq: f_entry_Nq+=1
        if not ok_Nred: f_Nred+=1
        if not no_par_kk: f_no_par_kk+=1
        if not ok_parN_q: f_RedCondA_N+=1
        if eRs1kk>0 and not (0<=q<=lastN): f_qrange+=1
        if (not ok_ekk or not ok_q_eq_p) and len(exs)<8:
            exs.append((fmt(M),p,eRs1kk,q,parN,eN1last))
    print(f"row1 cross-block kk>0 cases: {ncase}")
    print(f"  goal entry M 1 j1 == entry M 1 p +1 : fail {f_goal}")
    print(f"  ekk  entry Rs 1 kk == p+1           : fail {f_ekk}")
    print(f"  q==p (diag parent idx == p)         : fail {f_q_eq_p}")
    print(f"  entry N 1 q == q (diag col value)   : fail {f_entry_Nq}")
    print(f"  parent N 1 lastN == q               : fail {f_RedCondA_N}")
    print(f"  RedCondA N & RedCondB N             : fail {f_Nred}")
    print(f"  NOT hasParent Rs 1 kk               : fail {f_no_par_kk}")
    print(f"  q in range                          : fail {f_qrange}")
    if exs: print("examples:", exs)

main()
