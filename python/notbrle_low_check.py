import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import *

# ---- rank-stratified standard pair-sequence generator ----
# Standard forms via BMS expansion: start from small standard seqs, expand by oper.
# We collect standard M with M = N[n] (M in SkT(Suc k), N in SkT(k)) at various ranks.

def all_seqs(maxlen, maxval):
    # enumerate candidate pair sequences (small), keep standard ones
    res=[]
    vals=range(maxval+1)
    for L in range(1,maxlen+1):
        for body in itertools.product(itertools.product(vals,vals), repeat=L):
            M=list(body)
            if entry(M,0,0)!=0 or entry(M,1,0)!=0: continue
            try:
                if is_standard(M): res.append(M)
            except Exception:
                pass
    return res

# Build N-pool (standard), then M = oper(N,n) standard (n>=1). d0pos i1=1 case.
def d0pos_witnesses(Npool, ns=(1,2,3)):
    wits=[]
    for N in Npool:
        if Lng(N)<2: continue
        if not monoT(N):
            # we need N monoT for the IHk-on-N monoT branch; but article also allows multi N.
            # focus on the i1=1 d0pos slice setup: idx1 N (Lng N-1)=1
            pass
        j1N=Lng(N)-1
        if idx1(N,j1N)!=1: continue
        if not hasParent(N,1,j1N): continue
        jm2=parent(N,1,j1N)
        if jm2 is None or jm2>=j1N: continue
        delta=entry(N,0,j1N)-entry(N,0,jm2)
        if delta<=0: continue
        for n in ns:
            M=oper(N,n)
            if Lng(M)<2: continue
            try:
                if not is_standard(M): continue
            except Exception:
                continue
            wits.append((N,n,M,jm2,j1N,delta))
    return wits

# ---- (b) P((IncrFirst^^s) X) = map (IncrFirst^^s) (P X) ----
def check_b(Xpool, smax=4):
    fails=0; tot=0
    for X in Xpool:
        for s in range(smax+1):
            lhs=P(funpow(IncrFirst,s,X))
            rhs=[funpow(IncrFirst,s,c) for c in P(X)]
            tot+=1
            if lhs!=rhs:
                fails+=1
                if fails<=3: print("FAIL(b)",fmt(X),s)
    print(f"(b) P_funpow_IncrFirst: {tot-fails}/{tot}")
    return fails

# ---- (a) the LOW source seg-shift identity ----
# Setup per the spec (d0pos i1=1, M=N[n]):
#   w = j1N - jm2 ; j0prime, j1prime define M' = seg M j0prime j1prime monoT
#   q = (j0prime - jm2) div w ; j0red = jm2 + (j0prime-jm2) mod w ; Np=seg N j0red (Lng N-1)
#   fnM = j0prime + FirstNodes(M')!J1 ; J1 = Lng(Br Np)-1
#   CLAIM (a): seg M j0prime (fnM-1) = (IncrFirst^^(q*delta)) (seg N j0red (j0red+(fnM-1-j0prime)))
def check_a(wits):
    fails=0; tot=0; tested=0
    for (N,n,M,jm2,j1N,delta) in wits:
        w=j1N-jm2
        LM=Lng(M)
        # iterate over monoT slices M' = seg M j0prime j1prime with jm2 <= j0prime (regime B)
        for j0p in range(0,LM):
            for j1p in range(j0p+1,LM):
                Mp=seg(M,j0p,j1p)
                if Lng(Mp)<2: continue
                if not monoT(Mp): continue
                # need leR M 0 j0p j1p
                if not leR(M,0,j0p,j1p): continue
                # focus regime B: j0p >= jm2
                if j0p<jm2: continue
                # q, j0red
                q=(j0p-jm2)//w
                j0red=jm2+((j0p-jm2)%w)
                if j0red>=Lng(N): continue
                Np=seg(N,j0red,Lng(N)-1)
                if Lng(Np)<1: continue
                brNp=Br(Np)
                J1=Lng(brNp)-1
                if J1<0: continue
                fn=FirstNodes(Mp)
                if J1>=len(fn): continue
                fnM=j0p+fn[J1]
                if fnM-1<j0p: continue
                if fnM-1>=LM: continue
                tested+=1
                lhs=seg(M,j0p,fnM-1)
                rj1=j0red+(fnM-1-j0p)
                if rj1>=Lng(N):
                    # out of range -> skip (period reduction assumption)
                    tested-=1
                    continue
                rhs=funpow(IncrFirst, q*delta, seg(N,j0red,rj1))
                tot+=1
                if lhs!=rhs:
                    fails+=1
                    if fails<=5:
                        print("FAIL(a) N=",fmt(N),"n=",n,"j0p=",j0p,"j1p=",j1p,
                              "q=",q,"j0red=",j0red,"delta=",delta)
                        print("   lhs=",fmt(lhs))
                        print("   rhs=",fmt(rhs))
    print(f"(a) LOW source seg-shift: {tot-fails}/{tot} (tested slices {tested})")
    return fails

if __name__=="__main__":
    print("enumerating standard seqs (this calls bms -s)...")
    pool=all_seqs(maxlen=5, maxval=3)
    print("standard pool size:", len(pool))
    # (b): test on the whole pool plus IncrFirst variants
    fb=check_b(pool, smax=4)
    # (a): build d0pos witnesses
    wits=d0pos_witnesses(pool, ns=(1,2,3))
    print("d0pos i1=1 witnesses:", len(wits))
    fa=check_a(wits)
    print("TOTAL FAILS:", fb+fa)

# ---- (a') verify the LOW slice stays within ONE block q (the structural assumption) ----
def check_a_oneblock(wits):
    fails=0; tot=0
    for (N,n,M,jm2,j1N,delta) in wits:
        w=j1N-jm2; LM=Lng(M)
        for j0p in range(0,LM):
            for j1p in range(j0p+1,LM):
                Mp=seg(M,j0p,j1p)
                if Lng(Mp)<2 or not monoT(Mp): continue
                if not leR(M,0,j0p,j1p): continue
                if j0p<jm2: continue
                q=(j0p-jm2)//w
                j0red=jm2+((j0p-jm2)%w)
                if j0red>=Lng(N): continue
                Np=seg(N,j0red,Lng(N)-1)
                if Lng(Np)<1: continue
                brNp=Br(Np); J1=Lng(brNp)-1
                if J1<0: continue
                fn=FirstNodes(Mp)
                if J1>=len(fn): continue
                fnM=j0p+fn[J1]
                if fnM-1<j0p or fnM-1>=LM: continue
                rj1=j0red+(fnM-1-j0p)
                if rj1>=Lng(N): continue
                tot+=1
                # assumption: fnM-1 stays in block q : fnM-1 < jm2 + (q+1)*w
                if not (fnM-1 < jm2 + (q+1)*w):
                    fails+=1
                    if fails<=5: print("FAIL oneblock", fmt(N),j0p,fnM,q)
    print(f"(a') LOW slice stays in block q: {tot-fails}/{tot}")
    return fails

if __name__=="__main__" and "oneblock" in sys.argv:
    pool=all_seqs(maxlen=5, maxval=3)
    wits=d0pos_witnesses(pool, ns=(1,2,3))
    check_a_oneblock(wits)
