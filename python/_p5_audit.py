"""A21 part(5) empirical audit under condition (I)."""
import itertools, sys
from red_model import (Lng, entry, seg, Red, parent, Pred, oper, adm, Adm,
                       nextR, leR, monoT, reduced)
import red_model as rm
from trans_model import Trans

def transCondI(M):
    j1=Lng(M)-1
    return entry(M,1,j1)==0 and adm(M, parent(M,0,j1))

def transCondVI(M):
    j1=Lng(M)-1; j0=parent(M,0,j1)
    if j0 is None: return False
    return entry(M,1,j1)>0 and entry(M,1,j0)+1==entry(M,1,j1) and j0+1==j1

ZERO=rm.diagSeq(0,0)  # [(0,0)] -> 0_B placeholder
def is0B(t):
    return t==[(0,0)] or t==0 or str(t)=='0B' or t is None

# enumerate small reduced PT_PS pairseqs
def gen_seqs(maxlen, maxe):
    for L in range(2, maxlen+1):
        # row1 nondecreasing-ish; brute force all
        cols=[(a,b) for a in range(maxe+1) for b in range(maxe+1)]
        for M in itertools.product(cols, repeat=L):
            M=list(M)
            if entry(M,0,0)!=0 or entry(M,1,0)!=0: continue
            yield M

def in_PT_RT(M):
    # PT_PS = monoT (principal term, no multi). RT_PS = reduced.
    if not monoT(M): return False
    try:
        if not reduced(M): return False
    except Exception:
        return False
    return True

def check(maxlen=4, maxe=3, nmax=4):
    total=0; viol=0; examples=[]
    for M in gen_seqs(maxlen, maxe):
        if not in_PT_RT(M): continue
        j1=Lng(M)-1
        if not (j1>1): continue
        j0=parent(M,0,j1)
        if j0 is None: continue
        if not adm(M, j0): continue
        if not (entry(M,1,j0) >= entry(M,1,j1)): continue
        if not transCondI(M): continue
        # unique next-parent j0' of j0 in row 0
        cands=[j for j in range(Lng(M)) if nextR(M,0,j,j0)]
        if len(cands)!=1: continue
        j0p=cands[0]
        jm1p=Adm(M, j0p)
        for n in range(2, nmax+1):
            Mn=oper(M,n)
            idx=j0+(n-1)*(j1-j0)
            if idx>=Lng(Mn):
                examples.append(("IDX_OOB",M,n,idx,Lng(Mn))); continue
            N=seg(Mn,0,idx)
            total+=1
            ok=True
            reasons=[]
            # (M[n], idx) in Marked
            if not rm.marked(Mn, idx): ok=False; reasons.append("notMarked")
            # nextR (M[n]) 0 j0' idx
            if not nextR(Mn,0,j0p,idx): ok=False; reasons.append("nextR")
            # Lng N - 1 = idx
            if Lng(N)-1 != idx: ok=False; reasons.append("LngN")
            # parent N 0 (Lng N -1) = j0'
            pN=parent(N,0,Lng(N)-1)
            if pN != j0p: ok=False; reasons.append(f"parentN({pN}!={j0p})")
            # Adm N (parent N 0 (Lng N-1)) = jm1'
            if pN is not None and Adm(N, pN) != jm1p: ok=False; reasons.append("AdmN")
            # Trans (Pred N) != 0B
            try:
                tp=Trans(Pred(N))
                if is0B(tp): ok=False; reasons.append("TransPred0")
            except Exception as e:
                reasons.append("TransErr");
            # not transCondVI N
            if transCondVI(N): ok=False; reasons.append("condVI")
            if not ok:
                viol+=1
                if len(examples)<25: examples.append((M,n,reasons))
    print(f"total checks={total}, violations={viol}")
    for e in examples[:25]: print(e)

if __name__=='__main__':
    ml=int(sys.argv[1]) if len(sys.argv)>1 else 4
    me=int(sys.argv[2]) if len(sys.argv)>2 else 3
    nm=int(sys.argv[3]) if len(sys.argv)>3 else 4
    check(ml,me,nm)
