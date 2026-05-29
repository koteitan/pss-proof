import sys, itertools
sys.path.insert(0,'python')
from red_model import *

# enumerate standard forms via oper from diagSeq, up to level KMAX
def gen_standard(maxlen, maxval, KMAX):
    seen=set()
    # base: diagSeq u v with u<=v
    base=[]
    for u in range(maxval+1):
        for v in range(u, maxval+1):
            base.append(diagSeq(u,v))
    frontier=list(base)
    allM=list(base)
    for k in range(KMAX):
        newf=[]
        for M in frontier:
            for n in range(1,4):
                Mp=oper(M,n)
                key=fmt(Mp)
                if key not in seen and len(Mp)<=maxlen and Mp:
                    if all(a<=maxval and b<=maxval for (a,b) in Mp):
                        seen.add(key); newf.append(Mp); allM.append(Mp)
        frontier=newf
    # dedup
    out={}
    for M in allM:
        out[fmt(M)]=M
    return list(out.values())

def main():
    maxlen=int(sys.argv[1]) if len(sys.argv)>1 else 6
    maxval=int(sys.argv[2]) if len(sys.argv)>2 else 3
    KMAX=int(sys.argv[3]) if len(sys.argv)>3 else 6
    Ms=gen_standard(maxlen,maxval,KMAX)
    # filter to is_standard
    std=[M for M in Ms if is_standard(M)]
    print(f"#candidates={len(Ms)} #standard={len(std)}")
    nadj=nsgl=ntie=nnloc=0
    fadj=fsgl=fnloc=0
    fnloc_ex=[]
    fadj_ex=[]; fsgl_ex=[]
    ndesc=0; fdesc=0
    for M in std:
        L=Lng(M)
        # nlocal_adj_tie on M directly
        for j in range(L-1):
            if entry(M,0,j)==entry(M,0,j+1):
                nnloc+=1
                if not (entry(M,1,j+1)<=entry(M,1,j)):
                    fnloc+=1; fnloc_ex.append((fmt(M),j))
        # slices: M'=seg M j0 j1 with leR M 0 j0 j1, monoT M
        if not monoT(M): continue
        for j0p in range(L):
            for j1p in range(j0p+1, L):
                if j1p> L-1: continue
                if not leR(M,0,j0p,j1p): continue
                Mp=seg(M,j0p,j1p)
                Br_Mp=Br(Mp)
                # check descending(Br Mp)
                ndesc+=1
                if not check_descending(Br_Mp):
                    fdesc+=1
                # Yp = seg Mp (TrMax Mp+1)(Lng Mp -1)
                if TrMax(Mp)==Lng(Mp)-1: continue
                Yp=seg(Mp, TrMax(Mp)+1, Lng(Mp)-1)
                PYp=P(Yp)
                idx=IdxSum(PYp)
                # absolute offset of Yp in M
                absoff=j0p+TrMax(Mp)+1
                for J in range(1,len(PYp)):
                    L0=entry(PYp[J-1],0,0); L1c=entry(PYp[J],0,0)
                    if L0==L1c:  # row-0 tie
                        ntie+=1
                        # (S-adj)
                        adjok = (idx[J]==idx[J-1]+1)
                        if adjok: nadj+=1
                        else: fadj+=1; fadj_ex.append((fmt(M),j0p,j1p,J,idx[J-1],idx[J]))
                        # (S-sgl)
                        sglok = (Lng(PYp[J-1])==1)
                        if sglok: nsgl+=1
                        else: fsgl+=1; fsgl_ex.append((fmt(M),j0p,j1p,J,Lng(PYp[J-1])))
    print(f"nlocal_adj_tie: {nnloc} ties, {fnloc} FAIL  ex={fnloc_ex[:3]}")
    print(f"descending(Br M'): {ndesc} slices, {fdesc} FAIL")
    print(f"row-0 tie pairs in Yp: {ntie}")
    print(f"(S-adj) pR=pL+1: {nadj} ok, {fadj} FAIL  ex={fadj_ex[:5]}")
    print(f"(S-sgl) Lng left comp=1: {nsgl} ok, {fsgl} FAIL  ex={fsgl_ex[:5]}")

def check_descending(Q):
    n=len(Q)
    for J0 in range(n):
        for J1 in range(J0,n):
            if entry(Q[J0],0,0)<entry(Q[J1],0,0): return False
            if entry(Q[J0],0,0)==entry(Q[J1],0,0) and entry(Q[J0],1,0)<entry(Q[J1],1,0): return False
    return True

main()
