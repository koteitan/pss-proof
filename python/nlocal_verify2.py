import sys
sys.path.insert(0,'python')
from red_model import *

def check_descending(Q):
    n=len(Q)
    for J0 in range(n):
        for J1 in range(J0,n):
            if entry(Q[J0],0,0)<entry(Q[J1],0,0): return False
            if entry(Q[J0],0,0)==entry(Q[J1],0,0) and entry(Q[J0],1,0)<entry(Q[J1],1,0): return False
    return True

# generate (N, M=N[n]) pairs where N standard, idx1(N,LngN-1)=1 (d1pos branch)
def gen(maxlen,maxval,KMAX):
    base=[diagSeq(u,v) for u in range(maxval+1) for v in range(u,maxval+1)]
    frontier=list(base); allM=set(fmt(m) for m in base); store={fmt(m):m for m in base}
    for k in range(KMAX):
        newf=[]
        for M in frontier:
            for n in range(1,4):
                Mp=oper(M,n)
                key=fmt(Mp)
                if Mp and len(Mp)<=maxlen and all(a<=maxval and b<=maxval for(a,b)in Mp) and key not in allM:
                    allM.add(key); store[key]=Mp; newf.append(Mp)
        frontier=newf
    return list(store.values())

def main():
    maxlen,maxval,KMAX=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])
    Ns=[N for N in gen(maxlen,maxval,KMAX) if is_standard(N)]
    nadj=nsgl=ntie=0; fadj=fsgl=0; fadj_ex=[]; fsgl_ex=[]
    ndesc=fdesc=0; cnt=0
    for N in Ns:
        if Lng(N)<=1: continue
        if idx1(N,Lng(N)-1)!=1: continue   # need d1pos branch
        if not hasParent(N, idx1(N,Lng(N)-1), Lng(N)-1): continue
        for n in range(1,4):
            M=oper(N,n)
            if not M or len(M)>maxlen+4: continue
            if not is_standard(M): continue
            if not monoT(M): continue
            L=Lng(M)
            for j0p in range(L):
                for j1p in range(j0p+1,L):
                    if not leR(M,0,j0p,j1p): continue
                    Mp=seg(M,j0p,j1p)
                    Br_Mp=Br(Mp)
                    ndesc+=1
                    if not check_descending(Br_Mp): fdesc+=1
                    if TrMax(Mp)==Lng(Mp)-1: continue
                    Yp=seg(Mp,TrMax(Mp)+1,Lng(Mp)-1)
                    PYp=P(Yp); idx=IdxSum(PYp)
                    for J in range(1,len(PYp)):
                        if entry(PYp[J-1],0,0)==entry(PYp[J],0,0):
                            ntie+=1; cnt+=1
                            if idx[J]==idx[J-1]+1: nadj+=1
                            else: fadj+=1; fadj_ex.append((fmt(M),j0p,j1p,J))
                            if Lng(PYp[J-1])==1: nsgl+=1
                            else: fsgl+=1; fsgl_ex.append((fmt(M),j0p,j1p,J,Lng(PYp[J-1])))
    print(f"#std N (d1pos)={sum(1 for N in Ns if Lng(N)>1 and idx1(N,Lng(N)-1)==1)}")
    print(f"descending(Br M'): {ndesc} slices, {fdesc} FAIL")
    print(f"row-0 ties in Yp: {ntie}")
    print(f"(S-adj): {nadj} ok {fadj} FAIL ex={fadj_ex[:5]}")
    print(f"(S-sgl): {nsgl} ok {fsgl} FAIL ex={fsgl_ex[:5]}")

main()
