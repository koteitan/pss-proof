import sys; sys.path.insert(0,'python')
from red_model import *
def gen(maxlen,maxval,KMAX):
    base=[diagSeq(u,v) for u in range(maxval+1) for v in range(u,maxval+1)]
    frontier=list(base); store={fmt(m):m for m in base}
    for k in range(KMAX):
        newf=[]
        for M in frontier:
            for n in range(1,4):
                Mp=oper(M,n); key=fmt(Mp)
                if Mp and len(Mp)<=maxlen and all(a<=maxval and b<=maxval for(a,b)in Mp) and key not in store:
                    store[key]=Mp; newf.append(Mp)
        frontier=newf
    return list(store.values())
# CONJECTURE: for standard N and drop j N, the left-mins (P-component heads) of
# drop j N are a SUBSET of {0} ∪ {row-0 left-mins of N that are >= j}.
# More precisely: head positions of P(drop j N) (absolute = j + IdxSum) -- 
# are they each either j (the new first) or a genuine left-min of N?
# Check: for a row-0 TIE between consecutive heads p<q of P(drop j N), is the
# tie-break derivable from SkT_P_descending applied to consecutive heads of P N?
# Simplest test: do the head ABSOLUTE positions of P(drop j N) (excluding the
# very first head=j) coincide with row-0 left-minima of N (global)?
def lmin_global(N,p):
    return all(entry(N,0,t)>=entry(N,0,p) for t in range(p))
def main():
    maxlen,maxval,KMAX=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])
    Ns=[N for N in gen(maxlen,maxval,KMAX) if is_standard(N)]
    tot=0; nonglob=0; ex=[]
    # also test: are P(drop j N) components = corresponding suffix-components of P N?
    for N in Ns:
        L=Lng(N)
        for j in range(L):
            D=N[j:]
            if not D: continue
            PD=P(D); idx=IdxSum(PD)
            for J in range(1,len(PD)):   # skip first head (=j) 
                p=j+idx[J]
                tot+=1
                if not lmin_global(N,p):
                    nonglob+=1; ex.append((fmt(N),j,J,p))
    print(f"non-first heads of P(drop j N): {tot}, NOT global left-min: {nonglob} ex={ex[:5]}")
main()
