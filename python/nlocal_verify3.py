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

# CONJECTURE C1: for standard M, ANY slice seg M a b (b<=Lng-1), and consecutive
# P-components J-1,J of P(seg M a b) with row-0 tie, the row-1 weakly decreases.
# (i.e. descending(P(seg M a b)) tie-break -- the slice_P_descending core)
# CONJECTURE C2 (nonlocal_adj_tie generalized): for standard M and p<q absolute
# indices that are the heads (left-mins of the slice) with entry0 tie, the
# row-1 of q <= row-1 of p. Equivalent to C1 via head=absoff+IdxSum.
def main():
    maxlen,maxval,KMAX=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])
    Ns=[N for N in gen(maxlen,maxval,KMAX) if is_standard(N)]
    print(f"#std={len(Ns)}")
    c1tie=c1fail=0; ex1=[]
    # also: is the tie-break for slice-cut-heads = SkT_P_descending applied to seg M 0 b? 
    # i.e. does seg M a b 's P-component tie reduce to P(seg M 0 b) which IS standard prefix?
    c3tie=c3fail=0; ex3=[]
    for M in Ns:
        L=Lng(M)
        for a in range(L):
            for b in range(a, L):
                S=seg(M,a,b)
                if not S: continue
                PS=P(S); idx=IdxSum(PS)
                for J in range(1,len(PS)):
                    if entry(PS[J-1],0,0)==entry(PS[J],0,0):
                        c1tie+=1
                        if not (entry(PS[J],1,0)<=entry(PS[J-1],1,0)):
                            c1fail+=1; ex1.append((fmt(M),a,b,J))
    print(f"C1 slice_P tie-break (any slice of std M): {c1tie} ties, {c1fail} FAIL ex={ex1[:5]}")
main()
