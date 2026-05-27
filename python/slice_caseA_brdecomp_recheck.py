"""Methodology-corrected re-audit (is_standard + depth 5) of the §6.8 case-A
Br-decomposition facts in scope at the 9648 sorry.

Domain = faithful case-A (article 1466), d0zero, j0' < j0N:
  - N standard, 1 < Lng N, entry N 1 (Lng N-1) = 0, idx1=0,
  - n in {1,2,3}, j0N := parent N 0 (Lng N-1), j0' < j0N,
  - bge: Lng N - 1 <= j1' (jlarge), j1' < Lng (N[n]),
  - leR (N[n]) 0 j0' j1'.

With M' = seg (N[n]) j0' j1', N' = seg N j0' (Lng N-1):
Checks:
  (G)  descending (Br M')                                -- the goal
  (T)  TrMax M' == TrMax N'                              -- the proven brick
  (J)  entry N 0 j0N < entry N 0 (Lng N-1)               -- junction strict row0
  (DN) descending (Br N')                                -- IHk gives this
  Block / decomposition structure:
  (S)  branch region S = seg M' (TrMax M'+1)(Lng M'-1);
       block-boundary cuts inside S are left-minimal (row0 minimum = N_{0,j0N})
  Also classify which sub-case A/B/C each instance is, to know coverage.
"""
import itertools, red_model as R

def gen(maxlen, maxval):
    for L in range(2, maxlen+1):
        for c in itertools.product(range(maxval+1), repeat=2*L):
            M=[(c[2*j],c[2*j+1]) for j in range(L)]
            if M[0]==(0,0): yield M

def descending(blocks):
    # cdom along index: head pair lexicographic (row0 then row1) weakly decreasing
    for J in range(len(blocks)-1):
        a0,a1=R.entry(blocks[J],0,0),R.entry(blocks[J],1,0)
        b0,b1=R.entry(blocks[J+1],0,0),R.entry(blocks[J+1],1,0)
        if (a0<b0) or (a0==b0 and a1<b1): return False
    return True

def audit(maxlen=5, maxval=4):
    std=0; total=0
    gfail=[]; tfail=[]; jfail=[]; dnfail=[]
    caseA=0; caseB=0; caseC=0; other=0
    for N in gen(maxlen, maxval):
        try:
            if not R.is_standard(N): continue
        except Exception: continue
        std+=1
        Ln=R.Lng(N)
        if Ln<2 or R.entry(N,1,Ln-1)!=0: continue
        if R.idx1(N,Ln-1)!=0: continue
        j0N=R.parent(N,0,Ln-1)
        if j0N is None: continue
        for n in (1,2,3):
            Mn=R.oper(N,n); Lm=R.Lng(Mn)
            for j0p in range(0, j0N):                 # j0' < j0N
                for j1p in range(max(j0p+1, Ln-1), Lm):  # jlarge: Lng N-1 <= j1'
                    if not R.leR(Mn,0,j0p,j1p): continue
                    total+=1
                    Mp=R.seg(Mn,j0p,j1p)
                    Np=R.seg(N,j0p,Ln-1)
                    # (G)
                    if not descending(R.Br(Mp)): gfail.append((R.fmt(N),n,j0p,j1p))
                    # (T)
                    if R.TrMax(Mp)!=R.TrMax(Np): tfail.append((R.fmt(N),n,j0p,j1p,R.TrMax(Mp),R.TrMax(Np)))
                    # (J)
                    if not (R.entry(N,0,j0N) < R.entry(N,0,Ln-1)):
                        jfail.append((R.fmt(N),n,j0p,j1p))
                    # (DN)
                    if not descending(R.Br(Np)): dnfail.append((R.fmt(N),n,j0p,j1p))
                    # classify A/B/C on TrMax(N') vs j0N-j0', j_{-1}
                    tN=R.TrMax(Np)
                    if j0N-j0p <= tN: caseA+=1
                    else:
                        # j_{-1} = parent of (j0N-j0') in N' (row0)
                        jm1=R.parent(Np,0,j0N-j0p)
                        if jm1 is not None and jm1 <= tN < j0N-j0p: caseB+=1
                        elif jm1 is not None and tN < jm1: caseC+=1
                        else: other+=1
    print(f"standard={std}  case-A-domain instances={total}")
    print(f"sub-case counts: A={caseA} B={caseB} C={caseC} other={other}")
    print(f"(G) descending(Br M') FAILS = {len(gfail)}"); [print("  G",m) for m in gfail[:8]]
    print(f"(T) TrMax M'==TrMax N' FAILS = {len(tfail)}"); [print("  T",m) for m in tfail[:8]]
    print(f"(J) N_{{0,j0N}} < N_{{0,Lng-1}} FAILS = {len(jfail)}"); [print("  J",m) for m in jfail[:8]]
    print(f"(DN) descending(Br N') FAILS = {len(dnfail)}"); [print("  DN",m) for m in dnfail[:8]]

if __name__=="__main__":
    audit()
