"""Verify the EXACT sub-case A (article 1484-1488) decomposition identities
used by the Isabelle proof at the 9660 sorry.

Sub-case A domain: faithful case-A (article 1466), d0zero, j0' < j0N,
  AND  j0N - j0' <= TrMax(N').

With M' = seg (N[n]) j0' j1', N' = seg N j0' (Lng N-1),
     J1 = Lng(Br N')-1, w = j1N - j0N, r = (j1' - (j0N + q*w)) ... (last block offset)
Check, per article 1486/1488:
  (FN)  FirstNodes(N')_{J1} = j1N - j0'
  (BRN) Br(N')_{J1} = (N_{j1N}) i.e. the singleton segment seg N j1N j1N
  (DEC) Br M' = take J1 (Br N')  @  replicate (n-2) blk  @  [partial]
        blk     = seg N j0N (j1N - 1)              (head N!j0N)
        partial = seg N j0N (j0N + r)              (r = last-block remainder)
  (LEN) Lng(Br M') - 1 = J1 + (n - 2)              [== Lng(take J1 ..) + (n-1) - 1]
  (HEADS) heads of Br M' = (heads of Br N' for J<J1) ++ [N!j0N]*(n-1)
  (JUNC) entry N 0 j0N < entry N 0 j1N == entry (Br N' ! J1) 0 0
Also confirm: the branch region S = seg M' (TrMax M'+1)(Lng M'-1) and Br M' = P S,
  and the block-boundary cuts in S are left-minimal (row0 min == N_{0,j0N}).
"""
import itertools, red_model as R

def gen(maxlen, maxval):
    for L in range(2, maxlen+1):
        for c in itertools.product(range(maxval+1), repeat=2*L):
            M=[(c[2*j],c[2*j+1]) for j in range(L)]
            if M[0]==(0,0): yield M

def audit(maxlen=5, maxval=4):
    nA=0
    fn_fail=[]; brn_fail=[]; dec_fail=[]; len_fail=[]; junc_fail=[]; ps_fail=[]
    for N in gen(maxlen, maxval):
        try:
            if not R.is_standard(N): continue
        except Exception: continue
        Ln=R.Lng(N)
        if Ln<2 or R.entry(N,1,Ln-1)!=0: continue
        if R.idx1(N,Ln-1)!=0: continue
        j0N=R.parent(N,0,Ln-1)
        if j0N is None: continue
        j1N=Ln-1
        w=j1N-j0N
        for n in (1,2,3):
            Mn=R.oper(N,n); Lm=R.Lng(Mn)
            for j0p in range(0, j0N):
                for j1p in range(max(j0p+1, Ln-1), Lm):
                    if not R.leR(Mn,0,j0p,j1p): continue
                    Mp=R.seg(Mn,j0p,j1p)
                    Np=R.seg(N,j0p,j1N)        # N' = seg N j0' (Lng N - 1)
                    tN=R.TrMax(Np)
                    if not (j0N-j0p <= tN): continue   # sub-case A
                    nA+=1
                    # WLOG period-reduce: j1' lies in block q (0-based), replace n by q+1.
                    qblk = (j1p - j0N)//w     # block index of j1'
                    neff = qblk+1             # effective number of blocks (article WLOG q=n-1)
                    BrNp=R.Br(Np); BrMp=R.Br(Mp)
                    J1=len(BrNp)-1
                    # FirstNodes(N')_{J1}
                    FN=R.FirstNodes(Np)
                    if not (J1>=0 and FN[J1]==j1N-j0p):
                        fn_fail.append((R.fmt(N),n,j0p,j1p,FN[J1] if J1>=0 else None, j1N-j0p))
                    # Br(N')_{J1} == seg N' (j1N-j0') (j1N-j0') == singleton (N_{j1N})
                    if J1>=0:
                        comp=BrNp[J1]
                        expect=R.seg(Np, j1N-j0p, j1N-j0p)
                        if comp!=expect:
                            brn_fail.append((R.fmt(N),n,j0p,j1p,comp,expect))
                    # last-block remainder r: j1' lies in block q; r = j1' - (j0N's block start)
                    # in M-coords, block boundaries at j0N + k*w. find offset within block.
                    rel=j1p-j0N
                    r = rel % w if w>0 else 0
                    blk=R.seg(N,j0N,j1N-1)
                    partial=R.seg(N,j0N,j0N+r)
                    # decomposition: take J1 (Br N') @ replicate (neff-2) blk @ [partial]
                    nblk = neff-2
                    dec = BrNp[:J1] + ([blk]*nblk if nblk>0 else []) + [partial]
                    if BrMp!=dec:
                        dec_fail.append((R.fmt(N),n,j0p,j1p,neff,r,[R.fmt(b) for b in BrMp],[R.fmt(b) for b in dec]))
                    if len(BrMp)-1 != J1+(neff-2):
                        len_fail.append((R.fmt(N),n,j0p,j1p,neff,len(BrMp)-1,J1+(neff-2)))
                    # junction
                    if J1>=0:
                        if not (R.entry(N,0,j0N) < R.entry(BrNp[J1],0,0)):
                            junc_fail.append((R.fmt(N),n,j0p,j1p))
                    # Br Mp == P S
                    tM=R.TrMax(Mp)
                    S=R.seg(Mp, tM+1, R.Lng(Mp)-1)
                    if BrMp != R.P(S):
                        ps_fail.append((R.fmt(N),n,j0p,j1p))
    print(f"sub-case A instances = {nA}")
    print(f"(FN)  FirstNodes(N')_J1 == j1N-j0'  FAILS = {len(fn_fail)}"); [print("  FN",x) for x in fn_fail[:6]]
    print(f"(BRN) Br(N')_J1 == (N_j1N)          FAILS = {len(brn_fail)}"); [print("  BRN",x) for x in brn_fail[:6]]
    print(f"(DEC) Br M' == take J1(Br N')@blocks FAILS = {len(dec_fail)}"); [print("  DEC",x) for x in dec_fail[:6]]
    print(f"(LEN) Lng(Br M')-1 == J1+(n-2)      FAILS = {len(len_fail)}"); [print("  LEN",x) for x in len_fail[:6]]
    print(f"(JUNC) N_{{0,j0N}} < (Br N'_J1)_00   FAILS = {len(junc_fail)}"); [print("  JUNC",x) for x in junc_fail[:6]]
    print(f"(PS)  Br M' == P S                  FAILS = {len(ps_fail)}"); [print("  PS",x) for x in ps_fail[:6]]

if __name__=="__main__":
    audit()
