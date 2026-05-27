"""Methodology-corrected re-audit (is_standard + depth 5) of the §6.8 case-A
boundary stop and its M'-coordinate discharge inequality.

Domain = the EXACT faithful case-A hypotheses in scope at the 9402 sorry:
  - N standard (yaBMS is_standard),
  - 1 < Lng N,
  - d0zero: entry N 1 (Lng N - 1) = 0,
  - i1 = idx1 N (Lng N - 1) = 0 (automatic from d0zero),
  - notzero + hasParent (oper is generic) -- automatic since we require j1' >= Lng N-1,
  - n in {1,2,3}, 1 <= n,
  - j0N := parent N 0 (Lng N - 1),  j0' < j0N  (case lt0, article 1466),
  - bge: Lng N - 2 <= j1',
  - leR (N[n]) 0 j0' j1'.

Checks, with M' = seg (N[n]) j0' j1', N' = seg N j0' (Lng N-1), t = TrMax N':
  (1) boundary stop:  NOT nextrel1 M' t (t+1)      -- the goal
  (2) HARD-case discharge inequality (M'-coords):
        entry M' 1 t >= entry M' 1 (t+1)
      where HARD = the stop index t+1 is at/over the prefix-agreement boundary
        c = (Lng N - 2) - j0'   (so t+1 > c, i.e. t = c by confinement).
  (3) EASY case (t+1 <= c): handled by nextR1_boundary_stop_of_prefix; report count.
"""
import itertools, red_model as R

def gen(maxlen, maxval):
    for L in range(2, maxlen+1):
        for c in itertools.product(range(maxval+1), repeat=2*L):
            M=[(c[2*j],c[2*j+1]) for j in range(L)]
            if M[0]==(0,0): yield M

def audit(maxlen=5, maxval=4):
    std=0
    n_easy=0; n_hard=0
    stop_fail=[]; ineq_fail=[]
    ws=set()
    for N in gen(maxlen, maxval):
        try:
            if not R.is_standard(N): continue
        except Exception: continue
        std+=1
        Ln=R.Lng(N)
        if Ln<2 or R.entry(N,1,Ln-1)!=0: continue        # d0zero
        if R.idx1(N,Ln-1)!=0: continue                    # i1=0 (redundant w/ d0zero)
        j0N=R.parent(N,0,Ln-1)
        if j0N is None: continue
        for n in (1,2,3):
            Mn=R.oper(N,n); Lm=R.Lng(Mn)
            for j0p in range(0, j0N):                      # j0' < j0N  (case lt0)
                for j1p in range(max(j0p+1, Ln-2), Lm):    # bge: Lng N-2 <= j1'
                    if not R.leR(Mn,0,j0p,j1p): continue
                    Mp=R.seg(Mn,j0p,j1p)
                    Np=R.seg(N,j0p,Ln-1)
                    t=R.TrMax(Np)
                    # boundary stop (the goal)
                    if R.nextrel1(Mp,t,t+1):   # nextrel1 Mp t (t+1)
                        stop_fail.append((R.fmt(N),n,j0p,j1p,t))
                    # easy/hard split
                    c=(Ln-2)-j0p
                    if t+1<=c:
                        n_easy+=1
                    else:
                        n_hard+=1
                        ws.add(Ln-1-j0N)  # block width w
                        # M'-coordinate discharge inequality (only when t+1 in range;
                        # if t+1 >= Lng M' the stop is automatic since nextrel1 needs t+1<Lng M')
                        if t+1 < R.Lng(Mp):
                            if not (R.entry(Mp,1,t) >= R.entry(Mp,1,t+1)):
                                ineq_fail.append((R.fmt(N),n,j0p,j1p,t,
                                                  R.entry(Mp,1,t),R.entry(Mp,1,t+1)))
    print(f"standard={std}")
    print(f"easy(t+1<=c)={n_easy}  hard(t+1>c)={n_hard}  block-widths(hard)={sorted(ws)}")
    print(f"boundary-stop FAILS = {len(stop_fail)}")
    for m in stop_fail[:10]: print("  STOP-FAIL", m)
    print(f"hard M'-ineq (entry M' 1 t >= entry M' 1 (t+1)) FAILS = {len(ineq_fail)}")
    for m in ineq_fail[:10]: print("  INEQ-FAIL", m)

if __name__=="__main__":
    audit()
