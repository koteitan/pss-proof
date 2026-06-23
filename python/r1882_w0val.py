import sys
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng, entry, monoT, TrMax, Br, parent, diagSeq)
from trans_model import (Trans, Mark, Pred, reduced, Adm, ZB, Dpt, bpHeadV, bpHeadT, _c2,
                         condI, condIII, condV, condVI, flatBT, scb_decomps)
for v in [1,2,3,4]:
    u=0; w0=v+1; w1=0
    M=diagSeq(u,v)+[(w0,w1)]
    j1=Lng(M)-1
    jp=parent(M,0,j1)
    c1=Mark(Pred(M),Adm(M,jp))
    vv=bpHeadV(c1); t2=bpHeadT(c1)
    print(f"u={u} v={v}: M={M}")
    print(f"  j1={j1} jp={jp} e1j1={entry(M,1,j1)} e1jp={entry(M,1,jp)} c1={c1} v={vv} t2={t2}")
    print(f"  condI={condI(M)} condIII={condIII(M)} condV={condV(M)} condVI={condVI(M)} t2==0:{t2==ZB}")
    print(f"  c2={_c2(M,j1,jp,vv,t2)}")
    print(f"  Adm(M,jp)={Adm(M,jp)}  Trans(Pred)={Trans(Pred(M))}  Trans(M)={Trans(M)}")
    ds=scb_decomps(Trans(Pred(M)),flatBT(c1))
    print(f"  scb: {ds[0] if ds else None}")
