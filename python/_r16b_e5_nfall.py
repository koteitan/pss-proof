#!/usr/bin/env python3
"""r16b-E5: validate the EXACT tower-form equalities of the NFall residual
(the named hypothesis of m_8_7_fseq_descend_dispatcher_condV) over genuine
deep non-adm condV hosts.  For the shared surgery pair (s1,b1) obtained by
scb-decomposing Trans(M[1]) at flatBT(D_u t2):
  [M]  flatBT(Trans(M[Suc k])) == s1 @ flatBP(D_u (bodyM t2 e k)) @ b1
  [O]  flatBT(operB(TM)(numBT m)) == s1 @ flatBP(D_u (bodyO t2 e m)) @ b1  (m>=1)
where u=M1[jm1], e=M1[j0], bodyM/bodyO as in the Isabelle e5x_* defs.
"""
import sys, time, random
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from _r15_vx_lib import (Trans, operB, numBT, guarded, SKIP, internals,
                         ZB, Dpt, flatBT)
import trans_model as tm
from trans_model import addBT, adm, Adm, condV, Pred
from red_model import Lng, entry, parent, oper, diagSeq, monoT

# --- s85b_W (Isabelle s85b_W u t c k), heads are ints ---
def s85b_W(u,t,c,k):
    if k==0: return Dpt(u,c)
    return Dpt(u, addBT(t, s85b_W(u,t,c,k-1)))

def bodyM(t,e,k):
    if k==0: return t
    return addBT(t, s85b_W(e,t,t,k))
def bodyO(t,e,n):
    return addBT(t, s85b_W(e,t,Dpt(e,ZB),n-1))

def flatBP(v,inner):  # DB v inner
    return [('D',v)] + flatBT(inner)

def scb_at(T, coreflat):
    """find (s,b) with flatBT T = s @ coreflat @ b, all b == ')'."""
    f=flatBT(T); n=len(f); m=len(coreflat)
    for i in range(n-m+1):
        if f[i:i+m]==coreflat:
            b=f[i+m:]
            if all(x==')' for x in b): return f[:i], b
    return None

def mine(tmax,rng,want=25):
    t0=time.time(); seen=set(); out=[]
    while time.time()-t0<tmax and len(out)<want:
        u=rng.randrange(0,6); vv=u+rng.randrange(1,7); M=diagSeq(u,vv)
        for _ in range(rng.randrange(6,34)):
            if time.time()-t0>tmax: break
            nn=rng.choice((1,1,1,2,2,2,2,3,4))
            M2=guarded(oper,M,nn,budget=2)
            if M2 is SKIP or M2 is None or M2==M or Lng(M2)>24: break
            M=M2; key=tuple(M)
            if key in seen: continue
            seen.add(key)
            j1=Lng(M)-1
            if j1<=1 or not monoT(M) or not condV(M): continue
            if not adm(M,parent(M,0,j1)) and Lng(M)>=9: out.append(list(M))
    return [list(t) for t in dict.fromkeys(tuple(m) for m in out)]

def main():
    tmine=float(sys.argv[1]) if len(sys.argv)>1 else 90
    seed=int(sys.argv[2]) if len(sys.argv)>2 else 4242
    rng=random.Random(seed)
    hosts=mine(tmine,rng)
    print('non-adm condV deep hosts:',len(hosts),flush=True)
    okM=totM=okO=totO=0; bad=0; hostsdone=0
    for M in hosts:
        j1=Lng(M)-1; j0=parent(M,0,j1); jm1=Adm(M,j0)
        u=entry(M,1,jm1); e=entry(M,1,j0)
        ii=internals(M)
        if ii is None: continue
        t2=ii['t2']
        TM1=guarded(Trans,Pred(M),budget=25)   # Trans(M[1])=Trans(Pred M)
        if TM1 in (SKIP,None): continue
        core1=flatBP(u,t2)     # flatBT(D_u t2)
        sb=scb_at(TM1, core1)
        if sb is None:
            bad+=1; print('  NO (s1,b1) for host',M,flush=True); continue
        s1,b1=sb
        hostsdone+=1
        for k in range(0,5):
            Mk=guarded(oper,M,k+1,budget=2)   # M[Suc k]
            if Mk in (SKIP,None): break
            TMk=guarded(Trans,Mk,budget=25)
            if TMk in (SKIP,None): break
            lhs=flatBT(TMk); rhs=s1+flatBP(u,bodyM(t2,e,k))+b1
            totM+=1; okM+= (lhs==rhs)
            if lhs!=rhs and bad<5:
                print('  [M] MISMATCH host',M,'k=',k,flush=True); bad+=1
        for m in range(1,6):
            FS=guarded(operB,TM_,numBT(m),budget=15) if False else guarded(operB,Trans(M),numBT(m),budget=15)
            if FS in (SKIP,None): break
            lhs=flatBT(FS); rhs=s1+flatBP(u,bodyO(t2,e,m))+b1
            totO+=1; okO+= (lhs==rhs)
            if lhs!=rhs and bad<8:
                print('  [O] MISMATCH host',M,'m=',m,flush=True); bad+=1
    print('hosts with (s1,b1):',hostsdone,flush=True)
    print('  [M] Trans(M[Suc k]) form : %d/%d'%(okM,totM),flush=True)
    print('  [O] operB value form     : %d/%d'%(okO,totO),flush=True)

if __name__=='__main__':
    main()
