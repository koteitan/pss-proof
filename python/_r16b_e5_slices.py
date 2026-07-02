#!/usr/bin/env python3
"""r16b-E5: dump the s84x tower building-block Trans values for non-adm host(s)
to determine head (u vs e) of each piece. Confirms:
  Np    = seg M j0 j1        : Trans = D_e(t2 + D_{v1}0)  [head e]
  PredNp= seg M j0 (j1-1)    : Trans = D_e(t2)            [head e]
  Lp    = seg M j0 (j1-1)@col: Trans = D_e(t2 + D_e 0)    [head e]
  L 1   = M[1]@col           : Trans core (s1,b1) = D_u(t2 + D_e 0) [head u outer]
  Trans(M[1]) core           : D_u(t2)                    [head u outer]
"""
import sys
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from _r15_vx_lib import (Trans, operB, numBT, lessBT, leBT, internals, ZB, Dpt, PB, flatBT, guarded, SKIP)
from red_model import Lng, entry, parent, oper, reduced, monoT, seg, diagSeq
from trans_model import adm, Adm, condV, Pred

def fstr(t):
    out=[]
    for s in flatBT(t):
        if s=='Z': out.append('Z')
        elif isinstance(s,tuple) and s[0]=='D': out.append('D%s'%(s[1],))
        else: out.append(str(s))
    return ''.join(out)

def s84x_Np(M):
    j1=Lng(M)-1; j0=parent(M,1,j1); return seg(M,j0,j1)
def s84x_Lp(M):
    j1=Lng(M)-1; j0=parent(M,1,j1)
    return seg(M,j0,j1-1)+[(entry(M,0,j1), entry(M,1,j0))]
def s84x_L(M,n):
    j1=Lng(M)-1; j0=parent(M,1,j1)
    Mn=oper(M,n)
    return Mn+[(entry(M,0,j0)+n*(entry(M,0,j1)-entry(M,0,j0)), entry(M,1,j0))]

def dump(M):
    print('='*60)
    print('M=',M)
    j1=Lng(M)-1; j0=parent(M,0,j1); jm1=Adm(M,j0); jm2=parent(M,1,j1)
    print('j0(row0)=%d jm2(row1par)=%d jm1=%d j1=%d'%(j0,jm2,jm1,j1))
    print('M1: j0=%d jm1=%d j1=%d'%(entry(M,1,j0),entry(M,1,jm1),entry(M,1,j1)))
    ii=internals(M)
    print('t2=',fstr(ii['t2']),'  c2=',fstr(ii['c2']),'  v(=head c1/c2)=',ii['v'])
    Np=s84x_Np(M); PNp=Np[:-1]; Lp=s84x_Lp(M); L1=s84x_L(M,1); L2=s84x_L(M,2)
    for nm,S in [('Np(seg j0..j1)',Np),('PredNp(seg j0..j1-1)',PNp),
                 ('Lp',Lp),('L 1',L1),('L 2',L2)]:
        T=guarded(Trans,S,budget=25)
        print('  Trans(%-22s)= %s'%(nm, fstr(T) if T not in (SKIP,None) else 'SKIP'))
    print('  Trans(Pred M=M[1]) = %s'%fstr(Trans(Pred(M))))
    print('  Trans M            = %s'%fstr(Trans(M)))

# host 1 (from notes)
dump([(0,0),(1,1),(2,2),(3,1),(4,0),(5,1),(6,2),(7,0),(6,2)])
