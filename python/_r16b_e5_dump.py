#!/usr/bin/env python3
"""r16b-E5: dump scb-string structure of Trans(M[n]) and operB(Trans M)(numBT k)
for the known non-adm condV host, to read off the head pattern (u vs e)."""
import sys
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from _r15_vx_lib import (Trans, operB, numBT, lessBT, leBT, internals, ZB, Dpt, PB, flatBT)
from red_model import Lng, entry, parent, oper, reduced, monoT
from trans_model import adm, Adm, condV, Pred

def sym(x):
    if x==ZB: return 'Z'
    if isinstance(x,tuple) and x[0]=='D': return 'D%s'%(x[1],)
    return str(x)

def fstr(t):
    out=[]
    for s in flatBT(t):
        if s=='Z': out.append('Z')
        elif isinstance(s,tuple) and s[0]=='D': out.append('D%s'%(s[1],))
        elif s=='(' : out.append('(')
        elif s==')' : out.append(')')
        elif s==',' : out.append(',')
        else: out.append(str(s))
    return ''.join(out)

# non-adm host from the notes
M=[(0,0),(1,1),(2,2),(3,1),(4,0),(5,1),(6,2),(7,0),(6,2)]
print('M=',M,'reduced=',reduced(M),'mono=',monoT(M),'condV=',condV(M))
j1=Lng(M)-1; j0=parent(M,0,j1); jm1=Adm(M,j0)
print('j0=%d jm1=%d j1=%d adm(M,j0)=%s'%(j0,jm1,j1,adm(M,j0)))
print('M1,j0=%d M1,jm1=%d M1,j1=%d'%(entry(M,1,j0),entry(M,1,jm1),entry(M,1,j1)))
ii=internals(M)
print('t2=',ii['t2'],' t2 flat=',fstr(ii['t2']))
print('c1(=Mark Pred jm1)=',ii['c1'],' head v=',ii['v'])
print('c2=',ii['c2'])
TM=Trans(M)
print('Trans M      =',fstr(TM))
for n in range(1,5):
    Mn=oper(M,n)
    print('Trans(M[%d])  ='%n, fstr(Trans(Mn)))
for k in range(0,6):
    print('operB(TM,%d)  ='%k, fstr(operB(TM,numBT(k))))
print('--- exchange checks ---')
for n in range(1,5):
    Mn=oper(M,n); TMn=Trans(Mn)
    row=[]
    for k in range(0,n+3):
        FS=operB(TM,numBT(k))
        row.append('k=%d:%s%s'%(k,'<=' if leBT(TMn,FS) else '..','<' if lessBT(TMn,FS) else ''))
    print('n=%d desc<TM=%s '%(n,lessBT(TMn,TM)), ' '.join(row))
