#!/usr/bin/env python3
"""r42: deep structural probe of the known non-admeq condIV CEX host, showing the
actual Trans/operB values and the exchange triple, to read off the real shape."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, monoT, zeroT, hasParent, parent, seg, fmt,
                       reduced, oper, Pred as rPred)
from trans_model import Adm, adm, Pred, bpHeadT, bpHeadV, PB
from _r15_vx_lib import (Trans, Mark, operB, numBT, lessBT, leBT, condIV)

def pr(*a): print(*a, flush=True)

def flatstr(t):
    from trans_model import flatBT
    out = []
    for x in flatBT(t):
        if x == ('Z',): out.append('0')
        elif x == (')',): out.append(')')
        elif isinstance(x, tuple) and x[0] == 'D':
            out.append(f'D{x[1]}(')
        else: out.append(str(x))
    return ''.join(out)

def BTstr(t, d=0):
    # readable nested
    ps = t[1]
    if not ps: return '0'
    parts = []
    for (_, v, b) in ps:
        vs = 'inf' if v == float('inf') else str(v)
        parts.append(f'D_{vs}[{BTstr(b)}]')
    return '+'.join(parts)

M = [(0,0),(1,1),(2,2),(3,3),(3,2),(4,1),(5,2),(6,3),(6,1)]
pr('M =', fmt(M), ' Lng', Lng(M), ' reduced', reduced(M), ' mono', monoT(M),
   ' condIV', condIV(M))
L = Lng(M); j1 = L-1
jm2 = parent(M,1,j1); j0 = parent(M,0,j1)
jm3 = Adm(M,jm2); jm1 = Adm(M,j0)
pr(f'j1={j1} jm2(row1par)={jm2} j0(row0par)={j0} jm3=Adm(jm2)={jm3} jm1=Adm(j0)={jm1}')
pr(f'v1=e1[j1]={entry(M,1,j1)}  e1[jm2]={entry(M,1,jm2)} e1[jm3]={entry(M,1,jm3)} '
   f'e1[jm1]={entry(M,1,jm1)} e1[j0]={entry(M,1,j0)}')
pr(f'adm at 0..j1:', [adm(M,i) for i in range(L)])
TM = Trans(M)
pr('Trans M       =', BTstr(TM))
pr('  flat        =', flatstr(TM))
c1 = Mark(Pred(M), jm1)
pr('transC1=Mark(Pred M,jm1) =', BTstr(c1), '  head_v=', bpHeadV(c1))
t2 = bpHeadT(c1)
pr('transT2=bpHeadT c1 =', BTstr(t2))
# transC2 via _c2
from trans_model import _c2
c2 = _c2(M, j1, j0, bpHeadV(c1), t2)
pr('transC2 =', BTstr(c2), '  head_v(transV)=', bpHeadV(c2))
pr('bpHeadT transC2 =', BTstr(bpHeadT(c2)))
# slices
Nslice = seg(M, jm3, j1); Npslice = seg(M, jm2, j1)
pr('s84x_N (jm3-slice) =', fmt(Nslice), ' Trans=', BTstr(Trans(Nslice)))
pr('s84x_Np(jm2-slice) =', fmt(Npslice), ' Trans=', BTstr(Trans(Npslice)))
pr('transJm1-slice(seg jm1..) =', fmt(seg(M,jm1,j1)), ' Trans=', BTstr(Trans(seg(M,jm1,j1))))
pr('  (transC2 should equal Trans(transJm1-slice):', Trans(seg(M,jm1,j1)) == c2, ')')
pr('Mark M jm1 =', BTstr(Mark(M,jm1)), ' == transC2?', Mark(M,jm1)==c2)
pr()
for n in (1,2,3):
    Mn = oper(M,n); Mn1 = oper(M,n+1)
    TMn = Trans(Mn); TMn1 = Trans(Mn1)
    opN = operB(TM, numBT(n)); opNm1 = operB(TM, numBT(n-1))
    pr(f'--- n={n} ---')
    pr(f'  M[{n}]         =', fmt(Mn))
    pr(f'  Trans(M[{n}])  =', BTstr(TMn))
    pr(f'  operB(TM,{n})  =', BTstr(opN))
    pr(f'  CONJ1 Trans(M[n]) < operB(TM,n) :', lessBT(TMn, opN))
    pr(f'  CONJ2 Trans(M[n]) < Trans M     :', lessBT(TMn, TM))
    pr(f'  CONJ3 operB(TM,n-1) < Trans(M[n+1]):', lessBT(opNm1, TMn1))
