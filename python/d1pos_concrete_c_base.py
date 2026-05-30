#!/usr/bin/env python3
"""Verify the CONCRETE c and base formulas for oper_d1pos_collapse (conc-B).
For the branch region S = seg M (j0'+TrMax M'+1) j1' (so Br M' = P S):
  c    = Lng S - Lng(last(P S))               (last component left-endpoint)
  base = seg N (j0red + TrMax Np + 1) (j1red)  ... but P base = butlast(Br Np);
         we test base = seg S0low source -> check seg S 0 (c-1)=(IncrFirst^^shamt) base
         where base = the N-side branch slice that equals seg N (a0)(a1) for some a0,a1.
We test: c0,cle,lmin,tailnm, butl(=butlast(Br Np)=P base), lowshift.
We focus regime B (uncapped: jm2<=j0' and j0red+(j1'-j0')<LN-1) AND report all regimes.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import (Lng, entry, P, TrMax, seg, oper, idx1, hasParent, parent,
                       monoT, multiT, Br, IncrFirst, is_standard, fmt, le0, funpow)
from d1pos_j0j1red_search import gen_std, is_d1pos_mono, brle

def main():
    maxlen, maxval, KMAX = (int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])) \
        if len(sys.argv) > 3 else (12, 4, 8)
    Ns = [N for N in gen_std(maxlen, maxval, KMAX) if is_d1pos_mono(N)]
    tot=0; regB=0
    cok=cleok=lminok=tailok=butlok=lowok=collok=0
    fails={'lmin':[],'tail':[],'butl':[],'low':[],'coll':[]}
    for N in Ns:
        LN = Lng(N); jm2 = parent(N, 1, LN-1); w = LN-1-jm2
        if w<=0: continue
        delta=entry(N,0,LN-1)-entry(N,0,jm2)
        for n in (1,2,3):
            M = oper(N, n)
            if Lng(M) < 2: continue
            for j0p in range(Lng(M)):
                for j1p in range(j0p+1, Lng(M)):
                    if j1p < LN-1: continue
                    if not le0(M, j0p, j1p): continue
                    Mp = seg(M, j0p, j1p)
                    if not monoT(Mp): continue
                    if brle(Mp): continue
                    # formula G
                    q0=(j0p-jm2)//w if j0p>=jm2 else 0
                    j0red=jm2+(j0p-jm2)%w if j0p>=jm2 else j0p
                    j1red_uncap=j0red+(j1p-j0p)
                    j1red=min(j1red_uncap,LN-1)
                    shamt=q0*delta
                    if not (j0red<j1red<=LN-1): continue
                    Np=seg(N,j0red,j1red)
                    if not le0(N,j0red,j1red): continue
                    tot+=1
                    is_regB = (jm2<=j0p) and (j1red_uncap<LN-1)
                    if is_regB: regB+=1
                    # branch region S
                    T=TrMax(Mp)
                    A=j0p+T+1; E=j1p
                    if A>E: continue
                    S=seg(M,A,E)
                    PS=P(S)
                    BrMp=Br(Mp)
                    if BrMp!=PS:  # sanity: Br M' = P S
                        continue
                    LS=Lng(S)
                    c=LS-Lng(PS[-1])
                    # c0
                    if 0<c: cok+=1
                    # cle
                    if c<=LS-1: cleok+=1
                    # lmin
                    lm=all(entry(S,0,c)<=entry(S,0,j) for j in range(c))
                    if lm: lminok+=1
                    elif len(fails['lmin'])<5: fails['lmin'].append((fmt(N),n,j0p,j1p,'c',c))
                    # tailnm
                    tn=not multiT(seg(S,c,LS-1))
                    if tn: tailok+=1
                    elif len(fails['tail'])<5: fails['tail'].append((fmt(N),n,j0p,j1p,'c',c))
                    # butl: butlast(Br Np) = P base where base = seg N (j0red+TrMax Np+1) j1red ... no.
                    # Actually base is the N-side branch region: Br Np = P (seg N (j0red+TrMax Np+1) j1red)
                    TN=TrMax(Np); AN=j0red+TN+1; EN=j1red
                    baseN=seg(N,AN,EN)  # so Br Np = P baseN
                    # cbase = the analog cut on baseN, base = seg baseN 0 (cN-1)
                    PbaseN=P(baseN)
                    cN=Lng(baseN)-Lng(PbaseN[-1])
                    base=seg(baseN,0,cN-1)
                    # butl: butlast(Br Np)=P base
                    bl=(P(base)==Br(Np)[:-1])
                    if bl: butlok+=1
                    elif len(fails['butl'])<5: fails['butl'].append((fmt(N),n,j0p,j1p,'cN',cN,'Pbase',len(P(base)),'BrNp-1',len(Br(Np))-1))
                    # lowshift: seg S 0 (c-1) = (IncrFirst^^shamt) base
                    low=seg(S,0,c-1)
                    sh=funpow(IncrFirst,shamt,base)
                    ls=(low==sh)
                    if ls: lowok+=1
                    elif len(fails['low'])<5: fails['low'].append((fmt(N),n,j0p,j1p,'shamt',shamt,'low',fmt(low),'sh',fmt(sh)))
                    # full collapse
                    target=[funpow(IncrFirst,shamt,x) for x in Br(Np)[:-1]]+[seg(S,c,LS-1)]
                    co=(PS==target)
                    if co: collok+=1
                    elif len(fails['coll'])<5: fails['coll'].append((fmt(N),n,j0p,j1p))
    print(f"#cases={tot} regB={regB} KMAX={KMAX}")
    print(f"  c0      : {cok}/{tot}")
    print(f"  cle     : {cleok}/{tot}")
    print(f"  lmin    : {lminok}/{tot}")
    for f in fails['lmin']: print("    LMIN-FAIL",f)
    print(f"  tailnm  : {tailok}/{tot}")
    for f in fails['tail']: print("    TAIL-FAIL",f)
    print(f"  butl    : {butlok}/{tot}")
    for f in fails['butl']: print("    BUTL-FAIL",f)
    print(f"  lowshift: {lowok}/{tot}")
    for f in fails['low']: print("    LOW-FAIL",f)
    print(f"  collapse: {collok}/{tot}")
    for f in fails['coll']: print("    COLL-FAIL",f)

if __name__=='__main__': main()
