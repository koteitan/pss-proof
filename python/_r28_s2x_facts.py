#!/usr/bin/env python3
# r28-SHARP2 re-cut validation.
# Architecture: SHARP = RA(Red(seg M jm1 (L-2)))!1 = entry M 1 (j0+1), proven by
# strong induction on c (slice right end) with ST-atoms:
#   FACT-A : adm M (j0+1)                                   [la = j0+1]
#   FACT-B': forall c in (j0, L-1]: hasParent M 0 c and parent M 0 c in [jm1,j0]
#              ==> parent M 0 c = j0  and  entry M 1 c = entry M 1 j0 + 1
#   RAMP   : entry M 1 k = entry M 1 jm1 + (k-jm1) for k in [jm1, j0+1]  (RT-level)
# plus recursion-trace assertions (step guard, base dispatch condV/VI, prefix-eq).
# Tested on (1) deep ST corpus (pickled), (2) brute-force RT corpus (incl NON-standard).
import sys, time, pickle
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-f7/python')
from red_model import (Lng, entry, monoT, zeroT, seg, adm, diagSeq, parent, Adm,
                       Pred, fmt, Red, hasParent, le0)
from trans_model import reduced, condV, condVI, Trans, Mark, bpHeadT, ZB

SCR='/tmp/claude-1000/-home-koteitan-proofs-pss-proof/8b6b910e-60c9-4662-aff1-4806ad270a61/scratchpad'

def RN(t):
    xs=t[1]
    return [] if not xs else [xs[-1][1]]+RN(xs[-1][2])

def genuine(M):
    if not (reduced(M) and monoT(M)): return None
    if Lng(M)<3: return None
    j1=Lng(M)-1
    if not hasParent(M,0,j1): return None
    jp=parent(M,0,j1)
    if not condV(M): return None
    if adm(M,jp): return None
    if Trans(Pred(M))==ZB: return None
    jm1=Adm(M,jp)
    c1=Mark(Pred(M),jm1)
    if bpHeadT(c1)==ZB: return None
    return (jm1,jp,j1)

def RAlist(N,depth=0):
    # mirrors RightAnces on reduced input
    if depth>100: raise RuntimeError("deep")
    j1=Lng(N)-1
    if j1==0:
        return [] if N[0]==(0,0) else [entry(N,1,0)]
    assert monoT(N)
    if zeroT(Pred(N)): return [0,entry(N,1,j1)]
    jp=parent(N,0,j1); jm1=Adm(N,jp)
    sg=seg(N,0,jm1)
    if zeroT(sg): a=[0]
    else: a=RAlist(sg,depth+1)
    e1j1=entry(N,1,j1); e1jp=entry(N,1,jp)
    cI = e1j1==0 and adm(N,jp)
    cIII = e1j1>0 and e1jp>=e1j1 and adm(N,jp)
    cV = condV(N); cVI = condVI(N)
    if cI or cIII or cV or cVI: tail=[e1j1]
    else: tail=[e1jp,e1j1]
    return a+tail

def check_host(M,g,errs,trace_stats):
    jm1,j0,j1=g; L=Lng(M); la=j0+1
    ok=True
    # FACT-A
    if not adm(M,la):
        errs.append(('A',fmt(M))); ok=False
    # RAMP
    for k in range(jm1,j0+2):
        if entry(M,1,k)!=entry(M,1,jm1)+(k-jm1):
            errs.append(('RAMP',fmt(M),k)); ok=False; break
    # FACT-B'
    for c in range(j0+1,L):
        if not hasParent(M,0,c): continue
        pj=parent(M,0,c)
        if jm1<=pj<=j0:
            if not (pj==j0 and entry(M,1,c)==entry(M,1,j0)+1):
                errs.append(('B',fmt(M),c,pj,entry(M,1,c),entry(M,1,j0))); ok=False
    # recursion trace
    a=jm1
    c=L-2
    guard=0
    while True:
        guard+=1
        if guard>Lng(M)+3: errs.append(('LOOP',fmt(M))); ok=False; break
        S=seg(M,a,c); Q=Red(S)
        if not (reduced(Q) and monoT(Q)):
            errs.append(('QBAD',fmt(M),c)); ok=False; break
        # value transfer sanity: row1 of Q == row1 of S
        if [entry(Q,1,k) for k in range(Lng(Q))]!=[entry(S,1,k) for k in range(Lng(S))]:
            errs.append(('ROW1',fmt(M),c)); ok=False; break
        ra=RAlist(Q)
        if len(ra)<2 or ra[1]!=entry(M,1,la):
            errs.append(('RA1',fmt(M),c,ra,entry(M,1,la))); ok=False; break
        j1Q=Lng(Q)-1
        jpQ=parent(Q,0,j1Q)
        if jpQ is None: errs.append(('NOPAR',fmt(M),c)); ok=False; break
        pjM=a+jpQ
        # parent agreement with M
        if hasParent(M,0,c):
            if parent(M,0,c)!=pjM and parent(M,0,c)>=a:
                errs.append(('PARDIS',fmt(M),c,parent(M,0,c),pjM)); ok=False
        jm1Q=Adm(Q,jpQ)
        if jm1Q==0:
            # base: expect pjM == j0 and condV/VI of Q
            trace_stats['base']=trace_stats.get('base',0)+1
            if pjM!=j0:
                errs.append(('BASEPJ',fmt(M),c,pjM,j0)); ok=False
            if not (condV(Q) or condVI(Q)):
                errs.append(('BASECOND',fmt(M),c)); ok=False
            if entry(M,1,c)!=entry(M,1,la):
                errs.append(('BASEVAL',fmt(M),c)); ok=False
            break
        else:
            trace_stats['step']=trace_stats.get('step',0)+1
            cp=a+jm1Q
            if not (la<=cp<c):
                errs.append(('STEPGUARD',fmt(M),c,cp)); ok=False; break
            # prefix-eq: seg Q 0 jm1Q == Red(seg M a cp)
            if seg(Q,0,jm1Q)!=Red(seg(M,a,cp)):
                errs.append(('PREFIXEQ',fmt(M),c,cp)); ok=False; break
            if not le0(M,a,cp):
                errs.append(('LE0',fmt(M),c,cp)); ok=False; break
            # Adm agreement: Adm M (parent M 0 c) == cp ?
            if hasParent(M,0,c) and Adm(M,parent(M,0,c))!=cp:
                errs.append(('ADMAGREE',fmt(M),c,cp,Adm(M,parent(M,0,c)))); ok=False
            c=cp
    return ok

def gen_brute(maxlen,maxval,starts=((0,0),(1,1))):
    out=[]
    cols=[(x,y) for x in range(maxval+1) for y in range(maxval+1)]
    def dfs(prefix,L):
        if len(prefix)==L:
            out.append(list(prefix)); return
        for cc in cols:
            prefix.append(cc); dfs(prefix,L); prefix.pop()
    for L in range(3,maxlen+1):
        for s in starts:
            def dfs2(prefix):
                if len(prefix)==L: out.append(list(prefix)); return
                for cc in cols:
                    prefix.append(cc); dfs2(prefix); prefix.pop()
            dfs2([s])
    return out

def main():
    t0=time.time()
    with open(SCR+'/r28pool.pkl','rb') as f: ann=pickle.load(f)
    print("ST pool",len(ann),flush=True)
    errs=[]; ts={}; tot=0
    for (M,mo,red) in ann:
        if not mo or not red: continue
        g=genuine(M)
        if g is None: continue
        tot+=1
        check_host(M,g,errs,ts)
    print(f"ST genuine hosts={tot} trace_stats={ts} errs={len(errs)}",flush=True)
    for e in errs[:15]: print("  ST ERR",e)
    # brute RT corpus (incl non-standard) : test A and B' only
    print("=== brute RT (maxlen5 maxval4) ===",flush=True)
    bt=0; failA=[]; failB=[]
    for M in gen_brute(5,4):
        if not monoT(M): continue
        if not reduced(M): continue
        g=genuine(M)
        if g is None: continue
        bt+=1
        jm1,j0,j1=g; L=Lng(M); la=j0+1
        if not adm(M,la): failA.append(fmt(M))
        for c in range(j0+1,L):
            if not hasParent(M,0,c): continue
            pj=parent(M,0,c)
            if jm1<=pj<=j0:
                if not (pj==j0 and entry(M,1,c)==entry(M,1,j0)+1):
                    failB.append((fmt(M),c,pj))
    print(f"brute genuine={bt} FACT-A fails={len(failA)} (expected>0 on RT\\ST) FACT-B' fails={len(failB)}")
    for f in failA[:6]: print("  A-fail",f)
    for f in failB[:10]: print("  B-fail",f)
    print("time",round(time.time()-t0,1))

if __name__=='__main__':
    main()
