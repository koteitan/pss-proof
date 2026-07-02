import sys, time, signal, random
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,multiT,monoT,zeroT,parent,oper,leR,le0,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut,idx1,diagSeq)
import trans_model as tm
from trans_model import condV

"""ROUND 15 front K2, STEP 0 (empirical-first): the FULL per-column colcase of
m_8_5_anchor_fold_mixed over the genuine keystone regime (same filters as
_r14_k_broad.py: reduced M, block exists, condV(Mq), hasParent(Mq,1,j1),
parR nextrel0(Mq,p1,j1), coin p1==parent(Mq,0,j1), jm1>0, app, non-reset
B[0][0]>0, reduced Mq, multiT Mq).

Per column m (host N_m = Mq @ B[:m], n0 = jm1 = Adm(Mq, parent(Mq,0,j1))):
  stuck(m)   = multiT(N_m) and jm1 < Pcut(N_m)
  disjunct1  = reduced(N_m) & marked(N_m,jm1) & hp0(N_{m+1})
               & marked(N_m, transJm1(N_{m+1})) & jm1 <= transJm1(N_{m+1})
  disjunct2  = reduced(N_m) & multiT & stuck & entry(N_m,0,Pcut N_m) < fst(B!m)
  colfull    = disjunct1 or disjunct2      <- the target lemma's conclusion

Also recorded (proof-mechanism candidates):
  SFX  stuck-suffix:  stuck(m-1) ==> stuck(m)      (monotone stuckness)
  NS1  #non-stuck columns at m>=1 (are they empty? if so no induction needed)
  SHP  shape of non-stuck m>=1 hosts (mono vs multi&jm1>=Pcut)
  EQP  multi non-stuck m>=1: jm1 == Pcut(N_m)?     (clean Pcut_le route)
  PGE  m>=1: parent(N_{m+1},0,newlast) >= L (= Lng Mq)  (block-descent claim)
  DCH  dichotomy: monoT(N_m) (m>=1) <==> le0(N_1, 0, L)
  OKL  ok(m) (m>=1) <==> le0(N_1, jm1, L)          (ok(1) descent claim)
  OK0  marked(Mq, jm1)  (the m=0 basepoint via the Adm row-1 chain)
  HP1  hp0(N_1) at m=0 (needed for R2b(0))
  MK-hyps for the netfold (MAP section): hostP monoT(N_{m+1}) per column
"""

class TimeoutErr(Exception): pass
def handler(s,f): raise TimeoutErr()
signal.signal(signal.SIGALRM, handler)
def safe_reduced(M,b=1):
    signal.alarm(b)
    try: r=reduced(M); signal.alarm(0); return r
    except Exception: signal.alarm(0); return None

def gen_random(rng,maxlen=6,maxv=3,u_vals=(0,1,2,3,4)):
    pairs=[(a,b) for a in range(maxv+1) for b in range(maxv+1)]; npair=len(pairs)
    combos=[(u,L) for u in u_vals for L in range(2,maxlen+1)]
    while True:
        rng.shuffle(combos)
        for (u,L) in combos:
            idx=rng.randrange(npair**(L-1)); s=[]; t=idx
            for _ in range(L-1): s.append(pairs[t%npair]); t//=npair
            yield [(u,u)]+s

def gen_stps(rng,maxu=3,maxv=4,maxsteps=3,maxidx=3):
    while True:
        u=rng.randint(0,maxu); v=rng.randint(u,u+maxv)
        M=diagSeq(u,v)
        for _ in range(rng.randint(0,maxsteps)):
            n=rng.randint(1,maxidx)
            M2=oper(M,n)
            if Lng(M2)>14: break
            M=M2
        yield M

def transJm1(N):
    j1=Lng(N)-1
    if not hasParent(N,0,j1): return None
    return Adm(N,parent(N,0,j1))

def sweep(genf,tl,qs,seed,tag):
    rng=random.Random(seed); t0=time.time()
    from collections import Counter
    C=Counter(); seen=set(); fails=[]
    for M in genf(rng):
        if time.time()-t0>tl: break
        key=tuple(M)
        if key in seen: continue
        seen.add(key)
        if safe_reduced(M,1) is not True: continue
        j1M=Lng(M)-1
        if j1M<=0: continue
        if entry(M,0,j1M)==0 and entry(M,1,j1M)==0: continue
        i1M=idx1(M,j1M)
        if not hasParent(M,i1M,j1M): continue
        for q in qs:
            try:
                Mq=oper(M,q); j1=Lng(Mq)-1
                if j1<=0 or Lng(Mq)>16: continue
                if not condV(Mq): continue
                if not hasParent(Mq,1,j1): continue
                p1=parent(Mq,1,j1)
                if not (nextrel0(Mq,p1,j1) and p1==parent(Mq,0,j1)): continue
                jm1=Adm(Mq,parent(Mq,0,j1))
                if not (jm1>0): continue
                Msq=oper(M,q+1)
                if Msq[:len(Mq)]!=Mq: continue
                B=Msq[len(Mq):]; wB=len(B)
                if wB<1 or B[0][0]==0: continue
                if safe_reduced(Mq,1) is not True or not multiT(Mq): continue
                C['blocks']+=1
                L=Lng(Mq)
                # OK0: the m=0 basepoint (Adm row-1 chain target)
                if marked(Mq,jm1): C['ok0']+=1
                N1=Mq+[B[0]]
                reach0L=le0(N1,0,L); okL=le0(N1,jm1,L)
                if reach0L: C['reach0L']+=1
                if okL: C['okL']+=1
                prev_stuck=False
                host=list(Mq)
                for m in range(wB):
                    Nprev=list(host); col=B[m]; host=host+[col]; Ncur=list(host)
                    C['cols']+=1
                    rN=safe_reduced(Nprev,1) is True
                    if rN: C['colRT']+=1
                    mu=multiT(Nprev); mo=monoT(Nprev)
                    stuck = mu and jm1<Pcut(Nprev)
                    # SFX stuck-suffix
                    if m>0:
                        if prev_stuck and not stuck:
                            C['sfx_viol']+=1
                            if len(fails)<8: fails.append(('SFX',tuple(M),q,m))
                    prev_stuck=stuck
                    okm = marked(Nprev,jm1)
                    admm = adm(Nprev,jm1)
                    lerm = leR(Nprev,0,jm1,Lng(Nprev)-1)
                    hp0 = hasParent(Ncur,0,Lng(Ncur)-1)
                    tj = transJm1(Ncur) if hp0 else None
                    r2b = (tj is not None) and marked(Nprev,tj)
                    r2c = (tj is not None) and jm1<=tj
                    d1 = rN and okm and hp0 and r2b and r2c
                    wit = mu and entry(Nprev,0,Pcut(Nprev))<col[0]
                    d2 = rN and mu and stuck and wit and col[0]>0
                    if d1: C['d1']+=1
                    if d2: C['d2']+=1
                    if d1 or d2: C['colfull']+=1
                    else:
                        C['colfail']+=1
                        if len(fails)<8:
                            fails.append(('COL',tuple(M),q,m,dict(rN=rN,okm=okm,admm=admm,
                              lerm=lerm,hp0=hp0,r2b=r2b,r2c=r2c,stuck=stuck,mu=mu,mo=mo)))
                    if stuck:
                        C['stuckcols']+=1
                    else:
                        C['ns']+=1
                        if okm: C['ns_ok']+=1
                        elif len(fails)<8: fails.append(('NSOK',tuple(M),q,m))
                        if m>=1:
                            C['ns1']+=1
                            if mo: C['ns1_mono']+=1
                            if mu:
                                C['ns1_multi']+=1
                                if jm1>=Pcut(Nprev): C['ns1_multi_ge']+=1
                                if jm1==Pcut(Nprev): C['ns1_multi_eq']+=1
                            # OKL equivalence
                            if okm==okL: C['okl_eq']+=1
                            elif len(fails)<8: fails.append(('OKL',tuple(M),q,m,okm,okL))
                        else:
                            if hp0: C['hp1_m0']+=1
                            elif len(fails)<8: fails.append(('HP1',tuple(M),q))
                    # structural claims (all m>=1 columns, stuck or not)
                    if m>=1:
                        if hp0:
                            p0=parent(Ncur,0,Lng(Ncur)-1)
                            if p0>=L: C['pge']+=1
                            else:
                                C['pge_viol']+=1
                                if len(fails)<8: fails.append(('PGE',tuple(M),q,m,p0,L))
                        # DCH dichotomy
                        if mo==reach0L: C['dch']+=1
                        elif len(fails)<8: fails.append(('DCH',tuple(M),q,m,mo,reach0L))
                        # fst monotone vs B0
                        if col[0]>B[0][0]: C['fgt']+=1
                    # netfold MAP hyps
                    if monoT(Ncur): C['hostP']+=1
                    C['hostPn']+=1
            except TimeoutErr: continue
            except Exception: continue
    return C,fails

if __name__=='__main__':
    tl=int(sys.argv[1]) if len(sys.argv)>1 else 60
    seeds=[int(x) for x in sys.argv[2:]] or [555,321,7,99,2024,13]
    from collections import Counter
    T=Counter(); F=[]
    for sd in seeds:
        for genf,tag in ((gen_random,'rand'),(gen_stps,'stps')):
            C,fails=sweep(genf,tl,(1,2,3,4,5),sd,tag)
            T+=C; F+=fails
            print(f"[{tag} s{sd}] blocks={C['blocks']} cols={C['cols']} "
                  f"colfull={C['colfull']}/{C['cols']} d1={C['d1']} d2={C['d2']} fail={C['colfail']}")
    print("\n==== TOTALS ====")
    print(f"blocks={T['blocks']} cols={T['cols']}")
    print(f"COLFULL (disj1|disj2): {T['colfull']}/{T['cols']}   fail={T['colfail']}")
    print(f"  d1(non-stuck route)={T['d1']}  d2(stuck route)={T['d2']}  stuckcols={T['stuckcols']}")
    print(f"OK0 marked(Mq,jm1): {T['ok0']}/{T['blocks']}   HP1 hp0(N_1)@m=0: {T['hp1_m0']}/{T['blocks']}")
    print(f"non-stuck cols: {T['ns']} (ok: {T['ns_ok']}/{T['ns']});  at m>=1: {T['ns1']} "
          f"(mono {T['ns1_mono']}, multi {T['ns1_multi']}: ge {T['ns1_multi_ge']}, eq {T['ns1_multi_eq']})")
    print(f"SFX stuck-suffix violations: {T['sfx_viol']}")
    print(f"PGE parent>=L (m>=1): {T['pge']}/{T['pge']+T['pge_viol']}")
    print(f"DCH monoT<=>reach0L (m>=1): {T['dch']}/{T['dch']+sum(1 for f in F if f[0]=='DCH')}")
    print(f"OKL ok(m)<=>ok(1) (non-stuck m>=1): {T['okl_eq']}/{T['ns1']}")
    print(f"reach0L blocks: {T['reach0L']}/{T['blocks']}   okL blocks: {T['okL']}/{T['blocks']}")
    print(f"fst(B!m)>fst(B!0) (m>=1): {T['fgt']}")
    print(f"MAP hostP monoT(N_(m+1)) per col: {T['hostP']}/{T['hostPn']}")
    for f in F[:12]: print("FAIL:",f)
