import sys, time, signal, random
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,multiT,monoT,zeroT,parent,oper,leR,le0,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut,idx1,diagSeq)
import trans_model as tm
from trans_model import condV

"""ROUND 15 K2, STEP 0b: BLOCK-LEVEL pattern classification of the colcase
disjunction (m_8_5_anchor_fold_mixed) over genuine deepen blocks.

Per block record the pattern:
  hp0N1   = hasParent(N_1, 0, L)      (N_1 = Mq @ [B!0], L = Lng Mq)
  ok1     = le0(N_1, jm1, L)          (jm1 reaches the block-base column)
  pL      = parent(N_1, 0, L) if hp0N1
  jm1lepL = jm1 <= pL
  stuck1  = multiT(N_1) and jm1 < Pcut(N_1)     (for wB >= 2)
  colcase(m) for every m; block classes:
    D1ALL  : every column satisfies disjunct1
    MIXED  : m=0 d1, all m>=1 d2 (the r14 trunk-stuck pattern WITH a good m=0)
    FAIL0  : m=0 fails, m>=1 all d2   (colcase unsatisfiable as a whole)
    OTHER  : anything else (DANGER: a non-stuck m>=1 column failing d1, etc.)
  markid  = Mark(N_1, jm1) == Mark(Mq, jm1)  (identity of the opening step;
            only meaningful/attempted when it can be computed)
Also: SFX (stuck suffix), PGE (parent >= L for m>=1), OK1 => never stuck,
      not-ok1 & non-stuck m>=1 (danger rows), i1M split.
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

def transJm1(N):
    j1=Lng(N)-1
    if not hasParent(N,0,j1): return None
    return Adm(N,parent(N,0,j1))

def safe_mark(N,m):
    try:
        signal.alarm(2)
        r=tm.Mark(N,m); signal.alarm(0); return r
    except Exception:
        signal.alarm(0); return None

def sweep(tl,qs,seed):
    rng=random.Random(seed); t0=time.time()
    from collections import Counter
    C=Counter(); seen=set(); danger=[]; other=[]
    for M in gen_random(rng):
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
                C['i1_%d'%i1M]+=1
                C['w%s'%('1' if wB==1 else '2p')]+=1
                L=Lng(Mq)
                N1=Mq+[B[0]]
                hp0N1=hasParent(N1,0,L)
                ok1=le0(N1,jm1,L)
                pL=parent(N1,0,L) if hp0N1 else None
                if hp0N1: C['hp0N1']+=1
                if ok1: C['ok1']+=1
                if hp0N1 and ok1: C['hp0_ok1']+=1
                if hp0N1 and not ok1: C['hp0_nok1']+=1
                if (not hp0N1) and ok1: C['nohp0_ok1']+=1
                if hp0N1 and pL is not None and jm1<=pL: C['jm1lepL']+=1
                # opening-step Mark identity (only when both computable)
                ma=safe_mark(Mq,jm1); mb=safe_mark(N1,jm1)
                if ma is not None and mb is not None:
                    C['mkboth']+=1
                    if ma==mb: C['markid']+=1
                    if not hp0N1:
                        C['mkboth_nohp']+=1
                        if ma==mb: C['markid_nohp']+=1
                # per-column colcase
                pat=[]; host=list(Mq); prev_stuck=False; sfxbad=False
                for m in range(wB):
                    Nprev=list(host); col=B[m]; host=host+[col]; Ncur=list(host)
                    rN=safe_reduced(Nprev,1) is True
                    mu=multiT(Nprev)
                    stuck = mu and jm1<Pcut(Nprev)
                    if m>0 and prev_stuck and not stuck: sfxbad=True
                    prev_stuck=stuck
                    okm=marked(Nprev,jm1)
                    hp0=hasParent(Ncur,0,Lng(Ncur)-1)
                    tj=transJm1(Ncur) if hp0 else None
                    r2b=(tj is not None) and marked(Nprev,tj)
                    r2c=(tj is not None) and jm1<=tj
                    d1=rN and okm and hp0 and r2b and r2c
                    wit=mu and entry(Nprev,0,Pcut(Nprev))<col[0]
                    d2=rN and mu and stuck and wit and col[0]>0
                    pat.append('1' if d1 else ('2' if d2 else 'X'))
                    if m>=1:
                        if not stuck:
                            C['ns1cols']+=1
                            if not okm:
                                C['danger']+=1
                                if len(danger)<6: danger.append((tuple(M),q,m,ok1,hp0N1))
                        if hp0:
                            p0=parent(Ncur,0,Lng(Ncur)-1)
                            if p0>=L: C['pge']+=1
                            else: C['pgeV']+=1
                if sfxbad: C['sfxV']+=1
                s=''.join(pat)
                if all(c=='1' for c in s): C['D1ALL']+=1
                elif s[0]=='1' and all(c=='2' for c in s[1:]) and wB>=2: C['MIXED']+=1
                elif s[0]=='X' and all(c=='2' for c in s[1:]): C['FAIL0']+=1
                else:
                    C['OTHER']+=1
                    if len(other)<6: other.append((tuple(M),q,s,hp0N1,ok1))
                # ok1 vs stuck coexistence
                if ok1 and any(c=='2' for c in s): C['ok1_stuck']+=1
            except TimeoutErr: continue
            except Exception: continue
    return C,danger,other

if __name__=='__main__':
    tl=int(sys.argv[1]) if len(sys.argv)>1 else 60
    seeds=[int(x) for x in sys.argv[2:]] or [555,321,7,99,2024,13,42,1234,777,11,222,3333]
    from collections import Counter
    T=Counter(); D=[]; O=[]
    for sd in seeds:
        C,d,o=sweep(tl,(1,2,3,4,5),sd)
        T+=C; D+=d; O+=o
        print(f"[s{sd}] blocks={C['blocks']} D1ALL={C['D1ALL']} MIXED={C['MIXED']} "
              f"FAIL0={C['FAIL0']} OTHER={C['OTHER']} hp0N1={C['hp0N1']} ok1={C['ok1']}")
    print("\n==== TOTALS ====")
    print(f"blocks={T['blocks']} (i1=0: {T['i1_0']}, i1=1: {T['i1_1']};  w=1: {T['w1']}, w>=2: {T['w2p']})")
    print(f"patterns: D1ALL={T['D1ALL']} MIXED={T['MIXED']} FAIL0={T['FAIL0']} OTHER={T['OTHER']}")
    print(f"hp0N1={T['hp0N1']}/{T['blocks']}  ok1={T['ok1']}/{T['blocks']}  "
          f"hp0&ok1={T['hp0_ok1']}  hp0&!ok1={T['hp0_nok1']}  !hp0&ok1={T['nohp0_ok1']}")
    print(f"jm1<=pL (of hp0N1): {T['jm1lepL']}/{T['hp0N1']}")
    print(f"ok1 blocks containing a stuck column: {T['ok1_stuck']}")
    print(f"non-stuck m>=1 cols: {T['ns1cols']}  DANGER (non-stuck m>=1, R2a false): {T['danger']}")
    print(f"SFX violations: {T['sfxV']}   PGE: {T['pge']}/{T['pge']+T['pgeV']}")
    print(f"Mark opening identity Mark(N1,jm1)==Mark(Mq,jm1): {T['markid']}/{T['mkboth']} "
          f"(on !hp0N1 blocks: {T['markid_nohp']}/{T['mkboth_nohp']})")
    for x in D: print("DANGER:",x)
    for x in O: print("OTHER:",x)
