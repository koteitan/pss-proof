import sys, time, signal, random
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut,idx1)
import trans_model as tm
from trans_model import condV

"""ROUND 14 front K: branch-exact checks matching the Isabelle statements.
Per genuine trunk-stuck-eligible block (regime filters as _r13_basecut):
 i1=0 branch (entry(M,1,j1M)==0):
   E1a stuck col => m>0                                (exclusion instance)
   E1b fst(B!m)==entry(M,0,j0M+m)                      (explicit block, d0=0)
   E1c for stuck m>0: entry(M,0,j0M+m)>=entry(M,0,j1M) (nextrel0 betw clause)
   E1d entry(Mq,0,j0M)==entry(M,0,j0M)                 (copy-0 unshifted)
 i1=1 branch (entry(M,1,j1M)>0):
   E2a fst(B!m)==entry(M,0,j0M+m)+q*d0M
   E2b prev-copy: entry(Mq,0,Lng(M[q-1])+m)==entry(M,0,j0M+m)+(q-1)*d0M
   E2c d0M>=1
   E2d strict: prevcopy < fst(B!m)  for ALL m (incl stuck)
 both:
   E3 Pcut(Mq)<=jm1  and adm(Mq,Pcut(Mq))              (m=0 exclusion mech)
   E4 hasParent(Mq,0,Lng(Mq)-1) unique row-0 parent
   E5 final witness entry(Nprev,0,Pcut(Nprev))<fst(B!m) on stuck cols"""

class TimeoutErr(Exception): pass
def handler(s,f): raise TimeoutErr()
signal.signal(signal.SIGALRM, handler)
def safe_reduced(M,b=1):
    signal.alarm(b)
    try: r=reduced(M); signal.alarm(0); return r
    except Exception: signal.alarm(0); return None

def gen(rng,maxlen=6,maxv=3,u_vals=(0,1,2,3,4)):
    pairs=[(a,b) for a in range(maxv+1) for b in range(maxv+1)]; npair=len(pairs)
    combos=[(u,L) for u in u_vals for L in range(2,maxlen+1)]
    while True:
        rng.shuffle(combos)
        for (u,L) in combos:
            idx=rng.randrange(npair**(L-1)); s=[]; t=idx
            for _ in range(L-1): s.append(pairs[t%npair]); t//=npair
            yield [(u,u)]+s

def sweep(tl,qs,seed):
    rng=random.Random(seed); t0=time.time()
    from collections import Counter
    C=Counter(); seen=set(); bad=[]
    for M in gen(rng):
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
        j0M=parent(M,i1M,j1M)
        d0M=(entry(M,0,j1M)-entry(M,0,j0M)) if i1M>0 else 0
        wM=j1M-j0M
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
                tag='b%d'%i1M
                C[tag+'_blocks']+=1
                pcMq=Pcut(Mq)
                # E3 / E4
                C['E3_pc_le_jm1']+= (pcMq<=jm1); C['E3_n']+=1
                C['E3b_adm_pc']+= (1 if adm(Mq,pcMq) else 0)
                C['E4_hp0Mq']+= (1 if hasParent(Mq,0,j1) else 0); C['E4_n']+=1
                if i1M==1:
                    Mqm1=oper(M,q-1) if q>=1 else None
                    Lprev=Lng(Mqm1)
                    C['E2c_d0ge1']+=(d0M>=1); C['E2c_n']+=1
                host=list(Mq)
                for m in range(wB):
                    Nprev=list(host); col=B[m]; host=host+[col]; Ncur=list(host)
                    if safe_reduced(Ncur,1) is not True: continue
                    if safe_reduced(Nprev,1) is not True: continue
                    if not multiT(Nprev): continue
                    stuck = (jm1<Pcut(Nprev))
                    fc=col[0]
                    if i1M==0:
                        C['E1b_n']+=1
                        C['E1b']+=(fc==entry(M,0,j0M+m))
                        if stuck and fc>0:
                            C['E1a_n']+=1; C['E1a_mpos']+=(m>0)
                            if m>0:
                                C['E1c_n']+=1
                                C['E1c']+=(entry(M,0,j0M+m)>=entry(M,0,j1M))
                            C['E1d_n']+=1
                            C['E1d']+=(entry(Mq,0,j0M)==entry(M,0,j0M))
                    else:
                        C['E2a_n']+=1
                        C['E2a']+=(fc==entry(M,0,j0M+m)+q*d0M)
                        pcv=entry(Mq,0,Lprev+m)
                        C['E2b_n']+=1
                        C['E2b']+=(pcv==entry(M,0,j0M+m)+(q-1)*d0M)
                        C['E2d_n']+=1; C['E2d']+=(pcv<fc)
                        if stuck and fc>0: C['E2stuck']+=1
                    if stuck and fc>0:
                        C['E5_n']+=1
                        ok=entry(Nprev,0,Pcut(Nprev))<fc
                        C['E5']+=ok
                        if not ok and len(bad)<5:
                            bad.append((tuple(M),q,m,i1M))
            except Exception: continue
    return C,bad

if __name__=='__main__':
    tl=int(sys.argv[1]) if len(sys.argv)>1 else 60
    seeds=[int(x) for x in sys.argv[2:]] or [11,222,3333,44444,5]
    from collections import Counter
    T=Counter(); B=[]
    for sd in seeds:
        C,bad=sweep(tl,(1,2,3,4,5),sd); T+=C; B+=bad
        print(f"seed {sd}: {dict(C)}")
    print("\n==== TOTALS ====")
    for k in sorted(T): print(f"  {k}: {T[k]}")
    print(f"E1a stuck=>m>0: {T['E1a_mpos']}/{T['E1a_n']}")
    print(f"E1b fc==base(i1=0): {T['E1b']}/{T['E1b_n']}  E1c interior>=j1M: {T['E1c']}/{T['E1c_n']}  E1d copy0: {T['E1d']}/{T['E1d_n']}")
    print(f"E2a fc formula(i1=1): {T['E2a']}/{T['E2a_n']}  E2b prevcopy: {T['E2b']}/{T['E2b_n']}  E2c d0>=1: {T['E2c_d0ge1']}/{T['E2c_n']}  E2d strict: {T['E2d']}/{T['E2d_n']}  stuckrows(i1=1): {T['E2stuck']}")
    print(f"E3 Pcut(Mq)<=jm1: {T['E3_pc_le_jm1']}/{T['E3_n']}  adm(Mq,Pcut): {T['E3b_adm_pc']}/{T['E3_n']}  E4 hp0(Mq): {T['E4_hp0Mq']}/{T['E4_n']}")
    print(f"E5 witness on stuck: {T['E5']}/{T['E5_n']}")
    if B: print("BAD:",B)
