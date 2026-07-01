import sys, time, signal, random
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut)
import trans_model as tm
from trans_model import condV

"""ROUND 13: distribution of entry N 0 0 (=base value u) over the genuine
trunk-stuck non-reset regime.  If it is ALWAYS 0, then
`entry N 0 0 < fst col`  <=>  `0 < fst col`  =  the non-reset hypothesis,
i.e. the index-0 reduction is a COMPLETE (trivial) discharge."""

class TimeoutErr(Exception): pass
def handler(s,f): raise TimeoutErr()
signal.signal(signal.SIGALRM, handler)
def safe_reduced(M,b=1):
    signal.alarm(b)
    try: r=reduced(M); signal.alarm(0); return r
    except Exception: signal.alarm(0); return None
def gen(rng,maxlen=6,maxv=2,u_vals=(0,1,2,3,4)):
    pairs=[(a,b) for a in range(maxv+1) for b in range(maxv+1)]; npair=len(pairs)
    combos=[(u,L) for u in u_vals for L in range(2,maxlen+1)]
    while True:
        rng.shuffle(combos)
        for (u,L) in combos:
            idx=rng.randrange(npair**(L-1)); s=[]; t=idx
            for _ in range(L-1): s.append(pairs[t%npair]); t//=npair
            yield [(u,u)]+s

def sweep(tl,qs,seed):
    rng=random.Random(seed); t0=time.time(); cnt=0
    from collections import Counter
    e00=Counter(); rows=0; c0=0
    for M in gen(rng):
        if time.time()-t0>tl: break
        if safe_reduced(M,1) is not True: continue
        cnt+=1
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
                host=list(Mq)
                for m in range(wB):
                    Nprev=list(host); col=B[m]; host=host+[col]; Ncur=list(host)
                    if safe_reduced(Ncur,1) is not True: continue
                    if safe_reduced(Nprev,1) is not True: continue
                    if not multiT(Nprev): continue
                    if not (jm1<Pcut(Nprev)): continue
                    if col[0]==0: continue
                    v=entry(Nprev,0,0); e00[v]+=1; rows+=1
                    if v<col[0]: c0+=1
            except Exception: continue
    return cnt,e00,rows,c0

if __name__=='__main__':
    tl=int(sys.argv[1]) if len(sys.argv)>1 else 200
    seed=int(sys.argv[2]) if len(sys.argv)>2 else 321
    cnt,e00,rows,c0=sweep(tl,(1,2,3,4),seed)
    print(f"seed={seed} reduced scanned={cnt} stuck non-reset cols={rows}")
    print(f"entry N 0 0 value distribution: {dict(e00)}")
    print(f"C0 entry N 0 0 < fst col: {c0}/{rows}")
