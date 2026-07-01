import sys, time, signal, random
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut)
import trans_model as tm
from trans_model import condV

"""ROUND 13: candidate FULL-coverage structural witness for the non-reset
trunk-stuck witness: c := Pcut(Mq) (the BASE sequence's row-0 cut, FIXED per
block).  Records:
  V := entry Mq 0 (Pcut Mq)   (is it always 0? -> would make it TRIVIAL)
  basecut := V < fst(B!m)
  witness := entry(Nprev,0,Pcut Nprev) < fst(B!m)  (the true fact)
over many seeds for broad coverage."""

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
    Vdist=Counter(); rows=0; basecut=0; wit=0; Vpos_but_wit=0
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
                pcMq=Pcut(Mq); V=entry(Mq,0,pcMq)
                host=list(Mq)
                for m in range(wB):
                    Nprev=list(host); col=B[m]; host=host+[col]; Ncur=list(host)
                    if safe_reduced(Ncur,1) is not True: continue
                    if safe_reduced(Nprev,1) is not True: continue
                    if not multiT(Nprev): continue
                    if not (jm1<Pcut(Nprev)): continue
                    fc=col[0]
                    if fc==0: continue
                    rows+=1; Vdist[V]+=1
                    bc = V<fc
                    w = entry(Nprev,0,Pcut(Nprev))<fc
                    if bc: basecut+=1
                    if w: wit+=1
            except Exception: continue
    return cnt,Vdist,rows,basecut,wit

if __name__=='__main__':
    tl=int(sys.argv[1]) if len(sys.argv)>1 else 60
    seeds=[int(x) for x in sys.argv[2:]] or [555,321,7,99,2024,13,42]
    from collections import Counter
    TV=Counter(); TR=0; TB=0; TW=0
    for sd in seeds:
        c,Vd,r,b,w=sweep(tl,(1,2,3,4),sd)
        TV+=Vd; TR+=r; TB+=b; TW+=w
        print(f"seed={sd}: rows={r} basecut(V<fc)={b}/{r} witness={w}/{r} Vdist={dict(Vd)}")
    print(f"\nTOTAL rows={TR}")
    print(f"basecut  entry Mq 0 (Pcut Mq) < fst col: {TB}/{TR} ({100*TB/max(1,TR):.1f}%)")
    print(f"witness  epcut(Nprev) < fst col:         {TW}/{TR} ({100*TW/max(1,TR):.1f}%)")
    print(f"V=entry Mq 0 (Pcut Mq) distribution: {dict(TV)}")
    print(f"V==0 fraction: {TV.get(0,0)}/{TR}")
