import sys, time, signal, random
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut,idx1)
import trans_model as tm
from trans_model import condV

"""ROUND 13: WHERE does the row-0 minimum of X=Mq@take(m+1)B sit for non-reset
trunk-stuck columns?  Characterize the argmin (smallest earlier row-0) index
relative to structure, esp. when index 0 is NOT the min.  Candidate structural
witness indices j<last with entry X 0 j < fst col:
  idx0     : 0
  prevcopy : last - w  (w=Lng B, previous period copy same offset)
  copy0off : Lng(trunk)+m i.e. j0+m in copy 0  (needs j0 from Mq idx1=1)
  pcutMq   : Pcut(Mq)
  anysmall : min over [0,last)
Report per-candidate coverage + argmin distribution."""

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
    rows=[]
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
                LMq=Lng(Mq); j0Mq=parent(Mq,1,j1); pcMq=Pcut(Mq)
                host=list(Mq)
                for m in range(wB):
                    Nprev=list(host); col=B[m]; host=host+[col]; Ncur=list(host)
                    if safe_reduced(Ncur,1) is not True: continue
                    if safe_reduced(Nprev,1) is not True: continue
                    if not multiT(Nprev): continue
                    if not (jm1<Pcut(Nprev)): continue
                    if col[0]==0: continue
                    last=Lng(Ncur)-1; fc=entry(Ncur,0,last)
                    vals=[entry(Ncur,0,j) for j in range(last)]
                    mn=min(vals); argmn=vals.index(mn)
                    idx0 = vals[0] < fc
                    prevcopy = (last-wB>=0) and (vals[last-wB] < fc)
                    copy0 = (j0Mq+m < last) and (vals[j0Mq+m] < fc)
                    pcMqw = (pcMq < last) and (vals[pcMq] < fc)
                    # argmn category
                    if argmn==0: cat='idx0'
                    elif argmn<j0Mq: cat='trunk'
                    elif argmn<LMq: cat='Mq-block'
                    else: cat='in-newblock'
                    rows.append(dict(idx0=idx0,prevcopy=prevcopy,copy0=copy0,
                                     pcMqw=pcMqw,cat=cat,argmn=argmn,
                                     j0Mq=j0Mq,LMq=LMq,last=last,pcMq=pcMq))
            except Exception: continue
    return cnt,rows

if __name__=='__main__':
    tl=int(sys.argv[1]) if len(sys.argv)>1 else 120
    seeds=[int(x) for x in sys.argv[2:]] or [555,321,7]
    allrows=[]; tot=0
    for sd in seeds:
        c,r=sweep(tl,(1,2,3,4),sd); tot+=c; allrows+=r
        print(f"seed={sd}: scanned={c} rows={len(r)}")
    n=len(allrows)
    if n==0: sys.exit()
    def f(k): return f"{sum(1 for r in allrows if r[k])}/{n} ({100*sum(1 for r in allrows if r[k])/n:.0f}%)"
    print(f"\nTOTAL rows={n}")
    print(f"idx0     entry X 0 0 < fc:              {f('idx0')}")
    print(f"prevcopy entry X 0 (last-w) < fc:       {f('prevcopy')}")
    print(f"copy0    entry X 0 (j0Mq+m) < fc:       {f('copy0')}")
    print(f"pcMqw    entry X 0 (Pcut Mq) < fc:      {f('pcMqw')}")
    unions={
      'idx0|prevcopy':sum(1 for r in allrows if r['idx0'] or r['prevcopy']),
      'idx0|copy0':sum(1 for r in allrows if r['idx0'] or r['copy0']),
      'idx0|prevcopy|copy0':sum(1 for r in allrows if r['idx0'] or r['prevcopy'] or r['copy0']),
      'idx0|pcMqw':sum(1 for r in allrows if r['idx0'] or r['pcMqw']),
    }
    for k,v in unions.items(): print(f"UNION {k}: {v}/{n} ({100*v/n:.0f}%)")
    from collections import Counter
    print("argmin category:", dict(Counter(r['cat'] for r in allrows)))
    print("\nsample where idx0 FAILS:")
    for r in [r for r in allrows if not r['idx0']][:8]: print("  ",r)
