import sys, time, signal, random
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut)
import trans_model as tm
from trans_model import condV

"""ROUND 13: block-level reset/non-reset dichotomy for genuine deepen blocks.
Per genuine trunk-stuck-eligible block B (Msq=Mq@B), record:
  - reset_first = (fst(B[0])==0)
  - d0 = entry M 0 j1 - entry M 0 j0  (block period row-0 shift)
  - col0 ok:  fst(B[0])==0
  - colpos ok: 0<fst(B[m]) for all 0<m<Lng B
  - allpos:   0<fst(B[m]) for ALL m (non-reset-throughout)
Goal: confirm each block is EITHER (reset_first & colpos) OR (allpos), 100%,
and test whether reset_first <=> (d0==0)."""

class TimeoutErr(Exception): pass
def handler(signum,frame): raise TimeoutErr()
signal.signal(signal.SIGALRM, handler)

def safe_reduced(M, budget=1):
    signal.alarm(budget)
    try:
        r = reduced(M); signal.alarm(0); return r
    except Exception:
        signal.alarm(0); return None

def gen_shuffled(rng, maxlen=6, maxv=2, u_vals=(0,1,2,3,4)):
    pairs=[(a,b) for a in range(maxv+1) for b in range(maxv+1)]
    npairs=len(pairs)
    combos = [(u,L) for u in u_vals for L in range(2,maxlen+1)]
    while True:
        rng.shuffle(combos)
        for (u,L) in combos:
            idx = rng.randrange(npairs**(L-1))
            s=[]; t=idx
            for _ in range(L-1):
                s.append(pairs[t % npairs]); t//=npairs
            yield [(u,u)] + s

def main_sweep(timelimit, maxlen, maxv, qs, u_vals, seed):
    rng = random.Random(seed)
    t0=time.time(); cnt=0
    blocks=[]
    for M in gen_shuffled(rng, maxlen, maxv, u_vals):
        if time.time()-t0>timelimit: break
        r = safe_reduced(M, budget=1)
        if r is not True: continue
        cnt+=1
        LM=Lng(M); j1M=LM-1
        if j1M<=0: continue
        if entry(M,1,j1M)<=0: continue
        if not hasParent(M,1,j1M): continue
        j0=parent(M,1,j1M)
        d0=entry(M,0,j1M)-entry(M,0,j0)
        for q in qs:
            try:
                Mq=oper(M,q); j1=Lng(Mq)-1
                if j1<=0 or Lng(Mq)>16: continue
                if not condV(Mq): continue
                if not hasParent(Mq,1,j1): continue
                p1=parent(Mq,1,j1); parR=nextrel0(Mq,p1,j1); p0=parent(Mq,0,j1)
                if not (parR and p1==p0): continue
                jm1=Adm(Mq,p0)
                if not (jm1>0): continue
                Msq=oper(M,q+1)
                if Msq[:len(Mq)]!=Mq: continue
                B=Msq[len(Mq):]; wB=len(B)
                if wB<1: continue
                if safe_reduced(Mq,1) is not True: continue
                if not multiT(Mq): continue
                # only count blocks that actually have a trunk-stuck column
                host=list(Mq); any_stuck=False
                for m in range(wB):
                    Nprev=list(host); col=B[m]; host=host+[col]
                    if safe_reduced(host,1) is not True: break
                    if safe_reduced(Nprev,1) is not True: continue
                    if not multiT(Nprev): continue
                    if jm1 < Pcut(Nprev): any_stuck=True
                if not any_stuck: continue
                fcol0=B[0][0]
                reset_first=(fcol0==0)
                colpos=all(B[m][0]>0 for m in range(1,wB))
                allpos=all(B[m][0]>0 for m in range(wB))
                blocks.append(dict(M=tuple(M),q=q,d0=d0,wB=wB,
                                   reset_first=reset_first,colpos=colpos,
                                   allpos=allpos,fcol0=fcol0))
            except Exception:
                continue
    return cnt, blocks

if __name__=='__main__':
    tl = int(sys.argv[1]) if len(sys.argv)>1 else 200
    seed = int(sys.argv[2]) if len(sys.argv)>2 else 99
    cnt, blocks = main_sweep(tl, 6, 2, (1,2,3,4), (0,1,2,3,4), seed=seed)
    n=len(blocks)
    print(f"reduced seeds scanned={cnt}, genuine trunk-stuck BLOCKS={n}")
    if n==0: sys.exit()
    reset=[b for b in blocks if b['reset_first']]
    nonreset=[b for b in blocks if not b['reset_first']]
    print(f"reset-first blocks:    {len(reset)}/{n}")
    print(f"non-reset blocks:      {len(nonreset)}/{n}")
    # dichotomy: reset_first => colpos ; non-reset => allpos
    resetOK=sum(1 for b in reset if b['colpos'])
    nonresetOK=sum(1 for b in nonreset if b['allpos'])
    print(f"reset-first & colpos(rest positive): {resetOK}/{len(reset)}")
    print(f"non-reset & allpos(all positive):    {nonresetOK}/{len(nonreset)}")
    dichotomy=sum(1 for b in blocks if (b['reset_first'] and b['colpos']) or (not b['reset_first'] and b['allpos']))
    print(f"BLOCK-LEVEL DICHOTOMY (reset&colpos)|(nonreset&allpos): {dichotomy}/{n}")
    # reset_first <=> d0==0 ?
    eq=sum(1 for b in blocks if b['reset_first']==(b['d0']==0))
    print(f"reset_first <=> (d0==0):  {eq}/{n}")
    r_d0_0=sum(1 for b in reset if b['d0']==0)
    nr_d0_pos=sum(1 for b in nonreset if b['d0']>0)
    print(f"  among reset-first, d0==0: {r_d0_0}/{len(reset)}")
    print(f"  among non-reset,   d0>0:  {nr_d0_pos}/{len(nonreset)}")
    # any mid-block reset in non-reset blocks?
    print("\nsample non-reset blocks with d0:")
    for b in nonreset[:5]: print("  ", {k:b[k] for k in ('q','d0','wB','allpos','fcol0')})
    print("sample reset blocks with d0:")
    for b in reset[:5]: print("  ", {k:b[k] for k in ('q','d0','wB','colpos','fcol0')})
