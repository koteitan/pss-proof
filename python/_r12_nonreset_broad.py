import sys, itertools, time, signal, random
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut)
import red_model as rm
import trans_model as tm
from trans_model import condV

"""ROUND 12, Route 2, take 2: the FIRST attempt (_r12_nonreset_majority.py) used
the EXACT same exhaustive generator as prior rounds (maxlen=6,maxv=2,u in
0..3, 240s budget) and found 106/106 genuine trunk-stuck blocks ALL had a
reset first column (fst(B!0)==0) -- ZERO non-reset examples turned up,
disagreeing with the parent's independently-verified ~20%/~66% split.  Root
cause (diagnosed): the exhaustive generator's fixed nesting order (u outer,
then length, then itertools.product) only got through u=0, small lengths
within the 240s budget -- a narrow, low-value corner of the space where
row-0 entries are very likely to be 0 by chance, NOT a representative sample.
This version uses RANDOM sampling directly over (u, length, values) so a
240-900s budget reaches a genuinely diverse mix, matching the scale/diversity
the parent's 1337-row check presumably used."""

class TimeoutErr(Exception): pass
def handler(signum,frame): raise TimeoutErr()
signal.signal(signal.SIGALRM, handler)

def safe_reduced(M, budget=1):
    signal.alarm(budget)
    try:
        r = reduced(M)
        signal.alarm(0)
        return r
    except Exception:
        signal.alarm(0)
        return None

def gen_random(rng, maxlen=8, maxv=4, u_vals=range(0,6)):
    while True:
        u = rng.choice(list(u_vals))
        L = rng.randint(2, maxlen)
        s = [(rng.randint(0,maxv), rng.randint(0,maxv)) for _ in range(L-1)]
        yield [(u,u)] + s

def main_sweep(timelimit=600, maxlen=8, maxv=4, qs=(1,2,3,4,5), u_vals=range(0,6), seed=12345):
    rng = random.Random(seed)
    t0=time.time(); cnt=0; checked=0
    blocks=[]
    for M in gen_random(rng, maxlen, maxv, u_vals):
        if time.time()-t0>timelimit: break
        r = safe_reduced(M, budget=1)
        if r is not True: continue
        cnt+=1
        for q in qs:
            try:
                Mq=oper(M,q); j1=Lng(Mq)-1
                if j1<=0 or Lng(Mq)>20: continue
                if not condV(Mq): continue
                if not hasParent(Mq,1,j1): continue
                p1=parent(Mq,1,j1); parR=nextrel0(Mq,p1,j1); p0=parent(Mq,0,j1)
                if not (parR and p1==p0): continue
                jm1=Adm(Mq,p0)
                if not (jm1>0): continue
                checked+=1
                Msq=oper(M,q+1)
                if Msq[:len(Mq)]!=Mq: continue
                B=Msq[len(Mq):]; w=len(B)
                if w<1: continue
                if safe_reduced(Mq,1) is not True: continue
                if not multiT(Mq): continue
                host=list(Mq)
                percol=[]
                any_stuck=False
                PcutMq = Pcut(Mq)
                epcut0 = entry(Mq,0,PcutMq)
                for m in range(w):
                    Nprev=list(host); col=B[m]; host=host+[col]; Ncur=list(host)
                    if safe_reduced(Ncur,1) is not True: percol.append(None); continue
                    if safe_reduced(Nprev,1) is not True: percol.append(None); continue
                    if not multiT(Nprev): percol.append(None); continue
                    pcutN = Pcut(Nprev)
                    stuck = jm1 < pcutN
                    fcol = col[0]
                    epcut = entry(Nprev,0,pcutN)
                    if stuck: any_stuck=True
                    percol.append(dict(m=m, pcutN=pcutN, stuck=stuck, fcol=fcol,
                                        epcut=epcut,
                                        pcut_frozen=(pcutN==PcutMq),
                                        witness=(epcut<fcol) if fcol!=0 else None,
                                        witness0=(epcut0<fcol)))
                if not any_stuck: continue
                fcol0 = B[0][0]
                blocks.append(dict(M=tuple(M),q=q,jm1=jm1,PcutMq=PcutMq,
                                    epcut0=epcut0, w=w, fcol0=fcol0,
                                    reset_first=(fcol0==0), percol=percol))
            except Exception:
                continue
    return cnt, checked, blocks

if __name__ == '__main__':
    import sys as _s
    tl = int(_s.argv[1]) if len(_s.argv)>1 else 600
    cnt, checked, blocks = main_sweep(tl, 8, 4, (1,2,3,4,5), range(0,6))
    print(f"reduced seeds scanned={cnt}, regime-checked={checked}, "
          f"genuine trunk-stuck-eligible BLOCKS={len(blocks)}")
    reset = [b for b in blocks if b['reset_first']]
    nonreset = [b for b in blocks if not b['reset_first']]
    print(f"blocks with reset first column (fst(B[0])==0): {len(reset)}/{len(blocks)} "
          f"({100.0*len(reset)/max(1,len(blocks)):.1f}%)")
    print(f"blocks with NON-reset first column (fst(B[0])!=0): {len(nonreset)}/{len(blocks)} "
          f"({100.0*len(nonreset)/max(1,len(blocks)):.1f}%)")

    print("\n=== MAJORITY (non-reset-first-column) sub-population ===")
    f1_rows = []
    for b in nonreset:
        for pc in b['percol']:
            if pc is None: continue
            f1_rows.append(pc['pcut_frozen'])
    if f1_rows:
        print(f"F1 Pcut(Nprev)==Pcut(Mq) for ALL columns: "
              f"{sum(f1_rows)}/{len(f1_rows)}")

    f2_rows = []
    for b in nonreset:
        for pc in b['percol']:
            if pc is None or pc['fcol']==0: continue
            f2_rows.append(pc['witness0'])
    if f2_rows:
        print(f"F2 epcut0<fcol for ALL non-reset columns (block-uniform): "
              f"{sum(f2_rows)}/{len(f2_rows)}")

    f3_rows = []
    f3_detail = []
    for b in nonreset:
        for pc in b['percol']:
            if pc is None or not pc['stuck']: continue
            if pc['fcol']==0: continue
            f3_rows.append(pc['witness0'])
            f3_detail.append((b,pc))
    if f3_rows:
        print(f"F3 epcut0<fcol for TRUNK-STUCK non-reset columns only: "
              f"{sum(f3_rows)}/{len(f3_rows)}")
        bad = [(b,pc) for (b,pc) in f3_detail if not pc['witness0']]
        for b,pc in bad[:10]:
            print("  BAD F3:", dict(M=b['M'],q=b['q'],jm1=b['jm1'],PcutMq=b['PcutMq'],
                                     epcut0=b['epcut0'],m=pc['m'],fcol=pc['fcol'],
                                     epcut=pc['epcut'],pcutN=pc['pcutN']))

    f3b_rows = []
    for b in nonreset:
        for pc in b['percol']:
            if pc is None or not pc['stuck']: continue
            if pc['fcol']==0: continue
            f3b_rows.append(pc['witness'])
    if f3b_rows:
        print(f"F3b (live epcut)<fcol for TRUNK-STUCK non-reset columns: "
              f"{sum(f3b_rows)}/{len(f3b_rows)}")

    midreset = 0
    for b in nonreset:
        if any(pc is not None and pc['fcol']==0 for pc in b['percol'][1:]):
            midreset += 1
    print(f"\nblocks (majority pop) with a MID-block reset column (0<m, fcol==0): "
          f"{midreset}/{len(nonreset)}")
