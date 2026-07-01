import sys, itertools, time, signal, random
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut)
import red_model as rm
import trans_model as tm
from trans_model import condV

"""ROUND 12, Route 2, take 3: pure-random uniform sampling (_r12_nonreset_broad.py)
was too sparse -- condV-eligible M's are structurally special, so uniform
random (u,pairs) almost never hits the regime (only 14 regime-checked, 0
blocks, in 600s).  This version keeps the EXHAUSTIVE generator's structure
(same pair universe/lengths as prior rounds, known to work) but decodes
RANDOM indices directly into the product space (mixed-radix), so a time-
bounded run samples UNIFORMLY across ALL (u, length) combinations instead of
only ever reaching u=0 / small lengths within the budget."""

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

def gen_shuffled(rng, maxlen=6, maxv=2, u_vals=(0,1,2,3,4)):
    pairs=[(a,b) for a in range(maxv+1) for b in range(maxv+1)]
    npairs=len(pairs)
    combos = [(u,L) for u in u_vals for L in range(2,maxlen+1)]
    while True:
        rng.shuffle(combos)
        for (u,L) in combos:
            # decode a random index directly (mixed radix) -- avoids
            # materializing the full product for large L
            idx = rng.randrange(npairs**(L-1))
            s = []
            t = idx
            for _ in range(L-1):
                s.append(pairs[t % npairs]); t//=npairs
            yield [(u,u)] + s

def main_sweep(timelimit=300, maxlen=6, maxv=2, qs=(1,2,3,4), u_vals=(0,1,2,3,4), seed=777):
    rng = random.Random(seed)
    t0=time.time(); cnt=0; checked=0
    blocks=[]
    for M in gen_shuffled(rng, maxlen, maxv, u_vals):
        if time.time()-t0>timelimit: break
        r = safe_reduced(M, budget=1)
        if r is not True: continue
        cnt+=1
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
    tl = int(sys.argv[1]) if len(sys.argv)>1 else 300
    cnt, checked, blocks = main_sweep(tl, 6, 2, (1,2,3,4), (0,1,2,3,4))
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

    # also report the F1-across-q (base-level, not per-column) check: is
    # Pcut(Mq) itself constant if we vary q for the SAME M?  Group by M.
    from collections import defaultdict
    byM = defaultdict(dict)
    for b in blocks:
        byM[b['M']][b['q']] = b['PcutMq']
    multi_q = {m:v for m,v in byM.items() if len(v)>1}
    const_ct = sum(1 for m,v in multi_q.items() if len(set(v.values()))==1)
    print(f"\nSeeds with >=2 q's sampled: {len(multi_q)}; "
          f"Pcut(Mq) CONSTANT across q for that seed: {const_ct}/{len(multi_q)}")
