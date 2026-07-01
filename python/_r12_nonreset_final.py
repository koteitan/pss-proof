import sys, itertools, time, signal, random
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut)
import red_model as rm
import trans_model as tm
from trans_model import condV

"""ROUND 12, Route 2, take 4 -- CONFIRMATORY, LARGER sweep of the promising
lead from _r12_nonreset_broad2.py: restricted to genuinely TRUNK-STUCK columns
within blocks whose OWN first appended column is NON-reset (fst(B[0])!=0, the
majority ~60-80% case the parent flagged as uncovered), the FIXED quantity

  epcut0 := entry(Mq,0,Pcut(Mq))   [computed ONCE, before the deepen block
                                     even starts -- NOT recomputed per column]

satisfied epcut0 < fst(B!m) at EVERY genuinely trunk-stuck column m, 155/155
in a first confirmatory run (0 exceptions).  This script (a) scales up the
sample substantially, (b) adds a diagnostic to check WHETHER this holds
because Pcut(Nprev) literally equals Pcut(Mq) at exactly the stuck columns
(even though it drifts at non-stuck ones -- F1's "ALL columns" check only got
71/226), and (c) reports coverage as a fraction of the GENUINE regime
(trunk-stuck, non-reset-first-column blocks) explicitly, per the process
correction from Round 11's overclaim."""

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

def gen_shuffled(rng, maxlen=7, maxv=3, u_vals=(0,1,2,3,4,5)):
    pairs=[(a,b) for a in range(maxv+1) for b in range(maxv+1)]
    npairs=len(pairs)
    combos = [(u,L) for u in u_vals for L in range(2,maxlen+1)]
    while True:
        rng.shuffle(combos)
        for (u,L) in combos:
            idx = rng.randrange(npairs**(L-1))
            s = []
            t = idx
            for _ in range(L-1):
                s.append(pairs[t % npairs]); t//=npairs
            yield [(u,u)] + s

def main_sweep(timelimit, maxlen, maxv, qs, u_vals, seed):
    rng = random.Random(seed)
    t0=time.time(); cnt=0; checked=0
    stuck_rows=[]   # one row per genuinely trunk-stuck, non-reset-first column
    n_blocks_reset=0; n_blocks_nonreset=0
    for M in gen_shuffled(rng, maxlen, maxv, u_vals):
        if time.time()-t0>timelimit: break
        r = safe_reduced(M, budget=1)
        if r is not True: continue
        cnt+=1
        for q in qs:
            try:
                Mq=oper(M,q); j1=Lng(Mq)-1
                if j1<=0 or Lng(Mq)>18: continue
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
                any_stuck=False
                fcol0 = B[0][0]
                is_reset = (fcol0==0)
                PcutMq = Pcut(Mq)
                epcut0 = entry(Mq,0,PcutMq)
                host=list(Mq)
                block_rows=[]
                for m in range(w):
                    Nprev=list(host); col=B[m]; host=host+[col]; Ncur=list(host)
                    if safe_reduced(Ncur,1) is not True: continue
                    if safe_reduced(Nprev,1) is not True: continue
                    if not multiT(Nprev): continue
                    pcutN = Pcut(Nprev)
                    stuck = jm1 < pcutN
                    if not stuck: continue
                    any_stuck=True
                    fcol = col[0]
                    if is_reset and m==0: continue  # handled by the OTHER (proven) route
                    if fcol==0: continue  # mid-block reset -- separate/rarer sub-case
                    epcut = entry(Nprev,0,pcutN)
                    block_rows.append(dict(M=tuple(M),q=q,m=m,jm1=jm1,PcutMq=PcutMq,
                                            epcut0=epcut0,pcutN=pcutN,epcut=epcut,
                                            fcol=fcol,is_reset_first=is_reset,
                                            witness0=(epcut0<fcol),
                                            witness_live=(epcut<fcol),
                                            pcut_eq_Mq=(pcutN==PcutMq)))
                if any_stuck:
                    if is_reset: n_blocks_reset+=1
                    else: n_blocks_nonreset+=1
                stuck_rows.extend(block_rows)
            except Exception:
                continue
    return cnt, checked, stuck_rows, n_blocks_reset, n_blocks_nonreset

if __name__ == '__main__':
    tl = int(sys.argv[1]) if len(sys.argv)>1 else 500
    cnt, checked, rows, nres, nnon = main_sweep(tl, 7, 3, (1,2,3,4,5), (0,1,2,3,4,5), seed=4242)
    print(f"reduced seeds scanned={cnt}, regime-checked={checked}")
    print(f"genuine trunk-stuck blocks: reset-first={nres}, non-reset-first={nnon} "
          f"(non-reset fraction={100.0*nnon/max(1,nres+nnon):.1f}%)")
    print(f"non-reset-first, non-mid-reset TRUNK-STUCK column rows collected: {len(rows)}")
    w0 = sum(1 for r in rows if r['witness0'])
    wl = sum(1 for r in rows if r['witness_live'])
    pe = sum(1 for r in rows if r['pcut_eq_Mq'])
    print(f"epcut0<fcol (FIXED Mq-level quantity): {w0}/{len(rows)} "
          f"({100.0*w0/max(1,len(rows)):.2f}%)")
    print(f"live epcut<fcol (the ACTUAL witness needed): {wl}/{len(rows)} "
          f"({100.0*wl/max(1,len(rows)):.2f}%)")
    print(f"Pcut(Nprev)==Pcut(Mq) exactly AT these stuck rows: {pe}/{len(rows)} "
          f"({100.0*pe/max(1,len(rows)):.2f}%)")
    bad = [r for r in rows if not r['witness_live']]
    print(f"\nBAD (live witness fails): {len(bad)}")
    for r in bad[:20]: print("  ", r)
