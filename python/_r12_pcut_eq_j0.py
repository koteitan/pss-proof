import sys, itertools, time, signal, random
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut,idx1)
import red_model as rm
import trans_model as tm
from trans_model import condV

"""ROUND 12, Route 2: hand-derived hypothesis (via careful reading of `oper`'s
own periodic construction + m_8_5_slice_nextrel0_blockstart's per-boundary
nextrel0 chaining, ALREADY PROVEN): since oper(M,q) builds Mq as `q` shifted
period-copies of the FIXED base segment [j0,j1) (j0/j1/d0 computed from the
ORIGINAL SEED M, NOT from Mq, and the SAME for every q), and EVERY period
BOUNDARY j0+k*w (k=0..q-1) is nextrel0-chained to the next one (already
proven), chaining transitively should give le0(Mq, j0, Lng(Mq)-1) directly
via the FIRST boundary -- i.e. conjecture Pcut(Mq) == j0 for EVERY q (a FIXED,
q-INDEPENDENT quantity, not merely bounded/frozen).

If Pcut(Mq)==j0 holds, then epcut0 = entry(Mq,0,j0) = entry(M,0,j0) [the base
SEED's own value, q-independent, since j0 is in the k=0 unshifted copy], and
fst(B!m) = entry(M,0,j0+m) + q*d0 (oper's own explicit formula).  The witness
epcut0 < fst(B!m) for m=0 reduces to plain q*d0>0 (true since q>=1, d0>0 from
nextrel0(M,j0,j1_M)); for 0<m<w it follows from nextrel0's OWN "betwall"
clause (entries strictly between j0 and j1_M are >= entry at j1_M = entry at
j0 + d0), giving entry(M,0,j0+m) + q*d0 >= entry(M,0,j1_M) + (q-1)*d0 >
entry(M,0,j0) for q>=1.  ALL purely arithmetic, NO regime-specific empirical
residue -- test the ONE base fact (Pcut(Mq)==j0) directly, broadly, first."""

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

def main_sweep(timelimit=180, maxlen=8, maxv=4, qs=(1,2,3,4,5), u_vals=range(0,6), seed=999):
    rng = random.Random(seed)
    t0=time.time(); cnt=0; checked=0
    rows=[]
    for M in gen_random(rng, maxlen, maxv, u_vals):
        if time.time()-t0>timelimit: break
        r = safe_reduced(M, budget=1)
        if r is not True: continue
        cnt+=1
        j1M = Lng(M)-1
        if j1M<=0: continue
        i1 = idx1(M,j1M)
        if not hasParent(M,i1,j1M): continue
        j0 = parent(M,i1,j1M)
        d0 = (entry(M,0,j1M)-entry(M,0,j0)) if i1>0 else 0
        for q in qs:
            try:
                Mq=oper(M,q)
                if Lng(Mq)>20: continue
                if not multiT(Mq): continue
                if safe_reduced(Mq,1) is not True: continue
                checked+=1
                pcutMq = Pcut(Mq)
                epcut0 = entry(Mq,0,pcutMq)
                base_epcut0 = entry(M,0,j0) if j0 < Lng(M) else None
                rows.append(dict(M=tuple(M),q=q,j0=j0,d0=d0,i1=i1,
                                  pcutMq=pcutMq,
                                  pcut_eq_j0=(pcutMq==j0),
                                  epcut0=epcut0,
                                  base_epcut0=base_epcut0,
                                  epcut0_eq_base=(epcut0==base_epcut0)))
            except Exception:
                continue
    return cnt, checked, rows

if __name__ == '__main__':
    tl = int(sys.argv[1]) if len(sys.argv)>1 else 180
    cnt, checked, rows = main_sweep(tl)
    print(f"reduced seeds scanned={cnt}, (M,q) multiT-checked={checked}, rows={len(rows)}")
    ok = [r for r in rows if r['pcut_eq_j0']]
    print(f"Pcut(Mq)==j0 (q-independent): {len(ok)}/{len(rows)}")
    bad = [r for r in rows if not r['pcut_eq_j0']]
    for r in bad[:15]:
        print("  BAD pcut_eq_j0:", r)
    ok2 = [r for r in rows if r['epcut0_eq_base']]
    print(f"epcut0==entry(M,0,j0) (q-independent value): {len(ok2)}/{len(rows)}")
    for r in [r for r in rows if not r['epcut0_eq_base']][:10]:
        print("  BAD epcut0_eq_base:", r)
