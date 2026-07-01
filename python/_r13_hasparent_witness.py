import sys, time, signal, random
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut)
import trans_model as tm
from trans_model import condV

"""ROUND 13, Route 2 wiring: for genuine trunk-stuck non-reset columns of a
real deepen block, WHICH easy-to-formalize earlier index j<last has
entry X 0 j < entry X 0 last (=fst(B!m))?  That single fact discharges
hasParent(X,0,last) via idxsum_no_parent0_iff, hence the witness via
m_8_5_Pcut_nonreset_witness.  Candidates on X=Ncur=Mq@take(m+1)B, last=Lng X-1:
  C0    : index 0 (value entry X 0 0)
  Cprevw: index last-w for w=Lng B (previous copy, same offset)
  Cany  : ANY earlier smaller value exists (the true iff of hasParent)
Mirrors _r12_hasParent_check.py's filter exactly (found 74 rows)."""

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
    rows=[]
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
                Msq=oper(M,q+1)
                if Msq[:len(Mq)]!=Mq: continue
                B=Msq[len(Mq):]; wB=len(B)
                if wB<1: continue
                if safe_reduced(Mq,1) is not True: continue
                if not multiT(Mq): continue
                fcol0=B[0][0]
                if fcol0==0: continue   # reset-first, other route
                host=list(Mq)
                for m in range(wB):
                    Nprev=list(host); col=B[m]; host=host+[col]; Ncur=list(host)
                    if safe_reduced(Ncur,1) is not True: continue
                    if safe_reduced(Nprev,1) is not True: continue
                    if not multiT(Nprev): continue
                    pcutN=Pcut(Nprev)
                    stuck=jm1<pcutN
                    if not stuck: continue
                    fcol=col[0]
                    if fcol==0: continue
                    last=Lng(Ncur)-1
                    elast=entry(Ncur,0,last)     # == fcol
                    c0 = entry(Ncur,0,0) < elast
                    cprevw = (last-wB>=0) and (entry(Ncur,0,last-wB) < elast)
                    # smallest earlier value and its index
                    vals=[entry(Ncur,0,j) for j in range(last)]
                    mn=min(vals); argmn=vals.index(mn)
                    cany = mn < elast
                    rows.append(dict(M=tuple(M),q=q,m=m,wB=wB,
                                     elast=elast, e0=entry(Ncur,0,0),
                                     mn=mn, argmn=argmn, pcutN=pcutN, jm1=jm1,
                                     epcut=entry(Ncur,0,pcutN),
                                     c0=c0, cprevw=cprevw, cany=cany,
                                     hp=hasParent(Ncur,0,last)))
            except Exception:
                continue
    return cnt, rows

if __name__=='__main__':
    tl = int(sys.argv[1]) if len(sys.argv)>1 else 200
    seed = int(sys.argv[2]) if len(sys.argv)>2 else 2024
    cnt, rows = main_sweep(tl, 6, 2, (1,2,3,4), (0,1,2,3,4), seed=seed)
    n=len(rows)
    print(f"reduced seeds scanned={cnt}, genuine trunk-stuck non-reset rows={n}")
    if n==0: sys.exit()
    def frac(key): return f"{sum(1 for r in rows if r[key])}/{n}"
    print(f"hasParent(Ncur,0,last):        {frac('hp')}")
    print(f"C0    entry X 0 0 < fst(B!m):   {frac('c0')}")
    print(f"Cprevw prev-copy(-wB) smaller:  {frac('cprevw')}")
    print(f"Cany  ANY earlier smaller:      {frac('cany')}")
    print(f"epcut(Nprev)<fst (the witness): {sum(1 for r in rows if r['epcut']<r['elast'])}/{n}")
    mism=[r for r in rows if r['hp']!=r['cany']]
    print(f"hp != cany mismatches:          {len(mism)}")
    union=[r for r in rows if r['c0'] or r['cprevw']]
    print(f"C0 OR Cprevw union:             {len(union)}/{n}")
    # where does the minimum earlier value sit? (index 0 vs elsewhere)
    at0=sum(1 for r in rows if r['argmn']==0)
    print(f"argmin earlier value == index 0: {at0}/{n}")
    bad0=[r for r in rows if not r['c0']]
    print(f"\nrows where C0 FAILS: {len(bad0)}; sample:")
    for r in bad0[:8]:
        print("  ", dict(M=r['M'],q=r['q'],m=r['m'],e0=r['e0'],elast=r['elast'],
                         mn=r['mn'],argmn=r['argmn'],cprevw=r['cprevw']))
