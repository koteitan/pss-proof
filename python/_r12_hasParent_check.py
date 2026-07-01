import sys, itertools, time, signal, random
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut)
import trans_model as tm
from trans_model import condV

"""ROUND 12, Route 2: does hasParent(Ncur,0,Lng(Ncur)-1) [the ONE remaining
hypothesis of the new, general m_8_5_Pcut_nonreset_witness] hold AUTOMATICALLY
at every genuinely trunk-stuck, non-reset column of a real deepen block (the
same population _r12_nonreset_broad2.py/_r12_nonreset_final.py used), so the
new lemma closes the witness with NO extra named hypothesis beyond what the
existing regime already carries?"""

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
            idx = rng.randrange(npairs**(L-1))
            s = []
            t = idx
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
                B=Msq[len(Mq):]; w=len(B)
                if w<1: continue
                if safe_reduced(Mq,1) is not True: continue
                if not multiT(Mq): continue
                fcol0 = B[0][0]
                if fcol0==0: continue  # reset-first, other route
                host=list(Mq)
                for m in range(w):
                    Nprev=list(host); col=B[m]; host=host+[col]; Ncur=list(host)
                    if safe_reduced(Ncur,1) is not True: continue
                    if safe_reduced(Nprev,1) is not True: continue
                    if not multiT(Nprev): continue
                    pcutN = Pcut(Nprev)
                    stuck = jm1 < pcutN
                    if not stuck: continue
                    fcol = col[0]
                    if fcol==0: continue
                    last = Lng(Ncur)-1
                    hp = hasParent(Ncur,0,last)
                    rows.append(dict(M=tuple(M),q=q,m=m,hasParent0=hp))
            except Exception:
                continue
    return cnt, rows

if __name__=='__main__':
    tl = int(sys.argv[1]) if len(sys.argv)>1 else 200
    cnt, rows = main_sweep(tl, 6, 2, (1,2,3,4), (0,1,2,3,4), seed=2024)
    print(f"reduced seeds scanned={cnt}, genuine trunk-stuck non-reset rows={len(rows)}")
    ok = sum(1 for r in rows if r['hasParent0'])
    print(f"hasParent(Ncur,0,Lng(Ncur)-1) holds: {ok}/{len(rows)}")
    for r in rows:
        if not r['hasParent0']: print("  MISSING hasParent:", r)
