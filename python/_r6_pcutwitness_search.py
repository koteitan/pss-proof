import sys, itertools, time, signal
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut)
import red_model as rm
import trans_model as tm
from trans_model import condV

"""§8.5 keystone ROUND 6 (cont'd) -- entry(N,0,0)<fst(col) was REFUTED (95/245
counterexamples, e.g. M=((1,1),(0,0),(1,0),(1,1),(1,0)), q=1, m=1/2, where
entry(N,0,0)=1=fst(col)=1, not strict).  Hand-tracing that counterexample found
a WORKING witness instead: entry(N,0,Pcut(N)) -- the start of N's own CURRENTLY
OPEN branch (not the far-away global index 0) -- which was 0 < fst(col)=1 in
both failing rows.  This script tests `entry(N,0,Pcut(N)) < fst(col)` as the
REPLACEMENT hypothesis, restricted to genuine columns (fst(col) > 0, i.e.
excluding trivial fresh-reset columns where hasParent fails for an unrelated,
already-understood reason -- those never reach m_8_5_anchor_col_trunkstuck_
regime's application point anyway since transJm1 is undefined there)."""

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

def gen(maxlen=6, maxv=2, u_vals=(0,1,2,3)):
    pairs=[(a,b) for a in range(maxv+1) for b in range(maxv+1)]
    for u in u_vals:
        for L in range(2,maxlen+1):
            for s in itertools.product(pairs, repeat=L-1):
                M=[(u,u)]+list(s)
                yield M

def main_sweep(timelimit=240, maxlen=6, maxv=2, qs=(1,2,3,4), u_vals=(0,1,2,3)):
    t0=time.time(); cnt=0; checked=0
    rows=[]
    for M in gen(maxlen,maxv,u_vals):
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
                host=list(Mq)
                for m in range(w):
                    Nprev = list(host)
                    col = B[m]
                    host=host+[col]
                    Ncur=list(host)
                    if safe_reduced(Ncur,1) is not True: continue
                    if safe_reduced(Nprev,1) is not True: continue
                    if not multiT(Nprev): continue
                    pcut = Pcut(Nprev)
                    stuck = jm1 < pcut
                    if not stuck: continue
                    fcol = col[0]
                    if fcol == 0: continue   # trivial fresh-reset column, separate case
                    epcut = entry(Nprev,0,pcut)
                    e00 = entry(Nprev,0,0)
                    rows.append(dict(M=tuple(M),q=q,m=m,u=M[0][0],
                                      pcut=pcut, epcut=epcut, e00=e00, fcol=fcol,
                                      ok_pcut=(epcut<fcol), ok_e00=(e00<fcol)))
            except Exception:
                continue
    return cnt, checked, rows

if __name__ == '__main__':
    cnt, checked, rows = main_sweep(240, 6, 2, (1,2,3,4), (0,1,2,3))
    print(f"reduced seeds scanned={cnt}, regime-checked={checked}, trunk-stuck(fcol>0) rows={len(rows)}")
    okp = [r for r in rows if r['ok_pcut']]
    print(f"entry(N,0,Pcut(N)) < fst(col): {len(okp)}/{len(rows)}")
    bad = [r for r in rows if not r['ok_pcut']]
    for r in bad[:20]:
        print("  PCUT-WITNESS COUNTEREXAMPLE:", r)
    oke = [r for r in rows if r['ok_e00']]
    print(f"(for comparison) entry(N,0,0) < fst(col): {len(oke)}/{len(rows)}")
