import sys, itertools, time, signal
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut)
import red_model as rm
import trans_model as tm
from trans_model import condV

"""§8.5 ROUND 10, Route 2, refinement of _r10_witness_bound.py: that script found
epcut<=ANCHOR (ANCHOR:=entry(Mq,0,Lng(Mq)-1)) holds UNIVERSALLY (296/296) but
ANCHOR<fcol fails often (only 30/296) since ANCHOR literally equals fcol AT m=0 of
the current period (by the periodicity formula), and only grows for m>=1 (given
d0>0).  This script tests a SHARPER two-part chain designed to avoid the tie:
ANCHOR_PREV := entry(M[q-1],0,Lng(M[q-1])-1) (one FEWER period than Mq) -- since
ANCHOR_PREV = ANCHOR - d0 (one period earlier), if d0>0 then ANCHOR_PREV < fcol(m)
for EVERY m>=0 in the CURRENT (q -> q+1) deepen block (not just m>=1), giving a
uniform (no case-split) derivation IF epcut<=ANCHOR_PREV also holds universally."""

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
                if safe_reduced(Mq,1) is not True: continue
                if not multiT(Mq): continue
                ANCHOR = entry(Mq,0,j1)
                # ANCHOR_PREV: entry of M[q-1] at ITS OWN last index, if q>=1 defined & valid
                if q>=1:
                    Mqm1 = oper(M,q-1) if q>=1 else None
                    try:
                        j1m = Lng(Mqm1)-1
                        ANCHOR_PREV = entry(Mqm1,0,j1m) if j1m>=0 else None
                    except Exception:
                        ANCHOR_PREV = None
                else:
                    ANCHOR_PREV = None
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
                    row = dict(M=tuple(M),q=q,m=m,u=M[0][0],
                               pcut=pcut, epcut=epcut, ANCHOR=ANCHOR,
                               ANCHOR_PREV=ANCHOR_PREV,
                               fcol=fcol,
                               witness=(epcut<fcol))
                    if ANCHOR_PREV is not None:
                        row['epcut_le_prev']=(epcut<=ANCHOR_PREV)
                        row['prev_lt_fcol']=(ANCHOR_PREV<fcol)
                        row['derived2']=(epcut<=ANCHOR_PREV<fcol)
                    rows.append(row)
            except Exception:
                continue
    return cnt, checked, rows

if __name__ == '__main__':
    cnt, checked, rows = main_sweep(240, 6, 2, (1,2,3,4), (0,1,2,3))
    print(f"reduced seeds scanned={cnt}, regime-checked={checked}, trunk-stuck(fcol>0) rows={len(rows)}")
    rows2 = [r for r in rows if 'derived2' in r]
    print(f"rows with ANCHOR_PREV defined: {len(rows2)}/{len(rows)}")
    for label,key in [("WITNESS","witness"),("epcut<=ANCHOR_PREV","epcut_le_prev"),
                       ("ANCHOR_PREV<fcol","prev_lt_fcol"),("DERIVED2 chain","derived2")]:
        ok=[r for r in rows2 if r[key]]
        print(f"{label}: {len(ok)}/{len(rows2)}")
        bad=[r for r in rows2 if not r[key]]
        for r in bad[:6]:
            print("  BAD", label, r)
