import sys, itertools, time, signal
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut)
import red_model as rm
import trans_model as tm
from trans_model import condV

"""§8.5 ROUND 10, Route 2 fresh angle: Round 9's refuted "frozen-Pcut" sub-route
showed Pcut(N) is NOT constant across a trunk-stuck run -- it can JUMP FORWARD at
internal branch-reset columns (fst=0).  Instead of claiming Pcut(N) itself is
invariant, test an INEQUALITY-only invariant that survives jumps: does
    epcut := entry(Nprev,0,Pcut(Nprev))  <=  ANCHOR := entry(Mq,0,Lng(Mq)-1)
hold at EVERY trunk-stuck column (not just the ones before any reset), where
ANCHOR is a SINGLE FIXED value computed once from Mq (the q-th iterate BEFORE
this deepen block), not tracked per-column?  And separately, does
    fcol := fst(col) > ANCHOR
hold at every trunk-stuck (fcol>0, i.e. non-reset) column?  If BOTH hold
universally this gives a clean derivation epcut <= ANCHOR < fcol avoiding any
claim that Pcut itself is frozen."""

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
                    rows.append(dict(M=tuple(M),q=q,m=m,u=M[0][0],
                                      pcut=pcut, epcut=epcut, ANCHOR=ANCHOR,
                                      fcol=fcol,
                                      witness=(epcut<fcol),
                                      epcut_le_anchor=(epcut<=ANCHOR),
                                      anchor_lt_fcol=(ANCHOR<fcol),
                                      derived=(epcut<=ANCHOR<fcol)))
            except Exception:
                continue
    return cnt, checked, rows

if __name__ == '__main__':
    cnt, checked, rows = main_sweep(240, 6, 2, (1,2,3,4), (0,1,2,3))
    print(f"reduced seeds scanned={cnt}, regime-checked={checked}, trunk-stuck(fcol>0) rows={len(rows)}")
    for label,key in [("WITNESS","witness"),("epcut<=ANCHOR","epcut_le_anchor"),
                       ("ANCHOR<fcol","anchor_lt_fcol"),("DERIVED chain","derived")]:
        ok=[r for r in rows if r[key]]
        print(f"{label}: {len(ok)}/{len(rows)}")
        bad=[r for r in rows if not r[key]]
        for r in bad[:6]:
            print("  BAD", label, r)
