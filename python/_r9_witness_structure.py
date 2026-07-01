import sys, itertools, time, signal
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut)
import red_model as rm
import trans_model as tm
from trans_model import condV

"""§8.5 ROUND 9, Route A investigation -- structural analysis of the trunk-stuck
witness `entry N 0 (Pcut N) < fst col`, built as a MINIMAL DIFF on top of the
known-working harness _r6_pcutwitness_search.py (which found 245 genuine
trunk-stuck instances 245/245 for the witness itself).  ADDS: is Pcut(Nprev)
CONSTANT = Pcut(Mq) throughout a trunk-stuck run (pconst)? is e_star :=
entry(Mq,0,Pcut(Mq)) <= e_j0 := entry(Mq,0,j0) (j0=parent Mq 1 (Lng Mq-1))
(trunk containment)? is d0 := entry(Mq,0,j1)-entry(Mq,0,j0) > 0 (row-0 strictly
grows each period)?  If pconst+e00_le+d0pos all hold UNIVERSALLY, then
entry(Nprev,0,Pcut(Nprev)) = e_star <= e_j0 < e_j0 + q*d0 <= fst(col) gives a
CLEAN DERIVATION of the witness from these three simpler regime facts (q>=1)."""

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
                pcut_Mq = Pcut(Mq)
                j0 = p1
                e_j0 = entry(Mq,0,j0)
                d0 = entry(Mq,0,j1) - entry(Mq,0,j0)
                e_star = entry(Mq,0,pcut_Mq)
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
                                      pcut=pcut, pcut_Mq=pcut_Mq, epcut=epcut,
                                      e_star=e_star, e_j0=e_j0, d0=d0, j0=j0,
                                      fcol=fcol,
                                      witness=(epcut<fcol),
                                      pconst=(pcut==pcut_Mq),
                                      e00_le=(e_star<=e_j0),
                                      d0pos=(d0>0),
                                      derived=(e_star + q*d0 < fcol) if d0>=0 else None))
            except Exception:
                continue
    return cnt, checked, rows

if __name__ == '__main__':
    cnt, checked, rows = main_sweep(240, 6, 2, (1,2,3,4), (0,1,2,3))
    print(f"reduced seeds scanned={cnt}, regime-checked={checked}, trunk-stuck(fcol>0) rows={len(rows)}")
    okw = [r for r in rows if r['witness']]
    print(f"witness entry(Nprev,0,Pcut(Nprev))<fcol: {len(okw)}/{len(rows)}")
    okp = [r for r in rows if r['pconst']]
    print(f"Pcut(Nprev)==Pcut(Mq) constant: {len(okp)}/{len(rows)}")
    oke = [r for r in rows if r['e00_le']]
    print(f"e_star<=e_j0: {len(oke)}/{len(rows)}")
    okd = [r for r in rows if r['d0pos']]
    print(f"d0>0: {len(okd)}/{len(rows)}")
    okder = [r for r in rows if r['derived']]
    print(f"DERIVED (e_star+q*d0<fcol): {len(okder)}/{len(rows)}")

    for label,key in [("WITNESS","witness"),("PCUT-CONST","pconst"),
                       ("e_star<=e_j0","e00_le"),("d0>0","d0pos"),
                       ("DERIVED","derived")]:
        bad=[r for r in rows if not r[key]]
        print(f"\n{label} counterexamples: {len(bad)}")
        for r in bad[:8]:
            print("  ", r)
