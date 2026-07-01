import sys, itertools, time, signal
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut)
import red_model as rm
import trans_model as tm
from trans_model import condV

"""ROUND 11, Route 2, MAJOR SIMPLIFICATION CANDIDATE: the previous script found
epcut := entry(Nprev,0,Pcut(Nprev)) == 0 in ALL 296/296 trunk-stuck rows (not
just the "ANCHOR>=fcol" sub-case -- ALL of them, including the 30 "ANCHOR<fcol"
rows too).  Hypothesis: this is because Pcut(Nprev) is CONSTANT = Lng(Mq)
(the position of B[0], the deepen-block's own FIRST/reset column, which always
has fst=0 by construction) throughout the ENTIRE trunk-stuck run of a single
deepen block (m=1..w-1) -- i.e. Pcut does NOT keep advancing column by column,
it jumps ONCE (from Pcut(Mq) to Lng(Mq), Round 9's "jump" finding) and then
STAYS there for the rest of this block's run.  If true, epcut = entry(Nprev, 0,
Lng(Mq)) = fst(B[0]) = 0 directly (Nprev is a further extension of the list, so
its entry at the EARLIER fixed position Lng(Mq) never changes), giving the
FULL witness epcut(=0) < fcol(>0) with NO reference to ANCHOR at all.

Test directly: Pcut(Nprev) == Lng(Mq) for every trunk-stuck (jm1<Pcut(Nprev),
fcol>0) row, for m=0..w-1 (INCLUDING m=0, this time NOT filtered by fcol>0,
just checking the Pcut value itself -- though m=0's own column is the reset,
we still track Pcut of Nprev BEFORE appending column m)."""

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
                LngMq = Lng(Mq)
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
                    epcut = entry(Nprev,0,pcut)
                    rows.append(dict(M=tuple(M),q=q,m=m,u=M[0][0],
                                      LngMq=LngMq, pcut=pcut, epcut=epcut,
                                      fcol=fcol,
                                      pcut_eq_LngMq=(pcut==LngMq),
                                      witness=(fcol>0 and epcut<fcol) or fcol==0))
            except Exception:
                continue
    return cnt, checked, rows

if __name__ == '__main__':
    cnt, checked, rows = main_sweep(240, 6, 2, (1,2,3,4), (0,1,2,3))
    print(f"reduced seeds scanned={cnt}, regime-checked={checked}, trunk-stuck rows (incl m=0)={len(rows)}")
    ok = [r for r in rows if r['pcut_eq_LngMq']]
    print(f"Pcut(Nprev)==Lng(Mq): {len(ok)}/{len(rows)}")
    for r in [r for r in rows if not r['pcut_eq_LngMq']][:15]: print("  BAD pcut!=LngMq", r)
    okE = [r for r in rows if r['epcut']==0]
    print(f"epcut==0: {len(okE)}/{len(rows)}")
    for r in [r for r in rows if r['epcut']!=0][:15]: print("  BAD epcut!=0", r)
    m0 = [r for r in rows if r['m']==0]
    print(f"m==0 rows (the reset column itself): {len(m0)}")
