import sys, itertools, time, signal
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut)
import red_model as rm
import trans_model as tm
from trans_model import condV

"""ROUND 11, Route 2, MAJOR SIMPLIFICATION, part 2: _r11_pcut_eq_lngmq.py found
Pcut(Nprev) == Lng(Mq) EXACTLY for every trunk-stuck row m=1..w-1 (636/636
across 3 independent samples, zero exceptions).  This suggests a MUCH cleaner
derivation than the ANCHOR route: Pcut JUMPS to exactly Lng(Mq) (the position
of B[0], the deepen-block's own reset column) right when B[0] (fst=0) is
appended, and then FREEZES there for m=1..w-1 via the ALREADY-PROVEN Round 8
theorem m_8_5_Pcut_freezes (Pcut(N@[col])=Pcut(N) given entry N 0 (Pcut N) <
fst col -- here entry=0 < fst(col)>0 for every later non-reset column).

This script isolates the ONE missing base fact: does
    Pcut (Mq @ [B[0]]) == Lng(Mq)
hold EXACTLY (not just <=) whenever Mq is a genuine trunk-stuck host (condV,
multiT, jm1 admissible) and B[0] is the deepen-block's own first column
(known fst=0 from m_8_5_deepen_block_row0/the reset-column diagnosis)?  If so,
combined with the ALREADY-PROVEN m_8_5_Pcut_freezes (iterated), the ENTIRE
epcut==0 invariant reduces to this ONE base fact -- no ANCHOR needed at all.
"""

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
                col0 = B[0]
                fcol0 = col0[0]
                X = list(Mq)+[col0]
                LngMq = Lng(Mq)
                if safe_reduced(X,1) is not True: continue
                if not multiT(X): continue
                pcutX = Pcut(X)
                rows.append(dict(M=tuple(M),q=q,u=M[0][0],
                                  LngMq=LngMq, fcol0=fcol0, pcutX=pcutX,
                                  fcol0_is_0=(fcol0==0),
                                  pcut_eq=(pcutX==LngMq)))
            except Exception:
                continue
    return cnt, checked, rows

if __name__ == '__main__':
    cnt, checked, rows = main_sweep(240, 6, 2, (1,2,3,4), (0,1,2,3))
    print(f"reduced seeds scanned={cnt}, regime-checked={checked}, base rows={len(rows)}")
    ok = [r for r in rows if r['fcol0_is_0']]
    print(f"B[0] IS a reset column (fst==0): {len(ok)}/{len(rows)}")
    for r in [r for r in rows if not r['fcol0_is_0']][:10]: print("  fcol0!=0:", r)
    ok2 = [r for r in rows if r['pcut_eq']]
    print(f"Pcut(Mq@[B[0]])==Lng(Mq): {len(ok2)}/{len(rows)}")
    for r in [r for r in rows if not r['pcut_eq']][:15]: print("  BAD", r)
