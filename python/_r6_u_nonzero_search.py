import sys, itertools, time, signal
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut,Red)
import red_model as rm
import trans_model as tm
from trans_model import condV

"""§8.5 keystone ROUND 6 -- search for genuine u>0 (entry M 0 0 = entry M 1 0 = u
> 0) REDUCED seeds satisfying the keystone's own regime, WITHOUT going through
the yaBMS external standardness oracle (which Round 6 confirmed always forces
u=0 -- yaBMS's "standard" is the article's NARROWER "usual" notion, u=0 in the
diag base case, per content.md line 1346: the article explicitly states ST_PS
in its formal (broader) sense generalizes the usual notion by allowing u>0).
This tests whether `entry N 0 0 < fst col` (needed by
m_8_5_anchor_col_trunkstuck_regime) is robust to u>0, using `reduced()` (the
actual RT_PS-relevant check) as the sole well-formedness gate instead of
`is_std`."""

class TimeoutErr(Exception): pass
def handler(signum,frame): raise TimeoutErr()
signal.signal(signal.SIGALRM, handler)

def safe_reduced(M, budget=2):
    signal.alarm(budget)
    try:
        r = reduced(M)
        signal.alarm(0)
        return r
    except Exception:
        signal.alarm(0)
        return None

def transJm1(M):
    p = parent(M,0,Lng(M)-1)
    if p is None: return None
    return tm.Adm(M, p)

def gen(maxlen=6, maxv=2, u_vals=(1,2,3)):
    pairs=[(a,b) for a in range(maxv+1) for b in range(maxv+1)]
    for u in u_vals:
        for L in range(2,maxlen+1):
            for s in itertools.product(pairs, repeat=L-1):
                M=[(u,u)]+list(s)
                yield M

def main_sweep(timelimit=240, maxlen=6, maxv=2, qs=(1,2,3,4), u_vals=(1,2,3)):
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
                    e00 = entry(Nprev,0,0)
                    fcol = col[0]
                    rows.append(dict(M=tuple(M),q=q,m=m,u=M[0][0],
                                      e00=e00, fcol=fcol, ok=(e00<fcol)))
            except Exception:
                continue
    return cnt, checked, rows

if __name__ == '__main__':
    cnt, checked, rows = main_sweep(240, 6, 2, (1,2,3,4), (1,2,3))
    print(f"reduced u>0 seeds scanned={cnt}, regime-checked={checked}, trunk-stuck rows={len(rows)}")
    bad = [r for r in rows if not r['ok']]
    print(f"entry(N,0,0) < fst(col): {len(rows)-len(bad)}/{len(rows)}")
    for r in rows[:10]:
        print("  example:", r)
    for r in bad[:15]:
        print("  COUNTEREXAMPLE:", r)
