import sys, itertools, time, signal
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut)
import red_model as rm
import trans_model as tm
from trans_model import condV

"""§8.5 keystone ROUND 7 (cont'd) -- ROUTE 2 mechanism probe.  Round 7's first
test confirmed Pcut(Nprev)-Lng(Mq) is q-INDEPENDENT (72/72).  This script tests
the SPECIFIC mechanism that would explain it via the ALREADY-PROVEN GENERAL
(regime-free) m_8_5_Pcut_of_le0_cut (needs: (cut) leR (N@[col]) 0 (Pcut N)
(new_last), (nocut) no j<Pcut(N) is newly a valid cut) -- i.e. does
Pcut(N@[col]) = Pcut(N) LITERALLY hold whenever entry N 0 (Pcut N) < fst col,
and specifically:
  (a) is the row-0 PARENT of the new last index (parent (N@[col]) 0 last)
      EXACTLY Pcut(N) itself (not some other index >= Pcut(N))?
  (b) does Pcut(N@[col]) = Pcut(N) hold (no reset, no smaller cut appears)?
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

def transJm1(M):
    p = parent(M,0,Lng(M)-1)
    if p is None: return None
    return tm.Adm(M, p)

def gen(maxlen=7, maxv=2, u_vals=(0,1,2,3)):
    pairs=[(a,b) for a in range(maxv+1) for b in range(maxv+1)]
    for u in u_vals:
        for L in range(2,maxlen+1):
            for s in itertools.product(pairs, repeat=L-1):
                M=[(u,u)]+list(s)
                yield M

def main_sweep(timelimit=300, maxlen=7, maxv=2, qs=(1,2,3,4), u_vals=(0,1,2,3)):
    t0=time.time(); cnt=0
    rows=[]
    for M in gen(maxlen,maxv,u_vals):
        if time.time()-t0>timelimit: break
        r = safe_reduced(M, budget=1)
        if r is not True: continue
        cnt+=1
        for q in qs:
            try:
                Mq=oper(M,q); j1=Lng(Mq)-1
                if j1<=0 or Lng(Mq)>18: continue
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
                    if fcol == 0: continue
                    epcut = entry(Nprev,0,pcut)
                    if not (epcut < fcol): continue  # only the "witness holds" cases
                    lastidx = Lng(Ncur)-1
                    par0 = parent(Ncur,0,lastidx) if hasParent(Ncur,0,lastidx) else None
                    par_eq_pcut = (par0 == pcut)
                    pcut_cur = Pcut(Ncur) if multiT(Ncur) else None
                    pcut_frozen = (pcut_cur == pcut)
                    rows.append(dict(M=tuple(M),q=q,m=m,pcut=pcut,par0=par0,
                                      par_eq_pcut=par_eq_pcut,
                                      pcut_cur=pcut_cur, pcut_frozen=pcut_frozen,
                                      multiT_cur=multiT(Ncur)))
            except Exception:
                continue
    return cnt, rows

if __name__ == '__main__':
    cnt, rows = main_sweep(300, 7, 2, (1,2,3,4), (0,1,2,3))
    print(f"reduced seeds scanned={cnt}, witness-holds trunk-stuck rows={len(rows)}")
    a_ok = [r for r in rows if r['par_eq_pcut']]
    print(f"(a) row-0 parent of new last index == Pcut(N): {len(a_ok)}/{len(rows)}")
    a_bad = [r for r in rows if not r['par_eq_pcut']]
    for r in a_bad[:10]:
        print("  (a) MISMATCH:", r)
    notmulti = [r for r in rows if not r['multiT_cur']]
    print(f"Ncur NOT multiT anymore (branch closed/became mono): {len(notmulti)}/{len(rows)}")
    for r in notmulti[:5]:
        print("  NOT-MULTI:", r)
    haveB = [r for r in rows if r['multiT_cur']]
    b_ok = [r for r in haveB if r['pcut_frozen']]
    print(f"(b) Pcut(N@[col]) == Pcut(N) among still-multiT: {len(b_ok)}/{len(haveB)}")
    b_bad = [r for r in haveB if not r['pcut_frozen']]
    for r in b_bad[:10]:
        print("  (b) PCUT-CHANGED:", r)
