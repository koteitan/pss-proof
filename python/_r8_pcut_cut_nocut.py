import sys, itertools, time, signal
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,le0,P,Pcut)
import red_model as rm
import trans_model as tm
from trans_model import condV

"""ROUND 8 -- Route 2 continuation.  Round 7 identified m_8_5_Pcut_of_le0_cut
as the target lemma and diagnosed that its (cut) hypothesis resists the
naive adjacent-edge (Lng N - 1) route, needing instead a "PJ-interior-
reachability" argument via the row-0 PARENT par0 of the new last index
(which is NOT always literally Pcut(N) itself -- 177/254 yes, 77/254 no).
Round 7 did NOT examine (nocut) at all.

This script directly tests, on the SAME witness-holds trunk-stuck regime as
Round 7's freeze-mechanism probe:
  (A) cut:   le0(Ncur, pcut, lastidx_new)          -- should ALWAYS hold (freeze).
  (B) nocut: forall 0<j<pcut. not le0(Ncur, j, lastidx_new)
  (C) THE KEY MECHANISM CANDIDATE for (cut): le0(Nprev, pcut, par0) -- i.e. is
      Pcut(N) ALWAYS an ancestor (in the le0/nextrel0 unique-parent-chain sense)
      of the row-0 parent par0 of the newly appended column, even when
      par0 != pcut?  If YES always, then (cut) reduces to a GENERALISATION of
      m_8_5_marked_le0_step with c := par0 (not Lng N - 1), which IS a direct
      edge (par0 -> new, by definition of "parent") -- closing (cut) in general.
  (D) For (nocut): is "not le0(Nprev, j, pcut)" (j<pcut fails to reach pcut
      within Nprev) enough, i.e. is the failure of j to reach lastidx_new in
      Ncur EXACTLY explained by failure to reach pcut in Nprev (not by some
      NEW route opened by the appended column)?  Tests whether nocut reduces
      to a purely N-internal (not X-external) fact: does le0(Ncur,j,new) for
      j<pcut ALWAYS require le0(Ncur,j,par0), and does j<pcut,j>0 ever reach
      par0 in Ncur/Nprev?
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
                    if not (epcut < fcol): continue  # witness-holds regime
                    lastidx = Lng(Ncur)-1
                    par0 = parent(Ncur,0,lastidx) if hasParent(Ncur,0,lastidx) else None
                    # (A) cut
                    cutholds = le0(Ncur, pcut, lastidx)
                    # (B) nocut
                    nocutholds = all((not le0(Ncur,j,lastidx)) for j in range(1,pcut))
                    # (C) key mechanism candidate
                    mech = None
                    if par0 is not None:
                        mech = le0(Nprev, pcut, par0) if par0 <= Lng(Nprev)-1 else le0(Ncur,pcut,par0)
                    rows.append(dict(M=tuple(M),q=q,m=m,pcut=pcut,par0=par0,
                                      cutholds=cutholds, nocutholds=nocutholds,
                                      mech=mech))
            except Exception:
                continue
    return cnt, rows

if __name__ == '__main__':
    cnt, rows = main_sweep(300, 7, 2, (1,2,3,4), (0,1,2,3))
    print(f"reduced seeds scanned={cnt}, witness-holds trunk-stuck rows={len(rows)}")
    a_ok = [r for r in rows if r['cutholds']]
    print(f"(A) cut: le0(Ncur,pcut,lastidx_new): {len(a_ok)}/{len(rows)}")
    for r in [r for r in rows if not r['cutholds']][:5]:
        print("  (A) FAIL:", r)
    b_ok = [r for r in rows if r['nocutholds']]
    print(f"(B) nocut: no 0<j<pcut reaches lastidx_new: {len(b_ok)}/{len(rows)}")
    for r in [r for r in rows if not r['nocutholds']][:5]:
        print("  (B) FAIL:", r)
    c_ok = [r for r in rows if r['mech']]
    print(f"(C) mechanism le0(Nprev,pcut,par0) [ancestor even when par0!=pcut]: {len(c_ok)}/{len(rows)}")
    for r in [r for r in rows if not r['mech']][:10]:
        print("  (C) FAIL:", r)
