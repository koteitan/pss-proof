import sys, itertools, time, signal
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut)
import red_model as rm
import trans_model as tm
from trans_model import condV

"""ROUND 11, Route 2: test the exact two-case split flagged by Round 10 as
"the germ of a two-case argument" but NOT tried:

  epcut := entry(Nprev,0,Pcut(Nprev))
  ANCHOR := entry(Mq,0,Lng(Mq)-1)   (fixed once per q, computed from Mq BEFORE
                                      the deepen block starts)
  fcol  := fst(col)                 (the appended column's row-0 value)

Round 9/10 already confirmed universally (296/296): epcut <= ANCHOR.
Round 10 found: ANCHOR < fcol fails ~90% of the time, but EVERY failure is
(diagnosed) exactly the m==0 column of the CURRENT deepen block (period
boundary, where ANCHOR == fcol by the periodicity formula), and in every one
of those failing rows epcut < ANCHOR held STRICTLY.

This script tests directly, tagging rows by m==0 vs m>=1:
  (H1) m==0  ==>  ANCHOR == fcol            (the tie is EXACTLY at m=0, not just
                                              "sometimes at m=0")
  (H2) m==0  ==>  epcut <  ANCHOR  (strict) (closes case 1: epcut<ANCHOR=fcol)
  (H3) m>=1  ==>  ANCHOR <  fcol   (strict) (closes case 2 together with the
                                              already-confirmed epcut<=ANCHOR)
  (H4, sanity) m>=1 ==> epcut <= ANCHOR (re-check, already confirmed elsewhere)

If H1+H2+H3(+existing epcut<=ANCHOR) all hold universally, the two-case split
fully closes the witness epcut<fcol with NO exceptions, by:
   m==0:  epcut < ANCHOR == fcol       ==>  epcut < fcol
   m>=1:  epcut <= ANCHOR < fcol       ==>  epcut < fcol
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
                                      m0=(m==0),
                                      anchor_eq_fcol=(ANCHOR==fcol),
                                      epcut_lt_anchor=(epcut<ANCHOR),
                                      epcut_le_anchor=(epcut<=ANCHOR),
                                      anchor_lt_fcol=(ANCHOR<fcol)))
            except Exception:
                continue
    return cnt, checked, rows

if __name__ == '__main__':
    cnt, checked, rows = main_sweep(240, 6, 2, (1,2,3,4), (0,1,2,3))
    print(f"reduced seeds scanned={cnt}, regime-checked={checked}, trunk-stuck(fcol>0) rows={len(rows)}")
    m0rows = [r for r in rows if r['m0']]
    m1rows = [r for r in rows if not r['m0']]
    print(f"m==0 rows: {len(m0rows)}   m>=1 rows: {len(m1rows)}")

    print("\n--- CASE 1 (m==0, period boundary) ---")
    ok = [r for r in m0rows if r['anchor_eq_fcol']]
    print(f"H1 ANCHOR==fcol: {len(ok)}/{len(m0rows)}")
    for r in [r for r in m0rows if not r['anchor_eq_fcol']][:6]: print("  BAD H1", r)
    ok = [r for r in m0rows if r['epcut_lt_anchor']]
    print(f"H2 epcut<ANCHOR (strict): {len(ok)}/{len(m0rows)}")
    for r in [r for r in m0rows if not r['epcut_lt_anchor']][:6]: print("  BAD H2", r)
    ok = [r for r in m0rows if r['witness']]
    print(f"sanity: witness holds at m==0: {len(ok)}/{len(m0rows)}")

    print("\n--- CASE 2 (m>=1, interior) ---")
    ok = [r for r in m1rows if r['anchor_lt_fcol']]
    print(f"H3 ANCHOR<fcol (strict): {len(ok)}/{len(m1rows)}")
    for r in [r for r in m1rows if not r['anchor_lt_fcol']][:10]: print("  BAD H3", r)
    ok = [r for r in m1rows if r['epcut_le_anchor']]
    print(f"H4 epcut<=ANCHOR: {len(ok)}/{len(m1rows)}")
    for r in [r for r in m1rows if not r['epcut_le_anchor']][:6]: print("  BAD H4", r)
    ok = [r for r in m1rows if r['witness']]
    print(f"sanity: witness holds at m>=1: {len(ok)}/{len(m1rows)}")

    print("\n--- OVERALL closure check ---")
    derived_all = all(
        (r['epcut_lt_anchor'] and r['anchor_eq_fcol']) if r['m0']
        else (r['epcut_le_anchor'] and r['anchor_lt_fcol'])
        for r in rows
    )
    print(f"two-case derivation closes witness for ALL {len(rows)} rows: {derived_all}")
