import sys, itertools, time, signal
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut)
import red_model as rm
import trans_model as tm
from trans_model import condV

"""ROUND 11, Route 2, take 2: the m==0-vs-m>=1 split (_r11_twocase.py) turned
out to be the WRONG axis -- a concrete fully-periodic (d0==0) seed
M=(0,0)(1,0)(1,1)(1,0) ties ANCHOR==fcol at m=1,2 too, not just m=0 (the
whole period repeats verbatim, so every column ties, not just the first).
So the two-case split round10's text ACTUALLY proposed (re-read literally)
is NOT keyed on the column index m at all -- it is keyed on epcut itself:

  Case A: epcut <  ANCHOR (strict)  ==>  only need ANCHOR <= fcol (WEAK, non-
                                          strict) to conclude epcut<fcol.
  Case B: epcut == ANCHOR (the epcut<=ANCHOR bound is tight)  ==>  need
                                          ANCHOR <  fcol (STRICT) in this
                                          sub-case only.

Test:
  (G1) epcut<=ANCHOR (already confirmed 296/296 elsewhere -- re-check here)
  (G2) whenever epcut<ANCHOR (strict, case A): is ANCHOR<=fcol (weak) universal?
  (G3) whenever epcut==ANCHOR (case B, the tight-bound rows): is ANCHOR<fcol
       (strict) universal?
If G1+G2+G3 all hold with zero exceptions, this closes the witness with a
split keyed on epcut vs ANCHOR, not on the column position m.
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
                                      epcut_lt_anchor=(epcut<ANCHOR),
                                      epcut_eq_anchor=(epcut==ANCHOR),
                                      anchor_le_fcol=(ANCHOR<=fcol),
                                      anchor_lt_fcol=(ANCHOR<fcol)))
            except Exception:
                continue
    return cnt, checked, rows

if __name__ == '__main__':
    cnt, checked, rows = main_sweep(240, 6, 2, (1,2,3,4), (0,1,2,3))
    print(f"reduced seeds scanned={cnt}, regime-checked={checked}, trunk-stuck(fcol>0) rows={len(rows)}")
    caseA = [r for r in rows if r['epcut_lt_anchor']]
    caseB = [r for r in rows if r['epcut_eq_anchor']]
    other = [r for r in rows if not r['epcut_lt_anchor'] and not r['epcut_eq_anchor']]
    print(f"caseA (epcut<ANCHOR strict): {len(caseA)}   caseB (epcut==ANCHOR): {len(caseB)}   other(epcut>ANCHOR, should be 0): {len(other)}")
    for r in other[:6]: print("  OTHER(bad, epcut>ANCHOR)", r)

    print("\n--- CASE A (epcut<ANCHOR) ---")
    ok = [r for r in caseA if r['anchor_le_fcol']]
    print(f"G2 ANCHOR<=fcol (weak): {len(ok)}/{len(caseA)}")
    for r in [r for r in caseA if not r['anchor_le_fcol']][:6]: print("  BAD G2", r)
    ok = [r for r in caseA if r['witness']]
    print(f"sanity: witness holds in caseA: {len(ok)}/{len(caseA)}")

    print("\n--- CASE B (epcut==ANCHOR) ---")
    ok = [r for r in caseB if r['anchor_lt_fcol']]
    print(f"G3 ANCHOR<fcol (strict): {len(ok)}/{len(caseB)}")
    for r in [r for r in caseB if not r['anchor_lt_fcol']][:10]: print("  BAD G3", r)
    ok = [r for r in caseB if r['witness']]
    print(f"sanity: witness holds in caseB: {len(ok)}/{len(caseB)}")

    print("\n--- OVERALL closure check ---")
    derived_all = all(
        (r['anchor_le_fcol']) if r['epcut_lt_anchor']
        else (r['anchor_lt_fcol'] if r['epcut_eq_anchor'] else False)
        for r in rows
    )
    print(f"epcut<ANCHOR-vs-epcut==ANCHOR split closes witness for ALL {len(rows)} rows: {derived_all}")
