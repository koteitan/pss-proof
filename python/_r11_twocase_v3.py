import sys, itertools, time, signal
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,multiT,parent,oper,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut)
import red_model as rm
import trans_model as tm
from trans_model import condV

"""ROUND 11, Route 2, take 3: manual inspection of the concrete failing rows in
both _r10_witness_bound.py's BAD list and this round's _r11_twocase_v2.py BAD
list shows epcut==0 in EVERY SINGLE failing (ANCHOR<fcol fails) row, in BOTH
examples (M=(0,0)(1,0)(1,1)(1,0) and M=(0,0)(1,0)(2,0)(2,1)(1,0)).  Test the much
simpler two-case split directly:

  Case 1: ANCHOR < fcol (strict).  Then epcut<=ANCHOR<fcol closes it (already-
          confirmed epcut<=ANCHOR half).
  Case 2: ANCHOR >= fcol (the "bad" rows, includes both true ties and proper
          reversals).  Conjecture: epcut == 0 in EVERY such row (given fcol>0 by
          the harness's own reset filter, 0<fcol gives epcut<fcol directly).

If Case 2's conjecture (epcut==0 whenever ANCHOR>=fcol) holds with ZERO
exceptions, this two-case split cleanly closes the witness with NO reference to
ANCHOR at all in case 2 (much simpler than chasing a strict ANCHOR<fcol bound in
the degenerate regime)."""

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
                                      anchor_lt_fcol=(ANCHOR<fcol),
                                      epcut_le_anchor=(epcut<=ANCHOR),
                                      epcut_eq0=(epcut==0)))
            except Exception:
                continue
    return cnt, checked, rows

if __name__ == '__main__':
    cnt, checked, rows = main_sweep(240, 6, 2, (1,2,3,4), (0,1,2,3))
    print(f"reduced seeds scanned={cnt}, regime-checked={checked}, trunk-stuck(fcol>0) rows={len(rows)}")
    case1 = [r for r in rows if r['anchor_lt_fcol']]
    case2 = [r for r in rows if not r['anchor_lt_fcol']]
    print(f"case1 (ANCHOR<fcol): {len(case1)}   case2 (ANCHOR>=fcol): {len(case2)}")

    print("\n--- CASE 1 ---")
    ok = [r for r in case1 if r['epcut_le_anchor']]
    print(f"epcut<=ANCHOR: {len(ok)}/{len(case1)}")
    ok = [r for r in case1 if r['witness']]
    print(f"witness holds: {len(ok)}/{len(case1)}")

    print("\n--- CASE 2 ---")
    ok = [r for r in case2 if r['epcut_eq0']]
    print(f"CONJECTURE epcut==0: {len(ok)}/{len(case2)}")
    for r in [r for r in case2 if not r['epcut_eq0']][:15]: print("  BAD epcut!=0", r)
    ok = [r for r in case2 if r['witness']]
    print(f"witness holds: {len(ok)}/{len(case2)}")

    print("\n--- closure ---")
    closed = all(
        (r['epcut_le_anchor'] and r['anchor_lt_fcol']) if r['anchor_lt_fcol']
        else r['epcut_eq0']
        for r in rows
    )
    print(f"two-case (ANCHOR<fcol vs epcut==0) closes witness for ALL {len(rows)}: {closed}")
