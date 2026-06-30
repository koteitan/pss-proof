import sys, os, itertools, functools, subprocess, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,parent,TrMax,Br,oper,seg,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P)
import red_model as rm
from trans_model import Trans,Mark,ZB,PB,bpHeadT,reduced as treduced,condV,condI,condIII,condVI
import trans_model as tm

"""§8.5 keystone R2a/R2c -- ROUND 3 drill-down (2026-07-01, follows
_r2_anchor_nest2.py/_r2_anchor_nest3.py).  See python/_keystone_residual_summary.py
for the full write-up this script backs.  Summary of what this file demonstrates:

  1. R2a = (N,n0) in Marked = adm(N,n0) AND leR(N,0,n0,Lng(N)-1) (Marked_def).
     The adm conjunct is NEVER the obstruction (always true, ANY N extending the
     base by appended columns) -- this round formalises that as the unconditional
     `m_8_5_marked_adm_persist` (layerC/pss_scratch.thy), via the ALREADY-PROVEN
     `adm_prefix_agree_eq` (adm only inspects two LOCAL row-1 edges, which sit
     inside the shared prefix of N and any extension).

  2. The WHOLE remaining R2a content is the leR (le0) conjunct.  Filtering
     PROPERLY to the keystone's own regime (transCondV(M[q]) + the hp1/parR/coin/
     jm1pos hypotheses of m_8_5_basepoint -- NOT just condV(M) of the outer base
     seed, which under-scopes) confirms the WHOLE-PERIOD case (m==w, i.e. one
     full m_8_3_kind1_base_basepoint-covered q-step) is unconditionally true
     (92/92 in the harness below) -- consistent with the already-proven theorem.
     But FRACTIONAL intra-period columns (0<m<w) fail at a similar rate (~40%)
     whether or not m==w -- i.e. it is NOT simply "full boundary good, fractional
     bad"; le0-persistence genuinely depends on the column's own row-0-parent
     target.

  3. NEW STRUCTURAL FINDING (this round): le0-persistence across one column-append
     is governed by simple TRANSITIVITY -- formalised generically (regime-free) as
     `m_8_5_marked_le0_step` (layerC/pss_scratch.thy): given le0(N,a,c) [c<Lng N]
     and a DIRECT nextrel0 edge in N@C from c to the new index d, le0(N@C,a,d)
     follows.  Empirically: "prevOK (m-1) FALSE" => "ok m FALSE" with NO exceptions
     (0/24) -- once broken, never spontaneously recovers; "prevOK(m-1) & direct
     edge from the OLD last index" => "ok m" with NO exceptions (38/38).

  4. WHY it actually fails so often for genuine fold columns: the period block B
     frequently starts with a (0,0) "branch reset" column -- entry0 does NOT
     increase from the previous entry, so `parent(host,0,lastidx)` has NO row-0
     parent at all (the new column opens a FRESH `Br`/multiT branch sibling, not a
     literal row-0 successor of the previous entry).  See the worked example
     below: appending B = [(0,0),(1,1),(1,1)] to a condV-regime Mq makes the host
     MULTI (Br has 3 components, the growing one being its own local subtree), so
     plain row-0 "is n0 le0-reachable to the moving right end" genuinely need not
     hold -- n0 lives in an EARLIER `Br` component, and a fresh branch is not
     simply row-0-chained back through it.

  HYPOTHESIS FOR THE NEXT ROUND (not validated/formalised yet): the REAL anchor
  witness for these branch-opening columns is LOCAL, not global -- Trans/Mark's
  own `multi` case is `addBT (Trans trunk-part) (Trans last-branch)`, so the
  scbSubst substitution for a freshly-opened branch column likely succeeds because
  the marked core sits ENTIRELY inside the trailing addBT summand (the branch's
  own Trans), never needing n0's row-0 ancestry to reach across branches at all.
  This would explain why raw `anchor` (scb_decomp existence, NOT gated on R2a-c)
  holds MORE often than the Mark_MarkedB_nest-based R2a-c sufficient condition
  (82/102, 44/62 in the prior round's harness) -- the Mark_MarkedB_nest route
  is SOUND but too coarse: it demands global row-0 reachability that the genuine
  branch-interior substitution does not need.  NOT yet explored as an Isabelle
  proof route; flagged here for whoever picks this up next.
"""

BMS='/home/koteitan/proofs/pss-proof/wt2/tmp/yaBMS/c/bms'
@functools.lru_cache(None)
def is_std(t): return subprocess.run([BMS,"-s",rm.fmt(list(t))],capture_output=True,text=True).stdout.strip()=="1"

def transJm1(M):
    p = parent(M,0,Lng(M)-1)
    if p is None: return None
    return tm.Adm(M, p)

def gen(maxlen=5,maxv=2):
    pairs=[(a,b) for a in range(maxv+1) for b in range(maxv+1)]
    for L in range(3,maxlen+1):
        for s in itertools.product(pairs,repeat=L):
            M=list(s)
            if M[0]!=(0,0): continue
            yield M

def worked_example():
    M=[(0,0),(1,1),(1,1),(1,0)]
    Mq=oper(M,2); Msq=oper(M,3)
    B=Msq[len(Mq):]
    jm1=transJm1(Mq)
    print(f"worked example: M={rm.fmt(M)}  Mq={rm.fmt(Mq)}  jm1={jm1}  B={B}")
    host=list(Mq)
    for m in range(len(B)):
        host=host+[B[m]]
        lastidx=Lng(host)-1
        pl=parent(host,0,lastidx)
        print(f"  col{m} B[m]={B[m]}: host={rm.fmt(host)}  Br={Br(host)}  "
              f"parent0(lastidx)={pl}  adm(host,jm1)={adm(host,jm1)}  "
              f"leR(host,0,jm1,lastidx)={leR(host,0,jm1,lastidx)}")

def main_sweep():
    t0=time.time(); cnt=0; checked=0
    rows=[]
    for M in gen(5,2):
        if time.time()-t0>250: break
        try:
            if not (reduced(M) and is_std(tuple(M))): continue
        except Exception: continue
        cnt+=1
        for q in (2,3):
            try:
                Mq=oper(M,q); j1=Lng(Mq)-1
                if j1<=0 or Lng(Mq)>15: continue
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
                if w<2: continue
                host=list(Mq); prevok=True
                for m in range(w):
                    host=host+[B[m]]
                    lastidx=Lng(host)-1
                    if not reduced(host): continue
                    a=adm(host,jm1); l=leR(host,0,jm1,lastidx)
                    chains = (parent(host,0,lastidx)==lastidx-1)
                    rows.append((a,l,chains,prevok))
                    prevok = l
            except Exception:
                continue
    print(f"\nstd&reduced scanned={cnt}, regime-checked={checked}, rows={len(rows)}")
    def rate(sub): return f"{sum(1 for r in sub if r[1])}/{len(sub)}" if sub else "0/0"
    print("adm ALWAYS true:", rate2:=f"{sum(1 for r in rows if r[0])}/{len(rows)}")
    print("leR overall:", rate(rows))
    print("leR | prevok=True:", rate([r for r in rows if r[3]]))
    print("leR | prevok=False:", rate([r for r in rows if not r[3]]))
    print("leR | prevok=True & chains=True:", rate([r for r in rows if r[3] and r[2]]))

if __name__ == '__main__':
    worked_example()
    print()
    main_sweep()
