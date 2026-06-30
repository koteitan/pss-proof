import sys, os, itertools, functools, subprocess, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,multiT,parent,TrMax,Br,oper,seg,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut)
import red_model as rm
from trans_model import (Trans,Mark,ZB,PB,bpHeadT,bpHeadV,addBT,Dpt,flatBT,
                          reduced as treduced,condV,condI,condIII,condVI,scb_decomps)
import trans_model as tm

"""§8.5 keystone R2a -- ROUND 4 BREAKTHROUGH CANDIDATE (after fixing a real bug in
trans_model.py's Mark(): the multi/non-monoT case used Python's SIGNED `m - j0`,
diverging from Isabelle's truncating `nat` subtraction whenever m<j0 -- fixed to
`max(m-j0,0)`).

With the bug fixed, _marked_last_component_probe.py found: in the keystone's own
regime, EVERY multiT-host fold column sampled (28/28) is "trunk-stuck" (n0 <
Pcut(Nprev), so R2a is PROVABLY impossible by multi_Marked_last_component's
contrapositive) -- YET raw `anchor` (scb_decomp existence) holds 28/28 anyway, via
a DIFFERENT, much simpler witness than Mark_MarkedB_nest.

HYPOTHESIS (from one hand-traced example): in the trunk-stuck case, BOTH
Mark(Nprev,n0) and transC1(Ncur) = Mark(Nprev, transJm1 Ncur) independently
"junk-clamp" via the SAME `multi` recursion (Mark M m = Mark PJ (max(m-Pcut M,0)))
to the IDENTICAL value Mark(PJ,0) -- because BOTH n0 and transJm1(Ncur) are < Pcut
Nprev, both clamp to 0.  If Mark(Nprev,n0) = transC1(Ncur) LITERALLY, the needed
scb_decomp is the TRIVIAL reflexive one (scb_decomp_self / m_8_5_scbSubst_whole's
precondition: s=[], b=[], c = the whole flat string) -- no Marked-membership or
Mark_MarkedB_nest needed at all.

This script tests that equality hypothesis broadly, and separately characterizes
the boundary case (the FIRST reset column of a branch, where transJm1(Ncur) may
be undefined -- no row-0 parent at all for a literal (0,0) reset column).
"""

BMS='/home/koteitan/proofs/pss-proof/wt2/tmp/yaBMS/c/bms'
@functools.lru_cache(None)
def is_std(t): return subprocess.run([BMS,"-s",rm.fmt(list(t))],capture_output=True,text=True).stdout.strip()=="1"

def transJm1(M):
    p = parent(M,0,Lng(M)-1)
    if p is None: return None
    return tm.Adm(M, p)

def gen(maxlen=6,maxv=2):
    pairs=[(a,b) for a in range(maxv+1) for b in range(maxv+1)]
    for L in range(3,maxlen+1):
        for s in itertools.product(pairs,repeat=L):
            M=list(s)
            if M[0]!=(0,0): continue
            yield M

def main_sweep(timelimit=240, maxlen=5):
    t0=time.time(); cnt=0; checked=0
    rows=[]
    for M in gen(maxlen,2):
        if time.time()-t0>timelimit: break
        try:
            if not (reduced(M) and is_std(tuple(M))): continue
        except Exception: continue
        cnt+=1
        for q in (2,3,4):
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
                    host=host+[B[m]]
                    Ncur=list(host)
                    if not reduced(Ncur) or not reduced(Nprev): continue
                    if not multiT(Nprev): continue
                    pcut = Pcut(Nprev)
                    stuck = jm1 < pcut
                    if not stuck: continue
                    jm1cur = transJm1(Ncur)
                    try:
                        markPrev = Mark(Nprev, jm1)
                    except Exception:
                        continue
                    if jm1cur is None:
                        rows.append(dict(M=tuple(M),q=q,m=m,kind='NOPARENT',
                                          markPrev=markPrev, eq=None, anchor=None))
                        continue
                    stuckJ = jm1cur < pcut
                    try:
                        c1cur = Mark(Nprev, jm1cur)
                    except Exception:
                        continue
                    eq = (markPrev == c1cur)
                    ds = scb_decomps(markPrev, flatBT(c1cur))
                    anchor_ok = len(ds) > 0
                    rows.append(dict(M=tuple(M),q=q,m=m,kind=('STUCKJ' if stuckJ else 'NOTSTUCKJ'),
                                      markPrev=markPrev, c1cur=c1cur, eq=eq, anchor=anchor_ok))
            except Exception:
                continue
    return cnt, checked, rows

if __name__ == '__main__':
    cnt, checked, rows = main_sweep(240, 5)
    print(f"std&reduced scanned={cnt}, regime-checked={checked}, rows(trunk-stuck multiT)={len(rows)}")
    from collections import Counter
    print("kind breakdown:", Counter(r['kind'] for r in rows))
    stuckj = [r for r in rows if r['kind']=='STUCKJ']
    notstuckj = [r for r in rows if r['kind']=='NOTSTUCKJ']
    noparent = [r for r in rows if r['kind']=='NOPARENT']
    def rate(sub,key):
        ok=[r for r in sub if r[key]]
        return f"{len(ok)}/{len(sub)}" if sub else "0/0"
    print("STUCKJ (both n0 & jm1cur < pcut): eq-rate=", rate(stuckj,'eq'), " anchor-rate=", rate(stuckj,'anchor'))
    print("NOTSTUCKJ (n0<pcut but jm1cur>=pcut): eq-rate=", rate(notstuckj,'eq'), " anchor-rate=", rate(notstuckj,'anchor'))
    for r in notstuckj[:10]:
        print("  NOTSTUCKJ example:", r['M'],'q=',r['q'],'m=',r['m'],'eq=',r['eq'],'anchor=',r['anchor'])
    print(f"NOPARENT (jm1cur undefined -- first reset column, no row-0 parent): {len(noparent)}")
    for r in noparent[:6]:
        print("  example:", r['M'],'q=',r['q'],'m=',r['m'],'markPrev=',r['markPrev'])
