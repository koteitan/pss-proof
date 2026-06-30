import sys, os, itertools, functools, subprocess, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import (Lng,entry,monoT,multiT,parent,TrMax,Br,oper,seg,leR,adm,Adm,marked,
                        reduced,hasParent,nextrel0,P,Pcut)
import red_model as rm
from trans_model import (Trans,Mark,ZB,PB,bpHeadT,bpHeadV,addBT,Dpt,flatBT,
                          reduced as treduced,condV,condI,condIII,condVI,scb_decomps)
import trans_model as tm

"""§8.5 keystone R2a -- ROUND 4, KEY NEW INPUT: the ALREADY-PROVEN, UNCONDITIONAL,
FROZEN lemma `multi_Marked_last_component` (layerB/pss_wip.thy:1220, empirically
0/6,080): for M in T_PS, multiT M, (M,m) in Marked  ==>  Pcut M <= m  AND
(drop (Pcut M) M, m - Pcut M) in Marked.

CONTRAPOSITIVE: if M is multiT and m < Pcut M (m strictly in the TRUNK, before
the last P-component), then (M,m) NOT in Marked -- PROVABLY, not just
empirically.  This means the Round-3 "trunk junk-collapse" branch-reset
failure mode (R2a's leR conjunct failing when the tracked mark n0 sits before
a freshly-opened branch) is not a gap in our proof TECHNIQUE -- R2a is
genuinely, provably FALSE there.  The Mark_MarkedB_nest route cannot possibly
be patched for that case.

NEW QUESTION this script answers: restricting to the genuine subcase where R2a
DOES hold (since it must, for Mark_MarkedB_nest to apply at all) -- does
multi_Marked_last_component additionally tell us anything that makes a
BRANCH-LOCAL (recursive-on-PJ, strictly smaller pairseq) version of the R2a/
R2b/R2c argument tractable, INSTEAD of the global N-level Mark_MarkedB_nest
application m_8_5_anchor_col already uses?  Concretely: when Nprev is multiT
AND (Nprev,n0) in Marked [R2a] AND (Nprev, transJm1 Ncur) in Marked [R2b],
multi_Marked_last_component gives BOTH marks land in the SAME last branch PJ
(n0 - Pcut(Nprev) and transJm1(Ncur) - Pcut(Nprev), both in Marked w.r.t.
PJ).  Does R2c (n0 <= transJm1 Ncur) transfer to the PJ-local marks too
(it must, trivially, same Pcut subtracted from both sides)?  And: in this
multiT regime, how often do R2a/R2b BOTH hold (vs the "stuck in trunk"
failure)?  I.e. what FRACTION of multiT-Nprev fold columns are actually
recoverable at all via ANY Marked-based route?
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

def main_sweep(timelimit=240, maxlen=5):
    t0=time.time(); cnt=0; checked=0
    rows=[]
    for M in gen(maxlen,2):
        if time.time()-t0>timelimit: break
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
                if w<1: continue
                host=list(Mq)
                for m in range(w):
                    Nprev = list(host)
                    host=host+[B[m]]
                    Ncur=list(host)
                    if not reduced(Ncur) or not reduced(Nprev): continue
                    if Lng(Nprev)<1: continue
                    jm1cur = transJm1(Ncur)
                    if jm1cur is None: continue
                    R2a = marked(Nprev, jm1)
                    R2b = marked(Nprev, jm1cur)
                    R2c = (jm1 <= jm1cur)
                    isMultiPrev = multiT(Nprev)
                    pcut = Pcut(Nprev) if isMultiPrev else None
                    # raw anchor (ground truth, via the real recursive Mark)
                    try:
                        markPrev = Mark(Nprev, jm1)
                        c1cur = Mark(Nprev, jm1cur)  # = transC1(Ncur)
                    except Exception:
                        continue
                    ds = scb_decomps(markPrev, flatBT(c1cur))
                    anchor_ok = len(ds) > 0
                    rows.append(dict(M=tuple(M),q=q,m=m,
                                      isMultiPrev=isMultiPrev, pcut=pcut,
                                      jm1=jm1, jm1cur=jm1cur,
                                      R2a=R2a, R2b=R2b, R2c=R2c,
                                      anchor_ok=anchor_ok))
            except Exception:
                continue
    return cnt, checked, rows

def rate(sub):
    ok=[r for r in sub if r['anchor_ok']]
    return f"{len(ok)}/{len(sub)}" if sub else "0/0"

def summarize(rows):
    print(f"total rows={len(rows)}")
    multi = [r for r in rows if r['isMultiPrev']]
    mono = [r for r in rows if not r['isMultiPrev']]
    print(f"Nprev MULTI: {len(multi)}  Nprev MONO: {len(mono)}")
    print("anchor | MONO:", rate(mono))
    print("anchor | MULTI:", rate(multi))
    print("anchor | MULTI & R2a&R2b&R2c:", rate([r for r in multi if r['R2a'] and r['R2b'] and r['R2c']]))
    print("anchor | MULTI & not R2a:", rate([r for r in multi if not r['R2a']]))
    print("anchor | MULTI & R2a & not R2b:", rate([r for r in multi if r['R2a'] and not r['R2b']]))
    print("anchor | MULTI & R2a & R2b & not R2c:", rate([r for r in multi if r['R2a'] and r['R2b'] and not r['R2c']]))
    # sanity-check multi_Marked_last_component: R2a True & multi ==> jm1 >= pcut
    bad = [r for r in multi if r['R2a'] and r['jm1'] < r['pcut']]
    print(f"SANITY (multi_Marked_last_component contrapositive): "
          f"MULTI & R2a & jm1<pcut (should be EMPTY): {len(bad)}")
    bad2 = [r for r in multi if r['R2b'] and r['jm1cur'] < r['pcut']]
    print(f"SANITY: MULTI & R2b & jm1cur<pcut (should be EMPTY): {len(bad2)}")
    # how many multi rows are "stuck in trunk" (R2a fails because jm1<pcut)?
    stuck = [r for r in multi if r['jm1'] < r['pcut']]
    notstuck = [r for r in multi if r['jm1'] >= r['pcut']]
    print(f"MULTI & jm1<pcut (TRUNK-stuck, R2a structurally impossible): {len(stuck)}/{len(multi)}")
    print("  anchor | TRUNK-stuck:", rate(stuck))
    print(f"MULTI & jm1>=pcut (mark within last branch, R2a POSSIBLE): {len(notstuck)}/{len(multi)}")
    print("  anchor | within-branch (jm1>=pcut):", rate(notstuck))
    print("  R2a rate | within-branch:", f"{sum(1 for r in notstuck if r['R2a'])}/{len(notstuck)}")
    print("  R2a&R2b&R2c rate | within-branch:",
          f"{sum(1 for r in notstuck if r['R2a'] and r['R2b'] and r['R2c'])}/{len(notstuck)}")

if __name__ == '__main__':
    cnt, checked, rows = main_sweep(240, 5)
    print(f"std&reduced scanned={cnt}, regime-checked={checked}, rows={len(rows)}")
    summarize(rows)
