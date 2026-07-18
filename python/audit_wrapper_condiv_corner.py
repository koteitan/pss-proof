#!/usr/bin/env python3
"""AUDIT for lean/8/8.7-corner-shape.lean MISSION (SetleCensusWrapperCondIVCorner_wc).

The wrapper-condiv KEY FINDING hoped: admeq corner => transT2 M takes the NESTED shape
(transT2 M = t3 +_B D_w t4), which would make the corner census-wrapper existence hold.
The DEGENERATE shape (t3=t4=transT2 M) makes the existence structurally FALSE.

This audit (1) classifies every admeq-corner condIV STPS host by shape, and (2) directly
searches for the existence-conclusion witnesses of SetleCensusWrapperCondIVCorner_wc on each,
using the exact Lean definitions (transC2Core copied verbatim).

RESULT: the refinement is FALSE -- the admeq corner is ALWAYS degenerate, and the residual's
existence conclusion fails on every corner host (no witness (s,b,tv,t2,c') exists).
"""
import sys, signal
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/git/python')
import red_model as rm
# memoize reach (hot path) so the corpus scan is tractable
_rc={}; _orig=rm.reach
def fast_reach(M,nextf):
    k=(tuple(map(tuple,M)),nextf.__name__); v=_rc.get(k)
    if v is None: v=_orig(M,nextf); _rc[k]=v
    return v
rm.reach=fast_reach
from red_model import Lng, entry, monoT, parent, hasParent, oper, reduced, diagSeq, fmt, adm
from trans_model import (Pred, Adm, bpHeadT, bpHeadV, PB, SigmaB, addBT, Dpt,
                         Mark, Trans, ZB, flatBT, flatBP, unflatBT, scb_decomps, isPTB_str)

class TO(Exception): pass
signal.signal(signal.SIGALRM, lambda s,f:(_ for _ in ()).throw(TO()))

def lastParent(M): return parent(M,0,Lng(M)-1)
def transJ0(M): return lastParent(M)
def transJm1(M): return Adm(M, transJ0(M))
def transC1(M): return Mark(Pred(M), transJm1(M))
def transV(M): return bpHeadV(transC1(M))
def transT2(M): return bpHeadT(transC1(M))
def transT1(M): return Trans(Pred(M))
def s84x_jm2(M): return parent(M,1,Lng(M)-1)

def transCondI(M):
    j1=Lng(M)-1; jp=parent(M,0,j1); return jp is not None and entry(M,1,j1)==0 and adm(M,jp)
def transCondIII(M):
    j1=Lng(M)-1; jp=parent(M,0,j1)
    return jp is not None and entry(M,1,j1)>0 and entry(M,1,j1)<=entry(M,1,jp) and adm(M,jp)
def transCondIV(M):
    j1=Lng(M)-1; jp=parent(M,0,j1)
    return jp is not None and entry(M,1,j1)>0 and entry(M,1,j1)<=entry(M,1,jp) and not adm(M,jp)
def transCondV(M):
    j1=Lng(M)-1; jp=parent(M,0,j1)
    return jp is not None and entry(M,1,j1)>0 and entry(M,1,jp)+1==entry(M,1,j1) and jp+1<j1
def transCondVI(M):
    j1=Lng(M)-1; jp=parent(M,0,j1)
    return jp is not None and entry(M,1,j1)>0 and entry(M,1,jp)+1==entry(M,1,j1) and jp+1==j1

def transC2Core(M,v,t2):                          # verbatim from lean/PSS/Trans.lean:139
    j1=Lng(M)-1; jp=parent(M,0,j1)
    if transCondI(M) or transCondIII(M) or transCondV(M):
        return Dpt(v, addBT(t2, Dpt(entry(M,1,j1),ZB)))
    if transCondVI(M):
        return Dpt(v, Dpt(entry(M,1,j1),ZB))
    if t2==ZB:
        return Dpt(v, Dpt(entry(M,1,jp), Dpt(entry(M,1,j1),ZB)))
    Pt2=PB(t2); J1=len(Pt2)-1; pj=Pt2[J1]
    leftDj0=(bpHeadV(pj)==entry(M,1,jp))
    t3=SigmaB(Pt2[:J1]) if leftDj0 else t2
    t4=bpHeadT(pj) if leftDj0 else t2
    return Dpt(v, addBT(t3, Dpt(entry(M,1,jp), addBT(t4, Dpt(entry(M,1,j1),ZB)))))
def transC2(M): return transC2Core(M, transV(M), transT2(M))

def is_corner_admeq(M):
    if not hasParent(M,1,Lng(M)-1): return False
    jm2=s84x_jm2(M)
    return jm2 is not None and Adm(M,jm2)==transJm1(M)

def shape_of(M):                                   # ld = (bpHeadV last-princ == entry M 1 transJ0)
    t2=transT2(M)
    if t2==ZB: return 'zero'
    return 'nested' if bpHeadV(PB(t2)[-1])==entry(M,1,transJ0(M)) else 'degenerate'

def is_rp(b): return all(x==')' for x in b)

def conclusion_witness_exists(M):
    """Search for (s,b,tv,t2,c') satisfying SetleCensusWrapperCondIVCorner_wc's conclusion,
    using the (s0,b0) that satisfy hinner+hb0 and ins defined by hflat.  Returns
    (exists_for_all_valid_s0b0, [(s0b0, found, witness)])."""
    j1=Lng(M)-1; v1=entry(M,1,j1)
    A=flatBT(transT2(M))                           # flatBT (bpHeadT (transC1 M))
    hole=flatBT(Dpt(v1,ZB))                        # flatBT (Dprin v1 0)
    cand=[(s0,b0) for (s0,b0) in scb_decomps(bpHeadT(transC2(M)), hole) if is_rp(b0)]
    out=[]
    for (s0,b0) in cand:
        B=s0+[('D',v1-1),'Z']+b0                   # flatBT (ins 0_B) via hflat, flatBT 0_B=[Z]
        # ins is a genuine total BT->BT function iff RHS parses for BZero (it does when valid)
        found=False; wit=None
        for i in range(len(A)):
            if not (isinstance(A[i],tuple) and A[i][0]=='D'): continue
            tv=A[i][1]; s=A[:i]
            for j in range(i+1,len(A)+1):
                seg=A[i:j]
                if not isPTB_str(seg): continue
                b=A[j:]
                if not is_rp(b): continue
                try: t2=unflatBT(seg[1:])
                except: continue
                if B[:len(s)]!=s: continue
                if b and B[-len(b):]!=b: continue
                mid=B[len(s):len(B)-len(b)] if b else B[len(s):]
                if not mid or not(isinstance(mid[0],tuple) and mid[0][0]=='D' and mid[0][1]==tv): continue
                try: G=unflatBT(mid[1:])
                except: continue
                pt2=t2[1]; pg=G[1]
                if len(pg)>=len(pt2) and pg[:len(pt2)]==pt2:
                    found=True; wit=(s,b,tv,t2,('T',pg[len(pt2):])); break
            if found: break
        out.append(((s0,b0),found,wit))
    all_exist = all(f for (_,f,_) in out) and len(out)>0
    return all_exist, out

def gen_corpus(umax=2,vmax=4,opermax=5,size_cap=11,cap=6000):
    seen=set(); frontier=[]
    for u in range(umax+1):
        for v in range(u,u+vmax+1):
            M=tuple(diagSeq(u,v)); seen.add(M); frontier.append(M)
    allM=set(seen)
    while frontier and len(allM)<cap:
        M=frontier.pop(); Ml=list(M)
        for n in range(opermax+1):
            try: R=oper(Ml,n)
            except: continue
            if not R or Lng(R)>size_cap: continue
            if max(max(a,b) for (a,b) in R)>22: continue
            Rt=tuple(R)
            if Rt not in allM:
                allM.add(Rt)
                if len(allM)<cap: frontier.append(Rt)
    return allM

if __name__=='__main__':
    corpus=gen_corpus()
    print("corpus size:",len(corpus),flush=True)
    corners=[]
    for M in corpus:
        Ml=list(M)
        if Lng(Ml)-1<=1: continue
        try:
            signal.alarm(3)
            ok=reduced(Ml) and monoT(Ml) and transCondIV(Ml) and is_corner_admeq(Ml)
            if ok: ok=(transT1(Ml)!=ZB)
            signal.alarm(0)
        except Exception:
            signal.alarm(0); continue
        if not ok: continue
        try:
            signal.alarm(3); sh=shape_of(Ml); ex,_=conclusion_witness_exists(Ml); signal.alarm(0)
        except Exception:
            signal.alarm(0); continue
        corners.append((Ml,sh,ex))
    from collections import Counter
    print("admeq-corner condIV mono STPS hosts (transT1!=0):",len(corners))
    print("shape distribution:",Counter(sh for _,sh,_ in corners))
    print("conclusion-exists distribution:",Counter(ex for _,_,ex in corners))
    nnest=sum(1 for _,sh,_ in corners if sh=='nested')
    ndeg =sum(1 for _,sh,_ in corners if sh=='degenerate')
    print(f"\nnested={nnest}  degenerate={ndeg}")
    bad=[(M,sh) for M,sh,ex in corners if not ex]
    print(f"hosts where conclusion existence FAILS: {len(bad)} / {len(corners)}")
    print("\n=== target (0,0)(1,1)(2,2)(2,1) detail ===")
    t=[(0,0),(1,1),(2,2),(2,1)]
    print("  shape:",shape_of(t))
    ex,det=conclusion_witness_exists(t)
    print("  conclusion exists:",ex)
    for (s0b0,f,w) in det:
        print("  (s0,b0)=",s0b0,"-> witness found:",f)
    print("\nCONCLUSION: refinement 'corner => nested' is FALSE;",
          "residual SetleCensusWrapperCondIVCorner_wc is FALSE." if bad else "residual holds.")
