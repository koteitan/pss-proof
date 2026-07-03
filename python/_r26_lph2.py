#!/usr/bin/env python3
# r26-LPH2: pin down the cleanest provable route for
#   RN(transC1 M)[1] == entry M 1 (transJ1 M)   (form-1 residual of lph)
# over the GENUINE non-adm condV surgery regime. Deep + brute-force straddle + direct.
import sys, time, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-f7/python')
from red_model import (Lng, entry, monoT, seg, adm, oper, diagSeq,
                       parent, Adm, Pred, zeroT, P)
import red_model as rm
from trans_model import (Trans, Mark, bpHeadT, bpHeadV, Dpt, PB, ZB, flatBT,
                         condV, condI, condIII, condVI)
from trans_model import reduced as reduced   # cheap RedCondA/B check (m_6_6 equiv)

def transJ1(M): return Lng(M)-1
def transJ0(M): return parent(M,0,transJ1(M))
def transJm1(M): return Adm(M, transJ0(M))
def transC1(M): return Mark(Pred(M), transJm1(M))
def transT2(M): return bpHeadT(transC1(M))

def RightNodes(t):
    xs = t[1]
    if not xs: return []
    u = xs[-1][1]; a = xs[-1][2]
    return [u] + RightNodes(a)

def Ts(M):
    try: return Trans(M)
    except Exception: return None

# ---- host generators ----
def gen_oper(maxlen, maxn, maxseed, cap):
    seen=set(); frontier=[]
    for u in range(maxseed):
        for v in range(u,u+maxseed+2):
            M=tuple(diagSeq(u,v))
            if M not in seen: seen.add(M); frontier.append(list(M))
    pool=list(frontier)
    while frontier and len(pool)<cap:
        nxt=[]
        for M in frontier:
            if Lng(M)<=1: continue
            for n in range(1,maxn+1):
                N=oper(M,n)
                if Lng(N)>maxlen: continue
                t=tuple(N)
                if t not in seen: seen.add(t); nxt.append(N); pool.append(N)
                if len(pool)>=cap: break
            if len(pool)>=cap: break
        frontier=nxt
    return pool

def gen_straddle(maxlen, maxn, maxseed, cap):
    # reduced mono hosts, take seg(H,r,c) with r non-adm -> genuine straddle subseqs
    base = gen_oper(maxlen, maxn, maxseed, cap)
    out=set()
    for H in base:
        if not (reduced(H) and monoT(H)): continue
        n=Lng(H)
        for r in range(1,n-1):
            if adm(H,r): continue
            for c in range(r+1,n):
                sr=tuple(seg(H,r,c))
                out.add(sr)
    return [list(x) for x in out]

def gen_brute(maxlen, maxval):
    # direct enumeration of small pair sequences
    out=[]
    for L in range(3, maxlen+1):
        # first column pinned to (0,0) is typical for reduced; but allow (0,0)/(1,1) start
        cols = [(a,b) for a in range(maxval+1) for b in range(maxval+1)]
        # too big to full-product; restrict: build by DFS with light monotone prefilter
        def dfs(prefix):
            if len(prefix)==L:
                out.append(list(prefix)); return
            for (a,b) in cols:
                if len(prefix)==0 and (a,b)!=(0,0): continue
                prefix.append((a,b))
                if len(out)<200000: dfs(prefix)
                prefix.pop()
        if L<=5:
            dfs([])
    return out

def genuine(M):
    try:
        if Lng(M)<3: return False
        if not (reduced(M) and monoT(M)): return False
        if parent(M,0,Lng(M)-1) is None: return False
        if not condV(M): return False
        j0=transJ0(M)
        if adm(M,j0): return False   # non-adm
        tp=Ts(Pred(M))
        if tp is None or tp==ZB: return False   # t1 != 0
        c1=transC1(M); t2=bpHeadT(c1)
        if t2==ZB: return False
        return True
    except Exception:
        return False

def check(hosts, tag, budget, maxhosts):
    t0=time.time(); tot=0
    r0=0; r0bad=[]
    rc1host=0; rc1host_bad=[]
    rhost=0; rhost_bad=[]
    sharp=0; sharp_bad=[]     # RN(c1)[1] == entry M 1 (j0+1)
    bridge=0; bridge_bad=[]   # entry M 1 (j0+1) == entry M 1 (Lng-1)
    widappM=0                 # widening premises hold on M (j1>1, Admpos, t1!=0)
    Sred=0; Smono=0; Swid=0   # terminal slice S properties
    depths=[]
    seen=set()
    for M in hosts:
        if time.time()-t0>budget or tot>=maxhosts: break
        tM=tuple(M)
        if tM in seen: continue
        seen.add(tM)
        if not genuine(M): continue
        tot+=1
        j1=transJ1(M); j0=transJ0(M); jm1=transJm1(M)
        RHS=entry(M,1,j1)
        c1=transC1(M)
        rnc1=RightNodes(c1)
        LHS = rnc1[1] if len(rnc1)>=2 else None
        if LHS==RHS: r0+=1
        else: r0bad.append((rm.fmt(M),LHS,RHS))
        # host Trans
        TM=Ts(M)
        rnTM=RightNodes(TM) if TM is not None else []
        hostRN1 = rnTM[1] if len(rnTM)>=2 else None
        if LHS is not None and hostRN1==LHS: rc1host+=1
        else: rc1host_bad.append((rm.fmt(M),LHS,hostRN1))
        if hostRN1==RHS: rhost+=1
        else: rhost_bad.append((rm.fmt(M),hostRN1,RHS))
        # sharpened + bridge
        if j0+1<=Lng(M)-1:
            e=entry(M,1,j0+1)
            if LHS==e: sharp+=1
            else: sharp_bad.append((rm.fmt(M),LHS,e))
            if e==RHS: bridge+=1
            else: bridge_bad.append((rm.fmt(M),e,RHS))
        # widening premises on M
        if Lng(M)-1>1 and jm1>0 and (Ts(Pred(M)) not in (None,ZB)): widappM+=1
        # terminal slice
        S=seg(M,jm1,Lng(M)-2)
        if reduced(S): Sred+=1
        if monoT(S): Smono+=1
        if reduced(S) and monoT(S) and Lng(S)-1>1 and transJm1(S)>0 and Ts(Pred(S)) not in (None,ZB):
            Swid+=1
    print(f"[{tag}] genuine hosts tot={tot}")
    print(f"  R0  RN(c1)[1]==entryM1 j1      : {r0}/{tot}   bad={len(r0bad)}")
    for b in r0bad[:4]: print("     R0 CEX",b)
    print(f"  Rc1host RN(c1)[1]==RN(TransM)[1]: {rc1host}/{tot}  bad={len(rc1host_bad)}")
    for b in rc1host_bad[:4]: print("     Rc1host CEX",b)
    print(f"  Rhost RN(TransM)[1]==entryM1 j1 : {rhost}/{tot}  bad={len(rhost_bad)}")
    for b in rhost_bad[:4]: print("     Rhost CEX",b)
    print(f"  sharp RN(c1)[1]==entryM1(j0+1)  : {sharp}/{tot}  bad={len(sharp_bad)}")
    for b in sharp_bad[:4]: print("     sharp CEX",b)
    print(f"  bridge entryM1(j0+1)==entryM1 j1: {bridge}/{tot}  bad={len(bridge_bad)}")
    for b in bridge_bad[:4]: print("     bridge CEX",b)
    print(f"  widen premises on M hold        : {widappM}/{tot}")
    print(f"  terminal S: reduced={Sred} mono={Smono} widenable={Swid}  /{tot}")

if __name__=='__main__':
    ml = int(sys.argv[1]) if len(sys.argv)>1 else 10
    print("=== oper-generated deep ===", flush=True)
    check(gen_oper(ml,5,3,4000), "oper", budget=100, maxhosts=500)
    print("=== brute straddle ===", flush=True)
    check(gen_straddle(ml,4,4,3000), "straddle", budget=100, maxhosts=500)
    print("=== brute direct ===", flush=True)
    check(gen_brute(5,4), "brute", budget=60, maxhosts=500)
