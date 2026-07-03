#!/usr/bin/env python3
# r26-WRAPFIX validation (unbuffered; lazy bounded straddle enumeration).
#  (A) reach-conditioned KER: does le0 H q c kill all UNconditioned-KER CEX?
#  (B) reach-conditioned DEADM peel under le0 H q c.
#  (C) nf3x consumer reachability on non-adm condV hosts:
#          le0 M (transJ0 M) (Lng M-1)  [DEADM1 col] and
#          le0 M (transJ0 M) (Lng M-2)  [DEADM2 col].
# Straddle-aware: oper-pool AND lazy brute-force (capped host count).
import sys, time, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import (Lng, entry, monoT, reduced, seg, parent, leR, Adm, adm,
                       oper, diagSeq, marked, le0, nadm)
import red_model as rm
from trans_model import Trans, bpHeadT, Dpt, ZB

def pr(*a): print(*a); sys.stdout.flush()

def Ts(M):
    try: return Trans(M)
    except Exception: return None

def transJ0(M): return parent(M, 0, Lng(M)-1)

def gen_oper(maxlen, maxn, maxseed, cap):
    seen=set(); frontier=[]
    for u in range(maxseed):
        for v in range(u, u+maxseed+2):
            M=tuple(diagSeq(u,v))
            if M not in seen: seen.add(M); frontier.append(list(M))
    pool=list(frontier)
    while frontier and len(pool)<cap:
        nxt=[]
        for M in frontier:
            if Lng(M)<=1: continue
            for n in range(1, maxn+1):
                N=oper(M,n)
                if Lng(N)>maxlen: continue
                t=tuple(N)
                if t not in seen: seen.add(t); nxt.append(N); pool.append(N)
                if len(pool)>=cap: break
            if len(pool)>=cap: break
        frontier=nxt
    return pool

def gen_brute_iter(maxlen, maxval):
    cells=[(a,b) for a in range(maxval+1) for b in range(maxval+1)]
    for L in range(2, maxlen+1):
        for M in itertools.product(cells, repeat=L):
            yield list(M)

def probeKER(hosts, budget, tag):
    unc_ok=unc_bad=rc_ok=rc_bad=0; unc_bad_ex=[]; rc_bad_ex=[]
    t0=time.time(); seen=0
    for H in hosts:
        if time.time()-t0>budget: break
        if not (reduced(H) and monoT(H)): continue
        seen+=1; n=Lng(H)
        for q in range(n):
            am=Adm(H,q)
            if not marked(H,am): continue
            for c in range(q+1,n):
                TSa=Ts(seg(H,am,c)); TSq=Ts(seg(H,q,c))
                if TSa is None or TSq is None: continue
                holds=(bpHeadT(TSa)==bpHeadT(TSq)); reach=leR(H,0,q,c)
                if holds: unc_ok+=1
                else:
                    unc_bad+=1
                    if len(unc_bad_ex)<6: unc_bad_ex.append((rm.fmt(H),q,c,am,reach))
                if reach:
                    if holds: rc_ok+=1
                    else:
                        rc_bad+=1
                        if len(rc_bad_ex)<6: rc_bad_ex.append((rm.fmt(H),q,c,am))
    pr(f"  [A:{tag}] hosts_seen={seen}  KER unc ok={unc_ok} bad={unc_bad} | "
       f"reach-cond ok={rc_ok} bad={rc_bad}")
    for e in unc_bad_ex: pr(f"      UNC-CEX H={e[0]} q={e[1]} c={e[2]} Adm={e[3]} le0(q,c)={e[4]}")
    for e in rc_bad_ex: pr(f"      RC-CEX  H={e[0]} q={e[1]} c={e[2]} Adm={e[3]}")
    return rc_bad

def probeDEADM(hosts, budget, tag):
    ok=bad=0; bad_ex=[]; t0=time.time()
    for H in hosts:
        if time.time()-t0>budget: break
        if not (reduced(H) and monoT(H)): continue
        n=Lng(H)
        for q in range(1,n):
            if adm(H,q): continue
            am=Adm(H,q)
            for c in range(q+1,n):
                if not leR(H,0,q,c): continue
                TSq=Ts(seg(H,q,c)); TSa=Ts(seg(H,am,c))
                if TSq is None or TSa is None: continue
                want=Dpt(entry(H,1,q), bpHeadT(TSa))
                if TSq==want: ok+=1
                else:
                    bad+=1
                    if len(bad_ex)<8: bad_ex.append((rm.fmt(H),q,c,am))
    pr(f"  [B:{tag}] DEADM reach-cond peel ok={ok} bad={bad}")
    for e in bad_ex: pr(f"      DEADM-CEX H={e[0]} q={e[1]} c={e[2]} Adm={e[3]}")
    return bad

def probeNF3X(hosts, budget, tag):
    tot=r1_ok=r1_bad=r2_ok=r2_bad=0; r1ex=[]; r2ex=[]; t0=time.time()
    for M in hosts:
        if time.time()-t0>budget: break
        if not (reduced(M) and monoT(M)): continue
        n=Lng(M)
        if n<4: continue
        if entry(M,1,n-1)<=0: continue        # transCondV: entry1(last)>0
        j0=transJ0(M)
        if j0 is None: continue
        if adm(M,j0): continue                 # non-adm condV
        if not (j0 < n-2): continue            # rng: transJ0+1 < Lng-1
        tot+=1
        if leR(M,0,j0,n-1): r1_ok+=1
        else:
            r1_bad+=1
            if len(r1ex)<8: r1ex.append((rm.fmt(M),j0,n-1))
        if leR(M,0,j0,n-2): r2_ok+=1
        else:
            r2_bad+=1
            if len(r2ex)<8: r2ex.append((rm.fmt(M),j0,n-2))
    pr(f"  [C:{tag}] nf3x nonadm-condV hosts={tot}  "
       f"reach(Lng-1) ok={r1_ok} bad={r1_bad} | reach(Lng-2) ok={r2_ok} bad={r2_bad}")
    for e in r1ex: pr(f"      NOREACH1 M={e[0]} j0={e[1]} c={e[2]}")
    for e in r2ex: pr(f"      NOREACH2 M={e[0]} j0={e[1]} c={e[2]}")
    return r1_bad+r2_bad

def checkCEX():
    H=[(0,0),(1,1),(2,2),(1,0)]
    pr(f"[CEX] H={rm.fmt(H)} reduced={reduced(H)} monoT={monoT(H)} "
       f"adm(1)={adm(H,1)} le0(1,3)={le0(H,1,3)} (guard must be False)")

if __name__=='__main__':
    checkCEX()
    op=gen_oper(12,4,4,6000)
    pr(f"oper pool={len(op)}")
    pr("===== OPER =====")
    b1=probeKER(op,90,"oper"); b2=probeDEADM(op,90,"oper"); b3=probeNF3X(op,60,"oper")
    pr("===== BRUTE (lazy, len<=7 val<=2) =====")
    b4=probeKER(gen_brute_iter(7,2),140,"brute")
    b5=probeDEADM(gen_brute_iter(7,2),140,"brute")
    b6=probeNF3X(gen_brute_iter(7,2),140,"brute")
    pr(f"TOTALS bad: A={b1+b4} B={b2+b5} C={b3+b6}")
