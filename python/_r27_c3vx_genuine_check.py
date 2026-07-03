#!/usr/bin/env python3
"""r27-CONDIII: does the KER de-adm identity hold at the GENUINE (standard)
condIII instances, and does STANDARDNESS eliminate the straddle CEX?

Genuine instances used by vmlx_veM/veL_of_kernel:
  veM-KER at (M, jm2, Lng M-2),  jm2 = parent M 1 (Lng M-1), Adm M jm2 = jm3.
  veL-KER at (L1, jm2, Lng L1-1), L1 = Pred M @ [(entry M 0 (Lng M-1), entry M 1 jm2)].
Also directly check veM/veL themselves.  Run: python3 -u <this>.
"""
import sys, random, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')
from red_model import (Lng, entry, seg, Adm, adm, leR, monoT, reduced, marked,
                       parent, hasParent, is_standard, fmt, Pred, diagSeq)
from trans_model import Trans, bpHeadT, condIII

def pr(*a):
    print(*a); sys.stdout.flush()

def jm2(M): return parent(M, 1, Lng(M)-1)
def jm3(M): return Adm(M, jm2(M))
def sN(M):  return seg(M, jm3(M), Lng(M)-1)
def sNp(M): return seg(M, jm2(M), Lng(M)-1)
def sLp(M): return seg(M, jm2(M), Lng(M)-2) + [(entry(M,0,Lng(M)-1), entry(M,1,jm2(M)))]
def L1(M):  return Pred(M) + [(entry(M,0,Lng(M)-1), entry(M,1,jm2(M)))]

def in_regime(M):
    if Lng(M) < 4: return False
    if not (reduced(M) and monoT(M)): return False
    if not hasParent(M, 1, Lng(M)-1): return False
    if not (1 < Lng(M)-1): return False
    if not condIII(M): return False
    if not (jm2(M) + 1 < Lng(M)-1): return False   # rng
    return True

def gen_condIII_standard(cap=200, cap_iter=200000):
    """diagSeq(0,d)+tail brute force, filter standard condIII regime."""
    hosts, seen, it = [], set(), 0
    for d in range(3, 8):
        base = diagSeq(0, d)
        rng = range(0, d+2)
        for ntail in (2, 3, 4):
            for tail in itertools.product(itertools.product(rng, rng), repeat=ntail):
                it += 1
                if it > cap_iter: return hosts
                M = base + list(tail)
                key = tuple(M)
                if key in seen: continue
                seen.add(key)
                if not monoT(M): continue
                if not in_regime(M): continue
                try:
                    if not is_standard(M): continue
                except Exception: continue
                hosts.append(M)
                if len(hosts) >= cap: return hosts
    return hosts

def check_genuine(hosts):
    tot=veMbad=veLbad=kerMbad=kerLbad=0; deep=0; ntM=ntL=0; cex=[]
    for M in hosts:
        tot += 1
        if Lng(M) >= 9: deep += 1
        j2=jm2(M); j3=jm3(M); n=Lng(M)
        try:
            # veM
            veM_l = bpHeadT(Trans(Pred(sN(M)))); veM_r = bpHeadT(Trans(Pred(sNp(M))))
            if veM_l != veM_r: veMbad+=1; cex.append(('veM',fmt(M)))
            # veL
            Lh=L1(M)
            veL_l = bpHeadT(Trans(seg(Lh, j3, Lng(Lh)-1))); veL_r = bpHeadT(Trans(sLp(M)))
            if veL_l != veL_r: veLbad+=1; cex.append(('veL',fmt(M)))
            # KER at (M, jm2, Lng M-2)
            if j3 < j2: ntM+=1
            kM_l=bpHeadT(Trans(seg(M,j3,n-2))); kM_r=bpHeadT(Trans(seg(M,j2,n-2)))
            if kM_l != kM_r: kerMbad+=1; cex.append(('kerM',fmt(M),'j2',j2,'j3',j3))
            # KER at (L1, jm2, Lng L1-1)
            AjL=Adm(Lh,j2)
            if AjL < j2: ntL+=1
            kL_l=bpHeadT(Trans(seg(Lh,AjL,Lng(Lh)-1))); kL_r=bpHeadT(Trans(seg(Lh,j2,Lng(Lh)-1)))
            if kL_l != kL_r: kerLbad+=1; cex.append(('kerL',fmt(M)))
        except Exception as e:
            continue
    pr(f"  genuine condIII standard hosts: {tot} (deep>=9: {deep})")
    pr(f"    veM {tot-veMbad}/{tot}  veL {tot-veLbad}/{tot}")
    pr(f"    kerM {tot-kerMbad}/{tot} (nontriv {ntM})  kerL {tot-kerLbad}/{tot} (nontriv {ntL})")
    for c in cex[:8]: pr("    CEX:", c)
    return veMbad+veLbad+kerMbad+kerLbad

def check_KER_standard(cap=250, cap_iter=200000):
    """KER over STANDARD reduced-monoT hosts: does standardness kill the straddle CEX?"""
    tot=bad=deep=nt=0; seen=set(); it=0; cex=[]; nhosts=0
    for d in range(4, 8):
        base=diagSeq(0,d); rng=range(0,d+1)
        for tail in itertools.product(itertools.product(rng,rng), repeat=2):
            it+=1
            if it>cap_iter or nhosts>=cap:
                pr(f"  [KER-standard] {tot-bad}/{tot}  hosts {nhosts} deep {deep} nontriv {nt} CEX {bad}")
                for c in cex[:8]: pr("    KER-std CEX:", c)
                return bad
            H=base+list(tail)
            if Lng(H)<9: continue
            key=tuple(H)
            if key in seen: continue
            seen.add(key)
            if not monoT(H) or not reduced(H): continue
            try:
                if not is_standard(H): continue
            except Exception: continue
            nhosts+=1; n=Lng(H)
            for q in range(1,n-1):
                a=Adm(H,q)
                if not marked(H,a): continue
                for c in range(q+1,n):
                    if not leR(H,0,q,c): continue
                    tot+=1
                    if n>=9: deep+=1
                    if a<q: nt+=1
                    try:
                        if bpHeadT(Trans(seg(H,a,c)))!=bpHeadT(Trans(seg(H,q,c))):
                            bad+=1
                            if len(cex)<8: cex.append((fmt(H),'q',q,'c',c,'Adm',a))
                    except Exception: continue
    pr(f"  [KER-standard] {tot-bad}/{tot}  hosts {nhosts} deep {deep} nontriv {nt} CEX {bad}")
    for c in cex[:8]: pr("    KER-std CEX:", c)
    return bad

if __name__ == '__main__':
    random.seed(20270703)
    pr("== KER on STANDARD hosts (does standardness kill the straddle CEX?) ==")
    bstd = check_KER_standard()
    pr("== genuine condIII standard instances (veM/veL/kerM/kerL) ==")
    H = gen_condIII_standard()
    bg = check_genuine(H)
    pr("== SUMMARY ==")
    pr(f"  KER-standard CEX={bstd}   genuine-condIII bad={bg}")
    pr("  VERDICT:", "STANDARD-CLEAN" if (bstd+bg)==0 else "!!! CEX in standard regime !!!")
