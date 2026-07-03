#!/usr/bin/env python3
"""Characterize the §8.7 multiD junction descent residual.

For multiT N in ST_PS with last block drop(Pcut N)N != [(0,0)]:
  Trans(take(Pcut N)N) = Trm as,  Trans(drop(Pcut N)N) = Trm bs
  GOAL: leBT (Trm [hd bs]) (Trm [last as])   i.e. hd bs <=_BP last as
Measure:
  - heads:  hx = head(hd bs), lx = head(last as)
  - relation: hx < lx (strict by head) | hx == lx (then body tiebreak) | hx > lx (FAIL)
  - tie to descending(P N): entry(block J-1) 0/1 vs entry(block J) 0/1
  - confirm hd bs head == entry(drop(Pcut N)N) 1 0  (block J row-1 leftend)
  - relate last as head to block J-1 entries
"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import Lng, entry, monoT, multiT, zeroT, P, Pcut, reduced as rr
from trans_model import Trans, reduced
from fast_pss import diagSeq, oper

ZB=('T',[])
def lessBT(a,b):
    pa,pb=a[1],b[1]
    if not pa: return bool(pb)
    if not pb: return False
    return lessBP(pa[0],pb[0]) or (pa[0]==pb[0] and lessBT(('T',pa[1:]),('T',pb[1:])))
def lessBP(p,q):
    u,a=p[1],p[2]; v,b=q[1],q[2]; return u<v or (u==v and lessBT(a,b))
def leBT(a,b): return lessBT(a,b) or a==b

def gen(ms,mn,ml,r):
    seen=set();fr=[]
    for a in range(ms+1):
        for b in range(a,ms+1):
            s=tuple(diagSeq(a,b))
            if s and s not in seen: seen.add(s);fr.append(list(s))
    for _ in range(r):
        nf=[]
        for M in fr:
            for n in range(1,mn+1):
                Mp=oper(M,n)
                if 1<=Lng(Mp)<=ml:
                    t=tuple(Mp)
                    if t not in seen: seen.add(t);nf.append(Mp)
        fr=nf
        if not fr:break
    return [list(t) for t in seen]

def main():
    Ms=gen(4,4,11,4)
    n=0; goal_ok=0; goal_fail=0
    hx_lt=0; hx_eq=0; hx_gt=0
    head_match=0; head_mismatch=0
    descend_row0_strict=0; descend_row0_eq=0
    fail_ex=[]; eq_detail=[]
    for N in Ms:
        if Lng(N)<2 or not rr(N) or not multiT(N): continue
        pc=Pcut(N)
        A=N[:pc]; Blk=N[pc:]   # take, drop
        if Blk==[(0,0)]: continue
        try: tA=Trans(A); tB=Trans(Blk)
        except: continue
        if tA==ZB or tB==ZB: continue
        as_=tA[1]; bs=tB[1]
        if not as_ or not bs: continue
        n+=1
        hd_bs=bs[0]; last_as=as_[-1]
        hx=hd_bs[1]; lx=last_as[1]
        g=leBT(('T',[hd_bs]),('T',[last_as]))
        if g: goal_ok+=1
        else:
            goal_fail+=1
            if len(fail_ex)<5: fail_ex.append((N,('hx',hx),('lx',lx)))
        if hx<lx: hx_lt+=1
        elif hx==lx: hx_eq+=1
        else: hx_gt+=1
        # head of hd bs vs block J row-1 leftend
        if hx==entry(Blk,1,0): head_match+=1
        else: head_mismatch+=1
        # descending of P N at consecutive blocks J-1,J
        PN=P(N); J=len(PN)-1
        if J>=1:
            bJm1=PN[J-1]; bJ=PN[J]
            r0a=entry(bJm1,0,0); r0b=entry(bJ,0,0)
            r1a=entry(bJm1,1,0); r1b=entry(bJ,1,0)
            if r0a>r0b: descend_row0_strict+=1
            elif r0a==r0b:
                descend_row0_eq+=1
                if hx==lx and len(eq_detail)<5:
                    eq_detail.append((N,('r1a',r1a),('r1b',r1b),('hx',hx),('lx',lx)))
    print(f"multiD junction samples (last block != [(0,0)]): {n}")
    print(f"  GOAL leBT(hd bs, last as): ok={goal_ok} FAIL={goal_fail}")
    print(f"  head relation: hx<lx={hx_lt}  hx==lx={hx_eq}  hx>lx(FAIL)={hx_gt}")
    print(f"  hd-bs head == entry(block J) 1 0 : match={head_match} mismatch={head_mismatch}")
    print(f"  descending(P N) at J-1,J: row0 strict>={descend_row0_strict} row0 eq={descend_row0_eq}")
    if eq_detail:
        print("  EQUAL-head detail (r1a>=r1b expected):")
        for e in eq_detail: print("    ",e)
    if fail_ex:
        print("FAILS:")
        for e in fail_ex: print("   ",e)
    print("RESULT:", "GOAL HOLDS" if goal_fail==0 and n>0 else ("NO SAMPLES" if n==0 else "FAILS"))

if __name__=='__main__': main()
