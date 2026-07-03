#!/usr/bin/env python3
"""Filter the §8.6 6028-site FAIL hosts by yaBMS is_standard, to confirm the
nested-regime failures are GENUINE reachable standard-form pair sequences
(ST_PS), not model artifacts of the reduced∩monoT proxy.

Also report, for the standard FAIL hosts: condition (I/III/V?), t2 shape, and the
isolated [0]-orbit of the marked principal D_v(t2 + D_{m1j1} 0).
"""
import sys
sys.path.insert(0, "/home/koteitan/proofs/pss-proof/python")
sys.path.insert(0, "/home/koteitan/proofs/pss-proof/git/python")
import trans_model as TM
import red_model as rm
from red_model import Lng, entry, monoT, parent, is_standard, fmt
import buchholz as B

def tm_to_buc(t):
    return [('D', p[1], tm_to_buc(p[2])) for p in t[1]]
def fmtbuc(a): return B.fmt(a)

def iter_peel_86(u, tprime_buc, w, maxk=60):
    body=tprime_buc+[('D',w,[])]; host=[('D',u,body)]
    if not B.in_TB(host): return ('not_TB',None,None)
    want=[('D',u,tprime_buc)]; cur=host; orbit=[fmtbuc(cur)]
    for k in range(1,maxk+1):
        cur=B.bracket(cur,B.ZERO); orbit.append(fmtbuc(cur))
        if cur==want: return ('ok',k,orbit)
        if cur==[]: return ('hit0',None,orbit)
    return ('nofix',None,orbit)

def gen_pairseqs(maxlen, maxval):
    seqs=[]
    def rec(cur):
        if len(cur)>=2: seqs.append(list(cur))
        if len(cur)>=maxlen: return
        for a in range(0,maxval+1):
            for b in range(0,a+1):
                cur.append((a,b)); rec(cur); cur.pop()
    rec([(0,0)])
    return seqs

def main():
    seqs=gen_pairseqs(maxlen=5, maxval=2)  # smaller, since yaBMS calls are slow
    std_fail=[]; std_ok=[]; nonstd_fail=0; tested=0
    for M in seqs:
        if Lng(M)<2 or not TM.reduced(M) or not monoT(M): continue
        j1=Lng(M)-1; jp=parent(M,0,j1)
        t1=TM.Trans(TM.Pred(M))
        if t1==TM.ZB: continue
        cI=TM.condI(M); cIII=TM.condIII(M); cV=TM.condV(M)
        if not (cI or cIII or cV): continue
        c1=TM.Mark(TM.Pred(M), TM.Adm(M,jp))
        v=TM.bpHeadV(c1); t2=TM.bpHeadT(c1); t2b=tm_to_buc(t2)
        m1j1=entry(M,1,j1)
        tag,k,orbit=iter_peel_86(v,t2b,m1j1)
        tested+=1
        if tag=='ok':
            continue
        # FAIL in isolation -> check standardness
        try:
            std=is_standard(M)
        except Exception as e:
            std=None
        if std:
            std_fail.append((M,v,t2b,m1j1,tag,orbit, 'I' if cI else 'III' if cIII else 'V'))
        elif std is False:
            nonstd_fail+=1
    print(f"tested I/III/V hosts: {tested}")
    print(f"isolated-FAIL & STANDARD: {len(std_fail)}")
    print(f"isolated-FAIL & NON-standard: {nonstd_fail}")
    print()
    for r in std_fail[:25]:
        M,v,t2b,m1j1,tag,orbit,cond=r
        print(f"  STD-FAIL cond={cond} M={fmt(M)}  marked=D_{v}({fmtbuc(t2b)} + D_{m1j1} 0)")
        print(f"     [0]-orbit: {' -> '.join(orbit[:6])}{' ...' if len(orbit)>6 else ''}   ({tag})")
        print(f"     want D_{v}({fmtbuc(t2b)})")

if __name__=="__main__":
    main()
