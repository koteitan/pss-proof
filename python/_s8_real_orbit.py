#!/usr/bin/env python3
"""DEFINITIVE check for the 6014 Pred_oper0 lemma on condition-V STANDARD hosts.

The article's Pred_oper0 (6014) claims: for M monoT, j1>1, NOT condition VI,
Trans(M) an ordinal term, there is k with Trans(M)[0]^k = t_1 (= Trans(Pred(M))).

For condition I/III/V it derives this (6028) by applying §8.6 (末尾単項の零化) to
the marked principal c_2 = D_v(t_2 + D_{m1j1} 0), peeling D_{m1j1} 0 to get D_v t_2,
which (top-level / via [].5) should give Trans(M)[0]^k = s_1 D_v t_2 b_1 = t_1.

We test the REAL claim on the actual Trans(M): does iterating [0] on the WHOLE
Trans(M) ever reach t_1 = Trans(Pred(M))?   This is the article's actual obligation.
Also locate c_2 in Trans(M): TOP-LEVEL (rightmost principal) or NESTED?
"""
import sys
sys.path.insert(0,"/home/koteitan/proofs/pss-proof/python")
sys.path.insert(0,"/home/koteitan/proofs/pss-proof/git/python")
import trans_model as TM
import red_model as rm
from red_model import Lng, entry, monoT, parent, is_standard, fmt
import buchholz as B

def tm_to_buc(t):
    return [('D', p[1], tm_to_buc(p[2])) for p in t[1]]
def fmtbuc(a): return B.fmt(a)

def real_orbit_reaches(transM_buc, t1_buc, maxk=80):
    cur = transM_buc
    if not B.in_TB(cur): return ('transM_not_TB', None)
    orbit=[fmtbuc(cur)]
    for k in range(1,maxk+1):
        cur = B.bracket(cur, B.ZERO)
        orbit.append(fmtbuc(cur))
        if cur == t1_buc: return ('ok', k, orbit)
        if cur == [] and t1_buc != []:
            # passed 0 without hitting t1
            return ('hit0_miss', k, orbit)
    return ('nofix', None, orbit)

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
    seqs=gen_pairseqs(maxlen=5, maxval=2)
    nstd=0; results=[]
    for M in seqs:
        if Lng(M)<3 or not TM.reduced(M) or not monoT(M): continue
        j1=Lng(M)-1
        if j1<=1: continue
        # Pred_oper0 hypotheses: NOT condition VI, Trans(M) ordinal term
        if TM.condVI(M): continue
        try:
            transM = TM.Trans(M)
            t1 = TM.Trans(TM.Pred(M))
        except Exception:
            continue
        if t1==TM.ZB: continue
        # only the condition I/III/V branch (6028) for this focused test
        if not (TM.condI(M) or TM.condIII(M) or TM.condV(M)): continue
        try:
            std = is_standard(M)
        except Exception:
            std = None
        if not std: continue
        nstd+=1
        transM_b = tm_to_buc(transM); t1_b = tm_to_buc(t1)
        tag = real_orbit_reaches(transM_b, t1_b)
        # is c_2 (the rightmost top-level principal of Trans(M)) the marked one?
        # top-level rightmost principal:
        toplvl_rightmost = transM_b[-1] if transM_b else None
        results.append((M, transM_b, t1_b, tag))
    ok=sum(1 for r in results if r[3][0]=='ok')
    miss=[r for r in results if r[3][0]!='ok']
    print(f"condition-I/III/V STANDARD hosts (j1>1, not VI): {nstd}")
    print(f"  REAL Trans(M)[0]^k reaches t_1 (article's actual obligation): {ok}/{len(results)}")
    print(f"  MISSES (article obligation FAILS on real Trans(M)): {len(miss)}")
    print()
    for r in miss[:25]:
        M, tb, t1b, tag = r
        print(f"  MISS M={fmt(M)}")
        print(f"     Trans(M)   = {fmtbuc(tb)}")
        print(f"     t_1=Tr(Pred)= {fmtbuc(t1b)}")
        print(f"     orbit: {' -> '.join(tag[2][:7])}{' ...' if len(tag[2])>7 else ''}  [{tag[0]}]")

if __name__=="__main__":
    main()
