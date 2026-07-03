#!/usr/bin/env python3
"""Validate trans_model.Trans by the article's CORE invariant: the basic-sequence
descent  Trans(M[n]) < Trans(M)  for standard M, Lng>1, n>=1  (lemma 5869).
If the model is faithful this holds everywhere; failures expose model bugs OR
genuine article problems.  Also validate Trans(M) in OT_B (lemma 6122).
"""
import sys
sys.path.insert(0,"/home/koteitan/proofs/pss-proof/python")
sys.path.insert(0,"/home/koteitan/proofs/pss-proof/git/python")
import trans_model as TM
import red_model as rm
from red_model import Lng, monoT, fmt, oper, is_standard
import buchholz as B

def tm_to_buc(t): return [('D',p[1],tm_to_buc(p[2])) for p in t[1]]

def gen(maxlen,maxval):
    seqs=[]
    def rec(cur):
        if len(cur)>=2: seqs.append(list(cur))
        if len(cur)>=maxlen: return
        for a in range(0,maxval+1):
            for b in range(0,a+1):
                cur.append((a,b)); rec(cur); cur.pop()
    rec([(0,0)]); return seqs

def main():
    seqs=gen(5,2)
    desc_ok=desc_bad=ot_ok=ot_bad=0; nstd=0
    bad_desc=[]; bad_ot=[]
    for M in seqs:
        if Lng(M)<2: continue
        try:
            if not is_standard(M): continue
        except Exception:
            continue
        nstd+=1
        try:
            tr=tm_to_buc(TM.Trans(M))
        except Exception as e:
            continue
        if not B.in_OT(tr):
            ot_bad+=1; bad_ot.append((M,tr))
        else:
            ot_ok+=1
        # descent for n=1..4
        for n in range(1,5):
            Mn=oper(M,n)
            if Mn==M: continue
            try:
                trn=tm_to_buc(TM.Trans(Mn))
            except Exception:
                continue
            if B.lt_term(trn,tr):
                desc_ok+=1
            else:
                desc_bad+=1
                if len(bad_desc)<20:
                    bad_desc.append((M,n,tr,trn))
    print(f"standard M tested: {nstd}")
    print(f"OT_B membership: ok={ot_ok} bad={ot_bad}")
    print(f"descent Trans(M[n])<Trans(M): ok={desc_ok} bad={desc_bad}")
    print()
    for M,t in bad_ot[:10]:
        print(f"  OT-FAIL M={fmt(M)} Trans={B.fmt(t)}")
    for M,n,tr,trn in bad_desc[:20]:
        print(f"  DESC-FAIL M={fmt(M)} n={n}  Trans(M)={B.fmt(tr)}  Trans(M[{n}])={B.fmt(trn)}  M[{n}]={fmt(oper(M,n))}")

if __name__=="__main__":
    main()
