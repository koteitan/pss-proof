"""Methodology-corrected re-audit of the §6.8 case-A TrMax equality
    TrMax(seg (N[n]) a b) == TrMax(seg N a (Lng N-1))
over STANDARD N (yaBMS is_standard filter) with deep enumeration (length<=5).

Lesson (2026-05-27): the earlier audits (slice_trmaxeq_audit*.py) used neither a
standardness filter nor depth>=KMAX6, and reported false "1632/1632"/"141/141"
artifacts.  This script ALWAYS filters is_standard and enumerates to length 5.

NB: this BARE check does NOT reproduce the full case-A guard
(j0' < j0N < j1', Lng N-2 <= j1', the (A) sub-condition j0N-j0' <= TrMax N').
Result: 367/3042 mismatches => the bare equality is NON-universal on standard
inputs; the green brick TrMax_seg_oper_d0zero_eq's hypotheses are essential and
the boundary-stop discharge for case A is still OPEN.  A faithful re-derivation
must reproduce the exact guard here before any new empirical claim.
"""
import itertools, red_model as R

def gen(maxlen, maxval):
    for L in range(2, maxlen+1):
        for c in itertools.product(range(maxval+1), repeat=2*L):
            M=[(c[2*j],c[2*j+1]) for j in range(L)]
            if M[0]==(0,0): yield M

def audit(maxlen=5, maxval=4):
    std=0; checked=0; mism=[]
    for N in gen(maxlen, maxval):
        try:
            if not R.is_standard(N): continue
        except Exception: continue
        std+=1
        if R.Lng(N)<2 or R.entry(N,1,R.Lng(N)-1)!=0: continue  # d0zero
        for n in (1,2,3):
            Mn=R.oper(N,n); Lm=R.Lng(Mn)
            for a in range(0,Lm-1):
                for b in range(a+1,Lm):
                    if not R.leR(Mn,0,a,b): continue
                    if a>=R.Lng(N): continue
                    lhs=R.TrMax(R.seg(Mn,a,b)); rhs=R.TrMax(R.seg(N,a,R.Lng(N)-1))
                    checked+=1
                    if lhs!=rhs: mism.append((R.fmt(N),n,a,b,lhs,rhs))
    print(f"standard={std} checked={checked} mismatches={len(mism)}")
    for m in mism[:10]: print("  MISMATCH", m)

if __name__=="__main__":
    audit()
