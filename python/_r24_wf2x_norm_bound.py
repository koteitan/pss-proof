#!/usr/bin/env python3
"""
r24 WFRP2 — is the syntactic norm BOUNDED along lessBP-descending OT chains?

CRUX to test (the task's proposed reduction of wf RPrel to the bounded fragment):
   lessBP b p  &  b,p in OT-principals   ==>   nrmP b <= f(nrmP p)   for some f.
If TRUE, wf RPrel reduces to the finite bounded fragment (wfpx) + this bound.
If FALSE (norm unbounded below a fixed principal), that IS the psi-ordinal
obstruction: {q in OT : q < p} is infinite / norm-unbounded.

nrm mirrors wfpx_nrmT / wfpx_nrmP EXACTLY:
   nrmT(Trm ps) = 1 + sum nrmP ps ;  nrmP(D v b) = 1 + v + nrmT b.
"""
import buchholz as B

def nrmT(a):                       # a = list of principals (a term)
    return 1 + sum(nrmP(p) for p in a)
def nrmP(p):                       # p = ('D', v, b)
    _, v, b = p
    return 1 + int(v) + nrmT(b)

def isOT_princ(p):                 # isOT_BP p  (p a single principal)
    return B.in_OT([p])
def dfree_princ(p):                # dfree_BP p
    return B.in_TB([p])

# ---------------------------------------------------------------------------
# The FIXED principal p = D_1 0 = psi_1(0).
p = B.D(1, B.ZERO)
print("p = D_1 0 ;  isOT:", isOT_princ(p), " dfree:", dfree_princ(p), " nrmP(p) =", nrmP(p))
assert isOT_princ(p) and dfree_princ(p)

# ---------------------------------------------------------------------------
# Witness family  q_n = D_0(nat n) = D_0( 1*n ).   Claim: all in OT, all < p,
# nrmP(q_n) = 2n+2  -> unbounded.
print("\n--- witness family  q_n = D_0(n)  (n = numBT n) ---")
print(f"{'n':>4} {'isOT(q)':>8} {'dfree':>6} {'q<p':>5} {'nrmP(q)':>8}")
ok = True
for n in range(0, 12):
    q = B.D(0, B.nat(n))
    isot = isOT_princ(q)
    df   = dfree_princ(q)
    lt   = B.lt_princ(q, p)
    nn   = nrmP(q)
    ok  &= (isot and df and lt and nn == 2*n + 2)
    print(f"{n:>4} {str(isot):>8} {str(df):>6} {str(lt):>5} {nn:>8}")
print("family all-OT & all<p & nrmP=2n+2 :", ok)
assert ok, "witness family broke"

# ---------------------------------------------------------------------------
# CRUX test: is there ANY bound f(nrmP p) that caps nrmP of everything below p?
# The single-element chains [q_n] already blow past any fixed bound.
maxN = 200
below_norms = [nrmP(B.D(0, B.nat(n))) for n in range(0, maxN)]
print("\nmax nrmP among q_0..q_%d below p (nrmP p=%d): %d  (grows as 2n+2)"
      % (maxN-1, nrmP(p), max(below_norms)))
print("=> NO fixed f(nrmP p) bounds nrmP of the predecessors of p.  CRUX IS FALSE.")

# ---------------------------------------------------------------------------
# Cross-check the SECOND family from the analysis:  b_n = D_0( D_1^n 0 ).
def D1pow(n):
    a = B.ZERO
    for _ in range(n): a = [B.D(1, a)]
    return a
print("\n--- second witness family  b_n = D_0(D_1^n 0) ---")
ok2 = True
for n in range(0, 8):
    b = B.D(0, D1pow(n))
    isot = isOT_princ(b); df = dfree_princ(b); lt = B.lt_princ(b, p)
    ok2 &= (isot and df and lt)
    print(f"n={n}  isOT={isot} dfree={df} b<p={lt}  nrmP={nrmP(B.D(0,D1pow(n)))}")
print("second family all-OT & all<p:", ok2)

# ---------------------------------------------------------------------------
# Independent confirmation: enumerate OT principals of small size, and for
# each fixed principal p check how large nrmP gets among OT-principals < p.
# If the predecessor norm is bounded by any function of nrmP(p) we'd see the
# max stay small; instead it is capped only by our enumeration depth.
print("\n--- brute: for p=D_1 0, count OT-principals q<p by norm (enum depth) ---")
# enumerate terms up to norm K, restricted D_omega-free, indices in {0,1}
def enum_terms(maxnorm, idxs=(0,1)):
    # yield terms (principal lists) with nrmT <= maxnorm
    # principals with nrmP <= maxnorm
    cache_T = {1: [[]]}   # nrmT 1 -> [ [] ]
    # build principals of increasing norm
    def princ_upto(K):
        out = []
        for v in idxs:
            for tn in range(1, K - v):           # nrmP = 1+v+nrmT(b) <= K
                for b in terms_of_norm(tn):
                    out.append(('D', v, b))
        return out
    memoT = {}
    def terms_of_norm(tn):
        if tn in memoT: return memoT[tn]
        res = []
        if tn == 1:
            res = [[]]
        else:
            # Trm ps with 1 + sum nrmP ps = tn ; recursively
            # generate lists of principals summing to tn-1
            target = tn - 1
            princs = all_princ(target)
            res = list(gen_lists(princs, target))
        memoT[tn] = res
        return res
    memoP = {}
    def all_princ(maxP):
        key = maxP
        if key in memoP: return memoP[key]
        out = []
        for v in idxs:
            for tn in range(1, maxP - v + 1):
                if 1 + v + tn <= maxP:
                    for b in terms_of_norm(tn):
                        out.append(('D', v, b))
        memoP[key] = out
        return out
    def gen_lists(princs, target):
        # lists of principals whose nrmP sum == target
        if target == 0:
            yield []
            return
        for pr in princs:
            w = nrmP(pr)
            if w <= target:
                for rest in gen_lists(princs, target - w):
                    yield [pr] + rest
    return terms_of_norm(maxnorm), all_princ(maxnorm)

# simpler brute: just enumerate D_0(t) and D_1(t) principals with small terms t
seen = set()
frontier = [B.ZERO]
maxnorm_below_p = 0
count_below = 0
# BFS over OT terms built from indices {0,1}, bounded norm
import itertools
def gen_ot_terms(max_norm):
    results = []
    # start from principals
    princ_pool = []
    # iterative deepening by norm
    terms_by_norm = {1: [B.ZERO]}
    for K in range(2, max_norm+1):
        bucket = []
        # principals of norm < K from smaller terms
        princ = []
        for v in (0,1):
            for tn in range(1, K):
                for b in terms_by_norm.get(tn, []):
                    pp = ('D', v, b)
                    if B.in_OT([pp]) and B.in_TB([pp]):
                        princ.append((nrmP(pp), pp))
        # build terms of norm K as weakly-decreasing lists of principals summing to K-1
        # (only need principals, since predecessor test is on principals)
        terms_by_norm[K] = []
        # collect principal-terms (single principal) of norm K
        for wn, pp in princ:
            if 1 + wn == K:
                terms_by_norm[K].append([pp])
        # also record for use as sub-terms b
    return terms_by_norm

tb = gen_ot_terms(14)
allpr = []
for K, lst in tb.items():
    for t in lst:
        if len(t) == 1:
            allpr.append(t[0])
below = [pp for pp in allpr if B.in_OT([pp]) and B.in_TB([pp]) and B.lt_princ(pp, p)]
if below:
    print("enum depth norm<=14, indices{0,1}: #OT-principals q<p =", len(below),
          " max nrmP =", max(nrmP(pp) for pp in below))
print("(max grows with enumeration depth, not with nrmP(p)=%d)" % nrmP(p))

print("\nCONCLUSION: norm is NOT bounded below a fixed OT principal p.")
print("The predecessor set {q in OT : q < p} is INFINITE (order type = psi_1(0)).")
print("=> the bounded-fragment reduction FAILS; this is the psi-ordinal obstruction.")
