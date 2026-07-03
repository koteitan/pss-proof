import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt2/python')
from trans_model import Trans, Pred, reduced, PB, bpHeadT, ZB, condV
from red_model import Pcut, Lng, oper

def spineLeaf(T):
    h = bpHeadT(T); pb = PB(h)
    return bpHeadT(pb[-1]) if pb else ZB

def predpow(M, k):
    for _ in range(k): M = Pred(M)
    return M

def gen_base(maxlen=4, maxv=2):
    pairs = [(a, b) for a in range(maxv+1) for b in range(maxv+1)]
    for L in range(2, maxlen+1):
        for seq in itertools.product(pairs, repeat=L):
            yield list(seq)

# surgC context: X = oper(M, n+1), Y = oper(M, n).  Test spinelaw on X.
rows = []
for M in gen_base(4, 2):
    try:
        if not reduced(M): continue
    except Exception: continue
    for n in range(1, 4):
        try:
            Y = oper(M, n); X = oper(M, n+1)
            if not (reduced(Y) and reduced(X)): continue
            w = Pcut(X)
            base = predpow(X, w)
            lhs = spineLeaf(Trans(X))
            rhs = bpHeadT(Trans(base))
            rhsY = bpHeadT(Trans(Y))
            cV = condV(X)
            rows.append((base == Y, lhs == rhs, lhs == rhsY, cV, M, n, w))
        except Exception:
            continue

tot = len(rows)
baseY = sum(1 for r in rows if r[0])
lawok = sum(1 for r in rows if r[1])
lawbad = [r for r in rows if not r[1]]
print(f"surgC-context (X=oper(M,n+1), Y=oper(M,n)):  cases={tot}")
print(f"  (Pred^Pcut X)==Y : {baseY}/{tot}")
print(f"  spinelaw lhs==rhs(base): {lawok}/{tot}")
# split by condV
for flag in (True, False):
    sub = [r for r in rows if r[3]==flag]
    if sub:
        okc = sum(1 for r in sub if r[1])
        print(f"  condV={flag}: {okc}/{len(sub)} spinelaw-ok")
print("  --- first 8 spinelaw failures (with condV flag) ---")
for r in lawbad[:8]:
    print("   ", "condV="+str(r[3]), "M=",r[4],"n=",r[5],"Pcut=",r[6], "baseEqY=",r[0])
