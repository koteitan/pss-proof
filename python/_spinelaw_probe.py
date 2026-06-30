import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt2/python')
from trans_model import Trans, Pred, reduced, PB, bpHeadT, ZB
from red_model import Pcut, Lng

def spineLeaf(T):
    h = bpHeadT(T)
    pb = PB(h)
    if not pb:
        return ZB
    return bpHeadT(pb[-1])

def predpow(M, k):
    for _ in range(k):
        M = Pred(M)
    return M

# enumerate small pairseqs (rows of (a,b)), filter reduced (RT_PS)
def gen(maxlen=4, maxv=3):
    pairs = [(a, b) for a in range(maxv+1) for b in range(maxv+1)]
    for L in range(2, maxlen+1):
        for seq in itertools.product(pairs, repeat=L):
            M = list(seq)
            yield M

ok = bad = total = 0
fails = []
for M in gen(maxlen=4, maxv=2):
    try:
        if not reduced(M):
            continue
    except Exception:
        continue
    total += 1
    try:
        w = Pcut(M)
        lhs = spineLeaf(Trans(M))
        rhs = bpHeadT(Trans(predpow(M, w)))
    except Exception as e:
        continue
    if lhs == rhs:
        ok += 1
    else:
        bad += 1
        if len(fails) < 8:
            fails.append((M, w, lhs, rhs))

print(f"SPINELAW  reduced-tested={total}  ok={ok}  bad={bad}")
for M, w, lhs, rhs in fails:
    print("  FAIL", M, "Pcut=", w)
    print("    lhs=", lhs)
    print("    rhs=", rhs)
