import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt2/python')
from trans_model import Trans, Pred, reduced, PB, bpHeadT, ZB, Dpt, addBT
from red_model import Pcut, Lng

def spineLeaf(T):
    h = bpHeadT(T); pb = PB(h)
    return bpHeadT(pb[-1]) if pb else ZB

def predpow(M, k):
    for _ in range(k): M = Pred(M)
    return M

# base spine-shape: Trans X = Dpt e10 (t2 +B Dpt vm1 (spineLeaf(Trans X)))
# i.e. head of Trans X is a single Dpt; its body's last P-block is Dpt vm1 (leaf),
# where leaf == spineLeaf(Trans X).
def has_base_shape(TX):
    # TX = ('T',[('D',e10, body)])  single top D
    if len(TX[1]) != 1: return False
    body = TX[1][0][2]                  # the t2 +B Dpt vm1 leaf
    pb = PB(body)
    if not pb: return False
    last = pb[-1]                       # ('T',[('D',vm1, leaf)])
    if len(last[1]) != 1: return False
    leaf = last[1][0][2]
    return leaf == spineLeaf(TX)

def gen(maxlen=4, maxv=2):
    pairs = [(a, b) for a in range(maxv+1) for b in range(maxv+1)]
    for L in range(2, maxlen+1):
        for seq in itertools.product(pairs, repeat=L):
            yield list(seq)

shaped_ok=shaped_bad=unshaped_ok=unshaped_bad=0
sb_fail=[]
for M in gen(4,2):
    try:
        if not reduced(M): continue
        TX = Trans(M)
        w = Pcut(M)
        lhs = spineLeaf(TX)
        rhs = bpHeadT(Trans(predpow(M,w)))
    except Exception:
        continue
    eq = (lhs==rhs)
    if has_base_shape(TX):
        if eq: shaped_ok+=1
        else:
            shaped_bad+=1
            if len(sb_fail)<8: sb_fail.append((M,w,lhs,rhs))
    else:
        if eq: unshaped_ok+=1
        else: unshaped_bad+=1

print("partition by base-spine-shape(Trans X):")
print(f"  SHAPED   : ok={shaped_ok} bad={shaped_bad}")
print(f"  UNSHAPED : ok={unshaped_ok} bad={unshaped_bad}")
print("  --- shaped failures (counterexamples to 'shape => spinelaw') ---")
for M,w,l,r in sb_fail:
    print("   ", M, "Pcut=",w, "lhs=",l, "rhs=",r)
