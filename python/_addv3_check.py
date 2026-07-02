import sys, itertools
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/git/python')
from trans_model import Trans, Pred, condI, condIII, condV, condVI
from red_model import Lng, entry, parent, reduced, monoT, zeroT

def multBT(t, n):
    return ('T', t[1] * n)   # n copies of principal list; 0B = ('T',[])

def gen(maxlen, maxval):
    pairs = [(a,b) for a in range(maxval+1) for b in range(maxval+1)]
    seqs=[]
    for nn in range(3, maxlen+1):
        for tup in itertools.product(pairs, repeat=nn):
            M=list(tup)
            seqs.append(M)
    return seqs

def is_target(M):
    if Lng(M) < 3: return False
    if Lng(M) - 1 <= 1: return False     # j1 = Lng M -1 > 1  i.e. Lng>=3
    if not reduced(M): return False
    if not monoT(M): return False
    # transCondI
    j1 = Lng(M)-1
    if not condI(M): return False
    # j0 = 0
    if parent(M,0,j1) != 0: return False
    return True

cnt=0; fails=[]
for M in gen(4, 2):
    if not is_target(M): continue
    cnt+=1
    Q = Pred(M)
    try:
        tQ = Trans(Q)
    except Exception as e:
        fails.append((M,'Trans(Q) err',str(e))); continue
    if tQ == ('T',[]):
        fails.append((M,'Trans(Q)=0B',tQ)); continue
    for n in range(2,6):
        N = Q*n
        try:
            lhs = Trans(N)
        except Exception as e:
            fails.append((M,n,'Trans(N) err',str(e))); continue
        rhs = multBT(tQ, n)
        if lhs != rhs:
            fails.append((M,n,lhs,rhs))
print("targets matched:", cnt)
print("fails:", len(fails))
for f in fails[:20]:
    print("  FAIL", f)
