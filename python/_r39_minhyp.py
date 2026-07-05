import sys, time, itertools, random
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt-b1/python')
from red_model import Lng, monoT, zeroT, P, seg
from trans_model import reduced
def multiT(M): return (not zeroT(M)) and (not monoT(M))
def Pcut(M):
    comps=P(M); return Lng(M)-Lng(comps[-1])
def is_prefix(a,b): return len(a)<=len(b) and b[:len(a)]==a
# brute enumerate ALL reduced multiT pairseqs up to Lng L over small values -> test pcompPrefix
rng=random.Random(0); tot=0; ok=0; fails=[]
vals=range(0,4)
for L in range(2,7):
    cols=list(itertools.product(vals,vals))
    # random sample of sequences of length L
    for _ in range(40000):
        M=[random.choice(cols) for _ in range(L)]
        if not reduced(M): continue
        if not multiT(M): continue
        c=Pcut(M); bJ=seg(M,c,Lng(M)-1)
        if bJ==[(0,0)]: continue
        comps=P(M)
        if len(comps)<2: continue
        bJm1=comps[-2]; tot+=1
        if is_prefix(bJ,bJm1): ok+=1
        else: fails.append((M,bJ,bJm1))
        if len(fails)>=5: break
    if len(fails)>=5: break
print("reduced-multiT (NOT nec. ST_PS): pcompPrefix %d/%d"%(ok,tot))
for M,bJ,bJm1 in fails[:5]:
    print("  FAIL last=%s 2nd=%s M=%s"%(bJ,bJm1,M))
