import sys, itertools
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import Lng, entry, monoT, zeroT, le0

"""ROUND 8 -- does monoT(M) imply le0(M,0,r) for EVERY r<Lng(M) (not just the
endpoint r=Lng(M)-1, which is monoT's own definition)?  If TRUE in general this
would give a very cheap route to `cut` in m_8_5_Pcut_of_le0_cut (reach any
interior parent index par0 from Pcut(N), not just Lng(N)-1).  Brute force over
ALL pairseqs up to a small size/value bound (no regime filter -- generic
claim about le0/monoT alone, from pss_defs.thy semantics)."""

def gen(maxlen=6, maxv=3):
    pairs=[(a,b) for a in range(maxv+1) for b in range(maxv+1)]
    for L in range(1,maxlen+1):
        for s in itertools.product(pairs, repeat=L):
            yield list(s)

def main():
    total=0; fails=[]
    for M in gen(6,2):
        if Lng(M)<2: continue
        if not monoT(M): continue
        total+=1
        for r in range(Lng(M)):
            if not le0(M,0,r):
                fails.append((tuple(M),r))
    print(f"monoT hosts tested: {total}")
    print(f"counterexamples (monoT but 0 does not reach some r): {len(fails)}")
    for f in fails[:15]:
        print("  ", f)

if __name__=='__main__':
    main()
