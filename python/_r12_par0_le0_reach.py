import sys, itertools as it, time
sys.path.insert(0,'/home/koteitan/proofs/pss-proof/wt2/python')
from red_model import Lng,entry,multiT,hasParent,parent,Pcut,le0

"""ROUND 12, Route 2: refine _r12_par0_ge_pcut.py's 100%-confirmed
'Pcut(N)<=par0' into the MECHANISM needed to prove it in Isabelle via Pcut's
own minimality: does `le0(N,par0,Lng(N)-1)` hold (par0 itself is a valid
le0-connector to N's own last index -- so Pcut(N), being the LEAST such
connector, is automatically <= par0)?  Test this REACHABILITY fact directly
(not just the derived number inequality)."""

def gen(maxlen=6, maxv=3):
    pairs=[(a,b) for a in range(maxv+1) for b in range(maxv+1)]
    for L in range(2,maxlen+1):
        for s in it.product(pairs, repeat=L):
            yield list(s)

def main(timelimit=120, maxlen=6, maxv=3):
    t0=time.time(); tested=0; ok=0; bad=[]
    trivial=0
    for N in gen(maxlen,maxv):
        if time.time()-t0>timelimit: break
        if not multiT(N): continue
        try:
            pc = Pcut(N)
        except Exception:
            continue
        for col in [(a,b) for a in range(maxv+2) for b in range(maxv+2)]:
            if col[0]==0: continue
            Ncur = N+[col]
            last = Lng(Ncur)-1
            if not hasParent(Ncur,0,last): continue
            par0 = parent(Ncur,0,last)
            tested += 1
            if par0 == Lng(N)-1:
                trivial += 1
                ok += 1  # trivially reflexive
                continue
            reach = le0(N,par0,Lng(N)-1)
            if reach: ok += 1
            else: bad.append((tuple(N),col,pc,par0,Lng(N)-1))
    return tested, ok, trivial, bad

if __name__=='__main__':
    tl = int(sys.argv[1]) if len(sys.argv)>1 else 120
    tested, ok, trivial, bad = main(tl, 6, 3)
    print(f"tested={tested}, le0(N,par0,Lng(N)-1) [or par0==Lng(N)-1 trivial]: "
          f"{ok}/{tested} ({100.0*ok/max(1,tested):.2f}%)  trivial-cases={trivial}")
    for b in bad[:15]:
        print("  BAD:", b)
