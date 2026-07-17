import sys, itertools
sys.path.insert(0, 'python')
import trans_model as tm
from trans_model import Lng, entry, Pred, Adm, Mark, bpHeadT, Dpt, ZB, condVI, adm, reduced
import red_model as rm

def parent0(M, j1): return tm.parent(M, 0, j1)
def monoT(M): return tm.monoT(M)

def diagSeq(a, b): return [(j, j) for j in range(a, b+1)]

fires = 0; fails = 0
# diagSeq hosts
hosts = [diagSeq(u, v) for u in range(0,4) for v in range(u+2, u+6)]
# also a few crafted reduced-mono hosts scanned
for M in hosts:
    if Lng(M) < 3: continue
    if not reduced(M): continue
    if not monoT(M): continue
    if not condVI(M): continue
    j1 = Lng(M)-1
    jp = parent0(M, j1)          # transJ0
    if adm(M, jp): continue       # need NON-adm
    jm1 = Adm(M, jp)              # transJm1
    # our claim
    predC1 = Dpt(entry(M,1,jm1), Dpt(entry(M,1,jp), ZB))
    predT2 = Dpt(entry(M,1,jp), ZB)
    c1 = Mark(Pred(M), jm1)
    t2 = bpHeadT(c1)
    ok = (c1 == predC1) and (t2 == predT2)
    fires += 1
    if not ok:
        fails += 1
        print("FAIL", M, "c1=", c1, "pred=", predC1, "t2=", t2, "predT2=", predT2)
print(f"diagSeq hosts: fired={fires} fails={fails}")

# brute-force small standard forms with components up to 8 (per memo: CEX hide at 6-9)
fires2=0; fails2=0
def gen(n, maxc):
    for rows in itertools.product(range(maxc+1), repeat=2*n):
        M=[(rows[2*i],rows[2*i+1]) for i in range(n)]
        yield M
scanned=0
for n in (3,4):
    for M in gen(n, 5):
        scanned+=1
        try:
            if not reduced(M): continue
            if not monoT(M): continue
            if Lng(M)<3: continue
            if not condVI(M): continue
            j1=Lng(M)-1; jp=parent0(M,j1)
            if adm(M,jp): continue
            jm1=Adm(M,jp)
            predC1=Dpt(entry(M,1,jm1),Dpt(entry(M,1,jp),ZB))
            predT2=Dpt(entry(M,1,jp),ZB)
            c1=Mark(Pred(M),jm1); t2=bpHeadT(c1)
            fires2+=1
            if not (c1==predC1 and t2==predT2):
                fails2+=1
                if fails2<=5: print("BRUTE FAIL",M,"c1=",c1,"pred=",predC1)
        except Exception as e:
            pass
print(f"brute n=3,4 comp<=5: scanned={scanned} fired={fires2} fails={fails2}")
