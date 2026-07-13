#!/usr/bin/env python3
"""r76: non-vacuity census for the CORNER that y3i_L4_slice_scb's extra hypothesis
`reg` (= "j-2 < j0 or j0 admissible") used to cut away, and which y3k_L4_slice_scb
now covers: condition (V) with a NON-admissible j0 (there j-2 = j0).

For each mined ST_PS host M (monoT, hasParent M 1 j1, j1 = Lng M - 1 > 1, not (VI)):
  reg   := (jm2 < j0) or adm(M, j0)
  corner:= not reg          [<=> condV and not adm j0]
  guard := jm3 < jm2   (jm3 = Adm(M, jm2)); admeq := Adm(M,jm2) == jm1 = Adm(M,j0)
The interesting (non-trivial) instances of L4 in the corner are those with
guard and admeq.  We also check L4's part (3) numerically there:
   Trans(Pred(N'))  ==  D_{M[1,jm2]}( t2 ),      N' = seg M jm2 j1,
   t2 = bpHeadT(Mark(Pred M, jm1)).
"""
import sys, time, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4c/python')
from red_model import Lng, entry, parent, oper, diagSeq, monoT, hasParent, seg, Pred
from trans_model import Trans, adm, Adm, Mark

def condIII(M):
    j1 = Lng(M)-1; jp = parent(M,0,j1)
    return entry(M,1,j1) > 0 and entry(M,1,jp) >= entry(M,1,j1) and adm(M,jp)
def condIV(M):
    j1 = Lng(M)-1; jp = parent(M,0,j1)
    return entry(M,1,j1) > 0 and entry(M,1,jp) >= entry(M,1,j1) and not adm(M,jp)
def condV(M):
    j1 = Lng(M)-1; jp = parent(M,0,j1)
    return entry(M,1,j1) > 0 and entry(M,1,jp)+1 == entry(M,1,j1) and jp+1 < j1
def condVI(M):
    j1 = Lng(M)-1; jp = parent(M,0,j1)
    return entry(M,1,j1) > 0 and entry(M,1,jp)+1 == entry(M,1,j1) and jp+1 == j1

def bpHeadT(t):
    ps = t[1]
    return ('T', []) if not ps else ps[-1][2]

def mine(tmax, rng, want):
    t0 = time.time(); seen = set(); out = []
    while time.time()-t0 < tmax and len(out) < want:
        u = rng.randrange(0,5); v = u + rng.randrange(1,6)
        M = diagSeq(u,v)
        for _ in range(rng.randrange(4,26)):
            if time.time()-t0 > tmax: break
            k = rng.choice((1,1,1,2,2,2,3,4))
            try: M2 = oper(M,k)
            except Exception: break
            if not M2 or M2 == M or Lng(M2) > 14: break
            M = M2
            key = tuple(M)
            if key in seen: continue
            seen.add(key)
            j1 = Lng(M)-1
            if j1 <= 1 or not monoT(M): continue
            if not hasParent(M,1,j1): continue
            if condVI(M): continue
            out.append(list(M))
    return [list(m) for m in dict.fromkeys(tuple(m) for m in out)]

def main():
    tmax = float(sys.argv[1]) if len(sys.argv) > 1 else 90
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 7
    hosts = mine(tmax, random.Random(seed), 400)
    st = dict(total=0, reg=0, corner=0, corner_guard=0, corner_guard_admeq=0,
              d3_ok=0, d3_bad=0, jm2ltLm2_ok=0, jm2ltLm2_bad=0)
    cex = []
    for M in hosts:
        j1 = Lng(M)-1; j0 = parent(M,0,j1); jm2 = parent(M,1,j1)
        jm1 = Adm(M,j0); jm3 = Adm(M,jm2)
        st['total'] += 1
        # the numeric premise the y3k chain needs, from not-(VI) alone
        if jm2 < Lng(M)-2: st['jm2ltLm2_ok'] += 1
        else:
            st['jm2ltLm2_bad'] += 1; cex.append(('jm2<Lng-2 FAILS', list(M)))
        reg = (jm2 < j0) or adm(M,j0)
        if reg: st['reg'] += 1; continue
        st['corner'] += 1
        assert condV(M) and not adm(M,j0) and jm2 == j0, ('corner shape', M)
        if jm3 < jm2:
            st['corner_guard'] += 1
            if jm3 == jm1:
                st['corner_guard_admeq'] += 1
                Np = seg(M, jm2, j1)
                lhs = Trans(Pred(Np))
                t2 = bpHeadT(Mark(Pred(M), jm1))
                rhs = ('T', [('D', entry(M,1,jm2), t2)])
                if lhs == rhs: st['d3_ok'] += 1
                else:
                    st['d3_bad'] += 1; cex.append(('L4(3) FAILS', list(M), lhs, rhs))
    print('hosts (ST_PS, monoT, hasParent row1 j1, j1>1, not (VI)):', st['total'])
    print('  reg holds (old coverage)              :', st['reg'])
    print('  CORNER  condV & non-adm j0 (new)      :', st['corner'])
    print('     ... of which guard jm3<jm2         :', st['corner_guard'])
    print('     ... and admeq Adm(jm2)=jm1         :', st['corner_guard_admeq'])
    print('  L4 part (3) in the corner  ok/bad     :', st['d3_ok'], '/', st['d3_bad'])
    print('  y3k numeric premise jm2<Lng-2 ok/bad  :', st['jm2ltLm2_ok'], '/', st['jm2ltLm2_bad'])
    for c in cex[:5]: print('  CEX', c)

main()
