#!/usr/bin/env python3
"""r19-CFA: validate the abstract KIND-1 CF-META engine hypotheses (non-vacuity)
for genuine condIII deep hosts.

Engine claim (cfax_CF_kind1_concat / _mnform): for the condIII surgery data
  e3 = M_{1, jm3},  ub = M_{1,j1} - 1,  jm2 = parent(M,1,j1),
the four value facts
  jm2ub : entry M 1 jm2 = ub
  nzPN  : not zeroT (Pred (Np)),  Np = seg M jm2 j1
  fPN   : Trans(Pred Np)  is ub-principal, body A0
  fLp   : Trans(Lp)       is ub-principal, Lp = seg M jm2 (j1-1) @ [(M_{0,j1}, M_{1,jm2})]
  baseM : flatBT(Trans(M[1])) = s1 @ [D e3] @ flatBT A0 @ b1
  baseL : flatBT(Trans(L1))  = s1 @ [D e3] @ s0 @ [D ub, Z] @ b0 @ b1,  L1 = s84x_L M 1
together with the induction engine yield the full tower mnform:
  flatBT(Trans(M[m])) = s1 @ [D e3] @ (s0@[D ub])^(m-1) @ flatBT A0 @ b0^(m-1) @ b1.
We check every named fact AND rebuild mnform for m=1..4 from (s1,b1,block,flatA0,b0)
extracted at m=1,2, comparing to the actual flat string.
"""
import sys, os, time, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import red_model as rm, trans_model as tm
from red_model import Lng, entry, parent, oper, Pred, zeroT, monoT, diagSeq, fmt
from trans_model import Trans, Adm, flatBT, bpHeadT, bpHeadV, ZB

# memoize Trans
_TC = {}; _T0 = tm.Trans
def _Tm(M, d=0):
    k = tuple(map(tuple, M))
    if k not in _TC: _TC[k] = _T0(M, d)
    return _TC[k]
tm.Trans = _Tm
def T(M): return tm.Trans(M)

def pr(*a): print(*a, flush=True)

def seg(M, a, b): return [M[j] for j in range(a, b + 1)]

def cond_of(M):
    j1 = Lng(M) - 1
    if j1 <= 1: return None
    jp = parent(M, 0, j1)
    v1 = entry(M, 1, j1)
    a = tm.adm(M, jp)
    if v1 == 0: return 'I' if a else 'II'
    e = entry(M, 1, jp)
    if e + 1 == v1: return 'V' if a else 'VI'
    return 'III' if a else 'IV'

def principal(t): return len(t[1]) == 1

def s84x_L(M, n):
    j1 = Lng(M) - 1; jm2 = parent(M, 1, j1)
    Mn = oper(M, n)
    tail = (entry(M, 0, jm2) + n * (entry(M, 0, j1) - entry(M, 0, jm2)),
            entry(M, 1, jm2))
    return list(Mn) + [tail]

def s84x_Lp(M):
    j1 = Lng(M) - 1; jm2 = parent(M, 1, j1)
    return seg(M, jm2, j1 - 1) + [(entry(M, 0, j1), entry(M, 1, jm2))]

def s84x_Np(M):
    j1 = Lng(M) - 1; jm2 = parent(M, 1, j1)
    return seg(M, jm2, j1)

def find_sub(hay, needle, start=0):
    for i in range(start, len(hay) - len(needle) + 1):
        if hay[i:i + len(needle)] == needle: return i
    return -1

def allRP(xs): return all(x == ')' for x in xs)

def gen_pool(maxlen, maxn, maxseed, cap):
    seen = set(); frontier = []
    for u in range(maxseed):
        for v in range(u, u + maxseed + 2):
            M = tuple(map(tuple, diagSeq(u, v)))
            if M not in seen: seen.add(M); frontier.append([list(c) for c in M])
    pool = list(frontier)
    while frontier and len(pool) < cap:
        nxt = []
        for M in frontier:
            if Lng(M) <= 1: continue
            for n in range(1, maxn + 1):
                N = oper(M, n)
                if Lng(N) > maxlen: continue
                t = tuple(map(tuple, N))
                if t not in seen:
                    seen.add(t); nxt.append(N); pool.append(N)
                    if len(pool) >= cap: break
            if len(pool) >= cap: break
        frontier = nxt
    return pool

def check(M, S):
    try:
        j1 = Lng(M) - 1
        if j1 <= 1: return
        jm2 = parent(M, 1, j1)
        if jm2 is None: return
        jm3 = Adm(M, jm2)
        e3 = entry(M, 1, jm3)
        ub = entry(M, 1, j1) - 1
        S['host'] += 1
        # jm2ub
        S['jm2ub'] += (entry(M, 1, jm2) == ub)
        # nzPN
        Np = s84x_Np(M); PNp = Pred(Np)
        nz = not zeroT(PNp)
        S['nzPN'] += nz
        if not nz:
            return   # engine assumes nzPN; skip the rest (not a violation)
        # fPN: Trans(Pred Np) ub-principal
        TPN = T(PNp)
        fpn_ok = principal(TPN) and bpHeadV(TPN) == ub
        S['fPN'] += fpn_ok
        A0 = bpHeadT(TPN)
        flatA0 = flatBT(A0)
        # fLp: Trans(Lp) ub-principal
        Lp = s84x_Lp(M); TLp = T(Lp)
        flp_ok = principal(TLp) and bpHeadV(TLp) == ub
        S['fLp'] += flp_ok
        # rebuild mnform from m=1,2 extraction, verify m=1..4
        Dsym_e3 = ('D', e3); Dsym_ub = ('D', ub)
        F = [flatBT(T(oper(M, m))) for m in range(1, 5)]
        F1, F2 = F[0], F[1]
        # locate [D e3] @ flatA0 in F1
        pat1 = [Dsym_e3] + flatA0
        p = find_sub(F1, pat1)
        S['baseM_loc'] += (p >= 0)
        if p < 0: return
        s1 = F1[:p]; b1 = F1[p + len(pat1):]
        S['b1RP'] += allRP(b1)
        # F2: strip s1 / b1, mid2 = [D e3] + block + flatA0 + b0
        if not (F2[:len(s1)] == s1 and (len(b1) == 0 or F2[-len(b1):] == b1)):
            S['baseL_strip'] += 0; return
        S['baseL_strip'] += 1
        mid2 = F2[len(s1): len(F2) - len(b1)]
        if mid2[0] != Dsym_e3: return
        rest = mid2[1:]        # block + flatA0 + b0
        # flatA0 occurs; block ends in Dsym_ub
        q = find_sub(rest, flatA0)
        if q < 0: return
        block = rest[:q]; b0 = rest[q + len(flatA0):]
        S['b0RP'] += allRP(b0)
        S['block_ub'] += (len(block) > 0 and block[-1] == Dsym_ub)
        # now verify the tower for m=1..4
        ok_all = True
        for idx, m in enumerate(range(1, 5)):
            claim = s1 + [Dsym_e3] + block * (m - 1) + flatA0 + b0 * (m - 1) + b1
            if claim != F[idx]:
                ok_all = False; break
        S['mnform'] += ok_all
        if ok_all and Lng(M) >= 9:
            S['mnform_deep'] += 1
        if Lng(M) >= 9:
            S['host_deep'] += 1
        if not ok_all and len(S['cex']) < 6:
            S['cex'].append((fmt(M), m))
    except (ValueError, IndexError):
        S['err'] += 1

def main():
    tb = int(sys.argv[1]) if len(sys.argv) > 1 else 240
    random.seed(19)
    t0 = time.time()
    pool = gen_pool(maxlen=12, maxn=2, maxseed=7, cap=2000)
    pr(f"pool={len(pool)} maxLng={max(Lng(M) for M in pool)} "
       f"build_s={round(time.time()-t0,1)}")
    hosts = [M for M in pool if Lng(M) >= 3 and not zeroT(M) and monoT(M)
             and cond_of(M) == 'III']
    pr(f"condIII hosts={len(hosts)} deep(>=9)={sum(1 for M in hosts if Lng(M)>=9)}")
    S = dict.fromkeys(['host', 'host_deep', 'jm2ub', 'nzPN', 'fPN', 'fLp',
                       'baseM_loc', 'baseL_strip', 'b0RP', 'b1RP', 'block_ub',
                       'mnform', 'mnform_deep', 'err'], 0)
    S['cex'] = []
    t0 = time.time()
    for M in hosts:
        if time.time() - t0 > tb: break
        check(M, S)
    pr("RESULTS:")
    for k in ['host', 'host_deep', 'jm2ub', 'nzPN', 'fPN', 'fLp', 'baseM_loc',
              'baseL_strip', 'b0RP', 'b1RP', 'block_ub', 'mnform', 'mnform_deep',
              'err']:
        pr(f"  {k:12s} {S[k]}")
    if S['cex']: pr("  CEX:", S['cex'])

if __name__ == '__main__':
    main()
