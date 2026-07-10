#!/usr/bin/env python3
"""r46-devel STEP-0: identify the witness pair (N, N') for the packaged
residual `devel` of spx_slotTail_modDevel.

At an applicable deep-insertion host M (monoT, Br != [], Lng-1 > 1, both
Trans M / Trans(Pred M) single-principal with head v0 = entry M 1 0,
len(body principals of Trans M) >= 2):

  listM = body principals of Trans M = ps @ [D_x q]
  deposit  = listM[-1] = D_x q
  prevdep  = listM[-2] = D_hdv qb (= last ps)

Candidates (per principal): the branches Br(M)[k] raw and Red'd, the
from-joint slice (known refuted; control), root-attached branch.

Checks:
 (a) deposit == Trans(candidate) for which candidate?  Same for prevdep.
 (b) is the matching candidate standard (yaBMS bms -s)?
 (c) Lng(candidate) < Lng(M)?
 (d) order half: N == N'  or  lt_term(Trans N, Trans N')?
 (e) does EVERY body principal match the corresponding branch
     (len(listM) == len(Br M) and listM[k] == Trans(Br M[k]) head-principal)?
"""
import sys, time, signal, random
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
from red_model import (Lng, entry, monoT, Br, diagSeq, oper, seg, Joints,
                       Red, is_standard)
from trans_model import Trans, Pred
import buchholz as bu
from collections import deque

class TO(Exception): pass
def _h(s, f): raise TO()
signal.signal(signal.SIGALRM, _h)
def safe(f, *a, budget=6):
    signal.alarm(budget)
    try:
        r = f(*a); signal.alarm(0); return r
    except (TO, RecursionError, AssertionError, ValueError, IndexError,
            KeyError, RuntimeError):
        signal.alarm(0); return None

def bucOf(t):
    return [('D', p[1], bucOf(p[2])) for p in t[1]]

_std_cache = {}
def std(M):
    k = tuple(M)
    if k not in _std_cache:
        try:
            _std_cache[k] = is_standard(M)
        except Exception:
            _std_cache[k] = None
    return _std_cache[k]

_tr_cache = {}
def trO(M):
    k = tuple(M)
    if k not in _tr_cache:
        t = safe(Trans, M, budget=4)
        _tr_cache[k] = None if t is None else bucOf(t)
    return _tr_cache[k]

UNITS = [
 [(1,1),(2,1)],
 [(1,1),(2,2),(2,1)],
 [(1,1),(2,2),(3,1),(4,2)],
 [(1,1),(2,2),(3,1),(4,2),(4,2)],
 [(1,1),(2,2),(3,3),(4,1),(5,2)],
 [(1,1),(2,1),(3,1)],
 [(1,1),(2,2),(2,1),(3,1)],
 [(1,1),(2,2),(3,2)],
 [(1,1),(2,2),(3,1),(4,3)],
]
def repeat_seed(U, k): return [(0,0)] + U * k
SEED_HOSTS = [
 [(0,0),(1,1),(2,2),(3,1),(4,2),(4,2)],
 [(0,0),(1,1),(2,2),(3,1),(4,0),(5,1),(6,2),(7,0),(6,2)],
]

def gen(maxlen, tmax, seeds):
    seen = set(); t0 = time.time()
    starts = [diagSeq(u, u+d) for u in range(0, 7) for d in range(1, 7)]
    starts += [list(x) for x in SEED_HOSTS]
    for U in UNITS:
        for k in (2, 3, 4):
            s = repeat_seed(U, k)
            if Lng(s) <= maxlen: starts.append(s)
    dq = deque()
    for s in starts:
        k = tuple(s)
        if k not in seen: seen.add(k); dq.append(s); yield s
    tb = t0 + tmax * 0.5
    while dq and time.time() < tb:
        M = dq.popleft()
        for nn in range(1, 4):
            M2 = safe(oper, M, nn, budget=2)
            if M2 is None or M2 == M or Lng(M2) > maxlen: continue
            k = tuple(M2)
            if k not in seen: seen.add(k); dq.append(M2); yield M2
    for sd in seeds:
        if time.time() - t0 > tmax: return
        rng = random.Random(sd)
        for s in starts:
            M = list(s)
            for _ in range(90):
                if time.time() - t0 > tmax: return
                nn = rng.randrange(1, 4)
                M2 = safe(oper, M, nn, budget=2)
                if M2 is None or M2 == M or Lng(M2) > maxlen: break
                M = M2; k = tuple(M)
                if k not in seen: seen.add(k); yield M

def match_candidates(M, princ):
    """Return list of tags of candidates C with Trans(C) == Trm [princ]."""
    tags = []
    B = Br(M); J = Joints(M)
    for k in range(len(B)):
        t = trO(B[k])
        if t is not None and t == [princ]:
            tags.append(('br', k))
        rb = safe(Red, B[k], budget=3)
        if rb is not None and rb != B[k]:
            t2 = trO(rb)
            if t2 is not None and t2 == [princ]:
                tags.append(('redbr', k))
    if J:
        j0p = J[len(B) - 1]
        sl = seg(M, j0p, Lng(M) - 1)
        t = trO(sl)
        if t is not None and t == [princ]:
            tags.append(('joint-slice', -1))
    return tags

def main():
    tmax = int(sys.argv[1]) if len(sys.argv) > 1 else 240
    maxlen = int(sys.argv[2]) if len(sys.argv) > 2 else 16
    S = dict(pool=0, applic=0,
             dep_br_last=0, dep_redbr_last=0, dep_other=0, dep_none=0,
             prev_br_prev=0, prev_redbr_prev=0, prev_other=0, prev_none=0,
             allmatch=0, allmatch_fail=0,
             wit_std=0, wit_std_fail=0, wit_lng=0, wit_lng_fail=0,
             wit2_std=0, wit2_std_fail=0,
             order_eq=0, order_lt=0, order_fail=0,
             eq_pair=0, eq_pair_sameN=0, eq_pair_diffN=0)
    ex_dep_none, ex_prev_none, ex_order, ex_std = [], [], [], []
    t0 = time.time()
    for M in gen(maxlen, tmax, seeds=[11, 22]):
        if time.time() - t0 > tmax: break
        S['pool'] += 1
        if not monoT(M) or Br(M) == [] or not (Lng(M) - 1 > 1): continue
        PM = Pred(M)
        v0 = entry(M, 1, 0)
        TM = safe(Trans, M, budget=5); TPM = safe(Trans, PM, budget=5)
        if TM is None or TPM is None: continue
        if len(TM[1]) != 1 or len(TPM[1]) != 1: continue
        if TM[1][0][1] != v0 or TPM[1][0][1] != v0: continue
        listM = bucOf(TM[1][0][2]); listPM = bucOf(TPM[1][0][2])
        if len(listM) < 2: continue
        # shape gate: ppfx or wb (same as r45)
        ps = listM[:-1]
        okshape = (len(listPM) == len(listM) and listPM[:-1] == ps
                   and listPM[-1][1] == listM[-1][1]) or (listPM == ps)
        if not okshape: continue
        S['applic'] += 1
        B = Br(M); nb = len(B)
        dep = listM[-1]; prev = listM[-2]
        x, q = dep[1], dep[2]; hdv, qb = prev[1], prev[2]
        # (e) full correspondence body principals <-> branches
        if len(listM) == nb:
            all_ok = True
            for k in range(nb):
                t = trO(B[k])
                if t is None or t != [listM[k]]:
                    all_ok = False; break
            if all_ok: S['allmatch'] += 1
            else: S['allmatch_fail'] += 1
        else:
            S['allmatch_fail'] += 1
        # (a) deposit host
        dt = match_candidates(M, dep)
        N = None; Ntag = None
        if ('br', nb - 1) in dt:
            S['dep_br_last'] += 1; N = B[nb - 1]; Ntag = 'br'
        elif ('redbr', nb - 1) in dt:
            S['dep_redbr_last'] += 1
            N = safe(Red, B[nb - 1], budget=3); Ntag = 'redbr'
        elif dt:
            S['dep_other'] += 1
            tag, k = dt[0]
            N = (B[k] if tag == 'br' else
                 (safe(Red, B[k], budget=3) if tag == 'redbr' else None))
        else:
            S['dep_none'] += 1
            if len(ex_dep_none) < 6:
                ex_dep_none.append((list(M), bu.fmt(('T', []))
                                    if False else str(dep)))
        # prev host
        pt = match_candidates(M, prev)
        NP = None
        if nb >= 2 and ('br', nb - 2) in pt:
            S['prev_br_prev'] += 1; NP = B[nb - 2]
        elif nb >= 2 and ('redbr', nb - 2) in pt:
            S['prev_redbr_prev'] += 1; NP = safe(Red, B[nb - 2], budget=3)
        elif pt:
            S['prev_other'] += 1
            tag, k = pt[0]
            NP = (B[k] if tag == 'br' else
                  (safe(Red, B[k], budget=3) if tag == 'redbr' else None))
        else:
            S['prev_none'] += 1
            if len(ex_prev_none) < 6:
                ex_prev_none.append((list(M), str(prev)))
        # (b)(c) standardness + Lng of the deposit witness
        if N is not None:
            sd = std(N)
            if sd is True: S['wit_std'] += 1
            elif sd is False:
                S['wit_std_fail'] += 1
                if len(ex_std) < 6: ex_std.append(('N', list(M), list(N)))
            if Lng(N) < Lng(M): S['wit_lng'] += 1
            else: S['wit_lng_fail'] += 1
        if NP is not None:
            sd = std(NP)
            if sd is True: S['wit2_std'] += 1
            elif sd is False:
                S['wit2_std_fail'] += 1
                if len(ex_std) < 6: ex_std.append(('NP', list(M), list(NP)))
        # (d) order half, on the matched pair
        if N is not None and NP is not None:
            tN = trO(N); tNP = trO(NP)
            if N == NP:
                S['order_eq'] += 1
            elif (tN is not None and tNP is not None
                  and bu.lt_term(tN, tNP)):
                S['order_lt'] += 1
            else:
                S['order_fail'] += 1
                if len(ex_order) < 8:
                    ex_order.append((list(M), list(N), list(NP)))
            if x == hdv:
                S['eq_pair'] += 1
                if N == NP: S['eq_pair_sameN'] += 1
                else: S['eq_pair_diffN'] += 1
    print('==== r46 devel STEP-0 ====')
    for k, v in S.items(): print('  %-16s = %d' % (k, v))
    if ex_dep_none:
        print('\n *** deposit matched NO candidate ***')
        for e in ex_dep_none: print('   ', e)
    if ex_prev_none:
        print('\n *** prev principal matched NO candidate ***')
        for e in ex_prev_none: print('   ', e)
    if ex_std:
        print('\n *** witness NOT standard ***')
        for e in ex_std: print('   ', e)
    if ex_order:
        print('\n *** order half FAILED (N != NP and not Trans N < Trans NP) ***')
        for e in ex_order: print('   ', e)

if __name__ == '__main__':
    main()
