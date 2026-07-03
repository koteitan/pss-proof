#!/usr/bin/env python3
"""r26 CONDVINADM: validate the three OWED residuals of c613x_condVI_exch_nadm
for NON-admissible-j0 condVI ST_PS hosts:
  (t2eq) transT2 M = D_u 0,  u = entry M 1 j0
  (vU)   transV M = enat U,  U = entry M 1 jm1   (jm1 = Adm M j0)
  (Ult)  U < Suc u   i.e.  entry M 1 jm1 <= entry M 1 j0
plus the candidate proof-bridges:
  (bridge)  transC1 M = transC2(Pred M)
  (PredVI)  condVI(Pred M)
  (readback) transC1 M = Trans(seg(Pred M, jm1, Lng(Pred M)-1))  &  its bpHeadT = D_u 0
Deep ST_PS (oper closure of diagSeq = exactly ST_PS) AND brute-force reduced-monoT
straddle hosts (off the oper corpus)."""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from red_model import Lng, entry, P, monoT, seg, diagSeq, parent, oper, fmt
import red_model as rm
import trans_model as tm
from _r15_vx_lib import (Trans, Mark, gen_pool, mono_hosts, guarded, SKIP,
                         condVI, internals, flatBT)
from trans_model import (Dpt, ZB, adm, Adm, Pred, reduced, bpHeadV, bpHeadT)

def transJ0(M): return parent(M, 0, Lng(M)-1)

def check_host(M, stats, bad):
    info = internals(M)
    if info is None: return
    j1 = Lng(M)-1; j0 = transJ0(M); jm1 = Adm(M, j0)
    u = entry(M, 1, j0)
    v = info['v']; t2 = info['t2']; c1 = info['c1']
    stats['hosts'] += 1
    # (t2eq)
    t2eq = (t2 == Dpt(u, ZB))
    stats['t2eq'] += t2eq
    # (vU) v == entry(M,1,jm1)
    vU = (v == entry(M, 1, jm1))
    stats['vU'] += vU
    # (Ult) v <= u
    Ult = (v <= u)
    stats['Ult'] += Ult
    # bridge: c1 == transC2(Pred M)
    Pinfo = internals(Pred(M))
    bridge = (Pinfo is not None and c1 == Pinfo['c2'])
    stats['bridge'] += bridge
    # PredVI
    P_is = Lng(Pred(M)) >= 2 and guarded(condVI, Pred(M), budget=5)
    PredVI = (P_is is True)
    stats['PredVI'] += PredVI
    # readback: c1 == Trans(seg(Pred M, jm1, Lng(Pred M)-1))
    PM = Pred(M); LP = Lng(PM)
    S = seg(PM, jm1, LP-1)
    TS = guarded(Trans, tuple(S), budget=8)
    rb = (TS is not SKIP and c1 == TS)
    stats['readback'] += rb
    rbbody = (TS is not SKIP and bpHeadT(TS) == Dpt(u, ZB))
    stats['rbbody'] += rbbody
    if not (t2eq and vU and Ult):
        bad.append((fmt(M), f"j0={j0} jm1={jm1} u={u} v={v} t2={flatBT(t2)}"
                    f" t2eq={t2eq} vU={vU} Ult={Ult} bridge={bridge} PredVI={PredVI} rb={rb}"))

def run(hosts, label):
    stats = dict(hosts=0, t2eq=0, vU=0, Ult=0, bridge=0, PredVI=0, readback=0, rbbody=0)
    bad = []
    for M in hosts:
        try:
            check_host(list(M), stats, bad)
        except Exception as e:
            pass
    h = stats['hosts']
    print(f"\n=== {label}: {h} nadm-j0 condVI hosts ===")
    for k in ('t2eq', 'vU', 'Ult', 'bridge', 'PredVI', 'readback', 'rbbody'):
        print(f"  {k:9s}: {stats[k]}/{h}")
    for b in bad[:10]:
        print("  BAD:", b)
    return stats, bad

# ---- ST_PS regime (oper closure) ----
pool = gen_pool(maxlen=12, maxn=6, maxseed=4, cap=20000, oper_budget=5)
hosts = mono_hosts(pool)
nadm = [M for M in hosts if Lng(M) >= 4 and Lng(M)-1 > 1 and reduced(M)
        and guarded(condVI, M, budget=5) is not SKIP and condVI(M)
        and not adm(M, transJ0(M))]
run(nadm, f"ST_PS oper-closure (deep, Lng<=12, {len(hosts)} mono hosts)")

# ---- brute-force reduced monoT straddle hosts (off oper corpus) ----
def gen_brute(maxlen, maxval):
    """all pairseqs starting (0,0), entries in [0,maxval], reduced monoT."""
    out = []
    for L in range(4, maxlen+1):
        # each column (a,b), a,b in 0..maxval; first col (0,0)
        cols = [(a, b) for a in range(maxval+1) for b in range(maxval+1)]
        for rest in itertools.product(cols, repeat=L-1):
            M = [(0, 0)] + list(rest)
            if not monoT(M): continue
            if not reduced(M): continue
            out.append(tuple(M))
    return out

brute = gen_brute(6, 3)
bnadm = [M for M in brute if Lng(M)-1 > 1
         and guarded(condVI, M, budget=5) is not SKIP and condVI(M)
         and not adm(M, transJ0(M))]
run(bnadm, f"BRUTE reduced-monoT (Lng<=6, val<=3, {len(brute)} reduced-mono)")
