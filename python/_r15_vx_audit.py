#!/usr/bin/env python3
"""r15-VX: A28 index-shift propagation + exchange-shape audit over the GENUINE
ST_PS regime.  Validates the printed fundamental-sequence indices of every
still-sorry'd SS 8 exchange statement BEFORE proof effort is spent on them.

Sections (run: python3 _r15_vx_audit.py [section|all] [small|std|big]):
  calib85 : re-derive A28 on this harness's pools (sanity: printed (1) must fail)
  s84x    : p_8_4_Trans_oper_exchange (1)(2)(3), printed numBT(n-1), + shifts
  s84b    : p_8_4_oper_basic (1)(2)(3), printed exponents / numBT(n-1) / numBT n
  exch4   : F7 exchIV hypothesis: EX k. leBT (Trans (N[m])) (operB (Trans N) (numBT k))
            -- minimal-k distribution on all reachable genuine condIV hosts
  s81     : p_8_1_Trans_fseq_condI (1)(2) + the stepT residual of
            m_8_1_Trans_fseq_condI_comm_append_reduce
  s83     : SS 8.3 condII exchange, printed m_n = n-1 / n-2 (by leftDj0) --
            conclusions (1)(2)(3) of the article text + transcribed descent (4)
  s86     : p_8_6_Trans_fseq_condVI (1)(2)(3), printed m_n = n-2 / n-1

Genuine regime = diagSeq seeds closed under oper (ST_PS inductive def) plus
mono P-components of multi members (ST_PS by m_6_7_standard_P_components).
"""
import sys, time
from _r15_vx_lib import *  # noqa

NS = (1, 2, 3)

SEC_BUDGET = 900   # seconds of wall time per section (small-first host order)

class SecTimer:
    def __init__(self): self.t0 = time.time(); self.cut = 0
    def over(self):
        if time.time() - self.t0 > SEC_BUDGET:
            self.cut += 1
            return True
        return False

# ---------------- pool assembly ----------------
def build_hosts(size='std'):
    t0 = time.time()
    if size == 'small':
        specs = [dict(maxlen=8, maxn=3, maxseed=3, cap=1200)]
    elif size == 'big':
        specs = [dict(maxlen=9, maxn=4, maxseed=3, cap=6000),
                 dict(maxlen=7, maxn=4, maxseed=5, cap=6000),
                 dict(maxlen=12, maxn=3, maxseed=3, cap=3000),
                 dict(maxlen=10, maxn=5, maxseed=4, cap=4000)]
    elif size == 'wide2':   # rare-regime miner (condII / condIV)
        specs = [dict(maxlen=8, maxn=5, maxseed=6, cap=9000),
                 dict(maxlen=10, maxn=4, maxseed=5, cap=6000)]
    else:
        specs = [dict(maxlen=9, maxn=4, maxseed=3, cap=4000),
                 dict(maxlen=7, maxn=4, maxseed=5, cap=4000),
                 dict(maxlen=12, maxn=3, maxseed=3, cap=2000)]
    pool, seen = [], set()
    for sp in specs:
        for M in gen_pool(**sp):
            t = tuple(M)
            if t not in seen:
                seen.add(t); pool.append(M)
    hosts = mono_hosts(pool)
    hosts.sort(key=lambda M: (Lng(M), max(max(a, b) for (a, b) in M), tuple(M)))
    print(f'pool={len(pool)} distinct ST members; mono hosts={len(hosts)} '
          f'({time.time()-t0:.0f}s)')
    return hosts

def j1_of(M): return Lng(M) - 1

def regime_84(M):
    j1 = j1_of(M)
    return (monoT(M) and j1 > 1 and hasParent(M, 1, j1)
            and (condIII(M) or condIV(M)))

# ---------------- section: calib85 (A28 sanity) ----------------
def run_calib85(hosts):
    T = Tally(); nh = 0
    _st = SecTimer()
    for M in hosts:
        if _st.over(): break
        j1 = j1_of(M)
        if not (j1 > 1 and condV(M)): continue
        nh += 1
        j0 = parent(M, 0, j1)
        mnf = (lambda n: (n - 1) if adm(M, j0) else n)
        for n in NS:
            def chk():
                mn = mnf(n)
                tM = Trans(M); tMn = Trans(oper(M, n)); tMn1 = Trans(oper(M, n + 1))
                fs = operB(tM, numBT(mn)); fs1 = operB(tM, numBT(mn + 1))
                return {
                    '85(1) printed leBT@mn': leBT(tMn, fs),
                    '85(1) A28 strict@mn+1': lessBT(tMn, fs1),
                    '85(2) descent': lessBT(tMn, tM),
                    '85(3) printed leBT@mn..M[n+1]': leBT(fs, tMn1),
                    '85(3) shifted @mn+1..M[n+1]': leBT(fs1, tMn1),
                }
            res = guarded(chk, budget=15)
            if res is SKIP:
                T.add('85 instance', SKIP); continue
            for k, v in res.items(): T.add(k, v, (M, n))
    print(T.report(f'== calib85: condV hosts={nh} =='))

# ---------------- section: s84x (p_8_4_Trans_oper_exchange) ----------------
def run_s84x(hosts):
    T = Tally(); nh = {'III': 0, 'IV': 0}
    _st = SecTimer()
    for M in hosts:
        if _st.over(): break
        if not regime_84(M): continue
        tag = 'IV' if condIV(M) else 'III'
        nh[tag] += 1
        for n in NS:
            def chk():
                tM = Trans(M); tMn = Trans(oper(M, n)); tMn1 = Trans(oper(M, n + 1))
                fsm1 = operB(tM, numBT(n - 1)); fs0 = operB(tM, numBT(n))
                return {
                    f'84x{tag}(1) printed leBT@n-1': leBT(tMn, fsm1),
                    f'84x{tag}(1) shifted leBT@n': leBT(tMn, fs0),
                    f'84x{tag}(1) shifted strict@n': lessBT(tMn, fs0),
                    f'84x{tag}(2) descent': lessBT(tMn, tM),
                    f'84x{tag}(3) printed @n-1 < M[n+1]': lessBT(fsm1, tMn1),
                    f'84x{tag}(3) shifted @n < M[n+1]': lessBT(fs0, tMn1),
                }
            res = guarded(chk, budget=15)
            if res is SKIP:
                T.add(f'84x{tag} instance', SKIP); continue
            for k, v in res.items(): T.add(k, v, (M, n))
    print(T.report(f'== s84x: condIII hosts={nh["III"]} condIV hosts={nh["IV"]} =='))

# ---------------- section: s84b (p_8_4_oper_basic) ----------------
def run_s84b(hosts):
    T = Tally(); nh = {'III': 0, 'IV': 0}
    _st = SecTimer()
    for M in hosts:
        if _st.over(): break
        if not regime_84(M): continue
        tag = 'IV' if condIV(M) else 'III'
        nh[tag] += 1
        j1 = j1_of(M); jm2 = parent(M, 1, j1)
        for n in NS:
            def chk():
                Mn = oper(M, n); Mn1 = oper(M, n + 1)
                # (1) printed: M[n] = ([1]-iterate ^ (j1-jm2)) (M[n+1])
                it = Mn1
                for _ in range(j1 - jm2): it = oper(it, 1)
                r1 = (it == Mn)
                # (2) printed: operB(Trans M)(numBT(n-1)) = Trans(([1]^ (j1-1-jm2))(M[n+1]))
                tM = Trans(M)
                it2 = Mn1
                for _ in range(j1 - 1 - jm2): it2 = oper(it2, 1)
                lhs2 = operB(tM, numBT(n - 1))
                r2 = (lhs2 == Trans(it2))
                # (2) A28-style variant: numBT n at the same exponent
                r2s = (operB(tM, numBT(n)) == Trans(it2))
                # (2) FULL GRID: any (index shift d, [1]-iterate count e) equality?
                trs = {}
                it3 = Mn1
                for e in range(0, j1 - jm2 + 2):
                    trs[e] = Trans(it3)
                    it3 = oper(it3, 1)
                r2any = any(operB(tM, numBT(n - 1 + d)) == tv
                            for d in (-1, 0, 1) if n - 1 + d >= 0
                            for tv in trs.values())
                # (3) printed: principal pairing of Trans(M[n]) vs Trans(M)[n]
                tMn = Trans(Mn)
                r3 = principal_pair_exists(tMn, operB(tM, numBT(n))) is not None
                r3s = principal_pair_exists(tMn, operB(tM, numBT(n + 1))) is not None
                r3m = principal_pair_exists(tMn, operB(tM, numBT(n - 1))) is not None
                return {
                    f'84b{tag}(1) printed iterate j1-jm2': r1,
                    f'84b{tag}(2) printed @n-1 = Trans(iter j1-1-jm2)': r2,
                    f'84b{tag}(2) shifted @n  = Trans(iter j1-1-jm2)': r2s,
                    f'84b{tag}(2) ANY (d,e) grid equality': r2any,
                    f'84b{tag}(3) printed pair@n': r3,
                    f'84b{tag}(3) pair@n+1': r3s,
                    f'84b{tag}(3) pair@n-1': r3m,
                }
            res = guarded(chk, budget=20)
            if res is SKIP:
                T.add(f'84b{tag} instance', SKIP); continue
            for k, v in res.items(): T.add(k, v, (M, n))
    print(T.report(f'== s84b: condIII hosts={nh["III"]} condIV hosts={nh["IV"]} =='))

# ---------------- section: exch4 (F7 exchIV intermediate bound) ----------------
def run_exch4(hosts):
    T = Tally(); dist = {}; nh = 0
    _st = SecTimer()
    for M in hosts:
        if _st.over(): break
        j1 = j1_of(M)
        if not (monoT(M) and j1 > 1 and condIV(M) and hasParent(M, 1, j1)):
            continue
        nh += 1
        for m in (1, 2, 3, 4):
            def chk():
                tN = Trans(M); tNm = Trans(oper(M, m))
                ks = [k for k in range(m + 4) if leBT(tNm, operB(tN, numBT(k)))]
                return ks
            ks = guarded(chk, budget=20)
            if ks is SKIP:
                T.add('exch4 instance', SKIP); continue
            key = f'exch4 m={m}'
            T.add(key + ' EX k (k<=m+3)', bool(ks), (M, m))
            if ks:
                mk = min(ks)
                dist.setdefault(m, {}).setdefault(mk, 0)
                dist[m][mk] += 1
                T.add(key + ' @k=m-1 (printed 8.4)', (m - 1) in ks, (M, m))
                T.add(key + ' @k=m (A28 shift)', m in ks, (M, m))
    print(T.report(f'== exch4: condIV hosts (mono, hasParent1, j1>1) = {nh} =='))
    print('  min-k distribution {m: {min_k: count}}:', dist)

# ---------------- section: s81 (condI exchange + stepT residual) ----------------
def run_s81(hosts):
    T = Tally(); nh = 0
    _st = SecTimer()
    for M in hosts:
        if _st.over(): break
        j1 = j1_of(M)
        if not (monoT(M) and j1 > 1 and condI(M)): continue
        nh += 1
        j0 = parent(M, 0, j1)
        B = [M[j] for j in range(j0, j1)]
        for n in NS:
            def chk():
                tM = Trans(M); tMn = Trans(oper(M, n))
                r1 = (tMn == operB(tM, numBT(n - 1)))
                r2 = lessBT(tMn, tM)
                rs = (Trans(oper(M, n) + B) == operB(tM, numBT(n)))
                return {
                    '81(1) printed = @n-1': r1,
                    '81(2) descent': r2,
                    '81 stepT: Trans(M[k]@B) = @k': rs,
                }
            res = guarded(chk, budget=15)
            if res is SKIP:
                T.add('81 instance', SKIP); continue
            for k, v in res.items(): T.add(k, v, (M, n))
    print(T.report(f'== s81: condI hosts={nh} =='))

# ---------------- section: s83 (condII printed m_n bookkeeping) ----------------
def run_s83(hosts):
    T = Tally(); nh = 0; lefts = {True: 0, False: 0}
    _st = SecTimer()
    for M in hosts:
        if _st.over(): break
        j1 = j1_of(M)
        if not (monoT(M) and j1 > 1 and condII(M)): continue
        it = guarded(internals, M, budget=15)
        if it is SKIP or it is None or it['s1'] is None:
            T.add('83 internals', SKIP); continue
        nh += 1; lefts[it['leftDj0']] += 1
        j0, jm1, v = it['j0'], it['jm1'], it['v']
        t1, t2, t3, t4 = it['t1'], it['t2'], it['t3'], it['t4']
        for n in NS:
            mn = (n - 1) if it['leftDj0'] else (n - 2)
            def chk():
                tM = Trans(M); Mn = oper(M, n); tMn = Trans(Mn)
                out = {}
                if mn == -1:
                    out['83(1) mn=-1: Trans(M[n]) = s1 Dv t2 b1 (= t1)'] = (tMn == t1)
                else:
                    fs = operB(tM, numBT(mn))
                    out['83(2) printed = @mn'] = (tMn == fs)
                    out['83(2) shifted = @mn+1'] = (tMn == operB(tM, numBT(mn + 1)))
                # (3) Mark(M[n], jm1) = D_{M1,jm1}(t3 + (D_{M1,j0} t4) x (mn+1))
                rhs = Dpt(entry(M, 1, jm1),
                          addBT(t3, multBT(Dpt(entry(M, 1, j0), t4), mn + 1)))
                out['83(3) printed Mark@mn+1 copies'] = (Mark(Mn, jm1) == rhs)
                rhs2 = Dpt(entry(M, 1, jm1),
                           addBT(t3, multBT(Dpt(entry(M, 1, j0), t4), mn + 2)))
                out['83(3) shifted Mark@mn+2 copies'] = (Mark(Mn, jm1) == rhs2)
                out['83(4) descent'] = lessBT(tMn, tM)
                return out
            res = guarded(chk, budget=20)
            if res is SKIP:
                T.add('83 instance', SKIP); continue
            for k, vv in res.items(): T.add(k, vv, (M, n))
    print(T.report(f'== s83: condII hosts={nh} leftDj0 split={lefts} =='))

# ---------------- section: s86 (condVI printed indices) ----------------
def run_s86(hosts):
    T = Tally(); nh = 0
    _st = SecTimer()
    for M in hosts:
        if _st.over(): break
        j1 = j1_of(M)
        if not (monoT(M) and j1 > 1 and condVI(M)): continue
        nh += 1
        j0 = parent(M, 0, j1); admj0 = adm(M, j0)
        for n in NS:
            def chk():
                tM = Trans(M); tMn = Trans(oper(M, n))
                out = {}
                if n == 1 and admj0:
                    e = entry(M, 1, j1)
                    kfound = kle = None
                    t = tM
                    for k in range(0, e + 8):
                        if k > 0:
                            if t == tMn and kfound is None: kfound = k
                            if kle is None and leBT(tMn, t): kle = k
                        t = operB(t, numBT(0))
                    out['86(1) EX k: Trans(M[1]) = Trans(M)[0]^k'] = kfound is not None
                    if kfound is not None:
                        out['86(1) printed bound 1<k<=M1j1+1'] = (1 < kfound <= e + 1)
                    # weakened (leBT) form, printed k-bound
                    out['86(1w) EX k<=M1j1+1: leBT Trans(M[1]) Trans(M)[0]^k'] = \
                        (kle is not None and kle <= e + 1)
                    # exchVI single-operB shape (F7 hypothesis, n=1 leg)
                    out['86(1x) EX k<=n+3: leBT Trans(M[1]) Trans(M)[numBT k]'] = \
                        any(leBT(tMn, operB(tM, numBT(k))) for k in range(0, n + 4))
                else:
                    mn = (n - 2) if admj0 else (n - 1)
                    out['86(2) printed = @mn(n-2/n-1)'] = \
                        (tMn == operB(tM, numBT(mn)))
                    out['86(2) shifted = @mn+1'] = \
                        (tMn == operB(tM, numBT(mn + 1)))
                out['86(3) descent'] = lessBT(tMn, tM)
                return out
            res = guarded(chk, budget=15)
            if res is SKIP:
                T.add('86 instance', SKIP); continue
            for k, v in res.items(): T.add(k, v, (M, n))
    print(T.report(f'== s86: condVI hosts={nh} =='))

# ---------------- section: s86a (p_8_6_trailing_principal_annihilable) ----------------
def gen_terms(max_nodes=5, max_v=2):
    """All BT terms with <= max_nodes D-nodes, indices <= max_v (T_B = all)."""
    by_n = {0: [ZB]}
    for n in range(1, max_nodes + 1):
        outs = []
        # a term with n nodes: list of principals with node counts summing to n
        def parts(k, maxfirst):
            if k == 0:
                yield []
                return
            for first in range(1, min(k, maxfirst) + 1):
                for rest in parts(k - first, first):   # weakly decreasing sizes
                    yield [first] + rest
        # principal with m nodes: D_v(body with m-1 nodes)
        prin = {}
        for m in range(1, n + 1):
            prin[m] = [Dpt(v, b) for v in range(max_v + 1) for b in by_n[m - 1]]
        import itertools
        for sizes in parts(n, n):
            if len(sizes) > 3: continue
            for combo in itertools.product(*[prin[m] for m in sizes]):
                t = ZB
                for c in combo: t = addBT(t, c)
                outs.append(t)
        # dedupe
        seen = set(); ded = []
        for t in outs:
            k = repr(t)
            if k not in seen: seen.add(k); ded.append(t)
        by_n[n] = ded
    allts = []
    for n in range(0, max_nodes + 1): allts += by_n[n]
    return allts

def run_s86a(hosts):
    """p_8_6_trailing_principal_annihilable, over (a) exhaustive small T_B terms
    and (b) Trans-images of genuine ST_PS members."""
    T = Tally()
    cand_ts = gen_terms(5, 2)
    # add genuine Trans images (bounded)
    added = 0
    for M in hosts:
        if added >= 400: break
        t = guarded(Trans, M, budget=5)
        if t is SKIP: continue
        cand_ts.append(t); added += 1
    print(f'  s86a candidate terms: {len(cand_ts)} '
          f'(exhaustive small + {added} genuine Trans images)')
    ninst = 0
    for t in cand_ts:
        f = flatBT(t)
        n1 = len(f)
        tr = 0
        while tr < n1 and f[n1 - 1 - tr] == ')': tr += 1
        for kb in range(tr + 1):
            for i in range(n1 - kb):
                if not (isinstance(f[i], tuple) and f[i][0] == 'D'): continue
                cf = f[i:n1 - kb]
                if not isPTB_str(cf): continue
                c = unflatBT(cf)
                # core shape D_u(t' + D_v 0)?
                if len(c[1]) != 1: continue
                u = c[1][0][1]; body = c[1][0][2]
                if not body[1]: continue
                lastp = body[1][-1]
                if lastp[2] != ZB: continue
                v = lastp[1]
                tprime = ('T', body[1][:-1])
                s, b = f[:i], f[n1 - kb:]
                # conclusion: EX k in 1..v+1 with scb at (s, D_u t', b) of t[0]^k
                target = s + flatBT(Dpt(u, tprime)) + b
                def chk():
                    tt = t
                    for k in range(1, v + 2):
                        tt = operB(tt, numBT(0))
                        if flatBT(tt) == target: return True
                    return False
                r = guarded(chk, budget=8)
                ninst += 1
                if r is SKIP:
                    T.add('86a instance', SKIP); continue
                T.add('86a printed EX k<=v+1', r)
                if not r:
                    key = '86a printed EX k<=v+1'
                    if key not in T.cex:
                        T.cex[key] = ((0, 0, 0), ((f, i, kb, u, v), 0))
                # discriminators:
                # core-clean = the proven peel guard (v = 0 or u >= v);
                # ctx-clean  = no s-context head can capture the TB(v-1) domain
                #              (all D-heads in s >= v; vacuous for v = 0)
                core_clean = (v == 0 or u >= v)
                sheads = [x[1] for x in s if isinstance(x, tuple) and x[0] == 'D']
                ctx_clean = (v == 0) or all(h >= v for h in sheads)
                T.add('86a core-clean & ctx-clean', r if (core_clean and ctx_clean) else None)
                T.add('86a core-clean & ctx-DIRTY', r if (core_clean and not ctx_clean) else None)
                T.add('86a core-DIRTY & ctx-clean', r if (not core_clean and ctx_clean) else None)
                T.add('86a core-DIRTY & ctx-DIRTY', r if (not core_clean and not ctx_clean) else None)
    print(T.report(f'== s86a: scb-core instances checked={ninst} =='))
    if '86a printed EX k<=v+1' in T.cex:
        print('  first CEX (flat t, pos, kb, u, v):', T.cex['86a printed EX k<=v+1'][1][0])

SECTIONS = dict(calib85=run_calib85, s84x=run_s84x, s84b=run_s84b,
                exch4=run_exch4, s81=run_s81, s83=run_s83, s86=run_s86,
                s86a=run_s86a)

def main():
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    size = sys.argv[2] if len(sys.argv) > 2 else 'std'
    hosts = build_hosts(size)
    t0 = time.time()
    for name, fn in SECTIONS.items():
        if which in ('all', name):
            fn(hosts)
            print(f'  [{name} done at {time.time()-t0:.0f}s]', flush=True)

if __name__ == '__main__':
    main()
