#!/usr/bin/env python3
"""r15-VX: root-cause the round-14 C3 AssertionError inside trans_model.Trans
("no scb decomposition (invariant breach)").

The r14 script _r14_s4pc3_chain_check.py crashed on one pool instance; its notes
(_r14_s4p-c3_notes.py) left the root cause open (model bug vs domain artifact).
This script
  1. replays the same generator (genuine_pool seeds 1..9, same RNG protocol) and
     the same Trans/Mark call sites (check_P / check_top), catching
     AssertionError per call and recording every crashing instance;
  2. for each crash, walks the Trans/Mark recursion tree with public model
     functions only (find_innermost) to locate the INNERMOST host H where the
     assert fires;
  3. analyzes H: Red-fixpoint vs keystone reduced() agreement, Marked
     membership of (Pred H, Adm(H, jp)), substring occurrences of flat(c1) in
     flat(t1), which scb side conditions reject them -- and prints a verdict.

Run: python3 _r15_vx_c3crash.py [maxseed] [steps]   (defaults 9 3000)

RESULT (2026-07-02, run on the r14 protocol seeds 1..9):
  132829 Trans/Mark call sites checked, 0 crashes, 0 timeouts -- the assert
  NEVER fires genuinely on the replayed pools (consistent with the proven
  invariant m_7_3_Trans_Mark_MarkedB on RT_PS >= ST_PS).
ROOT CAUSE (established by deterministic injection, see _r15_vx_report.py):
  trans_model.isPTB_str used a bare `except Exception`, swallowing SIGALRM
  timeout exceptions raised mid-parse by the r14 script's 10 s watchdog; the
  timeout became `False`, scb_decomps dropped the legitimate candidate, and
  Trans raised "no scb decomposition (invariant breach)".  Injecting a
  timeout-shaped exception at the first _parseBP call reproduces the exact
  message.  VERDICT: model robustness bug (not a domain artifact, not a
  semantics bug).  FIXED in trans_model.py (catch only ValueError/IndexError);
  post-fix the injected timeout propagates to the caller.
"""
import sys, os, signal, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import red_model as rm
import trans_model as tm
from red_model import (Lng, entry, le0, monoT, zeroT, seg, parent, hasParent,
                       oper, diagSeq, fmt, Red)
from trans_model import (Adm, adm, Pred, reduced, flatBT, scb_decomps,
                         isPTB_str, ZB)

class TO(Exception): pass
def _alrm(s, f): raise TO()
signal.signal(signal.SIGALRM, _alrm)

# memoize (results only; AssertionError is never cached)
_tmemo, _mmemo = {}, {}
_Trans0, _Mark0 = tm.Trans, tm.Mark
def Trans(M, depth=0):
    k = tuple(M)
    r = _tmemo.get(k)
    if r is None:
        r = _Trans0(M, depth); _tmemo[k] = r
    return r
def Mark(M, m, depth=0):
    k = (tuple(M), m)
    r = _mmemo.get(k)
    if r is None:
        r = _Mark0(M, m, depth); _mmemo[k] = r
    return r
tm.Trans, tm.Mark = Trans, Mark

# ---------- the r14 chain-check call sites (same protocol) ----------
def RightNodes(t):
    ps = t[1]
    if not ps: return []
    p = ps[-1]
    return [p[1]] + RightNodes(p[2])

def marked(N, m):
    return adm(N, m) and le0(N, m, Lng(N) - 1)

def genuine_pool(seed, maxu=2, maxv=3, nmax=4, steps=3000, maxLng=14):
    random.seed(seed)
    pool, seen = [], set()
    frontier = [diagSeq(u, v) for u in range(maxu + 1)
                for v in range(u + 1, u + maxv + 1)]
    for M in frontier: seen.add(tuple(M))
    pool.extend(frontier)
    i = 0
    while i < steps and frontier:
        M = random.choice(frontier)
        n = random.randint(1, nmax)
        signal.alarm(5)
        try:
            Mn = oper(M, n)
        except (TO, Exception):
            signal.alarm(0); i += 1; continue
        signal.alarm(0)
        t = tuple(Mn)
        if t not in seen and 0 < Lng(Mn) <= maxLng:
            seen.add(t); pool.append(Mn); frontier.append(Mn)
        i += 1
    return pool

def transMark_callsites(M):
    """All Trans/Mark invocations check_P/check_top makes for host M.
    Returns list of ('T', host) / ('M', host, m) thunk descriptors."""
    out = []
    j1 = Lng(M) - 1
    for m in range(0, j1):
        if not marked(M, m): continue
        out.append(('M', M, m))
        if not zeroT(Pred(M)):
            jm1 = Adm(M, parent(M, 0, j1))
            if m < jm1:
                out.append(('M', seg(M, 0, jm1), m))
                out.append(('M', M, jm1))
    if j1 > 1 and hasParent(M, 1, j1):
        jm2 = parent(M, 1, j1)
        jm3 = Adm(M, jm2)
        out.append(('M', M, jm3))
        out.append(('T', seg(M, jm3, j1)))
    return out

# ---------- innermost-failure locator (public model functions only) ----------
def _raises_assert(f, *a):
    try:
        signal.alarm(20)
        f(*a)
        return False
    except AssertionError:
        return True
    except (TO, RecursionError, RuntimeError):
        return None          # diverges before any assert
    finally:
        signal.alarm(0)

def find_innermost(kind, M, m=None, depth=0):
    """Descend the Trans/Mark recursion; return ('T'/'M', host[, m]) of the
    innermost call whose own body (not a sub-call) raises the assert."""
    if depth > 300: return ('depth-limit', M, m)
    if not reduced(M):
        # the dispatch itself has no assert; the failure is inside Red M's call
        return find_innermost(kind, Red(M), m, depth + 1)
    j1 = Lng(M) - 1
    if j1 == 0: return (kind, M, m)
    if monoT(M):
        PM = Pred(M)
        if _raises_assert(lambda: Trans(PM)):
            return find_innermost('T', PM, None, depth + 1)
        t1 = Trans(PM)
        if t1 != ZB:
            jp = parent(M, 0, j1)
            jm1 = Adm(M, jp)
            if _raises_assert(lambda: Mark(PM, jm1)):
                return find_innermost('M', PM, jm1, depth + 1)
            if kind == 'M' and m is not None and m < j1:
                if _raises_assert(lambda: Mark(PM, m)):
                    return find_innermost('M', PM, m, depth + 1)
        return (kind, M, m)
    # multi
    Pm = rm.P(M)
    PJ = Pm[-1]; j0 = j1 - Lng(PJ) + 1
    A = seg(M, 0, j0 - 1)
    for sub in ((A, None), (PJ, None)):
        if _raises_assert(lambda: Trans(sub[0])):
            return find_innermost('T', sub[0], None, depth + 1)
    if kind == 'M' and PJ != [(0, 0)]:
        if _raises_assert(lambda: Mark(PJ, max(m - j0, 0))):
            return find_innermost('M', PJ, max(m - j0, 0), depth + 1)
    return (kind, M, m)

# ---------- analysis of the innermost host ----------
def analyze(kindMm):
    kind, H, m = kindMm[0], kindMm[1], (kindMm[2] if len(kindMm) > 2 else None)
    print(f'  innermost failing call: {kind} host={fmt(H)} m={m}')
    j1 = Lng(H) - 1
    redfix = (Red(H) == H)
    print(f'  Red-fixpoint (rm)     : {redfix}')
    print(f'  keystone reduced (tm) : {reduced(H)}   <-- MUST AGREE with Red-fixpoint')
    print(f'  monoT={monoT(H)} zeroT={zeroT(H)} j1={j1}')
    if not (monoT(H) and j1 > 0):
        print('  (assert lives in the mono t1!=0 branch; host shape unexpected)')
        return
    PM = Pred(H)
    t1 = Trans(PM)
    jp = parent(H, 0, j1)
    jm1 = Adm(H, jp)
    print(f'  jp={jp} jm1={jm1}  t1==0_B: {t1 == ZB}')
    admP = adm(PM, jm1); le0P = le0(PM, jm1, Lng(PM) - 1)
    print(f'  (Pred H, jm1) in Marked?  adm(Pred H,jm1)={admP}  '
          f'le0(Pred H,jm1,last)={le0P}')
    print(f'  Pred H Red-fixpoint    : {Red(PM) == PM}')
    c1 = Mark(PM, jm1)
    f1, fc = flatBT(t1), flatBT(c1)
    print(f'  len flat(t1)={len(f1)}  len flat(c1)={len(fc)}  '
          f'isPTB_str(flat c1)={isPTB_str(fc)}')
    occ = [i for i in range(len(f1) - len(fc) + 1) if f1[i:i + len(fc)] == fc]
    print(f'  substring occurrences of flat(c1) in flat(t1): {occ}')
    for i in occ:
        b = f1[i + len(fc):]
        print(f'    occ@{i}: suffix all-RP={all(x == ")" for x in b)} (len {len(b)})')
    print(f'  scb_decomps(t1, flat c1) = {scb_decomps(t1, fc)}')
    if not occ:
        print('  VERDICT HINT: flat(c1) does not occur in flat(t1) at all ->')
        print('    the (Trans,Mark) MarkedB invariant itself fails on this host;')
        print('    check whether the host is genuinely in RT_PS (above).')

def inject_demo():
    """Deterministic reproduction of the r14 crash: simulate a SIGALRM landing
    inside isPTB_str's try-block (pre-fix this printed the exact r14 message;
    post-fix the injected exception propagates)."""
    class TOX(Exception): pass
    orig = tm._parseBP
    state = {'n': 0, 'fire_at': None}
    def hooked(xs):
        state['n'] += 1
        if state['fire_at'] is not None and state['n'] == state['fire_at']:
            raise TOX('simulated SIGALRM inside isPTB_str')
        return orig(xs)
    tm._parseBP = hooked
    M = oper(oper(diagSeq(0, 2), 2), 2)
    _tmemo.clear(); _mmemo.clear()
    Trans(M)
    total = state['n']
    print(f'host M = {fmt(M)}; clean Trans OK, _parseBP calls = {total}')
    hit = False
    for fire in range(1, total + 1):
        state['n'] = 0; state['fire_at'] = fire
        _tmemo.clear(); _mmemo.clear()
        try:
            Trans(M)
        except AssertionError as e:
            print(f'PRE-FIX BEHAVIOUR at parse-call {fire}: AssertionError: {e}')
            hit = True
            break
        except TOX:
            pass    # post-fix: the timeout propagates (correct behaviour)
    if not hit:
        print('POST-FIX BEHAVIOUR: injected timeout always propagates; '
              'the false assert is gone')
    tm._parseBP = orig

def main():
    if len(sys.argv) > 1 and sys.argv[1] == 'inject':
        inject_demo(); return
    maxseed = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    steps = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
    crashes = []
    checked = skipped = 0
    for seed in range(1, maxseed + 1):
        pool = genuine_pool(seed, steps=steps)
        nred = 0
        for M in pool:
            try:
                signal.alarm(10)
                ok = reduced(M) and monoT(M)
                signal.alarm(0)
            except (TO, RecursionError, RuntimeError):
                signal.alarm(0); skipped += 1; continue
            if not ok: continue
            nred += 1
            for site in transMark_callsites(M):
                checked += 1
                try:
                    signal.alarm(20)
                    if site[0] == 'T': Trans(site[1])
                    else: Mark(site[1], site[2])
                    signal.alarm(0)
                except AssertionError:
                    signal.alarm(0)
                    crashes.append(site)
                    print(f'CRASH seed={seed} site={site[0]} '
                          f'host={fmt(site[1])} m={site[2] if len(site) > 2 else None}',
                          flush=True)
                except (TO, RecursionError, RuntimeError):
                    signal.alarm(0); skipped += 1
        print(f'seed {seed}: pool={len(pool)} reduced-mono={nred} '
              f'(cum checked={checked} crashes={len(crashes)} skips={skipped})',
              flush=True)
    print(f'\nTOTAL call sites checked={checked}, crashes={len(crashes)}, '
          f'timeouts/skips={skipped}')
    seen = set()
    for site in crashes:
        key = (site[0], tuple(site[1]), site[2] if len(site) > 2 else None)
        if key in seen: continue
        seen.add(key)
        print(f'\n=== drill-down: {site[0]} {fmt(site[1])} '
              f'm={site[2] if len(site) > 2 else None} ===')
        inner = find_innermost(site[0], site[1],
                               site[2] if len(site) > 2 else None)
        analyze(inner)

if __name__ == '__main__':
    main()
