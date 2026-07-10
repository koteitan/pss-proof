#!/usr/bin/env python3
"""r47 multiD STEP-0: validate the generation-induction route for comple.

comple: for multiT N in ST_PS, bJ = drop(Pcut N) N != [(0,0)], bJm1 = P N[-2]:
        leBT (Trans bJ) (Trans bJm1)

Route to validate on every BFS edge M -> N = oper(M,n) with N a nontrivial-junction
multiT host:
  (a) comple itself (deep; pcompPrefix-refuted corpus included);
  (b) M mono  => BIRTH: bJ is a prefix of bJm1  (pcompPrefix AT BIRTH only);
  (c) M multi => decomposition N = take(Pcut M) M @ E, E = oper(drop(Pcut M) M, n):
      - E mono  => junction(N) = (P M[-2], E)  and  leBT (Trans E) (Trans bJM) [fseqD]
      - E multi => junction(N) = last two components of E (recursed birth)
"""
import sys, time
sys.path.insert(0, '/home/koteitan/proofs/pss-proof/wt-s4b/python')
from collections import deque
from red_model import Lng, entry, monoT, multiT, zeroT, P, Pcut, oper, diagSeq
from trans_model import Trans

def lessBT(a, b):
    pa, pb = a[1], b[1]
    if not pa: return bool(pb)
    if not pb: return False
    return lessBP(pa[0], pb[0]) or (pa[0] == pb[0] and lessBT(('T', pa[1:]), ('T', pb[1:])))
def lessBP(p, q):
    return p[1] < q[1] or (p[1] == q[1] and lessBT(p[2], q[2]))
def leBT(a, b): return lessBT(a, b) or a == b
def is_prefix(a, b): return len(a) <= len(b) and b[:len(a)] == a

def junction(N):
    if not multiT(N): return None
    c = Pcut(N); bJ = N[c:]
    if bJ == [(0, 0)]: return None
    comps = P(N)
    if len(comps) < 2: return None
    return comps[-2], bJ

seeds = [diagSeq(u, u + d) for u in range(0, 6) for d in range(1, 7)]
seen = set(tuple(s) for s in seeds)
q = deque(seeds)
t0 = time.time()
NMAX = 34
cnt = dict(hosts=0, comple_ok=0, comple_fail=0, pfx_ok=0, pfx_fail=0,
           pfxfail_comple_ok=0, pfxfail_comple_fail=0, deep=0, deep_ok=0)
comple_fails = []; pfx_fails = []
ed = dict(birth=0, birth_pfx_ok=0, birth_pfx_fail=0,
          multi_decomp_ok=0, multi_decomp_fail=0,
          emono=0, emono_ident_ok=0, emono_ident_fail=0,
          emono_fseq_ok=0, emono_fseq_fail=0,
          emulti=0, emulti_ident_ok=0, emulti_ident_fail=0,
          ezeroT=0, zeroparent=0)
birth_fails = []; ident_fails = []; fseq_fails = []
while q and time.time() - t0 < 240:
    M = q.popleft()
    if Lng(M) > NMAX: continue
    for n in range(1, 5):
        try: N = oper(M, n)
        except Exception: continue
        tN = tuple(N)
        if tN in seen: continue
        seen.add(tN); q.append(N)
        j = junction(N)
        if j is None: continue
        bJm1, bJ = j
        cnt['hosts'] += 1
        tb = Trans(bJ); tb1 = Trans(bJm1)
        cok = leBT(tb, tb1)
        p = is_prefix(bJ, bJm1)
        cnt['comple_ok' if cok else 'comple_fail'] += 1
        cnt['pfx_ok' if p else 'pfx_fail'] += 1
        if Lng(N) >= 16:
            cnt['deep'] += 1
            if cok: cnt['deep_ok'] += 1
        if not cok and len(comple_fails) < 5: comple_fails.append((M, n, N, bJ, bJm1))
        if not p:
            if len(pfx_fails) < 3: pfx_fails.append((M, n, N, bJ, bJm1))
            cnt['pfxfail_comple_ok' if cok else 'pfxfail_comple_fail'] += 1
        if zeroT(M):
            ed['zeroparent'] += 1
        elif monoT(M):
            ed['birth'] += 1
            if p: ed['birth_pfx_ok'] += 1
            else:
                ed['birth_pfx_fail'] += 1
                if len(birth_fails) < 5: birth_fails.append((M, n, N, bJ, bJm1))
        else:
            cM = Pcut(M); preM = M[:cM]; bJM = M[cM:]
            try: E = oper(bJM, n)
            except Exception: E = None
            if E is None or N != preM + E:
                ed['multi_decomp_fail'] += 1
                if len(ident_fails) < 5: ident_fails.append(('decomp', M, n, N, E))
                continue
            ed['multi_decomp_ok'] += 1
            if zeroT(E):
                ed['ezeroT'] += 1
            elif monoT(E):
                ed['emono'] += 1
                compsM = P(M)
                okid = (bJ == E and len(compsM) >= 2 and bJm1 == compsM[-2])
                ed['emono_ident_ok' if okid else 'emono_ident_fail'] += 1
                if not okid and len(ident_fails) < 5:
                    ident_fails.append(('emono', M, n, N, bJ, bJm1, E))
                if leBT(Trans(E), Trans(bJM)): ed['emono_fseq_ok'] += 1
                else:
                    ed['emono_fseq_fail'] += 1
                    if len(fseq_fails) < 3: fseq_fails.append((bJM, n, E))
            else:
                ed['emulti'] += 1
                compsE = P(E)
                okid = (len(compsE) >= 2 and bJ == compsE[-1] and bJm1 == compsE[-2]
                        and bJ == E[Pcut(E):])
                ed['emulti_ident_ok' if okid else 'emulti_ident_fail'] += 1
                if not okid and len(ident_fails) < 5:
                    ident_fails.append(('emulti', M, n, N, bJ, bJm1, E))

print("visited=%d  time=%.0fs" % (len(seen), time.time() - t0))
print("hosts (nontrivial multiT junction, NEW nodes): %d" % cnt['hosts'])
print("  comple: ok=%d FAIL=%d   (deep Lng>=16: %d/%d)"
      % (cnt['comple_ok'], cnt['comple_fail'], cnt['deep_ok'], cnt['deep']))
print("  pcompPrefix: ok=%d fail=%d ; on pfx-fail comple ok=%d FAIL=%d"
      % (cnt['pfx_ok'], cnt['pfx_fail'], cnt['pfxfail_comple_ok'], cnt['pfxfail_comple_fail']))
print("edges: %s" % ed)
if comple_fails:
    print("COMPLE FAILS:")
    for e in comple_fails: print("  ", e)
if birth_fails:
    print("BIRTH-PREFIX FAILS (mono parent):")
    for e in birth_fails: print("  ", e)
if ident_fails:
    print("IDENT FAILS:")
    for e in ident_fails: print("  ", e)
if fseq_fails:
    print("FSEQ FAILS (mono component descent):")
    for e in fseq_fails: print("  ", e)
if pfx_fails:
    print("pfx-fail examples:")
    for e in pfx_fails: print("  ", e)
