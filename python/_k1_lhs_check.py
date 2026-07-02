#!/usr/bin/env python3
"""Empirical check of the kind-1 LHS context-nesting bound (residual for
m_8_4 / m_8_5 exch lhs):  for condIII/condV standard M,
    EX j. leBT (Trans(M[m])) (operB (Trans M) (numBT j)).
Verify which j works (claim: j=m or smaller), and that the context is shared
(Trans(M[m]) vs operB(...)(numBT j) differ only at the deepest leaf).
"""
import sys
sys.path.insert(0, "/home/koteitan/proofs/pss-proof/python")
import trans_model as tm
import red_model as rm
import buchholz as B

# --- bridge trans_model ('T',[('D',v,('T',body))]) <-> buchholz [('D',v,body)] ---
def conv(t):
    # t = ('T', ps)  ->  list of buchholz principals
    return [conv_bp(p) for p in t[1]]
def conv_bp(p):
    _, v, body = p
    return ('D', v, conv(body))

def oper(M, n):  return rm.oper(M, n)

def leBT(a, b):  # buchholz le_term
    return B.le_term(a, b)

def gen_monoT(maxlen=5, maxval=3):
    """DFS-generate reduced monoT pairseqs rooted at (0,0), with pruning."""
    seqs = []
    pairs = [(a,b) for a in range(maxval+1) for b in range(a+1)]  # entry0>=entry1
    def rec(M):
        if len(M) >= 4 and rm.monoT(M) and tm.reduced(M):
            seqs.append(list(M))
        if len(M) >= maxlen: return
        for p in pairs:
            M.append(p)
            # cheap prune: keep reduced-prefix-ish (monoT requires le0(0,last))
            if not rm.zeroT(M):
                rec(M)
            M.pop()
    rec([(0,0)])
    return seqs

def in_OTB(tt):
    a = conv(tt)
    return B.in_TB(a) and B.in_OT(a)

def main():
    found = {'III':0, 'V':0}
    examples = {'III':[], 'V':[]}
    seqs = gen_monoT()
    print(f"generated {len(seqs)} reduced monoT seqs")
    for M in seqs:
        for cname, cond in [('III', tm.condIII), ('V', tm.condV)]:
            if not cond(M): continue
            try:
                TM = tm.Trans(M)
            except Exception:
                continue
            if not in_OTB(TM): continue
            TMb = conv(TM)
            if TMb == []: continue
            # for several m, find matching j
            row = []
            ok_all = True
            for m in range(2, 6):
                try:
                    Mm = oper(M, m)
                    TMm = conv(tm.Trans(Mm))
                except Exception:
                    row.append((m, None)); ok_all=False; continue
                jmatch = None
                for j in range(0, 12):
                    rhs = B.bracket(TMb, B.nat(j))
                    if leBT(TMm, rhs):
                        jmatch = j; break
                row.append((m, jmatch))
                if jmatch is None: ok_all = False
            found[cname] += 1
            if len(examples[cname]) < 6:
                examples[cname].append((M, row, ok_all))
    for c in ('III','V'):
        print(f"\n=== cond{c}: {found[c]} standard hosts ===")
        for (M, row, ok) in examples[c]:
            print(f"  M={M}  ok={ok}  (m->j): {row}")

if __name__ == '__main__':
    main()
