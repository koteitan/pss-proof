#!/usr/bin/env python3
"""ANALYSIS for the §8 central question: are the annihilation/fseq lemmas applied
ONLY in the clean regime (v_inner=0 ∨ u≥v_inner, i.e. leaf t'=0 OR top-level) or
in the A25/A26-false NESTED regime?

We reconstruct, for each M in (reduced ∩ monoT) reaching the §7.3 Trans recursion
(conditions I-VI), the actual marked-principal shapes consumed by:
  - §8.6 末尾単項の零化可能性  applied as  D_u(t' + D_{w} 0)  (peel D_w 0)
  - §8.7 末尾項の零化可能性    applied as  D_u t'              (annihilate to D_u 0)
at the four Pred_oper0 use-sites (content.md 6028, 6038, 6052, 6056) and the
condition-VI use-site (5747).

For each, we record:
  u            = outer index of the marked principal
  t'           = body being preserved/annihilated
  w            = index of the trailing D_w 0 (for §8.6)   [None for §8.7]
  is_leaf      = (t' == 0_B)                  -> trivially clean (D_u(D_w 0))
  clean_peel   = (w==0) or (u >= w)           -> A25 clean regime for one peel
  nested_pos   = is the marked principal nested strictly inside an outer principal
                 of the host term Trans(M)?  (A26 falsity trigger)
We then evaluate, via buchholz.bracket, whether the actual [0]-orbit realises the
claimed annihilation, on the EXACT terms produced by the Trans recursion.
"""
import sys, itertools
sys.path.insert(0, "/home/koteitan/proofs/pss-proof/python")
sys.path.insert(0, "/home/koteitan/proofs/pss-proof/git/python")
import trans_model as TM
import red_model as rm
from red_model import Lng, entry, P, monoT, parent
import buchholz as B

# ---- bridge: trans_model BT  <->  buchholz term ----
# trans_model BT: ('T', [('D', v, BT), ...]);  0 = ('T',[])
# buchholz term: list of ('D', v, term);       0 = []
def tm_to_buc(t):
    return [('D', p[1], tm_to_buc(p[2])) for p in t[1]]
def buc_to_tm(a):
    return ('T', [('D', v, ('T', buc_to_tm(b)[0:0] or buc_to_tm(b)) ) for (_,v,b) in a]) if False else \
           ('T', [('D', v, buc_to_tm_inner(b)) for (_,v,b) in a])
def buc_to_tm_inner(a):
    return ('T', [('D', v, buc_to_tm_inner(b)) for (_,v,b) in a])

def fmtbuc(a): return B.fmt(a)

# enumerate candidate pair sequences (small), keep reduced ∩ monoT ∩ length>=2
def gen_pairseqs(maxlen, maxval):
    seqs = []
    # build standard-ish sequences: start (0,0), each next within bounds
    def rec(cur):
        if len(cur) >= 2:
            seqs.append(list(cur))
        if len(cur) >= maxlen:
            return
        last = cur[-1]
        for a in range(0, maxval+1):
            for b in range(0, a+1):
                cur.append((a,b)); rec(cur); cur.pop()
    rec([(0,0)])
    return seqs

def domidx_of_principal(p):
    """For buchholz principal p=('D',v,b): the 'dom-index' relevant to clean test.
    The trailing D_w 0 we peel is the LAST principal of the body. Return (u, body)."""
    _, u, b = p
    return u, b

def classify_86(u, tprime_buc, w):
    """§8.6: marked principal D_u(t' + D_w 0). Clean regime per A25: w==0 or u>=w
    OR t'==0 (leaf, always clean since then it's D_u(D_w 0))."""
    is_leaf = (tprime_buc == [])
    clean = is_leaf or (w == 0) or (u >= w)
    return is_leaf, clean

def peel_check_86(u, tprime_buc, w):
    """Empirically: does (D_u(t' + D_w 0))[0] cleanly become D_u t' (single peel)?
    Build the host principal, apply bracket once with z=0, compare to D_u t'."""
    body = tprime_buc + [('D', w, [])]
    host = [('D', u, body)]
    if not B.in_TB(host):
        return None
    got = B.bracket(host, B.ZERO)  # [0]
    want = [('D', u, tprime_buc)]
    return (got == want)

def iter_annihilate_87(u, tprime_buc, maxk=40):
    """§8.7: does D_u t' reach D_u 0 under iterated [0]? (top-level isolated)."""
    host = [('D', u, tprime_buc)]
    if not B.in_TB(host):
        return None
    cur = host; want = [('D', u, [])]
    for k in range(1, maxk+1):
        cur = B.bracket(cur, B.ZERO)
        if cur == want:
            return k
        if cur == []:
            return None
    return None

def main():
    seqs = gen_pairseqs(maxlen=5, maxval=3)
    # filter to the Trans-recursion domain: reduced, monoT, len>=2, PT (single principal Trans)
    rows = []
    seen = 0
    cond_use = {'I/III/V':[], 'II/IV-left':[], 'II/IV-noleft':[], 'VI':[]}
    errors = 0
    for M in seqs:
        try:
            if Lng(M) < 2: continue
            if not TM.reduced(M): continue
            if not monoT(M): continue
            j1 = Lng(M)-1
            jp = parent(M, 0, j1)
            # build the recursion symbols exactly as trans_model does
            t1 = TM.Trans(TM.Pred(M))
            if t1 == TM.ZB:
                continue
            c1 = TM.Mark(TM.Pred(M), TM.Adm(M, jp))
            v = TM.bpHeadV(c1); t2 = TM.bpHeadT(c1)
            # which condition?
            cI = TM.condI(M); cIII = TM.condIII(M); cV = TM.condV(M); cVI = TM.condVI(M)
            # condition II/IV = monoT & j1>0 & t1!=0 & not(I,III,V,VI)
            cIIIV = not (cI or cIII or cV or cVI)
            seen += 1
            m1j1 = entry(M,1,j1); m1jp = entry(M,1,jp)
            t2_buc = tm_to_buc(t2)
            if cI or cIII or cV:
                # §8.6 use-site 6028: marked principal D_v(t2 + D_{m1j1} 0), u=v
                is_leaf, clean = classify_86(v, t2_buc, m1j1)
                peel = peel_check_86(v, t2_buc, m1j1)
                cond_use['I/III/V'].append((M, v, t2_buc, m1j1, is_leaf, clean, peel))
            elif cVI:
                # use-site 5747: c2 = D_v D_{m1j1} 0 (LEAF, t'=0); annihilation of D_v(D_{m1j1}0)
                is_leaf, clean = classify_86(v, [], m1j1)  # t'=0
                peel = peel_check_86(v, [], m1j1)
                cond_use['VI'].append((M, v, [], m1j1, is_leaf, clean, peel))
            elif cIIIV:
                # §8.7 path. Need t2 != 0. Decompose P(t2)_{J1}.
                if t2 == TM.ZB:
                    # c2 = D_v D_{m1jp} D_{m1j1} 0 — handled separately (t2=0 leaf chain)
                    cond_use['II/IV-noleft'].append((M, v, [], m1j1, True, True, None))
                    continue
                Pt2 = TM.PB(t2); J1b = len(Pt2)-1; pj = Pt2[J1b]
                leftDj0 = (TM.bpHeadV(pj) == m1jp)
                if leftDj0:
                    t4 = TM.bpHeadT(pj)
                    t4_buc = tm_to_buc(t4)
                    # use-site 6038: §8.6 on D_{m1jp}(t4 + D_{m1j1} 0), u=m1jp
                    is_leaf, clean = classify_86(m1jp, t4_buc, m1j1)
                    peel = peel_check_86(m1jp, t4_buc, m1j1)
                    cond_use['II/IV-left'].append((M, m1jp, t4_buc, m1j1, is_leaf, clean, peel))
                else:
                    # use-site 6052: §8.7 on D_{m1jp}(t2 + D_{m1j1} 0) -> D_{m1jp} 0, top-level lift
                    # the marked principal annihilated to 0 is D_{m1jp}(t2 + D_{m1j1}0)
                    body = t2_buc + [('D', m1j1, [])]
                    is_leaf = (body == [])
                    kk = iter_annihilate_87(m1jp, body)
                    # also 6056: §8.6 on D_{m1jp}(t2 + D_{m1j1}0) wait -> D_{m1jp} t2 ... we record body
                    cond_use['II/IV-noleft'].append((M, m1jp, body, m1j1, is_leaf, (kk is not None), kk))
        except Exception as e:
            errors += 1
            if errors <= 5:
                print("ERR", M, repr(e))
    print(f"scanned reduced∩monoT∩(t1!=0) hosts: {seen};  errors: {errors}")
    print()
    for k, rs in cond_use.items():
        if not rs:
            print(f"[{k}] (no instances in sample)")
            continue
        nleaf = sum(1 for r in rs if r[4])
        nclean = sum(1 for r in rs if r[5])
        npeelok = sum(1 for r in rs if r[6] is True or (isinstance(r[6], int) and r[6] is not None and r[6] is not False))
        print(f"[{k}] n={len(rs)}  leaf(t'=0)={nleaf}  clean_regime={nclean}  empirically_realised={npeelok}")
        # show any NON-clean instance (the dangerous case)
        dirty = [r for r in rs if not r[5]]
        for r in dirty[:8]:
            M, u, tb, w, isl, cl, pk = r
            print(f"    NON-CLEAN host M={M} u={u} t'={fmtbuc(tb)} w={w} peel/iter={pk}")
        # also show a few representative clean ones with non-trivial t'
        nontriv = [r for r in rs if not r[4]][:4]
        for r in nontriv:
            M, u, tb, w, isl, cl, pk = r
            print(f"    t'!=0 host M={M} u={u} t'={fmtbuc(tb)} w={w} clean={cl} realised={pk}")

if __name__ == "__main__":
    main()
