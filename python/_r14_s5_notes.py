#!/usr/bin/env python3
"""r14-S5 NOTES — §8.5 deferred scb-decomposition lemmas (article route).

===============================================================================
WHAT WAS PROVEN (green, layerC/pss_scratch.thy, prefix m_8_5_scbdec_)
===============================================================================
1. m_8_5_scbdec_c1_shape      : transV M = enat M_{1,jm1}; transC1 M = D_u(t2);
                                t2 in T_B; jm1 < Lng M - 1.  (condA-free.)
2. m_8_5_scbdec_c2_condV      : ARTICLE (i) part (1), TRANSCRIBED+PROVEN as EX1:
                                unique (s'1,b'1) with (D_{M1,jm1} s'1, D_{M1,j1} 0, b'1)
                                an scb-decomposition of c2 = transC2 M.  Only condV
                                is needed (not the article's extra non-adm j0 guard).
3. m_8_5_scbdec_c2_sb_subst   : the workhorse 加法とscb分解 readback: for THE pair
                                and any w, t' in T_B:
                                (s'1, D_w t', b'1) decomposes t2 +B D_w t'
                                (article identity s'1 D_w t' b'1 = t2 + D_w t').
4. m_8_5_scbdec_fseq_condV    : A24-CORRECTED closed form, ALL n:
                                flat(Trans(M)[n]) = s1 D_{M1,jm1} (s0 D_{M1,j0})^n
                                                    D_{M1,j0} 0 b0^n b1
                                + kind-1 of Trans M at c2 for the SAME (s1,b1) that
                                decomposes Trans(M[1]) at D_{M1,jm1}(t2)  (base).
                                NOTE the bare innermost D_{M1,j0} (ONE FEWER s0-wrap
                                than the article formula) — A24 inherited into §8.5.
5. m_8_5_scbdec_oper1_core_condV : the corrected 基本列のscb分解 n=1 core pair:
                                same (s1,b1);
                                (s1, D_u t2, b1)                      of Trans(M[1])
                                (s1, D_u(t2 + D_{j0}(D_{j0} 0)), b1)  of Trans(M)[1]
6. m_8_5_scbdec_exchange1_n1_condV : CAPSTONE, corrected exchange (1) instance:
                                lessBT (Trans (M[1])) (operB (Trans M) (numBT 1))
                                — strict, via scbext_lessBT + lessBT_addBT_self.

===============================================================================
REFUTATIONS (correction candidates; parent should add to corrections.md)
===============================================================================
A28 candidate — §8.5 命題（条件(V)の下でのTransと基本列の交換関係） conclusion (1)
  and 補題（条件(V)の下での基本列のscb分解） part (2) inherit A24: FALSE as printed.
  * p_8_5_Trans_oper_exchange (pss_paper.thy) conclusion (1)
      leBT (Trans (M[n])) (operB (Trans M) (numBT m_n)),  m_n = n-1 (adm) / n (nonadm)
    is empirically FALSE on genuine ST_PS condV instances: 0/40 instance-n pairs
    (in fact ">" holds).  With the SHIFTED index m_n + 1 (adm: n / nonadm: n+1) the
    inequality holds STRICTLY 40/40.  Conclusion (3) holds at both indices
    (article 40/40, shifted 40/40 strictly).  Conclusion (2) unaffected (40/40).
  * The (ii) part (2) core is NOT D_u(t2 + D_{M1,j0} 0) at m_n; the observed core at
    the (s'0,b'0) position of Trans(M)[m_n + 1] is
        D_u(t2 + D_{M1,j0}(D_{M1,j0} 0))          (40/40)
    i.e. the part-(3) shape with t' := D_{M1,j0} 0.  (At the article's m_n the
    observed core is D_u(D_{M1,j0} 0) — t2 is NOT preserved: the xseq tower
    restarts from the bare basis, exactly the A24 mechanism.)
  * Root cause: 命題（scb分解と基本列の関係）(2) over-wraps (A24, already recorded);
    the §8.4/§8.5 downstream m_n bookkeeping must shift by one.
    LIKELY SAME ISSUE in §8.4: p_8_4_Trans_oper_exchange / p_8_4_oper_basic use
    numBT (n-1) / numBT n — NOT rechecked this round (different cond regime).
  * Smallest counterexample: M = [(0,0),(1,1),(1,1)] (ST: diagSeq 0 1 → oper...),
    n = 1, adm j0=0, m_1 = 0:
      Trans(M[1])  = D_0(D_1 0)
      Trans(M)[0]  = D_0(D_0 0)          <  Trans(M[1])   (article (1) fails)
      Trans(M)[1]  = D_0(D_1 0 + D_0(D_0 0)) > Trans(M[1]) (shifted (1) holds)

A29 candidate — 補題（条件(V)の下での各種scb分解） part (5) exponent at n = 1 [軽微]:
  statement says Trans(M[n]) = s1 D_{jm1} (s'1 D_{j0})^n t2 (b'1)^n b1 uniformly, but
  M[1] = Pred M gives Trans(M[1]) = s1 D_{jm1} t2 b1 (exponent 0); the article's own
  proof derives the n=1 case with exponent "2n-2" = 0, contradicting the statement's
  n.  Empirical: exponent-n form at n=1 matched 0/48; exponent-0 matched 48/48 (on
  the wider RT∩PT nonadm-condV regime; domain-free string-length argument shows the
  n=1 exponent-n form is impossible whenever (s'1,b'1) exists).  The proof's "2n"
  in part (4)'s induction header is likewise a typo for "n+1" (the induction step
  produces n+1).  For n >= 2 the stated forms matched on the standard-consistent
  subset (25/48; the 23 failures are OUTSIDE the stated ST_PS domain, see below).

===============================================================================
COVERAGE (genuine regime = ST_PS via oper-BFS from diagSeq seeds, real filters)
===============================================================================
* Lemma (ii) checks (python/_r14_s5_scbdec.py, 6 seeds, 420 s):
    16 distinct genuine ST_PS instances with condV & j1>1 & t1/=0 (ALL adm-j0),
    x n in {1,2,3} => 40 instance-n pairs (timeouts excluded):
      exch1(article m_n)   0/40 FALSE | exch1(m_n+1) strict 40/40
      exch2                40/40      | exch3(art) 40/40 | exch3(m_n+1) strict 40/40
      (1)-existence 40/40, uniqueness-of-(u,s,b) 40/40
      (2corr)-core  40/40  | (3)-shape 40/40 | (3) t' = t2 (adm) 40/40
* NON-adm condV in ST_PS: NOT REACHED — 0 instances in 20049 distinct genuine
  ST_PS members (BFS, maxlen 18, seeds diagSeq u..u+k, u<3, k<4, n<=4;
  python/_r14_s5_nonadm_hunt.py).  The lemma (i) regime is rare-or-empty in
  reachable ST_PS; its parts (2)-(5) therefore remain UNVALIDATED on the genuine
  regime (validated only on the wider RT∩PT regime below).
* Wider RT∩PT regime (exhaustive reduced monoT, Lng<=6, row0<=3/row1<=2, NOT
  necessarily standard; 48 nonadm-condV instances):
    (i)(1) head+uniqueness 48/48  (matches the PROVEN m_8_5_scbdec_c2_condV)
    (i)(2a) 25/48, (2b) 25/48, (3) 25/48  — the 23 failures are non-standard
    hosts (outside the lemma's ST_PS domain); on the 25 standard-consistent ones
    (2)(3)(4 n=1,2)(5 n=2,3) all hold with (4)-exponent n+1 / (5)-exponent n.
    (5)@n=1: exponent-0 (48/48), never exponent-1 (see A29).
* Proven closed form direct check (m_8_5_scbdec_fseq_condV vs python operB):
    ST_PS condV:  384/384 over 96 genuine instances, n = 0..3
    RT∩PT condV: 2295/2295 over 765 exhaustive instances (incl. ALL 48 nonadm),
                 n = 0..2 — the closed form needs only condV, matching the
                 Isabelle statement's generality (no adm/nonadm split).

===============================================================================
UNPROVEN DRAFTS (validated shapes; removed from .thy per no-sorry discipline)
===============================================================================
Lemma (i) 各種scb分解 (condV, non-adm j0), CORRECTED draft:
  For M in ST_PS ∩ PT_PS, n >= 1, transJ1 M > 1, transCondV M, ~adm M (transJ0 M),
  with the THE-pair sb from m_8_5_scbdec_c2_condV, s'1 = fst sb, b'1 = snd sb,
  and (s1,b1) the base pair of m_8_5_scbdec_fseq_condV:
  (2) scb_decomp (Trans (seg M (transJ0 M) (transJ1 M)))
        (Dsym (enat (entry M 1 (transJ0 M))) # s'1)
        (flatBT (Dpt (enat (entry M 1 (transJ1 M))) 0_B)) b'1
   /\ scb_decomp (Trans (seg M (transJ0 M) (transJ1 M - 1)
                          @ [(entry M 0 (transJ1 M), entry M 1 (transJ0 M))]))
        (Dsym (enat (entry M 1 (transJ0 M))) # s'1)
        (flatBT (Dpt (enat (entry M 1 (transJ0 M))) 0_B)) b'1
  (3) Trans (seg M (transJ0 M) (transJ1 M - 1))
        = Dpt (enat (entry M 1 (transJ0 M))) (transT2 M)
  (4) flatBT (Trans ((M[n]) @ [(entry M 0 (transJ0 M)
          + n * (entry M 0 (transJ1 M) - entry M 0 (transJ0 M)),
          entry M 1 (transJ0 M))]))
        = s1 @ [Dsym v] @ concat (replicate (n+1) (s'1 @ [Dsym j0e])) @ [Zsym]
          @ concat (replicate (n+1) b'1) @ b1
  (5) for n >= 2:
      flatBT (Trans (M[n]))
        = s1 @ [Dsym v] @ concat (replicate n (s'1 @ [Dsym j0e]))
          @ flatBT (transT2 M) @ concat (replicate n b'1) @ b1
      (n = 1: exponent 0 — A29.)
  BLOCKERS for a proof: (2) needs 条件(V)の下での終切片とTransの関係 (article 3664,
  unproven; the jm1->j0 head-shift across the slice) and 右端の置き換えとTransの関係
  (article 4265, unproven); (3) needs Red/Pred commutation on the slice + the same
  end-slice lemma; (4)(5) are induction on n over (2)(3) + the L_1-conditions
  analysis (article: L_1 satisfies cond II or IV).  None of these have m_* bricks
  yet; they are the natural next fronts (each is a §8.3/§8.4-sized lemma).

Lemma (ii) 基本列のscb分解, CORRECTED draft (m_n' := n if adm M j0 else n+1):
  unique (u, s'0, b'0, t') with t' in T_B:
  (1) scb_decomp (Trans (M[n]))  s'0 (flatBT (Dpt (enat u) (transT2 M))) b'0
  (2) scb_decomp (operB (Trans M) (numBT m_n')) s'0
        (flatBT (Dpt (enat u) (transT2 M
           +B Dpt (enat j0e) (Dpt (enat j0e) 0_B)))) b'0        [CORRECTED core]
  (3) scb_decomp (Trans (M[n+1])) s'0
        (flatBT (Dpt (enat u) (transT2 M +B Dpt (enat j0e) t'))) b'0
  with u = M_{1,jm1} if (adm j0 & n=1) else M_{1,j0};
       t' = t2 (adm) / t2 +B D_{j0} t2 (non-adm).
  PROVEN INSTANCE: n = 1 adm-case (1)+(2) = m_8_5_scbdec_oper1_core_condV; the
  Buchholz side (2) is proven for ALL n via m_8_5_scbdec_fseq_condV — the general
  (1)/(3) need the Trans-side closed forms ((i)(5) / §8.4 counterpart), which are
  the remaining wall.

DEAD ENDS / PITFALLS hit this round:
* The article kind-1 fseq formula (n+1 wraps) is not just "an A24 detail": it
  flips the DIRECTION of exchange (1) at the printed m_n.  Any §8.5 route that
  consumed p_8_5_Trans_oper_exchange conclusion (1) as stated would be unsound.
* operB python model: the (].4)(ii) branch must use tbvIdx (x_0 = D_{tbvIdx} 0,
  A23 form) — modelling it as the original [Buc1] footnote or as rule-(i)
  at u = v gives DIFFERENT values on multi-component bodies.
* trans_model scb_decomps returns at most 1 pair (uniqueness) — confirmed 100%.
"""
