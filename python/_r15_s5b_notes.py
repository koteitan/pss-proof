#!/usr/bin/env python3
"""r15-S5b NOTES — §8.5 condV scb-decomposition route COMPLETED (adm regime).

===============================================================================
WHAT WAS PROVEN (green build pss-r15-S5b, layerC/pss_scratch.thy, sorry 0)
===============================================================================
All under M in ST_PS cap PT_PS, transCondV M, adm M (transJ0 M); j1 > 1,
hasParent M 1 j1 and t1 != 0 are DERIVED from condition (V) (s85b_condV_bridge,
s85b_condV_setup — the row-1 parent existence is proven outright: j0 witnesses
M1j0 < M1j1 with (0,j0) <=M (0,j1), maximality via s84c1_anc_le_j0).
e := entry M 1 (transJ0 M) (= M_{1,j-1} since jm1 = j0 in the adm case).

1. m_8_5_scbdec_t2_nonzero_condV   : t2 != 0  (condV ONLY, no adm needed;
     via m_7_3_Mark_rightmost1: t2 = 0 would force jm1 = j1 - 1, but
     jm1 <= j0 < j1 - 1 under condV).
2. m_8_5_scbdec_Np_condV_adm       : Trans N' = c2 = D_e(t2 + D_{M1,j1} 0)
     [adm-analog of 各種scb分解 (2) slice leg].  KEY: the sorry'd
     p_8_2_condV_terminal_slice_Trans is NOT needed — in the adm case the
     N'-slice IS the basepoint slice, and m_7_4_Mark_Trans_repr +
     m_7_3_Mark_rightmost2 give Trans N' = Mark M jm1 = c2 directly.
3. m_8_5_scbdec_PredNp_condV_adm   : Trans (Pred N') = c1 = D_e t2
     [adm-analog of part (3); repr applied to Pred M at jm1 = j0].
4. m_8_5_scbdec_Lp_condV_adm       : Trans L' = D_e(t2 + D_e 0)
     [L-replacement leg; m_8_4_rightend_Trans (round-14, A30 form) pair pinned
     against the lifted producer pair via m_7_2_scb_unique_sb, core read back
     through m_7_2_add_scb_conj2].
5. s85b_L1_decomp_adm              : the tower base — any (s,b) decomposing
     Trans(Pred M) at c1 also decomposes Trans(L_1) at D_e(t2 + D_e 0).
     L_1 shares Pred/j0/jm1/c1 (hence the surgery wrappers) with M; its c2
     evaluates via Mark machinery on L_1 itself (basepoint slice of L_1 = L').
     Replaces the article's cond-(II)/(IV) analysis (which is the non-adm
     route) by pure Mark bricks.
6. m_8_5_scbdec_adm_forms          : MASTER closed forms, one witness tuple
     (s0,s1,b0,b1) for ALL n (adm-analogs of parts (4)/(5), A29-corrected
     exponents n / n-1; plus the A24-corrected fseq form and the kind-1 fact):
       flat(Trans L_n)   = s1 [D_e] X^n [Z] b0^n b1          (n >= 1)
       flat(Trans M[n])  = s1 [D_e] X^(n-1) flat(t2) b0^(n-1) b1
       flat(Trans(M)[n]) = s1 [D_e] X^n [D_e] [Z] b0^n b1    (all n)
     with X = s0 @ [D_e].  Induction engine: m_8_4_oper_props_5 (round-14)
     with the pair pinned by m_7_2_scb_unique_sb at every step; the C-2 zeroT
     guard is automatic under condV (Lng(Pred N') >= 2).
7. m_8_5_scbdec_oper_general_condV_adm : 基本列のscb分解 for ALL n (= Suc k),
     A28-corrected, as EX1 of a common pair (S,B):
       (S, D_e t2,                 B) decomposes Trans(M[n])
       (S, D_e(t2 + D_e(D_e 0)),   B) decomposes Trans(M)[m_n+1], m_n+1 = n
       (S, D_e(t2 + D_e t2),       B) decomposes Trans(M[n+1])
     (the article's core t2 + D_e 0 at index m_n is the A24-inherited
     over-wrap, refuted 0/40 in round 14).
8. m_8_5_scbdec_exchange1_condV_adm : STRICT corrected exchange (1), ALL n>=1:
       Trans(M[n]) < Trans(M)[n]        (unconditional)
9. m_8_5_scbdec_exchange2_condV_adm : exchange (2), ALL n >= 1, UNCONDITIONAL:
       Trans(M[n]) < Trans M
     NOT via [Buc1] 3.2 (which needs the OPEN pillar Trans M in OT_B): the
     nested tower s85b_W (W_0 = D_e c, W_{k+1} = D_e(t2 + W_k)) satisfies
     Trans(M[n]) = s1 W_{n-1} b1 and W_k < c2 = D_e(t2 + D_{M1,j1} 0) at every
     height because e < M1,j1 (condition (V)); scbext_lessBT closes.
10. m_8_5_scbdec_exchange3_condV_adm : exchange (3) leBT form, ALL n:
       Trans(M)[n] <= Trans(M[n+1])   under residual t2lb: leBT (D_e 0) t2;
     equality holds EXACTLY at t2 = D_e 0 (flat strings coincide).
11. m_8_5_scbdec_exchange3_strict_condV_adm : exchange (3) STRICT, ALL n,
     under the article-form residual HB (see RESIDUALS below);
     t2 != 0 (proven) + e < M1,j1 make HB imply D_e 0 < t2 strictly
     (s85b_complb_lessBT, pure BT-order lemma).
12. m_8_5_Trans_oper_exchange_condV_adm : the packaged article-facing triple
     (assumptions of p_8_5_Trans_oper_exchange + adm M j0):
       (1') Trans(M[n]) < Trans(M)[numBT n]      [strict, corrected index]
       (2)  Trans(M[n]) < Trans M                 [unconditional]
       (3') HB ==> Trans(M)[numBT n] < Trans(M[n+1])

===============================================================================
RESIDUALS (named, NOT cited — honest gaps)
===============================================================================
* HB (exchange (3) only): every monomial component of t2 is >= D_{M1,j1} 0,
    Isar: ALL c : set (PB (transT2 M)). leBT (Dpt (enat (entry M 1 (transJ1 M))) 0_B) c
  This is the adm-analog of the DEFERRED part (3) of p_8_5_Joints_FirstNodes
  _basic (article states it for non-adm; t2 was unexposed then — now it IS
  exposed as transT2).  Empirical: 53/53 genuine instances (two seeds).
  Discharge route (next front): components of t2 = bpHeadT(Mark (Pred M) j0)
  are indexed by row-1 children of j0, whose entries exceed M1,j0 = M1,j1 - 1;
  the bricks would be an adm analogue of m_8_4_rightmost_nonadm_ancestor
  feeding m_8_2_subexpr_component_strongmono_uncond, or a Mark-body structure
  lemma ("heads of Mark-body components = entries of next basepoints").
* Trans M in OT_B (the §8.7 pillar) is NOT needed anywhere in this block
  (exchange (2) avoided it) — it remains open only for the §8.7 endgame.
* Non-adm condV: the article's 各種scb分解 lemma (i) as printed (non-adm j0)
  remains unproven; that regime is UNREACHABLE in genuine ST_PS as far as
  search goes (r14: 0/20049; this round: 0 sightings in both runs).  Vacuity
  on ST_PS is NOT proven — only empirically supported.

===============================================================================
COVERAGE (GENUINE regime = ST_PS via oper-BFS from diagSeq seeds, real filters:
monoT, reduced (SIGALRM-guarded), condV, adm j0, j1 > 1; timeouts counted)
===============================================================================
Run 1 (python/_r15_s5b_adm_check.py, seed 20260702, 600 s):
  16 distinct genuine instances (9 partial-timeouts), 0 non-adm sightings.
  C1(hp1/jm1/jm2) C2 C3 C4 T2(ne/comps/leBT) pair-uniqueness: 16/16 each.
  C5/C6/C7 (closed forms) and E1/E2/E3le/E3strict-iff, n in {1,2,3,4}:
  48/48 instance-n pairs (16+15+10+7), all 100%.
Run 2 (python/_r15_s5b_adm_check2.py, seed 777, wider: maxlen 16, seeds<4,
  n<=4, 650 s): 42 instances (37 fully validated, 37 partial-timeouts),
  0 non-adm sightings.  Same claims: 37/37; n-indexed: 57/57 instance-n pairs
  (26+17+9+5), all 100%.
TOTAL: 53 fully-validated distinct genuine instances, 105/105 instance-n
pairs; every proven statement and both residuals 100%; the A28-refuted printed
pairing was NOT re-tested here (see round-14 notes: 0/40, ">" holds).

===============================================================================
DEAD ENDS / PITFALLS (Isabelle, this round)
===============================================================================
* List-block algebra: after simp's DEFAULT head expansion
  concat (replicate (Suc k) xs) = xs @ concat (replicate k xs), the rotation /
  block-commutation identities are needed in Cons/append NORMAL FORM, or simp
  cannot fire them inside larger strings.  s85b_rot ("a # concat(rep k (s@[a]))
  = ...") NEVER fires in context — use the tailed variants s85b_rot_cons,
  s85b_crep_comm_cons, s85b_crep_comm_snoc/snoc0 (all proven by
  (induction m) auto).  This killed 3 proof sites in the first builds.
* the_equality[OF wit] has a higher-order unification ambiguity on ?P ?a —
  instantiate P explicitly (the_equality[of "%j0. nextR L1 0 j0 ..." "..."]).
* unflatBT readback: never simp the equation flatBT t = flatBT (Dpt v X)
  before applying unflatBT_flat (simp unfolds the RHS flat and the pattern
  unflatBT (flatBT _) is gone).  Use arg_cong[OF feq, of unflatBT] then
  (simp only: unflatBT_flat).
* zeroT/length: simp does not know Lng M - 1 != 1 from 2 < Lng M (nat monus);
  supply it by arith.  Length lower bounds of flat strings: route through
  flatBP_len_ge2 explicitly, "using f1 by simp" does NOT see them.
* s84c1_nextrel1_dir via [OF ..., of ...] positional instantiation is fragile;
  build the bc/A premises as named facts and give a full OF chain.
* A previous interrupted session of this front left a complete draft in the
  session scratchpad (s5b_block.thy); it was audited, corrected (5+4 build
  errors, all in the pitfall classes above), strengthened (exchange (2)
  de-conditionalized from TOT via the s85b_W tower; strict exchange (3) +
  packaged wrapper added), and integrated.

===============================================================================
NEXT (for the parent / next round)
===============================================================================
* Discharge HB (the last conditional piece of the §8.5 condV exchange):
  Mark-body component structure lemma, see RESIDUALS.
* Wire exchange (1)/(2) into the §8.7 dispatcher's exchV hypothesis
  (python/_r14_f7_notes.py checklist) — the adm-condV case is now closed;
  the dispatcher's condV leg needs exactly conclusions (1)(2) at the shifted
  index (check the exact exchV shape before wiring).
* §8.4 counterpart m_n bookkeeping (p_8_4_Trans_oper_exchange) likely inherits
  the same A24/A28 shift — still un-rechecked (different cond regime).
"""
