#!/usr/bin/env python3
"""r14-S4a (front S4, stage 1): faithful Isar statements + empirical validation
for the six deferred §8.4 scb-cluster lemmas (content.md 4233-4999; deferral
notes pss_paper.thy:1942-1996).

STATUS: all six lemmas STATED and TYPECHECKED (build green with `oops`, then
stripped; the s84x_ definitions stay in layerC/pss_scratch.thy).  This file is
the canonical record: exact Isar text, per-part validation fractions over the
GENUINE regime, the two corrections found, and per-lemma dependency notes.

======================================================================
GENUINE REGIME (all runs)
======================================================================
ST_PS pool built from its inductive definition (pss_defs.thy:439):
diagSeq u v seeds (u<=2, v<=u+4..7) closed under M[n], n in 1..4(..5),
random exploration order.  Per-instance SIGALRM guard (Trans under condition
(IV) duplicates t2, term size is exponential in depth: timeouts/size-skips
counted, never silently dropped).  Filters are the lemmas' own hypotheses.
Runs:
  A: seed 1, maxLng 15 pool 3000, 480s  -> base 356 (III 155, IV 0, V 63,
     VI 138), timeouts 22
  B: condIV-dedicated (seed 7 deep mine): 40..42 condition-IV instances
     (Lng 4..20), timeouts 17 (all in the L2(3)/L2(5)/L3 Trans blowups)
  C: L6-dedicated (III or IV) & jm3<jm1: 200 instances (all III)
  D: L3 wide-domain (random reduced&monoT beyond ST): 36 instances
  E: deep mine for condIV & jm3<jm1: 24k+65k standard seqs explored, 0 found
     (all condIV instances found have j0 = jm2+1 with jm2 admissible, so
      jm3 = jm1; the L6 condition-IV branch may be VACUOUS on ST_PS)

Symbols: j1 = Lng M - 1, j0 = transJ0 M = parent M 0 j1,
jm1 = transJm1 M = Adm M j0, jm2 = s84x_jm2 M = parent M 1 j1 (guarded by
hasParent M 1 j1), jm3 = s84x_jm3 M = Adm M jm2, N = s84x_N M = seg M jm3 j1,
N' = s84x_Np M = seg M jm2 j1, L' = s84x_Lp M, L_n = s84x_L M n,
s1/b1 = s84x_s1/s84x_b1 (THE-exposure of the Trans-recursion scb strings).

======================================================================
CORRECTIONS FOUND (2) — candidate ids for corrections.md (parent assigns)
======================================================================
[C-1] L1 補題（条件(III)～(V)の下での右端の置き換えとTransの関係) part (3)
  (content.md 4273) is FALSE as written.  Literal claim: under j-2 < j0 and
  j0 non-M-admissible, (s, D_{M1,j0}(t2 + D_{M1,j0} 0), b) is an
  scb-decomposition of Trans(L').  REFUTED 0/40 on ALL condition-IV
  instances; a length argument shows it cannot share (s,b) with part (1).
  Minimal recorded CEX: M = (0,0)(1,1)(2,2)(3,1)(4,0)(5,1)(6,2)(6,1)
  (j1=7, j0=5, jm2=jm1=4): actual c between s and b is [D_0, Z]
  = flat(D_{M1,jm2} 0), NOT the literal c.  CORRECT conclusion = part (2)'s,
  unconditionally: (s, D_{M1,j-2} 0, b) is an scb-decomposition of Trans(L')
  — exactly the proof's own concluding sentence in BOTH cases (content.md
  4371 and 4387).  The transcribed m_8_4_rightend_Trans merges (2)/(3) into
  this single unconditional conjunct.  Corrected form: 40/40 (case IV)
  + 204/204 (case A = III/V).
[C-2] L2 補題（条件(III)～(VI)の下での展開規則の基本性質) part (5-3)
  (content.md 4407) is FALSE when zeroT(Pred N') (equivalently: condition
  (VI) with entry M 1 jm2 = 0; then jm2 = j1-1, M[n] = L_{n-1}, and
  Trans(Pred N') = 0_B is not a principal-term string, so NO scb
  decomposition marks it).  CEX: M = (0,0)(1,1)(2,0)(3,1), n=2:
  Trans(M[2]) = flat D0 D1 D0 D0 0; required c = flat(0_B) = [Z] fails
  isPTB_str.  Literal (5) refuted in 92/92 zeroT-regime attempts
  (L2_5zt_refut); parts (5-1),(5-2) survive there (642/642).  CORRECTION:
  guard (5-3) with "~ zeroT (Pred N')".  Guarded form: 550/550 (+46/46 on
  condition IV, run B).  Root cause: the proof's Mark-Trans representation
  step needs the marked slice nonzero (same guard as m_7_4_Mark_Trans_repr).

======================================================================
VALIDATION FRACTIONS (per part; run A + run B + run C + run D)
======================================================================
L1 m_8_4_rightend_Trans     (domain: ST&PT, hasParent, jm2+1 < j1)
  (1) existence+uniqueness of (s,b):  204/204 (A) + 40/40 (B)  = 244/244
  (2) [merged 2/3, corrected]:        204/204 (A) + 40/40 (B)  = 244/244
  (3) literal:                        0/40 (B)   REFUTED  [C-1]
L2 m_8_4_oper_props_*       (domain: ST&PT, hasParent, j1 > 1)
  (1): 356/356 (A) + 40/40 (B); (2) n=1..3: 1056/1056 (A) + 118/118 (B)
  (3): 334/334 (A) + 23/23 (B);  (4): 334/334 (A) + 23/23 (B)
  (5) corrected, n=2,3: (5-1&5-2 unique pair) 642/642 (A) + 46/46 (B);
      (5-3 guarded) 550/550 (A) + 46/46 (B); literal refuted 92/92 [C-2]
L3 m_8_4_Trans_scb          (domain: RT&PT, j1>1, hasParent)
  334/334 (A, standard) + 23/23 (B) + 36/36 (D, beyond-ST reduced&mono)
L4 m_8_4_slice_scb          (domain: ST&PT, hasParent, ~VI, Adm(jm2)=jm1)
  uniqueness 62/62+23/23; (1) 85/85; (2) 85/85; (3) 85/85
L5 m_8_4_various_scb_IIIV   (L4 domain + (jm2<j0 or adm j0))
  (1)(2)(3) 43/43+23/23 = 66/66 each; (2b: Trans L') 66/66;
  (4) n=1..3: 126/126+69/69 = 195/195; (5) n=1..3: 195/195;
  s1/b1 THE-witness unique: 66/66
L6 m_8_4_various_scb_IIIIV  (ST&PT, hasParent, j1>1, III|IV, jm3<jm1)
  (1) 142/142 (A) + 200/200 (C) = 342/342; (2) 342/342; (3) 342/342;
  (4a,4b,4c) 342/342 each; (5) n=1..3: 407+496 = 903/903; (6) 903/903.
  CAVEAT: all instances are condition III; condIV & jm3<jm1 not found in
  ~89k genuine standard sequences (possibly vacuous) — IV-branch unvalidated.

Empirical strengthening observed everywhere: the ∃!-witness is already
pinned by the FIRST scb-decomposition conjunct alone (scb uniqueness in
(s,b) given c, m_7_2_scb_unique_sb); the remaining conjuncts hold for that
witness.  Provers can use this shape: prove existence for conjunct 1, get
uniqueness from m_7_2_scb_unique_sb, then verify the rest.

======================================================================
EXACT ISAR TEXT (typechecked verbatim against layerC heap, build
pss-r14-S4a build1; definitions committed in layerC/pss_scratch.thy)
======================================================================

definition s84x_jm2 :: "pairseq \\<Rightarrow> nat" where
  "s84x_jm2 M = parent M 1 (Lng M - 1)"

definition s84x_jm3 :: "pairseq \\<Rightarrow> nat" where
  "s84x_jm3 M = Adm M (s84x_jm2 M)"

definition s84x_N :: "pairseq \\<Rightarrow> pairseq" where
  "s84x_N M = seg M (s84x_jm3 M) (Lng M - 1)"

definition s84x_Np :: "pairseq \\<Rightarrow> pairseq" where
  "s84x_Np M = seg M (s84x_jm2 M) (Lng M - 1)"

definition s84x_Lp :: "pairseq \\<Rightarrow> pairseq" where
  "s84x_Lp M = seg M (s84x_jm2 M) (Lng M - 2)
               @ [(entry M 0 (Lng M - 1), entry M 1 (s84x_jm2 M))]"

definition s84x_L :: "pairseq \\<Rightarrow> nat \\<Rightarrow> pairseq" where
  "s84x_L M n = (M::pairseq)[n]
               @ [(entry M 0 (s84x_jm2 M)
                     + n * (entry M 0 (Lng M - 1) - entry M 0 (s84x_jm2 M)),
                   entry M 1 (s84x_jm2 M))]"

definition s84x_s1 :: "pairseq \\<Rightarrow> Sym list" where
  "s84x_s1 M
     = fst (THE sb. scb_decomp (transT1 M) (fst sb) (flatBT (transC1 M)) (snd sb))"

definition s84x_b1 :: "pairseq \\<Rightarrow> Sym list" where
  "s84x_b1 M
     = snd (THE sb. scb_decomp (transT1 M) (fst sb) (flatBT (transC1 M)) (snd sb))"

lemma m_8_4_rightend_Trans:
  assumes "M \\<in> ST_PS" "M \\<in> PT_PS"
    and "hasParent M 1 (Lng M - 1)"
    and "s84x_jm2 M + 1 < Lng M - 1"
  shows "\\<exists>!sb. scb_decomp (Trans (s84x_Np M)) (fst sb)
                 (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\\<^sub>B)) (snd sb)
             \\<and> scb_decomp (Trans (s84x_Lp M)) (fst sb)
                 (flatBT (Dpt (enat (entry M 1 (s84x_jm2 M))) 0\\<^sub>B)) (snd sb)"

lemma m_8_4_oper_props_1:
  assumes "M \\<in> ST_PS" "M \\<in> PT_PS"
    and "hasParent M 1 (Lng M - 1)" "1 < Lng M - 1"
  shows "transCondIII M \\<or> transCondIV M \\<Longrightarrow> s84x_jm2 M < transJ0 M"
    and "transCondV M \\<or> transCondVI M \\<Longrightarrow> s84x_jm2 M = transJ0 M"

lemma m_8_4_oper_props_2:
  assumes "M \\<in> ST_PS" "M \\<in> PT_PS"
    and "hasParent M 1 (Lng M - 1)" "1 < Lng M - 1" "n \\<ge> 1"
  shows "s84x_L M n \\<in> RT_PS" and "monoT (s84x_L M n)"

lemma m_8_4_oper_props_3:
  assumes "M \\<in> ST_PS" "M \\<in> PT_PS"
    and "hasParent M 1 (Lng M - 1)" "1 < Lng M - 1"
  shows "j < Lng M \\<Longrightarrow> j' < Lng M \\<Longrightarrow> leR M 0 j j' = leR (s84x_L M 1) 0 j j'"
    and "j < Lng M \\<Longrightarrow> j' < Lng M \\<Longrightarrow> j \\<noteq> Lng M - 1 \\<Longrightarrow> j' \\<noteq> Lng M - 1 \\<Longrightarrow>
           leR M 1 j j' = leR (s84x_L M 1) 1 j j'"

lemma m_8_4_oper_props_4:
  assumes "M \\<in> ST_PS" "M \\<in> PT_PS"
    and "hasParent M 1 (Lng M - 1)" "1 < Lng M - 1"
  shows "transCondVI M \\<or> adm M (transJ0 M) \\<Longrightarrow>
           transCondI (s84x_L M 1) \\<or> transCondIII (s84x_L M 1)"
    and "\\<not> transCondVI M \\<Longrightarrow> \\<not> adm M (transJ0 M) \\<Longrightarrow>
           transCondII (s84x_L M 1) \\<or> transCondIV (s84x_L M 1)"

lemma m_8_4_oper_props_5:
  assumes "M \\<in> ST_PS" "M \\<in> PT_PS"
    and "hasParent M 1 (Lng M - 1)" "1 < Lng M - 1" "n > 1"
  shows "\\<exists>!sb. scb_decomp (Trans (s84x_L M (n - 1))) (fst sb)
                 (flatBT (Dpt (enat (entry M 1 (s84x_jm2 M))) 0\\<^sub>B)) (snd sb)
             \\<and> scb_decomp (Trans (s84x_L M n)) (fst sb)
                 (flatBT (Trans (s84x_Lp M))) (snd sb)
             \\<and> (\\<not> zeroT (Pred (s84x_Np M)) \\<longrightarrow>
                  scb_decomp (Trans ((M::pairseq)[n])) (fst sb)
                    (flatBT (Trans (Pred (s84x_Np M)))) (snd sb))"

lemma m_8_4_Trans_scb:
  assumes "M \\<in> RT_PS" "M \\<in> PT_PS"
    and "1 < Lng M - 1" "hasParent M 1 (Lng M - 1)"
  shows "\\<exists>!sb. scb_kind1 (Trans M) (fst sb) (flatBT (Trans (s84x_N M))) (snd sb)"

lemma m_8_4_slice_scb:
  assumes "M \\<in> ST_PS" "M \\<in> PT_PS"
    and "hasParent M 1 (Lng M - 1)"
    and "\\<not> transCondVI M" "Adm M (s84x_jm2 M) = transJm1 M"
  shows "\\<exists>!sb. scb_decomp (transC2 M)
                 (Dsym (enat (entry M 1 (transJm1 M))) # fst sb)
                 (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\\<^sub>B)) (snd sb)
             \\<and> scb_decomp (Trans (s84x_Np M))
                 (Dsym (enat (entry M 1 (s84x_jm2 M))) # fst sb)
                 (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\\<^sub>B)) (snd sb)"
    and "Trans (Pred (s84x_Np M)) = Dpt (enat (entry M 1 (s84x_jm2 M))) (transT2 M)"

lemma m_8_4_various_scb_IIIV:
  assumes "M \\<in> ST_PS" "M \\<in> PT_PS"
    and "hasParent M 1 (Lng M - 1)"
    and "\\<not> transCondVI M"
    and "s84x_jm2 M < transJ0 M \\<or> adm M (transJ0 M)"
    and "Adm M (s84x_jm2 M) = transJm1 M"
    and "n \\<ge> 1"
  shows "\\<exists>!sb. scb_decomp (transC2 M)
                 (Dsym (enat (entry M 1 (transJm1 M))) # fst sb)
                 (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\\<^sub>B)) (snd sb)
             \\<and> scb_decomp (Trans (s84x_Np M))
                 (Dsym (enat (entry M 1 (s84x_jm2 M))) # fst sb)
                 (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\\<^sub>B)) (snd sb)
             \\<and> scb_decomp (Trans (s84x_Lp M))
                 (Dsym (enat (entry M 1 (s84x_jm2 M))) # fst sb)
                 (flatBT (Dpt (enat (entry M 1 (s84x_jm2 M))) 0\\<^sub>B)) (snd sb)
             \\<and> Trans (Pred (s84x_Np M))
                 = Dpt (enat (entry M 1 (s84x_jm2 M))) (transT2 M)
             \\<and> flatBT (Trans (s84x_L M n))
                 = s84x_s1 M @ Dsym (enat (entry M 1 (transJm1 M)))
                     # concat (replicate n
                         (fst sb @ [Dsym (enat (entry M 1 (s84x_jm2 M)))]))
                     @ [Zsym] @ concat (replicate n (snd sb)) @ s84x_b1 M
             \\<and> flatBT (Trans ((M::pairseq)[n]))
                 = s84x_s1 M @ Dsym (enat (entry M 1 (transJm1 M)))
                     # concat (replicate (n - 1)
                         (fst sb @ [Dsym (enat (entry M 1 (s84x_jm2 M)))]))
                     @ flatBT (transT2 M)
                     @ concat (replicate (n - 1) (snd sb)) @ s84x_b1 M"

lemma m_8_4_various_scb_IIIIV:
  assumes "M \\<in> ST_PS" "M \\<in> PT_PS"
    and "hasParent M 1 (Lng M - 1)" "1 < Lng M - 1"
    and "transCondIII M \\<or> transCondIV M"
    and "s84x_jm3 M < transJm1 M"
    and "n \\<ge> 1"
  shows "\\<exists>!x. case x of (s0', s1', s2', b2', b1', b0') \\<Rightarrow>
         scb_decomp (Trans M) s0' (flatBT (Trans (s84x_N M))) b0'
       \\<and> scb_decomp (Trans (Pred (s84x_N M)))
           (Dsym (enat (entry M 1 (s84x_jm3 M))) # s1') (flatBT (transC1 M)) b1'
       \\<and> scb_decomp (Trans (s84x_N M))
           (Dsym (enat (entry M 1 (s84x_jm3 M))) # s1') (flatBT (transC2 M)) b1'
       \\<and> scb_decomp (transC2 M) s2'
           (flatBT (Dpt (enat (entry M 1 (Lng M - 1))) 0\\<^sub>B)) b2'
       \\<and> scb_decomp (Trans (Pred (s84x_Np M)))
           (Dsym (enat (entry M 1 (s84x_jm2 M))) # s1') (flatBT (transC1 M)) b1'
       \\<and> scb_decomp (Trans (s84x_Np M))
           (Dsym (enat (entry M 1 (s84x_jm2 M))) # s1') (flatBT (transC2 M)) b1'
       \\<and> scb_decomp (Trans (s84x_Lp M))
           (Dsym (enat (entry M 1 (s84x_jm2 M))) # s1' @ s2')
           (flatBT (Dpt (enat (entry M 1 (s84x_jm2 M))) 0\\<^sub>B)) (b2' @ b1')
       \\<and> flatBT (Trans (s84x_L M n))
           = s0' @ Dsym (enat (entry M 1 (s84x_jm3 M)))
               # concat (replicate n
                   (s1' @ s2' @ [Dsym (enat (entry M 1 (s84x_jm2 M)))]))
               @ [Zsym] @ concat (replicate n (b2' @ b1')) @ b0'
       \\<and> flatBT (Trans ((M::pairseq)[n]))
           = s0' @ Dsym (enat (entry M 1 (s84x_jm3 M)))
               # concat (replicate (n - 1)
                   (s1' @ s2' @ [Dsym (enat (entry M 1 (s84x_jm2 M)))]))
               @ s1' @ flatBT (transC1 M) @ b1'
               @ concat (replicate (n - 1) (b2' @ b1')) @ b0'"

======================================================================
MODELLING NOTES
======================================================================
- L1: (2)/(3) merged per [C-1]; the case split (j-2 = j0 or adm j0) vs
  (j-2 < j0 and ~adm j0) disappears from the conclusion.  jm2+1 < j1 is
  the article's j-2 < j1-1 in nat-safe form.
- L2(3): the article restricts <=_M = <=_{L_1} to ({0,1} x NAT) \\ {(1,j1)};
  transcribed with explicit index bounds j,j' < Lng M (= Lng (s84x_L M 1));
  out-of-range leR behavior of the closure definition is not part of the
  article's claim.
- L2(5): (5-3) guarded per [C-2].
- L5(4)(5)/L6(5)(6): string powers x^k = concat (replicate k x); the D_v
  prefix of the article is Dsym (enat v) # _ (cf. flatBP); "0" = [Zsym];
  t2 as a string = flatBT (transT2 M).
- The ∃! shapes follow the article ("a unique tuple satisfying ALL of");
  empirically the first conjunct already pins the witness (see above).

======================================================================
DEPENDENCY NOTES (for the prover fan-out)
======================================================================
Within-batch (article proof structure):
- m_8_4_oper_props_1..4: independent basics (proof: parent/adm arithmetic,
  reducedness of oper, seg heredity).  props_2 uses the L_n = prefix of
  M[n+1] identity (cf. proven m_8_4_oper_Suc_append, m_8_4_oper1_eq_Pred
  in pss_scratch).
- m_8_4_oper_props_5: uses props_2 (L_n reduced&mono) + m_7_4_Mark_Trans_repr
  (proven, pss_wip 13197) + 基点の切片への遺伝性; the zeroT guard [C-2] matches
  the repr's nonzero guard.
- m_8_4_rightend_Trans (L1): standalone brick.  Article route:
  m_8_2_standard_slice_Red_strongmono (proven), IncrFirst/Red slice relations
  (§6.5 proven family), R := Pred(Red N') + rightend-replacement is reduced
  (via RedCondA/B keystone), Trans (IncrFirst,Red)-invariance
  (m_7_3, proven), scb compose (m_7_2_scb_compose, proven) + add-scb
  (p_7_2_add_scb is SORRY - prover must use the proven surrogate family or
  reprove; check m_7_2 exports in pss_wip).
- m_8_4_Trans_scb (L3): independent of L1/L2.  Route: Marked membership,
  m_7_4_Mark_Trans_repr + RightNodes/RightAnces relation (m_7_4 cluster,
  proven) + kind-1 conditions from parent inequalities (親の基本性質(2)).
- m_8_4_slice_scb (L4): needs props_1 (III/IV -> jm2 < j0) + Mark rightmost
  props (m_7_3_Mark_rightmost1/2, proven) + scb triviality + Mark left-end
  (Mark_leftend_form, proven) + 条件(V)の下での終切片とTransの関係
  (p_8_2_condV_terminal_slice_Trans: SORRY — MAIN EXTERNAL BLOCKER; the
  surgery/nest machinery Mark_MarkedB_nest (proven) may substitute)
  + 公差(1,1) Trans props (m_8_1_diagSeq_Trans family, proven).
- m_8_4_various_scb_IIIV (L5): needs L4 + L1 + props_4 + props_5 + Trans
  recursion unfolds; (4)(5) by induction on n gluing L1/L4 via scb compose.
- m_8_4_various_scb_IIIIV (L6): needs props_* + L1 + Mark repr + scb compose
  + the same §8.2 terminal-slice blocker as L4; (5)(6) mirror L5's induction.

External blockers (NOT in this batch; do NOT cite p_* sorries):
- p_8_2_condV_terminal_slice_Trans (pss_paper 1603) — unproven; needed by
  L4(2), L5(2), L6(4) transport steps unless replaced by the proven
  Mark_MarkedB_nest / surg_* machinery.
- p_7_2_add_scb (pss_paper 1009) — unproven as stated; the proven m_7_2
  exports in pss_wip cover the used instances (check m_7_2_scb_compose,
  m_7_2_scb_unique_sb, m_7_2_scb_fseq_* before wiring).

CHAINS for parallel provers (dependency-closed, each internally ordered):
  chain 1: m_8_4_oper_props_1, m_8_4_oper_props_2, m_8_4_oper_props_3,
           m_8_4_oper_props_4, m_8_4_oper_props_5, m_8_4_slice_scb
  chain 2: m_8_4_rightend_Trans
  chain 3: m_8_4_Trans_scb
m_8_4_various_scb_IIIV / m_8_4_various_scb_IIIIV are validated + typechecked
but NOT in the fan-out (cross-chain deps: chain1's props+slice_scb AND
chain2's rightend_Trans); prove them in the next round once those land.
"""

# Machine-readable summary for the parent
STATEMENTS = {
    "m_8_4_rightend_Trans":    {"validated": "244/244 (lit (3) REFUTED 0/40)",
                                "chain": 2, "ready": True},
    "m_8_4_oper_props_1":      {"validated": "396/396", "chain": 1, "ready": True},
    "m_8_4_oper_props_2":      {"validated": "1174/1174", "chain": 1, "ready": True},
    "m_8_4_oper_props_3":      {"validated": "357/357", "chain": 1, "ready": True},
    "m_8_4_oper_props_4":      {"validated": "357/357", "chain": 1, "ready": True},
    "m_8_4_oper_props_5":      {"validated": "688/688 (lit (5-3) REFUTED 92/92 zeroT)",
                                "chain": 1, "ready": True},
    "m_8_4_Trans_scb":         {"validated": "393/393", "chain": 3, "ready": True},
    "m_8_4_slice_scb":         {"validated": "85/85", "chain": 1, "ready": True},
    "m_8_4_various_scb_IIIV":  {"validated": "66/66; parts(4,5) 195/195",
                                "chain": None, "ready": False},
    "m_8_4_various_scb_IIIIV": {"validated": "342/342; parts(5,6) 903/903 (III only; IV&jm3<jm1 unfound in 89k seqs)",
                                "chain": None, "ready": False},
}

if __name__ == '__main__':
    for k, v in STATEMENTS.items():
        print(f"{k:28s} ready={v['ready']} chain={v['chain']} {v['validated']}")
