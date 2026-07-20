theory Support_7_011
  imports Frontier_7_014
begin

text \<open>Front B — conjunct (2) of \<open>p_7_2_add_scb\<close>: replacing the marked principal
  \<open>c\<close> by another principal \<open>c'\<close> preserves the scb-decomposition with the same
  \<open>s\<close>/\<open>b\<close>.  Empirically TRUE (small-BT enumeration, 0 counterexamples).

  Proof: \<open>t +\<^sub>B c = Trm (untrm t @ [p\<^sub>c])\<close>; the constraint "\<open>b\<close> is all \<open>)\<close>"
  pins the marked occurrence of \<open>flatBT c\<close> to the \<^emph>\<open>last\<close> principal, so the
  hypothesis decomposition \<open>(s,b)\<close> equals the canonical \<open>(pre,post)\<close> by
  scb-uniqueness (\<open>m_7_2_scb_unique_sb\<close>).  The same \<open>pre\<close>/\<open>post\<close> (which depend
  only on \<open>untrm t = butlast xs\<close>) serve \<open>c'\<close> by \<open>addscb_flat_pre_post2\<close>.\<close>

lemma m_7_2_add_scb_conj2:
  assumes tTB: "t \<in> T_B" and cTB: "c \<in> T_B" and cp: "\<exists>p. c = Trm [p]"
      and c'TB: "c' \<in> T_B" and c'p: "\<exists>p. c' = Trm [p]"
      and hyp: "scb_decomp (t +\<^sub>B c) s (flatBT c) b"
  shows "scb_decomp (t +\<^sub>B c') s (flatBT c') b"
proof -
  from cp obtain pc where cpe: "c = Trm [pc]" by blast
  obtain uc ac where pcua: "pc = DB uc ac" by (cases pc)
  from c'p obtain pc' where c'pe: "c' = Trm [pc']" by blast
  obtain u' a' where pc'ua: "pc' = DB u' a'" by (cases pc')
  \<comment> \<open>\<open>t +\<^sub>B c = Trm xs\<close> with \<open>last xs\<close> the (whole) principal \<open>pc\<close>.\<close>
  define xs where "xs = untrm t @ [DB uc ac]"
  have tc_eq: "t +\<^sub>B c = Trm xs"
    using cpe pcua addscb_addBT_snoc[of t pc] unfolding xs_def by simp
  have xs_ne: "xs \<noteq> []" unfolding xs_def by simp
  have bl_xs: "butlast xs = untrm t" unfolding xs_def by simp
  \<comment> \<open>\<open>flatBT c = flatBP pc = Dsym uc # flatBT ac\<close>; similarly for \<open>c'\<close>.\<close>
  have fc_eq: "flatBT c = Dsym uc # flatBT ac" using cpe pcua by simp
  have fc'_eq: "flatBT c' = Dsym u' # flatBT a'" using c'pe pc'ua by simp
  \<comment> \<open>The uniform pre/post split for the trailing principal of \<open>Trm xs\<close>.\<close>
  obtain pre post where post_RP: "\<forall>x \<in> set post. x = RP"
      and split: "\<And>u a. flatBT (Trm (butlast xs @ [DB u a]))
                          = pre @ (Dsym u # flatBT a) @ post"
    using addscb_flat_pre_post2[OF xs_ne] by blast
  \<comment> \<open>Canonical scb-decomposition of \<open>t +\<^sub>B c\<close> marking the last principal \<open>c\<close>.\<close>
  have ptb_c: "isPTB_str (flatBT c)"
    using addscb_princ_isPTB[OF cTB cpe] .
  have tc_ne: "t +\<^sub>B c \<noteq> Trm []" using tc_eq xs_ne by simp
  have flat_tc: "flatBT (t +\<^sub>B c) = pre @ (Dsym uc # flatBT ac) @ post"
    using split[of uc ac] bl_xs tc_eq unfolding xs_def by simp
  have sd_can: "scb_decomp (t +\<^sub>B c) pre (flatBT c) post"
    unfolding scb_decomp_def
    using flat_tc fc_eq post_RP ptb_c tc_ne by simp
  \<comment> \<open>The hypothesis decomposition coincides with the canonical one.\<close>
  have sbeq: "s = pre \<and> b = post"
    by (rule m_7_2_scb_unique_sb[OF hyp sd_can tc_ne])
  \<comment> \<open>Replace the last principal by \<open>c'\<close>: same \<open>pre\<close>/\<open>post\<close>.\<close>
  have tc'_eq: "t +\<^sub>B c' = Trm (butlast xs @ [DB u' a'])"
    using c'pe pc'ua addscb_addBT_snoc[of t pc'] bl_xs unfolding xs_def
    by simp
  have flat_tc': "flatBT (t +\<^sub>B c') = pre @ (Dsym u' # flatBT a') @ post"
    using split[of u' a'] tc'_eq by simp
  have ptb_c': "isPTB_str (flatBT c')"
    using addscb_princ_isPTB[OF c'TB c'pe] .
  have tc'_ne: "t +\<^sub>B c' \<noteq> Trm []" using tc'_eq by simp
  show ?thesis
    unfolding scb_decomp_def
    using flat_tc' fc'_eq post_RP ptb_c' tc'_ne sbeq by simp
qed



section \<open>§7.2 第0種/第1種 scb分解の一意性 (p_7_2_scb_unique conjuncts (4),(5))\<close>

text \<open>
  EMPIRICAL TRUTH-CHECK (\<open>_scbkind_check.py\<close>, BT model, indices \<open>{0,1,2}\<close>,
  depth \<open>2\<close>, 1560 nonempty \<open>D\<^sub>\<omega>\<close>-free terms):

  \<^item> conjunct (4) \<open>kind0\<close>-uniqueness, conjunct (5) \<open>kind1\<close>-uniqueness, conjunct (3)
    \<open>kind0/kind1\<close>-exclusivity: 0 failures over 1560 nonempty terms.
  \<^item> The legacy encoder reported failures at \<open>t = Trm []\<close>: it waived the
    \<open>isPTB_str c\<close> condition inherited from \<^const>\<open>scb_decomp\<close> and expressed the
    kind condition only by a universal implication, so non-principal \<open>c\<close> strings made
    that implication vacuous.  A14 is retracted: the article makes the positive demand
    that \<open>c\<close> be a principal term.  The current \<^const>\<open>scb_kind0\<close> /
    \<^const>\<open>scb_kind1\<close> definitions encode that demand explicitly, so neither kind
    holds at zero and the article's unconditional conjuncts remain true.

  The brick below is retained as the GREEN nonempty-branch reduction.  The final
  @{text p_7_2_scb_unique} proof combines it with the positive-principal zero case.

  REDUCTION.  For \<open>t \<noteq> Trm []\<close>, the green @{thm [source] m_7_2_scb_unique_decomp}
  already gives \<open>(s\<^sub>0,b\<^sub>0) = (s\<^sub>1,b\<^sub>1)\<close> once \<open>c\<^sub>0 = c\<^sub>1\<close>.  So both kind-uniqueness
  conjuncts reduce to the single residual obligation \<open>c\<^sub>0 = c\<^sub>1\<close> (the article's
  "\<open>c\<close> is the maximal proper term substring", pinned by the \<open>RightNodes\<close> spine).
\<close>

\<comment> \<open>Reduction brick (GREEN): kind0/kind1 uniqueness from \<open>c\<close>-equality.  Sound — it
   cites only the green @{thm [source] m_7_2_scb_unique_decomp}, never an
   unproven stub.  This is the article's final step
   ("\<open>c\<^sub>0 = c\<^sub>1\<close> かつ \<open>b\<^sub>0 = b\<^sub>1\<close> ... \<open>s\<^sub>0 = s\<^sub>1\<close>").\<close>
lemma m_7_2_scb_kind_unique_of_ceq:
  assumes tTB: "t \<in> T_B"
      and ceq: "c\<^sub>0 = c\<^sub>1"
      and d0: "scb_decomp t s\<^sub>0 c\<^sub>0 b\<^sub>0"
      and d1: "scb_decomp t s\<^sub>1 c\<^sub>1 b\<^sub>1"
  shows "(s\<^sub>0, c\<^sub>0, b\<^sub>0) = (s\<^sub>1, c\<^sub>1, b\<^sub>1)"
proof -
  have d1': "scb_decomp t s\<^sub>1 c\<^sub>0 b\<^sub>1" using d1 ceq by simp
  have "s\<^sub>0 = s\<^sub>1 \<and> b\<^sub>0 = b\<^sub>1"
    by (rule m_7_2_scb_unique_decomp[OF tTB d0 d1'])
  thus ?thesis using ceq by simp
qed

text \<open>RESIDUAL (Front A, single hard subcase).  The \<S>6.6 keystone forward
  monoT-core lemma
    \<open>kst_reduced_imp_condAB_monoT_core:
       M \<in> RT_PS \<Longrightarrow> monoT M \<Longrightarrow> entry M 0 0 = 0 \<Longrightarrow> entry M 1 0 = 0
         \<Longrightarrow> RedCondA M \<and> RedCondB M\<close>
  is fully reduced to ONE obligation by the bricks above:  the induction on
  \<open>Lng M\<close> (measure_induct_rule) closes the \<open>zeroT\<close> base, the TRUNK case
  (@{thm [source] kfwd_reduced_core_trunk_condAB}), every \<open>RedCondA\<close>/\<open>RedCondB\<close>
  witness strictly below the last column (Pred-lift: @{thm [source]
  kfwd_nextR_Pred_imp}/@{thm [source] kfwd_hasParent_Pred_iff}/@{thm [source]
  kfwd_parent_Pred_eq}/@{thm [source] kfwd_entry_Pred_eq} + IH on \<open>Pred M\<close>,
  reduced by @{thm [source] herd_6_6_reduced_slice}, monoT by @{thm [source]
  m_6_2_mono_prefix}), and the last-column \<open>RedCondB\<close> witness (vacuous by
  @{thm [source] kfwd_monoT_hasParent_top}).  The SOLE residual is the
  last-column \<open>RedCondA\<close> relation (article content.md 1156-1218):

    \<open>condA_top\<close>:  for \<open>M \<in> RT_PS\<close>, \<open>monoT M\<close>, \<open>entry M 0 0 = entry M 1 0 = 0\<close>,
      \<open>TrMax M \<noteq> Lng M - 1\<close>, \<open>i \<le> 1\<close> and \<open>hasParent M i (Lng M - 1)\<close>,
      \<open>entry M i (parent M i (Lng M - 1)) + 1 = entry M i (Lng M - 1)\<close>.

  EMPIRICALLY TRUE (0 counterexamples over all 1884 monoT seqs / all 49 reduced
  monoT core nontrunk seqs at values \<le>3, lengths \<le>4).  Its proof is the
  article N-construction (\<open>N := diagSeq 0 (M\<^bsub>1,m\<^esub>-1) \<oplus> Red(P(seg M (j\<^sub>0+1) j\<^sub>1)\<^bsub>J\<^sub>0\<^esub>)\<close>
  resp. the \<open>J\<^sub>1>0\<close> form): \<open>N\<close> reduced via @{thm [source] m_6_6_reduced_leftend},
  left end \<open>(0,0)\<close> via @{thm [source] m_6_6_Red_leftend_2}, \<open>Lng N - 1 < j\<^sub>1\<close>, IH on
  \<open>N\<close>, witness translated across \<open>seg\<close>/\<open>P\<close>/\<open>IncrFirst\<close>
  (@{thm [source] nextrel0_IncrFirst_eq}, @{thm [source] nextrel1_IncrFirst_eq})
  and the coefficient bounds @{thm [source] m_6_6_condAB_coeff}.  This residual
  was NOT closed in this run.\<close>


subsection \<open>§7.2 scb分解の一意性 — the central \<open>c\<close>-equality \<open>m_7_2_scb_c_unique\<close>\<close>

text \<open>
  The article (content.md 1894/1896 for kind-0, 1916/1918 for kind-1) reduces
  the \<open>c\<close>-part equality of two same-kind scb-decompositions of \<open>t\<close> to a single
  pinned quantity: the position \<open>s\<close> at which the marked principal \<open>c\<close> begins
  inside \<open>flatBT t\<close>.  Concretely it shows (1894/1916) \<open>j\<^sub>1-j\<^sub>1\<^sub>,\<^sub>0 = j\<^sub>1-j\<^sub>1\<^sub>,\<^sub>1\<close>
  and \<open>v\<^sub>0 = v\<^sub>1\<close> from the \<open>RightNodes\<close>-spine condition, and then (1896/1918)
  concludes "\<open>s = s\<^sub>i\<close>" — i.e. \<open>s\<^sub>0 = s\<^sub>1\<close> — because both \<open>c\<^sub>i\<close> start at the
  unique LAST occurrence of \<open>D\<^bsub>v\<^sub>0\<^esub>\<close> in \<open>t\<close>.

  Once that single quantity is pinned, the \<open>c\<close>-equality is PURELY a string-
  cancellation fact and needs no further spine reasoning: from
  \<open>flatBT t = s\<^sub>0 \<frown> c\<^sub>0 \<frown> b\<^sub>0 = s\<^sub>1 \<frown> c\<^sub>1 \<frown> b\<^sub>1\<close> with \<open>length s\<^sub>0 = length s\<^sub>1\<close>
  we cancel the common-length prefix (\<open>append_eq_append_conv\<close>) to get
  \<open>s\<^sub>0 = s\<^sub>1\<close> and \<open>c\<^sub>0 \<frown> b\<^sub>0 = c\<^sub>1 \<frown> b\<^sub>1\<close>, and then — since each \<open>c\<^sub>i\<close> is a
  principal-term string \<open>flatBP p\<^sub>i\<close> (the \<open>isPTB_str\<close> part of \<open>scb_decomp\<close> for
  \<open>t \<noteq> 0\<close>) — the GREEN unique-readability brick @{thm [source] flatinj_flatBP_cancel}
  forces \<open>c\<^sub>0 = c\<^sub>1\<close> (and \<open>b\<^sub>0 = b\<^sub>1\<close>) outright.

  So the residual flagged last round (\<open>c\<^sub>0 = c\<^sub>1\<close>) reduces EXACTLY to the
  RightNodes-spine pinning \<open>length s\<^sub>0 = length s\<^sub>1\<close>; we take that pinned cut as
  the hypothesis (it is the article's "\<open>s = s\<^sub>i\<close>" / content.md 1896,1918), and
  discharge the remaining string cancellation here.  EMPIRICAL truth-check of
  the pinning: the cut is the last \<open>D\<^bsub>v\<^sub>0\<^esub>\<close> position, identical for both \<open>i\<close>;
  with equal cut the two principal prefixes of \<open>c\<^sub>0 \<frown> b\<^sub>0 = c\<^sub>1 \<frown> b\<^sub>1\<close> coincide
  by prefix-minimality of a balanced principal string (\<open>flatinj_dsum = -1\<close>).
\<close>

\<comment> \<open>Pure string kernel: two principal flat strings with the same all-\<open>RP\<close> tail
   length-aligned by a common cut coincide.  Sound — cites only the GREEN
   @{thm [source] flatinj_flatBP_cancel}.\<close>
lemma scbc_principal_cancel:
  assumes eq: "flatBP p\<^sub>0 @ b\<^sub>0 = flatBP p\<^sub>1 @ b\<^sub>1"
  shows "flatBP p\<^sub>0 = flatBP p\<^sub>1 \<and> b\<^sub>0 = b\<^sub>1"
  by (rule flatinj_flatBP_cancel[OF eq])

text \<open>命題（scb分解の一意性）central \<open>c\<close>-equality (§7.2, content.md 1894-1896 /
  1916-1918): for two scb-decompositions of the SAME nonempty \<open>t\<close> whose marked
  principals begin at the same cut (the pinned \<open>RightNodes\<close>-spine position,
  \<open>length s\<^sub>0 = length s\<^sub>1\<close>), the \<open>c\<close>-parts coincide.  This discharges the residual
  to which @{thm [source] m_7_2_scb_kind_unique_of_ceq} reduces conjuncts (4),(5).\<close>

lemma m_7_2_scb_c_unique:
  assumes tne: "t \<noteq> Trm []"
      and d0: "scb_decomp t s\<^sub>0 c\<^sub>0 b\<^sub>0"
      and d1: "scb_decomp t s\<^sub>1 c\<^sub>1 b\<^sub>1"
      and pin: "length s\<^sub>0 = length s\<^sub>1"
  shows "c\<^sub>0 = c\<^sub>1"
proof -
  \<comment> \<open>Unfold the two scb-decompositions; \<open>c\<^sub>i\<close> is a principal string (\<open>t \<noteq> 0\<close>).\<close>
  from d0 have e0: "flatBT t = s\<^sub>0 @ c\<^sub>0 @ b\<^sub>0" and pc0: "isPTB_str c\<^sub>0"
    using tne by (auto simp: scb_decomp_def)
  from d1 have e1: "flatBT t = s\<^sub>1 @ c\<^sub>1 @ b\<^sub>1" and pc1: "isPTB_str c\<^sub>1"
    using tne by (auto simp: scb_decomp_def)
  obtain p\<^sub>0 where p0: "c\<^sub>0 = flatBP p\<^sub>0" using pc0 unfolding isPTB_str_def by blast
  obtain p\<^sub>1 where p1: "c\<^sub>1 = flatBP p\<^sub>1" using pc1 unfolding isPTB_str_def by blast
  \<comment> \<open>Same total string, common-length prefix \<open>s\<close>: cancel it.\<close>
  have str: "s\<^sub>0 @ (c\<^sub>0 @ b\<^sub>0) = s\<^sub>1 @ (c\<^sub>1 @ b\<^sub>1)" using e0 e1 by simp
  have cb: "c\<^sub>0 @ b\<^sub>0 = c\<^sub>1 @ b\<^sub>1"
    using str pin by (simp add: append_eq_append_conv)
  \<comment> \<open>Two principal prefixes of the same string coincide (unique readability).\<close>
  have "flatBP p\<^sub>0 @ b\<^sub>0 = flatBP p\<^sub>1 @ b\<^sub>1" using cb p0 p1 by simp
  hence "flatBP p\<^sub>0 = flatBP p\<^sub>1" by (rule scbc_principal_cancel[THEN conjunct1])
  thus ?thesis using p0 p1 by simp
qed

text \<open>
  Nonempty-branch assembly of conjuncts (4),(5) of @{text p_7_2_scb_unique}:
  combine the central \<open>c\<close>-equality
  @{thm [source] m_7_2_scb_c_unique} with the GREEN
  @{thm [source] m_7_2_scb_kind_unique_of_ceq} (which pins \<open>s,b\<close> from \<open>c\<^sub>0 = c\<^sub>1\<close>).
  Both still carry the RightNodes-spine pinning \<open>length s\<^sub>0 = length s\<^sub>1\<close> as a
  hypothesis: deriving it from the kind-0/kind-1 \<open>RightNodes\<close> condition is the
  residual multi-lemma program recorded at content.md 1894/1916 (suffix-segment of
  \<open>RightNodes t\<close>); the later support lemmas discharge that program before the
  unconditional final theorem.
\<close>

lemma m_7_2_scb_kind0_unique:
  assumes tTB: "t \<in> T_B" and tne: "t \<noteq> Trm []"
      and d0: "scb_kind0 t s\<^sub>0 c\<^sub>0 b\<^sub>0"
      and d1: "scb_kind0 t s\<^sub>1 c\<^sub>1 b\<^sub>1"
      and pin: "length s\<^sub>0 = length s\<^sub>1"
  shows "(s\<^sub>0, c\<^sub>0, b\<^sub>0) = (s\<^sub>1, c\<^sub>1, b\<^sub>1)"
proof -
  have sd0: "scb_decomp t s\<^sub>0 c\<^sub>0 b\<^sub>0" using d0 by (simp add: scb_kind0_def)
  have sd1: "scb_decomp t s\<^sub>1 c\<^sub>1 b\<^sub>1" using d1 by (simp add: scb_kind0_def)
  have ceq: "c\<^sub>0 = c\<^sub>1" by (rule m_7_2_scb_c_unique[OF tne sd0 sd1 pin])
  show ?thesis by (rule m_7_2_scb_kind_unique_of_ceq[OF tTB ceq sd0 sd1])
qed

lemma m_7_2_scb_kind1_unique:
  assumes tTB: "t \<in> T_B" and tne: "t \<noteq> Trm []"
      and d0: "scb_kind1 t s\<^sub>0 c\<^sub>0 b\<^sub>0"
      and d1: "scb_kind1 t s\<^sub>1 c\<^sub>1 b\<^sub>1"
      and pin: "length s\<^sub>0 = length s\<^sub>1"
  shows "(s\<^sub>0, c\<^sub>0, b\<^sub>0) = (s\<^sub>1, c\<^sub>1, b\<^sub>1)"
proof -
  have sd0: "scb_decomp t s\<^sub>0 c\<^sub>0 b\<^sub>0" using d0 by (simp add: scb_kind1_def)
  have sd1: "scb_decomp t s\<^sub>1 c\<^sub>1 b\<^sub>1" using d1 by (simp add: scb_kind1_def)
  have ceq: "c\<^sub>0 = c\<^sub>1" by (rule m_7_2_scb_c_unique[OF tne sd0 sd1 pin])
  show ?thesis by (rule m_7_2_scb_kind_unique_of_ceq[OF tTB ceq sd0 sd1])
qed




\<comment> \<open>An all-\<open>)\<close> string has weight \<open>- length\<close> (each \<open>RP\<close> contributes \<open>-1\<close>).\<close>
lemma flatinj_dsum_allRP:
  "\<forall>x \<in> set w. x = RP \<Longrightarrow> flatinj_dsum w = - int (length w)"
  by (induction w) auto

\<comment> \<open>GREEN MAXIMALITY brick (residual link (ii), CLOSED).  A complete term string
   \<open>flatBT a\<close> cannot end strictly inside the trailing \<open>)\<close>-run of \<open>m' \<frown> flatBP p\<close>:
   if \<open>flatBT a \<frown> us = m' \<frown> flatBP p\<close> with \<open>us\<close> all-\<open>)\<close>, then \<open>us = []\<close>.
   Proof by the \<^const>\<open>flatinj_dsum\<close> weight: \<open>m'\<close> is a proper prefix of \<open>flatBT a\<close>
   (the straddle \<open>flatBT a\<close>-prefix-of-\<open>m'\<close> branch forces a \<open>Zsym\<close> into the all-\<open>)\<close>
   \<open>us\<close>), so \<open>flatinj_dsum m' \<ge> 0\<close>; but the total-weight identity gives
   \<open>flatinj_dsum m' = - int (length us) \<le> 0\<close>, hence \<open>length us = 0\<close>.  This is the
   weight contradiction the previous round left open.\<close>
lemma rnsub_straddle_excluded:
  assumes A: "m' @ flatBP (DB up ap) = flatBT a @ us"
      and usRP: "\<forall>x \<in> set us. x = RP"
  shows "us = []"
proof (rule ccontr)
  assume usne: "us \<noteq> []"
  have noZus: "Zsym \<notin> set us" using usRP by auto
  \<comment> \<open>\<open>m'\<close> is a proper prefix of \<open>flatBT a\<close>.\<close>
  have mlt: "length m' < length (flatBT a)"
  proof (rule ccontr)
    assume "\<not> length m' < length (flatBT a)"
    hence ge: "length (flatBT a) \<le> length m'" by simp
    \<comment> \<open>then \<open>flatBT a\<close> is a prefix of \<open>m'\<close>, so \<open>us\<close> = \<open>(tail of m') @ flatBP p\<close>,
       which contains a \<open>Zsym\<close> — contradicting \<open>us\<close> all-\<open>)\<close>.\<close>
    \<comment> \<open>\<open>flatBT a\<close> is a prefix of \<open>m'\<close> (length \<open>\<le>\<close>), so \<open>m' = flatBT a @ ws\<close>.\<close>
    define ws where "ws = drop (length (flatBT a)) m'"
    have mws: "m' = flatBT a @ ws"
    proof -
      have "flatBT a = take (length (flatBT a)) (flatBT a @ us)" by simp
      also have "\<dots> = take (length (flatBT a)) (m' @ flatBP (DB up ap))"
        using A by simp
      also have "\<dots> = take (length (flatBT a)) m'" using ge by simp
      finally have "flatBT a = take (length (flatBT a)) m'" .
      thus ?thesis unfolding ws_def by (metis append_take_drop_id)
    qed
    have "flatBT a @ us = flatBT a @ ws @ flatBP (DB up ap)" using A mws by simp
    hence "us = ws @ flatBP (DB up ap)" by simp
    moreover have "Zsym \<in> set (flatBP (DB up ap))"
      by (rule rnsub_Zsym_in_flatP)
    ultimately have "Zsym \<in> set us" by simp
    thus False using noZus by simp
  qed
  \<comment> \<open>So \<open>flatBT a = m' @ rest\<close> with \<open>rest\<close> nonempty: prefix-nonneg gives
     \<open>flatinj_dsum m' \<ge> 0\<close>.\<close>
  define rest where "rest = drop (length m') (flatBT a)"
  have far: "flatBT a = m' @ rest"
  proof -
    have "m' = take (length m') (m' @ flatBP (DB up ap))" by simp
    also have "\<dots> = take (length m') (flatBT a @ us)" using A by simp
    also have "\<dots> = take (length m') (flatBT a)" using mlt by simp
    finally have "m' = take (length m') (flatBT a)" .
    thus ?thesis unfolding rest_def by (metis append_take_drop_id)
  qed
  have rne: "rest \<noteq> []" using mlt unfolding rest_def by simp
  have mnn: "0 \<le> flatinj_dsum m'"
    by (rule flatinj_prefix_nonneg_BT[OF far rne])
  \<comment> \<open>Weight identity: \<open>flatinj_dsum m' = - int (length us)\<close>.\<close>
  have tot_a: "flatinj_dsum (flatBT a) = -1" by (rule flatinj_dsum_flatBT)
  have tot_p: "flatinj_dsum (flatBP (DB up ap)) = -1"
    using flatinj_dsum_flatBT[of "Trm [DB up ap]"] by simp
  have usw: "flatinj_dsum us = - int (length us)"
    using flatinj_dsum_allRP[OF usRP] .
  have "flatinj_dsum (m' @ flatBP (DB up ap)) = flatinj_dsum (flatBT a @ us)"
    using A by simp
  hence "flatinj_dsum m' + (-1) = (-1) + (- int (length us))"
    using tot_a tot_p usw by simp
  hence "flatinj_dsum m' = - int (length us)" by simp
  hence "int (length us) \<le> 0" using mnn by simp
  hence "length us = 0" by simp
  thus False using usne by simp
qed

\<comment> \<open>GREEN structural brick: at a \<open>Trm xs\<close> level (\<open>xs \<noteq> []\<close>, \<open>last xs = DB u a\<close>),
   an scb-shaped principal occurrence whose cut is AT OR AFTER the canonical
   last-principal start (\<open>length pre \<le> length s\<close>) is EITHER the whole last
   principal (\<open>length s = length pre\<close>: maximal, \<open>flatBP p = Dsym u # flatBT a\<close>,
   \<open>b = post\<close>) OR strictly inside the last principal's argument \<open>flatBT a\<close>
   (\<open>length pre < length s\<close>).  This is the GREEN half of the article's spine
   descent; it uses prefix-freeness @{thm [source] flatinj_flatBP_cancel}.\<close>
lemma rnsub_cut_ge_pre_dichotomy:
  assumes occ: "flatBT (Trm xs) = s @ flatBP (DB up ap) @ b"
      and bRP: "\<forall>x \<in> set b. x = RP"
      and PP: "flatBT (Trm xs) = pre @ (Dsym u # flatBT a) @ post"
      and postRP: "\<forall>x \<in> set post. x = RP"
      and ge: "length pre \<le> length s"
  shows "(length s = length pre \<and> flatBP (DB up ap) = Dsym u # flatBT a \<and> b = post)
       \<or> (length pre < length s
            \<and> (\<exists>s2 b2. flatBT a = s2 @ flatBP (DB up ap) @ b2
                        \<and> (\<forall>x \<in> set b2. x = RP)
                        \<and> length s = length pre + 1 + length s2))"
proof (cases "length s = length pre")
  case True
  \<comment> \<open>Maximal: cancel the common prefix \<open>pre = s\<close>, then prefix-freeness of the
     complete principal \<open>Dsym u # flatBT a = flatBP (DB u a)\<close>.\<close>
  have eqT: "s @ flatBP (DB up ap) @ b = pre @ (Dsym u # flatBT a) @ post"
    using occ PP by simp
  have seq: "s = pre"
    using eqT True by (simp add: append_eq_append_conv)
  have "pre @ flatBP (DB up ap) @ b = pre @ (Dsym u # flatBT a) @ post"
    using occ PP seq by simp
  hence cb: "flatBP (DB up ap) @ b = flatBP (DB u a) @ post" by simp
  have "flatBP (DB up ap) = flatBP (DB u a) \<and> b = post"
    by (rule flatinj_flatBP_cancel[OF cb])
  thus ?thesis using True seq by simp
next
  case False
  hence lt: "length pre < length s" using ge by simp
  \<comment> \<open>Cut strictly after \<open>pre\<close>: \<open>s = pre @ m\<close> with \<open>m\<close> nonempty.  The first symbol
     of the last principal \<open>Dsym u\<close> is at position \<open>length pre < length s\<close>, so it
     is consumed by \<open>m\<close>; hence the marked principal sits inside \<open>flatBT a\<close>.\<close>
  define m where "m = drop (length pre) s"
  have sm: "s = pre @ m"
  proof -
    have eq: "s @ flatBP (DB up ap) @ b = pre @ (Dsym u # flatBT a) @ post"
      using occ PP by simp
    have "pre = take (length pre) (pre @ (Dsym u # flatBT a) @ post)" by simp
    also have "\<dots> = take (length pre) (s @ flatBP (DB up ap) @ b)" using eq by simp
    also have "\<dots> = take (length pre) s" using ge by simp
    finally have "pre = take (length pre) s" .
    thus ?thesis unfolding m_def by (metis append_take_drop_id)
  qed
  have mne: "m \<noteq> []" using lt unfolding m_def by simp
  \<comment> \<open>From \<open>occ = PP\<close> with \<open>s = pre @ m\<close>:
       \<open>m @ flatBP (DB up ap) @ b = (Dsym u # flatBT a) @ post\<close>.\<close>
  have mid: "m @ flatBP (DB up ap) @ b = Dsym u # flatBT a @ post"
    using occ PP sm by simp
  \<comment> \<open>\<open>m\<close> begins with \<open>Dsym u\<close>; its tail \<open>m'\<close> is a prefix of \<open>flatBT a\<close>.\<close>
  obtain m' where m': "m = Dsym u # m'"
    using mid mne by (cases m) auto
  have mid2: "m' @ flatBP (DB up ap) @ b = flatBT a @ post"
    using mid m' by simp
  \<comment> \<open>The marked principal occurrence lives inside \<open>flatBT a\<close>: split \<open>flatBT a\<close> as
     \<open>m' @ flatBP (DB up ap) @ b2\<close> with \<open>b2\<close> all-\<open>)\<close>.  Because everything after the
     principal is all-\<open>)\<close> (\<open>b\<close> then \<open>post\<close>), the principal cannot straddle into
     \<open>post\<close>: a complete principal contains a \<open>Zsym\<close>, which \<open>post\<close>/\<open>b\<close> lack.\<close>
  \<comment> \<open>The marked principal ends within \<open>flatBT a\<close>: \<open>append_eq_append_conv2\<close>
     resolves the overlap of \<open>m' @ flatBP (DB up ap)\<close> with \<open>flatBT a\<close>; the
     straddle branch is excluded by @{thm [source] rnsub_straddle_excluded}.\<close>
  have splitc: "\<exists>us. (m' @ flatBP (DB up ap) = flatBT a @ us \<and> us @ b = post)
           \<or> ((m' @ flatBP (DB up ap)) @ us = flatBT a \<and> b = us @ post)"
  proof -
    have e: "(m' @ flatBP (DB up ap)) @ b = flatBT a @ post"
      using mid2 by simp
    show ?thesis
      using append_eq_append_conv2[THEN iffD1, OF e] by blast
  qed
  then obtain us where
    disj: "(m' @ flatBP (DB up ap) = flatBT a @ us \<and> us @ b = post)
         \<or> ((m' @ flatBP (DB up ap)) @ us = flatBT a \<and> b = us @ post)" by blast
  have lens: "length s = length pre + 1 + length m'"
    using sm m' by simp
  \<comment> \<open>Clean inside-shape of \<open>flatBT a\<close>, with the straddle branch excluded.\<close>
  have fa_inside: "\<exists>b2. flatBT a = m' @ flatBP (DB up ap) @ b2 \<and> (\<forall>x \<in> set b2. x = RP)"
  proof -
    from disj show ?thesis
    proof (elim disjE conjE)
      assume A: "m' @ flatBP (DB up ap) = flatBT a @ us" and B: "us @ b = post"
      have uspost: "\<forall>x \<in> set us. x = RP"
        using B postRP by (metis Un_iff set_append)
      have usnil: "us = []" by (rule rnsub_straddle_excluded[OF A uspost])
      have fa: "flatBT a = m' @ flatBP (DB up ap) @ []" using A usnil by simp
      show ?thesis using fa by simp
    next
      assume A: "(m' @ flatBP (DB up ap)) @ us = flatBT a" and B: "b = us @ post"
      have b2RP: "\<forall>x \<in> set us. x = RP"
        using B bRP by (metis Un_iff set_append)
      have fa: "flatBT a = m' @ flatBP (DB up ap) @ us" using A by simp
      show ?thesis using fa b2RP by blast
    qed
  qed
  then obtain b2 where
    fa2: "flatBT a = m' @ flatBP (DB up ap) @ b2" and b2RP: "\<forall>x \<in> set b2. x = RP"
    by blast
  have ex: "\<exists>s2 b2. flatBT a = s2 @ flatBP (DB up ap) @ b2
                      \<and> (\<forall>x \<in> set b2. x = RP)
                      \<and> length s = length pre + 1 + length s2"
    using fa2 b2RP lens by blast
  show ?thesis using lt ex by blast
qed

end
