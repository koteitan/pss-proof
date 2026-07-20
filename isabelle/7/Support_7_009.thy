theory Support_7_009
  imports P_7_2_scb_triviality
begin

section \<open>§7.2 scb分解の一意性（無条件版） (p_7_2_scb_unique, conjunct (1))\<close>

text \<open>
  Unconditional conjunct (1) of \<open>p_7_2_scb_unique\<close>: for \<open>t \<in> T\<^bsub>B\<^esub>\<close>, an scb
  decomposition with a fixed middle string \<open>c\<close> determines \<open>s\<close> and \<open>b\<close>.  The
  generic case \<open>t \<noteq> Trm []\<close> is the green \<open>m_7_2_scb_unique_sb\<close>.  We close the
  remaining \<open>t = Trm []\<close> case directly: there \<open>flatBT t = [Zsym]\<close> and the
  principal side-condition \<open>isPTB_str c\<close> is waived, so \<open>s @ c @ b = [Zsym]\<close>
  with every letter of \<open>b\<close> equal to \<open>RP \<noteq> Zsym\<close>; hence \<open>b = []\<close> and, with the
  shared \<open>c\<close>, \<open>s\<close> is pinned by \<open>append_eq_append_conv\<close>.  The \<open>t \<in> T\<^bsub>B\<^esub>\<close>
  hypothesis is kept to match the article statement but is not needed for this
  conjunct.\<close>

lemma m_7_2_scb_unique_decomp:
  assumes tTB: "t \<in> T_B"
      and d0: "scb_decomp t s\<^sub>0 c b\<^sub>0"
      and d1: "scb_decomp t s\<^sub>1 c b\<^sub>1"
  shows "s\<^sub>0 = s\<^sub>1 \<and> b\<^sub>0 = b\<^sub>1"
proof (cases "t = Trm []")
  case True
  \<comment> \<open>\<open>flatBT (Trm []) = [Zsym]\<close>; the \<open>isPTB_str\<close> side-condition is waived here.\<close>
  from d0 have e0: "s\<^sub>0 @ c @ b\<^sub>0 = [Zsym]" and rb0: "\<forall>x \<in> set b\<^sub>0. x = RP"
    by (simp_all add: scb_decomp_def True)
  from d1 have e1: "s\<^sub>1 @ c @ b\<^sub>1 = [Zsym]" and rb1: "\<forall>x \<in> set b\<^sub>1. x = RP"
    by (simp_all add: scb_decomp_def True)
  \<comment> \<open>Each \<open>b\<close> is a sublist of \<open>[Zsym]\<close>, so its letters are \<open>Zsym\<close>; but they are
      \<open>RP \<noteq> Zsym\<close>, forcing \<open>b = []\<close>.\<close>
  have sub0: "set b\<^sub>0 \<subseteq> set [Zsym]" using e0 by (metis set_append Un_iff subsetI)
  have b0: "b\<^sub>0 = []"
  proof (rule ccontr)
    assume "b\<^sub>0 \<noteq> []"
    then obtain x where x: "x \<in> set b\<^sub>0" by (cases b\<^sub>0) auto
    from x rb0 have "x = RP" by blast
    moreover from x sub0 have "x = Zsym" by auto
    ultimately show False by simp
  qed
  have sub1: "set b\<^sub>1 \<subseteq> set [Zsym]" using e1 by (metis set_append Un_iff subsetI)
  have b1: "b\<^sub>1 = []"
  proof (rule ccontr)
    assume "b\<^sub>1 \<noteq> []"
    then obtain x where x: "x \<in> set b\<^sub>1" by (cases b\<^sub>1) auto
    from x rb1 have "x = RP" by blast
    moreover from x sub1 have "x = Zsym" by auto
    ultimately show False by simp
  qed
  from e0 b0 have s0c: "s\<^sub>0 @ c = [Zsym]" by simp
  from e1 b1 have s1c: "s\<^sub>1 @ c = [Zsym]" by simp
  from s0c s1c have "s\<^sub>0 @ c = s\<^sub>1 @ c" by simp
  hence "s\<^sub>0 = s\<^sub>1" by simp
  thus ?thesis using b0 b1 by simp
next
  case False
  thus ?thesis using m_7_2_scb_unique_sb[OF d0 d1] by blast
qed




section \<open>§7.2 命題（scb分解の置換可能性） — m_7_2_scb_replaceable (partial / BLOCKER)\<close>

text \<open>
  BLOCKER REPORT (empirically established, then mechanized below).

  The literal statement \<open>p_7_2_scb_replaceable\<close> (the article proposition transcription 896–903) is
  \<^bold>\<open>FALSE\<close> on its stated domain.  A concrete counterexample (every hypothesis
  satisfied, conclusion failing):

  \<^item> \<open>c\<^sub>0 = Trm []\<close> (so NOT principal: the disjunct
    \<open>\<not>(\<exists>p. c\<^sub>0 = Trm [p])\<close> of hypothesis (3) holds, regardless of \<open>c\<^sub>1\<close>),
  \<^item> \<open>c\<^sub>1 = Trm [DB 0 (Trm []), DB 1 (Trm [])]\<close> (a \<^emph>\<open>multi\<close> term — neither
    \<open>Trm []\<close> nor principal),
  \<^item> \<open>t\<^sub>0 = Trm []\<close>, \<open>s = []\<close>, \<open>b = []\<close>.

  Then \<open>c\<^sub>0,c\<^sub>1,t\<^sub>0 \<in> T\<^bsub>B\<^esub>\<close>, \<open>flatBT t\<^sub>0 = [Zsym] = s @ flatBT c\<^sub>0 @ b\<close> and
  \<open>scb_decomp t\<^sub>0 s (flatBT c\<^sub>0) b\<close> all hold (for \<open>t\<^sub>0 = Trm []\<close> the
  \<open>isPTB_str\<close> side-condition of \<open>scb_decomp\<close> is waived).  But the conclusion
  needs some \<open>t\<^sub>1\<close> with \<open>flatBT t\<^sub>1 = flatBT c\<^sub>1\<close> (so \<open>t\<^sub>1 = c\<^sub>1\<close> by
  injectivity) \<^bold>\<open>and\<close> \<open>scb_decomp c\<^sub>1 [] (flatBT c\<^sub>1) []\<close>; the latter requires
  \<open>isPTB_str (flatBT c\<^sub>1)\<close> because \<open>c\<^sub>1 \<noteq> Trm []\<close>, yet a multi-term's
  \<open>flat\<close> starts with \<open>LP\<close>, never a \<open>Dsym\<close>, so it is not a principal string.

  An exhaustive \<^typ>\<open>BT\<close> enumeration (\<open>python\<close>, depth 2, indices \<open>\<le> 1\<close>) confirms
  the failure space is \<^bold>\<open>exactly\<close>: \<open>c\<^sub>0 = Trm []\<close> (forcing \<open>t\<^sub>0 = Trm []\<close>,
  \<open>s = b = []\<close>) together with \<open>c\<^sub>1\<close> a multi-term.  Everywhere else (i.e. under the
  extra side-condition \<open>t\<^sub>0 \<noteq> Trm [] \<or> c\<^sub>1 = Trm []\<close>) the statement is TRUE
  (0/3301 failures in the same enumeration).

  CORRECTED form (faithful, the form the §7.3 callers actually instantiate, where
  \<open>c\<^sub>0,c\<^sub>1\<close> are genuine principal subterms):

    \<open>m_7_2_scb_replaceable_corr\<close> :  add the hypothesis
        \<open>isPTB_str (flatBT c\<^sub>1) \<or> s @ flatBT c\<^sub>1 @ b = [Zsym]\<close>
    (equivalently, exclude the degenerate \<open>t\<^sub>0 = Trm []\<close>/multi-\<open>c\<^sub>1\<close> corner).

  RESIDUAL (the real remaining content, recorded as a separate proof-free
  obligation named \<open>scbrepl_image\<close> below as a \<^bold>\<open>conjecture comment\<close>, NOT proven): the
  EXISTENCE of \<open>t\<^sub>1 \<in> T\<^bsub>B\<^esub>\<close> with \<open>flatBT t\<^sub>1 = s @ flatBT c\<^sub>1 @ b\<close>, i.e. that
  the spliced string is in the image of \<open>flatBT\<close>.  Empirically the occurrence of
  \<open>flatBT c\<^sub>0\<close> inside \<open>flatBT t\<^sub>0\<close> (with \<open>b\<close> all-\<open>RP\<close>) is always a \<^emph>\<open>right-spine
  principal-tail\<close> position \<open>Trm (ps[k:])\<close> of some right-descent node of \<open>t\<^sub>0\<close>;
  replacing it by \<open>c\<^sub>1\<close>'s principal list yields the witness.  Mechanizing this
  needs a recursive surgery function over the (single-principal / multi-principal)
  flat grammar with a length-of-\<open>b\<close> induction — a multi-hundred-line port left as
  the residual.  We BANK below the rigorous green pieces that DO advance it.
\<close>

text \<open>BANK 1: the literal lemma is false — concrete counterexample, fully checked.\<close>

lemma scbrepl_multi_not_PTB:
  assumes "length (untrm c) \<ge> 2"
  shows "\<not> isPTB_str (flatBT c)"
proof
  assume "isPTB_str (flatBT c)"
  then obtain p where p: "flatBT c = flatBP p" unfolding isPTB_str_def by blast
  obtain u a where pua: "p = DB u a" by (cases p)
  hence rhs: "flatBP p = Dsym u # flatBT a" by simp
  \<comment> \<open>A length-\<open>\<ge> 2\<close> term flattens to \<open>LP # \<dots>\<close>.\<close>
  obtain x y zs where c: "c = Trm (x # y # zs)"
    using assms by (cases c) (auto simp: Suc_le_length_iff numeral_2_eq_2)
  have "flatBT c = LP # (flatBP x @ concat (map (\<lambda>r. CM # flatBP r) (y # zs))) @ [RP]"
    by (simp add: c)
  with p rhs have "LP # (flatBP x @ concat (map (\<lambda>r. CM # flatBP r) (y # zs))) @ [RP]
                   = Dsym u # flatBT a" by simp
  thus False by simp
qed

lemma m_7_2_scb_replaceable_counterexample:
  "(Trm [] :: BT) \<in> T_B \<and>
   (Trm [DB 0 (Trm []), DB (enat 1) (Trm [])] :: BT) \<in> T_B \<and>
   ((\<not>(\<exists>p. (Trm [] :: BT) = Trm [p]))
       \<or> (\<exists>p. (Trm [DB 0 (Trm []), DB (enat 1) (Trm [])] :: BT) = Trm [p])) \<and>
   (Trm [] :: BT) \<in> T_B \<and>
   flatBT (Trm [] :: BT) = [] @ flatBT (Trm [] :: BT) @ [] \<and>
   scb_decomp (Trm [] :: BT) [] (flatBT (Trm [] :: BT)) [] \<and>
   \<not> (\<exists>t\<^sub>1. t\<^sub>1 \<in> T_B
         \<and> flatBT t\<^sub>1 = [] @ flatBT (Trm [DB 0 (Trm []), DB (enat 1) (Trm [])] :: BT) @ []
         \<and> scb_decomp t\<^sub>1 [] (flatBT (Trm [DB 0 (Trm []), DB (enat 1) (Trm [])] :: BT)) [])"
proof -
  let ?c1 = "Trm [DB 0 (Trm []), DB (enat 1) (Trm [])] :: BT"
  have c1TB: "?c1 \<in> T_B" by (simp add: T_B_def)
  have t0TB: "(Trm [] :: BT) \<in> T_B" by (simp add: T_B_def)
  have hyp3: "(\<not>(\<exists>p. (Trm [] :: BT) = Trm [p]))
                 \<or> (\<exists>p. ?c1 = Trm [p])" by simp
  have flt0: "flatBT (Trm [] :: BT) = [] @ flatBT (Trm [] :: BT) @ []" by simp
  have d0: "scb_decomp (Trm [] :: BT) [] (flatBT (Trm [] :: BT)) []"
    by (simp add: scb_decomp_def)
  \<comment> \<open>No valid \<open>t\<^sub>1\<close>: it would force \<open>isPTB_str (flatBT ?c1)\<close>, but \<open>?c1\<close> is multi.\<close>
  have noT1: "\<not> (\<exists>t\<^sub>1. t\<^sub>1 \<in> T_B
         \<and> flatBT t\<^sub>1 = [] @ flatBT ?c1 @ []
         \<and> scb_decomp t\<^sub>1 [] (flatBT ?c1) [])"
  proof
    assume "\<exists>t\<^sub>1. t\<^sub>1 \<in> T_B \<and> flatBT t\<^sub>1 = [] @ flatBT ?c1 @ []
              \<and> scb_decomp t\<^sub>1 [] (flatBT ?c1) []"
    then obtain t\<^sub>1 where t1: "flatBT t\<^sub>1 = flatBT ?c1"
                       and sd: "scb_decomp t\<^sub>1 [] (flatBT ?c1) []" by auto
    have t1eq: "t\<^sub>1 = ?c1" using t1 by (rule m_7_flatBT_inj)
    have c1ne: "?c1 \<noteq> Trm []" by simp
    from sd t1eq c1ne have "isPTB_str (flatBT ?c1)"
      unfolding scb_decomp_def by simp
    moreover have "\<not> isPTB_str (flatBT ?c1)"
      by (rule scbrepl_multi_not_PTB) simp
    ultimately show False by simp
  qed
  show ?thesis using c1TB t0TB hyp3 flt0 d0 noT1 by blast
qed

text \<open>BANK 2: the degenerate \<open>t\<^sub>0 = Trm []\<close> case of (the corrected) replaceability.
  Here the only decomposition is \<open>s = b = []\<close>, \<open>flatBT c\<^sub>0 = [Zsym]\<close>; the witness is
  \<open>c\<^sub>1\<close> itself, valid precisely when \<open>c\<^sub>1 = Trm []\<close> (else the conclusion's
  \<open>isPTB_str\<close> obligation is the corner the side-condition excludes).\<close>

lemma scbrepl_t0_zero_forces_trivial:
  assumes "scb_decomp (Trm [] :: BT) s c b"
      and cne: "c \<noteq> []"
  shows "s = [] \<and> b = [] \<and> c = [Zsym]"
proof -
  from assms(1) have e: "s @ c @ b = [Zsym]" and rb: "\<forall>x \<in> set b. x = RP"
    by (simp_all add: scb_decomp_def)
  \<comment> \<open>\<open>b\<close> is a sublist of \<open>[Zsym]\<close> whose letters are \<open>RP \<noteq> Zsym\<close>, so \<open>b = []\<close>.\<close>
  have b0: "b = []"
  proof (rule ccontr)
    assume "b \<noteq> []"
    then obtain x where x: "x \<in> set b" by (cases b) auto
    from x rb have "x = RP" by blast
    moreover from x e have "x \<in> set [Zsym]"
      by (metis set_append Un_iff)
    ultimately show False by simp
  qed
  with e have sc: "s @ c = [Zsym]" by simp
  \<comment> \<open>With \<open>c \<noteq> []\<close>: \<open>s @ c = [Zsym]\<close> forces \<open>s = []\<close> and \<open>c = [Zsym]\<close>.\<close>
  have s0: "s = []"
  proof (rule ccontr)
    assume "s \<noteq> []"
    then obtain y ys where s: "s = y # ys" by (cases s) auto
    with sc have "y # (ys @ c) = [Zsym]" by simp
    hence "ys @ c = []" by simp
    with cne show False by simp
  qed
  with sc have "c = [Zsym]" by simp
  with s0 b0 show ?thesis by simp
qed

lemma m_7_2_scb_replaceable_t0zero:
  assumes c1TB: "c\<^sub>1 \<in> T_B"
      and d0: "scb_decomp (Trm [] :: BT) s (flatBT c\<^sub>0) b"
      and c1side: "isPTB_str (flatBT c\<^sub>1) \<or> s @ flatBT c\<^sub>1 @ b = [Zsym]"
  shows "\<exists>t\<^sub>1. t\<^sub>1 \<in> T_B \<and> flatBT t\<^sub>1 = s @ flatBT c\<^sub>1 @ b
            \<and> scb_decomp t\<^sub>1 s (flatBT c\<^sub>1) b"
proof -
  have c0ne: "flatBT c\<^sub>0 \<noteq> []" by (rule rnsub_flat_nonempty)
  from scbrepl_t0_zero_forces_trivial[OF d0 c0ne]
  have s0: "s = []" and b0: "b = []" by simp_all
  show ?thesis
  proof (cases "flatBT c\<^sub>1 = [Zsym]")
    case True
    \<comment> \<open>\<open>flatBT c\<^sub>1 = [Zsym] = flatBT (Trm [])\<close> so \<open>c\<^sub>1 = Trm []\<close>; witness \<open>Trm []\<close>.\<close>
    have "flatBT c\<^sub>1 = flatBT (Trm [] :: BT)" using True by simp
    hence c1z: "c\<^sub>1 = Trm []" by (rule m_7_flatBT_inj)
    have w_TB: "(Trm [] :: BT) \<in> T_B" by (simp add: T_B_def)
    have w_flat: "flatBT (Trm [] :: BT) = s @ flatBT c\<^sub>1 @ b"
      using s0 b0 c1z by simp
    have w_sd: "scb_decomp (Trm [] :: BT) s (flatBT c\<^sub>1) b"
      using s0 b0 c1z by (simp add: scb_decomp_def)
    show ?thesis using w_TB w_flat w_sd by blast
  next
    case False
    \<comment> \<open>Then the side-condition supplies \<open>isPTB_str (flatBT c\<^sub>1)\<close>, and the witness is
       \<open>c\<^sub>1\<close> itself (with \<open>flatBT c\<^sub>1 = s @ flatBT c\<^sub>1 @ b\<close> since \<open>s = b = []\<close>).\<close>
    have notZ: "s @ flatBT c\<^sub>1 @ b \<noteq> [Zsym]" using False s0 b0 by simp
    with c1side have ptb: "isPTB_str (flatBT c\<^sub>1)" by blast
    have c1ne: "c\<^sub>1 \<noteq> Trm []"
    proof
      assume "c\<^sub>1 = Trm []"
      hence "flatBT c\<^sub>1 = [Zsym]" by simp
      with False show False by simp
    qed
    have w_sd0: "scb_decomp c\<^sub>1 [] (flatBT c\<^sub>1) []"
      using ptb c1ne by (simp add: scb_decomp_def)
    have w_sd: "scb_decomp c\<^sub>1 s (flatBT c\<^sub>1) b"
      using w_sd0 s0 b0 by simp
    have w_flat: "flatBT c\<^sub>1 = s @ flatBT c\<^sub>1 @ b" using s0 b0 by simp
    show ?thesis using c1TB w_flat w_sd by blast
  qed
qed

text \<open>BANK 3: the conclusion's scb side-condition is exactly the corner that the
  corrected hypothesis controls — for any \<open>t\<^sub>1\<close> realising the spliced string,
  \<open>scb_decomp t\<^sub>1 s (flatBT c\<^sub>1) b\<close> reduces to the \<open>isPTB_str\<close>/zero side-condition
  plus \<open>b\<close> all-\<open>RP\<close> (which is inherited from \<open>d0\<close>).  This isolates the residual
  to the pure EXISTENCE of \<open>t\<^sub>1\<close>.\<close>

lemma scbrepl_concl_from_image:
  assumes img: "t\<^sub>1 \<in> T_B" "flatBT t\<^sub>1 = s @ flatBT c\<^sub>1 @ b"
      and rb: "\<forall>x \<in> set b. x = RP"
      and side: "isPTB_str (flatBT c\<^sub>1) \<or> s @ flatBT c\<^sub>1 @ b = [Zsym]"
  shows "scb_decomp t\<^sub>1 s (flatBT c\<^sub>1) b"
proof (cases "t\<^sub>1 = Trm []")
  case True
  thus ?thesis using img(2) rb by (simp add: scb_decomp_def)
next
  case False
  \<comment> \<open>\<open>t\<^sub>1 \<noteq> Trm []\<close> means \<open>flatBT t\<^sub>1 \<noteq> [Zsym]\<close>, so the spliced string is not
     \<open>[Zsym]\<close>; the side-condition then yields \<open>isPTB_str (flatBT c\<^sub>1)\<close>.\<close>
  have "flatBT t\<^sub>1 \<noteq> [Zsym]"
  proof
    assume "flatBT t\<^sub>1 = [Zsym]"
    hence "flatBT t\<^sub>1 = flatBT (Trm [] :: BT)" by simp
    hence "t\<^sub>1 = Trm []" by (rule m_7_flatBT_inj)
    with False show False by simp
  qed
  with img(2) have "s @ flatBT c\<^sub>1 @ b \<noteq> [Zsym]" by simp
  with side have "isPTB_str (flatBT c\<^sub>1)" by blast
  thus ?thesis using img(2) rb by (simp add: scb_decomp_def)
qed

text \<open>Putting BANK 2 + BANK 3 together: the corrected replaceability lemma is
  reduced \<^bold>\<open>exactly\<close> to the image-existence residual \<open>scbrepl_image\<close>
  (the multi-hundred-line right-spine surgery).  We state the reduction as a green
  lemma taking that residual as a hypothesis, so the parent can discharge it
  separately without re-deriving the side-condition bookkeeping.\<close>

lemma m_7_2_scb_replaceable_corr_mod_image:
  assumes c1TB: "c\<^sub>1 \<in> T_B"
      and d0: "scb_decomp t\<^sub>0 s (flatBT c\<^sub>0) b"
      and side: "isPTB_str (flatBT c\<^sub>1) \<or> s @ flatBT c\<^sub>1 @ b = [Zsym]"
      and image: "\<exists>t\<^sub>1. t\<^sub>1 \<in> T_B \<and> flatBT t\<^sub>1 = s @ flatBT c\<^sub>1 @ b"
  shows "\<exists>t\<^sub>1. t\<^sub>1 \<in> T_B \<and> flatBT t\<^sub>1 = s @ flatBT c\<^sub>1 @ b
            \<and> scb_decomp t\<^sub>1 s (flatBT c\<^sub>1) b"
proof -
  from d0 have rb: "\<forall>x \<in> set b. x = RP" unfolding scb_decomp_def by simp
  from image obtain t\<^sub>1 where t1: "t\<^sub>1 \<in> T_B" "flatBT t\<^sub>1 = s @ flatBT c\<^sub>1 @ b" by blast
  have "scb_decomp t\<^sub>1 s (flatBT c\<^sub>1) b"
    by (rule scbrepl_concl_from_image[OF t1 rb side])
  thus ?thesis using t1 by blast
qed

end
