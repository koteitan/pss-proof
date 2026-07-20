theory Support_7_010
  imports Frontier_7_013
begin

text \<open>BANK (conjunct 1): \<open>(t +\<^sub>B c, c) \<in> MarkedB\<close>.  The witness decomposition marks
  the last (snoc) principal \<open>p\<close>, supplied by \<open>rnsub_flat_pre_post\<close>.\<close>

lemma m_7_2_add_scb_conj1:
  assumes tTB: "t \<in> T_B" and cTB: "c \<in> T_B" and cp: "\<exists>p. c = Trm [p]"
  shows "(t +\<^sub>B c, c) \<in> MarkedB"
proof -
  from cp obtain p where cpe: "c = Trm [p]" by blast
  obtain u a where pua: "p = DB u a" by (cases p)
  define xs where "xs = untrm t @ [DB u a]"
  have tc_eq: "t +\<^sub>B c = Trm xs"
    using cpe pua addscb_addBT_snoc[of t p] unfolding xs_def by simp
  have xs_ne: "xs \<noteq> []" unfolding xs_def by simp
  have xs_last: "last xs = DB u a" unfolding xs_def by simp
  from rnsub_flat_pre_post[OF xs_ne xs_last]
  obtain pre post where post_RP: "\<forall>x \<in> set post. x = RP"
      and flat_split: "flatBT (Trm xs) = pre @ (Dsym u # flatBT a) @ post"
    by blast
  \<comment> \<open>\<open>flatBT c = flatBP p = Dsym u # flatBT a\<close>.\<close>
  have fc_eq: "flatBT c = Dsym u # flatBT a"
    using cpe pua by simp
  have ptb: "isPTB_str (flatBT c)"
    using addscb_princ_isPTB[OF cTB cpe] .
  have tc_ne: "t +\<^sub>B c \<noteq> Trm []"
    using tc_eq xs_ne by simp
  have sd: "scb_decomp (t +\<^sub>B c) pre (flatBT c) post"
    unfolding scb_decomp_def
    using flat_split fc_eq post_RP ptb tc_eq tc_ne by simp
  thus ?thesis unfolding MarkedB_def by auto
qed

text \<open>A13 COUNTEREXAMPLE (conjunct 3 is FALSE as literally transcribed).

  Take \<open>t = 0\<close>, \<open>c = D\<^sub>0 0\<close>, \<open>c' = D\<^sub>0(D\<^sub>0 0)\<close>, \<open>v = 0\<close>, and
  \<open>u\<^sub>1 = (D\<^sub>0(D\<^sub>0 0), D\<^sub>0 0)\<close> (a 2-principal term).  Then
  \<open>flatBT u\<^sub>1 = ( D\<^sub>0 D\<^sub>0 0 , D\<^sub>0 0 )\<close>.  With \<open>s\<^sub>1 = (\<close>, \<open>b\<^sub>1 = , D\<^sub>0 0 )\<close> the
  hypothesis \<open>flatBT u\<^sub>1 = s\<^sub>1 @ (D\<^sub>v # flatBT (t+c)) @ b\<^sub>1\<close> holds (the \<open>D\<^sub>v(t+c)\<close>
  slice is the \<^bold>\<open>first\<close> principal).  The UNIQUE valid scb-decomposition of
  \<open>u\<^sub>1\<close> with \<open>c\<close>-string \<open>flatBT c = D\<^sub>0 0\<close> marks the \<^bold>\<open>second\<close> principal:
  \<open>s\<^sub>0 = ( D\<^sub>0 D\<^sub>0 0 ,\<close>, \<open>b\<^sub>0 = )\<close> (the first-principal occurrence has a non-\<open>)\<close>
  tail, so it is not a valid mark).  The conclusion would need one \<open>u\<^sub>1'\<close> with
  BOTH \<open>flatBT u\<^sub>1' = s\<^sub>1 @ (D\<^sub>v # flatBT (t+c')) @ b\<^sub>1\<close> AND
  \<open>flatBT u\<^sub>1' = s\<^sub>0 @ flatBT c' @ b\<^sub>0\<close>; these two strings differ, so by
  \<open>flatBT\<close>-injectivity no such \<open>u\<^sub>1'\<close> exists.\<close>

lemma m_7_2_add_scb_conj3_counterexample:
  defines "t \<equiv> (Trm [] :: BT)"
      and "c \<equiv> (Trm [DB 0 (Trm [])] :: BT)"
      and "c' \<equiv> (Trm [DB 0 (Trm [DB 0 (Trm [])])] :: BT)"
      and "u1 \<equiv> (Trm [DB 0 (Trm [DB 0 (Trm [])]), DB 0 (Trm [])] :: BT)"
      and "v \<equiv> (0 :: nat)"
      and "s1 \<equiv> [LP]"
      and "b1 \<equiv> [CM, Dsym 0, Zsym, RP]"
      and "s0 \<equiv> [LP, Dsym 0, Dsym 0, Zsym, CM]"
      and "b0 \<equiv> [RP]"
  shows "t \<in> T_B \<and> c \<in> T_B \<and> (\<exists>p. c = Trm [p])
       \<and> c' \<in> T_B \<and> (\<exists>p. c' = Trm [p])
       \<and> u1 \<in> T_B
       \<and> flatBT u1 = s1 @ (Dsym (enat v) # flatBT (t +\<^sub>B c)) @ b1
       \<and> scb_decomp u1 s0 (flatBT c) b0
       \<and> \<not> (\<exists>u1'. u1' \<in> T_B
              \<and> flatBT u1' = s1 @ (Dsym (enat v) # flatBT (t +\<^sub>B c')) @ b1
              \<and> scb_decomp u1' s0 (flatBT c') b0)"
proof -
  have tTB: "t \<in> T_B" unfolding t_def by (simp add: T_B_def)
  have cTB: "c \<in> T_B" unfolding c_def by (simp add: T_B_def)
  have cP: "\<exists>p. c = Trm [p]" unfolding c_def by blast
  have c'TB: "c' \<in> T_B" unfolding c'_def by (simp add: T_B_def)
  have c'P: "\<exists>p. c' = Trm [p]" unfolding c'_def by blast
  have u1TB: "u1 \<in> T_B" unfolding u1_def by (simp add: T_B_def)
  \<comment> \<open>flat strings (evaluated by the \<open>flatBT\<close> simp rules).\<close>
  have ftc: "flatBT (t +\<^sub>B c) = [Dsym 0, Zsym]"
    unfolding t_def c_def by simp
  have hyp_flat: "flatBT u1 = s1 @ (Dsym (enat v) # flatBT (t +\<^sub>B c)) @ b1"
    unfolding u1_def s1_def b1_def v_def t_def c_def
    by (simp add: zero_enat_def)
  \<comment> \<open>the chosen scb-decomposition of \<open>u\<^sub>1\<close> (marks the 2nd principal).\<close>
  have fc: "flatBT c = [Dsym 0, Zsym]" unfolding c_def by simp
  have u1flat: "flatBT u1 =
      [LP, Dsym 0, Dsym 0, Zsym, CM, Dsym 0, Zsym, RP]"
    unfolding u1_def by simp
  have sd: "scb_decomp u1 s0 (flatBT c) b0"
    unfolding scb_decomp_def
  proof (intro conjI)
    show "flatBT u1 = s0 @ flatBT c @ b0"
      unfolding s0_def b0_def using u1flat fc by simp
    show "u1 \<noteq> Trm [] \<longrightarrow> isPTB_str (flatBT c)"
      using addscb_princ_isPTB[OF cTB] cP by blast
    show "\<forall>x \<in> set b0. x = RP" unfolding b0_def by simp
  qed
  \<comment> \<open>No \<open>u\<^sub>1'\<close>: the two required flat strings differ.\<close>
  have ftc': "flatBT (t +\<^sub>B c') =
      [Dsym 0, Dsym 0, Zsym]"
    unfolding t_def c'_def by simp
  have want_eq: "s1 @ (Dsym (enat v) # flatBT (t +\<^sub>B c')) @ b1
      = [LP, Dsym 0, Dsym 0, Dsym 0, Zsym,
         CM, Dsym 0, Zsym, RP]"
    unfolding s1_def b1_def v_def using ftc' by (simp add: zero_enat_def)
  have fc': "flatBT c' = [Dsym 0, Dsym 0, Zsym]"
    unfolding c'_def by simp
  have need_eq: "s0 @ flatBT c' @ b0
      = [LP, Dsym 0, Dsym 0, Zsym, CM,
         Dsym 0, Dsym 0, Zsym, RP]"
    unfolding s0_def b0_def using fc' by simp
  \<comment> \<open>The two explicit lists differ at index 3 (\<open>Dsym\<close> vs \<open>Zsym\<close>).\<close>
  have lists_differ:
    "[LP, Dsym 0, Dsym 0, Dsym 0, Zsym,
      CM, Dsym 0, Zsym, RP]
     \<noteq> [LP, Dsym 0, Dsym 0, Zsym, CM,
        Dsym 0, Dsym 0, Zsym, RP]"
    by simp
  have noU1': "\<not> (\<exists>u1'. u1' \<in> T_B
              \<and> flatBT u1' = s1 @ (Dsym (enat v) # flatBT (t +\<^sub>B c')) @ b1
              \<and> scb_decomp u1' s0 (flatBT c') b0)"
  proof
    assume "\<exists>u1'. u1' \<in> T_B
              \<and> flatBT u1' = s1 @ (Dsym (enat v) # flatBT (t +\<^sub>B c')) @ b1
              \<and> scb_decomp u1' s0 (flatBT c') b0"
    then obtain u1' where
        f1: "flatBT u1' = s1 @ (Dsym (enat v) # flatBT (t +\<^sub>B c')) @ b1"
      and sd': "scb_decomp u1' s0 (flatBT c') b0" by blast
    \<comment> \<open>Rewrite both sides to their explicit evaluated lists.\<close>
    have lhs: "flatBT u1' =
        [LP, Dsym 0, Dsym 0, Dsym 0, Zsym,
         CM, Dsym 0, Zsym, RP]"
      using f1 want_eq by simp
    have "flatBT u1' = s0 @ flatBT c' @ b0"
      using sd' unfolding scb_decomp_def by simp
    hence rhs: "flatBT u1' =
        [LP, Dsym 0, Dsym 0, Zsym, CM,
         Dsym 0, Dsym 0, Zsym, RP]"
      using need_eq by simp
    \<comment> \<open>\<open>flatBT u1'\<close> equals two distinct concrete lists — contradiction.\<close>
    from lhs rhs lists_differ show False by simp
  qed
  show ?thesis
    using tTB cTB cP c'TB c'P u1TB hyp_flat sd noU1' by blast
qed

end
