theory P_7_2_scb_triviality
  imports Frontier_7_012
begin

lemma m_7_2_scb_triviality:
  assumes mB: "(t, c) \<in> MarkedB"
  shows "(t = c)
       \<longleftrightarrow> (\<forall>s b. scb_decomp t s (flatBT c) b \<longrightarrow> s = [] \<and> b = [])"
    and "(t = c)
       \<longleftrightarrow> (\<exists>b. scb_decomp t [] (flatBT c) b)"
proof -
  \<comment> \<open>The MarkedB witness: some scb-decomposition with marked principal \<open>flat c\<close>.\<close>
  from mB obtain s\<^sub>w b\<^sub>w where wit: "scb_decomp t s\<^sub>w (flatBT c) b\<^sub>w"
    unfolding MarkedB_def by auto

  \<comment> \<open>Shared forward direction (1\<Rightarrow>2): trivial by the banked length count.\<close>
  have fwd2: "t = c \<Longrightarrow> (\<forall>s b. scb_decomp t s (flatBT c) b \<longrightarrow> s = [] \<and> b = [])"
    using scbtriv_eq_imp_trivial_decomp by blast

  \<comment> \<open>Show (2): \<open>t = c \<longleftrightarrow> every decomposition is trivial\<close>.\<close>
  show "(t = c)
       \<longleftrightarrow> (\<forall>s b. scb_decomp t s (flatBT c) b \<longrightarrow> s = [] \<and> b = [])"
  proof
    assume "t = c" thus "\<forall>s b. scb_decomp t s (flatBT c) b \<longrightarrow> s = [] \<and> b = []"
      by (rule fwd2)
  next
    assume triv: "\<forall>s b. scb_decomp t s (flatBT c) b \<longrightarrow> s = [] \<and> b = []"
    \<comment> \<open>Apply triviality to the MarkedB witness: \<open>s\<^sub>w = b\<^sub>w = ()\<close>.\<close>
    from triv wit have sw: "s\<^sub>w = []" and bw: "b\<^sub>w = []" by blast+
    have "flatBT t = flatBT c"
      using wit unfolding scb_decomp_def by (simp add: sw bw)
    thus "t = c" by (rule m_7_flatBT_inj)
  qed

  \<comment> \<open>Show (3): \<open>t = c \<longleftrightarrow> some \<open>s = ()\<close> decomposition exists\<close>.\<close>
  show "(t = c)
       \<longleftrightarrow> (\<exists>b. scb_decomp t [] (flatBT c) b)"
  proof
    assume tc: "t = c"
    \<comment> \<open>Witness \<open>b = ()\<close>.  \<open>flat c = () \<frown> flat c \<frown> ()\<close>; the principal-string
       condition (needed only when \<open>c \<noteq> 0\<close>) is supplied by the MarkedB witness,
       since \<open>t = c \<noteq> 0\<close> makes that witness carry \<open>isPTB_str (flat c)\<close>.\<close>
    have "scb_decomp c [] (flatBT c) []"
    proof (cases "c = Trm []")
      case True thus ?thesis by (simp add: scb_decomp_def)
    next
      case False
      hence "t \<noteq> Trm []" using tc by simp
      hence "isPTB_str (flatBT c)"
        using wit unfolding scb_decomp_def by simp
      thus ?thesis using False by (simp add: scb_decomp_def)
    qed
    thus "\<exists>b. scb_decomp t [] (flatBT c) b" using tc by blast
  next
    assume "\<exists>b. scb_decomp t [] (flatBT c) b"
    then obtain b where d: "scb_decomp t [] (flatBT c) b" by blast
    have "flatBT t = flatBT c @ b"
      using d unfolding scb_decomp_def by simp
    hence "b = []" by (rule scbtriv_flat_append_RP_nil)
    with \<open>flatBT t = flatBT c @ b\<close> have "flatBT t = flatBT c" by simp
    thus "t = c" by (rule m_7_flatBT_inj)
  qed
qed


text \<open>命題（scb分解の自明性の判定条件） (§7.2): for \<open>(t,c) \<in> T\<^bsub>B\<^esub>\<^sup>Marked\<close> the
  following are equivalent: (1) \<open>t = c\<close>; (2) every scb-decomposition \<open>(s,flat c,b)\<close>
  of \<open>t\<close> has \<open>s = ()\<close> and \<open>b = ()\<close>; (3) some scb-decomposition \<open>((),flat c,b)\<close> of
  \<open>t\<close> exists.\<close>

lemma p_7_2_scb_triviality:
  assumes "(t, c) \<in> MarkedB"
  shows "(t = c)
       \<longleftrightarrow> (\<forall>s b. scb_decomp t s (flatBT c) b \<longrightarrow> s = [] \<and> b = [])"
    and "(t = c)
       \<longleftrightarrow> (\<exists>b. scb_decomp t [] (flatBT c) b)"
proof -
  show "(t = c)
       \<longleftrightarrow> (\<forall>s b. scb_decomp t s (flatBT c) b \<longrightarrow> s = [] \<and> b = [])"
    by (rule m_7_2_scb_triviality(1)[OF assms])
  show "(t = c)
       \<longleftrightarrow> (\<exists>b. scb_decomp t [] (flatBT c) b)"
    by (rule m_7_2_scb_triviality(2)[OF assms])
qed

end
