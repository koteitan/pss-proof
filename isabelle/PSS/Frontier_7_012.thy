theory Frontier_7_012
  imports P_7_2_scb_compose
begin

subsection \<open>§7.2 命題（scb分解の自明性の判定条件） — m_7_2_scb_triviality\<close>

text \<open>
  The three-way triviality criterion (§7.2): for \<open>(t,c) \<in> T\<^bsub>B\<^esub>\<^sup>Marked\<close> the
  conditions \<open>t = c\<close>, "every \<open>(s, flat c, b)\<close> scb-decomposition of \<open>t\<close> is
  trivial (\<open>s = b = ()\<close>)", and "some \<open>((), flat c, b)\<close> scb-decomposition of
  \<open>t\<close> exists" coincide.

  At the \<^typ>\<open>BT\<close> level the article's string-identification "\<open>t = scb = c\<close>"
  is exactly \<^const>\<open>flatBT\<close> injectivity (@{thm [source] m_7_flatBT_inj}).

  \<^item> Forward (\<open>t = c \<Rightarrow>\<close> trivial): a length count, already banked as
    @{thm [source] scbtriv_eq_imp_trivial_decomp}.
  \<^item> Converse for (2): a trivial-on-both-sides decomposition gives
    \<open>flat t = flat c\<close> outright, so injectivity yields \<open>t = c\<close>.  (Any \<open>(s,b)\<close>
    decomposition exists because \<open>(t,c) \<in> MarkedB\<close>; the hypothesis forces it
    trivial.)
  \<^item> Converse for (3): an \<open>s = ()\<close> decomposition has \<open>flat t = flat c \<frown> b\<close> with
    \<open>b\<close> all-\<open>\<^bold>)\<close>.  If \<open>b \<noteq> ()\<close> then \<open>flat c\<close> is a proper nonempty prefix of the
    complete string \<open>flat t\<close>, so by prefix positivity
    (@{thm [source] flatinj_prefix_nonneg_BT}) \<open>flatinj_dsum (flat c) \<ge> 0\<close>,
    contradicting @{thm [source] flatinj_dsum_flatBT} (\<open>= -1\<close>).  Hence \<open>b = ()\<close>,
    \<open>flat t = flat c\<close>, and injectivity gives \<open>t = c\<close>.
\<close>

\<comment> \<open>The (3)\<Rightarrow>(1) engine: a trailing all-\<open>RP\<close> block appended to a complete
   \<open>flatBT\<close> string must be empty (prefix-freeness of complete strings).\<close>
lemma scbtriv_flat_append_RP_nil:
  assumes "flatBT t = flatBT c @ b"
  shows "b = []"
proof (rule ccontr)
  assume bne: "b \<noteq> []"
  have "0 \<le> flatinj_dsum (flatBT c)"
    by (rule flatinj_prefix_nonneg_BT[OF assms bne])
  thus False using flatinj_dsum_flatBT[of c] by simp
qed

end
