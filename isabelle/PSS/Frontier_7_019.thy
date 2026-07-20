theory Frontier_7_019
  imports Support_7_015
begin

text \<open>First value bricks on the new domain: \<open>Trans\<close>/\<open>Mark\<close> on reduced
  singletons \<open>[(v,v)]\<close> (= all reduced length-1 sequences,
  @{thm [source] m_6_6_oneColumn}), via the (A) branch of the recursion.\<close>

lemma Trans_singleton:
  "Trans [(v, v)] = (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)"
proof -
  have RT: "[(v, v)] \<in> RT_PS"
  proof -
    have "([(v, v)]::pairseq) \<in> T_PS" by (simp add: T_PS_def)
    thus ?thesis using m_6_6_oneColumn[of "[(v, v)]"] by auto
  qed
  have dom: "Trans_Mark_dom (Inl [(v, v)])" by (rule m_7_3_Trans_welldef[OF RT])
  show ?thesis
    using Trans.psimps[OF dom] RT by (simp add: entry_def)
qed

lemma Mark_singleton:
  "Mark [(v, v)] m = (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)"
proof -
  have RT: "[(v, v)] \<in> RT_PS"
  proof -
    have "([(v, v)]::pairseq) \<in> T_PS" by (simp add: T_PS_def)
    thus ?thesis using m_6_6_oneColumn[of "[(v, v)]"] by auto
  qed
  have dom: "Trans_Mark_dom (Inr ([(v, v)], m))" by (rule m_7_3_Mark_welldef[OF RT])
  show ?thesis
    using Mark.psimps[OF dom] RT by (simp add: entry_def)
qed


text \<open>\<open>unflatBT\<close> inverts \<open>flatBT\<close> (by @{thm [source] m_7_flatBT_inj}); this is
  how the \<open>s\<^sub>1 c\<^sub>2 b\<^sub>1\<close> concatenations in \<open>Trans\<close>/\<open>Mark\<close> evaluate.\<close>

lemma unflatBT_flat: "unflatBT (flatBT t) = t"
  unfolding unflatBT_def
  by (rule the_equality) (auto intro: m_7_flatBT_inj)


text \<open>Evaluating the \<open>SOME\<close> scb-extraction of \<open>Trans\<close>/\<open>Mark\<close> in the trivial
  case \<open>t\<^sub>1 = c\<^sub>1\<close> (e.g. both \<open>D\<^sub>v 0\<close>): the unique \<open>(s,b)\<close> is \<open>([], [])\<close>
  (@{thm [source] m_7_2_scb_unique_sb}).\<close>

lemma isPTB_str_Dpt:
  assumes "v \<noteq> \<infinity>" and "dfree_BT t"
  shows "isPTB_str (flatBT (Dpt v t))"
proof -
  have "dfree_BP (DB v t)" using assms by simp
  moreover have "flatBT (Dpt v t) = flatBP (DB v t)" by simp
  ultimately show ?thesis unfolding isPTB_str_def by blast
qed

lemma scb_decomp_self:
  assumes "isPTB_str (flatBT t)"
  shows "scb_decomp t [] (flatBT t) []"
  using assms by (simp add: scb_decomp_def)

lemma scb_SOME_self:
  assumes pt: "isPTB_str (flatBT t)" and tne: "t \<noteq> Trm []"
  shows "(SOME sb. scb_decomp t (fst sb) (flatBT t) (snd sb)) = ([], [])"
proof (rule some_equality)
  show "scb_decomp t (fst ([], [])) (flatBT t) (snd ([], []))"
    using scb_decomp_self[OF pt] by simp
next
  fix sb assume h: "scb_decomp t (fst sb) (flatBT t) (snd sb)"
  have "fst sb = [] \<and> snd sb = []"
    using m_7_2_scb_unique_sb[OF h scb_decomp_self[OF pt] tne] by simp
  thus "sb = ([], [])" by (cases sb) auto
qed

end
