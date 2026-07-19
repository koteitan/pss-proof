theory Frontier_6_016
  imports P_6_4_FirstNodes_TrMax_Joints
begin

text \<open>Auxiliary: \<open>FirstNodes M ! J = TrMax M + 1 + IdxSum (Br M) ! J\<close> and
  \<open>Joints M ! J = parent M 0 (FirstNodes M ! J)\<close> for \<open>J < length (Br M)\<close>.\<close>

lemma FirstNodes_nth:
  assumes "J < length (Br M)"
  shows "FirstNodes M ! J = TrMax M + 1 + IdxSum (Br M) ! J"
proof -
  have "J < length (IdxSum (Br M))" using assms by (simp add: IdxSum_def)
  thus ?thesis by (simp add: FirstNodes_def)
qed

lemma Joints_nth:
  assumes "J < length (Br M)"
  shows "Joints M ! J = parent M 0 (FirstNodes M ! J)"
  using assms by (simp add: Joints_def parent_def)

text \<open>The row-0 parent is the largest index below \<open>k\<close> whose row-0 entry is
  smaller than that of \<open>k\<close>.\<close>

lemma nextR0_largest_below:
  assumes "nextR M 0 a k" "j < k" "entry M 0 j < entry M 0 k"
  shows "j \<le> a"
proof (rule ccontr)
  assume "\<not> j \<le> a"
  hence aj: "a < j" by simp
  from assms(1) have "\<forall>j'. a < j' \<and> j' < k \<longrightarrow> entry M 0 j' \<ge> entry M 0 k"
    by (simp add: nextR_def nextrel0_def)
  hence "entry M 0 j \<ge> entry M 0 k" using aj assms(2) by blast
  thus False using assms(3) by simp
qed

text \<open>The row-0 entry at a first node equals the row-0 left-end entry of the
  corresponding branch component.\<close>

lemma entry_FirstNodes_eq_component:
  assumes M: "M \<in> PT_PS" and J: "J < length (Br M)"
  shows "entry M 0 (FirstNodes M ! J) = entry (Br M ! J) 0 0"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
  have trne: "TrMax M \<noteq> Lng M - 1"
  proof
    assume "TrMax M = Lng M - 1"
    hence "Br M = []" by (simp add: Br_def)
    with J show False by simp
  qed
  with tb have trlt: "TrMax M < Lng M - 1" by linarith
  let ?N = "seg M (TrMax M + 1) (Lng M - 1)"
  have brQ: "Br M = P ?N" using trne by (simp add: Br_def)
  have NL: "Lng ?N = Lng M - 1 - TrMax M" using trlt by simp
  have NLpos: "Lng ?N > 0" using trlt by simp
  have Nne: "?N \<noteq> []" using NLpos length_greater_0_conv by blast
  have NT: "?N \<in> T_PS" using Nne by (simp add: T_PS_def)
  have JN: "J < length (P ?N)" using J brQ by simp
  have Jle: "J \<le> Lng (P ?N) - 1" using JN by (cases "P ?N") auto
  \<comment> \<open>component as a slice of \<open>?N\<close>\<close>
  have comp: "(P ?N) ! J = seg ?N (IdxSum (P ?N) ! J) (IdxSum (P ?N) ! (J + 1) - 1)"
    by (rule m_6_4_P_IdxSum[OF NT Jle])
  have lenpos: "0 < Lng ((P ?N) ! J)"
    by (rule idxsum_P_component_nonempty[OF NT JN])
  \<comment> \<open>left-end entry of the component\<close>
  have e_comp: "entry ((P ?N) ! J) 0 0 = entry ?N 0 (IdxSum (P ?N) ! J)"
  proof -
    have lp: "0 < Lng (seg ?N (IdxSum (P ?N) ! J) (IdxSum (P ?N) ! (J + 1) - 1))"
      using lenpos by (simp only: comp[symmetric])
    have "entry (seg ?N (IdxSum (P ?N) ! J) (IdxSum (P ?N) ! (J + 1) - 1)) 0 0
         = entry ?N 0 ((IdxSum (P ?N) ! J) + 0)"
      by (rule entry_seg[OF lp])
    thus ?thesis using comp by simp
  qed
  \<comment> \<open>\<open>IdxSum\<close> value is a valid index into \<open>?N\<close>\<close>
  have idxbound: "IdxSum (P ?N) ! J \<le> Lng ?N - 1"
    using idxsum_leftend_lmin[OF NT JN] by blast
  hence idxlt: "IdxSum (P ?N) ! J < Lng ?N" using NLpos by simp
  have e_N: "entry ?N 0 (IdxSum (P ?N) ! J)
           = entry M 0 (TrMax M + 1 + IdxSum (P ?N) ! J)"
    using idxlt by (simp add: entry_seg)
  have fn: "FirstNodes M ! J = TrMax M + 1 + IdxSum (Br M) ! J"
    by (rule FirstNodes_nth[OF J])
  show ?thesis
    using e_comp e_N fn brQ by simp
qed

end
