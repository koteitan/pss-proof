theory Support_7_027
  imports Frontier_7_032
begin

text \<open>命題 (§7.4, 訂正 A19): \<open>Mark\<close> preserves the column order.  For marked
  columns \<open>m\<^sub>0, m\<^sub>1\<close>, \<open>m\<^sub>0 < m\<^sub>1\<close> iff the marked images differ and \<open>Mark M m\<^sub>0\<close>
  nests \<open>Mark M m\<^sub>1\<close> in \<open>MarkedB\<close> (pair order \<open>(Mark M m\<^sub>0, Mark M m\<^sub>1)\<close>).\<close>

lemma m_7_4_Mark_order:
  assumes MR: "M \<in> RT_PS" and m0M: "(M, m0) \<in> Marked" and m1M: "(M, m1) \<in> Marked"
  shows "(m0 < m1) \<longleftrightarrow> (Mark M m1 \<noteq> Mark M m0 \<and> (Mark M m0, Mark M m1) \<in> MarkedB)"
proof
  assume lt: "m0 < m1"
  have m0le: "m0 \<le> m1" using lt by simp
  have nest: "(Mark M m0, Mark M m1) \<in> MarkedB"
    using Mark_MarkedB_nest[THEN mp, THEN mp, THEN mp, THEN mp, OF m0M m1M m0le MR] .
  have m1le: "m1 \<le> Lng M - 1"
  proof -
    have "leR M 0 m1 (Lng M - 1)" using m1M by (simp add: Marked_def)
    hence "m1 < Lng M" by (simp add: leR_def le0_def)
    thus ?thesis by linarith
  qed
  have distinct: "Mark M m1 \<noteq> Mark M m0"
  proof (cases "0 < m0")
    case True
    show ?thesis using Mark_distinct[OF MR m0M m1M True lt m1le] by auto
  next
    case False
    hence m00: "m0 = 0" by simp
    have m1pos: "0 < m1" using lt m00 by simp
    have "Mark M m1 \<noteq> Trans M"
      using Mark0_ne_Mark[OF MR _ m1M m1pos] m0M m00 by simp
    moreover have "Mark M m0 = Trans M"
      using ra_Mark0_eq_Trans[THEN mp, THEN mp, OF _ MR] m0M m00 by simp
    ultimately show ?thesis by simp
  qed
  show "Mark M m1 \<noteq> Mark M m0 \<and> (Mark M m0, Mark M m1) \<in> MarkedB"
    using distinct nest by simp
next
  assume H: "Mark M m1 \<noteq> Mark M m0 \<and> (Mark M m0, Mark M m1) \<in> MarkedB"
  have neM: "Mark M m1 \<noteq> Mark M m0" using H by simp
  have nest01: "(Mark M m0, Mark M m1) \<in> MarkedB" using H by simp
  show "m0 < m1"
  proof (rule ccontr)
    assume "\<not> m0 < m1"
    hence m1le0: "m1 \<le> m0" by simp
    have nest10: "(Mark M m1, Mark M m0) \<in> MarkedB"
      using Mark_MarkedB_nest[THEN mp, THEN mp, THEN mp, THEN mp, OF m1M m0M m1le0 MR] .
    have "Mark M m0 = Mark M m1"
      by (rule MarkedB_antisym[OF nest01 nest10])
    thus False using neM by simp
  qed
qed

end
