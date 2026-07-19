theory P_6_6_oneColumn
  imports Frontier_6_091
begin

text \<open>系（\<open>1\<close>列ペア数列の基本性質） — the reduced length-1 sequences are exactly
  the diagonals \<open>((v,v))\<close>.\<close>

text \<open>系（\<open>1\<close>列ペア数列の基本性質）: the reduced length-1 sequences are exactly
  the diagonal singletons \<open>[(v,v)]\<close>.\<close>

lemma m_6_6_oneColumn:
  assumes MT: "M \<in> T_PS"
  shows "(Lng M = 1 \<and> M \<in> RT_PS) \<longleftrightarrow> (\<exists>v. M = [(v, v)])"
proof
  assume L: "Lng M = 1 \<and> M \<in> RT_PS"
  then obtain a b where Mab: "M = [(a, b)]" by (cases M) auto
  have "M = Red M" using L by (simp add: RT_PS_def)
  also have "Red M = [(b, b)]" using Mab Red_singleton by simp
  finally show "\<exists>v. M = [(v, v)]" by blast
next
  assume "\<exists>v. M = [(v, v)]"
  then obtain v where Mv: "M = [(v, v)]" by blast
  have "Red M = M" using Mv Red_singleton by simp
  thus "Lng M = 1 \<and> M \<in> RT_PS" using MT Mv by (simp add: RT_PS_def)
qed

lemma p_6_6_oneColumn:
  assumes "M \<in> T_PS"
  shows "(Lng M = 1 \<and> M \<in> RT_PS) \<longleftrightarrow> (\<exists>v. M = [(v, v)])"
  using assms by (rule m_6_6_oneColumn)

end
