theory Frontier_7_033
  imports Support_7_027
begin

text \<open>\<open>M = diagSeq u v @ [(w',w)]\<close> is mono (the row-0 trunk runs \<open>0 \<to>\<^sup>* j\<^sub>p \<to> j\<^sub>1\<close>).\<close>

text \<open>Index \<open>0\<close> is always admissible (the lower row-1 step \<open>nextR M 1 0 0\<close> is
  impossible, so \<open>0\<close> cannot be non-admissible).\<close>

lemma adm_index0: "adm M 0"
proof -
  have "\<not> nextrel1 M 0 0" by (simp add: nextrel1_def)
  hence "\<not> nextR M 1 (0 - 1) 0" by (simp add: nextR_def)
  thus ?thesis by (simp add: adm_def nadm_def)
qed

section \<open>§8 infra: Trans/Mark of a non-reduced ancestor slice = of its Red\<close>

text \<open>Foundational §8 helpers: an ancestor slice \<open>seg M j0' j1'\<close> equals
  \<open>(IncrFirst^^k)(Red (seg M j0' j1'))\<close> (@{thm [source] m_6_6_ancestor_slice_Red_IncrFirst}),
  and \<open>Trans\<close>/\<open>Mark\<close> are \<open>IncrFirst\<close>-invariant, so \<open>Trans\<close>/\<open>Mark\<close> of the (possibly
  non-reduced) slice coincide with those of its reduced form \<open>Red (seg \<dots>)\<close>, which
  is reduced+mono and computable.  Unblocks §8.1 c1-around parts (1g)/(3)/(4) and
  the §7.4 Mark-Trans representation.\<close>

lemma T_PS_funpow_IncrFirst:
  "M \<in> T_PS \<Longrightarrow> (IncrFirst ^^ k) M \<in> T_PS"
proof (induction k)
  case 0 thus ?case by simp
next
  case (Suc k)
  have "(IncrFirst ^^ k) M \<in> T_PS" using Suc by simp
  hence "IncrFirst ((IncrFirst ^^ k) M) \<in> T_PS" by (simp add: T_PS_def IncrFirst_def)
  thus ?case by simp
qed

lemma Trans_funpow_IncrFirst:
  assumes MT: "M \<in> T_PS" and RR: "Red M \<in> RT_PS"
  shows "Trans ((IncrFirst ^^ k) M) = Trans M"
proof (induction k)
  case 0 thus ?case by simp
next
  case (Suc k)
  let ?N = "(IncrFirst ^^ k) M"
  have NT: "?N \<in> T_PS" using MT by (rule T_PS_funpow_IncrFirst)
  have RN: "Red ?N \<in> RT_PS" using a1_Red_funpow_IncrFirst[OF MT] RR by simp
  have "(IncrFirst ^^ Suc k) M = IncrFirst ?N" by simp
  hence "Trans ((IncrFirst ^^ Suc k) M) = Trans (IncrFirst ?N)" by simp
  also have "\<dots> = Trans ?N" by (rule m_7_3_Trans_IncrFirst[OF NT RN])
  also have "\<dots> = Trans M" using Suc.IH by simp
  finally show ?case .
qed

end
