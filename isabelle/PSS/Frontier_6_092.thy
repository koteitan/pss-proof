theory Frontier_6_092
  imports P_6_6_oneColumn
begin

section \<open>§6.6 補題（簡約性と係数の基本性質）\<close>

text \<open>Head of a reduced mono sequence is diagonal: from \<open>Red M = M\<close> and the
  closed form @{thm [source] m_6_5_Red_rebase} at \<open>j = 0\<close>.\<close>

lemma reduced_mono_head_diag:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
  shows "entry M 0 0 = entry M 1 0"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have condA: "RedCondA M" using m_6_6_reduced_iff_cond[OF MT] M by simp
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  have rb: "Red M = map (\<lambda>j. (entry M 0 j - entry M 0 0 + entry M 1 0,
                               entry M 1 j)) [0..<Lng M]"
    by (rule m_6_5_Red_rebase[OF MT condA nmu])
  have red: "Red M = M" using M by (simp add: RT_PS_def)
  have L0: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  have Mmap: "M = map (\<lambda>j. (entry M 0 j - entry M 0 0 + entry M 1 0,
                             entry M 1 j)) [0..<Lng M]"
    by (rule trans[OF red[symmetric] rb])
  have "M ! 0 = (entry M 0 0 - entry M 0 0 + entry M 1 0, entry M 1 0)"
    using arg_cong[OF Mmap, of "\<lambda>xs. xs ! 0"] L0 by (simp del: upt_Suc)
  hence "fst (M ! 0) = entry M 1 0" by simp
  thus ?thesis by (simp add: entry_def)
qed

text \<open>補題（簡約性と係数の基本性質）, non-multi core: every pair of a reduced
  zero/mono sequence has \<open>snd \<le> fst\<close>.  Route: prepend the diagonal
  (@{thm [source] m_6_6_reduced_leftend}, \<open>u = 0\<close>) to normalize the head to
  \<open>(0,0)\<close>, then the keystone + @{thm [source] m_6_6_condAB_coeff} (2).\<close>

lemma reduced_nonmulti_coeff_set:
  assumes M: "M \<in> RT_PS" and nmu: "\<not> multiT M"
  shows "\<forall>p \<in> set M. snd p \<le> fst p"
proof (cases "zeroT M")
  case True
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have "Red M = [(0, 0)]" using Red.psimps[OF domM] True by simp
  hence "M = [(0, 0)]" using M by (simp add: RT_PS_def)
  thus ?thesis by simp
next
  case False
  hence mono: "monoT M" using nmu by (simp add: multiT_def)
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have MPT: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  let ?v = "entry M 1 0"
  define N where "N = (if 0 < ?v then diagSeq 0 (?v - 1) else []) @ M"
  have ule0: "(0::nat) \<le> ?v" by simp
  have RL: "Red N = N \<and> monoT N"
    using m_6_6_reduced_leftend[OF M MPT ule0] N_def by simp
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have Nne: "N \<noteq> []" using Mne by (simp add: N_def)
  have NT: "N \<in> T_PS" using Nne by (simp add: T_PS_def)
  have NR: "N \<in> RT_PS" using RL NT by (simp add: RT_PS_def)
  have condAN: "RedCondA N" and condBN: "RedCondB N"
    using m_6_6_reduced_iff_cond[OF NT] NR by auto
  have e00N: "entry N 0 0 = 0" and e10N: "entry N 1 0 = 0"
  proof -
    show "entry N 0 0 = 0"
    proof (cases "0 < ?v")
      case True
      have Ld: "0 < Lng (diagSeq 0 (?v - 1))" by (simp add: diagSeq_def)
      have "N ! 0 = diagSeq 0 (?v - 1) ! 0" using True Ld by (simp add: N_def nth_append)
      also have "\<dots> = (0, 0)" by (simp add: diagSeq_def del: upt_Suc)
      finally show ?thesis by (simp add: entry_def)
    next
      case False
      hence v0: "?v = 0" by simp
      have NM: "N = M" using False by (simp add: N_def)
      have "entry M 0 0 = ?v" using reduced_mono_head_diag[OF M mono] by simp
      thus ?thesis using NM v0 by simp
    qed
  next
    show "entry N 1 0 = 0"
    proof (cases "0 < ?v")
      case True
      have Ld: "0 < Lng (diagSeq 0 (?v - 1))" by (simp add: diagSeq_def)
      have "N ! 0 = diagSeq 0 (?v - 1) ! 0" using True Ld by (simp add: N_def nth_append)
      also have "\<dots> = (0, 0)" by (simp add: diagSeq_def del: upt_Suc)
      finally show ?thesis by (simp add: entry_def)
    next
      case False
      thus ?thesis by (simp add: N_def)
    qed
  qed
  have coeffN: "\<forall>j \<le> Lng N - 1. entry N 0 j \<ge> entry N 1 j"
    using m_6_6_condAB_coeff[OF NT e00N e10N condAN] condBN by blast
  show ?thesis
  proof
    fix p assume "p \<in> set M"
    hence "p \<in> set N" by (simp add: N_def)
    then obtain j where jL: "j < Lng N" and pj: "p = N ! j"
      by (auto simp: in_set_conv_nth)
    have "j \<le> Lng N - 1" using jL by simp
    hence "entry N 1 j \<le> entry N 0 j" using coeffN by blast
    thus "snd p \<le> fst p" using pj by (simp add: entry_def)
  qed
qed

end
