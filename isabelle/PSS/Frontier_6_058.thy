theory Frontier_6_058
  imports Support_6_039
begin

lemma elead_entry_diag_append_lo:
  assumes "i < Suc v - u"
  shows "entry (diagSeq u v @ rest) p i = u + i"
proof -
  have lt: "i < length (diagSeq u v)" using assms by (simp del: upt_Suc)
  have "(diagSeq u v @ rest) ! i = diagSeq u v ! i" using lt by (simp add: nth_append)
  also have "\<dots> = (u + i, u + i)" using diagSeq_nth[OF assms] by simp
  finally show ?thesis by (simp add: entry_def)
qed

lemma elead_entry_diag_append_hi:
  assumes "a < Lng rest"
  shows "entry (diagSeq u v @ rest) p ((Suc v - u) + a) = entry rest p a"
proof -
  have lp: "length (diagSeq u v) = Suc v - u" by (simp del: upt_Suc)
  have "(diagSeq u v @ rest) ! ((Suc v - u) + a) = rest ! a"
    using lp by (simp add: nth_append)
  thus ?thesis by (simp add: entry_def)
qed

text \<open>elead: \<open>monoT N\<close> where \<open>N = diagSeq u (m\<^sub>1\<^sub>0-1) @ M\<close>, for a \<open>monoT M\<close> with
  \<open>m\<^sub>1\<^sub>0 = entry M 1 0 \<le> entry M 0 0 = m\<^sub>0\<^sub>0\<close> (the reduced row-0/row-1 inequality) and
  \<open>u \<le> m\<^sub>1\<^sub>0\<close>.  When \<open>u = m\<^sub>1\<^sub>0\<close> the diagonal is empty and \<open>N = M\<close>; otherwise the
  row-0 spine \<open>u, u+1, \<dots>, m\<^sub>1\<^sub>0-1\<close> then \<open>m\<^sub>0\<^sub>0 \<ge> m\<^sub>1\<^sub>0 > m\<^sub>1\<^sub>0-1 \<ge> u\<close> is strictly
  increasing, so @{thm [source] le0_build} gives \<open>(0,0) \<le>\<^bsub>N\<^esub> (0, Lng N - 1)\<close>.\<close>

lemma elead_monoT_N:
  assumes MT: "M \<in> T_PS" and mono: "monoT M"
    and rle: "entry M 1 0 \<le> entry M 0 0"
    and ule: "u \<le> entry M 1 0"
  shows "monoT ((if u < entry M 1 0 then diagSeq u (entry M 1 0 - 1) else []) @ M)"
proof (cases "u < entry M 1 0")
  case False
  \<comment> \<open>\<open>u = m\<^sub>1\<^sub>0\<close> (article: empty diagonal), so \<open>N = M\<close>.\<close>
  thus ?thesis using mono by simp
next
  case True
  hence truepref: "(if u < entry M 1 0 then diagSeq u (entry M 1 0 - 1) else [])
                    = diagSeq u (entry M 1 0 - 1)" by simp
  have main: "monoT (diagSeq u (entry M 1 0 - 1) @ M)"
  proof -
  let ?m10 = "entry M 1 0"
  let ?m00 = "entry M 0 0"
  let ?v = "?m10 - 1"
  let ?N = "diagSeq u ?v @ M"
  have upos: "u < ?m10" using True by simp
  have m10pos: "0 < ?m10" using upos by simp
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have lenM: "0 < Lng M" using Mne by (cases M) auto
  have plen: "Suc ?v - u = ?m10 - u" using m10pos by simp
  have plenpos: "0 < Suc ?v - u" using upos m10pos by simp
  have lenN: "Lng ?N = (Suc ?v - u) + Lng M" by simp
  have NTPS: "?N \<in> T_PS" using Mne by (simp add: T_PS_def)
  have e00: "entry ?N 0 0 = u"
    using elead_entry_diag_append_lo[where i=0 and u=u and v="?v" and rest=M and p=0] plenpos
    by simp
  have m00gt: "u < ?m00" using upos rle by simp
  have key: "\<And>j. 0 < j \<Longrightarrow> j \<le> Lng ?N - 1 \<Longrightarrow> u < entry ?N 0 j"
  proof -
    fix j assume j0: "0 < j" and jle: "j \<le> Lng ?N - 1"
    show "u < entry ?N 0 j"
    proof (cases "j < Suc ?v - u")
      case True
      have "entry ?N 0 j = u + j" by (rule elead_entry_diag_append_lo[OF True])
      thus ?thesis using j0 by simp
    next
      case False
      hence kj: "Suc ?v - u \<le> j" by simp
      let ?a = "j - (Suc ?v - u)"
      have ja: "j = (Suc ?v - u) + ?a" using kj by simp
      have aL: "?a < Lng M" using jle lenN kj lenM by linarith
      have "entry ?N 0 j = entry M 0 ?a"
        using ja elead_entry_diag_append_hi[OF aL, where u=u and v="?v" and p=0] by simp
      moreover have "?m00 \<le> entry M 0 ?a" using entry0_ge_min[OF MT mono aL] .
      ultimately show ?thesis using m00gt by simp
    qed
  qed
  have j1lt: "Lng ?N - 1 < Lng ?N" using lenN lenM plenpos by linarith
  have j0lt: "(0::nat) < Lng ?N - 1" using lenN lenM plenpos by linarith
  have NPos: "0 < Lng ?N" using lenN lenM plenpos by linarith
  have rt: "(nextrel0 ?N)\<^sup>*\<^sup>* 0 (Lng ?N - 1)"
  proof (rule le0_build[OF NTPS j1lt j0lt])
    show "\<forall>j. 0 < j \<and> j \<le> Lng ?N - 1 \<longrightarrow> entry ?N 0 0 < entry ?N 0 j"
      using key e00 by simp
  qed
  have "le0 ?N 0 (Lng ?N - 1)" unfolding le0_def using NPos j1lt rt by blast
  hence leRN: "leR ?N 0 0 (Lng ?N - 1)" by (simp add: leR_def)
  have Lge2: "2 \<le> Lng ?N" using lenN lenM plenpos by linarith
  have "\<not> zeroT ?N" using Lge2 by (simp add: zeroT_def)
  with leRN show "monoT ?N" by (simp add: monoT_def)
  qed
  show ?thesis unfolding truepref by (rule main)
qed


subsection \<open>§6.5 命題（\<open>Red\<close>と基本列の可換性） — \<open>m_6_5_Red_oper\<close>\<close>

text \<open>roper: the base case \<open>j\<^sub>1 = Lng M - 1 = 0\<close> (i.e. \<open>Lng M = 1\<close>).  Then the
  fundamental sequence is the identity (\<open>M[n] = M\<close>), and \<open>Lng (Red M) = Lng M = 1\<close>
  (@{thm [source] m_6_5_Lng_Red}) so \<open>(Red M)[n] = Red M\<close> too.  Both sides equal
  \<open>Red M\<close>.\<close>

lemma roper_oper_Lng1:
  assumes L1: "Lng M = 1"
  shows "M[n] = M"
  using L1 by (simp add: oper_def Let_def)

end
