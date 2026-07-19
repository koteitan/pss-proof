theory Frontier_6_046
  imports Support_6_027
begin

(* ===== Red_Pred helper block from workflow predh-T3 ===== *)
text \<open>m: §6.4-under-\<open>Pred\<close> commutation, claim (i): the diagonal trunk prefix is
  preserved by \<open>Pred\<close>.  When \<open>Lng M > 1\<close> we have \<open>Pred M = butlast M\<close>, which only
  drops the last column \<open>M\<^bsub>Lng M-1\<^esub>\<close>.  Because \<open>TrMax M \<noteq> Lng M - 1\<close> (nontrivial
  branch present), the trunk lives strictly to the left of that column
  (\<open>TrMax M < Lng M - 1\<close>), so \<open>Pred M\<close> and \<open>M\<close> agree on the whole prefix
  \<open>[0, TrMax M]\<close>.  The below-trunk row-1 chain transfers (@{thm [source]
  nextrel1_prefix_imp}) and the boundary step still fails (lifting a hypothetical
  \<open>Pred M\<close>-step to \<open>M\<close> contradicts @{thm [source] TrMax_stop}); @{thm [source]
  TrMax_eq_of_prefix_agree} then pins the trunk.  Empirically 253/0 (and 177609/0
  over random \<open>T\<^sub>P\<^sub>S\<close> samples). This is a branch-piece of the future
  \<open>m_6_5_Red_Pred\<close> (Red(Pred M)=Pred(Red M)).\<close>

lemma TrMax_Pred:
  assumes M: "M \<in> T_PS" and L: "1 < Lng M" and br: "TrMax M \<noteq> Lng M - 1"
  shows "TrMax (Pred M) = TrMax M"
proof -
  have predT: "Pred M \<in> T_PS" by (rule Pred_preserves_T_PS[OF M])
  have predbl: "Pred M = butlast M" using L by (simp add: Pred_def)
  have LP: "Lng (Pred M) = Lng M - 1" using L by (simp add: predbl)
  \<comment> \<open>trunk strictly left of the dropped column\<close>
  have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF M])
  with br have tlt: "TrMax M < Lng M - 1" by linarith
  \<comment> \<open>\<open>Pred M\<close> and \<open>M\<close> agree on the prefix \<open>[0, TrMax M]\<close>\<close>
  have agree: "\<And>j. j \<le> TrMax M \<Longrightarrow> Pred M ! j = M ! j"
  proof -
    fix j assume "j \<le> TrMax M"
    hence jlt: "j < Lng (Pred M)" using tlt LP by linarith
    thus "Pred M ! j = M ! j" by (simp add: predbl nth_butlast)
  qed
  have cM: "TrMax M < Lng (Pred M)" using tlt LP by simp
  have cN: "TrMax M < Lng M" using tlt by linarith
  \<comment> \<open>boundary stop in \<open>Pred M\<close>: a step there would lift to \<open>M\<close>, contradicting \<open>TrMax_stop\<close>\<close>
  have stopM: "\<not> nextR M 1 (TrMax M) (TrMax M + 1)" by (rule TrMax_stop[OF M tlt])
  have stop: "\<not> nextR (Pred M) 1 (TrMax M) (TrMax M + 1)"
  proof
    assume "nextR (Pred M) 1 (TrMax M) (TrMax M + 1)"
    hence stepP: "nextrel1 (Pred M) (TrMax M) (TrMax M + 1)" by (simp add: nextR_def)
    \<comment> \<open>the endpoint \<open>TrMax M + 1\<close> is in range of \<open>Pred M\<close>, hence \<open>\<le> TrMax M + 1\<close>-prefix\<close>
    have y_in: "TrMax M + 1 < Lng (Pred M)" using stepP by (simp add: nextrel1_def)
    have x_le: "TrMax M \<le> TrMax M + 1" by simp
    have y_le: "TrMax M + 1 \<le> TrMax M + 1" by simp
    have cP: "TrMax M + 1 < Lng (Pred M)" using y_in .
    have cMM: "TrMax M + 1 < Lng M" using y_in LP by linarith
    \<comment> \<open>agreement extends to the prefix \<open>[0, TrMax M + 1]\<close> (still left of the dropped column)\<close>
    have agree1: "\<And>j. j \<le> TrMax M + 1 \<Longrightarrow> Pred M ! j = M ! j"
    proof -
      fix j assume "j \<le> TrMax M + 1"
      hence jlt: "j < Lng (Pred M)" using y_in by linarith
      thus "Pred M ! j = M ! j" by (simp add: predbl nth_butlast)
    qed
    have "nextrel1 M (TrMax M) (TrMax M + 1)"
      by (rule nextrel1_prefix_imp[OF agree1 cP cMM x_le y_le stepP])
    hence "nextR M 1 (TrMax M) (TrMax M + 1)" by (simp add: nextR_def)
    with stopM show False by simp
  qed
  show ?thesis
    by (rule TrMax_eq_of_prefix_agree[OF predT M agree cM cN order.refl stop])
qed



(* ===== Red_Pred helper block from workflow predh-T4 ===== *)
subsection \<open>§6.5 T4: structural pieces of \<open>Red(Pred M)=Pred(Red M)\<close> on the
  \<open>m\<^sub>1\<^sub>0>0\<close> branch (the core-reduce argument commutes with \<open>Pred\<close> up to the OUTER
  \<open>Red\<close>)\<close>

text \<open>\<open>IncrFirst\<close> commutes with \<open>butlast\<close> (it is a per-pair \<open>map\<close>).\<close>

lemma IncrFirst_butlast: "IncrFirst (butlast M) = butlast (IncrFirst M)"
  by (simp add: IncrFirst_def map_butlast)

lemma funpow_IncrFirst_butlast:
  "(IncrFirst ^^ k) (butlast M) = butlast ((IncrFirst ^^ k) M)"
  by (induction k) (simp_all add: IncrFirst_butlast)

text \<open>The first pair (index 0) is untouched by \<open>Pred\<close> when \<open>Lng M > 1\<close>, hence the
  diagonal prefix \<open>diagSeq 0 (m\<^sub>1\<^sub>0-1)\<close> and the \<open>IncrFirst\<close> exponent \<open>m\<^sub>1\<^sub>0\<close> are the
  same for \<open>M\<close> and \<open>Pred M\<close>.\<close>

lemma entry_Pred_0:
  assumes "1 < Lng M"
  shows "entry (Pred M) i 0 = entry M i 0"
proof -
  have ne: "M \<noteq> []" using assms by (cases M) auto
  have "Pred M = butlast M" using assms by (simp add: Pred_def)
  moreover have "butlast M ! 0 = M ! 0"
    using assms by (simp add: nth_butlast)
  ultimately show ?thesis by (simp add: entry_def)
qed

end
