theory Frontier_6_006
  imports P_6_2_P_IncrFirst
begin

text \<open>§6.8 (b): \<open>P\<close> commutes with an iterated \<open>IncrFirst\<close> as a per-component map.
  Funpow-iterate of @{thm [source] m_6_2_P_IncrFirst} (\<open>P (IncrFirst M) = map IncrFirst (P M)\<close>);
  the step uses that one-step fact + \<open>map\<close>-compose.  Empirically 1155/1155
  (python/notbrle_low_check.py, rank-stratified std).\<close>

lemma P_funpow_IncrFirst:
  shows "P ((IncrFirst ^^ s) X) = map (IncrFirst ^^ s) (P X)"
proof (induction s)
  case 0
  show ?case by simp
next
  case (Suc s)
  have "P ((IncrFirst ^^ Suc s) X) = P (IncrFirst ((IncrFirst ^^ s) X))"
    by (simp add: funpow_swap1)
  also have "\<dots> = map IncrFirst (P ((IncrFirst ^^ s) X))"
    by (rule m_6_2_P_IncrFirst)
  also have "\<dots> = map IncrFirst (map (IncrFirst ^^ s) (P X))"
    using Suc.IH by simp
  also have "\<dots> = map (\<lambda>c. IncrFirst ((IncrFirst ^^ s) c)) (P X)"
    by simp
  also have "\<dots> = map (IncrFirst ^^ Suc s) (P X)"
    by (simp add: funpow_swap1)
  finally show ?case .
qed

text \<open>Slice / drop / take relations on \<open>seg\<close> (reusable for §6.x).\<close>

lemma drop_eq_map_nth: "drop a M = map (nth M) [a..<Lng M]"
  by (rule nth_equalityI) (auto simp: nth_drop)

lemma seg_0_eq_take:
  assumes "Suc b \<le> Lng M"
  shows "seg M 0 b = take (Suc b) M"
  unfolding seg_def using assms
  by (intro nth_equalityI) (auto simp: nth_take simp del: upt_Suc)

lemma seg_to_last_eq_drop:
  assumes "Lng M > 0"
  shows "seg M a (Lng M - 1) = drop a M"
proof -
  have "seg M a (Lng M - 1) = map (\<lambda>j. M ! j) [a..<Lng M]"
    using assms by (simp add: seg_def del: upt_Suc)
  also have "\<dots> = drop a M" by (rule drop_eq_map_nth[symmetric])
  finally show ?thesis .
qed


lemma P_add_drop_eq_map_nth:
  "drop a M = map (nth M) [a..<Lng M]"
  by (rule nth_equalityI) (auto simp: nth_drop)

lemma P_add_seg_0_eq_take:
  assumes "Suc b \<le> Lng M"
  shows "seg M 0 b = take (Suc b) M"
  unfolding seg_def using assms
  by (intro nth_equalityI) (auto simp: nth_take simp del: upt_Suc)

lemma P_add_seg_to_last_eq_drop:
  assumes "Lng M > 0"
  shows "seg M a (Lng M - 1) = drop a M"
proof -
  have "seg M a (Lng M - 1) = map (\<lambda>j. M ! j) [a..<Lng M]"
    using assms by (simp add: seg_def del: upt_Suc)
  also have "\<dots> = drop a M" by (rule P_add_drop_eq_map_nth[symmetric])
  finally show ?thesis .
qed

text \<open>
  When \<open>Lng M > 1\<close> the cut \<open>Pcut M\<close> satisfies its own defining predicate:
  \<open>0 < Pcut M \<le> Lng M - 1\<close> and \<open>(0, Pcut M) \<le>\<^sub>M (0, Lng M - 1)\<close>.
\<close>

lemma P_add_Pcut_props:
  assumes "Lng M > 1"
  shows "0 < Pcut M \<and> Pcut M \<le> Lng M - 1 \<and> leR M 0 (Pcut M) (Lng M - 1)"
proof -
  have wit: "0 < Lng M - 1 \<and> Lng M - 1 \<le> Lng M - 1 \<and> leR M 0 (Lng M - 1) (Lng M - 1)"
    using assms by (auto simp: leR_def le0_def)
  show ?thesis unfolding Pcut_def
    by (rule LeastI[where P = "\<lambda>j. 0 < j \<and> j \<le> Lng M - 1 \<and> leR M 0 j (Lng M - 1)", OF wit])
qed

text \<open>
  Left-minimality of the cut \<open>Pcut M\<close> (article §6.2 加法性の証明, line "\<open>j'\<^sub>0\<close>の
  定義と親の存在の判定条件より \<open>\<dots> M\<^bsub>0,j\<^esub> \<ge> M\<^bsub>0,j'\<^sub>0\<^esub>\<close>"):  for a multi-term \<open>M\<close>,
  every index strictly to the left of the cut has a row-0 entry no smaller
  than the cut's.
\<close>

lemma P_add_Pcut_left_min:
  assumes M: "M \<in> T_PS" and multi: "multiT M" and L: "Lng M > 1"
  shows "\<And>j. j < Pcut M \<Longrightarrow> entry M 0 j \<ge> entry M 0 (Pcut M)"
proof -
  let ?c = "Pcut M"
  let ?j1 = "Lng M - 1"
  from P_add_Pcut_props[OF L] have c0: "0 < ?c" and cj1: "?c \<le> ?j1"
    and lec: "leR M 0 ?c ?j1" by auto
  have cL: "?c < Lng M" using cj1 L by simp
  fix j assume jc: "j < ?c"
  show "entry M 0 j \<ge> entry M 0 ?c"
  proof (rule ccontr)
    assume "\<not> entry M 0 j \<ge> entry M 0 ?c"
    hence lt: "entry M 0 j < entry M 0 ?c" by simp
    obtain p where p: "j \<le> p" "p < ?c" "nextR M 0 p ?c"
      using m_5_1_parent_exists_1[OF M jc cL lt] by auto
    have np: "nextrel0 M p ?c" using p(3) by (simp add: nextR_def)
    hence "(nextrel0 M)\<^sup>*\<^sup>* p ?c" by blast
    moreover have "(nextrel0 M)\<^sup>*\<^sup>* ?c ?j1" using lec by (simp add: leR_def le0_def)
    ultimately have rp: "(nextrel0 M)\<^sup>*\<^sup>* p ?j1" by (rule rtranclp_trans)
    have pL: "p < Lng M" using p(2) cL by simp
    have lepj1: "leR M 0 p ?j1" using rp pL L by (simp add: leR_def le0_def)
    show False
    proof (cases "p = 0")
      case True
      hence "leR M 0 0 ?j1" using lepj1 by simp
      hence "\<not> multiT M" using m_6_2_not_multi_iff_le[OF M] by simp
      thus False using multi by simp
    next
      case False
      hence p0: "0 < p" by simp
      have pj1: "p \<le> ?j1" using p(2) cj1 by simp
      have "?c \<le> p" unfolding Pcut_def
        by (rule Least_le[where P = "\<lambda>j. 0 < j \<and> j \<le> ?j1 \<and> leR M 0 j ?j1"])
           (use p0 pj1 lepj1 in auto)
      thus False using p(2) by simp
    qed
  qed
qed

text \<open>
  The suffix starting at a row-0 ancestor \<open>c\<close> of the last index is non-multi,
  hence \<open>P\<close> of it is a singleton.
\<close>

lemma P_add_drop_ancestor:
  assumes M: "M \<in> T_PS" and c: "0 < c" "c \<le> Lng M - 1"
    and lec: "leR M 0 c (Lng M - 1)"
  shows "P (drop c M) = [drop c M]"
proof (cases "c = Lng M - 1")
  case True
  have L0: "Lng M > 0" using c by linarith
  have L1: "Lng (drop c M) = 1"
    using True L0 unfolding length_drop by linarith
  have "\<not> multiT (drop c M)"
  proof (cases "zeroT (drop c M)")
    case True thus ?thesis by (simp add: multiT_def)
  next
    case False
    have "monoT (drop c M)" using L1 False by (simp add: monoT_def leR_def le0_def)
    thus ?thesis by (simp add: multiT_def)
  qed
  thus ?thesis by (subst P.simps) simp
next
  case False
  with c have ltc: "c < Lng M - 1" by simp
  have L0: "Lng M > 0" using c by linarith
  have "monoT (seg M c (Lng M - 1))"
    by (rule m_6_2_mono_ancestor_slice[OF M ltc lec])
  hence "monoT (drop c M)" using P_add_seg_to_last_eq_drop[OF L0] by simp
  hence "\<not> multiT (drop c M)" by (simp add: multiT_def)
  thus ?thesis by (subst P.simps) simp
qed

end
