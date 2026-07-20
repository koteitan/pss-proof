theory Pre_5
  imports pss_defs
begin

section \<open>Helper facts about the basic definitions\<close>

lemma Pred_preserves_T_PS:
  assumes "M \<in> T_PS"
  shows "Pred M \<in> T_PS"
proof (cases "Lng M \<le> 1")
  case True
  thus ?thesis using assms by (simp add: Pred_def)
next
  case False
  hence "butlast M \<noteq> []" by (simp add: length_greater_0_conv [symmetric])
  thus ?thesis using False by (simp add: T_PS_def Pred_def)
qed

lemma Lng_Pred_lt:
  assumes "Lng M > 1"
  shows "Lng (Pred M) < Lng M"
  using assms by (simp add: Pred_def)

text \<open>Reflexivity of \<open>\<le>\<^sub>M\<close> within \<open>Idx\<close> (used implicitly throughout §5.1).\<close>

lemma le0_refl:
  assumes "j < Lng M"
  shows "le0 M j j"
  using assms by (simp add: le0_def)

lemma leR_refl:
  assumes "i \<in> {0,1}" "j < Lng M"
  shows "leR M i j j"
  using assms by (auto simp: leR_def le0_def le1_def)

text \<open>\<open>\<le>\<^sub>M\<close>-reachability is index-monotone: \<open>(nextrel0 M)\<^sup>*\<^sup>* a b\<close> implies \<open>a \<le> b\<close>.\<close>

lemma nextrel0_rtrancl_mono:
  assumes "(nextrel0 M)\<^sup>*\<^sup>* a b"
  shows "a \<le> b"
  using assms by (induction rule: rtranclp_induct) (auto simp: nextrel0_def)

text \<open>
  Auxiliary for §5.1 系（直系先祖の基本性質） (1), by induction on the
  \<open><\<^sup>Next\<close>-chain (the article's "J に関する数学的帰納法").
\<close>

lemma le0_ances_aux:
  assumes "(nextrel0 M)\<^sup>*\<^sup>* j0 j1"
  shows "\<forall>j. j0 < j \<and> j \<le> j1 \<longrightarrow> entry M 0 j0 < entry M 0 j"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  show ?case by auto
next
  case (step y z)
  have ley: "entry M 0 j0 \<le> entry M 0 y"
  proof (cases "j0 < y")
    case True
    thus ?thesis using step.IH by force
  next
    case False
    have "j0 \<le> y" using step.hyps(1) nextrel0_rtrancl_mono by blast
    with False have "j0 = y" by simp
    thus ?thesis by simp
  qed
  from step.hyps(2) have nx_val: "entry M 0 y < entry M 0 z"
    and nx_mid: "\<forall>j'. y < j' \<and> j' < z \<longrightarrow> entry M 0 j' \<ge> entry M 0 z"
    by (auto simp: nextrel0_def)
  show ?case
  proof (intro allI impI)
    fix j assume j: "j0 < j \<and> j \<le> z"
    show "entry M 0 j0 < entry M 0 j"
    proof (cases "j \<le> y")
      case True
      thus ?thesis using step.IH j by simp
    next
      case False
      hence "y < j" by simp
      show ?thesis
      proof (cases "j = z")
        case True
        thus ?thesis using ley nx_val by simp
      next
        case False
        with \<open>y < j\<close> j have "y < j \<and> j < z" by simp
        hence "entry M 0 j \<ge> entry M 0 z" using nx_mid by blast
        thus ?thesis using ley nx_val by simp
      qed
    qed
  qed
qed
text \<open>Row-1 reachability is index-monotone.\<close>

lemma nextrel1_rtrancl_mono:
  assumes "(nextrel1 M)\<^sup>*\<^sup>* a b"
  shows "a \<le> b"
  using assms by (induction rule: rtranclp_induct) (auto simp: nextrel1_def)
text \<open>Transitivity of \<open>\<le>\<^sub>M\<close> on row 0, and "row-1 ancestry implies row-0 ancestry".\<close>

lemma le0_trans:
  assumes "le0 M a b" "le0 M b c"
  shows "le0 M a c"
  using assms by (auto simp: le0_def intro: rtranclp_trans)

lemma nextrel1_imp_nextrel0_rtrancl:
  assumes "(nextrel1 M)\<^sup>*\<^sup>* a b"
  shows "(nextrel0 M)\<^sup>*\<^sup>* a b"
  using assms
proof (induction rule: rtranclp_induct)
  case base show ?case by simp
next
  case (step y z)
  have "le0 M y z" using step.hyps(2) by (simp add: nextrel1_def)
  hence "(nextrel0 M)\<^sup>*\<^sup>* y z" by (simp add: le0_def)
  with step.IH show ?case by (rule rtranclp_trans)
qed

lemma m_le1_imp_le0:
  assumes "leR M 1 a b"
  shows "leR M 0 a b"
  using assms nextrel1_imp_nextrel0_rtrancl by (auto simp: leR_def le0_def le1_def)
text \<open>A prefix followed by an index-range map recovers a longer prefix.\<close>

lemma take_append_map_nth:
  assumes "i \<le> j" "j \<le> length xs"
  shows "take i xs @ map (nth xs) [i..<j] = take j xs"
proof -
  have "take (j - i) (drop i xs) = map (nth xs) [i..<j]"
    using assms by (intro nth_equalityI) (auto simp: nth_upt nth_take nth_drop)
  moreover have "take j xs = take i xs @ take (j - i) (drop i xs)"
    using assms by (metis le_add_diff_inverse take_add)
  ultimately show ?thesis by simp
qed

text \<open>The pair at index \<open>j\<close> is recovered from its two components.\<close>

lemma entry_pair: "(entry M 0 j, entry M 1 j) = M ! j"
  by (simp add: entry_def)

text \<open>
  Structure of a single fundamental-sequence step with \<open>n = 1\<close>: the iterated
  block reduces to one copy with no increments (since \<open>k = 0\<close>).
\<close>

lemma oper1_eq:
  assumes "Lng M > 1"
  shows "M[1] =
     (if entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0 then Pred M
      else if \<not> hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) then Pred M
      else take (parent M (idx1 M (Lng M - 1)) (Lng M - 1)) M @
           map (\<lambda>j. (entry M 0 j, entry M 1 j))
               [parent M (idx1 M (Lng M - 1)) (Lng M - 1)..<Lng M - 1])"
  using assms by (simp add: oper_def Let_def)

end
