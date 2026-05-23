theory pss_mechanized
  imports pss_paper
begin

text \<open>
  Mechanized (machine-checked) proofs of the article's statements.

  Each fact re-states a statement from @{file "pss_paper.thy"} (where it is
  recorded as @{command sorry}) and discharges it with a real proof.  This is
  the "own work" file; the goal is to contain no @{command sorry}.  Facts not
  yet mechanized are marked with a \<open>TODO\<close> comment and a temporary
  @{command sorry}.

  Naming mirrors @{file "pss_paper.thy"} with prefix \<open>m_\<close> instead of \<open>p_\<close>.
\<close>

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


section \<open>§5.1 親子関係\<close>

text \<open>\<open>\<le>\<^sub>M\<close>-reachability is index-monotone: \<open>(nextrel0 M)\<^sup>*\<^sup>* a b\<close> implies \<open>a \<le> b\<close>.\<close>

lemma nextrel0_rtrancl_mono:
  assumes "(nextrel0 M)\<^sup>*\<^sup>* a b"
  shows "a \<le> b"
  using assms by (induction rule: rtranclp_induct) (auto simp: nextrel0_def)

text \<open>m: 命題（親の存在の判定条件） (1) — discharges @{thm [source] p_5_1_parent_exists_1}.\<close>

lemma m_5_1_parent_exists_1:
  assumes "M \<in> T_PS" "j0 < j1" "j1 < Lng M" "entry M 0 j0 < entry M 0 j1"
  shows "\<exists>j. j0 \<le> j \<and> j < j1 \<and> nextR M 0 j j1"
proof -
  let ?S = "{j. j < j1 \<and> entry M 0 j < entry M 0 j1}"
  have fin: "finite ?S" by (auto intro: finite_subset[of ?S "{..<j1}"])
  have j0S: "j0 \<in> ?S" using assms(2,4) by auto
  hence ne: "?S \<noteq> {}" by blast
  have inS: "Max ?S \<in> ?S" using fin ne by (rule Max_in)
  hence jm1: "Max ?S < j1" and jmv: "entry M 0 (Max ?S) < entry M 0 j1" by auto
  have jge: "j0 \<le> Max ?S" using fin j0S by (rule Max_ge)
  have mid: "\<forall>j'. Max ?S < j' \<and> j' < j1 \<longrightarrow> entry M 0 j' \<ge> entry M 0 j1"
  proof (intro allI impI)
    fix j' assume a: "Max ?S < j' \<and> j' < j1"
    have "j' \<notin> ?S"
    proof
      assume "j' \<in> ?S"
      hence "j' \<le> Max ?S" by (rule Max_ge[OF fin])
      with a show False by simp
    qed
    with a show "entry M 0 j' \<ge> entry M 0 j1" by auto
  qed
  have "nextR M 0 (Max ?S) j1"
    using jm1 jmv mid assms(3) by (auto simp: nextR_def nextrel0_def)
  thus ?thesis using jge jm1 by blast
qed

text \<open>m: 命題（親の基本性質） (1) — discharges @{thm [source] p_5_1_parent_basic_1}.\<close>

lemma m_5_1_parent_basic_1:
  assumes "M \<in> T_PS" "j0 < j" "j \<le> j1" "nextR M 0 j0 j1"
  shows "entry M 0 j \<ge> entry M 0 j1"
proof (cases "j = j1")
  case True thus ?thesis by simp
next
  case False
  with assms have "j0 < j" "j < j1" by auto
  thus ?thesis using assms(4) by (auto simp: nextR_def nextrel0_def)
qed

text \<open>m: 命題（親の基本性質） (2) — discharges @{thm [source] p_5_1_parent_basic_2}.\<close>

lemma m_5_1_parent_basic_2:
  assumes "M \<in> T_PS" "j0 < j" "j \<le> j1" "nextR M 1 j0 j1" "leR M 0 j j1"
  shows "entry M 1 j \<ge> entry M 1 j1"
proof -
  from assms(4) have "nextrel1 M j0 j1" by (simp add: nextR_def)
  hence "\<forall>j'. j0 < j' \<and> le0 M j' j1 \<longrightarrow> entry M 1 j' \<ge> entry M 1 j1"
    by (simp add: nextrel1_def)
  moreover from assms(5) have "le0 M j j1" by (simp add: leR_def)
  ultimately show ?thesis using assms(2) by blast
qed

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

text \<open>m: 系（直系先祖の基本性質） (1) — discharges @{thm [source] p_5_1_ancestor_basic_1}.\<close>

lemma m_5_1_ancestor_basic_1:
  assumes "M \<in> T_PS" "j0 < j" "j \<le> j1" "leR M 0 j0 j1"
  shows "entry M 0 j0 < entry M 0 j"
proof -
  from assms(4) have "(nextrel0 M)\<^sup>*\<^sup>* j0 j1" by (simp add: leR_def le0_def)
  thus ?thesis using le0_ances_aux assms(2,3) by blast
qed


section \<open>§5.3 基本列\<close>

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

text \<open>m: 命題（\<open>Pred\<close>が\<open>[1]\<close>で表されること） — discharges @{thm [source] p_5_3_pred_is_oper1}.\<close>

lemma m_5_3_pred_is_oper1:
  assumes "M \<in> T_PS" "Lng M > 1"
  shows "Pred M = M[1]"
proof -
  have pred: "Pred M = take (Lng M - 1) M"
    using assms(2) by (simp add: Pred_def butlast_conv_take)
  show ?thesis
  proof (cases "entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0")
    case True
    thus ?thesis unfolding oper1_eq[OF assms(2)] by simp
  next
    case notzero: False
    show ?thesis
    proof (cases "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)")
      case False
      thus ?thesis unfolding oper1_eq[OF assms(2)] using notzero by simp
    next
      case hasp: True
      let ?j0 = "parent M (idx1 M (Lng M - 1)) (Lng M - 1)"
      from hasp have par: "nextR M (idx1 M (Lng M - 1)) ?j0 (Lng M - 1)"
        unfolding hasParent_def parent_def by (rule theI')
      hence j0lt: "?j0 < Lng M - 1"
        unfolding nextR_def nextrel0_def nextrel1_def by (auto split: if_splits)
      from hasp have nn: "\<not> \<not> hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)" by simp
      have "M[1] = take ?j0 M @ map (\<lambda>j. (entry M 0 j, entry M 1 j)) [?j0..<Lng M - 1]"
        unfolding oper1_eq[OF assms(2)] if_not_P[OF notzero] if_not_P[OF nn]
        by (rule refl)
      also have "map (\<lambda>j. (entry M 0 j, entry M 1 j)) [?j0..<Lng M - 1]
                 = map (nth M) [?j0..<Lng M - 1]"
        by (simp add: entry_def)
      also have "take ?j0 M @ map (nth M) [?j0..<Lng M - 1] = take (Lng M - 1) M"
        using j0lt by (intro take_append_map_nth) auto
      finally show ?thesis using pred by simp
    qed
  qed
qed


section \<open>Faithfulness lemmas (忠実性補題)\<close>

text \<open>
  This section justifies the modelling choices in @{file "pss_defs.thy"} by
  proving that they coincide with the article's literal definitions.
\<close>

subsection \<open>§5.1 \<open>\<le>\<^sub>M\<close> as the article's chain\<close>

text \<open>
  The article defines \<open>(i,j\<^sub>0) \<le>\<^sub>M (i,j\<^sub>1)\<close> via the existence of an array
  \<open>a\<close> with \<open>a \<noteq> ()\<close>, \<open>a\<^sub>0 = j\<^sub>0\<close>, \<open>a\<^bsub>Lng a-1\<^esub> = j\<^sub>1\<close> and
  \<open>(i,a\<^sub>k) <\<^bsub>M\<^esub>\<^sup>Next (i,a\<^bsub>k+1\<^esub>)\<close> for all \<open>k < Lng a - 1\<close>.  We use the
  reflexive-transitive closure instead; the two coincide.
\<close>

lemma chain_imp_rtranclp:
  assumes "a \<noteq> []" "\<forall>k<length a - 1. R (a!k) (a!(k+1))"
  shows "R\<^sup>*\<^sup>* (hd a) (last a)"
  using assms
proof (induction a)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "xs = []")
    case True thus ?thesis by simp
  next
    case False
    have head: "R x (hd xs)"
    proof -
      have "0 < length (x # xs) - 1" using False by (cases xs) auto
      hence "R ((x # xs) ! 0) ((x # xs) ! (0 + 1))" using Cons.prems(2) by blast
      thus ?thesis by (simp add: hd_conv_nth False)
    qed
    have tail: "\<forall>k<length xs - 1. R (xs!k) (xs!(k+1))"
    proof (intro allI impI)
      fix k assume "k < length xs - 1"
      hence "k + 1 < length (x # xs) - 1" by simp
      hence "R ((x # xs) ! (k+1)) ((x # xs) ! (k+1+1))" using Cons.prems(2) by blast
      thus "R (xs!k) (xs!(k+1))" by simp
    qed
    have "R\<^sup>*\<^sup>* (hd xs) (last xs)" using Cons.IH False tail by blast
    with head have "R\<^sup>*\<^sup>* x (last xs)" by (rule converse_rtranclp_into_rtranclp)
    thus ?thesis using False by simp
  qed
qed

lemma rtranclp_imp_chain:
  assumes "R\<^sup>*\<^sup>* x y"
  shows "\<exists>a. a \<noteq> [] \<and> hd a = x \<and> last a = y \<and> (\<forall>k<length a - 1. R (a!k) (a!(k+1)))"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  show ?case by (intro exI[of _ "[x]"]) simp
next
  case (step y z)
  then obtain a where a: "a \<noteq> []" "hd a = x" "last a = y"
      "\<forall>k<length a - 1. R (a!k) (a!(k+1))" by blast
  have "hd (a @ [z]) = x" using a by (simp add: hd_append)
  moreover have "last (a @ [z]) = z" by simp
  moreover have "\<forall>k<length (a @ [z]) - 1. R ((a @ [z])!k) ((a @ [z])!(k+1))"
  proof (intro allI impI)
    fix k assume k: "k < length (a @ [z]) - 1"
    show "R ((a @ [z])!k) ((a @ [z])!(k+1))"
    proof (cases "k < length a - 1")
      case True
      hence k1: "k < length a" and k2: "Suc k < length a" using a(1) by auto
      show ?thesis using a(4) True k1 k2 by (simp add: nth_append)
    next
      case False
      with k a(1) have keq: "k = length a - 1" by simp
      hence "(a @ [z]) ! k = last a"
        using a(1) by (simp add: nth_append last_conv_nth)
      moreover have "(a @ [z]) ! (k+1) = z"
        using keq a(1) by (simp add: nth_append)
      ultimately show ?thesis using a(3) step.hyps(2) by simp
    qed
  qed
  ultimately show ?case using a(1) by blast
qed

lemma rtranclp_iff_chain:
  "R\<^sup>*\<^sup>* x y \<longleftrightarrow>
   (\<exists>a. a \<noteq> [] \<and> hd a = x \<and> last a = y \<and> (\<forall>k<length a - 1. R (a!k) (a!(k+1))))"
  using rtranclp_imp_chain chain_imp_rtranclp by metis

text \<open>
  m: \<open>leR\<close> coincides with the article's literal chain definition of \<open>\<le>\<^sub>M\<close>
  (endpoints in \<open>Idx\<close>, same row \<open>i\<close>, and a \<open><\<^sup>Next\<close>-chain from \<open>j\<^sub>0\<close> to \<open>j\<^sub>1\<close>).
\<close>

lemma leR_eq_chain:
  assumes "i = 0 \<or> i = 1"
  shows "leR M i j0 j1 \<longleftrightarrow>
         j0 < Lng M \<and> j1 < Lng M \<and>
         (\<exists>a. a \<noteq> [] \<and> hd a = j0 \<and> last a = j1 \<and>
              (\<forall>k<length a - 1. nextR M i (a!k) (a!(k+1))))"
  using assms
proof (elim disjE)
  assume "i = 0"
  thus ?thesis by (simp add: leR_def le0_def nextR_def rtranclp_iff_chain)
next
  assume "i = 1"
  thus ?thesis by (simp add: leR_def le1_def nextR_def rtranclp_iff_chain)
qed


subsection \<open>§5.4 the uniform expansion step\<close>

text \<open>
  The article's system \<open>F\<close> sends \<open>M\<close> to \<open>Pred M\<close> in the two degenerate
  sub-cases (\<open>M\<^bsub>j\<^sub>1\<^esub> = (0,0)\<close>, or no unique parent) and to \<open>M[n]\<close> otherwise.
  Since \<open>M[n] = Pred M\<close> in exactly those degenerate sub-cases, the uniform
  step "\<open>M \<mapsto> M[n]\<close>" used by @{const Fval} / @{const Fdom} is faithful.
\<close>

lemma oper_degenerate_eq_Pred:
  assumes L: "Lng M > 1"
    and D: "entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0
            \<or> \<not> hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
  shows "M[n] = Pred M"
proof -
  have nz: "Lng M - 1 \<noteq> 0" using L by simp
  from D show ?thesis
  proof
    assume "entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0"
    thus ?thesis using nz by (simp add: oper_def Let_def)
  next
    assume "\<not> hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    thus ?thesis using nz by (auto simp: oper_def Let_def)
  qed
qed

end
