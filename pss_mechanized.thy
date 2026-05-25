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

text \<open>m: 命題（親の存在の判定条件） (2) — discharges @{thm [source] p_5_1_parent_exists_2}.\<close>

lemma m_5_1_parent_exists_2:
  assumes "M \<in> T_PS" "j0 < j1" "j1 < Lng M" "entry M 1 j0 < entry M 1 j1" "leR M 0 j0 j1"
  shows "\<exists>j. j0 \<le> j \<and> j < j1 \<and> nextR M 1 j j1"
proof -
  let ?S = "{j. j < j1 \<and> entry M 1 j < entry M 1 j1 \<and> le0 M j j1}"
  have fin: "finite ?S" by (auto intro: finite_subset[of ?S "{..<j1}"])
  have j0S: "j0 \<in> ?S" using assms(2,4,5) by (auto simp: leR_def)
  hence ne: "?S \<noteq> {}" by blast
  have inS: "Max ?S \<in> ?S" using fin ne by (rule Max_in)
  hence jm1: "Max ?S < j1" and jmv: "entry M 1 (Max ?S) < entry M 1 j1"
    and jmle: "le0 M (Max ?S) j1" by auto
  have jge: "j0 \<le> Max ?S" using fin j0S by (rule Max_ge)
  have univ: "\<forall>j'. Max ?S < j' \<and> le0 M j' j1 \<longrightarrow> entry M 1 j' \<ge> entry M 1 j1"
  proof (intro allI impI)
    fix j' assume a: "Max ?S < j' \<and> le0 M j' j1"
    show "entry M 1 j' \<ge> entry M 1 j1"
    proof (rule ccontr)
      assume "\<not> entry M 1 j' \<ge> entry M 1 j1"
      hence lt: "entry M 1 j' < entry M 1 j1" by simp
      from a have "(nextrel0 M)\<^sup>*\<^sup>* j' j1" by (simp add: le0_def)
      hence "j' \<le> j1" by (rule nextrel0_rtrancl_mono)
      moreover have "j' \<noteq> j1" using lt by auto
      ultimately have "j' < j1" by simp
      hence "j' \<in> ?S" using lt a by simp
      hence "j' \<le> Max ?S" by (rule Max_ge[OF fin])
      with a show False by simp
    qed
  qed
  have "nextR M 1 (Max ?S) j1"
    using jm1 jmv jmle univ assms(3) by (auto simp: nextR_def nextrel1_def)
  thus ?thesis using jge jm1 by blast
qed

text \<open>
  Auxiliary for §5.1 命題（親の存在の判定条件） (3): build a nextR-chain
  by strong induction on the endpoint (the article's "j1 に関する帰納法").
\<close>

lemma le0_build:
  assumes "M \<in> T_PS" "j1 < Lng M" "j0 < j1"
    and "\<forall>j. j0 < j \<and> j \<le> j1 \<longrightarrow> entry M 0 j0 < entry M 0 j"
  shows "(nextrel0 M)\<^sup>*\<^sup>* j0 j1"
  using assms(2,3,4)
proof (induction j1 rule: less_induct)
  case (less j1)
  have hj1: "entry M 0 j0 < entry M 0 j1" using less.prems(3) less.prems(2) by simp
  obtain j where j: "j0 \<le> j" "j < j1" "nextR M 0 j j1"
    using m_5_1_parent_exists_1[OF assms(1) less.prems(2) less.prems(1) hj1] by auto
  show ?case
  proof (cases "j = j0")
    case True
    hence "nextrel0 M j0 j1" using j(3) by (simp add: nextR_def)
    thus ?thesis by blast
  next
    case False
    with j(1) have "j0 < j" by simp
    have "(nextrel0 M)\<^sup>*\<^sup>* j0 j"
    proof (rule less.IH)
      show "j < j1" using j(2) .
      show "j < Lng M" using j(2) less.prems(1) by simp
      show "j0 < j" using \<open>j0 < j\<close> .
      show "\<forall>j''. j0 < j'' \<and> j'' \<le> j \<longrightarrow> entry M 0 j0 < entry M 0 j''"
        using less.prems(3) j(2) by auto
    qed
    moreover have "nextrel0 M j j1" using j(3) by (simp add: nextR_def)
    ultimately show ?thesis by (rule rtranclp.rtrancl_into_rtrancl)
  qed
qed

text \<open>m: 命題（親の存在の判定条件） (3) — discharges @{thm [source] p_5_1_parent_exists_3}.\<close>

lemma m_5_1_parent_exists_3:
  assumes "M \<in> T_PS" "j0 < j1" "j1 < Lng M"
    and H: "\<And>j. j0 < j \<Longrightarrow> j \<le> j1 \<Longrightarrow> entry M 0 j0 < entry M 0 j"
  shows "leR M 0 j0 j1"
proof -
  have allh: "\<forall>j. j0 < j \<and> j \<le> j1 \<longrightarrow> entry M 0 j0 < entry M 0 j" using H by blast
  have "(nextrel0 M)\<^sup>*\<^sup>* j0 j1" using le0_build[OF assms(1) assms(3) assms(2) allh] .
  thus ?thesis using assms(2,3) by (simp add: leR_def le0_def)
qed

text \<open>m: 系（直系先祖の木構造） (1) — discharges @{thm [source] p_5_1_ancestor_tree_1}.\<close>

lemma m_5_1_ancestor_tree_1:
  assumes "M \<in> T_PS" "leR M 0 j0 j1" "j0 \<le> j" "j \<le> j1"
  shows "leR M 0 j0 j"
proof (cases "j = j0")
  case True
  have "j0 < Lng M" using assms(2) by (simp add: leR_def le0_def)
  thus ?thesis using True by (simp add: leR_def le0_def)
next
  case False
  with assms(3) have j0j: "j0 < j" by simp
  have j1L: "j1 < Lng M" using assms(2) by (simp add: leR_def le0_def)
  hence jL: "j < Lng M" using assms(4) by simp
  show ?thesis
  proof (rule m_5_1_parent_exists_3[OF assms(1) j0j jL])
    fix j' assume "j0 < j'" "j' \<le> j"
    hence "j' \<le> j1" using assms(4) by simp
    show "entry M 0 j0 < entry M 0 j'"
      using m_5_1_ancestor_basic_1[OF assms(1) \<open>j0 < j'\<close> \<open>j' \<le> j1\<close> assms(2)] .
  qed
qed

text \<open>Row-1 reachability is index-monotone.\<close>

lemma nextrel1_rtrancl_mono:
  assumes "(nextrel1 M)\<^sup>*\<^sup>* a b"
  shows "a \<le> b"
  using assms by (induction rule: rtranclp_induct) (auto simp: nextrel1_def)

text \<open>Auxiliary for §5.1 系（直系先祖の基本性質） (2), by induction on the row-1 chain.\<close>

lemma le1_ances_aux:
  assumes "M \<in> T_PS" "(nextrel1 M)\<^sup>*\<^sup>* j0 j1"
  shows "\<forall>j. j0 < j \<and> j \<le> j1 \<and> le0 M j j1 \<longrightarrow> entry M 1 j0 < entry M 1 j"
  using assms(2)
proof (induction rule: rtranclp_induct)
  case base
  show ?case by auto
next
  case (step y z)
  have ley: "entry M 1 j0 \<le> entry M 1 y"
  proof (cases "j0 < y")
    case True
    have yL: "y < Lng M" using step.hyps(2) by (simp add: nextrel1_def)
    have le0yy: "le0 M y y" using yL by (rule le0_refl)
    have "entry M 1 j0 < entry M 1 y" using step.IH True le0yy by blast
    thus ?thesis by simp
  next
    case False
    have "j0 \<le> y" using step.hyps(1) nextrel1_rtrancl_mono by blast
    with False have "j0 = y" by simp
    thus ?thesis by simp
  qed
  from step.hyps(2) have yz: "y < z" and yzv: "entry M 1 y < entry M 1 z"
    and univ: "\<forall>j'. y < j' \<and> le0 M j' z \<longrightarrow> entry M 1 j' \<ge> entry M 1 z"
    by (auto simp: nextrel1_def)
  show ?case
  proof (intro allI impI)
    fix j assume j: "j0 < j \<and> j \<le> z \<and> le0 M j z"
    show "entry M 1 j0 < entry M 1 j"
    proof (cases "j \<le> y")
      case True
      have lez: "leR M 0 j z" using j by (simp add: leR_def)
      have "y \<le> z" using yz by simp
      have "leR M 0 j y" using m_5_1_ancestor_tree_1[OF assms(1) lez True \<open>y \<le> z\<close>] .
      hence "le0 M j y" by (simp add: leR_def)
      thus ?thesis using step.IH j True by blast
    next
      case False
      hence "y < j" by simp
      hence "entry M 1 j \<ge> entry M 1 z" using univ j by blast
      thus ?thesis using ley yzv by simp
    qed
  qed
qed

text \<open>m: 系（直系先祖の基本性質） (2) — discharges @{thm [source] p_5_1_ancestor_basic_2}.\<close>

lemma m_5_1_ancestor_basic_2:
  assumes "M \<in> T_PS" "j0 < j" "j \<le> j1" "leR M 1 j0 j1" "leR M 0 j j1"
  shows "entry M 1 j0 < entry M 1 j"
proof -
  from assms(4) have "(nextrel1 M)\<^sup>*\<^sup>* j0 j1" by (simp add: leR_def le1_def)
  moreover from assms(5) have "le0 M j j1" by (simp add: leR_def)
  ultimately show ?thesis using le1_ances_aux[OF assms(1)] assms(2,3) by blast
qed

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

text \<open>Auxiliary for §5.1 命題（親の存在の判定条件） (4): build a row-1 chain.\<close>

lemma le1_build:
  assumes "M \<in> T_PS" "j1 < Lng M" "j0 < j1"
    and "leR M 0 j0 j1"
    and "\<forall>j. j0 < j \<and> le0 M j j1 \<longrightarrow> entry M 1 j0 < entry M 1 j"
  shows "(nextrel1 M)\<^sup>*\<^sup>* j0 j1"
  using assms(2,3,4,5)
proof (induction j1 rule: less_induct)
  case (less j1)
  have le0j1j1: "le0 M j1 j1" using less.prems(1) by (rule le0_refl)
  have hj1: "entry M 1 j0 < entry M 1 j1"
    using less.prems(4) less.prems(2) le0j1j1 by blast
  obtain j where j: "j0 \<le> j" "j < j1" "nextR M 1 j j1"
    using m_5_1_parent_exists_2[OF assms(1) less.prems(2) less.prems(1) hj1 less.prems(3)]
    by auto
  have nx: "nextrel1 M j j1" using j(3) by (simp add: nextR_def)
  hence le0jj1: "le0 M j j1" by (simp add: nextrel1_def)
  show ?case
  proof (cases "j = j0")
    case True
    thus ?thesis using nx by blast
  next
    case False
    with j(1) have j0j: "j0 < j" by simp
    have jL: "j < Lng M" using j(2) less.prems(1) by simp
    have j0lej: "j0 \<le> j" using j0j by simp
    have jlej1: "j \<le> j1" using j(2) by simp
    have l0j: "leR M 0 j0 j"
      by (rule m_5_1_ancestor_tree_1[OF assms(1) less.prems(3) j0lej jlej1])
    have Uj: "\<forall>j'. j0 < j' \<and> le0 M j' j \<longrightarrow> entry M 1 j0 < entry M 1 j'"
    proof (intro allI impI)
      fix j' assume a: "j0 < j' \<and> le0 M j' j"
      hence "le0 M j' j1" using le0jj1 le0_trans by blast
      thus "entry M 1 j0 < entry M 1 j'" using less.prems(4) a by blast
    qed
    have chain: "(nextrel1 M)\<^sup>*\<^sup>* j0 j"
    proof (rule less.IH)
      show "j < j1" using j(2) .
      show "j < Lng M" using jL .
      show "j0 < j" using j0j .
      show "leR M 0 j0 j" using l0j .
      show "\<forall>j'. j0 < j' \<and> le0 M j' j \<longrightarrow> entry M 1 j0 < entry M 1 j'" using Uj .
    qed
    from chain nx show ?thesis by (rule rtranclp.rtrancl_into_rtrancl)
  qed
qed

text \<open>m: 命題（親の存在の判定条件） (4) — discharges @{thm [source] p_5_1_parent_exists_4}.\<close>

lemma m_5_1_parent_exists_4:
  assumes "M \<in> T_PS" "j0 < j1" "j1 < Lng M"
    and H: "\<And>j. j0 < j \<Longrightarrow> leR M 0 j j1 \<Longrightarrow> entry M 1 j0 < entry M 1 j"
    and L: "leR M 0 j0 j1"
  shows "leR M 1 j0 j1"
proof -
  have U: "\<forall>j. j0 < j \<and> le0 M j j1 \<longrightarrow> entry M 1 j0 < entry M 1 j"
  proof (intro allI impI)
    fix j assume a: "j0 < j \<and> le0 M j j1"
    hence "leR M 0 j j1" by (simp add: leR_def)
    thus "entry M 1 j0 < entry M 1 j" using H a by blast
  qed
  have "(nextrel1 M)\<^sup>*\<^sup>* j0 j1" using le1_build[OF assms(1) assms(3) assms(2) L U] .
  thus ?thesis using assms(2,3) by (simp add: leR_def le1_def)
qed

text \<open>m: 系（直系先祖の木構造） (2) — discharges @{thm [source] p_5_1_ancestor_tree_2}.\<close>

lemma m_5_1_ancestor_tree_2:
  assumes "M \<in> T_PS" "leR M 1 j0 j1" "j0 \<le> j" "leR M 0 j j1"
  shows "leR M 1 j0 j"
proof (cases "j = j0")
  case True
  have "j0 < Lng M" using assms(2) by (simp add: leR_def le1_def)
  thus ?thesis using True by (simp add: leR_def le1_def)
next
  case False
  with assms(3) have j0j: "j0 < j" by simp
  have jL: "j < Lng M" using assms(4) by (simp add: leR_def le0_def)
  have le0jj1: "le0 M j j1" using assms(4) by (simp add: leR_def)
  have jj1: "j \<le> j1"
  proof -
    have "(nextrel0 M)\<^sup>*\<^sup>* j j1" using le0jj1 by (simp add: le0_def)
    thus ?thesis by (rule nextrel0_rtrancl_mono)
  qed
  have le00j1: "leR M 0 j0 j1" using m_le1_imp_le0[OF assms(2)] .
  have j0lej: "j0 \<le> j" using j0j by simp
  have le00j: "leR M 0 j0 j"
    by (rule m_5_1_ancestor_tree_1[OF assms(1) le00j1 j0lej jj1])
  show ?thesis
  proof (rule m_5_1_parent_exists_4[OF assms(1) j0j jL _ le00j])
    fix j'' assume H1: "j0 < j''" and H2: "leR M 0 j'' j"
    have le0j''j: "le0 M j'' j" using H2 by (simp add: leR_def)
    have "j'' \<le> j"
    proof -
      have "(nextrel0 M)\<^sup>*\<^sup>* j'' j" using le0j''j by (simp add: le0_def)
      thus ?thesis by (rule nextrel0_rtrancl_mono)
    qed
    hence j''j1: "j'' \<le> j1" using jj1 by simp
    have "leR M 0 j'' j1" using le0_trans[OF le0j''j le0jj1] by (simp add: leR_def)
    thus "entry M 1 j0 < entry M 1 j''"
      using m_5_1_ancestor_basic_2[OF assms(1) H1 j''j1 assms(2)] by simp
  qed
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


section \<open>§5.4 ペア数列システム\<close>

text \<open>
  m: 命題（F_M と基本列の関係）— corrected form (see @{file "corrections.md"} A1).
  Discharges @{thm [source] p_5_4_F_oper_dom}.  Immediate from the inductive
  definition of @{const Fdom}: with \<open>Lng M > 1\<close> only @{thm [source] Fdom.Fdom_step}
  applies.
\<close>

lemma m_5_4_F_oper_dom:
  assumes "M \<in> T_PS" "n \<ge> 1" "Lng M > 1"
  shows "Fdom f M n \<longleftrightarrow> Fdom f (M[n]) (f n)"
proof
  assume h: "Fdom f M n"
  show "Fdom f (M[n]) (f n)" using h
  proof (cases rule: Fdom.cases)
    case Fdom_base
    with assms(3) show ?thesis by simp
  next
    case Fdom_step
    then show ?thesis by blast
  qed
next
  assume "Fdom f (M[n]) (f n)"
  with assms(3) show "Fdom f M n" by (rule Fdom.Fdom_step)
qed

text \<open>m: 命題（F_M と基本列の関係） value part — discharges @{thm [source] p_5_4_F_oper_val}.\<close>

lemma m_5_4_F_oper_val:
  assumes "M \<in> T_PS" "n \<ge> 1" "Lng M > 1" "Fdom f M n"
  shows "Fval f M n = Fval f (M[n]) (f n)"
  using assms(3) by (simp add: Fval.simps)


section \<open>§6.1 最上行のインクリメント\<close>

lemma Lng_IncrFirst[simp]: "Lng (IncrFirst M) = Lng M"
  by (simp add: IncrFirst_def)

lemma entry_IncrFirst:
  "j < Lng M \<Longrightarrow>
   entry (IncrFirst M) i j = (if i = 0 then Suc (entry M 0 j) else entry M i j)"
  by (simp add: IncrFirst_def entry_def)

lemma nextrel0_IncrFirst_eq: "nextrel0 (IncrFirst M) = nextrel0 M"
proof (intro ext)
  fix j0 j1
  show "nextrel0 (IncrFirst M) j0 j1 = nextrel0 M j0 j1"
    unfolding nextrel0_def by (auto simp: entry_IncrFirst)
qed

lemma le0_IncrFirst_eq: "le0 (IncrFirst M) = le0 M"
  by (intro ext) (simp add: le0_def nextrel0_IncrFirst_eq)

lemma nextrel1_IncrFirst_eq: "nextrel1 (IncrFirst M) = nextrel1 M"
proof (intro ext)
  fix j0 j1
  show "nextrel1 (IncrFirst M) j0 j1 = nextrel1 M j0 j1"
    unfolding nextrel1_def
    by (auto simp: entry_IncrFirst le0_IncrFirst_eq le0_def)
qed

lemma le1_IncrFirst_eq: "le1 (IncrFirst M) = le1 M"
  by (intro ext) (simp add: le1_def nextrel1_IncrFirst_eq)

text \<open>m: 命題（\<open>\<le>\<^sub>M\<close>の\<open>IncrFirst\<close>不変性） — discharges @{thm [source] p_6_1_le_IncrFirst_inv}.\<close>

lemma m_6_1_le_IncrFirst_inv: "leR (IncrFirst M) i j0 j1 = leR M i j0 j1"
  by (simp add: leR_def le0_IncrFirst_eq le1_IncrFirst_eq)


section \<open>§6.2 単項性\<close>

text \<open>Helper: a pair sequence in \<open>T_PS\<close> with \<open>Lng M \<noteq> 1\<close> has \<open>Lng M > 1\<close>.\<close>

lemma T_PS_Lng_gt1:
  assumes "M \<in> T_PS" "Lng M \<noteq> 1"
  shows "Lng M > 1"
  using assms by (cases M) (auto simp: T_PS_def)

text \<open>\<open>\<not> multiT\<close> coincides with \<open>(0,0) \<le>\<^sub>M (0, Lng M - 1)\<close> (criterion (1) = (3)).\<close>

lemma m_6_2_not_multi_iff_le:
  assumes "M \<in> T_PS"
  shows "(\<not> multiT M) = leR M 0 0 (Lng M - 1)"
proof
  assume "\<not> multiT M"
  hence "zeroT M \<or> monoT M" by (simp add: multiT_def)
  thus "leR M 0 0 (Lng M - 1)"
  proof
    assume "zeroT M"
    hence "Lng M = 1" by (simp add: zeroT_def)
    thus ?thesis by (simp add: leR_def le0_def)
  next
    assume "monoT M"
    thus ?thesis by (simp add: monoT_def)
  qed
next
  assume le: "leR M 0 0 (Lng M - 1)"
  show "\<not> multiT M"
  proof (cases "zeroT M")
    case True thus ?thesis by (simp add: multiT_def)
  next
    case False
    hence "monoT M" using le by (simp add: monoT_def)
    thus ?thesis by (simp add: multiT_def)
  qed
qed

text \<open>m: 命題（複項性の判定条件） (2)=(3) — discharges @{thm [source] p_6_2_multi_crit_23}.\<close>

lemma m_6_2_multi_crit_23:
  assumes "M \<in> T_PS"
  shows "(\<forall>j. 0 < j \<and> j < Lng M \<longrightarrow> entry M 0 0 < entry M 0 j) = leR M 0 0 (Lng M - 1)"
proof
  assume H: "\<forall>j. 0 < j \<and> j < Lng M \<longrightarrow> entry M 0 0 < entry M 0 j"
  show "leR M 0 0 (Lng M - 1)"
  proof (cases "Lng M = 1")
    case True thus ?thesis by (simp add: leR_def le0_def)
  next
    case False
    have L: "Lng M > 1" by (rule T_PS_Lng_gt1[OF assms False])
    show ?thesis
    proof (rule m_5_1_parent_exists_3[OF assms])
      show "0 < Lng M - 1" using L by simp
      show "Lng M - 1 < Lng M" using L by simp
      fix j assume "0 < j" "j \<le> Lng M - 1"
      hence "j < Lng M" using L by simp
      thus "entry M 0 0 < entry M 0 j" using H \<open>0 < j\<close> by blast
    qed
  qed
next
  assume le: "leR M 0 0 (Lng M - 1)"
  show "\<forall>j. 0 < j \<and> j < Lng M \<longrightarrow> entry M 0 0 < entry M 0 j"
  proof (intro allI impI)
    fix j assume a: "0 < j \<and> j < Lng M"
    hence "0 < j" "j \<le> Lng M - 1" by auto
    thus "entry M 0 0 < entry M 0 j"
      using m_5_1_ancestor_basic_1[OF assms _ _ le] by blast
  qed
qed

text \<open>m: 命題（複項性の判定条件） (1)=(2) — discharges @{thm [source] p_6_2_multi_crit_12}.\<close>

lemma m_6_2_multi_crit_12:
  assumes "M \<in> T_PS"
  shows "(\<not> multiT M) = (\<forall>j. 0 < j \<and> j < Lng M \<longrightarrow> entry M 0 0 < entry M 0 j)"
  using m_6_2_not_multi_iff_le[OF assms] m_6_2_multi_crit_23[OF assms] by simp

text \<open>Basic facts about the slice \<open>seg M a b\<close>.\<close>

lemma Lng_seg[simp]: "Lng (seg M a b) = Suc b - a"
  by (simp add: seg_def del: upt_Suc)

lemma entry_seg:
  assumes "j < Lng (seg M a b)"
  shows "entry (seg M a b) i j = entry M i (a + j)"
proof -
  have lj: "j < Suc b - a" using assms by simp
  hence "a + j < Suc b" by simp
  hence "[a..<Suc b] ! j = a + j" by (simp add: nth_upt del: upt_Suc)
  moreover have "j < length [a..<Suc b]" using lj by (simp add: length_upt del: upt_Suc)
  ultimately show ?thesis by (simp add: seg_def entry_def del: upt_Suc)
qed

text \<open>m: 命題（単項性の直系先祖による切片への遺伝性） — discharges
  @{thm [source] p_6_2_mono_ancestor_slice}.\<close>

lemma m_6_2_mono_ancestor_slice:
  assumes "M \<in> T_PS" "j0' < j1'" "leR M 0 j0' j1'"
  shows "monoT (seg M j0' j1')"
proof -
  let ?M' = "seg M j0' j1'"
  have LM'gt1: "Lng ?M' > 1" using assms(2) by simp
  have lne: "Lng ?M' \<noteq> 0" using assms(2) by simp
  have M'TPS: "?M' \<in> T_PS" using lne by (cases ?M') (auto simp: T_PS_def)
  have notzero: "\<not> zeroT ?M'" using LM'gt1 by (auto simp: zeroT_def)
  have "leR ?M' 0 0 (Lng ?M' - 1)"
  proof (rule m_5_1_parent_exists_3[OF M'TPS])
    show "0 < Lng ?M' - 1" using LM'gt1 by simp
    show "Lng ?M' - 1 < Lng ?M'" using LM'gt1 by simp
    fix j assume "0 < j" "j \<le> Lng ?M' - 1"
    hence jlt: "j < Lng ?M'" using LM'gt1 by simp
    have e0: "entry ?M' 0 0 = entry M 0 j0'" using LM'gt1 by (simp add: entry_seg)
    have ej: "entry ?M' 0 j = entry M 0 (j0' + j)" using jlt by (simp add: entry_seg)
    have "entry M 0 j0' < entry M 0 (j0' + j)"
    proof (rule m_5_1_ancestor_basic_1[OF assms(1) _ _ assms(3)])
      show "j0' < j0' + j" using \<open>0 < j\<close> by simp
      show "j0' + j \<le> j1'" using \<open>j \<le> Lng ?M' - 1\<close> assms(2) by simp
    qed
    thus "entry ?M' 0 0 < entry ?M' 0 j" using e0 ej by simp
  qed
  thus ?thesis using notzero by (simp add: monoT_def)
qed

text \<open>m: 系（単項性の始切片への遺伝性） — discharges @{thm [source] p_6_2_mono_prefix}.\<close>

lemma m_6_2_mono_prefix:
  assumes "M \<in> PT_PS" "0 < j0" "j0 < Lng M"
  shows "monoT (seg M 0 j0)"
proof -
  have MT: "M \<in> T_PS" and mono: "monoT M" using assms(1) by (simp_all add: PT_PS_def)
  have "\<not> multiT M" using mono by (simp add: multiT_def)
  hence le: "leR M 0 0 (Lng M - 1)" using m_6_2_not_multi_iff_le[OF MT] by simp
  have "leR M 0 0 j0"
  proof (rule m_5_1_ancestor_tree_1[OF MT le])
    show "0 \<le> j0" by simp
    show "j0 \<le> Lng M - 1" using assms(3) by simp
  qed
  thus ?thesis by (rule m_6_2_mono_ancestor_slice[OF MT assms(2)])
qed

text \<open>A non-empty multi-term pair sequence has length \<open>> 1\<close>.\<close>

lemma multiT_imp_Lng_gt1:
  assumes "M \<in> T_PS" "multiT M"
  shows "Lng M > 1"
proof (rule ccontr)
  assume "\<not> Lng M > 1"
  with assms(1) have L1: "Lng M = 1" by (cases M) (auto simp: T_PS_def)
  from assms(2) have "\<not> zeroT M" "\<not> monoT M" by (simp_all add: multiT_def)
  from L1 \<open>\<not> zeroT M\<close> have "monoT M" by (simp add: monoT_def leR_def le0_def)
  with \<open>\<not> monoT M\<close> show False ..
qed

text \<open>\<open>P M\<close> is always non-empty.\<close>

lemma P_nonempty: "P M \<noteq> []"
  by (subst P.simps) simp

text \<open>m: 命題（\<open>P\<close>の各成分の非複項性） (2) — discharges @{thm [source] p_6_2_P_components_2}.\<close>

lemma m_6_2_P_components_2:
  assumes "M \<in> T_PS"
  shows "multiT M \<longleftrightarrow> length (P M) > 1"
proof (cases "multiT M")
  case True
  hence "Lng M > 1" using multiT_imp_Lng_gt1[OF assms] by simp
  with True have "P M = P (take (Pcut M) M) @ [drop (Pcut M) M]"
    by (subst P.simps) simp
  hence "length (P M) = Suc (length (P (take (Pcut M) M)))" by simp
  thus ?thesis using True P_nonempty[of "take (Pcut M) M"]
    by (cases "P (take (Pcut M) M)") auto
next
  case False
  hence "P M = [M]" by (subst P.simps) simp
  with False show ?thesis by simp
qed


text \<open>
  m: 命題（\<open>P\<close>の\<open>IncrFirst\<close>同変性） — discharges @{thm [source] p_6_2_P_IncrFirst}.
  Follows from the \<open>IncrFirst\<close>-invariance of \<open>\<le>\<^sub>M\<close> (m_6_1).  We first record that
  \<open>zeroT\<close>, \<open>monoT\<close>, \<open>multiT\<close> and \<open>Pcut\<close> are all invariant under \<open>IncrFirst\<close>,
  since they depend only on \<open>Lng M\<close>, \<open>entry M 1 _\<close> (row 1, unchanged) and \<open>leR M\<close>.
\<close>

lemma IncrFirst_zeroT_eq: "zeroT (IncrFirst M) = zeroT M"
proof (cases "Lng M = 0")
  case True thus ?thesis by (simp add: zeroT_def)
next
  case False
  hence "(0::nat) < Lng M" by simp
  thus ?thesis by (simp add: zeroT_def entry_IncrFirst)
qed

lemma IncrFirst_monoT_eq: "monoT (IncrFirst M) = monoT M"
  by (simp add: monoT_def IncrFirst_zeroT_eq m_6_1_le_IncrFirst_inv)

lemma IncrFirst_multiT_eq: "multiT (IncrFirst M) = multiT M"
  by (simp add: multiT_def IncrFirst_zeroT_eq IncrFirst_monoT_eq)

lemma IncrFirst_Pcut_eq: "Pcut (IncrFirst M) = Pcut M"
  by (simp add: Pcut_def m_6_1_le_IncrFirst_inv)

lemma IncrFirst_take: "IncrFirst (take k M) = take k (IncrFirst M)"
  by (simp add: IncrFirst_def take_map)

lemma IncrFirst_drop: "IncrFirst (drop k M) = drop k (IncrFirst M)"
  by (simp add: IncrFirst_def drop_map)

lemma m_6_2_P_IncrFirst:
  shows "P (IncrFirst M) = map IncrFirst (P M)"
proof (induction M rule: P.induct)
  case (1 M)
  show ?case
  proof (cases "multiT M \<and> 1 < Lng M")
    case True
    hence step: "P M = P (take (Pcut M) M) @ [drop (Pcut M) M]"
      by (subst P.simps) simp
    from True have stepI:
      "P (IncrFirst M)
         = P (take (Pcut M) (IncrFirst M)) @ [drop (Pcut M) (IncrFirst M)]"
      by (subst P.simps) (simp add: IncrFirst_multiT_eq IncrFirst_Pcut_eq)
    have IH: "P (IncrFirst (take (Pcut M) M)) = map IncrFirst (P (take (Pcut M) M))"
      using True 1 by blast
    show ?thesis
      using stepI step IH
      by (simp add: IncrFirst_take IncrFirst_drop)
  next
    case False
    hence "P M = [M]" by (subst P.simps) simp
    moreover have "P (IncrFirst M) = [IncrFirst M]"
      using False by (subst P.simps) (simp add: IncrFirst_multiT_eq)
    ultimately show ?thesis by simp
  qed
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

text \<open>
  m: 命題（\<open>P\<close>の加法性） — discharges @{thm [source] p_6_2_P_additive}.
  Additivity of \<open>P\<close> at a left-minimal cut \<open>j\<^sub>0\<close>.  We prove the equivalent
  \<open>take\<close> / \<open>drop\<close> form by strong induction on \<open>Lng M\<close>: in the multi-term case
  the recursive cut \<open>c = Pcut M\<close> satisfies \<open>j\<^sub>0 \<le> c\<close> (article: \<open>0 < j\<^sub>0 \<le> j'\<^sub>0\<close>),
  and both the prefix \<open>take c M\<close> and the suffix \<open>drop j\<^sub>0 M\<close> are strictly shorter,
  so the induction hypothesis applies to both, mirroring the article's
  lexicographic induction on \<open>(j'\<^sub>0 - j\<^sub>0, j\<^sub>0)\<close>.
\<close>

lemma m_6_2_P_additive:
  assumes "M \<in> T_PS" "0 < j0" "j0 \<le> Lng M - 1"
    and "\<And>j. j < j0 \<Longrightarrow> entry M 0 j \<ge> entry M 0 j0"
  shows "P M = P (seg M 0 (j0 - 1)) @ P (seg M j0 (Lng M - 1))"
proof -
  have "\<forall>Mm j0. Mm \<in> T_PS \<longrightarrow> Lng Mm = n \<longrightarrow> 0 < j0 \<longrightarrow> j0 \<le> Lng Mm - 1 \<longrightarrow>
        (\<forall>j. j < j0 \<longrightarrow> entry Mm 0 j \<ge> entry Mm 0 j0) \<longrightarrow>
        P Mm = P (take j0 Mm) @ P (drop j0 Mm)" for n
  proof (induction n rule: less_induct)
    case (less n)
    show ?case
    proof (intro allI impI)
      fix j0 :: nat and Mm :: pairseq
      assume MT: "Mm \<in> T_PS" and Ln: "Lng Mm = n" and j00: "0 < j0"
        and j0L: "j0 \<le> Lng Mm - 1"
        and hyp: "\<forall>j. j < j0 \<longrightarrow> entry Mm 0 j \<ge> entry Mm 0 j0"
      have L: "Lng Mm > 1" using j00 j0L by linarith
      show "P Mm = P (take j0 Mm) @ P (drop j0 Mm)"
      proof (cases "multiT Mm")
        case nonmulti: False
        have "monoT Mm" using nonmulti L by (auto simp: multiT_def zeroT_def)
        hence le00: "leR Mm 0 0 (Lng Mm - 1)" by (simp add: monoT_def)
        have "entry Mm 0 0 < entry Mm 0 j0"
          by (rule m_5_1_ancestor_basic_1[OF MT j00 j0L le00])
        moreover have "entry Mm 0 0 \<ge> entry Mm 0 j0" using hyp j00 by blast
        ultimately show ?thesis by simp
      next
        case multi: True
        let ?c = "Pcut Mm"
        let ?j1 = "Lng Mm - 1"
        from P_add_Pcut_props[OF L] have c0: "0 < ?c" and cj1: "?c \<le> ?j1"
          and lec: "leR Mm 0 ?c ?j1" by auto
        have cL: "?c < Lng Mm" using cj1 L by simp
        have lmin: "\<And>j. j < ?c \<Longrightarrow> entry Mm 0 j \<ge> entry Mm 0 ?c"
          using P_add_Pcut_left_min[OF MT multi L] .
        have j0c: "j0 \<le> ?c"
        proof (rule ccontr)
          assume "\<not> j0 \<le> ?c"
          hence cj0: "?c < j0" by simp
          have "entry Mm 0 ?c < entry Mm 0 j0"
            by (rule m_5_1_ancestor_basic_1[OF MT cj0 j0L lec])
          moreover have "entry Mm 0 ?c \<ge> entry Mm 0 j0" using hyp cj0 by blast
          ultimately show False by simp
        qed
        have cond: "multiT Mm \<and> 1 < Lng Mm" using multi L by simp
        have Pstep: "P Mm = P (take ?c Mm) @ [drop ?c Mm]"
          by (subst P.simps) (simp only: cond if_True simp_thms)
        have Pdrop_c: "P (drop ?c Mm) = [drop ?c Mm]"
          by (rule P_add_drop_ancestor[OF MT c0 cj1 lec])
        show ?thesis
        proof (cases "j0 = ?c")
          case True
          show ?thesis using Pstep Pdrop_c True by simp
        next
          case False
          with j0c have j0ltc: "j0 < ?c" by simp
          let ?Mp = "take ?c Mm"
          have MpT: "?Mp \<in> T_PS" using c0 cL by (cases ?Mp) (auto simp: T_PS_def)
          have LMp: "Lng ?Mp = ?c" using cL by simp
          have IH1: "P ?Mp = P (take j0 ?Mp) @ P (drop j0 ?Mp)"
          proof -
            have "Lng ?Mp < n" using LMp cL Ln by simp
            moreover have "j0 \<le> Lng ?Mp - 1" using LMp j0ltc by simp
            moreover have "\<forall>j. j < j0 \<longrightarrow> entry ?Mp 0 j \<ge> entry ?Mp 0 j0"
            proof (intro allI impI)
              fix j assume "j < j0"
              hence "j < ?c" "j0 < ?c" using j0ltc by auto
              hence "entry ?Mp 0 j = entry Mm 0 j" "entry ?Mp 0 j0 = entry Mm 0 j0"
                by (auto simp: entry_def)
              thus "entry ?Mp 0 j \<ge> entry ?Mp 0 j0" using hyp \<open>j < j0\<close> by simp
            qed
            ultimately show ?thesis
              using less.IH[rule_format, OF _ MpT refl j00] by blast
          qed
          have tj0: "take j0 ?Mp = take j0 Mm"
            using j0ltc by (simp add: take_take min.absorb1)
          have dj0: "drop j0 ?Mp = take (?c - j0) (drop j0 Mm)"
            by (simp add: drop_take)
          let ?Ms = "drop j0 Mm"
          have MsT: "?Ms \<in> T_PS" using j0L L by (cases ?Ms) (auto simp: T_PS_def)
          have LMs: "Lng ?Ms = Lng Mm - j0" by simp
          have IH2: "P ?Ms = P (take (?c - j0) ?Ms) @ P (drop (?c - j0) ?Ms)"
          proof -
            have "Lng ?Ms < n" using LMs j00 Ln L by simp
            moreover have "0 < ?c - j0" using j0ltc by simp
            moreover have "?c - j0 \<le> Lng ?Ms - 1" using LMs cj1 j00 by simp
            moreover have "\<forall>j. j < ?c - j0 \<longrightarrow> entry ?Ms 0 j \<ge> entry ?Ms 0 (?c - j0)"
            proof (intro allI impI)
              fix j assume jlt: "j < ?c - j0"
              have jc: "j0 + j < ?c" using jlt j0c by simp
              hence jcL: "j0 + j < Lng Mm" using cL by simp
              have e1: "entry ?Ms 0 j = entry Mm 0 (j0 + j)"
                using jcL by (simp add: entry_def nth_drop)
              have e2: "entry ?Ms 0 (?c - j0) = entry Mm 0 ?c"
                using j0c cL by (simp add: entry_def nth_drop)
              have "entry Mm 0 (j0 + j) \<ge> entry Mm 0 ?c" using jc by (rule lmin)
              thus "entry ?Ms 0 j \<ge> entry ?Ms 0 (?c - j0)" using e1 e2 by simp
            qed
            ultimately show ?thesis
              using less.IH[rule_format, OF _ MsT refl] by blast
          qed
          have ds: "drop (?c - j0) ?Ms = drop ?c Mm"
            using j0c by (simp add: drop_drop)
          have IH1': "P (take ?c Mm) = P (take j0 Mm) @ P (take (?c - j0) ?Ms)"
            using IH1 by (simp only: tj0 dj0)
          have IH2': "P ?Ms = P (take (?c - j0) ?Ms) @ P (drop ?c Mm)"
            using IH2 by (simp only: ds)
          have "P Mm = P (take ?c Mm) @ [drop ?c Mm]" by (rule Pstep)
          also have "\<dots> = (P (take j0 Mm) @ P (take (?c - j0) ?Ms)) @ [drop ?c Mm]"
            by (simp only: IH1')
          also have "\<dots> = P (take j0 Mm) @ (P (take (?c - j0) ?Ms) @ P (drop ?c Mm))"
            by (simp only: Pdrop_c append_assoc)
          also have "\<dots> = P (take j0 Mm) @ P ?Ms" by (simp only: IH2')
          finally show ?thesis .
        qed
      qed
    qed
  qed
  hence main: "P M = P (take j0 M) @ P (drop j0 M)"
    using assms by blast
  have e1: "take j0 M = seg M 0 (j0 - 1)"
    using assms(2,3) by (subst P_add_seg_0_eq_take) auto
  have e2: "drop j0 M = seg M j0 (Lng M - 1)"
    using assms(2,3) by (subst P_add_seg_to_last_eq_drop) auto
  show ?thesis using main e1 e2 by simp
qed


text \<open>The cut index \<open>Pcut M\<close> satisfies its defining predicate when \<open>M\<close> is multi.\<close>

lemma Pcut_le:
  assumes "1 < Lng M"
  shows "0 < Pcut M \<and> Pcut M \<le> Lng M - 1 \<and> leR M 0 (Pcut M) (Lng M - 1)"
proof -
  let ?P = "\<lambda>j. 0 < j \<and> j \<le> Lng M - 1 \<and> leR M 0 j (Lng M - 1)"
  have wit: "?P (Lng M - 1)"
    using assms by (auto simp: leR_def le0_def)
  have "?P (Pcut M)"
    unfolding Pcut_def by (rule LeastI[where P = ?P, OF wit])
  thus ?thesis .
qed

text \<open>\<open>drop k M\<close> is the slice \<open>seg M k (Lng M - 1)\<close> when \<open>k < Lng M\<close>.\<close>

lemma drop_eq_seg:
  assumes "k < Lng M"
  shows "drop k M = seg M k (Lng M - 1)"
proof -
  have "Suc (Lng M - 1) = Lng M" using assms by simp
  hence eq: "seg M k (Lng M - 1) = map (nth M) [k..<Lng M]"
    by (simp add: seg_def del: upt_Suc)
  have "drop k M = map (nth M) [k..<Lng M]"
    by (intro nth_equalityI) (auto simp: nth_upt)
  thus ?thesis using eq by simp
qed

text \<open>m: 命題（\<open>P\<close>の各成分の非複項性） (1) — discharges @{thm [source] p_6_2_P_components_1}.\<close>

lemma m_6_2_P_components_1:
  assumes "M \<in> T_PS"
  shows "\<forall>M' \<in> set (P M). zeroT M' \<or> monoT M'"
proof -
  have "M \<in> T_PS \<longrightarrow> (\<forall>M' \<in> set (P M). zeroT M' \<or> monoT M')"
  proof (induction M rule: P.induct)
    case (1 M)
    show ?case
    proof (rule impI)
      assume MT: "M \<in> T_PS"
    show "\<forall>M' \<in> set (P M). zeroT M' \<or> monoT M'"
    proof (cases "multiT M \<and> 1 < Lng M")
      case False
      hence PM: "P M = [M]" by (subst P.simps) simp
      have "zeroT M \<or> monoT M"
      proof (cases "multiT M")
        case True
        \<comment> \<open>\<open>multiT M\<close> with \<open>M \<in> T_PS\<close> forces \<open>1 < Lng M\<close>, contradicting the base case.\<close>
        have "1 < Lng M" by (rule multiT_imp_Lng_gt1[OF MT True])
        with False True show ?thesis by simp
      next
        case False
        thus ?thesis by (simp add: multiT_def)
      qed
      thus ?thesis using PM by simp
    next
      case True
      hence multi: "multiT M" and L: "1 < Lng M" by simp_all
      have PM: "P M = P (take (Pcut M) M) @ [drop (Pcut M) M]"
        using True by (subst P.simps) simp
      have cut: "0 < Pcut M \<and> Pcut M \<le> Lng M - 1 \<and> leR M 0 (Pcut M) (Lng M - 1)"
        by (rule Pcut_le[OF L])
      hence c0: "0 < Pcut M" and c1: "Pcut M \<le> Lng M - 1"
        and cle: "leR M 0 (Pcut M) (Lng M - 1)" by simp_all
      have cltL: "Pcut M < Lng M" using c1 L by simp
      \<comment> \<open>The prefix \<open>take (Pcut M) M\<close> is non-empty, hence in \<open>T_PS\<close>; apply the IH.\<close>
      have pre_TPS: "take (Pcut M) M \<in> T_PS"
      proof -
        have "Lng (take (Pcut M) M) = Pcut M" using cltL by simp
        hence "take (Pcut M) M \<noteq> []" using c0 by auto
        thus ?thesis by (simp add: T_PS_def)
      qed
      have IH: "\<forall>M' \<in> set (P (take (Pcut M) M)). zeroT M' \<or> monoT M'"
        using "1.IH"[OF True] pre_TPS by blast
      have last_nonmulti: "zeroT (drop (Pcut M) M) \<or> monoT (drop (Pcut M) M)"
      proof (cases "Pcut M < Lng M - 1")
        case True
        have "monoT (seg M (Pcut M) (Lng M - 1))"
          by (rule m_6_2_mono_ancestor_slice[OF MT True cle])
        hence "monoT (drop (Pcut M) M)" unfolding drop_eq_seg[OF cltL] .
        thus ?thesis by simp
      next
        case False
        with c1 have eq: "Pcut M = Lng M - 1" by simp
        let ?M' = "drop (Pcut M) M"
        have len1: "Lng ?M' = 1" using eq cltL by simp
        show ?thesis
        proof (cases "entry ?M' 1 0 = 0")
          case True
          thus ?thesis using len1 by (simp add: zeroT_def)
        next
          case False
          have nz: "\<not> zeroT ?M'" using False by (simp add: zeroT_def)
          have "leR ?M' 0 0 (Lng ?M' - 1)"
            using len1 by (simp add: leR_def le0_def)
          thus ?thesis using nz by (simp add: monoT_def)
        qed
      qed
      have setPM: "set (P M) = set (P (take (Pcut M) M)) \<union> {drop (Pcut M) M}"
        by (subst PM) (simp del: P.simps)
      show ?thesis unfolding setPM using IH last_nonmulti by blast
    qed
    qed
  qed
  thus ?thesis using assms by blast
qed


subsection \<open>§6.3 許容性\<close>

text \<open>
  THE KEY HELPER for the §6.3 slice lemmas.  For a slice \<open>N = seg M j0' j1'\<close>
  (with \<open>j1' < Lng M\<close>) the row-0 \<open><\<^sup>Next\<close> relation on \<open>N\<close> corresponds
  exactly to that on \<open>M\<close>, shifted by \<open>j0'\<close>, on the index range of \<open>N\<close>.
  Both \<open>nextrel0 N a b\<close> and \<open>nextrel0 M (j0'+a) (j0'+b)\<close> have the same shape;
  the middle-condition quantifiers correspond under \<open>j' = j0'+j\<close>, and the
  length bounds agree because \<open>b < Lng N \<longleftrightarrow> j0'+b \<le> j1' < Lng M\<close>.
\<close>

lemma adm_nextrel0_seg:
  assumes "j1' < Lng M" "a < Lng (seg M j0' j1')" "b < Lng (seg M j0' j1')"
  shows "nextrel0 (seg M j0' j1') a b \<longleftrightarrow> nextrel0 M (j0' + a) (j0' + b)"
proof -
  let ?N = "seg M j0' j1'"
  have aN: "a < Suc j1' - j0'" and bN: "b < Suc j1' - j0'" using assms(2,3) by simp_all
  have aLM: "j0' + a < Lng M" using aN assms(1) by simp
  have bLM: "j0' + b < Lng M" using bN assms(1) by simp
  have eA: "entry ?N 0 a = entry M 0 (j0' + a)" using assms(2) by (simp add: entry_seg)
  have eB: "entry ?N 0 b = entry M 0 (j0' + b)" using assms(3) by (simp add: entry_seg)
  have mid: "(\<forall>j. a < j \<and> j < b \<longrightarrow> entry ?N 0 j \<ge> entry ?N 0 b)
           = (\<forall>j'. j0' + a < j' \<and> j' < j0' + b \<longrightarrow> entry M 0 j' \<ge> entry M 0 (j0' + b))"
  proof
    assume H: "\<forall>j. a < j \<and> j < b \<longrightarrow> entry ?N 0 j \<ge> entry ?N 0 b"
    show "\<forall>j'. j0' + a < j' \<and> j' < j0' + b \<longrightarrow> entry M 0 j' \<ge> entry M 0 (j0' + b)"
    proof (intro allI impI)
      fix j' assume a': "j0' + a < j' \<and> j' < j0' + b"
      have j0j': "j0' \<le> j'" using a' by simp
      let ?j = "j' - j0'"
      have jN: "?j < Lng ?N" using a' bN j0j' by (simp only: Lng_seg) linarith
      have "a < ?j \<and> ?j < b" using a' j0j' by linarith
      hence "entry ?N 0 ?j \<ge> entry ?N 0 b" using H by blast
      moreover have "entry ?N 0 ?j = entry M 0 j'" using jN a' by (simp add: entry_seg)
      ultimately show "entry M 0 j' \<ge> entry M 0 (j0' + b)" using eB by simp
    qed
  next
    assume H: "\<forall>j'. j0' + a < j' \<and> j' < j0' + b \<longrightarrow> entry M 0 j' \<ge> entry M 0 (j0' + b)"
    show "\<forall>j. a < j \<and> j < b \<longrightarrow> entry ?N 0 j \<ge> entry ?N 0 b"
    proof (intro allI impI)
      fix j assume aj: "a < j \<and> j < b"
      hence jN: "j < Lng ?N" using bN by simp
      have ej: "entry ?N 0 j = entry M 0 (j0' + j)" using jN by (simp add: entry_seg)
      have "j0' + a < j0' + j \<and> j0' + j < j0' + b" using aj by simp
      hence "entry M 0 (j0' + j) \<ge> entry M 0 (j0' + b)" using H by blast
      thus "entry ?N 0 j \<ge> entry ?N 0 b" using ej eB by simp
    qed
  qed
  have "nextrel0 ?N a b \<longleftrightarrow>
        (a < Lng ?N \<and> b < Lng ?N \<and> a < b \<and> entry ?N 0 a < entry ?N 0 b \<and>
         (\<forall>j. a < j \<and> j < b \<longrightarrow> entry ?N 0 j \<ge> entry ?N 0 b))"
    by (simp add: nextrel0_def)
  also have "\<dots> \<longleftrightarrow>
        (j0' + a < Lng M \<and> j0' + b < Lng M \<and> j0' + a < j0' + b \<and>
         entry M 0 (j0' + a) < entry M 0 (j0' + b) \<and>
         (\<forall>j'. j0' + a < j' \<and> j' < j0' + b \<longrightarrow> entry M 0 j' \<ge> entry M 0 (j0' + b)))"
    using assms(2,3) aLM bLM eA eB mid by auto
  also have "\<dots> \<longleftrightarrow> nextrel0 M (j0' + a) (j0' + b)"
    by (simp add: nextrel0_def)
  finally show ?thesis .
qed

text \<open>An \<open>M\<close>-chain inside \<open>[j0'..j1']\<close> transfers to an \<open>N\<close>-chain (shifted).\<close>

lemma adm_le0_seg_M_to_N:
  assumes "j1' < Lng M" "(nextrel0 M)\<^sup>*\<^sup>* (j0' + a) c" "c \<le> j1'"
  shows "(nextrel0 (seg M j0' j1'))\<^sup>*\<^sup>* a (c - j0')"
  using assms(2,3)
proof (induction rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step y z)
  have ge0: "j0' + a \<le> y" using step.hyps(1) by (rule nextrel0_rtrancl_mono)
  have yz: "y < z" using step.hyps(2) by (simp add: nextrel0_def)
  have yj1: "y \<le> j1'" using yz step.prems by simp
  have IHy: "(nextrel0 (seg M j0' j1'))\<^sup>*\<^sup>* a (y - j0')" using step.IH yj1 by simp
  have yN: "y - j0' < Lng (seg M j0' j1')" using yj1 ge0 by simp
  have zN: "z - j0' < Lng (seg M j0' j1')" using step.prems ge0 yz by simp
  have "j0' + (y - j0') = y" using ge0 by simp
  moreover have "j0' + (z - j0') = z" using ge0 yz by simp
  ultimately have "nextrel0 (seg M j0' j1') (y - j0') (z - j0')"
    using adm_nextrel0_seg[OF assms(1) yN zN] step.hyps(2) by simp
  with IHy show ?case by (rule rtranclp.rtrancl_into_rtrancl)
qed

text \<open>Conversely an \<open>N\<close>-chain transfers to an \<open>M\<close>-chain (shifted up).\<close>

lemma adm_le0_seg_N_to_M:
  assumes "j1' < Lng M" "(nextrel0 (seg M j0' j1'))\<^sup>*\<^sup>* a b"
  shows "(nextrel0 M)\<^sup>*\<^sup>* (j0' + a) (j0' + b)"
  using assms(2)
proof (induction rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step y z)
  have yz: "y < z" using step.hyps(2) by (simp add: nextrel0_def)
  have zN: "z < Lng (seg M j0' j1')" using step.hyps(2) by (simp add: nextrel0_def)
  have yN: "y < Lng (seg M j0' j1')" using yz zN by simp
  have "nextrel0 M (j0' + y) (j0' + z)"
    using adm_nextrel0_seg[OF assms(1) yN zN] step.hyps(2) by simp
  with step.IH show ?case by (rule rtranclp.rtrancl_into_rtrancl)
qed

text \<open>
  Hence \<open>le0\<close> on the slice corresponds to \<open>le0\<close> on \<open>M\<close> shifted by \<open>j0'\<close>, for
  indices in range.
\<close>

lemma adm_le0_seg:
  assumes "j1' < Lng M" "a \<le> j1' - j0'" "b \<le> j1' - j0'" "j0' \<le> j1'"
  shows "le0 (seg M j0' j1') a b \<longleftrightarrow> le0 M (j0' + a) (j0' + b)"
proof
  assume "le0 (seg M j0' j1') a b"
  hence ch: "(nextrel0 (seg M j0' j1'))\<^sup>*\<^sup>* a b"
    and aN: "a < Lng (seg M j0' j1')" and bN: "b < Lng (seg M j0' j1')"
    by (simp_all add: le0_def)
  have "(nextrel0 M)\<^sup>*\<^sup>* (j0' + a) (j0' + b)"
    by (rule adm_le0_seg_N_to_M[OF assms(1) ch])
  moreover have "j0' + a < Lng M" using aN assms(1) by simp
  moreover have "j0' + b < Lng M" using bN assms(1) by simp
  ultimately show "le0 M (j0' + a) (j0' + b)" by (simp add: le0_def)
next
  assume "le0 M (j0' + a) (j0' + b)"
  hence ch: "(nextrel0 M)\<^sup>*\<^sup>* (j0' + a) (j0' + b)" by (simp add: le0_def)
  have cj1: "j0' + b \<le> j1'" using assms(3,4) by simp
  have "(nextrel0 (seg M j0' j1'))\<^sup>*\<^sup>* a (j0' + b - j0')"
    by (rule adm_le0_seg_M_to_N[OF assms(1) ch cj1])
  hence "(nextrel0 (seg M j0' j1'))\<^sup>*\<^sup>* a b" by simp
  moreover have "a < Lng (seg M j0' j1')" using assms(2,4) by simp
  moreover have "b < Lng (seg M j0' j1')" using assms(3,4) by simp
  ultimately show "le0 (seg M j0' j1') a b" by (simp add: le0_def)
qed

text \<open>
  The row-1 \<open><\<^sup>Next\<close> relation also corresponds on the slice interior.  Here
  \<open>nextrel1\<close> additionally constrains the row-1 entries and quantifies over
  \<open>le0 _ j j1\<close>-ancestors; the \<open>le0\<close> correspondence above turns the universal
  condition on \<open>N\<close> into the one on \<open>M\<close>.
\<close>

lemma adm_nextrel1_seg:
  assumes "j1' < Lng M" "a < Lng (seg M j0' j1')" "b < Lng (seg M j0' j1')"
  shows "nextrel1 (seg M j0' j1') a b \<longleftrightarrow> nextrel1 M (j0' + a) (j0' + b)"
proof -
  let ?N = "seg M j0' j1'"
  have aN: "a < Suc j1' - j0'" and bN: "b < Suc j1' - j0'" using assms(2,3) by simp_all
  have j0j1: "j0' \<le> j1'" using bN by simp
  have aLM: "j0' + a < Lng M" using aN assms(1) by simp
  have bLM: "j0' + b < Lng M" using bN assms(1) by simp
  have eA: "entry ?N 1 a = entry M 1 (j0' + a)" using assms(2) by (simp add: entry_seg)
  have eB: "entry ?N 1 b = entry M 1 (j0' + b)" using assms(3) by (simp add: entry_seg)
  have le0AB: "le0 ?N a b \<longleftrightarrow> le0 M (j0' + a) (j0' + b)"
    using adm_le0_seg[OF assms(1) _ _ j0j1] aN bN by simp
  have univ: "(\<forall>j. a < j \<and> le0 ?N j b \<longrightarrow> entry ?N 1 j \<ge> entry ?N 1 b)
            = (\<forall>j'. j0' + a < j' \<and> le0 M j' (j0' + b) \<longrightarrow> entry M 1 j' \<ge> entry M 1 (j0' + b))"
  proof
    assume H: "\<forall>j. a < j \<and> le0 ?N j b \<longrightarrow> entry ?N 1 j \<ge> entry ?N 1 b"
    show "\<forall>j'. j0' + a < j' \<and> le0 M j' (j0' + b) \<longrightarrow> entry M 1 j' \<ge> entry M 1 (j0' + b)"
    proof (intro allI impI)
      fix j' assume a': "j0' + a < j' \<and> le0 M j' (j0' + b)"
      hence le0': "le0 M j' (j0' + b)" by simp
      have j'le: "j' \<le> j0' + b"
      proof -
        have "(nextrel0 M)\<^sup>*\<^sup>* j' (j0' + b)" using le0' by (simp add: le0_def)
        thus ?thesis by (rule nextrel0_rtrancl_mono)
      qed
      have j'ge: "j0' \<le> j'" using a' by simp
      let ?j = "j' - j0'"
      have jb: "?j \<le> j1' - j0'" using j'le bN j0j1 j'ge by linarith
      have aj: "a < ?j" using a' j'ge by linarith
      have le0Nj: "le0 ?N ?j b"
        using adm_le0_seg[OF assms(1) _ _ j0j1] jb bN le0' j'ge by simp
      have ejN: "entry ?N 1 ?j = entry M 1 j'"
        using j'le j'ge bN by (simp add: entry_seg)
      have "entry ?N 1 ?j \<ge> entry ?N 1 b" using H aj le0Nj by blast
      thus "entry M 1 j' \<ge> entry M 1 (j0' + b)" using ejN eB by simp
    qed
  next
    assume H: "\<forall>j'. j0' + a < j' \<and> le0 M j' (j0' + b) \<longrightarrow> entry M 1 j' \<ge> entry M 1 (j0' + b)"
    show "\<forall>j. a < j \<and> le0 ?N j b \<longrightarrow> entry ?N 1 j \<ge> entry ?N 1 b"
    proof (intro allI impI)
      fix j assume aj: "a < j \<and> le0 ?N j b"
      hence le0Nj: "le0 ?N j b" by simp
      have jN: "j < Lng ?N" using le0Nj by (simp add: le0_def)
      have jb: "j \<le> j1' - j0'" using jN by simp
      have le0M: "le0 M (j0' + j) (j0' + b)"
        using adm_le0_seg[OF assms(1) jb _ j0j1] bN le0Nj by simp
      have "j0' + a < j0' + j" using aj by simp
      hence "entry M 1 (j0' + j) \<ge> entry M 1 (j0' + b)" using H le0M by blast
      moreover have "entry ?N 1 j = entry M 1 (j0' + j)" using jN by (simp add: entry_seg)
      ultimately show "entry ?N 1 j \<ge> entry ?N 1 b" using eB by simp
    qed
  qed
  have "nextrel1 ?N a b \<longleftrightarrow>
        (a < Lng ?N \<and> b < Lng ?N \<and> a < b \<and> entry ?N 1 a < entry ?N 1 b \<and>
         le0 ?N a b \<and>
         (\<forall>j. a < j \<and> le0 ?N j b \<longrightarrow> entry ?N 1 j \<ge> entry ?N 1 b))"
    by (simp add: nextrel1_def)
  also have "\<dots> \<longleftrightarrow>
        (j0' + a < Lng M \<and> j0' + b < Lng M \<and> j0' + a < j0' + b \<and>
         entry M 1 (j0' + a) < entry M 1 (j0' + b) \<and>
         le0 M (j0' + a) (j0' + b) \<and>
         (\<forall>j'. j0' + a < j' \<and> le0 M j' (j0' + b) \<longrightarrow> entry M 1 j' \<ge> entry M 1 (j0' + b)))"
    using assms(2,3) aLM bLM eA eB le0AB univ by auto
  also have "\<dots> \<longleftrightarrow> nextrel1 M (j0' + a) (j0' + b)"
    by (simp add: nextrel1_def)
  finally show ?thesis .
qed

text \<open>
  Row-1 \<open>nextR\<close> on the slice interior corresponds to that on \<open>M\<close> shifted by
  \<open>j0'\<close>.  This is the statement the article uses at line 611.
\<close>

lemma adm_nextR1_seg:
  assumes "j1' < Lng M" "a < Lng (seg M j0' j1')" "b < Lng (seg M j0' j1')"
  shows "nextR (seg M j0' j1') 1 a b \<longleftrightarrow> nextR M 1 (j0' + a) (j0' + b)"
  using adm_nextrel1_seg[OF assms] by (simp add: nextR_def)

text \<open>m: 命題（許容性の切片への遺伝性） — discharges @{thm [source] p_6_3_adm_slice}.\<close>

lemma m_6_3_adm_slice:
  assumes "M \<in> T_PS" "j0' \<le> j0" "j0 \<le> j1'" "j1' \<le> Lng M - 1"
  shows "(adm M j0 \<or> j0' = j0 \<or> j0 = j1') = adm (seg M j0' j1') (j0 - j0')"
proof -
  let ?N = "seg M j0' j1'"
  have LM: "Lng M > 0" using assms(1) by (cases M) (auto simp: T_PS_def)
  have j1LM: "j1' < Lng M" using assms(4) LM by linarith
  have LN: "Lng ?N = Suc j1' - j0'" by simp
  show ?thesis
  proof (cases "j0' = j0 \<or> j0 = j1'")
    case True
    \<comment> \<open>Boundary cases: \<open>j0-j0'\<close> is \<open>0\<close> or \<open>Lng N - 1\<close>, so \<open>j0-j0'\<close> is \<open>N\<close>-admissible.\<close>
    have lhs: "adm M j0 \<or> j0' = j0 \<or> j0 = j1'" using True by blast
    have "adm ?N (j0 - j0')"
    proof -
      have "\<not> nadm ?N (j0 - j0')"
      proof
        assume nd: "nadm ?N (j0 - j0')"
        have notgt: "\<not> (j0 - j0' > Lng ?N)" using assms(2,3) LN by simp
        with nd have nx2: "nextR ?N 1 (j0 - j0') (j0 - j0' + 1)"
          by (simp add: nadm_def)
        from True show False
        proof
          assume "j0' = j0"
          hence "j0 - j0' = 0" by simp
          with nd notgt have "nextR ?N 1 0 (0 - 1) \<and> nextR ?N 1 0 (0 + 1)"
            by (simp add: nadm_def)
          \<comment> \<open>\<open>nextR ?N 1 0 (0-1)\<close> needs \<open>0 < 0\<close>; impossible.\<close>
          hence "nextrel1 ?N 0 0" by (simp add: nextR_def)
          thus False by (simp add: nextrel1_def)
        next
          assume e: "j0 = j1'"
          hence jeq: "j0 - j0' = Lng ?N - 1" using LN assms(2,3) by simp
          have "j0 - j0' + 1 < Lng ?N" using nx2 by (simp add: nextR_def nextrel1_def)
          thus False using jeq LN assms(2,3) e by simp
        qed
      qed
      thus ?thesis by (simp add: adm_def)
    qed
    thus ?thesis using lhs by blast
  next
    case False
    hence ne: "j0' \<noteq> j0" "j0 \<noteq> j1'" by auto
    hence j0'j0: "j0' < j0" and j0j1: "j0 < j1'" using assms(2,3) by auto
    have lhs_eq: "(adm M j0 \<or> j0' = j0 \<or> j0 = j1') = adm M j0" using ne by blast
    \<comment> \<open>Strict interior: reduce to the row-1 \<open>nextR\<close> correspondence.\<close>
    have notgtM: "\<not> (j0 > Lng M)" using j0j1 j1LM by simp
    have notgtN: "\<not> (j0 - j0' > Lng ?N)" using assms(2,3) LN by simp
    \<comment> \<open>indices of the two relevant relations are in range of \<open>N\<close>.\<close>
    have b1: "j0 - j0' - 1 < Lng ?N" using j0'j0 j0j1 LN by simp
    have b2: "j0 - j0' < Lng ?N" using j0j1 LN assms(2) by simp
    have b3: "j0 - j0' + 1 < Lng ?N" using j0j1 LN assms(2) by simp
    have sh1: "j0' + (j0 - j0' - 1) = j0 - 1" using j0'j0 by simp
    have sh2: "j0' + (j0 - j0') = j0" using j0'j0 by simp
    have sh3: "j0' + (j0 - j0' + 1) = j0 + 1" using j0'j0 by simp
    have c1: "nextR ?N 1 (j0 - j0' - 1) (j0 - j0') \<longleftrightarrow> nextR M 1 (j0 - 1) j0"
      using adm_nextR1_seg[OF j1LM b1 b2] sh1 sh2 by simp
    have c2: "nextR ?N 1 (j0 - j0') (j0 - j0' + 1) \<longleftrightarrow> nextR M 1 j0 (j0 + 1)"
      using adm_nextR1_seg[OF j1LM b2 b3] sh2 sh3 by simp
    have "nadm M j0 \<longleftrightarrow> nadm ?N (j0 - j0')"
      using notgtM notgtN c1 c2 by (simp add: nadm_def)
    hence "adm M j0 \<longleftrightarrow> adm ?N (j0 - j0')" by (simp add: adm_def)
    thus ?thesis using lhs_eq by simp
  qed
qed

text \<open>\<open>0\<close> is always \<open>M\<close>-admissible (\<open>(1,-1) <\<^sup>Next (1,0)\<close> is impossible).\<close>

lemma adm_zero: "adm M 0"
proof -
  have "\<not> nextR M 1 0 0" by (simp add: nextR_def nextrel1_def)
  hence "\<not> nadm M 0" by (auto simp: nadm_def)
  thus ?thesis by (simp add: adm_def)
qed

text \<open>The admissible set below a non-admissible \<open>j\<close> is finite and non-empty.\<close>

lemma adm_below_set_finite: "finite {j'. adm M j' \<and> j' < j}"
  by (rule finite_subset[of _ "{..<j}"]) auto

lemma adm_below_set_nonempty:
  assumes "\<not> adm M j"
  shows "{j'. adm M j' \<and> j' < j} \<noteq> {}"
proof -
  have "0 < j"
  proof (rule ccontr)
    assume "\<not> 0 < j"
    hence "j = 0" by simp
    thus False using assms adm_zero by simp
  qed
  thus ?thesis using adm_zero by blast
qed

text \<open>\<open>Adm M j\<close> is itself \<open>M\<close>-admissible.\<close>

lemma adm_Adm_adm: "adm M (Adm M j)"
proof (cases "adm M j")
  case True thus ?thesis by (simp add: Adm_def)
next
  case False
  let ?S = "{j'. adm M j' \<and> j' < j}"
  have "Max ?S \<in> ?S"
    by (rule Max_in[OF adm_below_set_finite adm_below_set_nonempty[OF False]])
  hence "adm M (Max ?S)" by simp
  thus ?thesis using False by (simp add: Adm_def)
qed

text \<open>\<open>Adm M j \<le> j\<close>.\<close>

lemma adm_Adm_le: "Adm M j \<le> j"
proof (cases "adm M j")
  case True thus ?thesis by (simp add: Adm_def)
next
  case False
  let ?S = "{j'. adm M j' \<and> j' < j}"
  have "Max ?S \<in> ?S"
    by (rule Max_in[OF adm_below_set_finite adm_below_set_nonempty[OF False]])
  hence "Max ?S < j" by simp
  thus ?thesis using False by (simp add: Adm_def)
qed

text \<open>Maximality: any admissible \<open>k \<le> j\<close> is \<open>\<le> Adm M j\<close>.\<close>

lemma adm_Adm_max:
  assumes "adm M k" "k \<le> j"
  shows "k \<le> Adm M j"
proof (cases "adm M j")
  case True thus ?thesis using assms by (simp add: Adm_def)
next
  case False
  let ?S = "{j'. adm M j' \<and> j' < j}"
  have kj: "k < j" using assms False by (cases "k = j") auto
  hence "k \<in> ?S" using assms(1) by simp
  hence "k \<le> Max ?S" by (rule Max_ge[OF adm_below_set_finite])
  thus ?thesis using False by (simp add: Adm_def)
qed

text \<open>m: 命題（許容化の切片への遺伝性） — discharges @{thm [source] p_6_3_admof_slice}.\<close>

lemma m_6_3_admof_slice:
  assumes "M \<in> T_PS" "j0' \<le> Adm M j0" "j0 < j1'" "j1' \<le> Lng M - 1"
  shows "Adm (seg M j0' j1') (j0 - j0') = Adm M j0 - j0'"
proof -
  let ?N = "seg M j0' j1'"
  let ?am = "Adm M j0"
  let ?aN = "Adm ?N (j0 - j0')"
  have LM: "Lng M > 0" using assms(1) by (cases M) (auto simp: T_PS_def)
  have j1LM: "j1' < Lng M" using assms(4) LM by linarith
  have amle: "?am \<le> j0" by (rule adm_Adm_le)
  have amadm: "adm M ?am" by (rule adm_Adm_adm)
  have j0'am: "j0' \<le> ?am" using assms(2) .
  have j0'j0: "j0' \<le> j0" using j0'am amle by simp
  \<comment> \<open>\<open>?am\<close> is \<open>M\<close>-admissible and \<open>j0' \<le> ?am \<le> j0 < j1'\<close>, so \<open>?am - j0'\<close> is
      \<open>?N\<close>-admissible by the slice lemma.\<close>
  have amN: "adm ?N (?am - j0')"
  proof -
    have "(adm M ?am \<or> j0' = ?am \<or> ?am = j1') = adm ?N (?am - j0')"
      by (rule m_6_3_adm_slice[OF assms(1) j0'am _ assms(4)]) (use amle assms(3) in simp)
    thus ?thesis using amadm by simp
  qed
  have amj1: "?am - j0' \<le> j0 - j0'" using amle by simp
  \<comment> \<open>Lower bound: \<open>?aN \<ge> ?am - j0'\<close> by maximality of \<open>?aN\<close>.\<close>
  have ge: "?am - j0' \<le> ?aN" by (rule adm_Adm_max[OF amN amj1])
  \<comment> \<open>Upper bound.  First, \<open>?aN \<le> j0 - j0'\<close> and \<open>?aN\<close> is \<open>?N\<close>-admissible.\<close>
  have aNle: "?aN \<le> j0 - j0'" by (rule adm_Adm_le)
  have aNadm: "adm ?N ?aN" by (rule adm_Adm_adm)
  \<comment> \<open>\<open>?aN + j0'\<close> is \<open>M\<close>-admissible or hits a boundary, hence \<open>\<le> ?am\<close>.\<close>
  have le: "?aN \<le> ?am - j0'"
  proof (rule ccontr)
    assume "\<not> ?aN \<le> ?am - j0'"
    hence gt: "?am - j0' < ?aN" by simp
    have aNj0: "?aN + j0' \<le> j0" using aNle j0'j0 by simp
    \<comment> \<open>Convert \<open>?N\<close>-admissibility of \<open>?aN\<close> back to \<open>M\<close> at index \<open>?aN + j0'\<close>.\<close>
    have eq: "(adm M (?aN + j0') \<or> j0' = ?aN + j0' \<or> ?aN + j0' = j1')
              = adm ?N ((?aN + j0') - j0')"
      by (rule m_6_3_adm_slice[OF assms(1) _ _ assms(4)])
         (use aNj0 assms(3) in simp_all)
    have "(?aN + j0') - j0' = ?aN" by simp
    with eq aNadm have disj: "adm M (?aN + j0') \<or> j0' = ?aN + j0' \<or> ?aN + j0' = j1'"
      by simp
    \<comment> \<open>\<open>j0' = ?aN + j0'\<close> means \<open>?aN = 0 \<le> ?am - j0'\<close>, contradicting \<open>gt\<close>;
        \<open>?aN + j0' = j1' > j0 \<ge> ?aN + j0'\<close> is impossible; so \<open>?aN + j0'\<close> is
        \<open>M\<close>-admissible.\<close>
    have admM: "adm M (?aN + j0')"
    proof -
      have "j0' \<noteq> ?aN + j0'" using gt by auto
      moreover have "?aN + j0' \<noteq> j1'" using aNj0 assms(3) by simp
      ultimately show ?thesis using disj by blast
    qed
    \<comment> \<open>By maximality of \<open>?am\<close>, \<open>?aN + j0' \<le> ?am\<close>, i.e. \<open>?aN \<le> ?am - j0'\<close>.\<close>
    have "?aN + j0' \<le> ?am" by (rule adm_Adm_max[OF admM aNj0])
    hence "?aN \<le> ?am - j0'" using j0'am by simp
    thus False using gt by simp
  qed
  show ?thesis using ge le by simp
qed

text \<open>m: 命題（基点の切片への遺伝性） — discharges @{thm [source] p_6_3_marked_slice}.\<close>

lemma m_6_3_marked_slice:
  assumes "(M, m) \<in> Marked" "j0' \<le> m" "m \<le> j1'" "j1' \<le> Lng M - 1"
  shows "(seg M j0' j1', m - j0') \<in> Marked"
proof -
  let ?N = "seg M j0' j1'"
  have MT: "M \<in> T_PS" and admM: "adm M m" and leM: "leR M 0 m (Lng M - 1)"
    using assms(1) by (auto simp: Marked_def)
  have LM: "Lng M > 0" using MT by (cases M) (auto simp: T_PS_def)
  have j1LM: "j1' < Lng M" using assms(4) LM by linarith
  have j0j1: "j0' \<le> j1'" using assms(2,3) by simp
  \<comment> \<open>\<open>?N\<close> is non-empty, hence in \<open>T_PS\<close>.\<close>
  have LN: "Lng ?N = Suc j1' - j0'" by simp
  have LNpos: "Lng ?N > 0" using j0j1 LN by simp
  have NT: "?N \<in> T_PS" using LNpos by (cases ?N) (auto simp: T_PS_def)
  \<comment> \<open>\<open>m - j0'\<close> is \<open>?N\<close>-admissible by the slice lemma.\<close>
  have admN: "adm ?N (m - j0')"
  proof -
    have "(adm M m \<or> j0' = m \<or> m = j1') = adm ?N (m - j0')"
      by (rule m_6_3_adm_slice[OF MT assms(2,3,4)])
    thus ?thesis using admM by blast
  qed
  \<comment> \<open>\<open>(0, m - j0') \<le>\<^sub>?N (0, Lng ?N - 1)\<close> via the row-0 \<open>le0\<close> slice correspondence.\<close>
  have leN: "leR ?N 0 (m - j0') (Lng ?N - 1)"
  proof -
    have mlast: "leR M 0 m (Lng M - 1)" by (rule leM)
    \<comment> \<open>Bring the row-0 ancestry down to the slice's last index \<open>j1'\<close>.\<close>
    have mj1: "leR M 0 m j1'"
      by (rule m_5_1_ancestor_tree_1[OF MT mlast assms(3)]) (use assms(4) LM in linarith)
    have le0Mj1: "le0 M (j0' + (m - j0')) (j0' + (j1' - j0'))"
      using mj1 assms(2,3) j0j1 by (simp add: leR_def)
    have "le0 ?N (m - j0') (j1' - j0')"
      using adm_le0_seg[OF j1LM _ _ j0j1] assms(2,3) j0j1 le0Mj1 by simp
    moreover have "Lng ?N - 1 = j1' - j0'" using LN by simp
    ultimately show ?thesis by (simp add: leR_def)
  qed
  show ?thesis using NT admN leN by (simp add: Marked_def)
qed


text \<open>m: 命題（\<open>P\<close>と基本列の関係） — discharges @{thm [source] p_6_2_P_oper_1},
  @{thm [source] p_6_2_P_oper_2}.\<close>

text \<open>\<open>concat (P M) = M\<close>: the \<open>P\<close>-decomposition reassembles to \<open>M\<close>.\<close>

lemma poper_P_multi:
  assumes "multiT M \<and> 1 < Lng M"
  shows "P M = P (take (Pcut M) M) @ [drop (Pcut M) M]"
  by (subst P.simps) (simp only: if_P[OF assms])

lemma poper_P_nonmulti:
  assumes "\<not> (multiT M \<and> 1 < Lng M)"
  shows "P M = [M]"
  by (subst P.simps) (simp only: if_not_P[OF assms])

lemma poper_concat_P: "concat (P M) = M"
proof (induction M rule: P.induct)
  case (1 M)
  show ?case
  proof (cases "multiT M \<and> 1 < Lng M")
    case True
    have step: "P M = P (take (Pcut M) M) @ [drop (Pcut M) M]"
      by (rule poper_P_multi[OF True])
    have "concat (P M) = concat (P (take (Pcut M) M)) @ drop (Pcut M) M"
      by (simp only: step concat_append concat.simps append_Nil2)
    also have "\<dots> = take (Pcut M) M @ drop (Pcut M) M"
      using True 1 by simp
    also have "\<dots> = M" by simp
    finally show ?thesis .
  next
    case False
    have "P M = [M]" by (rule poper_P_nonmulti[OF False])
    thus ?thesis by simp
  qed
qed

text \<open>Structure of \<open>P M\<close> in the multi-term case: \<open>last\<close> and \<open>butlast\<close>.\<close>

lemma poper_last_P_multi:
  assumes "multiT M" "1 < Lng M"
  shows "last (P M) = drop (Pcut M) M \<and> butlast (P M) = P (take (Pcut M) M)"
proof -
  have "P M = P (take (Pcut M) M) @ [drop (Pcut M) M]"
    using assms by (intro poper_P_multi) simp
  thus ?thesis by simp
qed

text \<open>Entry-shift under left truncation \<open>drop c\<close>.\<close>

lemma poper_entry_drop:
  assumes "k < Lng M - c"
  shows "entry (drop c M) i k = entry M i (c + k)"
  using assms by (simp add: entry_def nth_drop add.commute)

text \<open>\<open>nextrel0\<close> commutes with left truncation on indices below the length.\<close>

lemma poper_nextrel0_drop:
  assumes "a < Lng M - c" "b < Lng M - c"
  shows "nextrel0 (drop c M) a b \<longleftrightarrow> nextrel0 M (c + a) (c + b)"
proof -
  have lenD: "Lng (drop c M) = Lng M - c" by simp
  show ?thesis
    unfolding nextrel0_def lenD
  proof (intro iffI)
    assume H: "a < Lng M - c \<and> b < Lng M - c \<and> a < b \<and>
      entry (drop c M) 0 a < entry (drop c M) 0 b \<and>
      (\<forall>j. a < j \<and> j < b \<longrightarrow> entry (drop c M) 0 j \<ge> entry (drop c M) 0 b)"
    have "c + a < Lng M" "c + b < Lng M" using assms by auto
    moreover have "c + a < c + b" using H by simp
    moreover have "entry M 0 (c + a) < entry M 0 (c + b)"
      using H assms by (simp add: poper_entry_drop)
    moreover have "\<forall>j. c + a < j \<and> j < c + b \<longrightarrow> entry M 0 j \<ge> entry M 0 (c + b)"
    proof (intro allI impI)
      fix j assume aj: "c + a < j \<and> j < c + b"
      hence "a < j - c \<and> j - c < b" by auto
      moreover have "j - c < Lng M - c" using aj assms by auto
      ultimately have "entry (drop c M) 0 (j - c) \<ge> entry (drop c M) 0 b" using H by blast
      moreover have "entry (drop c M) 0 (j - c) = entry M 0 j"
        using \<open>j - c < Lng M - c\<close> aj by (simp add: poper_entry_drop)
      moreover have "entry (drop c M) 0 b = entry M 0 (c + b)"
        using assms by (simp add: poper_entry_drop)
      ultimately show "entry M 0 j \<ge> entry M 0 (c + b)" by simp
    qed
    ultimately show "c + a < Lng M \<and> c + b < Lng M \<and> c + a < c + b \<and>
      entry M 0 (c + a) < entry M 0 (c + b) \<and>
      (\<forall>j. c + a < j \<and> j < c + b \<longrightarrow> entry M 0 j \<ge> entry M 0 (c + b))" by blast
  next
    assume H: "c + a < Lng M \<and> c + b < Lng M \<and> c + a < c + b \<and>
      entry M 0 (c + a) < entry M 0 (c + b) \<and>
      (\<forall>j. c + a < j \<and> j < c + b \<longrightarrow> entry M 0 j \<ge> entry M 0 (c + b))"
    have "entry (drop c M) 0 a < entry (drop c M) 0 b"
      using H assms by (simp add: poper_entry_drop)
    moreover have "\<forall>j. a < j \<and> j < b \<longrightarrow> entry (drop c M) 0 j \<ge> entry (drop c M) 0 b"
    proof (intro allI impI)
      fix j assume aj: "a < j \<and> j < b"
      hence "c + a < c + j \<and> c + j < c + b" by simp
      hence "entry M 0 (c + j) \<ge> entry M 0 (c + b)" using H by blast
      moreover have "j < Lng M - c" using aj assms by auto
      ultimately show "entry (drop c M) 0 j \<ge> entry (drop c M) 0 b"
        using assms by (simp add: poper_entry_drop)
    qed
    ultimately show "a < Lng M - c \<and> b < Lng M - c \<and> a < b \<and>
      entry (drop c M) 0 a < entry (drop c M) 0 b \<and>
      (\<forall>j. a < j \<and> j < b \<longrightarrow> entry (drop c M) 0 j \<ge> entry (drop c M) 0 b)"
      using assms H by simp
  qed
qed


text \<open>\<open>le0\<close> commutes with left truncation.\<close>

lemma poper_le0_drop_fwd:
  assumes "(nextrel0 (drop c M))\<^sup>*\<^sup>* a b"
  shows "(nextrel0 M)\<^sup>*\<^sup>* (c + a) (c + b)"
  using assms
proof (induction rule: rtranclp_induct)
  case base show ?case by simp
next
  case (step y z)
  have yzlt: "y < Lng M - c" "z < Lng M - c"
    using step.hyps(2) by (auto simp: nextrel0_def)
  have "nextrel0 M (c + y) (c + z)"
    using step.hyps(2) poper_nextrel0_drop[OF yzlt] by simp
  with step.IH show ?case by (rule rtranclp.rtrancl_into_rtrancl)
qed

lemma poper_le0_drop_bwd:
  assumes "(nextrel0 M)\<^sup>*\<^sup>* x z" "c \<le> x" "z < Lng M"
  shows "(nextrel0 (drop c M))\<^sup>*\<^sup>* (x - c) (z - c)"
  using assms
proof (induction rule: rtranclp_induct)
  case base show ?case by simp
next
  case (step y w)
  have yw: "y < w" "w < Lng M" using step.hyps(2) by (auto simp: nextrel0_def)
  have xy: "x \<le> y" using step.hyps(1) nextrel0_rtrancl_mono by blast
  have cy: "c \<le> y" using step.prems(1) xy by simp
  have IH: "(nextrel0 (drop c M))\<^sup>*\<^sup>* (x - c) (y - c)"
    using step.IH step.prems(1) yw(1) yw(2) by simp
  have ylt: "y - c < Lng M - c" using yw(1) yw(2) cy by simp
  have wlt: "w - c < Lng M - c" using yw(2) cy yw(1) by simp
  have "nextrel0 M (c + (y - c)) (c + (w - c)) = nextrel0 (drop c M) (y - c) (w - c)"
    using poper_nextrel0_drop[OF ylt wlt] by simp
  moreover have "c + (y - c) = y" "c + (w - c) = w" using cy yw(1) by auto
  ultimately have "nextrel0 (drop c M) (y - c) (w - c)" using step.hyps(2) by simp
  with IH show ?case by (rule rtranclp.rtrancl_into_rtrancl)
qed

lemma poper_le0_drop:
  assumes "a < Lng M - c" "b < Lng M - c"
  shows "le0 (drop c M) a b \<longleftrightarrow> le0 M (c + a) (c + b)"
proof -
  have bnd: "c + a < Lng M" "c + b < Lng M" using assms by linarith+
  show ?thesis
proof
  assume "le0 (drop c M) a b"
  hence "(nextrel0 (drop c M))\<^sup>*\<^sup>* a b" by (simp add: le0_def)
  hence "(nextrel0 M)\<^sup>*\<^sup>* (c + a) (c + b)" by (rule poper_le0_drop_fwd)
  thus "le0 M (c + a) (c + b)" using bnd by (simp add: le0_def)
next
  assume "le0 M (c + a) (c + b)"
  hence r: "(nextrel0 M)\<^sup>*\<^sup>* (c + a) (c + b)" by (simp add: le0_def)
  have "(nextrel0 (drop c M))\<^sup>*\<^sup>* (c + a - c) (c + b - c)"
    using poper_le0_drop_bwd[where c = c, OF r] bnd by simp
  thus "le0 (drop c M) a b" using assms by (simp add: le0_def)
qed
qed

text \<open>\<open>nextrel1\<close> commutes with left truncation (uses \<open>le0\<close>-shift).\<close>

lemma poper_nextrel1_drop:
  assumes "a < Lng M - c" "b < Lng M - c"
  shows "nextrel1 (drop c M) a b \<longleftrightarrow> nextrel1 M (c + a) (c + b)"
proof -
  have lenD: "Lng (drop c M) = Lng M - c" by simp
  show ?thesis
    unfolding nextrel1_def lenD
  proof (intro iffI)
    assume H: "a < Lng M - c \<and> b < Lng M - c \<and> a < b \<and>
      entry (drop c M) 1 a < entry (drop c M) 1 b \<and> le0 (drop c M) a b \<and>
      (\<forall>j. a < j \<and> le0 (drop c M) j b \<longrightarrow> entry (drop c M) 1 j \<ge> entry (drop c M) 1 b)"
    have e: "entry M 1 (c + a) < entry M 1 (c + b)"
      using H assms by (simp add: poper_entry_drop)
    have l: "le0 M (c + a) (c + b)" using H poper_le0_drop[OF assms] by simp
    have univ: "\<forall>j. c + a < j \<and> le0 M j (c + b) \<longrightarrow> entry M 1 j \<ge> entry M 1 (c + b)"
    proof (intro allI impI)
      fix j assume aj: "c + a < j \<and> le0 M j (c + b)"
      have jlt: "j < Lng M" using aj by (auto simp: le0_def)
      have cj: "c \<le> j" using aj by linarith
      have jdlt: "j - c < Lng M - c" using jlt cj aj by linarith
      have "le0 (drop c M) (j - c) b"
      proof -
        have "le0 M (c + (j - c)) (c + b)" using aj cj by simp
        thus ?thesis using poper_le0_drop[OF jdlt assms(2)] by simp
      qed
      moreover have "a < j - c" using aj cj by linarith
      ultimately have "entry (drop c M) 1 (j - c) \<ge> entry (drop c M) 1 b" using H by blast
      moreover have "entry (drop c M) 1 (j - c) = entry M 1 j"
        using jdlt cj by (simp add: poper_entry_drop)
      moreover have "entry (drop c M) 1 b = entry M 1 (c + b)"
        using assms by (simp add: poper_entry_drop)
      ultimately show "entry M 1 j \<ge> entry M 1 (c + b)" by simp
    qed
    show "c + a < Lng M \<and> c + b < Lng M \<and> c + a < c + b \<and>
      entry M 1 (c + a) < entry M 1 (c + b) \<and> le0 M (c + a) (c + b) \<and>
      (\<forall>j. c + a < j \<and> le0 M j (c + b) \<longrightarrow> entry M 1 j \<ge> entry M 1 (c + b))"
      using assms H e l univ by auto
  next
    assume H: "c + a < Lng M \<and> c + b < Lng M \<and> c + a < c + b \<and>
      entry M 1 (c + a) < entry M 1 (c + b) \<and> le0 M (c + a) (c + b) \<and>
      (\<forall>j. c + a < j \<and> le0 M j (c + b) \<longrightarrow> entry M 1 j \<ge> entry M 1 (c + b))"
    have e: "entry (drop c M) 1 a < entry (drop c M) 1 b"
      using H assms by (simp add: poper_entry_drop)
    have l: "le0 (drop c M) a b" using H poper_le0_drop[OF assms] by simp
    have univ: "\<forall>j. a < j \<and> le0 (drop c M) j b \<longrightarrow> entry (drop c M) 1 j \<ge> entry (drop c M) 1 b"
    proof (intro allI impI)
      fix j assume aj: "a < j \<and> le0 (drop c M) j b"
      have jlt: "j < Lng M - c" using aj by (auto simp: le0_def)
      have "le0 M (c + j) (c + b)" using aj poper_le0_drop[OF _ assms(2)] jlt by simp
      moreover have "c + a < c + j" using aj by simp
      ultimately have "entry M 1 (c + j) \<ge> entry M 1 (c + b)" using H by blast
      moreover have "entry (drop c M) 1 j = entry M 1 (c + j)"
        using jlt by (simp add: poper_entry_drop)
      moreover have "entry (drop c M) 1 b = entry M 1 (c + b)"
        using assms by (simp add: poper_entry_drop)
      ultimately show "entry (drop c M) 1 j \<ge> entry (drop c M) 1 b" by simp
    qed
    show "a < Lng M - c \<and> b < Lng M - c \<and> a < b \<and>
      entry (drop c M) 1 a < entry (drop c M) 1 b \<and> le0 (drop c M) a b \<and>
      (\<forall>j. a < j \<and> le0 (drop c M) j b \<longrightarrow> entry (drop c M) 1 j \<ge> entry (drop c M) 1 b)"
      using assms H e l univ by auto
  qed
qed

lemma poper_le1_drop_fwd:
  assumes "(nextrel1 (drop c M))\<^sup>*\<^sup>* a b"
  shows "(nextrel1 M)\<^sup>*\<^sup>* (c + a) (c + b)"
  using assms
proof (induction rule: rtranclp_induct)
  case base show ?case by simp
next
  case (step y z)
  have yzlt: "y < Lng M - c" "z < Lng M - c"
    using step.hyps(2) by (auto simp: nextrel1_def)
  have "nextrel1 M (c + y) (c + z)"
    using step.hyps(2) poper_nextrel1_drop[OF yzlt] by simp
  with step.IH show ?case by (rule rtranclp.rtrancl_into_rtrancl)
qed

lemma poper_le1_drop_bwd:
  assumes "(nextrel1 M)\<^sup>*\<^sup>* x z" "c \<le> x" "z < Lng M"
  shows "(nextrel1 (drop c M))\<^sup>*\<^sup>* (x - c) (z - c)"
  using assms
proof (induction rule: rtranclp_induct)
  case base show ?case by simp
next
  case (step y w)
  have yw: "y < w" "w < Lng M" using step.hyps(2) by (auto simp: nextrel1_def)
  have xy: "x \<le> y" using step.hyps(1) nextrel1_rtrancl_mono by blast
  have cy: "c \<le> y" using step.prems(1) xy by simp
  have IH: "(nextrel1 (drop c M))\<^sup>*\<^sup>* (x - c) (y - c)"
    using step.IH step.prems(1) yw(1) yw(2) by simp
  have ylt: "y - c < Lng M - c" using yw(1) yw(2) cy by simp
  have wlt: "w - c < Lng M - c" using yw(2) cy yw(1) by simp
  have "nextrel1 M (c + (y - c)) (c + (w - c)) = nextrel1 (drop c M) (y - c) (w - c)"
    using poper_nextrel1_drop[OF ylt wlt] by simp
  moreover have "c + (y - c) = y" "c + (w - c) = w" using cy yw(1) by auto
  ultimately have "nextrel1 (drop c M) (y - c) (w - c)" using step.hyps(2) by simp
  with IH show ?case by (rule rtranclp.rtrancl_into_rtrancl)
qed

lemma poper_le1_drop:
  assumes "a < Lng M - c" "b < Lng M - c"
  shows "le1 (drop c M) a b \<longleftrightarrow> le1 M (c + a) (c + b)"
proof -
  have bnd: "c + a < Lng M" "c + b < Lng M" using assms by linarith+
  show ?thesis
proof
  assume "le1 (drop c M) a b"
  hence "(nextrel1 (drop c M))\<^sup>*\<^sup>* a b" by (simp add: le1_def)
  hence "(nextrel1 M)\<^sup>*\<^sup>* (c + a) (c + b)" by (rule poper_le1_drop_fwd)
  thus "le1 M (c + a) (c + b)" using bnd by (simp add: le1_def)
next
  assume "le1 M (c + a) (c + b)"
  hence r: "(nextrel1 M)\<^sup>*\<^sup>* (c + a) (c + b)" by (simp add: le1_def)
  have "(nextrel1 (drop c M))\<^sup>*\<^sup>* (c + a - c) (c + b - c)"
    using poper_le1_drop_bwd[where c = c, OF r] bnd by simp
  thus "le1 (drop c M) a b" using assms by (simp add: le1_def)
qed
qed

text \<open>\<open>nextR\<close> / \<open>leR\<close> commute with left truncation.\<close>

lemma poper_nextR_drop:
  assumes "a < Lng M - c" "b < Lng M - c"
  shows "nextR (drop c M) i a b \<longleftrightarrow> nextR M i (c + a) (c + b)"
  unfolding nextR_def
  using poper_nextrel0_drop[OF assms] poper_nextrel1_drop[OF assms] by simp

lemma poper_leR_drop:
  assumes "a < Lng M - c" "b < Lng M - c"
  shows "leR (drop c M) i a b \<longleftrightarrow> leR M i (c + a) (c + b)"
  unfolding leR_def
  using poper_le0_drop[OF assms] poper_le1_drop[OF assms] by simp

text \<open>A \<open>nextR\<close>-parent gives row-0 ancestry and \<open>j0 < j1\<close>.\<close>

lemma poper_nextR_imp_le0:
  assumes "nextR M i j0 j1"
  shows "j0 < j1 \<and> leR M 0 j0 j1"
proof (cases "i = 0")
  case True
  hence "nextrel0 M j0 j1" using assms by (simp add: nextR_def)
  hence "j0 < j1" "j0 < Lng M" "j1 < Lng M" "(nextrel0 M)\<^sup>*\<^sup>* j0 j1"
    by (auto simp: nextrel0_def)
  thus ?thesis by (simp add: leR_def le0_def)
next
  case False
  hence "nextrel1 M j0 j1" using assms by (simp add: nextR_def)
  hence "j0 < j1" "le0 M j0 j1" by (auto simp: nextrel1_def)
  thus ?thesis by (simp add: leR_def)
qed

text \<open>
  Under the §6.2 cut hypotheses (\<open>M\<close> multi, \<open>c = Pcut M\<close> a row-0 ancestor of the
  last index), every \<open>nextR\<close>-parent of the last index lies at or beyond \<open>c\<close>.
\<close>

lemma poper_parent_ge_c:
  assumes M: "M \<in> T_PS" and multi: "multiT M" and L: "1 < Lng M"
    and par: "nextR M i j0 (Lng M - 1)"
  shows "Pcut M \<le> j0"
proof (rule ccontr)
  assume "\<not> Pcut M \<le> j0"
  hence j0c: "j0 < Pcut M" by simp
  from poper_nextR_imp_le0[OF par] have lej0: "leR M 0 j0 (Lng M - 1)" by simp
  show False
  proof (cases "j0 = 0")
    case True
    hence "leR M 0 0 (Lng M - 1)" using lej0 by simp
    hence "\<not> multiT M" using m_6_2_not_multi_iff_le[OF M] by simp
    thus False using multi by simp
  next
    case False
    hence j00: "0 < j0" by simp
    have j0j1: "j0 \<le> Lng M - 1"
      using poper_nextR_imp_le0[OF par] L by linarith
    have "Pcut M \<le> j0" unfolding Pcut_def
      by (rule Least_le[where P = "\<lambda>j. 0 < j \<and> j \<le> Lng M - 1 \<and> leR M 0 j (Lng M - 1)"])
         (use j00 j0j1 lej0 in auto)
    thus False using j0c by simp
  qed
qed


text \<open>
  Correspondence of \<open>nextR\<close>-parents of the last index between \<open>M\<close> and its
  left-truncation \<open>drop c M\<close>, where \<open>c = Pcut M\<close>.  Every parent is \<open>\<ge> c\<close>, so
  the two parent-sets are in bijection via \<open>j0 \<mapsto> j0 - c\<close>.
\<close>

lemma poper_parent_set_drop:
  assumes M: "M \<in> T_PS" and multi: "multiT M" and L: "1 < Lng M"
    and cdef: "c = Pcut M" and clt: "c < Lng M - 1"
  shows "nextR M i j0 (Lng M - 1)
         \<longleftrightarrow> (c \<le> j0 \<and> nextR (drop c M) i (j0 - c) (Lng (drop c M) - 1))"
proof
  let ?j1 = "Lng M - 1"
  let ?j1' = "Lng (drop c M) - 1"
  have lenD: "Lng (drop c M) = Lng M - c" by simp
  have j1'eq: "?j1' = ?j1 - c" using lenD by simp
  assume par: "nextR M i j0 ?j1"
  have cj0: "c \<le> j0" using poper_parent_ge_c[OF M multi L par] cdef by simp
  have j0lt: "j0 < ?j1" using poper_nextR_imp_le0[OF par] by simp
  have a1: "j0 - c < Lng M - c" using cj0 j0lt clt by linarith
  have a2: "?j1 - c < Lng M - c" using clt by linarith
  have "nextR (drop c M) i (j0 - c) (?j1 - c) = nextR M i (c + (j0 - c)) (c + (?j1 - c))"
    by (rule poper_nextR_drop[OF a1 a2])
  moreover have "c + (j0 - c) = j0" using cj0 by simp
  moreover have "c + (?j1 - c) = ?j1" using clt by simp
  ultimately have "nextR (drop c M) i (j0 - c) (?j1 - c)" using par by simp
  thus "c \<le> j0 \<and> nextR (drop c M) i (j0 - c) ?j1'" using cj0 j1'eq by simp
next
  let ?j1 = "Lng M - 1"
  let ?j1' = "Lng (drop c M) - 1"
  have lenD: "Lng (drop c M) = Lng M - c" by simp
  assume H: "c \<le> j0 \<and> nextR (drop c M) i (j0 - c) ?j1'"
  hence cj0: "c \<le> j0" and par': "nextR (drop c M) i (j0 - c) (?j1 - c)"
    using lenD by auto
  have j0'lt: "j0 - c < ?j1 - c"
    using poper_nextR_imp_le0[OF par'] lenD by simp
  have a1: "j0 - c < Lng M - c" using j0'lt clt by linarith
  have a2: "?j1 - c < Lng M - c" using clt by linarith
  have "nextR (drop c M) i (j0 - c) (?j1 - c) = nextR M i (c + (j0 - c)) (c + (?j1 - c))"
    by (rule poper_nextR_drop[OF a1 a2])
  moreover have "c + (j0 - c) = j0" using cj0 by simp
  moreover have "c + (?j1 - c) = ?j1" using clt by simp
  ultimately show "nextR M i j0 ?j1" using par' by simp
qed

lemma poper_hasParent_drop:
  assumes M: "M \<in> T_PS" and multi: "multiT M" and L: "1 < Lng M"
    and cdef: "c = Pcut M" and clt: "c < Lng M - 1"
  shows "hasParent M i (Lng M - 1) \<longleftrightarrow> hasParent (drop c M) i (Lng (drop c M) - 1)"
proof -
  let ?j1 = "Lng M - 1"
  let ?j1' = "Lng (drop c M) - 1"
  have corr: "\<And>j0. nextR M i j0 ?j1
        \<longleftrightarrow> (c \<le> j0 \<and> nextR (drop c M) i (j0 - c) ?j1')"
    using poper_parent_set_drop[OF M multi L cdef clt] by blast
  show ?thesis unfolding hasParent_def
  proof
    assume "\<exists>!j0. nextR M i j0 ?j1"
    then obtain j0 where j0: "nextR M i j0 ?j1"
      and uniq: "\<And>y. nextR M i y ?j1 \<Longrightarrow> y = j0" by auto
    have cj0: "c \<le> j0" using corr j0 by blast
    have par': "nextR (drop c M) i (j0 - c) ?j1'" using corr j0 by blast
    have "\<And>y. nextR (drop c M) i y ?j1' \<Longrightarrow> y = j0 - c"
    proof -
      fix y assume y: "nextR (drop c M) i y ?j1'"
      have "nextR M i (c + y) ?j1" using corr[of "c + y"] y by simp
      hence "c + y = j0" using uniq by simp
      thus "y = j0 - c" by simp
    qed
    with par' show "\<exists>!j0. nextR (drop c M) i j0 ?j1'" by blast
  next
    assume "\<exists>!j0. nextR (drop c M) i j0 ?j1'"
    then obtain a where a: "nextR (drop c M) i a ?j1'"
      and uniq: "\<And>y. nextR (drop c M) i y ?j1' \<Longrightarrow> y = a" by auto
    have parM: "nextR M i (c + a) ?j1" using corr[of "c + a"] a by simp
    have "\<And>y. nextR M i y ?j1 \<Longrightarrow> y = c + a"
    proof -
      fix y assume y: "nextR M i y ?j1"
      hence cy: "c \<le> y" and par': "nextR (drop c M) i (y - c) ?j1'" using corr by blast+
      hence "y - c = a" using uniq by simp
      thus "y = c + a" using cy by simp
    qed
    with parM show "\<exists>!j0. nextR M i j0 ?j1" by blast
  qed
qed

lemma poper_parent_drop:
  assumes M: "M \<in> T_PS" and multi: "multiT M" and L: "1 < Lng M"
    and cdef: "c = Pcut M" and clt: "c < Lng M - 1"
    and has: "hasParent M i (Lng M - 1)"
  shows "parent M i (Lng M - 1) = c + parent (drop c M) i (Lng (drop c M) - 1)"
proof -
  let ?j1 = "Lng M - 1"
  let ?j1' = "Lng (drop c M) - 1"
  from has obtain j0 where j0: "nextR M i j0 ?j1"
    and uniq: "\<And>y. nextR M i y ?j1 \<Longrightarrow> y = j0"
    unfolding hasParent_def by auto
  have parM: "parent M i ?j1 = j0" unfolding parent_def using j0 uniq by (rule the_equality)
  have corr: "\<And>j0. nextR M i j0 ?j1
        \<longleftrightarrow> (c \<le> j0 \<and> nextR (drop c M) i (j0 - c) ?j1')"
    using poper_parent_set_drop[OF M multi L cdef clt] by blast
  have cj0: "c \<le> j0" using corr j0 by blast
  have par': "nextR (drop c M) i (j0 - c) ?j1'" using corr j0 by blast
  have uniq': "\<And>y. nextR (drop c M) i y ?j1' \<Longrightarrow> y = j0 - c"
  proof -
    fix y assume y: "nextR (drop c M) i y ?j1'"
    have "nextR M i (c + y) ?j1" using corr[of "c + y"] y by simp
    hence "c + y = j0" using uniq by simp
    thus "y = j0 - c" by simp
  qed
  have parM': "parent (drop c M) i ?j1' = j0 - c"
    unfolding parent_def using par' uniq' by (rule the_equality)
  show ?thesis using parM parM' cj0 by simp
qed


text \<open>Unfolding of \<open>M[n]\<close> in the non-degenerate (expansion) branch.\<close>

lemma poper_oper_expand:
  assumes "Lng M > 1"
    and nzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
  shows "M[n] =
     (let j1 = Lng M - 1; i1 = idx1 M j1; j0 = parent M i1 j1;
          d0 = (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0);
          d1 = (if 1 < i1 then entry M 1 j1 - entry M 1 j0 else 0)
      in take j0 M @
         concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * d0, entry M 1 j + k * d1))
                               [j0..<j1]) [0..<n]))"
proof -
  have nz: "(Lng M - 1 = 0) = False" using assms(1) by simp
  have c2: "(entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0) = False"
    using nzero by simp
  have c3: "(\<not> hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)) = False"
    using hp by simp
  show ?thesis
    unfolding oper_def Let_def
    by (simp only: nz c2 c3 if_False if_True)
qed

text \<open>The fundamental sequence preserves length-1 nonemptiness and the head pair.\<close>

lemma poper_oper_nth0:
  assumes M: "M \<in> T_PS" and L: "1 < Lng M" and n: "n \<ge> 1"
  shows "(M[n]) \<noteq> [] \<and> (M[n]) ! 0 = M ! 0"
proof -
  let ?j1 = "Lng M - 1"
  have nz: "?j1 \<noteq> 0" using L by simp
  have Pred0: "Pred M \<noteq> [] \<and> Pred M ! 0 = M ! 0"
  proof -
    have "Pred M = butlast M" using L by (simp add: Pred_def)
    moreover have "butlast M \<noteq> []" using L by (cases M) auto
    moreover have "butlast M ! 0 = M ! 0" using L by (simp add: nth_butlast)
    ultimately show ?thesis by simp
  qed
  show ?thesis
  proof (cases "entry M 0 ?j1 = 0 \<and> entry M 1 ?j1 = 0")
    case True
    hence "M[n] = Pred M" using nz by (simp add: oper_def Let_def)
    thus ?thesis using Pred0 by simp
  next
    case notzero: False
    show ?thesis
    proof (cases "hasParent M (idx1 M ?j1) ?j1")
      case False
      hence "M[n] = Pred M" using notzero nz by (simp add: oper_def Let_def)
      thus ?thesis using Pred0 by simp
    next
      case haspar: True
      let ?i1 = "idx1 M ?j1"
      let ?j0 = "parent M ?i1 ?j1"
      let ?d0 = "if 0 < ?i1 then entry M 0 ?j1 - entry M 0 ?j0 else 0"
      let ?d1 = "if 1 < ?i1 then entry M 1 ?j1 - entry M 1 ?j0 else 0"
      have parR: "nextR M ?i1 ?j0 ?j1"
        using haspar unfolding hasParent_def parent_def by (rule theI')
      have j0lt: "?j0 < ?j1" using poper_nextR_imp_le0[OF parR] by simp
      have oper: "M[n] = take ?j0 M @
          concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * ?d0, entry M 1 j + k * ?d1))
                                [?j0..<?j1]) [0..<n])"
        using poper_oper_expand[OF L notzero haspar, of n] by (simp add: Let_def)
      show ?thesis
      proof (cases "0 < ?j0")
        case True
        have ne: "take ?j0 M \<noteq> []" using True j0lt L by (cases M) auto
        have h: "(take ?j0 M) ! 0 = M ! 0" using True by (simp add: nth_take)
        show ?thesis using oper ne h by (simp add: nth_append)
      next
        case False
        hence j00: "?j0 = 0" by simp
        have n0: "0 < n" using n by simp
        have blk: "concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * ?d0, entry M 1 j + k * ?d1))
                                [0..<?j1]) [0..<n])
              = map (\<lambda>j. (entry M 0 j, entry M 1 j)) [0..<?j1] @
                concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * ?d0, entry M 1 j + k * ?d1))
                                [0..<?j1]) [1..<n])"
          using n0 by (subst upt_conv_Cons) auto
        have first_ne: "map (\<lambda>j. (entry M 0 j, entry M 1 j)) [0..<?j1] \<noteq> []"
          using nz by simp
        have first0: "map (\<lambda>j. (entry M 0 j, entry M 1 j)) [0..<?j1] ! 0 = M ! 0"
          using nz entry_pair[of M 0] by (simp add: nth_upt)
        from oper j00 have "M[n] = map (\<lambda>j. (entry M 0 j, entry M 1 j)) [0..<?j1] @
                concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * ?d0, entry M 1 j + k * ?d1))
                                [0..<?j1]) [1..<n])"
          using blk by simp
        thus ?thesis using first_ne first0 by (simp add: nth_append)
      qed
    qed
  qed
qed

text \<open>\<open>Pred\<close> splits along a left-truncation strictly inside \<open>M\<close>.\<close>

lemma poper_take_append_take_drop:
  assumes "c + k \<le> Lng M"
  shows "take c M @ take k (drop c M) = take (c + k) M"
  using assms by (metis take_add)

lemma poper_Pred_split:
  assumes "c < Lng M - 1" "1 < Lng M"
  shows "Pred M = take c M @ Pred (drop c M)"
proof -
  have lenD: "Lng (drop c M) = Lng M - c" by simp
  have LD: "1 < Lng (drop c M)" using assms by simp
  have "Pred (drop c M) = take (Lng M - c - 1) (drop c M)"
    using LD lenD by (simp add: Pred_def butlast_conv_take)
  hence "take c M @ Pred (drop c M) = take c M @ take (Lng M - c - 1) (drop c M)" by simp
  also have "\<dots> = take (c + (Lng M - c - 1)) M"
    using assms by (intro poper_take_append_take_drop) linarith
  also have "c + (Lng M - c - 1) = Lng M - 1" using assms by linarith
  also have "take (Lng M - 1) M = Pred M"
    using assms by (simp add: Pred_def butlast_conv_take)
  finally show ?thesis by simp
qed

text \<open>
  m: the fundamental sequence commutes with the left-truncation at \<open>Pcut M\<close>
  when the last \<open>P\<close>-component is non-trivial (\<open>Pcut M < Lng M - 1\<close>).
\<close>

lemma poper_oper_drop:
  assumes M: "M \<in> T_PS" and multi: "multiT M" and L: "1 < Lng M"
    and cdef: "c = Pcut M" and clt: "c < Lng M - 1"
  shows "M[n] = take c M @ (drop c M)[n]"
proof -
  let ?j1 = "Lng M - 1"
  let ?M' = "drop c M"
  let ?j1' = "Lng ?M' - 1"
  have lenD: "Lng ?M' = Lng M - c" by simp
  have j1'eq: "?j1' = ?j1 - c" using lenD by simp
  have c0: "0 < c" using cdef Pcut_le[OF L] by simp
  have cL: "c < Lng M" using clt by linarith
  have LD: "1 < Lng ?M'" using clt lenD by linarith
  have j1pos: "?j1 \<noteq> 0" using L by simp
  have j1'pos: "?j1' \<noteq> 0" using LD by simp
  \<comment> \<open>entries at the last index agree\<close>
  have ej1L: "?j1' < Lng ?M'" using LD by simp
  have e0: "entry ?M' 0 ?j1' = entry M 0 ?j1"
    using ej1L j1'eq clt by (simp add: poper_entry_drop)
  have e1: "entry ?M' 1 ?j1' = entry M 1 ?j1"
    using ej1L j1'eq clt by (simp add: poper_entry_drop)
  have idx_eq: "idx1 ?M' ?j1' = idx1 M ?j1" by (simp only: idx1_def e1)
  show ?thesis
  proof (cases "entry M 0 ?j1 = 0 \<and> entry M 1 ?j1 = 0")
    case zero: True
    have "M[n] = Pred M" using zero j1pos by (simp add: oper_def Let_def)
    moreover have "?M'[n] = Pred ?M'"
      using zero e0 e1 j1'pos by (simp add: oper_def Let_def)
    moreover have "Pred M = take c M @ Pred ?M'"
      by (rule poper_Pred_split[OF clt L])
    ultimately show ?thesis by simp
  next
    case notzero: False
    let ?i1 = "idx1 M ?j1"
    show ?thesis
    proof (cases "hasParent M ?i1 ?j1")
      case noparent: False
      have hp': "\<not> hasParent ?M' (idx1 ?M' ?j1') ?j1'"
        using noparent poper_hasParent_drop[OF M multi L cdef clt] idx_eq by simp
      have "M[n] = Pred M"
        using notzero noparent j1pos by (simp add: oper_def Let_def)
      moreover have "?M'[n] = Pred ?M'"
        using notzero e0 e1 hp' j1'pos by (simp add: oper_def Let_def)
      moreover have "Pred M = take c M @ Pred ?M'"
        by (rule poper_Pred_split[OF clt L])
      ultimately show ?thesis by simp
    next
      case haspar: True
      have hp': "hasParent ?M' (idx1 ?M' ?j1') ?j1'"
        using haspar poper_hasParent_drop[OF M multi L cdef clt] idx_eq by simp
      let ?j0 = "parent M ?i1 ?j1"
      let ?j0' = "parent ?M' (idx1 ?M' ?j1') ?j1'"
      have par_eq: "?j0 = c + ?j0'"
        using poper_parent_drop[OF M multi L cdef clt haspar] idx_eq by simp
      \<comment> \<open>the parent is a genuine \<open>nextR\<close>-parent\<close>
      have parR: "nextR M ?i1 ?j0 ?j1"
        using haspar unfolding hasParent_def parent_def by (rule theI')
      have cj0: "c \<le> ?j0" using poper_parent_ge_c[OF M multi L parR] cdef by simp
      have j0lt: "?j0 < ?j1" using poper_nextR_imp_le0[OF parR] by simp
      have j0'lt: "?j0' < ?j1'" using par_eq cj0 j0lt clt j1'eq by linarith
      \<comment> \<open>increments agree\<close>
      let ?d0 = "if 0 < ?i1 then entry M 0 ?j1 - entry M 0 ?j0 else 0"
      let ?d1 = "if 1 < ?i1 then entry M 1 ?j1 - entry M 1 ?j0 else 0"
      let ?d0' = "if 0 < idx1 ?M' ?j1' then entry ?M' 0 ?j1' - entry ?M' 0 ?j0' else 0"
      let ?d1' = "if 1 < idx1 ?M' ?j1' then entry ?M' 1 ?j1' - entry ?M' 1 ?j0' else 0"
      have ej0lt: "?j0' < Lng ?M'" using j0'lt LD by linarith
      have e0j0: "entry ?M' 0 ?j0' = entry M 0 ?j0"
        using ej0lt par_eq lenD cj0 by (simp add: poper_entry_drop)
      have e1j0: "entry ?M' 1 ?j0' = entry M 1 ?j0"
        using ej0lt par_eq lenD cj0 by (simp add: poper_entry_drop)
      have d0_eq: "?d0' = ?d0" using idx_eq e0 e0j0 by simp
      have d1_eq: "?d1' = ?d1" using idx_eq e1 e1j0 by simp
      \<comment> \<open>operator unfolds (non-degenerate branch)\<close>
      have operM: "M[n] = take ?j0 M @
          concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * ?d0, entry M 1 j + k * ?d1))
                                [?j0..<?j1]) [0..<n])"
        using poper_oper_expand[OF L notzero haspar, of n] by (simp add: Let_def)
      have nzero': "\<not> (entry ?M' 0 ?j1' = 0 \<and> entry ?M' 1 ?j1' = 0)"
        using notzero e0 e1 by simp
      have hp'': "hasParent ?M' (idx1 ?M' ?j1') ?j1'" using hp' .
      have operM': "?M'[n] = take ?j0' ?M' @
          concat (map (\<lambda>k. map (\<lambda>j. (entry ?M' 0 j + k * ?d0', entry ?M' 1 j + k * ?d1'))
                                [?j0'..<?j1']) [0..<n])"
        using poper_oper_expand[OF LD nzero' hp'', of n] by (simp add: Let_def)
      \<comment> \<open>prefix splits\<close>
      have take_split: "take ?j0 M = take c M @ take ?j0' ?M'"
        using par_eq cj0 cL j0lt L
        by (simp add: poper_take_append_take_drop par_eq)
      \<comment> \<open>blocks agree via reindexing \<open>j = c + j'\<close>\<close>
      have block_eq: "\<And>k. map (\<lambda>j. (entry M 0 j + k * ?d0, entry M 1 j + k * ?d1)) [?j0..<?j1]
            = map (\<lambda>j. (entry ?M' 0 j + k * ?d0', entry ?M' 1 j + k * ?d1')) [?j0'..<?j1']"
      proof -
        fix k
        have "[?j0..<?j1] = map (\<lambda>j'. c + j') [?j0'..<?j1']"
        proof (rule nth_equalityI)
          show "length [?j0..<?j1] = length (map (\<lambda>j'. c + j') [?j0'..<?j1'])"
            using par_eq j1'eq cj0 clt by simp
        next
          fix i assume "i < length [?j0..<?j1]"
          hence ilt: "i < ?j1 - ?j0" by simp
          have ilt': "i < ?j1' - ?j0'" using ilt par_eq j1'eq cj0 clt by linarith
          have "[?j0..<?j1] ! i = ?j0 + i" using ilt by (simp add: nth_upt)
          moreover have "map (\<lambda>j'. c + j') [?j0'..<?j1'] ! i = c + (?j0' + i)"
            using ilt' by (simp add: nth_upt)
          ultimately show "[?j0..<?j1] ! i = map (\<lambda>j'. c + j') [?j0'..<?j1'] ! i"
            using par_eq by simp
        qed
        hence "map (\<lambda>j. (entry M 0 j + k * ?d0, entry M 1 j + k * ?d1)) [?j0..<?j1]
             = map ((\<lambda>j. (entry M 0 j + k * ?d0, entry M 1 j + k * ?d1)) \<circ> (\<lambda>j'. c + j'))
                   [?j0'..<?j1']"
          by simp
        also have "\<dots> = map (\<lambda>j'. (entry ?M' 0 j' + k * ?d0', entry ?M' 1 j' + k * ?d1'))
                            [?j0'..<?j1']"
        proof (rule map_cong[OF refl])
          fix j' assume "j' \<in> set [?j0'..<?j1']"
          hence j'rng: "?j0' \<le> j' \<and> j' < ?j1'" by simp
          hence j'L: "j' < Lng ?M'" using j1'eq LD by linarith
          have "entry M 0 (c + j') = entry ?M' 0 j'"
            using j'L lenD by (simp add: poper_entry_drop)
          moreover have "entry M 1 (c + j') = entry ?M' 1 j'"
            using j'L lenD by (simp add: poper_entry_drop)
          ultimately show "((\<lambda>j. (entry M 0 j + k * ?d0, entry M 1 j + k * ?d1)) \<circ>
                            (\<lambda>j'. c + j')) j'
                = (entry ?M' 0 j' + k * ?d0', entry ?M' 1 j' + k * ?d1')"
            using d0_eq d1_eq by simp
        qed
        finally show "map (\<lambda>j. (entry M 0 j + k * ?d0, entry M 1 j + k * ?d1)) [?j0..<?j1]
            = map (\<lambda>j. (entry ?M' 0 j + k * ?d0', entry ?M' 1 j + k * ?d1')) [?j0'..<?j1']" .
      qed
      have "M[n] = take c M @ (take ?j0' ?M' @
          concat (map (\<lambda>k. map (\<lambda>j. (entry ?M' 0 j + k * ?d0', entry ?M' 1 j + k * ?d1'))
                                [?j0'..<?j1']) [0..<n]))"
        using operM take_split block_eq by simp
      also have "\<dots> = take c M @ ?M'[n]" using operM' by simp
      finally show ?thesis .
    qed
  qed
qed


text \<open>
  Case (1): when the last \<open>P\<close>-component has length 1.  If \<open>P M\<close> is a singleton
  then \<open>Lng M = 1\<close> and the operator is the identity; otherwise \<open>M\<close> is multi with
  \<open>Pcut M = Lng M - 1\<close>, the last index has no \<open>nextR\<close>-parent, so \<open>M[n] = Pred M\<close>.
\<close>

lemma m_6_2_P_oper_1:
  assumes M: "M \<in> T_PS" and n: "n \<ge> 1" and last1: "Lng (last (P M)) = 1"
  shows "M[n] = Pred M
       \<and> (if length (P M) = 1 then P (M[n]) = [(M[n])] else P (M[n]) = butlast (P M))"
proof (cases "length (P M) = 1")
  case sing: True
  hence notmulti: "\<not> multiT M" using m_6_2_P_components_2[OF M] by (simp del: P.simps)
  have PM: "P M = [M]"
  proof (cases "multiT M \<and> 1 < Lng M")
    case True thus ?thesis using notmulti by simp
  next
    case False thus ?thesis by (rule poper_P_nonmulti)
  qed
  hence "last (P M) = M" by simp
  hence L1: "Lng M = 1" using last1 by simp
  have op: "M[n] = M" using L1 by (simp add: oper_def Let_def)
  have pred: "Pred M = M" using L1 by (simp add: Pred_def)
  have "P (M[n]) = [(M[n])]" using op PM by (simp del: P.simps)
  thus ?thesis using op pred sing by (simp del: P.simps)
next
  case notsing: False
  have multi: "multiT M"
  proof -
    have "length (P M) > 1" using notsing P_nonempty[of M] by (cases "P M") auto
    thus ?thesis using m_6_2_P_components_2[OF M] by (simp del: P.simps)
  qed
  have L: "1 < Lng M" using multiT_imp_Lng_gt1[OF M multi] .
  let ?c = "Pcut M"
  have lastP: "last (P M) = drop ?c M" and butP: "butlast (P M) = P (take ?c M)"
    using poper_last_P_multi[OF multi L] by auto
  from Pcut_le[OF L] have c0: "0 < ?c" and cj1: "?c \<le> Lng M - 1" by auto
  have cL: "?c < Lng M" using cj1 L by linarith
  have lenD: "Lng (drop ?c M) = Lng M - ?c" by simp
  \<comment> \<open>the last component has length 1, so the cut is at the very end\<close>
  have "Lng (drop ?c M) = 1" using last1 lastP by simp
  hence ceq: "?c = Lng M - 1" using lenD cj1 cL by linarith
  \<comment> \<open>no \<open>nextR\<close>-parent of the last index, hence \<open>M[n] = Pred M\<close>\<close>
  have noparent: "\<not> hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
  proof
    assume "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    then obtain j0 where j0: "nextR M (idx1 M (Lng M - 1)) j0 (Lng M - 1)"
      unfolding hasParent_def by auto
    have "?c \<le> j0" using poper_parent_ge_c[OF M multi L j0] .
    moreover have "j0 < Lng M - 1" using poper_nextR_imp_le0[OF j0] by simp
    ultimately show False using ceq by simp
  qed
  have nz: "Lng M - 1 \<noteq> 0" using L by simp
  have op: "M[n] = Pred M"
  proof (cases "entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0")
    case True thus ?thesis using nz by (simp add: oper_def Let_def)
  next
    case False thus ?thesis using noparent nz by (simp add: oper_def Let_def)
  qed
  \<comment> \<open>\<open>P(M[n]) = P(Pred M) = P(take ?c M) = butlast (P M)\<close>\<close>
  have predtake: "Pred M = take ?c M" using ceq L by (simp add: Pred_def butlast_conv_take)
  have "P (M[n]) = P (take ?c M)" using op predtake by simp
  also have "\<dots> = butlast (P M)" using butP by simp
  finally have "P (M[n]) = butlast (P M)" .
  thus ?thesis using op notsing by (simp del: P.simps)
qed


text \<open>
  Case (2): when the last \<open>P\<close>-component has length \<open>> 1\<close>.  Either \<open>P M\<close> is a
  singleton (then the statement is trivial), or \<open>M\<close> is multi and the expansion
  acts inside the last component \<open>drop (Pcut M) M\<close>; the result follows from
  @{thm [source] poper_oper_drop} and the additivity @{thm [source] m_6_2_P_additive}.
\<close>

lemma m_6_2_P_oper_2:
  assumes M: "M \<in> T_PS" and n: "n \<ge> 1" and lastgt: "Lng (last (P M)) > 1"
  shows "M[n] = concat (butlast (P M)) @ (last (P M))[n]
       \<and> P (M[n]) = butlast (P M) @ P ((last (P M))[n])"
proof (cases "length (P M) = 1")
  case sing: True
  have notmulti: "\<not> multiT M" using sing m_6_2_P_components_2[OF M] by (simp del: P.simps)
  have PM: "P M = [M]"
  proof (cases "multiT M \<and> 1 < Lng M")
    case True thus ?thesis using notmulti by simp
  next
    case False thus ?thesis by (rule poper_P_nonmulti)
  qed
  hence lastM: "last (P M) = M" and butl: "butlast (P M) = []" by simp_all
  show ?thesis using lastM butl PM by simp
next
  case notsing: False
  have multi: "multiT M"
  proof -
    have "length (P M) > 1" using notsing P_nonempty[of M] by (cases "P M") auto
    thus ?thesis using m_6_2_P_components_2[OF M] by (simp del: P.simps)
  qed
  have L: "1 < Lng M" using multiT_imp_Lng_gt1[OF M multi] .
  let ?c = "Pcut M"
  let ?M' = "drop ?c M"
  have lastP: "last (P M) = ?M'" and butP: "butlast (P M) = P (take ?c M)"
    using poper_last_P_multi[OF multi L] by auto
  from Pcut_le[OF L] have c0: "0 < ?c" and cj1: "?c \<le> Lng M - 1"
    and lec: "leR M 0 ?c (Lng M - 1)" by auto
  have cL: "?c < Lng M" using cj1 L by linarith
  have lenD: "Lng ?M' = Lng M - ?c" by simp
  have LD: "1 < Lng ?M'" using lastgt lastP by simp
  have clt: "?c < Lng M - 1" using LD lenD by linarith
  have cdef: "?c = Pcut M" by (rule refl)
  \<comment> \<open>part 1: \<open>M[n] = take ?c M @ ?M'[n]\<close> rewritten via \<open>concat (butlast (P M)) = take ?c M\<close>\<close>
  have concbut: "concat (butlast (P M)) = take ?c M"
    using butP poper_concat_P[of "take ?c M"] by simp
  have op_drop: "M[n] = take ?c M @ ?M'[n]"
    by (rule poper_oper_drop[OF M multi L cdef clt])
  have part1: "M[n] = concat (butlast (P M)) @ (last (P M))[n]"
    using op_drop concbut lastP by simp
  \<comment> \<open>part 2: additivity of \<open>P\<close> applied to \<open>N = M[n] = take ?c M @ ?M'[n]\<close>\<close>
  let ?N = "M[n]"
  have NT: "?N \<in> T_PS"
  proof -
    have "?M'[n] \<noteq> []" using poper_oper_nth0[OF _ LD n] cL by (cases ?M') (auto simp: T_PS_def)
    hence "?N \<noteq> []" using op_drop by simp
    thus ?thesis by (simp add: T_PS_def)
  qed
  have LtakeC: "Lng (take ?c M) = ?c" using cL by simp
  have takeN: "take ?c ?N = take ?c M"
    using op_drop LtakeC by simp
  have dropN: "drop ?c ?N = ?M'[n]"
    using op_drop LtakeC by simp
  \<comment> \<open>head of \<open>?M'[n]\<close> equals head of \<open>?M'\<close>, giving \<open>entry ?N 0 ?c = entry M 0 ?c\<close>\<close>
  have hd': "(?M'[n]) ! 0 = ?M' ! 0" using poper_oper_nth0[OF _ LD n] cL
    by (cases ?M') (auto simp: T_PS_def)
  have NcL: "?c < Lng ?N"
  proof -
    have "?M'[n] \<noteq> []" using poper_oper_nth0[OF _ LD n] cL by (cases ?M') (auto simp: T_PS_def)
    hence "0 < Lng (?M'[n])" by simp
    thus ?thesis using op_drop LtakeC by simp
  qed
  have entryNc: "entry ?N 0 ?c = entry M 0 ?c"
  proof -
    have "?N ! ?c = (?M'[n]) ! 0" using op_drop LtakeC by (simp add: nth_append)
    also have "\<dots> = ?M' ! 0" by (rule hd')
    also have "\<dots> = M ! ?c" using cL by (simp add: nth_drop)
    finally have "?N ! ?c = M ! ?c" .
    thus ?thesis by (simp add: entry_def)
  qed
  \<comment> \<open>left-minimality at \<open>?c\<close>: \<open>entry ?N 0 j \<ge> entry ?N 0 ?c\<close> for \<open>j < ?c\<close>\<close>
  have lmin: "\<And>j. j < ?c \<Longrightarrow> entry ?N 0 j \<ge> entry ?N 0 ?c"
  proof -
    fix j assume jc: "j < ?c"
    have "entry ?N 0 j = entry M 0 j"
    proof -
      have "?N ! j = (take ?c M) ! j" using op_drop jc LtakeC by (simp add: nth_append)
      also have "\<dots> = M ! j" using jc cL by (simp add: nth_take)
      finally show ?thesis by (simp add: entry_def)
    qed
    moreover have "entry M 0 j \<ge> entry M 0 ?c"
      using P_add_Pcut_left_min[OF M multi L jc] .
    ultimately show "entry ?N 0 j \<ge> entry ?N 0 ?c" using entryNc by simp
  qed
  have cN1: "?c \<le> Lng ?N - 1" using NcL by linarith
  have paddseg: "P ?N = P (seg ?N 0 (?c - 1)) @ P (seg ?N ?c (Lng ?N - 1))"
  proof (rule m_6_2_P_additive[OF NT c0 cN1])
    fix j assume "j < ?c" thus "entry ?N 0 ?c \<le> entry ?N 0 j" using lmin by simp
  qed
  have seg1: "seg ?N 0 (?c - 1) = take ?c ?N"
    using NcL c0 by (subst seg_0_eq_take) (auto simp del: P.simps)
  have seg2: "seg ?N ?c (Lng ?N - 1) = drop ?c ?N"
    using NcL by (simp add: drop_eq_seg del: P.simps)
  have padd: "P ?N = P (take ?c ?N) @ P (drop ?c ?N)"
    using paddseg seg1 seg2 by (simp del: P.simps)
  have part2: "P (M[n]) = butlast (P M) @ P ((last (P M))[n])"
    using padd takeN dropN butP lastP by (simp del: P.simps)
  show ?thesis using part1 part2 by blast
qed


section \<open>§6.4 幹と枝\<close>

text \<open>
  The auto-generated \<open>P.simps\<close> is a non-terminating rewrite (it always unfolds
  \<open>P\<close> once more); throughout this section we keep it OFF as a default simp rule
  and unfold \<open>P\<close> only explicitly via \<open>subst P.simps\<close>.
\<close>

declare P.simps[simp del]

text \<open>
  FOUNDATIONAL helper: the components of \<open>P M\<close> concatenate back to \<open>M\<close>.
  By the recursion of \<open>P\<close>: in the multi case \<open>P M = P (take c M) @ [drop c M]\<close>,
  so \<open>concat (P M) = concat (P (take c M)) @ drop c M = take c M @ drop c M = M\<close>
  using the IH on \<open>take c M\<close>.
\<close>

lemma idxsum_concat_P: "concat (P M) = M"
proof (induction M rule: P.induct)
  case (1 M)
  show ?case
  proof (cases "multiT M \<and> 1 < Lng M")
    case True
    hence step: "P M = P (take (Pcut M) M) @ [drop (Pcut M) M]"
      by (subst P.simps) simp
    have IH: "concat (P (take (Pcut M) M)) = take (Pcut M) M"
      using True "1.IH" by blast
    have "concat (P M) = concat (P (take (Pcut M) M)) @ drop (Pcut M) M"
      by (simp only: step) simp
    also have "\<dots> = take (Pcut M) M @ drop (Pcut M) M" by (simp only: IH)
    also have "\<dots> = M" by simp
    finally show ?thesis .
  next
    case False
    hence "P M = [M]" by (subst P.simps) (simp only: if_not_P if_False)
    thus ?thesis by simp
  qed
qed

text \<open>The \<open>J\<close>-th value of \<open>IdxSum Q\<close> is the cumulative length sum of the first \<open>J\<close> blocks.\<close>

lemma idxsum_nth:
  assumes "J \<le> length Q"
  shows "IdxSum Q ! J = sum_list (map length (take J Q))"
proof -
  have JL: "J < length [0..<Suc (length Q)]" using assms by simp
  have "IdxSum Q ! J = (\<lambda>J. sum_list (map length (take J Q))) ([0..<Suc (length Q)] ! J)"
    unfolding IdxSum_def using JL by (rule nth_map)
  also have "[0..<Suc (length Q)] ! J = J" using assms by (simp del: upt_Suc)
  finally show ?thesis by simp
qed

text \<open>Cumulative length sums are monotone in the prefix length.\<close>

lemma idxsum_sum_take_mono:
  assumes "J0 \<le> J1"
  shows "sum_list (map length (take J0 Q)) \<le> sum_list (map length (take J1 Q))"
proof -
  have "take J0 Q = take J0 (take J1 Q)"
    using assms by (simp add: min.absorb1)
  hence "\<exists>ys. take J1 Q = take J0 Q @ ys"
    by (metis append_take_drop_id)
  then obtain ys where "take J1 Q = take J0 Q @ ys" by blast
  thus ?thesis by simp
qed

text \<open>The successive difference of \<open>IdxSum\<close> is the length of the \<open>J\<close>-th block.\<close>

lemma idxsum_diff:
  assumes "J < length Q"
  shows "IdxSum Q ! (J + 1) = IdxSum Q ! J + length (Q ! J)"
proof -
  have a: "IdxSum Q ! J = sum_list (map length (take J Q))"
    using assms by (simp add: idxsum_nth)
  have b: "IdxSum Q ! (J + 1) = sum_list (map length (take (Suc J) Q))"
    using assms by (simp add: idxsum_nth)
  have "take (Suc J) Q = take J Q @ [Q ! J]"
    using assms by (simp add: take_Suc_conv_app_nth)
  hence "sum_list (map length (take (Suc J) Q))
         = sum_list (map length (take J Q)) + length (Q ! J)" by simp
  thus ?thesis using a b by simp
qed

text \<open>A list-level block-extraction fact: the \<open>J\<close>-th block of \<open>concat Q\<close> lies between
  its cumulative length sums.\<close>

lemma idxsum_concat_block:
  assumes "J < length Q"
  shows "Q ! J = take (length (Q ! J)) (drop (sum_list (map length (take J Q))) (concat Q))"
proof -
  have decomp: "concat Q = concat (take J Q) @ Q ! J @ concat (drop (Suc J) Q)"
  proof -
    have "Q = take J Q @ Q ! J # drop (Suc J) Q"
      using assms by (rule id_take_nth_drop)
    hence "concat Q = concat (take J Q @ Q ! J # drop (Suc J) Q)" by simp
    thus ?thesis by simp
  qed
  have len: "length (concat (take J Q)) = sum_list (map length (take J Q))"
    by (simp add: length_concat)
  have "drop (sum_list (map length (take J Q))) (concat Q)
        = Q ! J @ concat (drop (Suc J) Q)"
    by (subst decomp) (simp add: len)
  thus ?thesis by simp
qed

text \<open>\<open>map (nth M) [a..<a+n]\<close> is \<open>take n (drop a M)\<close> when in range.\<close>

lemma map_nth_range_eq_take_drop:
  assumes "a + n \<le> length M"
  shows "map (nth M) [a..<a + n] = take n (drop a M)"
  using assms by (intro nth_equalityI) (auto simp: nth_drop)

text \<open>Each component of \<open>P M\<close> is non-empty (being zero- or mono-term).\<close>

lemma idxsum_P_component_nonempty:
  assumes "M \<in> T_PS" "J < length (P M)"
  shows "Lng (P M ! J) > 0"
proof -
  have "P M ! J \<in> set (P M)" using assms(2) by (rule nth_mem)
  hence "zeroT (P M ! J) \<or> monoT (P M ! J)"
    using m_6_2_P_components_1[OF assms(1)] by blast
  thus ?thesis
  proof
    assume "zeroT (P M ! J)"
    thus ?thesis by (simp add: zeroT_def)
  next
    assume "monoT (P M ! J)"
    hence "leR (P M ! J) 0 0 (Lng (P M ! J) - 1)" by (simp add: monoT_def)
    thus ?thesis by (simp add: leR_def le0_def)
  qed
qed

text \<open>m: 命題（\<open>P\<close>と\<open>IdxSum\<close>の関係） — discharges @{thm [source] p_6_4_P_IdxSum}.
  Each component of \<open>P M\<close> is the \<open>M\<close>-slice between consecutive \<open>IdxSum\<close> values.\<close>

lemma m_6_4_P_IdxSum:
  assumes "M \<in> T_PS" "J \<le> Lng (P M) - 1"
  shows "(P M) ! J = seg M (IdxSum (P M) ! J) (IdxSum (P M) ! (J + 1) - 1)"
proof -
  let ?Q = "P M"
  have ne: "?Q \<noteq> []" by (rule P_nonempty)
  hence JL: "J < length ?Q" using assms(2) by (cases ?Q) auto
  let ?a = "IdxSum ?Q ! J"
  let ?b = "IdxSum ?Q ! (J + 1) - 1"
  have aval: "?a = sum_list (map length (take J ?Q))"
    using JL by (simp add: idxsum_nth)
  have diff: "IdxSum ?Q ! (J + 1) = ?a + length (?Q ! J)"
    using JL by (rule idxsum_diff)
  have concatM: "concat ?Q = M" by (rule idxsum_concat_P)
  \<comment> \<open>length of \<open>M\<close> via concat\<close>
  have lenM: "length M = sum_list (map length ?Q)"
    using concatM by (metis length_concat)
  \<comment> \<open>the block equals the take/drop slice\<close>
  have block: "?Q ! J = take (length (?Q ! J)) (drop ?a M)"
    using idxsum_concat_block[OF JL] aval concatM by (simp del: P.simps)
  \<comment> \<open>range bound: \<open>?a + length (?Q!J) \<le> length M\<close>\<close>
  have rangeb: "?a + length (?Q ! J) \<le> length M"
  proof -
    have "?a + length (?Q ! J) = sum_list (map length (take (Suc J) ?Q))"
      using aval JL by (simp add: take_Suc_conv_app_nth)
    also have "\<dots> \<le> sum_list (map length (take (length ?Q) ?Q))"
      using JL by (intro idxsum_sum_take_mono) simp
    also have "\<dots> = sum_list (map length ?Q)" by simp
    finally show ?thesis using lenM by simp
  qed
  \<comment> \<open>\<open>Suc ?b = IdxSum ?Q ! (J+1)\<close>\<close>
  have lenpos: "0 < length (?Q ! J)"
    using idxsum_P_component_nonempty[OF assms(1) JL] by simp
  have sucb: "Suc ?b = ?a + length (?Q ! J)"
    using diff lenpos by simp
  have "seg M ?a ?b = map (nth M) [?a..<Suc ?b]"
    by (simp add: seg_def del: upt_Suc)
  also have "\<dots> = map (nth M) [?a..<?a + length (?Q ! J)]"
    by (simp only: sucb)
  also have "\<dots> = take (length (?Q ! J)) (drop ?a M)"
    using rangeb by (rule map_nth_range_eq_take_drop)
  also have "\<dots> = ?Q ! J" using block by simp
  finally show ?thesis by simp
qed

text \<open>Row-0 parents are unique: \<open>nextR M 0 _ k\<close> determines its source.\<close>

lemma idxsum_parent0_unique:
  assumes "nextR M 0 a k" "nextR M 0 b k"
  shows "a = b"
proof -
  from assms have na: "nextrel0 M a k" and nb: "nextrel0 M b k"
    by (simp_all add: nextR_def)
  show ?thesis
  proof (rule ccontr)
    assume "a \<noteq> b"
    then consider "a < b" | "b < a" by linarith
    thus False
    proof cases
      case 1
      from na have "a < k" and bnd: "\<forall>j. a < j \<and> j < k \<longrightarrow> entry M 0 j \<ge> entry M 0 k"
        by (auto simp: nextrel0_def)
      from nb have "b < k" and "entry M 0 b < entry M 0 k" by (auto simp: nextrel0_def)
      moreover have "entry M 0 b \<ge> entry M 0 k" using bnd 1 \<open>b < k\<close> by simp
      ultimately show False by simp
    next
      case 2
      from nb have "b < k" and bnd: "\<forall>j. b < j \<and> j < k \<longrightarrow> entry M 0 j \<ge> entry M 0 k"
        by (auto simp: nextrel0_def)
      from na have "a < k" and "entry M 0 a < entry M 0 k" by (auto simp: nextrel0_def)
      moreover have "entry M 0 a \<ge> entry M 0 k" using bnd 2 \<open>a < k\<close> by simp
      ultimately show False by simp
    qed
  qed
qed

text \<open>Hence \<open>\<exists>!\<close>-parent in row 0 collapses to mere existence.\<close>

lemma idxsum_ex1_parent0_iff:
  "(\<exists>!j0. nextR M 0 j0 k) \<longleftrightarrow> (\<exists>j0. nextR M 0 j0 k)"
  using idxsum_parent0_unique by metis

text \<open>No row-0 parent of \<open>k\<close> iff \<open>k\<close> is a row-0 left-minimum.\<close>

lemma idxsum_no_parent0_iff:
  assumes "M \<in> T_PS" "k < Lng M"
  shows "(\<not> (\<exists>!j0. nextR M 0 j0 k)) \<longleftrightarrow> (\<forall>j<k. entry M 0 j \<ge> entry M 0 k)"
proof -
  have "(\<exists>j0. nextR M 0 j0 k) \<longleftrightarrow> (\<exists>j<k. entry M 0 j < entry M 0 k)"
  proof
    assume "\<exists>j0. nextR M 0 j0 k"
    then obtain j0 where "nextR M 0 j0 k" by blast
    hence "j0 < k \<and> entry M 0 j0 < entry M 0 k" by (auto simp: nextR_def nextrel0_def)
    thus "\<exists>j<k. entry M 0 j < entry M 0 k" by blast
  next
    assume "\<exists>j<k. entry M 0 j < entry M 0 k"
    then obtain j where j: "j < k" "entry M 0 j < entry M 0 k" by blast
    obtain j' where "nextR M 0 j' k"
      using m_5_1_parent_exists_1[OF assms(1) j(1) assms(2) j(2)] by blast
    thus "\<exists>j0. nextR M 0 j0 k" by blast
  qed
  hence "(\<not> (\<exists>j0. nextR M 0 j0 k)) \<longleftrightarrow> (\<forall>j<k. \<not> entry M 0 j < entry M 0 k)"
    by blast
  thus ?thesis by (simp add: idxsum_ex1_parent0_iff not_less)
qed

text \<open>
  CORE: the left endpoints of the components of \<open>P M\<close> are exactly the row-0
  left-minima of \<open>M\<close>.  Proved by induction on \<open>P\<close>.  Direction 1 (left endpoint
  \<Rightarrow> left-minimum, in range).
\<close>

lemma idxsum_leftend_lmin:
  assumes "M \<in> T_PS" "J < length (P M)"
  shows "IdxSum (P M) ! J \<le> Lng M - 1
       \<and> (\<forall>j < IdxSum (P M) ! J. entry M 0 j \<ge> entry M 0 (IdxSum (P M) ! J))"
  using assms
proof (induction M arbitrary: J rule: P.induct)
  case (1 M)
  show ?case
  proof (cases "multiT M \<and> 1 < Lng M")
    case multi: True
    let ?c = "Pcut M"
    have multiM: "multiT M" using multi by simp
    have L: "1 < Lng M" using multi by simp
    have step: "P M = P (take ?c M) @ [drop ?c M]"
      using multi by (subst P.simps) simp
    have cut: "0 < ?c \<and> ?c \<le> Lng M - 1 \<and> leR M 0 ?c (Lng M - 1)"
      by (rule Pcut_le[OF L])
    hence c0: "0 < ?c" and cj1: "?c \<le> Lng M - 1" and cle: "leR M 0 ?c (Lng M - 1)"
      by simp_all
    have cL: "?c < Lng M" using cj1 L by simp
    have preTPS: "take ?c M \<in> T_PS"
      using c0 cL by (cases "take ?c M") (auto simp: T_PS_def)
    have lenpre: "length (take ?c M) = ?c" using cL by simp
    \<comment> \<open>length sums\<close>
    have concpre: "concat (P (take ?c M)) = take ?c M" by (rule idxsum_concat_P)
    have sumpre: "sum_list (map length (P (take ?c M))) = ?c"
      using concpre lenpre by (metis length_concat)
    have lenPM: "length (P M) = Suc (length (P (take ?c M)))"
      using step by simp
    show ?thesis
    proof (cases "J < length (P (take ?c M))")
      case inpre: True
      have eqidx: "IdxSum (P M) ! J = IdxSum (P (take ?c M)) ! J"
      proof -
        have "IdxSum (P M) ! J = sum_list (map length (take J (P M)))"
          using "1.prems"(2) by (simp add: idxsum_nth)
        also have "take J (P M) = take J (P (take ?c M))"
          using inpre step by (simp add: append_eq_conv_conj)
        also have "sum_list (map length (take J (P (take ?c M)))) = IdxSum (P (take ?c M)) ! J"
          using inpre by (simp add: idxsum_nth less_imp_le_nat)
        finally show ?thesis .
      qed
      have IH: "IdxSum (P (take ?c M)) ! J \<le> Lng (take ?c M) - 1
              \<and> (\<forall>j < IdxSum (P (take ?c M)) ! J.
                   entry (take ?c M) 0 j \<ge> entry (take ?c M) 0 (IdxSum (P (take ?c M)) ! J))"
        using "1.IH"[OF multi preTPS inpre] .
      let ?a = "IdxSum (P (take ?c M)) ! J"
      have aub: "?a \<le> ?c - 1" using IH lenpre by simp
      have altc: "?a < ?c" using aub c0 by simp
      have arange: "IdxSum (P M) ! J \<le> Lng M - 1"
        using eqidx altc cj1 by simp
      have lmin: "\<forall>j < IdxSum (P M) ! J. entry M 0 j \<ge> entry M 0 (IdxSum (P M) ! J)"
      proof (intro allI impI)
        fix j assume jlt: "j < IdxSum (P M) ! J"
        hence jlta: "j < ?a" using eqidx by simp
        hence jc: "j < ?c" and ac: "?a < ?c" using altc by auto
        have e1: "entry (take ?c M) 0 j = entry M 0 j"
          using jc cL by (simp add: entry_def)
        have e2: "entry (take ?c M) 0 ?a = entry M 0 ?a"
          using ac cL by (simp add: entry_def)
        have "entry (take ?c M) 0 j \<ge> entry (take ?c M) 0 ?a"
          using IH jlta by blast
        thus "entry M 0 j \<ge> entry M 0 (IdxSum (P M) ! J)"
          using e1 e2 eqidx by simp
      qed
      show ?thesis using arange lmin by blast
    next
      case False
      with "1.prems"(2) lenPM have Jeq: "J = length (P (take ?c M))" by simp
      have eqc: "IdxSum (P M) ! J = ?c"
      proof -
        have "IdxSum (P M) ! J = sum_list (map length (take J (P M)))"
          using "1.prems"(2) by (simp add: idxsum_nth)
        also have "take J (P M) = P (take ?c M)"
          using Jeq step by simp
        also have "sum_list (map length (P (take ?c M))) = ?c" by (rule sumpre)
        finally show ?thesis .
      qed
      have arange: "IdxSum (P M) ! J \<le> Lng M - 1" using eqc cj1 by simp
      have lmin: "\<forall>j < IdxSum (P M) ! J. entry M 0 j \<ge> entry M 0 (IdxSum (P M) ! J)"
        using eqc P_add_Pcut_left_min[OF "1.prems"(1) multiM L] by simp
      show ?thesis using arange lmin by blast
    qed
  next
    case nonmulti: False
    hence PM: "P M = [M]" by (subst P.simps) (simp only: if_not_P if_False)
    hence Jeq: "J = 0" using "1.prems"(2) by simp
    have idx0: "IdxSum (P M) ! J = 0"
      using Jeq PM by (simp add: IdxSum_def)
    show ?thesis using idx0 by simp
  qed
qed

text \<open>Direction 2 (left-minimum, in range \<Rightarrow> left endpoint).\<close>

lemma idxsum_lmin_leftend:
  assumes "M \<in> T_PS" "k \<le> Lng M - 1"
    "\<forall>j<k. entry M 0 j \<ge> entry M 0 k"
  shows "\<exists>J < length (P M). IdxSum (P M) ! J = k"
  using assms
proof (induction M arbitrary: k rule: P.induct)
  case (1 M)
  show ?case
  proof (cases "multiT M \<and> 1 < Lng M")
    case multi: True
    let ?c = "Pcut M"
    have L: "1 < Lng M" using multi by simp
    have step: "P M = P (take ?c M) @ [drop ?c M]"
      using multi by (subst P.simps) simp
    have cut: "0 < ?c \<and> ?c \<le> Lng M - 1 \<and> leR M 0 ?c (Lng M - 1)"
      by (rule Pcut_le[OF L])
    hence c0: "0 < ?c" and cj1: "?c \<le> Lng M - 1" and cle: "leR M 0 ?c (Lng M - 1)"
      by simp_all
    have cL: "?c < Lng M" using cj1 L by simp
    have preTPS: "take ?c M \<in> T_PS"
      using c0 cL by (cases "take ?c M") (auto simp: T_PS_def)
    have lenpre: "length (take ?c M) = ?c" using cL by simp
    have concpre: "concat (P (take ?c M)) = take ?c M" by (rule idxsum_concat_P)
    have sumpre: "sum_list (map length (P (take ?c M))) = ?c"
      using concpre lenpre by (metis length_concat)
    have lenPM: "length (P M) = Suc (length (P (take ?c M)))"
      using step by simp
    \<comment> \<open>Rule out \<open>?c < k\<close>: such \<open>k\<close> cannot be a left-minimum.\<close>
    have kc: "k \<le> ?c"
    proof (rule ccontr)
      assume "\<not> k \<le> ?c"
      hence ck: "?c < k" by simp
      have kL: "k < Lng M" using "1.prems"(2) L by simp
      have ck1: "k \<le> Lng M - 1" using "1.prems"(2) .
      have leck: "leR M 0 ?c k"
        by (rule m_5_1_ancestor_tree_1[OF "1.prems"(1) cle less_imp_le[OF ck] ck1])
      have "entry M 0 ?c < entry M 0 k"
        by (rule m_5_1_ancestor_basic_1[OF "1.prems"(1) ck order.refl leck])
      moreover have "entry M 0 ?c \<ge> entry M 0 k" using "1.prems"(3) ck by blast
      ultimately show False by simp
    qed
    show ?thesis
    proof (cases "k = ?c")
      case True
      have "IdxSum (P M) ! (length (P (take ?c M))) = ?c"
      proof -
        have "IdxSum (P M) ! (length (P (take ?c M)))
              = sum_list (map length (take (length (P (take ?c M))) (P M)))"
          using lenPM by (simp add: idxsum_nth)
        also have "take (length (P (take ?c M))) (P M) = P (take ?c M)"
          using step by simp
        finally show ?thesis using sumpre by simp
      qed
      thus ?thesis using True lenPM by (intro exI[of _ "length (P (take ?c M))"]) simp
    next
      case False
      with kc have kltc: "k < ?c" by simp
      \<comment> \<open>Transfer the left-minimum to the prefix and apply the IH.\<close>
      have kpre: "k \<le> Lng (take ?c M) - 1" using kltc lenpre by simp
      have lminpre: "\<forall>j<k. entry (take ?c M) 0 j \<ge> entry (take ?c M) 0 k"
      proof (intro allI impI)
        fix j assume "j < k"
        hence jc: "j < ?c" and kc': "k < ?c" using kltc by auto
        have "entry (take ?c M) 0 j = entry M 0 j" using jc cL by (simp add: entry_def)
        moreover have "entry (take ?c M) 0 k = entry M 0 k"
          using kc' cL by (simp add: entry_def)
        ultimately show "entry (take ?c M) 0 j \<ge> entry (take ?c M) 0 k"
          using "1.prems"(3) \<open>j < k\<close> by simp
      qed
      obtain J where J: "J < length (P (take ?c M))" "IdxSum (P (take ?c M)) ! J = k"
        using "1.IH"[OF multi preTPS kpre lminpre] by blast
      have "IdxSum (P M) ! J = IdxSum (P (take ?c M)) ! J"
      proof -
        have "IdxSum (P M) ! J = sum_list (map length (take J (P M)))"
          using J(1) lenPM by (simp add: idxsum_nth)
        also have "take J (P M) = take J (P (take ?c M))"
          using J(1) step by (simp add: append_eq_conv_conj)
        also have "sum_list (map length (take J (P (take ?c M)))) = IdxSum (P (take ?c M)) ! J"
          using J(1) by (simp add: idxsum_nth less_imp_le_nat)
        finally show ?thesis .
      qed
      hence "IdxSum (P M) ! J = k" using J(2) by simp
      thus ?thesis using J(1) lenPM by (intro exI[of _ J]) simp
    qed
  next
    case nonmulti: False
    hence PM: "P M = [M]" by (subst P.simps) (simp only: if_not_P if_False)
    \<comment> \<open>For non-multi \<open>M\<close>, the only row-0 left-minimum in range is \<open>0\<close>.\<close>
    have k0: "k = 0"
    proof (rule ccontr)
      assume "k \<noteq> 0"
      hence kpos: "0 < k" by simp
      have L1: "Lng M \<ge> 1" using "1.prems"(1) by (cases M) (auto simp: T_PS_def)
      have kL: "k < Lng M" using "1.prems"(2) kpos by simp
      have neq1: "Lng M \<noteq> 1" using kpos "1.prems"(2) kL by linarith
      have L: "1 < Lng M" by (rule T_PS_Lng_gt1[OF "1.prems"(1) neq1])
      have notmulti: "\<not> multiT M" using nonmulti L by simp
      have le00: "leR M 0 0 (Lng M - 1)"
        using m_6_2_not_multi_iff_le[OF "1.prems"(1)] notmulti by simp
      have le0k: "leR M 0 0 k"
        by (rule m_5_1_ancestor_tree_1[OF "1.prems"(1) le00 _ "1.prems"(2)]) simp
      have "entry M 0 0 < entry M 0 k"
        by (rule m_5_1_ancestor_basic_1[OF "1.prems"(1) kpos order.refl le0k])
      moreover have "entry M 0 0 \<ge> entry M 0 k" using "1.prems"(3) kpos by blast
      ultimately show False by simp
    qed
    have "IdxSum (P M) ! 0 = 0" using PM by (simp add: IdxSum_def)
    thus ?thesis using PM k0 by (intro exI[of _ 0]) simp
  qed
qed

text \<open>m: 系（\<open>P\<close>と\<open>IdxSum\<close>の合成の特徴付け） (1) — discharges
  @{thm [source] p_6_4_P_IdxSum_char_1}.\<close>

lemma m_6_4_P_IdxSum_char_1:
  assumes "M \<in> T_PS" "J \<le> Lng (P M) - 1"
  shows "\<not> (\<exists>!j0. nextR M 0 j0 (IdxSum (P M) ! J))"
proof -
  have ne: "P M \<noteq> []" by (rule P_nonempty)
  hence JL: "J < length (P M)" using assms(2) by (cases "P M") auto
  let ?k = "IdxSum (P M) ! J"
  have lm: "IdxSum (P M) ! J \<le> Lng M - 1
          \<and> (\<forall>j < IdxSum (P M) ! J. entry M 0 j \<ge> entry M 0 (IdxSum (P M) ! J))"
    by (rule idxsum_leftend_lmin[OF assms(1) JL])
  hence krange: "?k \<le> Lng M - 1" and lmin: "\<forall>j<?k. entry M 0 j \<ge> entry M 0 ?k" by blast+
  have L0: "Lng M \<ge> 1" using assms(1) by (cases M) (auto simp: T_PS_def)
  have kL: "?k < Lng M" using krange L0 by simp
  show ?thesis
    using idxsum_no_parent0_iff[OF assms(1) kL] lmin by blast
qed

text \<open>m: 系（\<open>P\<close>と\<open>IdxSum\<close>の合成の特徴付け） (2) — discharges
  @{thm [source] p_6_4_P_IdxSum_char_2}.\<close>

lemma m_6_4_P_IdxSum_char_2:
  assumes "M \<in> T_PS" "j \<le> Lng M - 1" "\<not> (\<exists>!j0. nextR M 0 j0 j)"
  shows "\<exists>J. J \<le> Lng (P M) - 1 \<and> j = IdxSum (P M) ! J"
proof -
  have L0: "Lng M \<ge> 1" using assms(1) by (cases M) (auto simp: T_PS_def)
  have jL: "j < Lng M" using assms(2) L0 by simp
  have lmin: "\<forall>j'<j. entry M 0 j' \<ge> entry M 0 j"
    using idxsum_no_parent0_iff[OF assms(1) jL] assms(3) by blast
  obtain J where J: "J < length (P M)" "IdxSum (P M) ! J = j"
    using idxsum_lmin_leftend[OF assms(1) assms(2) lmin] by blast
  have "J \<le> Lng (P M) - 1" using J(1) by simp
  thus ?thesis using J(2) by auto
qed

text \<open>\<open>IdxSum Q\<close> is monotone in the index (up to \<open>length Q\<close>).\<close>

lemma idxsum_mono:
  assumes "J0 \<le> J1" "J1 \<le> length Q"
  shows "IdxSum Q ! J0 \<le> IdxSum Q ! J1"
proof -
  have "IdxSum Q ! J0 = sum_list (map length (take J0 Q))"
    using assms by (simp add: idxsum_nth)
  moreover have "IdxSum Q ! J1 = sum_list (map length (take J1 Q))"
    using assms(2) by (simp add: idxsum_nth)
  moreover have "sum_list (map length (take J0 Q)) \<le> sum_list (map length (take J1 Q))"
    using assms(1) by (rule idxsum_sum_take_mono)
  ultimately show ?thesis by simp
qed

text \<open>m: 命題（\<open>P\<close>の各成分の左端の単調性） — discharges
  @{thm [source] p_6_4_P_leftend_mono}.\<close>

lemma m_6_4_P_leftend_mono:
  assumes "M \<in> T_PS" "J0' \<le> J1'" "J1' \<le> Lng (P M) - 1"
  shows "entry ((P M) ! J0') 0 0 \<ge> entry ((P M) ! J1') 0 0"
proof -
  let ?Q = "P M"
  have ne: "?Q \<noteq> []" by (rule P_nonempty)
  hence J1L: "J1' < length ?Q" using assms(3) by (cases ?Q) auto
  have J0L: "J0' < length ?Q" using assms(2) J1L by simp
  have J0le: "J0' \<le> Lng ?Q - 1" using assms(2,3) by simp
  let ?a0 = "IdxSum ?Q ! J0'"
  let ?a1 = "IdxSum ?Q ! J1'"
  \<comment> \<open>component left ends are the IdxSum values\<close>
  have seg0: "?Q ! J0' = seg M ?a0 (IdxSum ?Q ! (J0' + 1) - 1)"
    by (rule m_6_4_P_IdxSum[OF assms(1) J0le])
  have seg1: "?Q ! J1' = seg M ?a1 (IdxSum ?Q ! (J1' + 1) - 1)"
    by (rule m_6_4_P_IdxSum[OF assms(1) assms(3)])
  \<comment> \<open>each component is non-empty, so its 0-th entry is \<open>entry M 0 (left end)\<close>\<close>
  have len0: "0 < Lng (?Q ! J0')"
    by (rule idxsum_P_component_nonempty[OF assms(1) J0L])
  have len1: "0 < Lng (?Q ! J1')"
    by (rule idxsum_P_component_nonempty[OF assms(1) J1L])
  have e0: "entry (?Q ! J0') 0 0 = entry M 0 ?a0"
  proof -
    have "0 < Lng (seg M ?a0 (IdxSum ?Q ! (J0' + 1) - 1))"
      using len0 seg0 by simp
    hence "entry (seg M ?a0 (IdxSum ?Q ! (J0' + 1) - 1)) 0 0 = entry M 0 ?a0"
      by (subst entry_seg) auto
    thus ?thesis using seg0 by simp
  qed
  have e1: "entry (?Q ! J1') 0 0 = entry M 0 ?a1"
  proof -
    have "0 < Lng (seg M ?a1 (IdxSum ?Q ! (J1' + 1) - 1))"
      using len1 seg1 by simp
    hence "entry (seg M ?a1 (IdxSum ?Q ! (J1' + 1) - 1)) 0 0 = entry M 0 ?a1"
      by (subst entry_seg) auto
    thus ?thesis using seg1 by simp
  qed
  \<comment> \<open>\<open>?a1\<close> is a row-0 left-minimum and \<open>?a0 \<le> ?a1\<close>\<close>
  have lm1: "IdxSum ?Q ! J1' \<le> Lng M - 1
           \<and> (\<forall>j < IdxSum ?Q ! J1'. entry M 0 j \<ge> entry M 0 (IdxSum ?Q ! J1'))"
    by (rule idxsum_leftend_lmin[OF assms(1) J1L])
  hence lmin1: "\<forall>j < ?a1. entry M 0 j \<ge> entry M 0 ?a1" by blast
  have mono: "?a0 \<le> ?a1"
    by (rule idxsum_mono[OF assms(2) less_imp_le_nat[OF J1L]])
  show ?thesis
  proof (cases "?a0 = ?a1")
    case True
    thus ?thesis using e0 e1 by simp
  next
    case False
    with mono have "?a0 < ?a1" by simp
    hence "entry M 0 ?a0 \<ge> entry M 0 ?a1" using lmin1 by blast
    thus ?thesis using e0 e1 by simp
  qed
qed


subsection \<open>§6.2 単項性: 非複項列の基本列 (non-multi expansion)\<close>

text \<open>
  For a non-multi \<open>M\<close>, \<open>M[n]\<close> is either \<open>n\<close> copies of \<open>Pred M\<close> (when the last
  index is a row-0 child of index 0 with zero second coordinate) or a single
  non-multi sequence \<open>[M[n]]\<close>.  These two lemmas discharge
  @{thm [source] p_6_2_nonmulti_oper_1} / @{thm [source] p_6_2_nonmulti_oper_2}.
\<close>

text \<open>A non-empty non-multi prefix \<open>Pred M\<close> stays non-multi.\<close>

lemma nonmulti_Pred:
  assumes M: "M \<in> T_PS" and nm: "\<not> multiT M" and L: "1 < Lng M"
  shows "\<not> multiT (Pred M)"
proof -
  let ?Q = "Pred M"
  have predtake: "?Q = take (Lng M - 1) M" using L by (simp add: Pred_def butlast_conv_take)
  have LQ: "Lng ?Q = Lng M - 1" using L by (simp add: Pred_def)
  have QT: "?Q \<in> T_PS" using L by (cases M) (auto simp: T_PS_def Pred_def)
  have mono: "\<forall>j. 0 < j \<and> j < Lng M \<longrightarrow> entry M 0 0 < entry M 0 j"
    using m_6_2_multi_crit_12[OF M] nm by simp
  show ?thesis
  proof (subst m_6_2_multi_crit_12[OF QT], intro allI impI)
    fix j assume j: "0 < j \<and> j < Lng ?Q"
    hence jlt: "j < Lng M - 1" using LQ by simp
    hence jL: "j < Lng M" by simp
    have e0: "entry ?Q 0 0 = entry M 0 0"
      using L predtake by (simp add: entry_def nth_take)
    have ej: "entry ?Q 0 j = entry M 0 j"
      using jlt predtake by (simp add: entry_def nth_take)
    have "entry M 0 0 < entry M 0 j" using mono[rule_format, of j] j jL by simp
    thus "entry ?Q 0 0 < entry ?Q 0 j" using e0 ej by simp
  qed
qed

text \<open>Row-0 entry of an \<open>n\<close>-fold concatenation, on the first copy.\<close>

lemma entry_concat_replicate_lt:
  assumes "j < Lng Q"
  shows "entry (concat (replicate (Suc m) Q)) i j = entry Q i j"
proof -
  have "concat (replicate (Suc m) Q) = Q @ concat (replicate m Q)"
    by (simp add: replicate_Suc)
  thus ?thesis using assms by (simp add: entry_def nth_append)
qed

text \<open>\<open>P\<close> of an \<open>n\<close>-fold concatenation of a non-multi sequence is \<open>n\<close> copies.\<close>

lemma P_concat_replicate_nonmulti:
  assumes Q: "Q \<in> T_PS" and nm: "\<not> multiT Q"
  shows "n \<ge> 1 \<Longrightarrow> P (concat (replicate n Q)) = replicate n Q"
proof (induction n)
  case 0 thus ?case by simp
next
  case (Suc m)
  show ?case
  proof (cases "m = 0")
    case True
    have "concat (replicate (Suc 0) Q) = Q" by simp
    moreover have "P Q = [Q]" by (rule poper_P_nonmulti) (simp add: nm)
    ultimately show ?thesis using True by simp
  next
    case mpos: False
    hence m1: "m \<ge> 1" by simp
    let ?N = "concat (replicate (Suc m) Q)"
    have lenQ: "0 < Lng Q" using Q by (cases Q) (auto simp: T_PS_def)
    have decomp: "?N = Q @ concat (replicate m Q)"
      by (simp add: replicate_Suc)
    have lenN: "Lng ?N = Suc m * Lng Q"
      by (simp add: length_concat map_replicate sum_list_replicate)
    have NT: "?N \<in> T_PS" using lenQ lenN by (cases ?N) (auto simp: T_PS_def)
    have c0: "0 < Lng Q" using lenQ .
    have cN1: "Lng Q \<le> Lng ?N - 1"
    proof -
      have "2 * Lng Q \<le> Suc m * Lng Q" using m1 by simp
      thus ?thesis using lenN lenQ by linarith
    qed
    \<comment> \<open>row-0 entry minimality at the cut \<open>Lng Q\<close>\<close>
    have entry_cut: "entry ?N 0 (Lng Q) = entry Q 0 0"
    proof -
      have "?N ! (Lng Q) = (concat (replicate m Q)) ! 0"
        using decomp by (simp add: nth_append)
      also have "\<dots> = Q ! 0"
        using m1 lenQ by (cases m) (auto simp add: replicate_Suc nth_append)
      finally show ?thesis by (simp add: entry_def)
    qed
    have lmin: "\<And>j. j < Lng Q \<Longrightarrow> entry ?N 0 (Lng Q) \<le> entry ?N 0 j"
    proof -
      fix j assume jq: "j < Lng Q"
      have ej: "entry ?N 0 j = entry Q 0 j"
        using jq decomp by (simp add: entry_def nth_append)
      have mono: "\<forall>k. 0 < k \<and> k < Lng Q \<longrightarrow> entry Q 0 0 < entry Q 0 k"
        using m_6_2_multi_crit_12[OF Q] nm by simp
      show "entry ?N 0 (Lng Q) \<le> entry ?N 0 j"
      proof (cases "j = 0")
        case True thus ?thesis using ej entry_cut by simp
      next
        case False
        hence "entry Q 0 0 < entry Q 0 j" using mono[rule_format, of j] jq by simp
        thus ?thesis using ej entry_cut by simp
      qed
    qed
    have padd: "P ?N = P (seg ?N 0 (Lng Q - 1)) @ P (seg ?N (Lng Q) (Lng ?N - 1))"
      by (rule m_6_2_P_additive[OF NT c0 cN1 lmin])
    have NcL: "Lng Q < Lng ?N" using cN1 lenN lenQ by linarith
    have seg1: "seg ?N 0 (Lng Q - 1) = take (Lng Q) ?N"
      using NcL c0 by (subst seg_0_eq_take) (auto simp del: P.simps)
    have seg2: "seg ?N (Lng Q) (Lng ?N - 1) = drop (Lng Q) ?N"
      by (rule drop_eq_seg[OF NcL, symmetric])
    have takeN: "take (Lng Q) ?N = Q" using decomp by simp
    have dropN: "drop (Lng Q) ?N = concat (replicate m Q)" using decomp by simp
    have "P ?N = P Q @ P (concat (replicate m Q))"
      using padd seg1 seg2 takeN dropN by (simp del: P.simps)
    also have "\<dots> = [Q] @ P (concat (replicate m Q))"
      using poper_P_nonmulti[of Q] nm by (simp del: P.simps)
    also have "\<dots> = [Q] @ replicate m Q" using Suc.IH m1 by simp
    also have "\<dots> = replicate (Suc m) Q" by (simp add: replicate_app_Cons_same)
    finally show ?thesis .
  qed
qed

text \<open>m: 命題（非複項性と基本列の関係）(1) — \<open>n\<close> copies of \<open>Pred M\<close>.\<close>

lemma m_6_2_nonmulti_oper_1:
  assumes M: "M \<in> T_PS" and n: "n \<ge> 1" and nm: "\<not> multiT M"
    and par: "nextR M 0 0 (Lng M - 1)" and e1: "entry M 1 (Lng M - 1) = 0"
  shows "P (M[n]) = replicate n (Pred M)"
proof -
  let ?j1 = "Lng M - 1"
  \<comment> \<open>\<open>nextR M 0 0 ?j1\<close> forces \<open>Lng M > 1\<close>\<close>
  have nr0: "nextrel0 M 0 ?j1" using par by (simp add: nextR_def)
  have j1pos: "0 < ?j1" using nr0 by (simp add: nextrel0_def)
  have L: "1 < Lng M" using j1pos by simp
  have nz: "?j1 \<noteq> 0" using L by simp
  \<comment> \<open>last pair is not \<open>(0,0)\<close> (row 0 entry is positive)\<close>
  have e0pos: "entry M 0 ?j1 > 0" using nr0 by (simp add: nextrel0_def)
  have notzero: "\<not> (entry M 0 ?j1 = 0 \<and> entry M 1 ?j1 = 0)" using e0pos by simp
  \<comment> \<open>\<open>i1 = 0\<close> since the last second coordinate is 0\<close>
  have i1: "idx1 M ?j1 = 0" using e1 by (simp add: idx1_def)
  \<comment> \<open>the row-0 parent of \<open>?j1\<close> is \<open>0\<close>\<close>
  have ex1: "\<exists>!j0. nextR M 0 j0 ?j1"
    by (metis idxsum_ex1_parent0_iff par)
  have hp: "hasParent M (idx1 M ?j1) ?j1"
    unfolding i1 hasParent_def using ex1 .
  have parent0: "parent M (idx1 M ?j1) ?j1 = 0"
    unfolding i1 parent_def by (rule the1_equality[OF ex1 par])
  \<comment> \<open>operator expands with zero increments and zero offset\<close>
  have op: "M[n] = concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j, entry M 1 j)) [0..<?j1]) [0..<n])"
  proof -
    have "M[n] = take (parent M (idx1 M ?j1) ?j1) M @
        concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j +
                  k * (if 0 < idx1 M ?j1 then entry M 0 ?j1 - entry M 0 (parent M (idx1 M ?j1) ?j1) else 0),
                              entry M 1 j +
                  k * (if 1 < idx1 M ?j1 then entry M 1 ?j1 - entry M 1 (parent M (idx1 M ?j1) ?j1) else 0)))
                              [parent M (idx1 M ?j1) ?j1..<?j1]) [0..<n])"
      using poper_oper_expand[OF L notzero hp, of n] by (simp add: Let_def)
    thus ?thesis using i1 parent0 by simp
  qed
  \<comment> \<open>each block equals \<open>Pred M = take ?j1 M\<close>\<close>
  have predtake: "Pred M = take ?j1 M" using L by (simp add: Pred_def butlast_conv_take)
  have block: "map (\<lambda>j. (entry M 0 j, entry M 1 j)) [0..<?j1] = Pred M"
  proof -
    have jL: "?j1 \<le> Lng M" by simp
    have "map (\<lambda>j. (entry M 0 j, entry M 1 j)) [0..<?j1] = take ?j1 M"
    proof (rule nth_equalityI)
      show "length (map (\<lambda>j. (entry M 0 j, entry M 1 j)) [0..<?j1]) = length (take ?j1 M)"
        using jL by simp
    next
      fix i assume "i < length (map (\<lambda>j. (entry M 0 j, entry M 1 j)) [0..<?j1])"
      hence ilt: "i < ?j1" by simp
      hence "map (\<lambda>j. (entry M 0 j, entry M 1 j)) [0..<?j1] ! i = (entry M 0 i, entry M 1 i)"
        by (simp add: nth_upt)
      also have "\<dots> = M ! i" by (rule entry_pair)
      also have "\<dots> = take ?j1 M ! i" using ilt by (simp add: nth_take)
      finally show "map (\<lambda>j. (entry M 0 j, entry M 1 j)) [0..<?j1] ! i = take ?j1 M ! i" .
    qed
    thus ?thesis using predtake by simp
  qed
  have opn: "M[n] = concat (replicate n (Pred M))"
  proof -
    have "M[n] = concat (map (\<lambda>k. Pred M) [0..<n])" using op block by simp
    also have "\<dots> = concat (replicate n (Pred M))" by (simp add: map_replicate_const)
    finally show ?thesis .
  qed
  \<comment> \<open>\<open>Pred M\<close> is a non-empty non-multi sequence\<close>
  have predNM: "\<not> multiT (Pred M)" by (rule nonmulti_Pred[OF M nm L])
  have predT: "Pred M \<in> T_PS" using L by (cases M) (auto simp: T_PS_def Pred_def)
  show ?thesis
    using opn P_concat_replicate_nonmulti[OF predT predNM n] by simp
qed

text \<open>m: 命題（非複項性と基本列の関係）(2) — singleton \<open>[M[n]]\<close>.\<close>

lemma m_6_2_nonmulti_oper_2:
  assumes M: "M \<in> T_PS" and n: "n \<ge> 1" and nm: "\<not> multiT M"
    and H: "\<not> nextR M 0 0 (Lng M - 1) \<or> entry M 1 (Lng M - 1) > 0"
  shows "P ((M::pairseq)[n]) = [(M[n])]"
proof -
  let ?j1 = "Lng M - 1"
  have "\<not> (multiT (M[n]) \<and> 1 < Lng (M[n]))"
  proof (cases "Lng M = 1")
    case True
    hence "?j1 = 0" by simp
    hence "M[n] = M" by (simp add: oper_def Let_def)
    thus ?thesis using nm by simp
  next
    case False
    have L: "1 < Lng M" using M False by (cases M) (auto simp: T_PS_def)
    have nz: "?j1 \<noteq> 0" using L by simp
    \<comment> \<open>mono: row-0 strictly increases away from 0\<close>
    have mono: "\<forall>j. 0 < j \<and> j < Lng M \<longrightarrow> entry M 0 0 < entry M 0 j"
      using m_6_2_multi_crit_12[OF M] nm by simp
    have j1L: "?j1 < Lng M" using L by simp
    have e0j1: "entry M 0 ?j1 > 0"
    proof -
      have "entry M 0 0 < entry M 0 ?j1" using mono[rule_format, of ?j1] nz j1L by simp
      thus ?thesis by simp
    qed
    have notzero: "\<not> (entry M 0 ?j1 = 0 \<and> entry M 1 ?j1 = 0)" using e0j1 by simp
    show ?thesis
    proof (cases "hasParent M (idx1 M ?j1) ?j1")
      case noparent: False
      \<comment> \<open>degenerate: \<open>M[n] = Pred M\<close>, non-multi\<close>
      have "M[n] = Pred M"
        using notzero noparent nz by (auto simp: oper_def Let_def)
      moreover have "\<not> multiT (Pred M)" by (rule nonmulti_Pred[OF M nm L])
      ultimately show ?thesis by simp
    next
      case haspar: True
      let ?i1 = "idx1 M ?j1"
      let ?j0 = "parent M ?i1 ?j1"
      let ?d0 = "if 0 < ?i1 then entry M 0 ?j1 - entry M 0 ?j0 else 0"
      let ?d1 = "if 1 < ?i1 then entry M 1 ?j1 - entry M 1 ?j0 else 0"
      have parR: "nextR M ?i1 ?j0 ?j1"
        using haspar unfolding hasParent_def parent_def by (rule theI')
      have j0lt: "?j0 < ?j1" using parR by (cases "?i1 = 0")
          (auto simp: nextR_def nextrel0_def nextrel1_def)
      have op: "M[n] = take ?j0 M @
          concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * ?d0, entry M 1 j + k * ?d1))
                                [?j0..<?j1]) [0..<n])"
        using poper_oper_expand[OF L notzero haspar, of n] by (simp add: Let_def)
      \<comment> \<open>the saving fact: when the parent is index 0, the row-0 increment is positive\<close>
      have j0d0: "?j0 = 0 \<Longrightarrow> 0 < ?d0"
      proof -
        assume j00: "?j0 = 0"
        have "?i1 \<noteq> 0"
        proof
          assume "?i1 = 0"
          hence "nextR M 0 0 ?j1" using parR j00 by simp
          \<comment> \<open>then \<open>i1 = 0\<close> means \<open>entry M 1 ?j1 = 0\<close>, contradicting \<open>H\<close>\<close>
          moreover have "entry M 1 ?j1 = 0"
            using \<open>?i1 = 0\<close> by (simp add: idx1_def split: if_split_asm)
          ultimately show False using H by simp
        qed
        hence i11: "0 < ?i1" by simp
        have "entry M 0 ?j0 < entry M 0 ?j1"
          using mono[rule_format, of ?j1] j00 nz L by simp
        thus "0 < ?d0" using i11 by simp
      qed
      \<comment> \<open>show \<open>M[n]\<close> is non-multi via the row-0 strict-minimum criterion\<close>
      let ?N = "M[n]"
      have NT: "?N \<in> T_PS" using poper_oper_nth0[OF M L n] by (simp add: T_PS_def)
      \<comment> \<open>row-0 head equals \<open>entry M 0 0\<close>\<close>
      have hd0: "entry ?N 0 0 = entry M 0 0"
        using poper_oper_nth0[OF M L n] by (simp add: entry_def)
      \<comment> \<open>express the row-0 value list of \<open>?N\<close>\<close>
      let ?A = "map (entry M 0) [0..<?j0]"
      let ?B = "concat (map (\<lambda>k. map (\<lambda>j. entry M 0 j + k * ?d0) [?j0..<?j1]) [0..<n])"
      have j0L: "?j0 \<le> Lng M" using j0lt nz L by linarith
      have fstN: "map fst ?N = ?A @ ?B"
      proof -
        have "map fst (take ?j0 M) = ?A"
        proof (rule nth_equalityI)
          show "length (map fst (take ?j0 M)) = length ?A" using j0L by simp
        next
          fix i assume ilen: "i < length (map fst (take ?j0 M))"
          hence ilt: "i < ?j0" using j0L by simp
          have itk: "i < length (take ?j0 M)" using ilen by simp
          have "map fst (take ?j0 M) ! i = fst (take ?j0 M ! i)"
            using itk by (simp add: nth_map)
          also have "\<dots> = fst (M ! i)" using ilt by (simp add: nth_take)
          also have "\<dots> = entry M 0 i" by (simp add: entry_def)
          also have "\<dots> = ?A ! i" using ilt by simp
          finally show "map fst (take ?j0 M) ! i = ?A ! i" .
        qed
        moreover have "map fst (concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * ?d0,
                            entry M 1 j + k * ?d1)) [?j0..<?j1]) [0..<n])) = ?B"
          by (simp add: map_concat o_def)
        ultimately show ?thesis using op by simp
      qed
      \<comment> \<open>row-0 value list of \<open>?N\<close> is \<open>(entry M 0 0) # tail\<close> with all tail values larger\<close>
      have headM: "map fst ?N \<noteq> []"
        using poper_oper_nth0[OF M L n] by (cases ?N) auto
      \<comment> \<open>the key: every element of the tail strictly exceeds \<open>entry M 0 0\<close>\<close>
      have tailgt: "\<forall>x \<in> set (tl (map fst ?N)). entry M 0 0 < x"
      proof (cases "0 < ?j0")
        case j0pos: True
        \<comment> \<open>prefix non-empty: tail \<open>= tl ?A @ ?B\<close>\<close>
        have Ane: "?A \<noteq> []" using j0pos by simp
        have tleq: "tl (map fst ?N) = tl ?A @ ?B" using fstN Ane by simp
        show ?thesis
        proof
          fix x assume "x \<in> set (tl (map fst ?N))"
          hence "x \<in> set (tl ?A) \<or> x \<in> set ?B" using tleq by auto
          thus "entry M 0 0 < x"
          proof
            assume "x \<in> set (tl ?A)"
            then obtain p where p: "p \<in> set [Suc 0..<?j0]" and xeq: "x = entry M 0 p"
              using j0pos by (cases ?j0) (auto simp: map_tl[symmetric] upt_conv_Cons)
            have prng: "0 < p \<and> p < ?j0" using p by auto
            hence "p < Lng M" using j0lt nz L by linarith
            hence "entry M 0 0 < entry M 0 p" using mono[rule_format, of p] prng by simp
            thus ?thesis using xeq by simp
          next
            assume "x \<in> set ?B"
            then obtain kk where kk: "kk \<in> set [0..<n]"
              and xin: "x \<in> set (map (\<lambda>j. entry M 0 j + kk * ?d0) [?j0..<?j1])"
              by (auto simp: set_concat)
            from xin obtain j where jrng: "j \<in> set [?j0..<?j1]"
              and xeq: "x = entry M 0 j + kk * ?d0" by auto
            from jrng have jrng': "?j0 \<le> j \<and> j < ?j1" by auto
            have jpos: "0 < j" using jrng' j0pos by simp
            have jL: "j < Lng M" using jrng' j0lt nz L by linarith
            hence "entry M 0 0 < entry M 0 j" using mono[rule_format, of j] jpos by simp
            thus ?thesis using xeq by simp
          qed
        qed
      next
        case j00: False
        hence j0z: "?j0 = 0" by simp
        hence d0pos: "0 < ?d0" by (rule j0d0)
        have Ane: "?A = []" using j0z by simp
        \<comment> \<open>split \<open>?B\<close> into block 0 and the rest\<close>
        have nlist: "[0..<n] = 0 # [Suc 0..<n]" using n by (simp add: upt_conv_Cons)
        have blk0: "map (\<lambda>j. entry M 0 j + 0 * ?d0) [?j0..<?j1] = map (entry M 0) [0..<?j1]"
          using j0z by simp
        have Beq: "?B = map (entry M 0) [0..<?j1] @
              concat (map (\<lambda>k. map (\<lambda>j. entry M 0 j + k * ?d0) [?j0..<?j1]) [Suc 0..<n])"
        proof -
          have "?B = concat (map (\<lambda>k. map (\<lambda>j. entry M 0 j + k * ?d0) [?j0..<?j1]) (0 # [Suc 0..<n]))"
            by (simp only: nlist)
          also have "\<dots> = map (\<lambda>j. entry M 0 j + 0 * ?d0) [?j0..<?j1] @
              concat (map (\<lambda>k. map (\<lambda>j. entry M 0 j + k * ?d0) [?j0..<?j1]) [Suc 0..<n])"
            by simp
          also have "\<dots> = map (entry M 0) [0..<?j1] @
              concat (map (\<lambda>k. map (\<lambda>j. entry M 0 j + k * ?d0) [?j0..<?j1]) [Suc 0..<n])"
            by (simp only: blk0)
          finally show ?thesis .
        qed
        have j1ne: "[0..<?j1] \<noteq> []" using nz by simp
        have tlblk0: "tl (map (entry M 0) [0..<?j1]) = map (entry M 0) [Suc 0..<?j1]"
          using nz by (cases ?j1) (auto simp: upt_conv_Cons)
        have tleq: "tl (map fst ?N) = map (entry M 0) [Suc 0..<?j1] @
              concat (map (\<lambda>k. map (\<lambda>j. entry M 0 j + k * ?d0) [?j0..<?j1]) [Suc 0..<n])"
        proof -
          have "map fst ?N = map (entry M 0) [0..<?j1] @
              concat (map (\<lambda>k. map (\<lambda>j. entry M 0 j + k * ?d0) [?j0..<?j1]) [Suc 0..<n])"
            using fstN Ane Beq by simp
          hence "tl (map fst ?N) = tl (map (entry M 0) [0..<?j1]) @
              concat (map (\<lambda>k. map (\<lambda>j. entry M 0 j + k * ?d0) [?j0..<?j1]) [Suc 0..<n])"
            using j1ne by (simp add: tl_append2)
          thus ?thesis by (simp only: tlblk0)
        qed
        show ?thesis
        proof
          fix x assume "x \<in> set (tl (map fst ?N))"
          hence "x \<in> set (map (entry M 0) [Suc 0..<?j1]) \<or>
                 x \<in> set (concat (map (\<lambda>k. map (\<lambda>j. entry M 0 j + k * ?d0) [?j0..<?j1]) [Suc 0..<n]))"
            using tleq by auto
          thus "entry M 0 0 < x"
          proof
            assume "x \<in> set (map (entry M 0) [Suc 0..<?j1])"
            then obtain p where p: "p \<in> set [Suc 0..<?j1]" and xeq: "x = entry M 0 p" by auto
            have prng: "0 < p \<and> p < ?j1" using p by auto
            hence "p < Lng M" using nz L by linarith
            hence "entry M 0 0 < entry M 0 p" using mono[rule_format, of p] prng by simp
            thus ?thesis using xeq by simp
          next
            assume "x \<in> set (concat (map (\<lambda>k. map (\<lambda>j. entry M 0 j + k * ?d0) [?j0..<?j1]) [Suc 0..<n]))"
            then obtain kk where kk: "kk \<in> set [Suc 0..<n]"
              and xin: "x \<in> set (map (\<lambda>j. entry M 0 j + kk * ?d0) [?j0..<?j1])"
              by (auto simp: set_concat)
            from xin obtain j where jrng: "j \<in> set [?j0..<?j1]"
              and xeq: "x = entry M 0 j + kk * ?d0" by auto
            from jrng have jrng': "?j0 \<le> j \<and> j < ?j1" by auto
            have kkpos: "0 < kk" using kk by auto
            have jL: "j < Lng M" using jrng' j0lt nz L by linarith
            show "entry M 0 0 < x"
            proof (cases "0 < j")
              case True
              hence "entry M 0 0 < entry M 0 j" using mono[rule_format, of j] jL by simp
              thus ?thesis using xeq by simp
            next
              case False
              hence "j = 0" by simp
              hence "x = entry M 0 0 + kk * ?d0" using xeq by simp
              moreover have "0 < kk * ?d0" using kkpos d0pos by simp
              ultimately show ?thesis by simp
            qed
          qed
        qed
      qed
      have strict: "\<forall>k. 0 < k \<and> k < Lng ?N \<longrightarrow> entry M 0 0 < entry ?N 0 k"
      proof (intro allI impI)
        fix k assume k: "0 < k \<and> k < Lng ?N"
        have klen: "length (tl (map fst ?N)) = Lng ?N - 1" by (simp add: length_map)
        have kml: "k - 1 < length (tl (map fst ?N))" using k klen by linarith
        have ksuc: "Suc (k - 1) = k" using k by simp
        have "entry ?N 0 k = (map fst ?N) ! k" using k by (simp add: entry_def)
        also have "\<dots> = (map fst ?N) ! Suc (k - 1)" using ksuc by simp
        also have "\<dots> = (tl (map fst ?N)) ! (k - 1)" using kml by (simp add: nth_tl)
        also have "\<dots> \<in> set (tl (map fst ?N))" using kml by (rule nth_mem)
        finally show "entry M 0 0 < entry ?N 0 k" using tailgt by blast
      qed
      have "\<forall>j. 0 < j \<and> j < Lng ?N \<longrightarrow> entry ?N 0 0 < entry ?N 0 j"
        using strict hd0 by simp
      hence "\<not> multiT ?N" using m_6_2_multi_crit_12[OF NT] by simp
      thus ?thesis by simp
    qed
  qed
  thus ?thesis by (rule poper_P_nonmulti)
qed


text \<open>m: 命題（切片の単項成分と\<open><\<^bsub>M\<^esub>\<^sup>Next\<close>の関係） — discharges
  @{thm [source] p_6_4_mono_slice_next}.\<close>

lemma m_6_4_mono_slice_next:
  assumes "M \<in> PT_PS" "0 < j0" "j0 \<le> Lng M - 1"
    "J \<le> Lng (P (seg M j0 (Lng M - 1))) - 1"
  shows "hasParent M 0 (j0 + IdxSum (P (seg M j0 (Lng M - 1))) ! J)
       \<and> parent M 0 (j0 + IdxSum (P (seg M j0 (Lng M - 1))) ! J) < j0"
proof -
  let ?N = "seg M j0 (Lng M - 1)"
  let ?Q = "P ?N"
  let ?k = "IdxSum ?Q ! J"
  have MT: "M \<in> T_PS" and monoM: "monoT M" using assms(1) by (auto simp: PT_PS_def)
  have LM: "Lng M > 0" using MT by (cases M) (auto simp: T_PS_def)
  have j0LM: "j0 < Lng M" using assms(3) LM by linarith
  \<comment> \<open>The slice is non-empty, hence in \<open>T_PS\<close>.\<close>
  have LN: "Lng ?N = Suc (Lng M - 1) - j0" by simp
  have LNpos: "Lng ?N > 0" using j0LM LM by simp
  have Nne: "?N \<noteq> []" using LNpos length_greater_0_conv by blast
  have NT: "?N \<in> T_PS" using Nne by (simp add: T_PS_def)
  have ne: "?Q \<noteq> []" by (rule P_nonempty)
  hence JL: "J < length ?Q" using assms(4) by (cases ?Q) auto
  \<comment> \<open>\<open>?k\<close> is a row-0 left-minimum of \<open>?N\<close>, in range.\<close>
  have lm: "?k \<le> Lng ?N - 1
          \<and> (\<forall>j < ?k. entry ?N 0 j \<ge> entry ?N 0 ?k)"
    by (rule idxsum_leftend_lmin[OF NT JL])
  hence krange: "?k \<le> Lng ?N - 1" and lmin: "\<forall>j < ?k. entry ?N 0 j \<ge> entry ?N 0 ?k"
    by blast+
  have kN: "?k < Lng ?N" using krange LNpos by simp
  have kabsLM: "j0 + ?k < Lng M" using kN LN j0LM by simp
  \<comment> \<open>Translate the left-minimum to \<open>M\<close>: every \<open>j'\<in>[j0, j0+?k)\<close> has
      \<open>entry M 0 j' \<ge> entry M 0 (j0+?k)\<close>.\<close>
  have ek: "entry ?N 0 ?k = entry M 0 (j0 + ?k)" using kN by (simp add: entry_seg)
  have lminM: "\<forall>j'. j0 \<le> j' \<and> j' < j0 + ?k \<longrightarrow> entry M 0 j' \<ge> entry M 0 (j0 + ?k)"
  proof (intro allI impI)
    fix j' assume a: "j0 \<le> j' \<and> j' < j0 + ?k"
    let ?j = "j' - j0"
    have jk: "?j < ?k" using a by linarith
    hence jN: "?j < Lng ?N" using kN by simp
    have "entry ?N 0 ?j \<ge> entry ?N 0 ?k" using lmin jk by blast
    moreover have "entry ?N 0 ?j = entry M 0 j'" using jN a by (simp add: entry_seg)
    ultimately show "entry M 0 j' \<ge> entry M 0 (j0 + ?k)" using ek by simp
  qed
  \<comment> \<open>\<open>M\<close> is mono, so \<open>(0,0) \<le>\<^sub>M (0, Lng M - 1)\<close>, hence \<open>entry M 0 0 < entry M 0 (j0+?k)\<close>.\<close>
  have le00: "leR M 0 0 (Lng M - 1)" using monoM by (simp add: monoT_def)
  have lt0: "entry M 0 0 < entry M 0 (j0 + ?k)"
  proof (rule m_5_1_ancestor_basic_1[OF MT _ _ le00])
    show "0 < j0 + ?k" using assms(2) by simp
    show "j0 + ?k \<le> Lng M - 1" using kabsLM by simp
  qed
  \<comment> \<open>A row-0 parent of \<open>j0+?k\<close> exists in \<open>M\<close>.\<close>
  obtain p where p: "0 \<le> p" "p < j0 + ?k" "nextR M 0 p (j0 + ?k)"
    using m_5_1_parent_exists_1[OF MT _ kabsLM lt0] assms(2) by auto
  have ex1: "\<exists>!j0'. nextR M 0 j0' (j0 + ?k)"
    using p(3) idxsum_ex1_parent0_iff by metis
  hence hp: "hasParent M 0 (j0 + ?k)" by (simp add: hasParent_def)
  \<comment> \<open>\<open>parent\<close> is exactly \<open>p\<close>, and \<open>p < j0\<close> since all of \<open>[j0,j0+?k)\<close> are \<open>\<ge>\<close>.\<close>
  have parent_eq: "parent M 0 (j0 + ?k) = p"
    unfolding parent_def using p(3) ex1
    by (rule the1_equality[rotated])
  have pval: "entry M 0 p < entry M 0 (j0 + ?k)"
    using p(3) by (auto simp: nextR_def nextrel0_def)
  have plt: "p < j0"
  proof (rule ccontr)
    assume "\<not> p < j0"
    hence "j0 \<le> p" by simp
    hence "entry M 0 p \<ge> entry M 0 (j0 + ?k)" using lminM p(2) by simp
    thus False using pval by simp
  qed
  show ?thesis using hp parent_eq plt by simp
qed


text \<open>The trunk-right-end set is bounded by \<open>Lng M - 1\<close> and contains \<open>0\<close>, so
  \<open>TrMax M\<close> is well-defined and \<open>\<le> Lng M - 1\<close>.\<close>

lemma TrMax_bound:
  assumes "M \<in> T_PS"
  shows "TrMax M \<le> Lng M - 1"
proof -
  let ?S = "{j. \<forall>j'<j. nextR M 1 j' (j' + 1)}"
  have LM: "Lng M > 0" using assms by (cases M) (auto simp: T_PS_def)
  \<comment> \<open>\<open>?S \<subseteq> {..Lng M - 1}\<close>: any \<open>j > Lng M - 1\<close> fails at \<open>j' = Lng M - 1\<close>.\<close>
  have sub: "?S \<subseteq> {..Lng M - 1}"
  proof
    fix j assume "j \<in> ?S"
    hence H: "\<forall>j'<j. nextR M 1 j' (j' + 1)" by simp
    show "j \<in> {..Lng M - 1}"
    proof (rule ccontr)
      assume "j \<notin> {..Lng M - 1}"
      hence "Lng M - 1 < j" by simp
      hence "nextR M 1 (Lng M - 1) ((Lng M - 1) + 1)" using H by blast
      hence "(Lng M - 1) + 1 < Lng M" by (simp add: nextR_def nextrel1_def)
      thus False using LM by simp
    qed
  qed
  hence fin: "finite ?S" by (rule finite_subset) simp
  have z: "0 \<in> ?S" by simp
  hence ne: "?S \<noteq> {}" by blast
  have "TrMax M = Max ?S" by (simp add: TrMax_def)
  also have "Max ?S \<le> Lng M - 1"
  proof -
    have "Max ?S \<in> ?S" using fin ne by (rule Max_in)
    thus ?thesis using sub by auto
  qed
  finally show ?thesis .
qed

text \<open>m: 命題（\<open>FirstNodes\<close>と\<open>TrMax\<close>と\<open>Joints\<close>の関係） — discharges
  @{thm [source] p_6_4_FirstNodes_TrMax_Joints} (statement rendered with
  \<open>J < Lng (Br M)\<close>).  The joint of a branch component is the row-0 parent of its
  first node, which by @{thm [source] m_6_4_mono_slice_next} lies in the trunk
  (\<open>< TrMax M + 1\<close>); its first node lies strictly right of the trunk.\<close>

lemma m_6_4_FirstNodes_TrMax_Joints:
  assumes M: "M \<in> PT_PS" and J: "J < Lng (Br M)"
  shows "Joints M ! J \<le> TrMax M \<and> TrMax M < FirstNodes M ! J"
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
  have brQ: "Br M = P (seg M (TrMax M + 1) (Lng M - 1))"
    using trne by (simp add: Br_def)
  let ?j0 = "TrMax M + 1"
  let ?Q = "P (seg M ?j0 (Lng M - 1))"
  \<comment> \<open>\<open>FirstNodes M ! J = ?j0 + IdxSum (Br M) ! J\<close>\<close>
  have JIdx: "J < length (IdxSum (Br M))" using J by (simp add: IdxSum_def)
  have fnJ: "FirstNodes M ! J = ?j0 + IdxSum (Br M) ! J"
    using JIdx by (simp add: FirstNodes_def)
  \<comment> \<open>apply \<open>m_6_4_mono_slice_next\<close> at \<open>j0 = TrMax M + 1\<close>\<close>
  have lenQ: "Lng ?Q = Lng (Br M)" using brQ by simp
  have Jle: "J \<le> Lng ?Q - 1" using J lenQ by linarith
  from m_6_4_mono_slice_next[OF M _ _ Jle] trlt
  have hp: "hasParent M 0 (?j0 + IdxSum ?Q ! J)"
    and plt: "parent M 0 (?j0 + IdxSum ?Q ! J) < ?j0" by auto
  have idx_fn: "?j0 + IdxSum ?Q ! J = FirstNodes M ! J"
    using fnJ by (simp add: brQ)
  \<comment> \<open>\<open>Joints M ! J\<close> is exactly this parent\<close>
  have joints_parent: "Joints M ! J = parent M 0 (FirstNodes M ! J)"
    using J by (simp add: Joints_def parent_def)
  have "Joints M ! J \<le> TrMax M"
    using plt joints_parent idx_fn by simp
  moreover have "TrMax M < FirstNodes M ! J" using fnJ by simp
  ultimately show ?thesis ..
qed


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

text \<open>m: 系（\<open>FirstNodes\<close>と\<open>Joints\<close>の単調性）の主要部 (parts (1),(2),(3)) —
  \<open>FirstNodes\<close> increasing, \<open>Joints\<close> decreasing (non-strict), row-0 entries at
  \<open>FirstNodes\<close> decreasing.  Part (2) here is the non-strict form, which is all
  that \<open>m_6_4_mono_slice\<close> needs.\<close>

lemma m_6_4_FirstNodes_Joints_mono_aux:
  assumes M: "M \<in> PT_PS" and lt: "J0' < J1'" and J1: "J1' < Lng (Br M)"
  shows "FirstNodes M ! J0' \<le> FirstNodes M ! J1'
       \<and> Joints M ! J0' \<ge> Joints M ! J1'
       \<and> entry M 0 (FirstNodes M ! J0') \<ge> entry M 0 (FirstNodes M ! J1')"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have J0L: "J0' < length (Br M)" using lt J1 by simp
  have J1L: "J1' < length (Br M)" using J1 by simp
  have J0le: "J0' \<le> J1'" using lt by simp
  \<comment> \<open>(1) FirstNodes increasing\<close>
  have idxmono: "IdxSum (Br M) ! J0' \<le> IdxSum (Br M) ! J1'"
    by (rule idxsum_mono[OF J0le less_imp_le_nat[OF J1L]])
  have fn0: "FirstNodes M ! J0' = TrMax M + 1 + IdxSum (Br M) ! J0'"
    by (rule FirstNodes_nth[OF J0L])
  have fn1: "FirstNodes M ! J1' = TrMax M + 1 + IdxSum (Br M) ! J1'"
    by (rule FirstNodes_nth[OF J1L])
  have part1: "FirstNodes M ! J0' \<le> FirstNodes M ! J1'"
    using fn0 fn1 idxmono by simp
  \<comment> \<open>(3) row-0 entries at FirstNodes decreasing, via \<open>m_6_4_P_leftend_mono\<close>\<close>
  have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
  have trne: "TrMax M \<noteq> Lng M - 1"
  proof
    assume "TrMax M = Lng M - 1"
    hence "Br M = []" by (simp add: Br_def)
    with J1 show False by simp
  qed
  with tb have trlt: "TrMax M < Lng M - 1" by linarith
  let ?N = "seg M (TrMax M + 1) (Lng M - 1)"
  have brQ: "Br M = P ?N" using trne by (simp add: Br_def)
  have NLpos: "Lng ?N > 0" using trlt by simp
  have Nne: "?N \<noteq> []" using NLpos length_greater_0_conv by blast
  have NT: "?N \<in> T_PS" using Nne by (simp add: T_PS_def)
  have J1Q: "J1' \<le> Lng (P ?N) - 1" using J1L brQ by (cases "P ?N") auto
  have leftend: "entry ((P ?N) ! J0') 0 0 \<ge> entry ((P ?N) ! J1') 0 0"
    by (rule m_6_4_P_leftend_mono[OF NT J0le J1Q])
  have ec0: "entry M 0 (FirstNodes M ! J0') = entry (Br M ! J0') 0 0"
    by (rule entry_FirstNodes_eq_component[OF M J0L])
  have ec1: "entry M 0 (FirstNodes M ! J1') = entry (Br M ! J1') 0 0"
    by (rule entry_FirstNodes_eq_component[OF M J1L])
  have part3: "entry M 0 (FirstNodes M ! J0') \<ge> entry M 0 (FirstNodes M ! J1')"
    using ec0 ec1 leftend brQ by simp
  \<comment> \<open>(2) Joints decreasing (non-strict): \<open>a1\<close> is a row-0 ancestor of \<open>f0\<close>,
      hence \<open>\<le> a0 = parent M 0 f0\<close>.\<close>
  let ?f0 = "FirstNodes M ! J0'"
  let ?f1 = "FirstNodes M ! J1'"
  let ?a0 = "Joints M ! J0'"
  let ?a1 = "Joints M ! J1'"
  have a0_eq: "?a0 = parent M 0 ?f0" by (rule Joints_nth[OF J0L])
  have a1_eq: "?a1 = parent M 0 ?f1" by (rule Joints_nth[OF J1L])
  \<comment> \<open>parents exist and lie in the trunk\<close>
  have tj0: "Joints M ! J0' \<le> TrMax M \<and> TrMax M < FirstNodes M ! J0'"
    by (rule m_6_4_FirstNodes_TrMax_Joints[OF M J0L])
  have tj1: "Joints M ! J1' \<le> TrMax M \<and> TrMax M < FirstNodes M ! J1'"
    by (rule m_6_4_FirstNodes_TrMax_Joints[OF M J1L])
  have a0tr: "?a0 \<le> TrMax M" and trf0: "TrMax M < ?f0" using tj0 by simp_all
  have a1tr: "?a1 \<le> TrMax M" and trf1: "TrMax M < ?f1" using tj1 by simp_all
  \<comment> \<open>get the actual \<open>nextR\<close> facts for the two parents\<close>
  have brQne: "length (P ?N) > 0" using P_nonempty by auto
  have J0Q': "J0' \<le> Lng (P ?N) - 1" using J0L brQ by (cases "P ?N") auto
  have hp0: "hasParent M 0 (TrMax M + 1 + IdxSum (P ?N) ! J0')
           \<and> parent M 0 (TrMax M + 1 + IdxSum (P ?N) ! J0') < TrMax M + 1"
    using m_6_4_mono_slice_next[OF M _ _ J0Q'] trlt by auto
  have hp1: "hasParent M 0 (TrMax M + 1 + IdxSum (P ?N) ! J1')
           \<and> parent M 0 (TrMax M + 1 + IdxSum (P ?N) ! J1') < TrMax M + 1"
    using m_6_4_mono_slice_next[OF M _ _ J1Q] trlt by auto
  have idx0: "TrMax M + 1 + IdxSum (P ?N) ! J0' = ?f0" using fn0 brQ by simp
  have idx1: "TrMax M + 1 + IdxSum (P ?N) ! J1' = ?f1" using fn1 brQ by simp
  have hpf0: "hasParent M 0 ?f0" using hp0 idx0 by simp
  have hpf1: "hasParent M 0 ?f1" using hp1 idx1 by simp
  have nx0: "nextR M 0 ?a0 ?f0"
  proof -
    have "\<exists>!j0. nextR M 0 j0 ?f0" using hpf0 by (simp add: hasParent_def)
    hence "nextR M 0 (THE j0. nextR M 0 j0 ?f0) ?f0" by (rule theI')
    thus ?thesis using a0_eq by (simp add: parent_def)
  qed
  have nx1: "nextR M 0 ?a1 ?f1"
  proof -
    have "\<exists>!j0. nextR M 0 j0 ?f1" using hpf1 by (simp add: hasParent_def)
    hence "nextR M 0 (THE j0. nextR M 0 j0 ?f1) ?f1" by (rule theI')
    thus ?thesis using a1_eq by (simp add: parent_def)
  qed
  \<comment> \<open>\<open>a1 < f1\<close>, \<open>entry M 0 a1 < entry M 0 f1\<close>\<close>
  from nx1 have a1f1: "?a1 < ?f1" and ea1: "entry M 0 ?a1 < entry M 0 ?f1"
    by (simp_all add: nextR_def nextrel0_def)
  \<comment> \<open>\<open>leR M 0 a1 f1\<close>, then by the tree, \<open>leR M 0 a1 f0\<close> (since \<open>a1 \<le> f0 \<le> f1\<close>)\<close>
  have lea1f1: "leR M 0 ?a1 ?f1"
    using nx1 a1f1 by (auto simp: nextR_def leR_def le0_def nextrel0_def)
  have a1lef0: "?a1 \<le> ?f0" using a1tr trf0 by simp
  have f0lef1: "?f0 \<le> ?f1" using part1 by simp
  have lea1f0: "leR M 0 ?a1 ?f0"
    by (rule m_5_1_ancestor_tree_1[OF MT lea1f1 a1lef0 f0lef1])
  \<comment> \<open>\<open>a1\<close> is below \<open>f0\<close> with smaller row-0 entry, so \<open>a1 \<le> parent M 0 f0 = a0\<close>\<close>
  have a1ltf0: "?a1 < ?f0" using a1tr trf0 by simp
  have ea1f0: "entry M 0 ?a1 < entry M 0 ?f0"
    by (rule m_5_1_ancestor_basic_1[OF MT a1ltf0 le_refl lea1f0])
  have part2: "?a0 \<ge> ?a1"
    using nextR0_largest_below[OF nx0 a1ltf0 ea1f0] by simp
  show ?thesis using part1 part2 part3 by blast
qed

text \<open>m: 系（\<open>FirstNodes\<close>と\<open>Joints\<close>の単調性） — discharges the corrected
  @{thm [source] p_6_4_FirstNodes_Joints_mono} (parts (1)(2)(3); the article's
  strict part (4) is false, correction A3).  Identical to
  @{thm [source] m_6_4_FirstNodes_Joints_mono_aux}.\<close>

lemma m_6_4_FirstNodes_Joints_mono:
  assumes "M \<in> PT_PS" "J0' < J1'" "J1' < Lng (Br M)"
  shows "FirstNodes M ! J0' \<le> FirstNodes M ! J1'
       \<and> Joints M ! J0' \<ge> Joints M ! J1'
       \<and> entry M 0 (FirstNodes M ! J0') \<ge> entry M 0 (FirstNodes M ! J1')"
  by (rule m_6_4_FirstNodes_Joints_mono_aux[OF assms])

text \<open>The defining property of the trunk: every step below \<open>TrMax M\<close> is a row-1
  \<open><\<^sup>Next\<close>-edge.\<close>

lemma TrMax_trunk_step:
  assumes "M \<in> T_PS" "j' < TrMax M"
  shows "nextR M 1 j' (j' + 1)"
proof -
  let ?S = "{j. \<forall>j'<j. nextR M 1 j' (j' + 1)}"
  have LM: "Lng M > 0" using assms(1) by (cases M) (auto simp: T_PS_def)
  have sub: "?S \<subseteq> {..Lng M - 1}"
  proof
    fix j assume "j \<in> ?S"
    hence H: "\<forall>j'<j. nextR M 1 j' (j' + 1)" by simp
    show "j \<in> {..Lng M - 1}"
    proof (rule ccontr)
      assume "j \<notin> {..Lng M - 1}"
      hence "Lng M - 1 < j" by simp
      hence "nextR M 1 (Lng M - 1) ((Lng M - 1) + 1)" using H by blast
      hence "(Lng M - 1) + 1 < Lng M" by (simp add: nextR_def nextrel1_def)
      thus False using LM by simp
    qed
  qed
  hence fin: "finite ?S" by (rule finite_subset) simp
  have ne: "?S \<noteq> {}" by blast
  have "Max ?S \<in> ?S" using fin ne by (rule Max_in)
  hence "\<forall>j'<Max ?S. nextR M 1 j' (j' + 1)" by simp
  moreover have "TrMax M = Max ?S" by (simp add: TrMax_def)
  ultimately show ?thesis using assms(2) by simp
qed

text \<open>Trunk ancestry in row 1: any \<open>a \<le> b \<le> TrMax M\<close> are row-1 related.\<close>

lemma trunk_le1:
  assumes "M \<in> T_PS" "a \<le> b" "b \<le> TrMax M"
  shows "leR M 1 a b"
proof -
  have LM: "Lng M > 0" using assms(1) by (cases M) (auto simp: T_PS_def)
  have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF assms(1)])
  have "(nextrel1 M)\<^sup>*\<^sup>* a b" using assms(2,3)
  proof (induction b)
    case 0 thus ?case by simp
  next
    case (Suc b)
    show ?case
    proof (cases "a = Suc b")
      case True thus ?thesis by simp
    next
      case False
      with Suc.prems(1) have ab: "a \<le> b" by simp
      have bT: "b < TrMax M" using Suc.prems(2) by simp
      have "(nextrel1 M)\<^sup>*\<^sup>* a b" using Suc.IH[OF ab] bT by simp
      moreover have "nextrel1 M b (Suc b)"
        using TrMax_trunk_step[OF assms(1) bT] by (simp add: nextR_def)
      ultimately show ?thesis by simp
    qed
  qed
  moreover have "a < Lng M" using assms(2,3) tb LM by linarith
  moreover have "b < Lng M" using assms(3) tb LM by linarith
  ultimately show ?thesis by (simp add: leR_def le1_def)
qed

text \<open>Trunk ancestry in row 0 (a consequence of \<open>trunk_le1\<close>).\<close>

lemma trunk_le0:
  assumes "M \<in> T_PS" "a \<le> b" "b \<le> TrMax M"
  shows "leR M 0 a b"
  using m_le1_imp_le0[OF trunk_le1[OF assms]] .

text \<open>For \<open>k < IdxSum Q ! (length Q)\<close> there is a unique block index \<open>J\<close> with
  \<open>IdxSum Q ! J \<le> k < IdxSum Q ! (J + 1)\<close>.\<close>

lemma idxsum_locate:
  assumes "k < IdxSum Q ! (length Q)"
  shows "\<exists>J < length Q. IdxSum Q ! J \<le> k \<and> k < IdxSum Q ! (J + 1)"
proof -
  let ?S = "{J. J \<le> length Q \<and> IdxSum Q ! J \<le> k}"
  have z: "IdxSum Q ! 0 = 0" by (simp add: idxsum_nth)
  hence z0: "0 \<in> ?S" by simp
  have fin: "finite ?S" by (auto intro: finite_subset[of ?S "{..length Q}"])
  have ne: "?S \<noteq> {}" using z0 by blast
  let ?J = "Max ?S"
  have inS: "?J \<in> ?S" using fin ne by (rule Max_in)
  hence Jle: "?J \<le> length Q" and JIdx: "IdxSum Q ! ?J \<le> k" by auto
  have Jlt: "?J < length Q"
  proof (cases "?J = length Q")
    case True
    hence "IdxSum Q ! (length Q) \<le> k" using JIdx by simp
    thus ?thesis using assms by simp
  next
    case False thus ?thesis using Jle by simp
  qed
  have "k < IdxSum Q ! (?J + 1)"
  proof (rule ccontr)
    assume "\<not> k < IdxSum Q ! (?J + 1)"
    hence "IdxSum Q ! (?J + 1) \<le> k" by simp
    hence "?J + 1 \<in> ?S" using Jlt by simp
    hence "?J + 1 \<le> ?J" by (rule Max_ge[OF fin])
    thus False by simp
  qed
  thus ?thesis using Jlt JIdx by blast
qed

text \<open>Within a branch component, the left end is a row-0 ancestor of every later
  index of that component (translated back to \<open>M\<close>).  For \<open>TrMax M < k \<le> Lng M - 1\<close>
  this yields a branch index \<open>J\<close> with \<open>leR M 0 (FirstNodes M ! J) k\<close>.\<close>

lemma branch_component_le0:
  assumes M: "M \<in> PT_PS" and ktr: "TrMax M < k" and kL: "k \<le> Lng M - 1"
  shows "\<exists>J < length (Br M). leR M 0 (FirstNodes M ! J) k"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
  have trlt: "TrMax M < Lng M - 1" using ktr kL by linarith
  let ?N = "seg M (TrMax M + 1) (Lng M - 1)"
  have brQ: "Br M = P ?N" using trlt by (simp add: Br_def)
  have NL: "Lng ?N = Lng M - 1 - TrMax M" using trlt by simp
  have NLpos: "Lng ?N > 0" using trlt by simp
  have Nne: "?N \<noteq> []" using NLpos length_greater_0_conv by blast
  have NT: "?N \<in> T_PS" using Nne by (simp add: T_PS_def)
  have LMlt: "Lng M - 1 < Lng M" using trlt by linarith
  let ?Q = "P ?N"
  let ?kp = "k - (TrMax M + 1)"
  have kpN: "?kp < Lng ?N" using ktr kL NL by linarith
  \<comment> \<open>\<open>IdxSum ?Q ! (length ?Q) = Lng ?N\<close>\<close>
  have total: "IdxSum ?Q ! (length ?Q) = Lng ?N"
  proof -
    have "IdxSum ?Q ! (length ?Q) = sum_list (map length (take (length ?Q) ?Q))"
      by (simp add: idxsum_nth)
    also have "\<dots> = sum_list (map length ?Q)" by simp
    also have "\<dots> = length (concat ?Q)" by (simp add: length_concat)
    also have "concat ?Q = ?N" by (rule idxsum_concat_P)
    finally show ?thesis by simp
  qed
  have kplt: "?kp < IdxSum ?Q ! (length ?Q)" using kpN total by simp
  obtain J where J: "J < length ?Q" "IdxSum ?Q ! J \<le> ?kp"
    "?kp < IdxSum ?Q ! (J + 1)"
    using idxsum_locate[OF kplt] by blast
  let ?a = "IdxSum ?Q ! J"
  let ?b = "IdxSum ?Q ! (J + 1) - 1"
  have Jle: "J \<le> Lng ?Q - 1" using J(1) by simp
  have comp: "?Q ! J = seg ?N ?a ?b" by (rule m_6_4_P_IdxSum[OF NT Jle])
  have lenpos: "0 < Lng (?Q ! J)" by (rule idxsum_P_component_nonempty[OF NT J(1)])
  have diff: "IdxSum ?Q ! (J + 1) = ?a + length (?Q ! J)" by (rule idxsum_diff[OF J(1)])
  have bge: "?kp \<le> ?b" using J(3) diff lenpos by linarith
  \<comment> \<open>row-0 ancestry from the component's left end to \<open>?kp\<close>, inside \<open>?N\<close>\<close>
  have leNa: "leR ?N 0 ?a ?kp"
  proof (cases "?a = ?kp")
    case True
    have aN: "?a < Lng ?N" using J(2) kpN by simp
    thus ?thesis using True by (simp add: leR_def le0_def)
  next
    case False
    with J(2) have altkp: "?a < ?kp" by simp
    let ?C = "?Q ! J"
    have CinP: "?C \<in> set ?Q" using J(1) by (rule nth_mem)
    have Czm: "zeroT ?C \<or> monoT ?C" using m_6_2_P_components_1[OF NT] CinP by blast
    have aN: "?a < Lng ?N" using J(2) kpN by simp
    have bN: "?b < Lng ?N"
    proof -
      have "IdxSum ?Q ! (J + 1) \<le> IdxSum ?Q ! (length ?Q)"
        by (rule idxsum_mono[OF _ order.refl]) (use J(1) in simp)
      hence "IdxSum ?Q ! (J + 1) \<le> Lng ?N" using total by simp
      thus ?thesis using NLpos by linarith
    qed
    \<comment> \<open>local position \<open>p = ?kp - ?a\<close> inside the component \<open>?C = seg ?N ?a ?b\<close>\<close>
    let ?p = "?kp - ?a"
    have ppos: "0 < ?p" using altkp by simp
    have CL: "Lng ?C = Suc ?b - ?a" using comp by simp
    have pb: "?p \<le> Lng ?C - 1" using bge CL altkp J(2) by linarith
    have Cgt1: "Lng ?C > 1" using ppos pb by linarith
    \<comment> \<open>so \<open>?C\<close> is monoT (not zeroT, since \<open>Lng > 1\<close>)\<close>
    have Cmono: "monoT ?C" using Czm Cgt1 by (auto simp: zeroT_def)
    have leC: "leR ?C 0 0 (Lng ?C - 1)" using Cmono by (simp add: monoT_def)
    have CTPS: "?C \<in> T_PS" using Cgt1 by (cases ?C) (auto simp: T_PS_def)
    have le0I: "(0::nat) \<le> ?p" by simp
    have leCp: "leR ?C 0 0 ?p"
      by (rule m_5_1_ancestor_tree_1[OF CTPS leC le0I pb])
    \<comment> \<open>translate component-le0 to \<open>?N\<close>-le0\<close>
    have le0C: "le0 ?C 0 ?p" using leCp by (simp add: leR_def)
    have aux: "le0 (seg ?N ?a ?b) 0 ?p = le0 ?N (?a + 0) (?a + ?p)"
    proof (rule adm_le0_seg)
      show "?b < Lng ?N" using bN .
      show "0 \<le> ?b - ?a" by simp
      show "?p \<le> ?b - ?a" using pb CL by simp
      show "?a \<le> ?b" using altkp bge by linarith
    qed
    have "le0 ?N ?a (?a + ?p)" using le0C comp aux by simp
    moreover have "?a + ?p = ?kp" using altkp J(2) by simp
    ultimately show ?thesis by (simp add: leR_def)
  qed
  \<comment> \<open>translate \<open>?N\<close>-le0 to \<open>M\<close>-le0\<close>
  have leMa: "leR M 0 (TrMax M + 1 + ?a) (TrMax M + 1 + ?kp)"
  proof -
    have le0N: "le0 ?N ?a ?kp" using leNa by (simp add: leR_def)
    have aN: "?a \<le> Lng ?N - 1" using J(2) kpN by linarith
    have eq: "le0 ?N ?a ?kp = le0 M (TrMax M + 1 + ?a) (TrMax M + 1 + ?kp)"
    proof (rule adm_le0_seg)
      show "Lng M - 1 < Lng M" using LMlt .
      show "?a \<le> Lng M - 1 - (TrMax M + 1)" using aN NL by simp
      show "?kp \<le> Lng M - 1 - (TrMax M + 1)" using kpN NL by simp
      show "TrMax M + 1 \<le> Lng M - 1" using trlt by simp
    qed
    have "le0 M (TrMax M + 1 + ?a) (TrMax M + 1 + ?kp)" using le0N eq by simp
    thus ?thesis by (simp add: leR_def)
  qed
  have JBr: "J < length (Br M)" using J(1) brQ by simp
  have fn: "FirstNodes M ! J = TrMax M + 1 + ?a" using FirstNodes_nth[OF JBr] brQ by simp
  have kk: "TrMax M + 1 + ?kp = k" using ktr by simp
  have "leR M 0 (FirstNodes M ! J) k" using leMa fn kk by simp
  thus ?thesis using JBr by blast
qed

text \<open>Core of \<open>m_6_4_mono_slice\<close>: for \<open>j0'\<close> a (weak) ancestor of the last joint,
  every index \<open>k\<close> with \<open>j0' < k \<le> Lng M - 1\<close> is a row-0 descendant of \<open>j0'\<close>.\<close>

lemma slice_le0_to_index:
  assumes M: "M \<in> PT_PS" and brne: "Br M \<noteq> []"
    and j0le: "j0' \<le> Joints M ! (Lng (Br M) - 1)"
    and lt: "j0' < k" and kL: "k \<le> Lng M - 1"
  shows "leR M 0 j0' k"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  let ?last = "Lng (Br M) - 1"
  have lastL: "?last < Lng (Br M)" using brne by (cases "Br M") auto
  \<comment> \<open>the last joint is in the trunk\<close>
  have lastTr: "Joints M ! ?last \<le> TrMax M"
    using m_6_4_FirstNodes_TrMax_Joints[OF M lastL] by simp
  have j0Tr: "j0' \<le> TrMax M" using j0le lastTr by simp
  show ?thesis
  proof (cases "k \<le> TrMax M")
    case True
    \<comment> \<open>Case A: \<open>k\<close> is in the trunk.\<close>
    show ?thesis by (rule trunk_le0[OF MT less_imp_le_nat[OF lt] True])
  next
    case False
    \<comment> \<open>Case B: \<open>k\<close> is in a branch component.\<close>
    hence ktr: "TrMax M < k" by simp
    obtain J where JBr: "J < length (Br M)"
      and leFNk: "leR M 0 (FirstNodes M ! J) k"
      using branch_component_le0[OF M ktr kL] by blast
    \<comment> \<open>\<open>nextR M 0 (Joints M ! J) (FirstNodes M ! J)\<close>\<close>
    have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
    have trne: "TrMax M \<noteq> Lng M - 1"
    proof
      assume "TrMax M = Lng M - 1"
      hence "Br M = []" by (simp add: Br_def)
      with brne show False by simp
    qed
    with tb have trlt: "TrMax M < Lng M - 1" by linarith
    let ?N = "seg M (TrMax M + 1) (Lng M - 1)"
    have brQ: "Br M = P ?N" using trne by (simp add: Br_def)
    have JQ: "J \<le> Lng (P ?N) - 1" using JBr brQ by (cases "P ?N") auto
    have hp: "hasParent M 0 (TrMax M + 1 + IdxSum (P ?N) ! J)"
      using m_6_4_mono_slice_next[OF M _ _ JQ] trlt by auto
    have fnJ: "TrMax M + 1 + IdxSum (P ?N) ! J = FirstNodes M ! J"
      using FirstNodes_nth[OF JBr] brQ by simp
    have hpf: "hasParent M 0 (FirstNodes M ! J)" using hp fnJ by simp
    have aJ_eq: "Joints M ! J = parent M 0 (FirstNodes M ! J)" by (rule Joints_nth[OF JBr])
    have nxJ: "nextR M 0 (Joints M ! J) (FirstNodes M ! J)"
    proof -
      have "\<exists>!j0. nextR M 0 j0 (FirstNodes M ! J)" using hpf by (simp add: hasParent_def)
      hence "nextR M 0 (THE j0. nextR M 0 j0 (FirstNodes M ! J)) (FirstNodes M ! J)"
        by (rule theI')
      thus ?thesis using aJ_eq by (simp add: parent_def)
    qed
    \<comment> \<open>\<open>Joints M ! J \<le> TrMax M\<close> and \<open>Joints M ! ?last \<le> Joints M ! J\<close>\<close>
    have aJTr: "Joints M ! J \<le> TrMax M"
      using m_6_4_FirstNodes_TrMax_Joints[OF M JBr] by simp
    have JleLast: "J \<le> ?last" using JBr by simp
    have lastLeaJ: "Joints M ! ?last \<le> Joints M ! J"
    proof (cases "J = ?last")
      case True thus ?thesis by simp
    next
      case False
      with JleLast have "J < ?last" by simp
      thus ?thesis
        using m_6_4_FirstNodes_Joints_mono_aux[OF M _ lastL] by simp
    qed
    have j0leaJ: "j0' \<le> Joints M ! J" using j0le lastLeaJ by simp
    \<comment> \<open>chain \<open>j0' \<le> Joints!J <\<^sup>Next FirstNodes!J \<le> k\<close>\<close>
    have le1: "leR M 0 j0' (Joints M ! J)"
      by (rule trunk_le0[OF MT j0leaJ aJTr])
    have leFN: "leR M 0 (Joints M ! J) (FirstNodes M ! J)"
      using nxJ by (auto simp: nextR_def leR_def le0_def nextrel0_def)
    have "le0 M j0' (FirstNodes M ! J)"
      using le0_trans[of M j0' "Joints M ! J" "FirstNodes M ! J"]
            le1 leFN by (simp add: leR_def)
    hence "le0 M j0' k"
      using le0_trans[of M j0' "FirstNodes M ! J" k] leFNk by (simp add: leR_def)
    thus ?thesis by (simp add: leR_def)
  qed
qed

text \<open>m: 系（単項性の切片への遺伝性, §6.4 version） — discharges
  @{thm [source] p_6_4_mono_slice}.\<close>

lemma m_6_4_mono_slice:
  assumes M: "M \<in> PT_PS" and lt: "j0' < j1'" and j1L: "j1' \<le> Lng M - 1"
    and j0le: "j0' \<le> Joints M ! (Lng (Br M) - 1)"
  shows "monoT (seg M j0' j1')"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have LM: "Lng M > 0" using MT by (cases M) (auto simp: T_PS_def)
  have j1lt: "j1' < Lng M" using j1L LM by linarith
  show ?thesis
  proof (cases "Br M = []")
    case True
    \<comment> \<open>Degenerate trunk-only case: \<open>TrMax M = Lng M - 1\<close>, so the whole sequence is
        the trunk and \<open>leR M 0 0 (Lng M - 1)\<close> already holds; the slice is mono.\<close>
    have trmax: "TrMax M = Lng M - 1"
    proof (rule ccontr)
      assume "TrMax M \<noteq> Lng M - 1"
      hence "Br M = P (seg M (TrMax M + 1) (Lng M - 1))" by (simp add: Br_def)
      moreover have "P (seg M (TrMax M + 1) (Lng M - 1)) \<noteq> []" by (rule P_nonempty)
      ultimately show False using True by simp
    qed
    have le: "leR M 0 j0' j1'"
    proof (rule m_5_1_parent_exists_3[OF MT lt j1lt])
      fix kk assume k: "j0' < kk" "kk \<le> j1'"
      hence kL: "kk \<le> Lng M - 1" using j1L by simp
      hence kTr: "kk \<le> TrMax M" using trmax by simp
      have "leR M 0 j0' kk" by (rule trunk_le0[OF MT less_imp_le_nat[OF k(1)] kTr])
      thus "entry M 0 j0' < entry M 0 kk"
        by (rule m_5_1_ancestor_basic_1[OF MT k(1) order.refl])
    qed
    show ?thesis by (rule m_6_2_mono_ancestor_slice[OF MT lt le])
  next
    case False
    have le: "leR M 0 j0' j1'"
    proof (rule m_5_1_parent_exists_3[OF MT lt j1lt])
      fix kk assume k: "j0' < kk" "kk \<le> j1'"
      hence kL: "kk \<le> Lng M - 1" using j1L by simp
      have "leR M 0 j0' kk"
        by (rule slice_le0_to_index[OF M False j0le k(1) kL])
      thus "entry M 0 j0' < entry M 0 kk"
        by (rule m_5_1_ancestor_basic_1[OF MT k(1) order.refl])
    qed
    show ?thesis by (rule m_6_2_mono_ancestor_slice[OF MT lt le])
  qed
qed

text \<open>
  Inline helper: row-1 parents are unique (analogous to @{thm idxsum_parent0_unique} for row 0).
\<close>

lemma nextR1_unique:
  assumes "nextR M 1 a j" "nextR M 1 b j"
  shows "a = b"
proof (rule ccontr)
  assume ne: "a \<noteq> b"
  from assms(1) have na: "nextrel1 M a j" by (simp add: nextR_def)
  from assms(2) have nb: "nextrel1 M b j" by (simp add: nextR_def)
  from na have le0aj: "le0 M a j" by (simp add: nextrel1_def)
  from nb have le0bj: "le0 M b j" by (simp add: nextrel1_def)
  from na have ea: "entry M 1 a < entry M 1 j" by (simp add: nextrel1_def)
  from nb have eb: "entry M 1 b < entry M 1 j" by (simp add: nextrel1_def)
  from na have ca: "\<forall>x. a < x \<and> le0 M x j \<longrightarrow> entry M 1 x \<ge> entry M 1 j"
    by (simp add: nextrel1_def)
  from nb have cb: "\<forall>x. b < x \<and> le0 M x j \<longrightarrow> entry M 1 x \<ge> entry M 1 j"
    by (simp add: nextrel1_def)
  from ne consider "a < b" | "b < a" by linarith
  thus False
  proof cases
    case 1
    have "entry M 1 b \<ge> entry M 1 j" using ca 1 le0bj by blast
    with eb show False by simp
  next
    case 2
    have "entry M 1 a \<ge> entry M 1 j" using cb 2 le0aj by blast
    with ea show False by simp
  qed
qed

text \<open>
  Helper: if row-1 has no parent at position j, entry M 1 j = 0 (under condB).
  Proof: by contradiction. If entry M 1 j > 0, find the P-component K containing j.
  Its left-end ?a satisfies: entry M 0 ?a = 0 (from e00 and almin), so ¬ hasParent M 0 ?a,
  hence entry M 1 ?a = 0 by RedCondB. The component is monoT (length > 1 since j > ?a),
  so le0 M ?a j by adm_le0_seg. Then m_5_1_parent_exists_2 yields a row-1 parent of j,
  contradicting nop.
\<close>

lemma condAB_row1_noparent_zero:
  assumes M: "M \<in> T_PS"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and condB: "RedCondB M"
    and j: "j < Lng M" and nop: "\<not> hasParent M 1 j"
  shows "entry M 1 j = 0"
proof (cases "j = 0")
  case True thus ?thesis using e10 by simp
next
  case j0: False
  hence jp: "0 < j" by simp
  show ?thesis
  proof (rule ccontr)
    assume ne: "entry M 1 j \<noteq> 0"
    hence jpos: "0 < entry M 1 j" by simp
    \<comment> \<open>Locate j's component in P M.\<close>
    have total: "IdxSum (P M) ! (length (P M)) = Lng M"
    proof -
      have "IdxSum (P M) ! (length (P M)) = sum_list (map length (P M))"
        by (simp add: idxsum_nth)
      also have "\<dots> = length (concat (P M))" by (simp add: length_concat)
      also have "concat (P M) = M" by (rule idxsum_concat_P)
      finally show ?thesis by simp
    qed
    have jlt: "j < IdxSum (P M) ! (length (P M))" using j total by simp
    obtain K where K1: "K < length (P M)"
      and K2: "IdxSum (P M) ! K \<le> j"
      and K3: "j < IdxSum (P M) ! (K + 1)"
      using idxsum_locate[OF jlt] by blast
    let ?a = "IdxSum (P M) ! K"
    have arange: "?a \<le> Lng M - 1"
      using idxsum_leftend_lmin[OF M K1] by blast
    have almin: "\<forall>j' < ?a. entry M 0 j' \<ge> entry M 0 ?a"
      using idxsum_leftend_lmin[OF M K1] by blast
    have LMpos: "0 < Lng M" using j by linarith
    have aL: "?a < Lng M"
    proof -
      have "Suc ?a \<le> Suc (Lng M - 1)" using arange by simp
      also have "Suc (Lng M - 1) = Lng M" using LMpos by simp
      finally show ?thesis by simp
    qed
    have ae0: "entry M 0 ?a = 0"
    proof -
      have "entry M 0 0 \<ge> entry M 0 ?a"
      proof (cases "?a = 0")
        case True thus ?thesis using e00 by simp
      next
        case False hence "0 < ?a" by simp
        thus ?thesis using almin by blast
      qed
      thus ?thesis using e00 by (simp add: antisym)
    qed
    have anopar0: "\<not> hasParent M 0 ?a"
      using idxsum_no_parent0_iff[OF M aL] almin unfolding hasParent_def by blast
    have ae1: "entry M 1 ?a = 0"
    proof -
      have "entry M 0 ?a = entry M 1 ?a"
        using condB anopar0 arange
        unfolding RedCondB_def hasParent_def by blast
      thus ?thesis using ae0 by simp
    qed
    have elt: "entry M 1 ?a < entry M 1 j" using ae1 jpos by simp
    have le0aj: "le0 M ?a j"
    proof (cases "?a = j")
      case True
      thus ?thesis using aL by (simp add: le0_def)
    next
      case False
      hence alt: "?a < j" using K2 by simp
      have CK: "P M ! K \<in> set (P M)" using K1 by (rule nth_mem)
      have Czm: "zeroT (P M ! K) \<or> monoT (P M ! K)"
        using m_6_2_P_components_1[OF M] CK by blast
      have Kle: "K \<le> Lng (P M) - 1" using K1 by (cases "P M") auto
      let ?b = "IdxSum (P M) ! (K + 1) - 1"
      have comp: "P M ! K = seg M ?a ?b"
        by (rule m_6_4_P_IdxSum[OF M Kle])
      have diff: "IdxSum (P M) ! (K + 1) = ?a + length (P M ! K)"
        by (rule idxsum_diff[OF K1])
      have lenpos: "0 < length (P M ! K)"
        by (rule idxsum_P_component_nonempty[OF M K1])
      have bge: "j \<le> ?b" using K3 diff lenpos by linarith
      have bL: "?b < Lng M"
      proof -
        have "IdxSum (P M) ! (K + 1) \<le> IdxSum (P M) ! (length (P M))"
          by (rule idxsum_mono) (use K1 in simp_all)
        hence "IdxSum (P M) ! (K + 1) \<le> Lng M" using total by simp
        thus ?thesis using lenpos diff by linarith
      qed
      have CL: "Lng (P M ! K) = Suc ?b - ?a"
        using comp by simp
      have Cgt1: "Lng (P M ! K) > 1" using alt bge CL by linarith
      have Cmono: "monoT (P M ! K)" using Czm Cgt1 by (auto simp: zeroT_def)
      have CTPS: "P M ! K \<in> T_PS"
        using Cgt1 by (cases "P M ! K") (auto simp: T_PS_def)
      have leCfull: "leR (P M ! K) 0 0 (Lng (P M ! K) - 1)"
        using Cmono by (simp add: monoT_def)
      let ?p = "j - ?a"
      have ppos: "0 < ?p" using alt by simp
      have pb: "?p \<le> Lng (P M ! K) - 1" using bge CL alt by linarith
      have leCp: "leR (P M ! K) 0 0 ?p"
        by (rule m_5_1_ancestor_tree_1[OF CTPS leCfull]) (use pb in linarith, use pb in linarith)
      have le0Cp: "le0 (P M ! K) 0 ?p" using leCp by (simp add: leR_def)
      have le0Cseg: "le0 (seg M ?a ?b) 0 ?p \<longleftrightarrow> le0 M (?a + 0) (?a + ?p)"
      proof (rule adm_le0_seg)
        show "?b < Lng M" using bL .
        show "0 \<le> ?b - ?a" by simp
        show "?p \<le> ?b - ?a" using bge CL alt by linarith
        show "?a \<le> ?b" using alt bge by linarith
      qed
      have aplus: "?a + ?p = j" using alt by simp
      have "le0 M (?a + 0) (?a + ?p)" using le0Cp comp le0Cseg by simp
      hence "le0 M ?a j" using aplus by simp
      thus ?thesis by simp
    qed
    have a_lt_j: "?a < j"
    proof -
      have "?a \<noteq> j"
      proof
        assume eq: "?a = j"
        hence "entry M 1 j = 0" using ae1 by simp
        thus False using jpos by simp
      qed
      thus ?thesis using K2 by linarith
    qed
    have leR0aj: "leR M 0 ?a j" using le0aj by (simp add: leR_def)
    obtain j' where j'range: "?a \<le> j'" "j' < j" and j'par: "nextR M 1 j' j"
      using m_5_1_parent_exists_2[OF M a_lt_j j elt leR0aj] by blast
    have "hasParent M 1 j"
      unfolding hasParent_def
    proof (rule ex_ex1I)
      show "\<exists>j0. nextR M 1 j0 j" using j'par by blast
    next
      fix a b assume "nextR M 1 a j" "nextR M 1 b j"
      thus "a = b" using nextR1_unique by blast
    qed
    with nop show False by simp
  qed
qed

text \<open>
  m: 補題（条件(A)と(B)と係数の基本性質） — discharges @{thm [source] p_6_6_condAB_coeff}
  (§6.6, 補題（条件(A)と(B)と係数の基本性質）).
\<close>

lemma m_6_6_condAB_coeff:
  assumes MT: "M \<in> T_PS" and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and condA: "RedCondA M"
  shows
    "(\<forall>j \<le> Lng M - 1. entry M 0 j \<le> j)
   \<and> (RedCondB M \<longrightarrow> (\<forall>j \<le> Lng M - 1. entry M 0 j \<ge> entry M 1 j))
   \<and> (\<forall>i \<le> 1. (i = 0 \<or> (i = 1 \<and> RedCondB M)) \<longrightarrow>
        (\<forall>j \<le> Lng M - 1.
           (\<exists>j0' j1'. \<not> leR M i j0' j1' \<and> j0' < j1' \<and> j1' \<le> j) \<longrightarrow> entry M i j < j))"
proof -
  have LM: "1 \<le> Lng M" using MT by (cases M) (auto simp: T_PS_def)
  \<comment> \<open>From RedCondA: if hasParent M i j, then entry M i j = entry M i (parent M i j) + 1.\<close>
  have condA_entry: "\<And>i j. i \<le> 1 \<Longrightarrow> j < Lng M \<Longrightarrow> hasParent M i j \<Longrightarrow>
      entry M i (parent M i j) + 1 = entry M i j"
    using condA unfolding RedCondA_def by blast
  \<comment> \<open>parent M i j < j when hasParent M i j.\<close>
  have parent_lt: "\<And>i j. i \<le> 1 \<Longrightarrow> j < Lng M \<Longrightarrow> hasParent M i j \<Longrightarrow> parent M i j < j"
  proof -
    fix i j assume hi: "i \<le> 1" and hj: "j < Lng M" and hp: "hasParent M i j"
    from hp obtain j0 where j0: "nextR M i j0 j"
      unfolding hasParent_def by blast
    have "parent M i j = j0" unfolding parent_def
      using hp j0 by (auto simp: hasParent_def dest: the1_equality)
    moreover have "j0 < j"
      using j0 unfolding nextR_def nextrel0_def nextrel1_def by (auto split: if_splits)
    ultimately show "parent M i j < j" by simp
  qed
  \<comment> \<open>row-0 no-parent implies entry M 0 j = 0.\<close>
  have nopar0_zero: "\<And>j. j < Lng M \<Longrightarrow> \<not> hasParent M 0 j \<Longrightarrow> entry M 0 j = 0"
  proof -
    fix j assume hj: "j < Lng M" and hp: "\<not> hasParent M 0 j"
    have lmin: "\<forall>j' < j. entry M 0 j' \<ge> entry M 0 j"
      using idxsum_no_parent0_iff[OF MT hj] hp unfolding hasParent_def by blast
    have "entry M 0 0 \<ge> entry M 0 j"
    proof (cases "j = 0")
      case True thus ?thesis using e00 by simp
    next
      case False hence "0 < j" by simp
      thus ?thesis using lmin by blast
    qed
    thus "entry M 0 j = 0" using e00 by simp
  qed
  \<comment> \<open>----------- Part 1: entry M 0 j ≤ j for all j < Lng M. -----------\<close>
  have part1: "\<forall>j. j < Lng M \<longrightarrow> entry M 0 j \<le> j"
  proof (intro allI impI)
    fix j assume hjL: "j < Lng M"
    show "entry M 0 j \<le> j"
    using hjL
    proof (induction j rule: less_induct)
      case (less j)
      show "entry M 0 j \<le> j"
      proof (cases "hasParent M 0 j")
        case hp: False
        have "entry M 0 j = 0" using nopar0_zero[OF less.prems] hp by simp
        thus ?thesis by simp
      next
        case hp: True
        let ?p = "parent M 0 j"
        have plt: "?p < j" using parent_lt[of 0 j] hp less.prems by simp
        have pL: "?p < Lng M" using plt less.prems by linarith
        have pind: "entry M 0 ?p \<le> ?p" using less.IH[OF plt pL] .
        have eA: "entry M 0 ?p + 1 = entry M 0 j"
          using condA_entry[of 0 j] hp less.prems by simp
        from pind eA plt show "entry M 0 j \<le> j" by linarith
      qed
    qed
  qed
  \<comment> \<open>----------- Part 2: RedCondB → entry M 0 j ≥ entry M 1 j for all j < Lng M. -----------\<close>
  have part2: "RedCondB M \<longrightarrow> (\<forall>j. j < Lng M \<longrightarrow> entry M 0 j \<ge> entry M 1 j)"
  proof (intro impI allI impI)
    fix j
    assume condB: "RedCondB M" and hjL: "j < Lng M"
    show "entry M 0 j \<ge> entry M 1 j"
    using hjL
    proof (induction j rule: less_induct)
      case (less j)
      show "entry M 0 j \<ge> entry M 1 j"
      proof (cases "hasParent M 1 j")
        case hp1: False
        have "entry M 1 j = 0"
          using condAB_row1_noparent_zero[OF MT e00 e10 condB less.prems hp1] .
        thus ?thesis by simp
      next
        case hp1: True
        let ?p1 = "parent M 1 j"
        have p1lt: "?p1 < j" using parent_lt[of 1 j] hp1 less.prems by simp
        have p1L: "?p1 < Lng M" using p1lt less.prems by linarith
        have e1A: "entry M 1 ?p1 + 1 = entry M 1 j"
          using condA_entry[of 1 j] hp1 less.prems by simp
        have IH1: "entry M 0 ?p1 \<ge> entry M 1 ?p1"
          using less.IH[OF p1lt p1L] .
        have par1: "nextR M 1 ?p1 j"
          using hp1 unfolding hasParent_def parent_def by (rule theI')
        have le0p1j: "le0 M ?p1 j"
          using poper_nextR_imp_le0[OF par1] by (simp add: leR_def)
        have leR0p1j: "leR M 0 ?p1 j" using le0p1j by (simp add: leR_def)
        have e0lt: "entry M 0 ?p1 < entry M 0 j"
          by (rule m_5_1_ancestor_basic_1[OF MT p1lt _ leR0p1j]) simp
        from e1A IH1 e0lt show "entry M 0 j \<ge> entry M 1 j" by linarith
      qed
    qed
  qed
  \<comment> \<open>----------- Part 3: gap ⟹ strict entry bound. -----------\<close>
  have part3: "\<forall>i \<le> 1. (i = 0 \<or> (i = 1 \<and> RedCondB M)) \<longrightarrow>
        (\<forall>j \<le> Lng M - 1.
           (\<exists>j0' j1'. \<not> leR M i j0' j1' \<and> j0' < j1' \<and> j1' \<le> j) \<longrightarrow> entry M i j < j)"
  proof (rule allI, rule impI, rule impI)
    fix i :: nat assume hi: "i \<le> 1" and hcond: "i = 0 \<or> (i = 1 \<and> RedCondB M)"
    \<comment> \<open>Prove the implication for all j simultaneously by strong induction.\<close>
    have key: "\<forall>j. j < Lng M \<longrightarrow>
        (\<exists>j0' j1'. \<not> leR M i j0' j1' \<and> j0' < j1' \<and> j1' \<le> j) \<longrightarrow> entry M i j < j"
    proof (intro allI)
      fix j
      show "j < Lng M \<longrightarrow> (\<exists>j0' j1'. \<not> leR M i j0' j1' \<and> j0' < j1' \<and> j1' \<le> j) \<longrightarrow> entry M i j < j"
      proof (induction j rule: less_induct)
        case (less j)
        show ?case
        proof (intro impI)
          assume hjL: "j < Lng M"
            and gap: "\<exists>j0' j1'. \<not> leR M i j0' j1' \<and> j0' < j1' \<and> j1' \<le> j"
          from gap obtain j0' j1' where
              gap0: "\<not> leR M i j0' j1'" and gap1: "j0' < j1'" and gap2: "j1' \<le> j"
            by blast
          have jpos: "0 < j" using gap1 gap2 by linarith
          \<comment> \<open>Abbreviate the IH for later use.\<close>
          have IH: "\<forall>y < j. y < Lng M \<longrightarrow>
              (\<exists>j0'' j1''. \<not> leR M i j0'' j1'' \<and> j0'' < j1'' \<and> j1'' \<le> y) \<longrightarrow>
              entry M i y < y"
            using less.IH by blast
          show "entry M i j < j"
          proof (cases "hasParent M i j")
            case hp: False
            \<comment> \<open>No parent: entry M i j = 0 < j.\<close>
            show ?thesis
            proof (cases i)
              case i0: 0
              have "entry M 0 j = 0"
                using nopar0_zero[OF hjL] hp i0 by simp
              thus ?thesis using jpos by (simp add: i0)
            next
              case i1: (Suc n)
              have i_eq: "i = 1" using hi i1 by simp
              have condB: "RedCondB M" using hcond i_eq by simp
              have "entry M 1 j = 0"
                using condAB_row1_noparent_zero[OF MT e00 e10 condB hjL] hp i_eq by simp
              thus ?thesis using jpos i_eq by simp
            qed
          next
            case hp: True
            let ?p = "parent M i j"
            have plt: "?p < j" using parent_lt[of i j] hp hjL hi by simp
            have pL: "?p < Lng M" using plt hjL by linarith
            have eA: "entry M i ?p + 1 = entry M i j"
              using condA_entry[of i j] hp hjL hi by simp
            show "entry M i j < j"
            proof (cases "j1' \<le> ?p")
              case True
              \<comment> \<open>Gap entirely in [0..?p]: apply IH to ?p.\<close>
              have gap_p: "\<exists>j0'' j1''. \<not> leR M i j0'' j1'' \<and> j0'' < j1'' \<and> j1'' \<le> ?p"
                using gap0 gap1 True by blast
              have epp: "entry M i ?p < ?p" using IH[rule_format, OF plt pL gap_p] .
              from epp eA plt show "entry M i j < j" by linarith
            next
              case False
              \<comment> \<open>j1' > ?p. Case split on whether ?p < j-1 or ?p = j-1.\<close>
              show ?thesis
              proof (cases "?p < j - 1")
                case ppj1: True
                \<comment> \<open>?p < j-1: entry M i j = entry M i ?p + 1 ≤ ?p + 1 ≤ j-1 < j.\<close>
                have eple: "entry M i ?p \<le> ?p"
                proof (cases i)
                  case 0
                  thus ?thesis using part1 pL by blast
                next
                  case (Suc n)
                  have i_eq: "i = 1" using hi \<open>i = Suc n\<close> by simp
                  have condB: "RedCondB M" using hcond i_eq by simp
                  have e0ge: "entry M 0 ?p \<ge> entry M 1 ?p"
                    using part2 condB pL by blast
                  have e0le: "entry M 0 ?p \<le> ?p" using part1 pL by blast
                  have "entry M 1 ?p \<le> ?p" using e0ge e0le by linarith
                  thus ?thesis using i_eq by simp
                qed
                from eple eA ppj1 show "entry M i j < j" by linarith
              next
                case pj1: False
                \<comment> \<open>?p = j-1. Since j1' > ?p = j-1 and j1' ≤ j, we get j1' = j.\<close>
                hence peq: "?p = j - 1" using plt by linarith
                hence j1'_eq_j: "j1' = j" using False gap2 by linarith
                \<comment> \<open>So ¬leR M i j0' j, j0' < j.\<close>
                have gap0': "\<not> leR M i j0' j" using gap0 j1'_eq_j by simp
                \<comment> \<open>j0' ≤ ?p or j0' > ?p.\<close>
                show ?thesis
                proof (cases "j0' \<le> ?p")
                  case hj0: True
                  \<comment> \<open>j0' ≤ ?p.\<close>
                  have j0'_lt_p: "j0' < ?p"
                  proof -
                    have "j0' \<noteq> ?p"
                    proof
                      assume eq: "j0' = ?p"
                      have par: "nextR M i ?p j"
                        using hp unfolding hasParent_def parent_def by (rule theI')
                      have "leR M i ?p j"
                      proof (cases "i = 0")
                        case True
                        hence nr: "nextrel0 M ?p j" using par by (simp add: nextR_def)
                        have pL: "?p < Lng M" using nr by (simp add: nextrel0_def)
                        have jL: "j < Lng M" using nr by (simp add: nextrel0_def)
                        have rtc: "(nextrel0 M)\<^sup>*\<^sup>* ?p j" using nr by (rule r_into_rtranclp)
                        thus ?thesis using True pL jL by (simp add: leR_def le0_def)
                      next
                        case False
                        hence nr: "nextrel1 M ?p j" using par by (simp add: nextR_def)
                        have pL: "?p < Lng M" using nr by (simp add: nextrel1_def)
                        have jL: "j < Lng M" using nr by (simp add: nextrel1_def)
                        have rtc: "(nextrel1 M)\<^sup>*\<^sup>* ?p j" using nr by (rule r_into_rtranclp)
                        thus ?thesis using False pL jL by (simp add: leR_def le1_def)
                      qed
                      thus False using gap0' eq by simp
                    qed
                    thus ?thesis using hj0 by linarith
                  qed
                  have not_le_p: "\<not> leR M i j0' ?p"
                  proof
                    assume le_j0'_p: "leR M i j0' ?p"
                    have par: "nextR M i ?p j"
                      using hp unfolding hasParent_def parent_def by (rule theI')
                    have le_p_j: "leR M i ?p j"
                    proof (cases "i = 0")
                      case True
                      hence nr: "nextrel0 M ?p j" using par by (simp add: nextR_def)
                      have pL: "?p < Lng M" using nr by (simp add: nextrel0_def)
                      have jL: "j < Lng M" using nr by (simp add: nextrel0_def)
                      have rtc: "(nextrel0 M)\<^sup>*\<^sup>* ?p j" using nr by (rule r_into_rtranclp)
                      thus ?thesis using True pL jL by (simp add: leR_def le0_def)
                    next
                      case False
                      hence nr: "nextrel1 M ?p j" using par by (simp add: nextR_def)
                      have pL: "?p < Lng M" using nr by (simp add: nextrel1_def)
                      have jL: "j < Lng M" using nr by (simp add: nextrel1_def)
                      have rtc: "(nextrel1 M)\<^sup>*\<^sup>* ?p j" using nr by (rule r_into_rtranclp)
                      thus ?thesis using False pL jL by (simp add: leR_def le1_def)
                    qed
                    have "leR M i j0' j"
                    proof (cases "i = 0")
                      case True
                      from le_j0'_p have "le0 M j0' ?p" using True by (simp add: leR_def)
                      from le_p_j have "le0 M ?p j" using True by (simp add: leR_def)
                      show ?thesis using le0_trans[OF \<open>le0 M j0' ?p\<close> \<open>le0 M ?p j\<close>] True
                        by (simp add: leR_def)
                    next
                      case False
                      have i_eq: "i = 1" using hi False by linarith
                      from le_j0'_p have le0p: "le1 M j0' ?p" using False by (simp add: leR_def)
                      from le_p_j have le1p: "le1 M ?p j" using False by (simp add: leR_def)
                      have "le1 M j0' j" using le0p le1p by (auto simp: le1_def intro: rtranclp_trans)
                      thus ?thesis using False by (simp add: leR_def)
                    qed
                    thus False using gap0' by simp
                  qed
                  have gap_p: "\<exists>j0'' j1''. \<not> leR M i j0'' j1'' \<and> j0'' < j1'' \<and> j1'' \<le> ?p"
                    using not_le_p gap1 j1'_eq_j j0'_lt_p by blast
                  have epp2: "entry M i ?p < ?p" using IH[rule_format, OF plt pL gap_p] .
                  from epp2 eA plt show "entry M i j < j" by linarith
                next
                  case hj0: False
                  \<comment> \<open>j0' > ?p and j0' < j (from j0' < j1' = j).\<close>
                  \<comment> \<open>?p = j-1, so j-1 < j0' < j is impossible for natural numbers.\<close>
                  have lt1: "j0' < j" using gap1 j1'_eq_j by linarith
                  have lt2: "j - 1 < j0'" using hj0 peq by linarith
                  from lt1 lt2 peq show "entry M i j < j" by linarith
                qed
              qed
            qed
          qed
        qed
      qed
    qed
    have key': "\<And>j. j \<le> Lng M - 1 \<Longrightarrow>
        (\<exists>j0' j1'. \<not> leR M i j0' j1' \<and> j0' < j1' \<and> j1' \<le> j) \<Longrightarrow> entry M i j < j"
    proof -
      fix j :: nat
      assume hjle: "j \<le> Lng M - 1"
        and gap: "\<exists>j0' j1'. \<not> leR M i j0' j1' \<and> j0' < j1' \<and> j1' \<le> j"
      have hjL: "j < Lng M" using hjle LM by linarith
      from key have "(\<exists>j0' j1'. \<not> leR M i j0' j1' \<and> j0' < j1' \<and> j1' \<le> j) \<longrightarrow> entry M i j < j"
        using hjL by blast
      thus "entry M i j < j" using gap by blast
    qed
    show "\<forall>j \<le> Lng M - 1. (\<exists>j0' j1'. \<not> leR M i j0' j1' \<and> j0' < j1' \<and> j1' \<le> j) \<longrightarrow>
           entry M i j < j"
    proof (intro allI impI)
      fix j :: nat
      assume "j \<le> Lng M - 1"
        and "\<exists>j0' j1'. \<not> leR M i j0' j1' \<and> j0' < j1' \<and> j1' \<le> j"
      thus "entry M i j < j" by (rule key')
    qed
  qed
  \<comment> \<open>Assemble: convert j ≤ Lng M - 1 ↔ j < Lng M (using LM: 1 ≤ Lng M).\<close>
  have part1': "\<forall>j \<le> Lng M - 1. entry M 0 j \<le> j"
  proof (intro allI impI)
    fix j assume hjle: "j \<le> Lng M - 1"
    have "j < Lng M" using hjle LM by linarith
    thus "entry M 0 j \<le> j" using part1 by blast
  qed
  have part2': "RedCondB M \<longrightarrow> (\<forall>j \<le> Lng M - 1. entry M 0 j \<ge> entry M 1 j)"
  proof (intro impI allI impI)
    fix j assume cb: "RedCondB M" and hjle: "j \<le> Lng M - 1"
    have "j < Lng M" using hjle LM by linarith
    thus "entry M 0 j \<ge> entry M 1 j" using part2 cb by blast
  qed
  show ?thesis using part1' part2' part3 by blast
qed

section \<open>§7.4 許容的親子関係 (Admissible parent relation)\<close>

text \<open>Transitivity of \<open>\<le>\<^sub>M\<close> on row 1, and the unified \<open>leR\<close>.\<close>

lemma le1_trans:
  assumes "le1 M a b" "le1 M b c"
  shows "le1 M a c"
  using assms by (auto simp: le1_def intro: rtranclp_trans)

lemma leR_trans:
  assumes "leR M i a b" "leR M i b c"
  shows "leR M i a c"
  using assms by (cases "i = 0") (auto simp: leR_def intro: le0_trans le1_trans)

text \<open>A single \<open>nextR\<close>-step is an instance of \<open>\<le>\<^sub>M\<close> (row \<open>i = 0\<close> or row 1).\<close>

lemma nextR_imp_leR:
  assumes "nextR M i j0 j1"
  shows "leR M i j0 j1"
proof (cases "i = 0")
  case True
  hence "nextrel0 M j0 j1" using assms by (simp add: nextR_def)
  thus ?thesis using True
    by (auto simp: leR_def le0_def nextrel0_def intro: r_into_rtranclp)
next
  case False
  hence "nextrel1 M j0 j1" using assms by (simp add: nextR_def)
  thus ?thesis using False
    by (auto simp: leR_def le1_def nextrel1_def intro: r_into_rtranclp)
qed

text \<open>
  Chaining: if every index \<open>j'\<close> in \<open>{a+1..j}\<close> is the row-1 child of its
  predecessor (\<open>nextrel1 M (j'-1) j'\<close>), then \<open>a\<close> reaches \<open>j\<close> in row 1.
\<close>

lemma nextrel1_chain:
  assumes "a \<le> j"
    and "\<forall>j'. a < j' \<and> j' \<le> j \<longrightarrow> nextrel1 M (j' - 1) j'"
  shows "(nextrel1 M)\<^sup>*\<^sup>* a j"
  using assms
proof (induction j rule: less_induct)
  case (less j)
  show ?case
  proof (cases "a = j")
    case True
    thus ?thesis by simp
  next
    case False
    with less.prems(1) have aj: "a < j" by simp
    hence j1: "j - 1 < j" by simp
    have alej1: "a \<le> j - 1" using aj by simp
    have hyp: "\<forall>j'. a < j' \<and> j' \<le> j - 1 \<longrightarrow> nextrel1 M (j' - 1) j'"
      using less.prems(2) by auto
    have chain: "(nextrel1 M)\<^sup>*\<^sup>* a (j - 1)"
      by (rule less.IH[OF j1 alej1 hyp])
    have step: "nextrel1 M (j - 1) j"
      using less.prems(2) aj by auto
    from chain step show ?thesis by (rule rtranclp.rtrancl_into_rtrancl)
  qed
qed

text \<open>
  KEY SUB-LEMMA: the admissibilization \<open>Adm\<^sub>M(j)\<close> is a row-1 ancestor of \<open>j\<close>
  (for \<open>j \<le> Lng M - 1\<close>).  Every index strictly between \<open>Adm\<^sub>M(j)\<close> and \<open>j\<close> is
  non-admissible (by maximality of \<open>Adm\<^sub>M(j)\<close>), and a non-admissible index
  below \<open>Lng M\<close> is the row-1 child of its predecessor.
\<close>

lemma adm_row1_ancestry:
  assumes "M \<in> T_PS" "j \<le> Lng M - 1"
  shows "leR M 1 (Adm M j) j"
proof -
  have L: "Lng M \<ge> 1" using assms(1) by (cases M) (auto simp: T_PS_def)
  let ?a = "Adm M j"
  have ale: "?a \<le> j" by (rule adm_Adm_le)
  have jL: "j < Lng M" using assms(2) L by linarith
  have aL: "?a < Lng M" using ale jL by simp
  have steps: "\<forall>j'. ?a < j' \<and> j' \<le> j \<longrightarrow> nextrel1 M (j' - 1) j'"
  proof (intro allI impI)
    fix j' assume a: "?a < j' \<and> j' \<le> j"
    have nadm: "\<not> adm M j'"
    proof
      assume "adm M j'"
      hence "j' \<le> ?a" using adm_Adm_max[of M j' j] a by simp
      with a show False by simp
    qed
    have j'L: "j' < Lng M" using a jL by simp
    from nadm have "nadm M j'" by (simp add: adm_def)
    hence "nextR M 1 (j' - 1) j' \<and> nextR M 1 j' (j' + 1)"
      using j'L by (auto simp: nadm_def)
    thus "nextrel1 M (j' - 1) j'" by (simp add: nextR_def)
  qed
  have chain: "(nextrel1 M)\<^sup>*\<^sup>* ?a j" by (rule nextrel1_chain[OF ale steps])
  show ?thesis using chain ale aL jL by (simp add: leR_def le1_def)
qed

text \<open>
  Parent maximality: if \<open>j0\<close> is the (unique) row-\<open>i\<close> parent of \<open>j1\<close> and \<open>j\<close>
  is a row-\<open>i\<close> ancestor of \<open>j1\<close> with \<open>j < j1\<close>, then \<open>j \<le> j0\<close> (the last step
  into \<open>j1\<close> must come from the unique parent \<open>j0\<close>).
\<close>

lemma parent_max:
  assumes "hasParent M i j1" "nextR M i j0 j1"
    and "leR M i j j1" "j < j1"
  shows "j \<le> j0"
proof (cases "i = 0")
  case True
  from assms(3) True have rt: "(nextrel0 M)\<^sup>*\<^sup>* j j1" by (simp add: leR_def le0_def)
  from rt assms(4) obtain p where jp: "(nextrel0 M)\<^sup>*\<^sup>* j p" and pj1: "nextrel0 M p j1"
    by (cases rule: rtranclp.cases) auto
  have "nextR M i p j1" using pj1 True by (simp add: nextR_def)
  hence "p = j0" using assms(1,2) unfolding hasParent_def by (metis (mono_tags))
  moreover have "j \<le> p" using jp by (rule nextrel0_rtrancl_mono)
  ultimately show ?thesis by simp
next
  case False
  from assms(3) False have rt: "(nextrel1 M)\<^sup>*\<^sup>* j j1" by (simp add: leR_def le1_def)
  from rt assms(4) obtain p where jp: "(nextrel1 M)\<^sup>*\<^sup>* j p" and pj1: "nextrel1 M p j1"
    by (cases rule: rtranclp.cases) auto
  have "nextR M i p j1" using pj1 False by (simp add: nextR_def)
  hence "p = j0" using assms(1,2) unfolding hasParent_def by (metis (mono_tags))
  moreover have "j \<le> p" using jp by (rule nextrel1_rtrancl_mono)
  ultimately show ?thesis by simp
qed

text \<open>
  m: 命題（\<open>Adm\<^sub>M\<close>と\<open><\<^bsub>M\<^esub>\<^sup>NextAdm\<close>の関係） — discharges
  @{thm [source] p_7_4_Adm_nextAdm} (§7.4).
\<close>

lemma m_7_4_Adm_nextAdm:
  assumes "M \<in> T_PS" "hasParent M i (Lng M - 1)"
  shows "nextAdm M i (Adm M (parent M i (Lng M - 1))) (Lng M - 1)"
proof -
  let ?j1 = "Lng M - 1"
  let ?j0 = "parent M i ?j1"
  let ?a = "Adm M ?j0"
  \<comment> \<open>The unique row-\<open>i\<close> parent of \<open>j1\<close> (\<open>i = 0\<close> uses row 0, any other \<open>i\<close> row 1).\<close>
  from assms(2) have par: "nextR M i ?j0 ?j1"
    unfolding hasParent_def parent_def by (rule theI')
  have j0lt: "?j0 < ?j1"
    using par unfolding nextR_def nextrel0_def nextrel1_def by (auto split: if_splits)
  have j0le1: "?j0 \<le> ?j1" using j0lt by simp
  have L: "Lng M > 1" using j0lt by linarith
  have j1L: "?j1 < Lng M" using L by linarith
  \<comment> \<open>(2) \<open>a < j1\<close>.\<close>
  have ale: "?a \<le> ?j0" by (rule adm_Adm_le)
  have alt: "?a < ?j1" using ale j0lt by simp
  \<comment> \<open>(3) \<open>adm M a\<close>.\<close>
  have aadm: "adm M ?a" by (rule adm_Adm_adm)
  \<comment> \<open>(1) \<open>leR M i a j1\<close>: row-1 ancestry of \<open>a\<close> below \<open>j0\<close>, then step \<open>j0 <\<^sup>Next j1\<close>.\<close>
  have j0le: "?j0 \<le> Lng M - 1" using j0lt by simp
  have a_anc_j0_1: "leR M 1 ?a ?j0" by (rule adm_row1_ancestry[OF assms(1) j0le])
  have step_j0_j1: "leR M i ?j0 ?j1" by (rule nextR_imp_leR[OF par])
  have leR_i_a_j1: "leR M i ?a ?j1"
  proof (cases "i = 0")
    case True
    have "leR M 0 ?a ?j0" by (rule m_le1_imp_le0[OF a_anc_j0_1])
    moreover have "leR M 0 ?j0 ?j1" using step_j0_j1 True by simp
    ultimately have "leR M 0 ?a ?j1" using le0_trans by (simp add: leR_def)
    thus ?thesis using True by simp
  next
    case False
    have a_anc_j0_i: "leR M i ?a ?j0" using a_anc_j0_1 False by (simp add: leR_def)
    show ?thesis by (rule leR_trans[OF a_anc_j0_i step_j0_j1])
  qed
  \<comment> \<open>(4) intermediate indices are non-ancestors or non-admissible.\<close>
  have mid: "\<forall>j. ?a < j \<and> j < ?j1 \<longrightarrow> \<not> leR M i j ?j1 \<or> \<not> adm M j"
  proof (intro allI impI)
    fix j assume jb: "?a < j \<and> j < ?j1"
    show "\<not> leR M i j ?j1 \<or> \<not> adm M j"
    proof (rule ccontr)
      assume "\<not> (\<not> leR M i j ?j1 \<or> \<not> adm M j)"
      hence anc: "leR M i j ?j1" and jadm: "adm M j" by auto
      have "j \<le> ?j0" by (rule parent_max[OF assms(2) par anc]) (use jb in simp)
      hence "j \<le> ?a" using adm_Adm_max[OF jadm] by simp
      with jb show False by simp
    qed
  qed
  show ?thesis
    unfolding nextAdm_def using leR_i_a_j1 alt aadm mid by blast
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


section \<open>§6.5 Red termination: foundational helpers\<close>

text \<open>
  Helpers for the well-definedness (= termination) of @{const Red}.  The
  article proves \<open>p_6_5_Red_welldef\<close> in two layers: on the core
  \<open>{M \<in> PT\<^sub>PS | M\<^sub>0 = (0,0)}\<close> by induction on \<open>Lng M - TrMax M\<close>, and on the rest
  of \<open>T\<^sub>PS\<close> immediately.  The facts below establish the arithmetic the measure
  needs: lengths/entries of \<open>diagSeq\<close>, that a diagonal prefix extends the trunk,
  and that branches are strictly shorter than the branch segment.
\<close>

subsection \<open>Diagonal segments \<open>diagSeq a b = ((j,j))\<^bsub>j=a\<^esub>\<^bsup>b\<^esup>\<close>\<close>

lemma Lng_diagSeq[simp]: "Lng (diagSeq a b) = Suc b - a"
  by (simp add: diagSeq_def del: upt_Suc)

lemma diagSeq_nth:
  assumes "j < Suc b - a"
  shows "diagSeq a b ! j = (a + j, a + j)"
proof -
  have lt: "j < length [a..<Suc b]" using assms by (simp del: upt_Suc)
  have aj: "a + j < Suc b" using assms by linarith
  show ?thesis by (simp add: diagSeq_def nth_map[OF lt] nth_upt aj del: upt_Suc)
qed

lemma entry_diagSeq:
  assumes "j < Suc b - a"
  shows "entry (diagSeq a b) i j = a + j"
  using diagSeq_nth[OF assms] by (simp add: entry_def)

subsection \<open>Branch length bound\<close>

text \<open>A single block of a \<open>concat\<close> is no longer than the whole \<open>concat\<close>.\<close>

lemma length_nth_le_concat:
  assumes "J < length xss"
  shows "length (xss ! J) \<le> length (concat xss)"
proof -
  have mem: "(map length xss) ! J \<in> set (map length xss)"
    using assms by (simp add: nth_mem)
  have "length (xss ! J) = (map length xss) ! J" using assms by simp
  also have "\<dots> \<le> sum_list (map length xss)" by (rule member_le_sum_list[OF mem]) simp
  also have "\<dots> = length (concat xss)" by (simp add: length_concat)
  finally show ?thesis .
qed

text \<open>m: each branch component is strictly shorter than the branch segment,
  i.e. \<open>Lng (Br M ! J) \<le> Lng M - TrMax M - 1\<close>.  This bounds the recursion
  argument \<open>N\<^sub>J\<close> in the core case of @{const Red} (case 2).\<close>

lemma Lng_Br_le:
  assumes J: "J < Lng (Br M)"
  shows "Lng (Br M ! J) \<le> Lng M - TrMax M - 1"
proof -
  have ne: "Br M \<noteq> []" using J by auto
  have tr: "TrMax M \<noteq> Lng M - 1"
  proof
    assume "TrMax M = Lng M - 1"
    hence "Br M = []" by (simp add: Br_def)
    thus False using ne by simp
  qed
  hence brP: "Br M = P (seg M (TrMax M + 1) (Lng M - 1))" by (simp add: Br_def)
  let ?Q = "seg M (TrMax M + 1) (Lng M - 1)"
  have "Lng (Br M ! J) \<le> Lng (concat (P ?Q))"
    using J by (simp only: brP length_nth_le_concat)
  also have "\<dots> = Lng ?Q" by (simp add: poper_concat_P)
  also have "\<dots> = Suc (Lng M - 1) - (TrMax M + 1)" by (simp only: Lng_seg)
  also have "\<dots> \<le> Lng M - TrMax M - 1" by simp
  finally show ?thesis .
qed

subsection \<open>Trunk of a diagonal segment\<close>

text \<open>The row-1 chain steps along a diagonal: \<open>(1,j) <\<^bsub>diagSeq u v\<^esub>\<^sup>Next (1,j+1)\<close>
  for every interior \<open>j\<close>.  (The single ancestor of \<open>j+1\<close> reachable from above
  is \<open>j+1\<close> itself, so the row-1 minimality condition is vacuous.)\<close>

lemma nextR1_diagSeq:
  assumes "Suc j < Suc v - u"
  shows "nextR (diagSeq u v) 1 j (Suc j)"
proof -
  let ?M = "diagSeq u v"
  have L: "Lng ?M = Suc v - u" by simp
  have e0j:  "entry ?M 0 j = u + j"          using assms by (intro entry_diagSeq) simp
  have e0sj: "entry ?M 0 (Suc j) = u + Suc j" using assms by (intro entry_diagSeq) simp
  have e1j:  "entry ?M 1 j = u + j"          using assms by (intro entry_diagSeq) simp
  have e1sj: "entry ?M 1 (Suc j) = u + Suc j" using assms by (intro entry_diagSeq) simp
  have n0: "nextrel0 ?M j (Suc j)"
    unfolding nextrel0_def using assms e0j e0sj L by auto
  have rt: "(nextrel0 ?M)\<^sup>*\<^sup>* j (Suc j)" using n0 by (rule r_into_rtranclp)
  have le0: "le0 ?M j (Suc j)" unfolding le0_def using assms L rt by auto
  have univ: "\<forall>j''. j < j'' \<and> le0 ?M j'' (Suc j)
                  \<longrightarrow> entry ?M 1 (Suc j) \<le> entry ?M 1 j''"
  proof (intro allI impI)
    fix j'' assume a: "j < j'' \<and> le0 ?M j'' (Suc j)"
    hence "(nextrel0 ?M)\<^sup>*\<^sup>* j'' (Suc j)" by (simp add: le0_def)
    hence "j'' \<le> Suc j" by (rule nextrel0_rtrancl_mono)
    with a have "j'' = Suc j" by linarith
    thus "entry ?M 1 (Suc j) \<le> entry ?M 1 j''" by simp
  qed
  have "nextrel1 ?M j (Suc j)"
    unfolding nextrel1_def using assms e1j e1sj L le0 univ by auto
  thus ?thesis by (simp add: nextR_def)
qed

text \<open>m: a diagonal segment is entirely trunk: \<open>TrMax (diagSeq u v) = v - u\<close>
  \<open>(= Lng - 1)\<close>.  Foundational for the core base case of @{const Red}
  (\<open>j\<^sub>1' = j\<^sub>1\<close>) and for the trunk-extension estimate of \<open>coreReduce\<close>.\<close>

lemma TrMax_diagSeq:
  assumes uv: "u \<le> v"
  shows "TrMax (diagSeq u v) = v - u"
proof -
  let ?M = "diagSeq u v"
  have L: "Lng ?M = Suc v - u" by simp
  have pos: "\<And>j'. j' < v - u \<Longrightarrow> nextR ?M 1 j' (Suc j')"
  proof -
    fix j' assume "j' < v - u"
    hence "Suc j' < Suc v - u" using uv by (simp add: Suc_diff_le)
    thus "nextR ?M 1 j' (Suc j')" by (rule nextR1_diagSeq)
  qed
  have neg: "\<not> nextR ?M 1 (v - u) (Suc (v - u))"
  proof
    assume "nextR ?M 1 (v - u) (Suc (v - u))"
    hence "nextrel1 ?M (v - u) (Suc (v - u))" by (simp add: nextR_def)
    hence "Suc (v - u) < Lng ?M" by (simp add: nextrel1_def)
    thus False using L uv by simp
  qed
  have Seq: "{j. \<forall>j'<j. nextR ?M 1 j' (j' + 1)} = {.. v - u}"
  proof (rule set_eqI, rule iffI)
    fix j assume "j \<in> {j. \<forall>j'<j. nextR ?M 1 j' (j' + 1)}"
    hence h: "\<forall>j'<j. nextR ?M 1 j' (Suc j')" by simp
    show "j \<in> {.. v - u}"
    proof (rule ccontr)
      assume "j \<notin> {.. v - u}"
      hence "v - u < j" by simp
      with h have "nextR ?M 1 (v - u) (Suc (v - u))" by simp
      thus False using neg by simp
    qed
  next
    fix j assume "j \<in> {.. v - u}"
    hence jle: "j \<le> v - u" by simp
    have "\<forall>j'<j. nextR ?M 1 j' (Suc j')"
    proof (intro allI impI)
      fix j' assume "j' < j"
      hence "j' < v - u" using jle by linarith
      thus "nextR ?M 1 j' (Suc j')" by (rule pos)
    qed
    thus "j \<in> {j. \<forall>j'<j. nextR ?M 1 j' (j' + 1)}" by simp
  qed
  have "TrMax ?M = Max {j. \<forall>j'<j. nextR ?M 1 j' (j' + 1)}" by (simp add: TrMax_def)
  also have "\<dots> = Max {.. v - u}" by (simp only: Seq)
  also have "\<dots> = v - u" by (rule Max_eqI) auto
  finally show ?thesis .
qed

subsection \<open>\<open>IncrFirst\<close>-invariance of \<open>TrMax\<close> (and its iterate)\<close>

text \<open>\<open>TrMax\<close> depends only on the row-1 \<open><\<^sup>Next\<close> chain, which is \<open>IncrFirst\<close>-
  invariant (\<open>nextrel1_IncrFirst_eq\<close>); hence so is \<open>TrMax\<close>, and \<open>Lng - TrMax\<close>
  (the core measure) is preserved by the \<open>IncrFirst\<^bsup>m\<^sub>1\<^sub>0\<^esup>\<close> in case 4 of @{const Red}.\<close>

lemma TrMax_IncrFirst[simp]: "TrMax (IncrFirst M) = TrMax M"
  by (simp add: TrMax_def nextR_def nextrel1_IncrFirst_eq)

lemma Lng_funpow_IncrFirst[simp]: "Lng ((IncrFirst ^^ k) M) = Lng M"
  by (induction k) simp_all

lemma TrMax_funpow_IncrFirst[simp]: "TrMax ((IncrFirst ^^ k) M) = TrMax M"
  by (induction k) simp_all

subsection \<open>Trunk extension by a diagonal prefix\<close>

text \<open>A consecutive row-1 increase \<open>(1,j) <\<^bsub>M\<^esub>\<^sup>Next (1,j+1)\<close> follows from the
  raw monotonicity at \<open>j\<close>: the row-0 step gives \<open>\<le>\<^sub>M\<close>, and the only \<open>\<le>\<^sub>M\<close>-ancestor
  of \<open>j+1\<close> above \<open>j\<close> is \<open>j+1\<close> itself, so the row-1 minimality is automatic.
  Generic helper subsuming @{thm [source] nextR1_diagSeq}.\<close>

lemma nextR1_consecutive:
  assumes L: "Suc j < Lng M"
    and e0: "entry M 0 j < entry M 0 (Suc j)"
    and e1: "entry M 1 j < entry M 1 (Suc j)"
  shows "nextR M 1 j (Suc j)"
proof -
  have n0: "nextrel0 M j (Suc j)" unfolding nextrel0_def using L e0 by auto
  have rt: "(nextrel0 M)\<^sup>*\<^sup>* j (Suc j)" using n0 by (rule r_into_rtranclp)
  have le0: "le0 M j (Suc j)" unfolding le0_def using L rt by auto
  have univ: "\<forall>i. j < i \<and> le0 M i (Suc j) \<longrightarrow> entry M 1 (Suc j) \<le> entry M 1 i"
  proof (intro allI impI)
    fix i assume a: "j < i \<and> le0 M i (Suc j)"
    hence "(nextrel0 M)\<^sup>*\<^sup>* i (Suc j)" by (simp add: le0_def)
    hence "i \<le> Suc j" by (rule nextrel0_rtrancl_mono)
    with a have "i = Suc j" by linarith
    thus "entry M 1 (Suc j) \<le> entry M 1 i" by simp
  qed
  have "nextrel1 M j (Suc j)"
    unfolding nextrel1_def using L e1 le0 univ by auto
  thus ?thesis by (simp add: nextR_def)
qed

text \<open>Entries of \<open>diagSeq 0 k @ rest\<close>: diagonal on the prefix \<open>i \<le> k\<close>, and
  \<open>rest\<close>'s head at the junction index \<open>Suc k\<close>.\<close>

lemma entry_diagSeq_append_lo:
  assumes "i \<le> k"
  shows "entry (diagSeq 0 k @ rest) p i = i"
proof -
  have lt: "i < length (diagSeq 0 k)" using assms by simp
  have ai: "i < Suc k - 0" using assms by simp
  have "(diagSeq 0 k @ rest) ! i = diagSeq 0 k ! i" using lt by (simp add: nth_append)
  also have "\<dots> = (i, i)" using diagSeq_nth[OF ai] by simp
  finally show ?thesis by (simp add: entry_def)
qed

lemma entry_diagSeq_append_junction:
  "entry (diagSeq 0 k @ rest) p (Suc k) = entry rest p 0"
  by (simp add: entry_def nth_append)

text \<open>If a non-empty \<open>rest\<close> starts strictly above the diagonal (both rows
  \<open>> k\<close>), the trunk runs through the whole diagonal prefix and the junction, so
  \<open>TrMax (diagSeq 0 k @ rest) \<ge> Suc k\<close>.  This is the trunk-extension fact behind
  \<open>coreReduce\<close> (case 4 of @{const Red}): a diagonal prefix of length \<open>m\<^sub>1\<^sub>0\<close> raises
  \<open>TrMax\<close> by \<open>m\<^sub>1\<^sub>0\<close>, keeping \<open>Lng - TrMax\<close> from growing.\<close>

lemma nextR1_diagSeq_append:
  assumes ne: "rest \<noteq> []" and r0: "k < entry rest 0 0" and r1: "k < entry rest 1 0"
    and jk: "j' \<le> k"
  shows "nextR (diagSeq 0 k @ rest) 1 j' (Suc j')"
proof -
  let ?M = "diagSeq 0 k @ rest"
  have lenr: "Lng rest > 0" using ne by (cases rest) auto
  have lenM: "Lng ?M = Suc k + Lng rest" by simp
  have L: "Suc j' < Lng ?M" using jk lenr lenM by linarith
  have ej': "entry ?M 0 j' = j'" "entry ?M 1 j' = j'" using jk by (auto simp: entry_diagSeq_append_lo)
  have key: "entry ?M 0 j' < entry ?M 0 (Suc j') \<and> entry ?M 1 j' < entry ?M 1 (Suc j')"
  proof (cases "j' < k")
    case True
    hence sk: "Suc j' \<le> k" by simp
    have "entry ?M 0 (Suc j') = Suc j'" "entry ?M 1 (Suc j') = Suc j'"
      using sk by (auto simp: entry_diagSeq_append_lo)
    thus ?thesis using ej' by simp
  next
    case False
    hence jk': "j' = k" using jk by simp
    have "entry ?M 0 (Suc j') = entry rest 0 0" "entry ?M 1 (Suc j') = entry rest 1 0"
      using jk' by (auto simp: entry_diagSeq_append_junction)
    thus ?thesis using ej' jk' r0 r1 by simp
  qed
  show ?thesis by (rule nextR1_consecutive[OF L conjunct1[OF key] conjunct2[OF key]])
qed

lemma le_TrMax_intro:
  assumes T: "M \<in> T_PS" and H: "\<forall>j'<n. nextR M 1 j' (j' + 1)"
  shows "n \<le> TrMax M"
proof -
  let ?S = "{j. \<forall>j'<j. nextR M 1 j' (j' + 1)}"
  have LM: "Lng M > 0" using T by (cases M) (auto simp: T_PS_def)
  have sub: "?S \<subseteq> {..Lng M - 1}"
  proof
    fix j assume "j \<in> ?S"
    hence Hj: "\<forall>j'<j. nextR M 1 j' (j' + 1)" by simp
    show "j \<in> {..Lng M - 1}"
    proof (rule ccontr)
      assume "j \<notin> {..Lng M - 1}"
      hence "Lng M - 1 < j" by simp
      hence "nextR M 1 (Lng M - 1) ((Lng M - 1) + 1)" using Hj by blast
      hence "(Lng M - 1) + 1 < Lng M" by (simp add: nextR_def nextrel1_def)
      thus False using LM by simp
    qed
  qed
  hence fin: "finite ?S" by (rule finite_subset) simp
  have nS: "n \<in> ?S" using H by simp
  have "n \<le> Max ?S" using fin nS by (rule Max_ge)
  thus ?thesis by (simp add: TrMax_def)
qed

lemma TrMax_diagSeq_append_ge:
  assumes ne: "rest \<noteq> []" and r0: "k < entry rest 0 0" and r1: "k < entry rest 1 0"
  shows "Suc k \<le> TrMax (diagSeq 0 k @ rest)"
proof -
  let ?M = "diagSeq 0 k @ rest"
  have T: "?M \<in> T_PS" using ne by (simp add: T_PS_def)
  have "\<forall>j'<Suc k. nextR ?M 1 j' (j' + 1)"
  proof (intro allI impI)
    fix j' assume "j' < Suc k"
    hence "j' \<le> k" by simp
    from nextR1_diagSeq_append[OF ne r0 r1 this] show "nextR ?M 1 j' (j' + 1)" by simp
  qed
  from le_TrMax_intro[OF T this] show ?thesis .
qed

subsection \<open>The core measure \<open>\<beta>\<close> and the one-step \<open>coreReduce\<close>\<close>

text \<open>\<open>entry\<close> under the \<open>IncrFirst\<close> iterate: row 0 is raised by \<open>k\<close>, row 1 fixed.\<close>

lemma entry_funpow_IncrFirst0:
  "j < Lng M \<Longrightarrow> entry ((IncrFirst ^^ k) M) 0 j = entry M 0 j + k"
proof (induction k)
  case 0 thus ?case by simp
next
  case (Suc k)
  have jl: "j < Lng ((IncrFirst ^^ k) M)" using Suc.prems by simp
  have "entry ((IncrFirst ^^ Suc k) M) 0 j = entry (IncrFirst ((IncrFirst ^^ k) M)) 0 j"
    by simp
  also have "\<dots> = Suc (entry ((IncrFirst ^^ k) M) 0 j)" using jl by (simp add: entry_IncrFirst)
  also have "\<dots> = Suc (entry M 0 j + k)" using Suc by simp
  finally show ?case by simp
qed

lemma entry_funpow_IncrFirst1:
  "j < Lng M \<Longrightarrow> entry ((IncrFirst ^^ k) M) 1 j = entry M 1 j"
proof (induction k)
  case 0 thus ?case by simp
next
  case (Suc k)
  have jl: "j < Lng ((IncrFirst ^^ k) M)" using Suc.prems by simp
  have "entry ((IncrFirst ^^ Suc k) M) 1 j = entry (IncrFirst ((IncrFirst ^^ k) M)) 1 j"
    by simp
  also have "\<dots> = entry ((IncrFirst ^^ k) M) 1 j" using jl by (simp add: entry_IncrFirst)
  also have "\<dots> = entry M 1 j" using Suc by simp
  finally show ?case .
qed

text \<open>\<open>\<beta> M = Lng M - TrMax M\<close> is the core measure (branch positions right of the
  trunk).  \<open>coreReduce M\<close> is the core element (starting at \<open>(0,0)\<close>) that a
  non-core mono \<open>M\<close> reduces to in one @{const Red} step: shift row 0 down when
  \<open>M\<^bsub>1,0\<^esub> = 0\<close> (case 3), else prepend a diagonal of length \<open>M\<^bsub>1,0\<^esub>\<close> (case 4).\<close>

definition betaM :: "pairseq \<Rightarrow> nat" where
  "betaM M = Lng M - TrMax M"

definition coreReduce :: "pairseq \<Rightarrow> pairseq" where
  "coreReduce M =
     (if entry M 1 0 = 0
      then map (\<lambda>j. (entry M 0 j - entry M 0 0, entry M 1 j)) [0..<Lng M]
      else diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ (entry M 1 0)) M)"

text \<open>\<open>coreReduce M\<close> starts at \<open>(0,0)\<close> (it lands in the core), for any non-empty
  non-core \<open>M\<close>.\<close>

lemma coreReduce_core:
  assumes T: "M \<in> T_PS"
  shows "entry (coreReduce M) 0 0 = 0 \<and> entry (coreReduce M) 1 0 = 0"
proof (cases "entry M 1 0 = 0")
  case True
  have L: "Lng M > 0" using T by (cases M) (auto simp: T_PS_def)
  have "coreReduce M = map (\<lambda>j. (entry M 0 j - entry M 0 0, entry M 1 j)) [0..<Lng M]"
    using True by (simp add: coreReduce_def)
  thus ?thesis using True L by (simp add: entry_def)
next
  case False
  let ?k = "entry M 1 0 - 1"
  have "coreReduce M = diagSeq 0 ?k @ (IncrFirst ^^ (entry M 1 0)) M"
    using False by (simp add: coreReduce_def)
  thus ?thesis using False
    by (simp add: entry_diagSeq_append_lo[where i=0])
qed

text \<open>m: the core measure does not grow under \<open>coreReduce\<close>:
  \<open>\<beta> (coreReduce M) \<le> Lng M\<close>.  Case 3 (\<open>m\<^sub>1\<^sub>0=0\<close>) is immediate (\<open>Lng\<close> fixed,
  \<open>\<beta> \<le> Lng\<close>); case 4 (\<open>m\<^sub>1\<^sub>0>0\<close>) uses @{thm [source] TrMax_diagSeq_append_ge}: the
  prepended diagonal of length \<open>m\<^sub>1\<^sub>0\<close> raises \<open>TrMax\<close> by \<open>m\<^sub>1\<^sub>0\<close>.\<close>

lemma betaM_coreReduce_le:
  assumes T: "M \<in> T_PS"
  shows "betaM (coreReduce M) \<le> Lng M"
proof (cases "entry M 1 0 = 0")
  case True
  have "coreReduce M = map (\<lambda>j. (entry M 0 j - entry M 0 0, entry M 1 j)) [0..<Lng M]"
    using True by (simp add: coreReduce_def)
  hence "Lng (coreReduce M) = Lng M" by simp
  thus ?thesis by (simp add: betaM_def)
next
  case False
  let ?m = "entry M 1 0"
  let ?k = "?m - 1"
  let ?rest = "(IncrFirst ^^ ?m) M"
  have m1: "?m \<ge> 1" using False by simp
  have L0: "0 < Lng M" using T by (cases M) (auto simp: T_PS_def)
  have cr: "coreReduce M = diagSeq 0 ?k @ ?rest" using False by (simp add: coreReduce_def)
  have lenr: "Lng ?rest = Lng M" by simp
  have ne: "?rest \<noteq> []" using L0 lenr by (metis length_greater_0_conv)
  have er0: "entry ?rest 0 0 = entry M 0 0 + ?m" by (rule entry_funpow_IncrFirst0[OF L0])
  have er1: "entry ?rest 1 0 = entry M 1 0" by (rule entry_funpow_IncrFirst1[OF L0])
  have r0: "?k < entry ?rest 0 0" using m1 er0 by simp
  have r1: "?k < entry ?rest 1 0" using m1 er1 by simp
  have trge: "Suc ?k \<le> TrMax (coreReduce M)"
    using cr TrMax_diagSeq_append_ge[OF ne r0 r1] by simp
  have lenc: "Lng (coreReduce M) = Suc ?k + Lng M" using cr by simp
  have "betaM (coreReduce M) = (Suc ?k + Lng M) - TrMax (coreReduce M)"
    by (simp add: betaM_def lenc)
  also have "\<dots> \<le> (Suc ?k + Lng M) - Suc ?k" using trge by (rule diff_le_mono2)
  also have "\<dots> = Lng M" by simp
  finally show ?thesis .
qed

text \<open>Every \<open>P\<close>-block of a non-empty sequence is non-empty (the cut
  \<open>0 < Pcut M \<le> Lng M - 1\<close> keeps both \<open>take\<close> and \<open>drop\<close> halves non-empty).
  Needed e.g. for \<open>Lng (Br M ! J) = Lng (N\<^sub>J)\<close>.\<close>

lemma P_blocks_nonempty:
  assumes "M \<noteq> []"
  shows "\<forall>B \<in> set (P M). B \<noteq> []"
proof -
  have "M \<noteq> [] \<longrightarrow> (\<forall>B \<in> set (P M). B \<noteq> [])"
  proof (induction M rule: P.induct)
    case (1 M)
    show ?case
    proof (rule impI)
      assume ne: "M \<noteq> []"
      show "\<forall>B \<in> set (P M). B \<noteq> []"
      proof (cases "multiT M \<and> 1 < Lng M")
        case True
        let ?c = "Pcut M"
        have L: "1 < Lng M" using True by simp
        have step: "P M = P (take ?c M) @ [drop ?c M]" using True by (subst P.simps) simp
        have cge: "0 < ?c" and cle: "?c \<le> Lng M - 1" using Pcut_le[OF L] by auto
        have tne: "take ?c M \<noteq> []" using cge ne by (simp add: take_eq_Nil)
        have IH: "\<forall>B \<in> set (P (take ?c M)). B \<noteq> []" using "1.IH"[OF True] tne by blast
        have dne: "drop ?c M \<noteq> []" using cle L by (simp add: drop_eq_Nil)
        show ?thesis using step IH dne by auto
      next
        case False
        note nc = this
        have "P M = [M]" by (subst P.simps) (rule if_not_P[OF nc])
        thus ?thesis using ne by simp
      qed
    qed
  qed
  thus ?thesis using assms by blast
qed

text \<open>Row-0 minimality of a mono sequence: \<open>M\<^bsub>0,0\<^esub> < M\<^bsub>0,j\<^esub>\<close> for every
  \<open>0 < j < Lng M\<close> (the left end is the strict row-0 minimum).  This is the fact
  that makes the \<open>m\<^sub>1\<^sub>0 = 0\<close> row-0 shift in \<open>coreReduce\<close> order-preserving (no
  \<open>nat\<close> truncation), via @{thm [source] m_5_1_ancestor_basic_1} and \<open>monoT\<close>.\<close>

lemma monoT_row0_min:
  assumes M: "M \<in> T_PS" and mono: "monoT M" and j: "0 < j" "j < Lng M"
  shows "entry M 0 0 < entry M 0 j"
proof -
  have le: "leR M 0 0 (Lng M - 1)" using mono by (simp add: monoT_def)
  have jle: "j \<le> Lng M - 1" using j by simp
  show ?thesis by (rule m_5_1_ancestor_basic_1[OF M j(1) jle le])
qed

text \<open>The row-0 shift used by \<open>coreReduce\<close> in the \<open>m\<^sub>1\<^sub>0 = 0\<close> case: subtract
  \<open>M\<^bsub>0,0\<^esub>\<close> from row 0, keep row 1.  For a mono \<open>M\<close> the left end is the row-0
  minimum (@{thm [source] monoT_row0_min}), so the subtraction is
  order-preserving and \<open>shiftRow0\<close> stays mono.\<close>

definition shiftRow0 :: "pairseq \<Rightarrow> pairseq" where
  "shiftRow0 M = map (\<lambda>j. (entry M 0 j - entry M 0 0, entry M 1 j)) [0..<Lng M]"

lemma Lng_shiftRow0[simp]: "Lng (shiftRow0 M) = Lng M"
  by (simp add: shiftRow0_def)

lemma entry_shiftRow0_0:
  "j < Lng M \<Longrightarrow> entry (shiftRow0 M) 0 j = entry M 0 j - entry M 0 0"
  by (simp add: shiftRow0_def entry_def)

lemma entry_shiftRow0_1:
  "j < Lng M \<Longrightarrow> entry (shiftRow0 M) 1 j = entry M 1 j"
  by (simp add: shiftRow0_def entry_def)

lemma entry0_ge_min:
  assumes M: "M \<in> T_PS" and mono: "monoT M" and j: "j < Lng M"
  shows "entry M 0 0 \<le> entry M 0 j"
proof (cases "j = 0")
  case True thus ?thesis by simp
next
  case False
  hence "0 < j" by simp
  from monoT_row0_min[OF M mono this j] show ?thesis by simp
qed

lemma nextrel0_shiftRow0_eq:
  assumes M: "M \<in> T_PS" and mono: "monoT M"
  shows "nextrel0 (shiftRow0 M) j0 j1 = nextrel0 M j0 j1"
proof (cases "j0 < Lng M \<and> j1 < Lng M")
  case True
  hence j0L: "j0 < Lng M" and j1L: "j1 < Lng M" by simp_all
  let ?c = "entry M 0 0"
  have e0: "entry (shiftRow0 M) 0 j0 = entry M 0 j0 - ?c" using j0L by (rule entry_shiftRow0_0)
  have e1: "entry (shiftRow0 M) 0 j1 = entry M 0 j1 - ?c" using j1L by (rule entry_shiftRow0_0)
  have gj0: "?c \<le> entry M 0 j0" using entry0_ge_min[OF M mono j0L] .
  have gj1: "?c \<le> entry M 0 j1" using entry0_ge_min[OF M mono j1L] .
  have lt_iff: "(entry M 0 j0 - ?c < entry M 0 j1 - ?c) = (entry M 0 j0 < entry M 0 j1)"
    using gj0 gj1 by linarith
  have ge_iff: "\<forall>j. j0 < j \<and> j < j1 \<longrightarrow>
                  (entry (shiftRow0 M) 0 j \<ge> entry (shiftRow0 M) 0 j1)
                  = (entry M 0 j \<ge> entry M 0 j1)"
  proof (intro allI impI)
    fix j assume jb: "j0 < j \<and> j < j1"
    hence jL: "j < Lng M" using j1L by simp
    have ej: "entry (shiftRow0 M) 0 j = entry M 0 j - ?c" using jL by (rule entry_shiftRow0_0)
    have gj: "?c \<le> entry M 0 j" using entry0_ge_min[OF M mono jL] .
    show "(entry (shiftRow0 M) 0 j \<ge> entry (shiftRow0 M) 0 j1)
            = (entry M 0 j \<ge> entry M 0 j1)"
      using ej e1 gj gj1 by linarith
  qed
  show ?thesis
    unfolding nextrel0_def
    using e0 e1 lt_iff ge_iff by (simp add: Lng_shiftRow0 cong: conj_cong)
next
  case False
  thus ?thesis by (auto simp: nextrel0_def Lng_shiftRow0)
qed

lemma le0_shiftRow0_eq:
  assumes M: "M \<in> T_PS" and mono: "monoT M"
  shows "le0 (shiftRow0 M) j0 j1 = le0 M j0 j1"
proof -
  have "nextrel0 (shiftRow0 M) = nextrel0 M"
    by (intro ext) (rule nextrel0_shiftRow0_eq[OF M mono])
  thus ?thesis by (simp add: le0_def Lng_shiftRow0)
qed

lemma monoT_shiftRow0:
  assumes M: "M \<in> T_PS" and mono: "monoT M"
  shows "monoT (shiftRow0 M)"
proof -
  have nz: "\<not> zeroT (shiftRow0 M)"
  proof -
    have "zeroT (shiftRow0 M) = zeroT M"
    proof (cases "Lng M = 1")
      case True
      hence "0 < Lng M" by simp
      hence "entry (shiftRow0 M) 1 0 = entry M 1 0" by (rule entry_shiftRow0_1)
      thus ?thesis using True by (simp add: zeroT_def Lng_shiftRow0)
    next
      case False
      thus ?thesis by (simp add: zeroT_def Lng_shiftRow0)
    qed
    thus ?thesis using mono by (simp add: monoT_def)
  qed
  have "leR M 0 0 (Lng M - 1)" using mono by (simp add: monoT_def)
  hence "leR (shiftRow0 M) 0 0 (Lng (shiftRow0 M) - 1)"
    by (simp add: leR_def Lng_shiftRow0 le0_shiftRow0_eq[OF M mono])
  thus ?thesis using nz by (simp add: monoT_def)
qed

text \<open>\<open>coreReduce M\<close> is mono (hence non-multi) in the \<open>m\<^sub>1\<^sub>0 = 0\<close> case:
  there it equals @{const shiftRow0}, which preserves \<open>monoT\<close>.\<close>

lemma coreReduce_monoT_m10_0:
  assumes M: "M \<in> T_PS" and mono: "monoT M" and z: "entry M 1 0 = 0"
  shows "monoT (coreReduce M)"
proof -
  have "coreReduce M = shiftRow0 M" using z by (simp add: coreReduce_def shiftRow0_def)
  thus ?thesis using monoT_shiftRow0[OF M mono] by simp
qed

text \<open>Entry of \<open>diagSeq 0 k @ rest\<close> on the \<open>rest\<close> part (index \<open>Suc k + a\<close>).\<close>

lemma entry_diagSeq_append_hi:
  assumes "a < Lng rest"
  shows "entry (diagSeq 0 k @ rest) p (Suc k + a) = entry rest p a"
proof -
  have "(diagSeq 0 k @ rest) ! (Suc k + a) = rest ! a" by (simp add: nth_append)
  thus ?thesis by (simp add: entry_def)
qed

lemma monoT_funpow_IncrFirst[simp]: "monoT ((IncrFirst ^^ k) M) = monoT M"
  by (induction k) (simp_all add: IncrFirst_monoT_eq)

text \<open>If a mono \<open>rest\<close> starts strictly above the diagonal in row 0, prepending the
  diagonal \<open>diagSeq 0 k\<close> keeps it mono: row 0 is \<open>> 0\<close> at every index after \<open>0\<close>,
  so @{thm [source] le0_build} gives \<open>(0,0) \<le>\<^bsub>M\<^esub> (0, Lng-1)\<close>.  This is the
  row-0 analogue of @{thm [source] TrMax_diagSeq_append_ge}; it discharges the
  \<open>m\<^sub>1\<^sub>0 > 0\<close> case of "coreReduce is mono".\<close>

lemma monoT_diagSeq_append:
  assumes ne: "rest \<noteq> []" and rmono: "monoT rest" and rTPS: "rest \<in> T_PS"
    and r0: "k < entry rest 0 0"
  shows "monoT (diagSeq 0 k @ rest)"
proof -
  let ?M = "diagSeq 0 k @ rest"
  have lenr: "0 < Lng rest" using ne by (cases rest) auto
  have lenM: "Lng ?M = Suc k + Lng rest" by simp
  have MTPS: "?M \<in> T_PS" using ne by (simp add: T_PS_def)
  have e00: "entry ?M 0 0 = 0" using entry_diagSeq_append_lo[where i=0 and k=k and rest=rest] by simp
  have key: "\<And>j. 0 < j \<Longrightarrow> j \<le> Lng ?M - 1 \<Longrightarrow> 0 < entry ?M 0 j"
  proof -
    fix j assume j0: "0 < j" and jle: "j \<le> Lng ?M - 1"
    show "0 < entry ?M 0 j"
    proof (cases "j \<le> k")
      case True
      hence "entry ?M 0 j = j" by (rule entry_diagSeq_append_lo)
      thus ?thesis using j0 by simp
    next
      case False
      hence kj: "k < j" by simp
      let ?a = "j - Suc k"
      have ja: "j = Suc k + ?a" using kj by simp
      have aL: "?a < Lng rest" using jle lenM kj by linarith
      have "entry ?M 0 j = entry rest 0 ?a"
        using ja entry_diagSeq_append_hi[OF aL, where k=k and p=0] by simp
      moreover have "entry rest 0 0 \<le> entry rest 0 ?a"
        using entry0_ge_min[OF rTPS rmono aL] .
      ultimately show ?thesis using r0 by simp
    qed
  qed
  have j1lt: "Lng ?M - 1 < Lng ?M" using lenM lenr by simp
  have j0lt: "(0::nat) < Lng ?M - 1" using lenM lenr by simp
  have "(nextrel0 ?M)\<^sup>*\<^sup>* 0 (Lng ?M - 1)"
  proof (rule le0_build[OF MTPS j1lt j0lt])
    show "\<forall>j. 0 < j \<and> j \<le> Lng ?M - 1 \<longrightarrow> entry ?M 0 0 < entry ?M 0 j"
      using key e00 by simp
  qed
  hence "le0 ?M 0 (Lng ?M - 1)" using j1lt by (simp add: le0_def)
  hence "leR ?M 0 0 (Lng ?M - 1)" by (simp add: leR_def)
  moreover have "\<not> zeroT ?M" using lenM lenr by (simp add: zeroT_def)
  ultimately show ?thesis by (simp add: monoT_def)
qed

lemma coreReduce_monoT_m10_pos:
  assumes M: "M \<in> T_PS" and mono: "monoT M" and pos: "0 < entry M 1 0"
  shows "monoT (coreReduce M)"
proof -
  let ?m = "entry M 1 0"
  let ?rest = "(IncrFirst ^^ ?m) M"
  have L0: "0 < Lng M" using M by (cases M) (auto simp: T_PS_def)
  have cr: "coreReduce M = diagSeq 0 (?m - 1) @ ?rest" using pos by (simp add: coreReduce_def)
  have lenr: "Lng ?rest = Lng M" by simp
  have ne: "?rest \<noteq> []" using L0 lenr by (metis length_greater_0_conv)
  have rTPS: "?rest \<in> T_PS" using ne by (simp add: T_PS_def)
  have rmono: "monoT ?rest" using mono by simp
  have "entry ?rest 0 0 = entry M 0 0 + ?m" by (rule entry_funpow_IncrFirst0[OF L0])
  hence r0: "?m - 1 < entry ?rest 0 0" using pos by simp
  show ?thesis using cr monoT_diagSeq_append[OF ne rmono rTPS r0] by simp
qed

text \<open>m: \<open>coreReduce M\<close> is non-multi (mono) for any non-core mono \<open>M\<close> — the
  case-3/4 obligation that makes the global measure \<open>\<nu>\<close> well-behaved.\<close>

lemma coreReduce_nonmulti:
  assumes M: "M \<in> T_PS" and mono: "monoT M"
  shows "\<not> multiT (coreReduce M)"
proof (cases "entry M 1 0 = 0")
  case True
  from coreReduce_monoT_m10_0[OF M mono True] show ?thesis by (simp add: multiT_def)
next
  case False
  hence "0 < entry M 1 0" by simp
  from coreReduce_monoT_m10_pos[OF M mono this] show ?thesis by (simp add: multiT_def)
qed

text \<open>The trunk holds up to \<open>TrMax M\<close>: the row-1 chain \<open>(1,j) <\<^sup>Next (1,j+1)\<close>
  is unbroken for every \<open>j < TrMax M\<close>.  (\<open>TrMax M = Max ?S\<close> lies in the
  downward-closed finite set \<open>?S\<close>.)\<close>

lemma TrMax_in_S:
  assumes T: "M \<in> T_PS"
  shows "\<forall>j'<TrMax M. nextR M 1 j' (j' + 1)"
proof -
  let ?S = "{j. \<forall>j'<j. nextR M 1 j' (j' + 1)}"
  have LM: "Lng M > 0" using T by (cases M) (auto simp: T_PS_def)
  have sub: "?S \<subseteq> {..Lng M - 1}"
  proof
    fix j assume "j \<in> ?S"
    hence H: "\<forall>j'<j. nextR M 1 j' (j' + 1)" by simp
    show "j \<in> {..Lng M - 1}"
    proof (rule ccontr)
      assume "j \<notin> {..Lng M - 1}"
      hence "Lng M - 1 < j" by simp
      hence "nextR M 1 (Lng M - 1) ((Lng M - 1) + 1)" using H by blast
      hence "(Lng M - 1) + 1 < Lng M" by (simp add: nextR_def nextrel1_def)
      thus False using LM by simp
    qed
  qed
  hence fin: "finite ?S" by (rule finite_subset) simp
  have "0 \<in> ?S" by simp
  hence ne: "?S \<noteq> {}" by blast
  have "Max ?S \<in> ?S" by (rule Max_in[OF fin ne])
  thus ?thesis by (simp add: TrMax_def)
qed

text \<open>m: row-0 grows by at least 1 per step along the trunk:
  \<open>M\<^bsub>0,0\<^esub> + j \<le> M\<^bsub>0,j\<^esub>\<close> for \<open>j \<le> TrMax M\<close>.  (Each trunk step gives a row-0
  \<open>\<le>\<^sub>M\<close>-edge, hence a strict row-0 increase.)\<close>

lemma trunk_row0_inc:
  assumes T: "M \<in> T_PS" and jt: "j \<le> TrMax M" and jL: "j < Lng M"
  shows "entry M 0 0 + j \<le> entry M 0 j"
  using jt jL
proof (induction j)
  case 0 thus ?case by simp
next
  case (Suc j')
  have jt': "j' < TrMax M" using Suc.prems(1) by simp
  have nx: "nextR M 1 j' (Suc j')" using TrMax_in_S[OF T] jt' by simp
  have le: "leR M 0 j' (Suc j')" using nx by (auto simp: leR_def nextR_def nextrel1_def)
  have inc: "entry M 0 j' < entry M 0 (Suc j')"
    by (rule m_5_1_ancestor_basic_1[OF T _ _ le]) auto
  have IH: "entry M 0 0 + j' \<le> entry M 0 j'" using Suc by simp
  show ?case using inc IH by simp
qed

text \<open>Both rows are strictly increasing along the trunk: a consecutive trunk
  step \<open>k \<rightarrow> k+1\<close> (\<open>k < TrMax M\<close>) strictly increases each row's entry, hence so
  does any forward jump within the trunk.\<close>

lemma trunk_step_lt:
  assumes M: "M \<in> T_PS" and i: "i = 0 \<or> i = 1" and k: "k < TrMax M"
  shows "entry M i k < entry M i (Suc k)"
proof -
  have nx: "nextR M 1 k (Suc k)" using TrMax_in_S[OF M] k by simp
  from i show ?thesis
  proof
    assume i0: "i = 0"
    have le: "leR M 0 k (Suc k)" using nx by (auto simp: leR_def nextR_def nextrel1_def)
    have "entry M 0 k < entry M 0 (Suc k)"
      by (rule m_5_1_ancestor_basic_1[OF M _ _ le]) auto
    thus ?thesis using i0 by simp
  next
    assume i1: "i = 1"
    have "entry M 1 k < entry M 1 (Suc k)" using nx by (auto simp: nextR_def nextrel1_def)
    thus ?thesis using i1 by simp
  qed
qed

lemma trunk_lt:
  assumes M: "M \<in> T_PS" and i: "i = 0 \<or> i = 1" and j0j1: "j0 < j1" and j1: "j1 \<le> TrMax M"
  shows "entry M i j0 < entry M i j1"
  using j0j1 j1
proof (induction j1)
  case 0 thus ?case by simp
next
  case (Suc j1)
  have kT: "j1 < TrMax M" using Suc.prems(2) by simp
  have step: "entry M i j1 < entry M i (Suc j1)" by (rule trunk_step_lt[OF M i kT])
  show ?case
  proof (cases "j0 = j1")
    case True thus ?thesis using step by simp
  next
    case False
    hence j0j1': "j0 < j1" using Suc.prems(1) by simp
    have "j1 \<le> TrMax M" using Suc.prems(2) by simp
    hence "entry M i j0 < entry M i j1" using Suc.IH[OF j0j1'] by simp
    thus ?thesis using step by simp
  qed
qed

text \<open>\<open>Joints M ! J\<close> is the (unique) row-0 parent of \<open>FirstNodes M ! J\<close>:
  \<open>(0, Joints M ! J) <\<^bsub>M\<^esub>\<^sup>Next (0, FirstNodes M ! J)\<close>.  (Extracted from the
  \<open>m_6_4_FirstNodes_Joints_mono\<close> development.)\<close>

lemma Joints_parent_nextR:
  assumes M: "M \<in> PT_PS" and JBr: "J < Lng (Br M)"
  shows "nextR M 0 (Joints M ! J) (FirstNodes M ! J)"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have brne: "Br M \<noteq> []" using JBr by auto
  have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
  have trne: "TrMax M \<noteq> Lng M - 1"
  proof
    assume "TrMax M = Lng M - 1"
    hence "Br M = []" by (simp add: Br_def)
    with brne show False by simp
  qed
  with tb have trlt: "TrMax M < Lng M - 1" by linarith
  let ?N = "seg M (TrMax M + 1) (Lng M - 1)"
  have brQ: "Br M = P ?N" using trne by (simp add: Br_def)
  have JQ: "J \<le> Lng (P ?N) - 1" using JBr brQ by (cases "P ?N") auto
  have hp: "hasParent M 0 (TrMax M + 1 + IdxSum (P ?N) ! J)"
    using m_6_4_mono_slice_next[OF M _ _ JQ] trlt by auto
  have fnJ: "TrMax M + 1 + IdxSum (P ?N) ! J = FirstNodes M ! J"
    using FirstNodes_nth[OF JBr] brQ by simp
  have hpf: "hasParent M 0 (FirstNodes M ! J)" using hp fnJ by simp
  have aJ_eq: "Joints M ! J = parent M 0 (FirstNodes M ! J)" by (rule Joints_nth[OF JBr])
  have "\<exists>!j0. nextR M 0 j0 (FirstNodes M ! J)" using hpf by (simp add: hasParent_def)
  hence "nextR M 0 (THE j0. nextR M 0 j0 (FirstNodes M ! J)) (FirstNodes M ! J)"
    by (rule theI')
  thus ?thesis using aJ_eq by (simp add: parent_def)
qed

text \<open>m: article [13] key inequality — \<open>M\<^bsub>0,0\<^esub> + Joints M ! J + 1 \<le> (Br M ! J)\<^bsub>0,0\<^esub>\<close>.
  Combines the trunk row-0 growth up to \<open>Joints M ! J\<close>, the strict row-0 jump
  across the parent edge to \<open>FirstNodes M ! J\<close>, and
  @{thm [source] entry_FirstNodes_eq_component}.  This is what keeps \<open>N\<^sub>J\<close>'s new
  first entry strictly below the rest of the branch, i.e. \<open>N\<^sub>J\<close> mono.\<close>

lemma joints_lt_branch_first:
  assumes M: "M \<in> PT_PS" and JBr: "J < Lng (Br M)"
  shows "entry M 0 0 + Joints M ! J + 1 \<le> entry (Br M ! J) 0 0"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have aJTr: "Joints M ! J \<le> TrMax M"
    using m_6_4_FirstNodes_TrMax_Joints[OF M JBr] by simp
  have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  have jL: "Joints M ! J < Lng M" using aJTr tb LMpos by linarith
  have trunk: "entry M 0 0 + Joints M ! J \<le> entry M 0 (Joints M ! J)"
    by (rule trunk_row0_inc[OF MT aJTr jL])
  have nx: "nextR M 0 (Joints M ! J) (FirstNodes M ! J)" by (rule Joints_parent_nextR[OF M JBr])
  have strict: "entry M 0 (Joints M ! J) < entry M 0 (FirstNodes M ! J)"
    using nx by (simp add: nextR_def nextrel0_def)
  have ec: "entry M 0 (FirstNodes M ! J) = entry (Br M ! J) 0 0"
    by (rule entry_FirstNodes_eq_component[OF M JBr])
  show ?thesis using trunk strict ec by simp
qed

text \<open>Each branch component is non-empty and non-multi (it is a \<open>P\<close>-block of the
  branch segment).\<close>

lemma Br_component_nonempty:
  assumes M: "M \<in> PT_PS" and JBr: "J < Lng (Br M)"
  shows "Br M ! J \<noteq> []"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have brne: "Br M \<noteq> []" using JBr by auto
  have trne: "TrMax M \<noteq> Lng M - 1"
  proof
    assume "TrMax M = Lng M - 1"
    hence "Br M = []" by (simp add: Br_def)
    with brne show False by simp
  qed
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  with trne TrMax_bound[OF MT] have trlt: "TrMax M < Lng M - 1" by linarith
  let ?N = "seg M (TrMax M + 1) (Lng M - 1)"
  have brQ: "Br M = P ?N" using trne by (simp add: Br_def)
  have NL: "0 < Lng ?N" using trlt LMpos by (simp add: Lng_seg)
  have Nne: "?N \<noteq> []" using NL by (metis length_greater_0_conv)
  have mem: "Br M ! J \<in> set (Br M)" using JBr by (simp add: nth_mem)
  show ?thesis using P_blocks_nonempty[OF Nne] brQ mem by auto
qed

lemma Br_component_nonmulti:
  assumes M: "M \<in> PT_PS" and JBr: "J < Lng (Br M)"
  shows "zeroT (Br M ! J) \<or> monoT (Br M ! J)"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have brne: "Br M \<noteq> []" using JBr by auto
  have trne: "TrMax M \<noteq> Lng M - 1"
  proof
    assume "TrMax M = Lng M - 1"
    hence "Br M = []" by (simp add: Br_def)
    with brne show False by simp
  qed
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  with trne TrMax_bound[OF MT] have trlt: "TrMax M < Lng M - 1" by linarith
  let ?N = "seg M (TrMax M + 1) (Lng M - 1)"
  have brQ: "Br M = P ?N" using trne by (simp add: Br_def)
  have NL: "0 < Lng ?N" using trlt LMpos by (simp add: Lng_seg)
  have Nne: "?N \<noteq> []" using NL by (metis length_greater_0_conv)
  have NT: "?N \<in> T_PS" using Nne by (simp add: T_PS_def)
  have mem: "Br M ! J \<in> set (Br M)" using JBr by (simp add: nth_mem)
  show ?thesis using m_6_2_P_components_1[OF NT] brQ mem by auto
qed

text \<open>List fact: replacing the head leaves later entries unchanged.\<close>

lemma nth_Cons_tl:
  assumes "0 < j" "j < length ys"
  shows "(x # tl ys) ! j = ys ! j"
proof -
  from assms(1) obtain i where i: "j = Suc i" using gr0_implies_Suc by blast
  have "i < length (tl ys)" using assms(2) i by simp
  hence "(tl ys) ! i = ys ! Suc i" by (simp add: nth_tl)
  thus ?thesis using i by simp
qed

text \<open>\<open>N\<^sub>J\<close> (the core-case recursion argument of @{const Red}) and the encoding
  \<open>npJ = n\<^sub>J + 1\<close>.\<close>

definition npJ :: "pairseq \<Rightarrow> nat \<Rightarrow> nat" where
  "npJ M J = (if entry (Br M ! J) 1 0 = 0 then 0
              else Suc (THE j. nextR M 1 j (FirstNodes M ! J)))"

definition NJ :: "pairseq \<Rightarrow> nat \<Rightarrow> pairseq" where
  "NJ M J = (entry M 0 0 + Joints M ! J + 1, entry M 1 0 + npJ M J) # tl (Br M ! J)"

lemma Lng_NJ: "Br M ! J \<noteq> [] \<Longrightarrow> Lng (NJ M J) = Lng (Br M ! J)"
  by (simp add: NJ_def)

lemma entry_NJ_0_0: "entry (NJ M J) 0 0 = entry M 0 0 + Joints M ! J + 1"
  by (simp add: NJ_def entry_def)

lemma entry_NJ_1_0: "entry (NJ M J) 1 0 = entry M 1 0 + npJ M J"
  by (simp add: NJ_def entry_def)

lemma entry_NJ_hi:
  assumes "0 < j" "j < Lng (Br M ! J)"
  shows "entry (NJ M J) 0 j = entry (Br M ! J) 0 j"
proof -
  have "NJ M J ! j = Br M ! J ! j"
    unfolding NJ_def using assms by (rule nth_Cons_tl)
  thus ?thesis by (simp add: entry_def)
qed

text \<open>m: \<open>N\<^sub>J\<close> is non-multi (article [13]): for a core mono \<open>M\<close> and a branch
  index \<open>J\<close>, \<open>\<not> multiT (N\<^sub>J)\<close>.  If \<open>Br M ! J\<close> is zero, \<open>N\<^sub>J\<close> is a length-1 zero
  (core: \<open>M\<^bsub>1,0\<^esub> = 0\<close>, \<open>n\<^sub>J = -1\<close>); otherwise it is mono — its new first entry
  \<open>Joints M ! J + 1 \<le> (Br M ! J)\<^bsub>0,0\<^esub>\<close> stays strictly below the rest of the
  branch (@{thm [source] joints_lt_branch_first} + @{thm [source] monoT_row0_min}).\<close>

lemma NJ_nonmulti:
  assumes M: "M \<in> PT_PS" and core: "entry M 0 0 = 0" "entry M 1 0 = 0"
    and JBr: "J < Lng (Br M)"
  shows "\<not> multiT (NJ M J)"
proof -
  have brJne: "Br M ! J \<noteq> []" by (rule Br_component_nonempty[OF M JBr])
  have lenNJ: "Lng (NJ M J) = Lng (Br M ! J)" using brJne by (rule Lng_NJ)
  from Br_component_nonmulti[OF M JBr] show ?thesis
  proof
    assume z: "zeroT (Br M ! J)"
    have l1: "Lng (NJ M J) = 1" using z lenNJ by (simp add: zeroT_def)
    have np0: "npJ M J = 0" using z by (simp add: npJ_def zeroT_def)
    have "entry (NJ M J) 1 0 = 0" using core(2) np0 by (simp add: NJ_def entry_def)
    hence "zeroT (NJ M J)" using l1 by (simp add: zeroT_def)
    thus ?thesis by (simp add: multiT_def)
  next
    assume mo: "monoT (Br M ! J)"
    have brJTPS: "Br M ! J \<in> T_PS" using brJne by (simp add: T_PS_def)
    have NJTPS: "NJ M J \<in> T_PS" using brJne by (simp add: T_PS_def NJ_def)
    show ?thesis
    proof (cases "Lng (Br M ! J) = 1")
      case True
      \<comment> \<open>mono length-1 branch: \<open>(Br M ! J)\<^bsub>1,0\<^esub> \<noteq> 0\<close>, so \<open>npJ > 0\<close> and \<open>N\<^sub>J\<close> is a
        length-1 mono.\<close>
      have e10: "entry (Br M ! J) 1 0 \<noteq> 0" using mo True by (auto simp: monoT_def zeroT_def)
      hence np_pos: "0 < npJ M J" by (simp add: npJ_def)
      have l1: "Lng (NJ M J) = 1" using True lenNJ by simp
      have "entry (NJ M J) 1 0 = npJ M J" using core(2) by (simp add: NJ_def entry_def)
      hence nz: "\<not> zeroT (NJ M J)" using np_pos by (simp add: zeroT_def)
      have "leR (NJ M J) 0 0 (Lng (NJ M J) - 1)"
        using l1 by (simp add: leR_def le0_refl)
      hence "monoT (NJ M J)" using nz by (simp add: monoT_def)
      thus ?thesis by (simp add: multiT_def)
    next
      case False
      have brL2: "Lng (Br M ! J) > 1" using brJne False by (cases "Br M ! J") auto
      have nz: "\<not> zeroT (NJ M J)" using lenNJ brL2 by (simp add: zeroT_def)
      have key: "\<forall>j. 0 < j \<and> j \<le> Lng (NJ M J) - 1
                   \<longrightarrow> entry (NJ M J) 0 0 < entry (NJ M J) 0 j"
      proof (intro allI impI)
        fix j assume jb: "0 < j \<and> j \<le> Lng (NJ M J) - 1"
        hence j0: "0 < j" and jle: "j \<le> Lng (NJ M J) - 1" by simp_all
        have jlt: "j < Lng (Br M ! J)" using jle lenNJ brL2 by linarith
        have eNJ0: "entry (NJ M J) 0 0 = Joints M ! J + 1"
          using core(1) by (simp add: NJ_def entry_def)
        have eNJj: "entry (NJ M J) 0 j = entry (Br M ! J) 0 j" using j0 jlt by (rule entry_NJ_hi)
        have K: "Joints M ! J + 1 \<le> entry (Br M ! J) 0 0"
          using joints_lt_branch_first[OF M JBr] core(1) by simp
        have mn: "entry (Br M ! J) 0 0 < entry (Br M ! J) 0 j"
          by (rule monoT_row0_min[OF brJTPS mo j0 jlt])
        show "entry (NJ M J) 0 0 < entry (NJ M J) 0 j" using eNJ0 eNJj K mn by simp
      qed
      have Lpos: "0 < Lng (NJ M J) - 1" using lenNJ brL2 by linarith
      have Llt: "Lng (NJ M J) - 1 < Lng (NJ M J)" using lenNJ brL2 by linarith
      have NJpos: "0 < Lng (NJ M J)" using lenNJ brL2 by linarith
      have "(nextrel0 (NJ M J))\<^sup>*\<^sup>* 0 (Lng (NJ M J) - 1)"
        by (rule le0_build[OF NJTPS Llt Lpos]) (use key in simp)
      hence "le0 (NJ M J) 0 (Lng (NJ M J) - 1)" using Llt NJpos by (simp add: le0_def)
      hence "leR (NJ M J) 0 0 (Lng (NJ M J) - 1)" by (simp add: leR_def)
      hence "monoT (NJ M J)" using nz by (simp add: monoT_def)
      thus ?thesis by (simp add: multiT_def)
    qed
  qed
qed

subsection \<open>The termination measure \<open>\<nu>\<close>\<close>

text \<open>\<open>muMono M\<close>: the core measure for mono/zero sequences.  Core (\<open>hd = (0,0)\<close>):
  \<open>2\<beta>\<close>.  Non-core: \<open>2\<beta>(coreReduce M) + 1\<close>, one above the core element it reduces
  to.  \<open>nu M\<close> lifts it over multi via the \<open>P\<close>-blocks (which are zero/mono by
  @{thm [source] m_6_2_P_components_1}, so \<open>nu\<close> needs no recursion).\<close>

definition muMono :: "pairseq \<Rightarrow> nat" where
  "muMono M = (if entry M 0 0 = 0 \<and> entry M 1 0 = 0 then 2 * betaM M
               else 2 * betaM (coreReduce M) + 1)"

definition nu :: "pairseq \<Rightarrow> nat" where
  "nu M = (if multiT M then 1 + sum_list (map muMono (P M)) else muMono M)"

lemma betaM_pos:
  assumes "M \<in> T_PS"
  shows "1 \<le> betaM M"
proof -
  have L: "Lng M > 0" using assms by (cases M) (auto simp: T_PS_def)
  have T: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF assms])
  from L T show ?thesis unfolding betaM_def by linarith
qed

text \<open>Per-case descent of \<open>nu\<close> along @{const Red}'s recursive calls.\<close>

lemma nu_Pblock_lt:
  assumes M: "M \<in> T_PS" and multi: "multiT M" and x: "x \<in> set (P M)"
  shows "nu x < nu M"
proof -
  have nuM: "nu M = 1 + sum_list (map muMono (P M))" using multi by (simp add: nu_def)
  have x_nm: "\<not> multiT x" using m_6_2_P_components_1[OF M] x by (auto simp: multiT_def)
  have mem: "muMono x \<in> set (map muMono (P M))" using x by simp
  have "nu x = muMono x" using x_nm by (simp add: nu_def)
  also have "muMono x \<le> sum_list (map muMono (P M))" by (rule member_le_sum_list[OF mem]) simp
  finally show ?thesis using nuM by linarith
qed

lemma nu_coreReduce_lt:
  assumes M: "M \<in> T_PS" and mono: "monoT M"
    and noncore: "\<not> (entry M 0 0 = 0 \<and> entry M 1 0 = 0)"
  shows "nu (coreReduce M) < nu M"
proof -
  have nmM: "\<not> multiT M" using mono by (simp add: multiT_def)
  have muM: "muMono M = 2 * betaM (coreReduce M) + 1"
    unfolding muMono_def by (rule if_not_P[OF noncore])
  have nuM: "nu M = 2 * betaM (coreReduce M) + 1" using nmM muM by (simp add: nu_def)
  have cr_nm: "\<not> multiT (coreReduce M)" by (rule coreReduce_nonmulti[OF M mono])
  have cr_core: "entry (coreReduce M) 0 0 = 0 \<and> entry (coreReduce M) 1 0 = 0"
    by (rule coreReduce_core[OF M])
  have "nu (coreReduce M) = muMono (coreReduce M)" using cr_nm by (simp add: nu_def)
  also have "\<dots> = 2 * betaM (coreReduce M)" using cr_core by (simp add: muMono_def)
  finally show ?thesis using nuM by simp
qed

lemma nu_NJ_lt:
  assumes M: "M \<in> PT_PS" and core: "entry M 0 0 = 0" "entry M 1 0 = 0"
    and JBr: "J < Lng (Br M)"
  shows "nu (NJ M J) < nu M"
proof -
  have MT: "M \<in> T_PS" and mono: "monoT M" using M by (simp_all add: PT_PS_def)
  have nmM: "\<not> multiT M" using mono by (simp add: multiT_def)
  have nuM: "nu M = 2 * betaM M" using nmM core by (simp add: nu_def muMono_def)
  have nj_nm: "\<not> multiT (NJ M J)" by (rule NJ_nonmulti[OF M core JBr])
  have nj_noncore: "\<not> (entry (NJ M J) 0 0 = 0 \<and> entry (NJ M J) 1 0 = 0)"
  proof -
    have "entry (NJ M J) 0 0 = entry M 0 0 + Joints M ! J + 1" by (simp add: NJ_def entry_def)
    thus ?thesis by simp
  qed
  have muNJ: "muMono (NJ M J) = 2 * betaM (coreReduce (NJ M J)) + 1"
    unfolding muMono_def by (rule if_not_P[OF nj_noncore])
  have nuNJ: "nu (NJ M J) = 2 * betaM (coreReduce (NJ M J)) + 1"
    using nj_nm muNJ by (simp add: nu_def)
  have brJne: "Br M ! J \<noteq> []" by (rule Br_component_nonempty[OF M JBr])
  have NJTPS: "NJ M J \<in> T_PS" using brJne by (simp add: T_PS_def NJ_def)
  have bcr: "betaM (coreReduce (NJ M J)) \<le> Lng (NJ M J)" by (rule betaM_coreReduce_le[OF NJTPS])
  have lenNJ: "Lng (NJ M J) = Lng (Br M ! J)" using brJne by (rule Lng_NJ)
  have brbound: "Lng (Br M ! J) \<le> Lng M - TrMax M - 1" by (rule Lng_Br_le[OF JBr])
  have bpos: "1 \<le> betaM M" by (rule betaM_pos[OF MT])
  have "Lng (NJ M J) \<le> betaM M - 1" using lenNJ brbound by (simp add: betaM_def)
  with bcr bpos show ?thesis using nuNJ nuM by linarith
qed

text \<open>m: 命題（\<open>Red\<close> の well-defined 性） — discharges
  @{thm [source] p_6_5_Red_welldef}.  \<open>Red\<close> terminates on \<open>T\<^sub>PS\<close> by well-founded
  induction on the measure @{const nu}; each of the five @{thm [source] Red.domintros}
  premises has strictly smaller \<open>nu\<close> (steps a–d) and stays in \<open>T\<^sub>PS\<close>.\<close>

lemma m_6_5_Red_welldef:
  assumes "M \<in> T_PS"
  shows "Red_dom M"
proof -
  have "M \<in> T_PS \<longrightarrow> Red_dom M"
  proof (induction M rule: measure_induct_rule[where f=nu])
    case (less M)
    show ?case
    proof (rule impI)
      assume MT: "M \<in> T_PS"
      have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
      have LM1: "1 \<le> Lng M" using Mne by (cases M) auto
      show "Red_dom M"
      proof (rule Red.domintros)
        fix y assume mu: "multiT M"
          and yin: "y \<in> set (if Suc 0 < Lng M
                              then P (take (Pcut M) M) @ [drop (Pcut M) M] else [M])"
        have L1: "Lng M > 1" by (rule multiT_imp_Lng_gt1[OF MT mu])
        have "P M = P (take (Pcut M) M) @ [drop (Pcut M) M]"
          using mu L1 by (subst P.simps) simp
        hence ypm: "y \<in> set (P M)" using yin L1 by simp
        have yT: "y \<in> T_PS" using P_blocks_nonempty[OF Mne] ypm by (auto simp: T_PS_def)
        have "nu y < nu M" by (rule nu_Pblock_lt[OF MT mu ypm])
        thus "Red_dom y" using less.IH yT by blast
      next
        fix xd assume nz: "\<not> zeroT M" and nmu: "\<not> multiT M"
          and c0: "entry M 0 0 = 0" and c1: "entry M (Suc 0) 0 = 0"
          and JBr: "xd < Lng (Br M)" and bz: "entry (Br M ! xd) (Suc 0) 0 = 0"
        have mono: "monoT M" using nz nmu by (simp add: multiT_def)
        have Mpt: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
        have c1': "entry M 1 0 = 0" using c1 by simp
        have eq: "(Suc (Joints M ! xd), 0) # tl (Br M ! xd) = NJ M xd"
          using c0 c1 bz by (simp add: NJ_def npJ_def)
        have argT: "(Suc (Joints M ! xd), 0) # tl (Br M ! xd) \<in> T_PS" by (simp add: T_PS_def)
        have "nu (NJ M xd) < nu M" by (rule nu_NJ_lt[OF Mpt c0 c1' JBr])
        hence "nu ((Suc (Joints M ! xd), 0) # tl (Br M ! xd)) < nu M" using eq by simp
        thus "Red_dom ((Suc (Joints M ! xd), 0) # tl (Br M ! xd))"
          using less.IH argT by blast
      next
        fix xd assume nz: "\<not> zeroT M" and nmu: "\<not> multiT M"
          and c0: "entry M 0 0 = 0" and c1: "entry M (Suc 0) 0 = 0"
          and JBr: "xd < Lng (Br M)" and bp: "0 < entry (Br M ! xd) (Suc 0) 0"
        have mono: "monoT M" using nz nmu by (simp add: multiT_def)
        have Mpt: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
        have c1': "entry M 1 0 = 0" using c1 by simp
        have eq: "(Suc (Joints M ! xd), Suc (THE j. nextR M (Suc 0) j (FirstNodes M ! xd)))
                    # tl (Br M ! xd) = NJ M xd"
          using c0 c1 bp by (simp add: NJ_def npJ_def)
        have argT: "(Suc (Joints M ! xd), Suc (THE j. nextR M (Suc 0) j (FirstNodes M ! xd)))
                      # tl (Br M ! xd) \<in> T_PS" by (simp add: T_PS_def)
        have "nu (NJ M xd) < nu M" by (rule nu_NJ_lt[OF Mpt c0 c1' JBr])
        hence "nu ((Suc (Joints M ! xd),
                    Suc (THE j. nextR M (Suc 0) j (FirstNodes M ! xd))) # tl (Br M ! xd)) < nu M"
          using eq by simp
        thus "Red_dom ((Suc (Joints M ! xd),
                Suc (THE j. nextR M (Suc 0) j (FirstNodes M ! xd))) # tl (Br M ! xd))"
          using less.IH argT by blast
      next
        assume nz: "\<not> zeroT M" and nmu: "\<not> multiT M"
          and c1: "entry M (Suc 0) 0 = 0" and c0p: "0 < entry M 0 0"
        have mono: "monoT M" using nz nmu by (simp add: multiT_def)
        have noncore: "\<not> (entry M 0 0 = 0 \<and> entry M 1 0 = 0)" using c0p by simp
        let ?f = "\<lambda>j. (entry M 0 j - entry M 0 0, entry M (Suc 0) j)"
        have split: "[0..<Lng M] = [0..<Lng M - Suc 0] @ [Lng M - Suc 0]"
        proof -
          have eq: "Lng M = Suc (Lng M - Suc 0)" using LM1 by simp
          thus ?thesis using upt_Suc_append[of 0 "Lng M - Suc 0"] by (simp del: upt_Suc)
        qed
        have argeq: "map ?f [0..<Lng M - Suc 0] @ [?f (Lng M - Suc 0)] = coreReduce M"
          using c1 split by (simp add: coreReduce_def)
        have argT: "map ?f [0..<Lng M - Suc 0] @ [?f (Lng M - Suc 0)] \<in> T_PS" by (simp add: T_PS_def)
        have "nu (coreReduce M) < nu M" by (rule nu_coreReduce_lt[OF MT mono noncore])
        hence "nu (map ?f [0..<Lng M - Suc 0] @ [?f (Lng M - Suc 0)]) < nu M" using argeq by simp
        thus "Red_dom (map ?f [0..<Lng M - Suc 0] @ [?f (Lng M - Suc 0)])"
          using less.IH argT by blast
      next
        assume nz: "\<not> zeroT M" and nmu: "\<not> multiT M" and c1p: "0 < entry M (Suc 0) 0"
        have mono: "monoT M" using nz nmu by (simp add: multiT_def)
        have noncore: "\<not> (entry M 0 0 = 0 \<and> entry M 1 0 = 0)" using c1p by simp
        have argeq: "diagSeq 0 (entry M (Suc 0) 0 - Suc 0) @ (IncrFirst ^^ entry M (Suc 0) 0) M
                       = coreReduce M"
          using c1p by (simp add: coreReduce_def)
        have iFne: "(IncrFirst ^^ entry M (Suc 0) 0) M \<noteq> []"
          using Mne by (metis Lng_funpow_IncrFirst length_0_conv)
        have argT: "diagSeq 0 (entry M (Suc 0) 0 - Suc 0) @ (IncrFirst ^^ entry M (Suc 0) 0) M
                      \<in> T_PS" using iFne by (simp add: T_PS_def)
        have "nu (coreReduce M) < nu M" by (rule nu_coreReduce_lt[OF MT mono noncore])
        hence "nu (diagSeq 0 (entry M (Suc 0) 0 - Suc 0)
                    @ (IncrFirst ^^ entry M (Suc 0) 0) M) < nu M" using argeq by simp
        thus "Red_dom (diagSeq 0 (entry M (Suc 0) 0 - Suc 0)
                @ (IncrFirst ^^ entry M (Suc 0) 0) M)"
          using less.IH argT by blast
      qed
    qed
  qed
  thus ?thesis using assms by blast
qed

text \<open>m: 命題（Lng の Red 不変性） — discharges p_6_5_Lng_Red.\<close>
lemma m_6_5_Lng_Red:
  assumes MT: "M \<in> T_PS"
  shows "Lng (Red M) = Lng M"
proof -
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  \<comment> \<open>The property we prove by Red.pinduct induction.\<close>
  have "M \<in> T_PS \<longrightarrow> Lng (Red M) = Lng M"
    using domM
  proof (induction M rule: Red.pinduct)
    case (1 M)
    \<comment> \<open>One single case covering all branches; we case-split manually.\<close>
    note dom    = 1(1)
    note IH_mu  = 1(2)  \<comment> \<open>multiT IH: x∈set(P M) ⟹ Lng(Red x) = Lng x\<close>
    note IH_bz  = 1(3)  \<comment> \<open>core-branch IH (e10=0)\<close>
    note IH_nc3 = 1(4)  \<comment> \<open>non-core m10=0 IH\<close>
    note IH_nc4 = 1(5)  \<comment> \<open>non-core m10>0 IH\<close>
    show ?case
    proof (rule impI)
      assume MT': "M \<in> T_PS"
      have Mne: "M \<noteq> []" using MT' by (simp add: T_PS_def)
      have LMpos: "0 < Lng M" using Mne by (cases M) auto
      show "Lng (Red M) = Lng M"
      proof (cases "zeroT M")
        \<comment> \<open>Branch 1: zeroT M.  Red M = [(0,0)], Lng 1 = Lng M.\<close>
        case True
        have rM: "Red M = [(0, 0)]"
          using Red.psimps[OF dom] True by simp
        thus ?thesis using True by (simp add: rM zeroT_def)
      next
        case nz: False
        show "Lng (Red M) = Lng M"
        proof (cases "multiT M")
          \<comment> \<open>Branch 2: multiT M.  Red M = concat(map Red (P M)).\<close>
          case True
          have rM: "Red M = concat (map Red (P M))"
            using Red.psimps[OF dom] nz True by simp
          have L1: "1 < Lng M" by (rule multiT_imp_Lng_gt1[OF MT' True])
          \<comment> \<open>Bring P M into form the IH_mu was stated with.\<close>
          have pmset: "(if Suc 0 < Lng M
                        then P (take (Pcut M) M) @ [drop (Pcut M) M] else [M])
                      = P M"
            using L1 True by (subst P.simps) simp
          have IH': "\<forall>y \<in> set (P M). Lng (Red y) = Lng y"
          proof
            fix y assume y: "y \<in> set (P M)"
            have yT: "y \<in> T_PS" using P_blocks_nonempty[OF Mne] y by (auto simp: T_PS_def)
            have ih: "y \<in> T_PS \<longrightarrow> Lng (Red y) = Lng y"
              by (rule IH_mu[OF nz True y])
            thus "Lng (Red y) = Lng y" using yT ih by blast
          qed
          have "Lng (Red M) = Lng (concat (map Red (P M)))"
            by (simp add: rM)
          also have "\<dots> = Lng (concat (P M))"
          proof -
            have leneq: "\<And>y. y \<in> set (P M) \<Longrightarrow> Lng (Red y) = Lng y"
              using IH' by blast
            have steps: "map (Lng \<circ> Red) (P M) = map Lng (P M)"
              by (rule map_cong[OF refl]) (simp add: leneq)
            have "Lng (concat (map Red (P M))) = Lng (concat (P M))"
              by (simp only: length_concat map_map steps)
            thus ?thesis by (simp add: rM)
          qed
          also have "\<dots> = Lng M" by (simp add: poper_concat_P)
          finally show ?thesis .
        next
          \<comment> \<open>Branches 3–5: mono (¬ zeroT, ¬ multiT). Use Let_def to expose sub-cases.\<close>
          case nmu: False
          have mono: "monoT M" using nz nmu by (simp add: multiT_def)
          have Mpt: "M \<in> PT_PS" using MT' mono by (simp add: PT_PS_def)
          let ?j1  = "Lng M - 1"
          let ?j1' = "TrMax M"
          let ?m00 = "entry M 0 0"
          let ?m10 = "entry M 1 0"
          show "Lng (Red M) = Lng M"
          proof (cases "?m00 = 0 \<and> ?m10 = 0")
            \<comment> \<open>Core case: M starts at (0,0).\<close>
            case core: True
            hence c0: "?m00 = 0" and c1: "?m10 = 0" by simp_all
            show ?thesis
            proof (cases "?j1' = ?j1")
              \<comment> \<open>Branch 3a: TrMax = Lng-1; diagonal output.\<close>
              case True
              have rM: "Red M = diagSeq ?m10 (?m10 + ?j1)"
                using Red.psimps[OF dom] nz nmu c0 c1 True
                by (simp add: Let_def)
              have "Lng (Red M) = Suc (?m10 + ?j1) - ?m10"
                by (simp add: rM)
              also have "\<dots> = Lng M" using LMpos c1 by simp
              finally show ?thesis .
            next
              \<comment> \<open>Branch 3b: TrMax ≠ Lng-1; diagonal prefix + branches.\<close>
              case tne: False
              have trlt: "?j1' < Lng M - 1"
                using TrMax_bound[OF MT'] tne LMpos by linarith
              \<comment> \<open>IH for each branch index J: Lng(Red(NJ M J)) = Lng(Br M ! J).\<close>
              have IH_NJ: "\<And>J. J < Lng (Br M) \<Longrightarrow>
                    Lng (Red (NJ M J)) = Lng (Br M ! J)"
              proof -
                fix J assume JBr: "J < Lng (Br M)"
                have brJne: "Br M ! J \<noteq> []"
                  by (rule Br_component_nonempty[OF Mpt JBr])
                \<comment> \<open>The IH_bz from pinduct gives us what we need.\<close>
                have J_in: "J \<in> set [0..<Lng (Br M)]"
                  using JBr by simp
                have arg_T: "(entry M 0 0 + Joints M ! J + 1,
                              entry M 1 0 + (if entry (Br M ! J) 1 0 = 0 then 0
                                             else Suc (THE j. nextR M 1 j (FirstNodes M ! J))))
                             # tl (Br M ! J) \<in> T_PS"
                  by (simp add: T_PS_def)
                let ?arg = "(entry M 0 0 + Joints M ! J + 1,
                              entry M 1 0 + (if entry (Br M ! J) 1 0 = 0 then 0
                                             else Suc (THE j. nextR M 1 j (FirstNodes M ! J))))
                             # tl (Br M ! J)"
                have NJ_eq: "?arg = NJ M J"
                  by (simp add: NJ_def npJ_def)
                have IH_J: "Lng (Red ?arg) = Lng ?arg"
                  using IH_bz[OF nz nmu refl refl refl refl _ tne J_in] c0 c1 arg_T
                  by (auto simp: c0 c1)
                have Largarg: "Lng ?arg = Lng (Br M ! J)"
                  using brJne by (simp add: NJ_def)
                show "Lng (Red (NJ M J)) = Lng (Br M ! J)"
                  using IH_J NJ_eq Largarg by (simp add: NJ_def)
              qed
              \<comment> \<open>Unfold Red M in this branch.\<close>
              have rM: "Red M = diagSeq 0 ?j1' @
                    concat (map (\<lambda>J.
                        (IncrFirst ^^ (Joints M ! J + 1
                            - (if entry (Br M ! J) 1 0 = 0 then 0
                               else Suc (THE j. nextR M 1 j (FirstNodes M ! J)))))
                          (Red ((entry M 0 0 + Joints M ! J + 1,
                                 entry M 1 0 + (if entry (Br M ! J) 1 0 = 0 then 0
                                        else Suc (THE j. nextR M 1 j (FirstNodes M ! J))))
                                # tl (Br M ! J))))
                      [0..<Lng (Br M)])"
                using Red.psimps[OF dom] nz nmu c0 c1 tne
                by (simp add: Let_def)
              \<comment> \<open>Compute Lng step by step.\<close>
              \<comment> \<open>Abbreviate the branch arg.\<close>
              let ?f = "\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1
                            - (if entry (Br M ! J) 1 0 = 0 then 0
                               else Suc (THE j. nextR M 1 j (FirstNodes M ! J)))))
                          (Red ((entry M 0 0 + Joints M ! J + 1,
                                 entry M 1 0 + (if entry (Br M ! J) 1 0 = 0 then 0
                                        else Suc (THE j. nextR M 1 j (FirstNodes M ! J))))
                                # tl (Br M ! J)))"
              have "Lng (Red M) = Suc ?j1' + Lng (concat (map ?f [0..<Lng (Br M)]))"
                by (simp add: rM)
              also have "\<dots> = Suc ?j1' + sum_list (map (Lng \<circ> ?f) [0..<Lng (Br M)])"
                by (simp add: length_concat map_map)
              also have "\<dots> = Suc ?j1' + sum_list (map (\<lambda>J. Lng (Br M ! J)) [0..<Lng (Br M)])"
              proof (rule arg_cong[where f="\<lambda>x. Suc ?j1' + x"])
                show "sum_list (map (Lng \<circ> ?f) [0..<Lng (Br M)]) =
                      sum_list (map (\<lambda>J. Lng (Br M ! J)) [0..<Lng (Br M)])"
                proof (rule arg_cong[where f=sum_list], rule map_cong[OF refl])
                  fix J assume J: "J \<in> set [0..<Lng (Br M)]"
                  hence JBr': "J < Lng (Br M)" by simp
                  have NJ_J_eq: "(entry M 0 0 + Joints M ! J + 1,
                                  entry M 1 0 + (if entry (Br M ! J) 1 0 = 0 then 0
                                                 else Suc (THE j. nextR M 1 j (FirstNodes M ! J))))
                                 # tl (Br M ! J) = NJ M J"
                    by (simp add: NJ_def npJ_def)
                  show "(Lng \<circ> ?f) J = Lng (Br M ! J)"
                  proof -
                    have fJ: "?f J = (IncrFirst ^^ (Joints M ! J + 1
                            - (if entry (Br M ! J) 1 0 = 0 then 0
                               else Suc (THE j. nextR M 1 j (FirstNodes M ! J)))))
                          (Red ((entry M 0 0 + Joints M ! J + 1,
                                 entry M 1 0 + (if entry (Br M ! J) 1 0 = 0 then 0
                                        else Suc (THE j. nextR M 1 j (FirstNodes M ! J))))
                                # tl (Br M ! J)))"
                      by simp
                    have "(Lng \<circ> ?f) J = Lng (Red ((entry M 0 0 + Joints M ! J + 1,
                                 entry M 1 0 + (if entry (Br M ! J) 1 0 = 0 then 0
                                        else Suc (THE j. nextR M 1 j (FirstNodes M ! J))))
                                # tl (Br M ! J)))"
                      using fJ by (simp add: Lng_funpow_IncrFirst)
                    also have "\<dots> = Lng (Red (NJ M J))"
                      by (simp only: NJ_J_eq)
                    also have "\<dots> = Lng (Br M ! J)"
                      using IH_NJ[OF JBr'] .
                    finally show ?thesis .
                  qed
                qed
              qed
              also have "\<dots> = Suc ?j1' + Lng (concat (Br M))"
              proof -
                have "sum_list (map (\<lambda>J. Lng (Br M ! J)) [0..<Lng (Br M)]) = Lng (concat (Br M))"
                proof -
                  have "map (\<lambda>J. Lng (Br M ! J)) [0..<Lng (Br M)] = map Lng (Br M)"
                    by (rule nth_equalityI) (auto simp: map_nth)
                  thus ?thesis by (simp add: length_concat)
                qed
                thus ?thesis by simp
              qed
              also have "\<dots> = Suc ?j1' + Lng (seg M (?j1' + 1) (Lng M - 1))"
                using trlt by (simp add: Br_def poper_concat_P)
              also have "\<dots> = Suc ?j1' + (Suc (Lng M - 1) - (?j1' + 1))"
                by (simp only: Lng_seg)
              also have "\<dots> = Lng M" using trlt LMpos by simp
              finally show ?thesis .
            qed
          next
            \<comment> \<open>Non-core case: M doesn't start at (0,0).\<close>
            case nc: False
            show ?thesis
            proof (cases "?m10 = 0")
              \<comment> \<open>Branch 4: m10=0 (but m00≠0).  Red M = Red(shift).\<close>
              case True
              have c0p: "0 < ?m00" using nc True by simp
              have rM: "Red M = Red (map (\<lambda>j. (entry M 0 j - ?m00, entry M 1 j))
                                        [0..<Suc ?j1])"
                using Red.psimps[OF dom] nz nmu nc True
                by (simp add: Let_def)
              have shift_T: "map (\<lambda>j. (entry M 0 j - ?m00, entry M 1 j)) [0..<Suc ?j1] \<in> T_PS"
                by (simp add: T_PS_def)
              have IH': "Lng (Red (map (\<lambda>j. (entry M 0 j - ?m00, entry M 1 j))
                                       [0..<Suc ?j1])) =
                         Lng (map (\<lambda>j. (entry M 0 j - ?m00, entry M 1 j)) [0..<Suc ?j1])"
                using IH_nc3[OF nz nmu refl refl refl refl nc True] shift_T
                by blast
              have "Lng (Red M) = Lng (map (\<lambda>j. (entry M 0 j - ?m00, entry M 1 j))
                                             [0..<Suc ?j1])"
                using rM IH' by simp
              also have "\<dots> = Lng M" using LMpos by simp
              finally show ?thesis .
            next
              \<comment> \<open>Branch 5: m10>0. Red M uses N = Red(diagSeq ++ IncrFirst M).\<close>
              case False
              hence c1p: "0 < ?m10" by simp
              let ?arg = "diagSeq 0 (?m10 - 1) @ (IncrFirst ^^ ?m10) M"
              have funpow_ne: "(IncrFirst ^^ ?m10) M \<noteq> []"
                using Mne by (metis Lng_funpow_IncrFirst length_0_conv)
              have arg_T: "?arg \<in> T_PS"
                using funpow_ne by (simp add: T_PS_def)
              have c1p': "?m10 \<noteq> 0" using c1p by simp
              have IH': "Lng (Red ?arg) = Lng ?arg"
                using IH_nc4[OF nz nmu refl refl refl refl nc c1p'] arg_T
                by blast
              have Larg: "Lng ?arg = ?m10 + Lng M"
                using c1p by (simp add: Lng_funpow_IncrFirst)
              have LN: "Lng (Red ?arg) = ?m10 + Lng M"
                using IH' Larg by simp
              have rM: "Red M = (let N = Red ?arg; jN = Lng N - 1 in
                         if ?m10 \<le> jN \<and> seg N ?m10 jN \<in> PT_PS then
                           map (\<lambda>j. (entry N 0 j - entry N 0 ?m10 + entry N 1 ?m10,
                                     entry N 1 j))
                               [?m10..<Suc jN]
                         else M)"
                using Red.psimps[OF dom] nz nmu nc c1p
                by (simp add: Let_def)
              show ?thesis
              proof (cases "?m10 \<le> Lng (Red ?arg) - 1 \<and>
                            seg (Red ?arg) ?m10 (Lng (Red ?arg) - 1) \<in> PT_PS")
                case True
                have "Red M = map (\<lambda>j. (entry (Red ?arg) 0 j
                                        - entry (Red ?arg) 0 ?m10
                                        + entry (Red ?arg) 1 ?m10,
                                        entry (Red ?arg) 1 j))
                                  [?m10..<Suc (Lng (Red ?arg) - 1)]"
                  using rM True by (simp add: Let_def)
                hence "Lng (Red M) = Suc (Lng (Red ?arg) - 1) - ?m10"
                  by (simp add: length_upt del: upt_Suc)
                also have "\<dots> = Lng M"
                  using LN LMpos by arith
                finally show ?thesis .
              next
                case nc5: False
                \<comment> \<open>cases False: ¬(?m10 ≤ Lng(Red arg)-1 ∧ seg...∈PT_PS)\<close>
                \<comment> \<open>Since LN, LMpos: m10 ≤ Lng(Red arg)-1 is TRUE, so seg...∉PT_PS.\<close>
                have jN_bound: "?m10 \<le> Lng (Red ?arg) - 1"
                  using LN LMpos by arith
                have seg_not_PT: "seg (Red ?arg) ?m10 (Lng (Red ?arg) - 1) \<notin> PT_PS"
                  using nc5 jN_bound by blast
                have "Red M = M"
                  using rM jN_bound seg_not_PT
                  by (simp add: Let_def)
                thus ?thesis by simp
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  thus ?thesis using MT by blast
qed


subsection \<open>§6.5 補正定義域 \<open>anchored_slice\<close> の基本性質 (correction A4)\<close>

text \<open>An ancestor-anchored slice is non-empty, hence in \<open>T\<^sub>PS\<close> (so \<open>Red\<close> is
  defined on it via @{thm [source] m_6_5_Red_welldef}).\<close>

lemma anchored_slice_imp_T_PS:
  assumes "M \<in> anchored_slice"
  shows "M \<in> T_PS"
proof -
  from assms obtain S a b where ab: "a \<le> b" and M: "M = seg S a b"
    unfolding anchored_slice_def by blast
  have "length M = Suc b - a" using M by simp
  with ab have "0 < length M" by simp
  thus ?thesis by (simp add: T_PS_def)
qed


text \<open>m: 命題（zeroT の Red 不変性） — discharges p_6_5_Red_zeroT.\<close>
\<comment> \<open>Auxiliary: when Lng M = 1, ¬ zeroT M, M ∈ T_PS, then entry (Red M) 1 0 ≠ 0.\<close>
lemma rz_Red_entry1_nz:
  assumes MT: "M \<in> T_PS" and L1: "Lng M = 1" and nz: "\<not> zeroT M"
  shows "entry (Red M) 1 0 \<noteq> 0"
proof -
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  \<comment> \<open>Lng M = 1 and ¬ zeroT M implies monoT and ¬ multiT.\<close>
  have mono: "monoT M" using L1 nz by (simp add: monoT_def leR_def le0_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  let ?m10 = "entry M 1 0"
  have m10pos: "0 < ?m10" using nz L1 by (simp add: zeroT_def)
  \<comment> \<open>¬ core: m10 > 0 implies ¬ (m00 = 0 \<and> m10 = 0).\<close>
  have nc: "\<not> (entry M 0 0 = 0 \<and> ?m10 = 0)" using m10pos by simp
  \<comment> \<open>Red M unfolds to the m10>0 non-core branch.\<close>
  let ?arg = "diagSeq 0 (?m10 - 1) @ (IncrFirst ^^ ?m10) M"
  have rM: "Red M = (let N = Red ?arg; jN = Lng N - 1 in
             if ?m10 \<le> jN \<and> seg N ?m10 jN \<in> PT_PS then
               map (\<lambda>j. (entry N 0 j - entry N 0 ?m10 + entry N 1 ?m10,
                         entry N 1 j))
                   [?m10..<Suc jN]
             else M)"
    using Red.psimps[OF domM] nz nmu nc m10pos
    by (simp add: Let_def)
  \<comment> \<open>arg is in T_PS (non-empty).\<close>
  have funpow_ne: "(IncrFirst ^^ ?m10) M \<noteq> []"
    using Mne by (metis Lng_funpow_IncrFirst length_0_conv)
  have arg_T: "?arg \<in> T_PS" using funpow_ne by (simp add: T_PS_def)
  \<comment> \<open>Lng (Red arg) = Lng arg = m10 + 1.\<close>
  have Larg1: "Lng ?arg = ?m10 + 1"
    using m10pos L1 by (simp add: Lng_funpow_IncrFirst)
  have LN: "Lng (Red ?arg) = ?m10 + 1"
    using m_6_5_Lng_Red[OF arg_T] Larg1 by simp
  \<comment> \<open>jN = m10, so m10 \<le> jN holds.\<close>
  have jN_eq: "Lng (Red ?arg) - 1 = ?m10" using LN m10pos by simp
  have m10_le: "?m10 \<le> Lng (Red ?arg) - 1" using jN_eq by simp
  \<comment> \<open>Case split on whether seg (Red arg) m10 m10 \<in> PT_PS.\<close>
  show "entry (Red M) 1 0 \<noteq> 0"
  proof (cases "seg (Red ?arg) ?m10 (Lng (Red ?arg) - 1) \<in> PT_PS")
    case ptps: True
    \<comment> \<open>Red M = [(entry N 1 m10, entry N 1 m10)].\<close>
    have rM': "Red M = map (\<lambda>j. (entry (Red ?arg) 0 j - entry (Red ?arg) 0 ?m10
                                  + entry (Red ?arg) 1 ?m10,
                                  entry (Red ?arg) 1 j))
                            [?m10..<Suc (Lng (Red ?arg) - 1)]"
      using rM ptps m10_le by (simp add: Let_def)
    have rM'': "Red M = [(entry (Red ?arg) 1 ?m10, entry (Red ?arg) 1 ?m10)]"
      using rM' jN_eq by simp
    \<comment> \<open>seg N m10 m10 \<in> PT_PS \<Longrightarrow> monoT \<Longrightarrow> \<not> zeroT \<Longrightarrow> entry N 1 m10 \<noteq> 0.\<close>
    have seg_len1: "Lng (seg (Red ?arg) ?m10 ?m10) = 1"
      using LN m10pos by simp
    have seg_mono: "monoT (seg (Red ?arg) ?m10 ?m10)"
      using ptps jN_eq by (simp add: PT_PS_def)
    have seg_nz: "\<not> zeroT (seg (Red ?arg) ?m10 ?m10)"
      using seg_mono by (simp add: monoT_def)
    have eseg: "entry (seg (Red ?arg) ?m10 ?m10) 1 0 = entry (Red ?arg) 1 ?m10"
      using entry_seg[where M="Red ?arg" and a="?m10" and b="?m10" and i=1 and j=0]
            seg_len1 by simp
    have ne10: "entry (Red ?arg) 1 ?m10 \<noteq> 0"
    proof -
      have "entry (seg (Red ?arg) ?m10 ?m10) 1 0 \<noteq> 0"
        using seg_nz seg_len1 by (simp add: zeroT_def)
      thus ?thesis using eseg by simp
    qed
    have "entry (Red M) 1 0 = entry (Red ?arg) 1 ?m10"
      by (simp add: rM'' entry_def)
    thus "entry (Red M) 1 0 \<noteq> 0" using ne10 by simp
  next
    case False
    \<comment> \<open>Red M = M, and entry M 1 0 = m10 > 0.\<close>
    have "Red M = M" using rM m10_le False by (simp add: Let_def)
    thus ?thesis using m10pos by simp
  qed
qed

lemma m_6_5_Red_zeroT:
  assumes MT: "M \<in> T_PS"
  shows "zeroT M \<longleftrightarrow> zeroT (Red M)"
proof -
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have LR: "Lng (Red M) = Lng M" by (rule m_6_5_Lng_Red[OF MT])
  show ?thesis
  proof (rule iffI)
    \<comment> \<open>Forward: zeroT M \<Longrightarrow> Red M = [(0,0)], which is zeroT.\<close>
    assume z: "zeroT M"
    have rM: "Red M = [(0, 0)]" using Red.psimps[OF domM] z by simp
    show "zeroT (Red M)" by (simp add: rM zeroT_def entry_def)
  next
    \<comment> \<open>Backward: zeroT (Red M) \<Longrightarrow> zeroT M.
        Prove contrapositive: \<not> zeroT M \<Longrightarrow> \<not> zeroT (Red M).\<close>
    assume zRM: "zeroT (Red M)"
    show "zeroT M"
    proof (rule ccontr)
      assume nz: "\<not> zeroT M"
      \<comment> \<open>Lng (Red M) = Lng M, and zeroT (Red M) gives Lng (Red M) = 1.\<close>
      have L1: "Lng M = 1" using LR zRM by (simp add: zeroT_def)
      \<comment> \<open>entry M 1 0 \<noteq> 0 gives entry (Red M) 1 0 \<noteq> 0 by rz_Red_entry1_nz.\<close>
      have ne: "entry (Red M) 1 0 \<noteq> 0" by (rule rz_Red_entry1_nz[OF MT L1 nz])
      \<comment> \<open>But zeroT (Red M) requires entry (Red M) 1 0 = 0. Contradiction.\<close>
      thus False using zRM by (simp add: zeroT_def)
    qed
  qed
qed


section \<open>§6.7 標準形の階層和による表示\<close>

text \<open>補助補題: \<open>SkT_PS k \<subseteq> ST_PS\<close>  (帰納法 on \<open>k\<close>)\<close>

lemma SkT_PS_subset_ST_PS:
  shows "SkT_PS k \<subseteq> ST_PS"
proof (induction k)
  case 0
  \<comment> \<open>SkT_PS 0 = {diagSeq u v | u ≤ v}. Each element is in ST_PS by the diag rule.\<close>
  show "SkT_PS 0 \<subseteq> ST_PS"
  proof
    fix N assume "N \<in> SkT_PS 0"
    then obtain u v where Nuv: "N = diagSeq u v" and uv: "u \<le> v"
      by auto
    show "N \<in> ST_PS" using uv unfolding Nuv by (rule ST_PS.diag)
  qed
next
  case (Suc k)
  \<comment> \<open>SkT_PS (Suc k) = {M[n] | M ∈ SkT_PS k, 1 ≤ n}.
      By IH M ∈ ST_PS, so M[n] ∈ ST_PS by the oper rule.\<close>
  show "SkT_PS (Suc k) \<subseteq> ST_PS"
  proof
    fix N assume "N \<in> SkT_PS (Suc k)"
    then obtain M n where NMn: "N = (M::pairseq)[n]"
                      and Mk:  "M \<in> SkT_PS k"
                      and n1:  "1 \<le> n"
      by auto
    have MST: "M \<in> ST_PS" using Mk Suc.IH by blast
    show "N \<in> ST_PS" using MST n1 unfolding NMn by (rule ST_PS.oper)
  qed
qed

text \<open>m: 命題（標準形の階層和による表示） — discharges p_6_7_ST_eq_Union_SkT.
  \<open>ST_PS = \<Union>\<^sub>k SkT_PS k\<close>  (§6.7 命題, 標準形の階層和による表示)\<close>

text \<open>補助補題: \<open>ST_PS \<subseteq> \<Union>k. SkT_PS k\<close>  (ST_PS.induct で帰納)\<close>

\<comment> \<open>Introduce a wrapper predicate to avoid the ⋃ IH unfolding problem.\<close>
definition in_some_SkT :: "pairseq \<Rightarrow> bool" where
  "in_some_SkT x \<longleftrightarrow> (\<exists>k. x \<in> SkT_PS k)"

lemma ST_PS_in_some_SkT:
  "x \<in> ST_PS \<Longrightarrow> in_some_SkT x"
proof (induct x rule: ST_PS.induct)
  \<comment> \<open>diag case: diagSeq u v ∈ SkT_PS 0.\<close>
  case (diag u v)
  have "diagSeq u v \<in> SkT_PS 0" using diag by auto
  thus "in_some_SkT (diagSeq u v)" unfolding in_some_SkT_def by blast
next
  \<comment> \<open>oper case: in_some_SkT M (IH) ⟹ in_some_SkT M[n].\<close>
  case (oper M n)
  \<comment> \<open>oper.hyps: (1) M ∈ ST_PS, (2) in_some_SkT M (IH), (3) 1 ≤ n\<close>
  from oper.hyps(2) obtain k where Mk: "M \<in> SkT_PS k"
    unfolding in_some_SkT_def by blast
  have "(M::pairseq)[n] \<in> SkT_PS (Suc k)" using Mk oper.hyps(3) by auto
  thus "in_some_SkT ((M::pairseq)[n])" unfolding in_some_SkT_def by blast
qed

lemma ST_PS_subset_Union_SkT:
  "x \<in> ST_PS \<Longrightarrow> x \<in> (\<Union>k. SkT_PS k)"
  using ST_PS_in_some_SkT unfolding in_some_SkT_def by blast

lemma m_6_7_ST_eq_Union_SkT:
  shows "ST_PS = (\<Union>k. SkT_PS k)"
  using ST_PS_subset_Union_SkT SkT_PS_subset_ST_PS by blast


text \<open>m: 補題（Redと左端の関係） (1) — discharges @{thm [source] p_6_6_Red_leftend_1}.
  Red preserves the row-1 left end: \<open>entry (Red M) 1 0 = entry M 1 0\<close>.

  Proof sketch: by Red.pinduct.  In each branch of the Red recursion:
  (1) zeroT: Red M = [(0,0)], entry M 1 0 = 0.
  (2) multiT: concat first block reduces to P M ! 0 whose leftend = entry M 1 0 (via m_6_4_P_IdxSum).
  (3a) core trunk: diagSeq 0 j1, entry at 0 = 0 = m10.
  (3b) core non-trunk: diagSeq 0 j1' prefix, entry at 0 = 0 = m10.
  (4) m10=0 shift: IH on shiftRow0 M, entry shiftRow0 1 0 = entry M 1 0.
  (5) m10>0 else: Red M = M, trivial.
  (5) m10>0 then: arg = coreReduce M is monoT (coreReduce_monoT_m10_pos), starts at (0,0),
      TrMax arg >= m10 (TrMax_diagSeq_append_ge), so Red arg opens as diagSeq 0 (TrMax arg) prefix
      and entry N 1 m10 = m10 by entry_diagSeq / entry_diagSeq_append_lo.\<close>

lemma m_6_6_Red_leftend_1:
  assumes MT: "M \<in> T_PS"
  shows "entry (Red M) 1 0 = entry M 1 0"
proof -
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have "M \<in> T_PS \<longrightarrow> entry (Red M) 1 0 = entry M 1 0"
    using domM
  proof (induction M rule: Red.pinduct)
    case (1 M)
    note dom    = 1(1)
    note IH_mu  = 1(2)
    note IH_nc3 = 1(4)
    show ?case
    proof (rule impI)
      assume MT': "M \<in> T_PS"
      have Mne: "M \<noteq> []" using MT' by (simp add: T_PS_def)
      have LMpos: "0 < Lng M" using Mne by (cases M) auto
      show "entry (Red M) 1 0 = entry M 1 0"
      proof (cases "zeroT M")
        \<comment> \<open>Branch 1: zeroT M.  Red M = [(0,0)], entry M 1 0 = 0.\<close>
        case True
        have rM: "Red M = [(0, 0)]"
          using Red.psimps[OF dom] True by simp
        have "entry M 1 0 = 0" using True by (simp add: zeroT_def)
        thus ?thesis by (simp add: rM entry_def)
      next
        case nz: False
        show "entry (Red M) 1 0 = entry M 1 0"
        proof (cases "multiT M")
          \<comment> \<open>Branch 2: multiT M.  Red M = concat (map Red (P M)).\<close>
          case True
          have rM: "Red M = concat (map Red (P M))"
            using Red.psimps[OF dom] nz True by simp
          have L1: "1 < Lng M" by (rule multiT_imp_Lng_gt1[OF MT' True])
          \<comment> \<open>IH for P M ! 0\<close>
          have ne_PM: "P M \<noteq> []" by (rule P_nonempty)
          have PM0_in: "P M ! 0 \<in> set (P M)"
            using ne_PM by (cases "P M") auto
          have PM0_T: "P M ! 0 \<in> T_PS"
            using P_blocks_nonempty[OF Mne] PM0_in by (auto simp: T_PS_def)
          have ih0: "P M ! 0 \<in> T_PS \<longrightarrow>
                       entry (Red (P M ! 0)) 1 0 = entry (P M ! 0) 1 0"
            by (rule IH_mu[OF nz True PM0_in])
          hence IH': "entry (Red (P M ! 0)) 1 0 = entry (P M ! 0) 1 0"
            using PM0_T by blast
          \<comment> \<open>P M ! 0 = seg M 0 ?, so entry (P M ! 0) 1 0 = entry M 1 0\<close>
          have PM0_JL: "0 < length (P M)"
            using ne_PM by (cases "P M") simp_all
          have PM0_len_pos: "0 < Lng (P M ! 0)"
            by (rule idxsum_P_component_nonempty[OF MT' PM0_JL])
          have idx0: "IdxSum (P M) ! 0 = 0"
            by (simp add: idxsum_nth)
          have e_PM0: "entry (P M ! 0) 1 0 = entry M 1 0"
          proof -
            have Jle: "(0::nat) \<le> Lng (P M) - 1"
              using ne_PM by (cases "P M") simp_all
            have PM0_seg: "P M ! 0 = seg M (IdxSum (P M) ! 0) (IdxSum (P M) ! 1 - 1)"
              using m_6_4_P_IdxSum[OF MT' Jle] by simp
            have lp: "0 < Lng (seg M (IdxSum (P M) ! 0) (IdxSum (P M) ! 1 - 1))"
              using PM0_len_pos PM0_seg by simp
            have "entry (P M ! 0) 1 0
                 = entry (seg M (IdxSum (P M) ! 0) (IdxSum (P M) ! 1 - 1)) 1 0"
              using PM0_seg by simp
            also have "\<dots> = entry M 1 (IdxSum (P M) ! 0 + 0)"
              by (rule entry_seg[OF lp])
            also have "\<dots> = entry M 1 0" by (simp add: idx0)
            finally show ?thesis .
          qed
          \<comment> \<open>concat (map Red (P M)) ! 0 = Red (P M ! 0) ! 0\<close>
          have rPM0_ne: "Red (P M ! 0) \<noteq> []"
          proof -
            have "Lng (Red (P M ! 0)) = Lng (P M ! 0)"
              by (rule m_6_5_Lng_Red[OF PM0_T])
            thus ?thesis using PM0_len_pos by (cases "Red (P M ! 0)") auto
          qed
          have concat_nth0: "concat (map Red (P M)) ! 0 = Red (P M ! 0) ! 0"
          proof -
            have split: "P M = P M ! 0 # tl (P M)"
              using ne_PM by (cases "P M") auto
            have "concat (map Red (P M))
                 = Red (P M ! 0) @ concat (map Red (tl (P M)))"
              by (subst split) simp
            thus ?thesis using rPM0_ne by (simp add: nth_append)
          qed
          \<comment> \<open>Chain the equalities\<close>
          have "entry (Red M) 1 0 = entry (concat (map Red (P M))) 1 0"
            by (simp add: rM)
          also have "\<dots> = entry (Red (P M ! 0)) 1 0"
            by (simp add: entry_def concat_nth0)
          also have "\<dots> = entry (P M ! 0) 1 0" by (rule IH')
          also have "\<dots> = entry M 1 0" by (rule e_PM0)
          finally show ?thesis .
        next
          \<comment> \<open>Branches 3-5: mono.\<close>
          case nmu: False
          have mono: "monoT M" using nz nmu by (simp add: multiT_def)
          let ?j1  = "Lng M - 1"
          let ?j1' = "TrMax M"
          let ?m00 = "entry M 0 0"
          let ?m10 = "entry M 1 0"
          show "entry (Red M) 1 0 = entry M 1 0"
          proof (cases "?m00 = 0 \<and> ?m10 = 0")
            \<comment> \<open>Core case: M starts at (0,0).\<close>
            case core: True
            hence c0: "?m00 = 0" and c1: "?m10 = 0" by simp_all
            show ?thesis
            proof (cases "?j1' = ?j1")
              \<comment> \<open>Branch 3a: TrMax = Lng-1; diagonal output diagSeq m10 (m10+j1).\<close>
              case True
              have rM: "Red M = diagSeq ?m10 (?m10 + ?j1)"
                using Red.psimps[OF dom] nz nmu c0 c1 True
                by (simp add: Let_def)
              have e_rM: "entry (Red M) 1 0 = ?m10"
              proof -
                have "entry (diagSeq ?m10 (?m10 + ?j1)) 1 0 = ?m10 + 0"
                  by (rule entry_diagSeq) (simp add: LMpos)
                thus ?thesis using rM by simp
              qed
              show ?thesis using e_rM c1 by simp
            next
              \<comment> \<open>Branch 3b: TrMax /= Lng-1; diagSeq prefix + branches.\<close>
              case tne: False
              let ?tail = "concat (map (\<lambda>J.
                        (IncrFirst ^^ (Joints M ! J + 1
                            - (if entry (Br M ! J) 1 0 = 0 then 0
                               else Suc (THE j. nextR M 1 j (FirstNodes M ! J)))))
                          (Red ((entry M 0 0 + Joints M ! J + 1,
                                 entry M 1 0 + (if entry (Br M ! J) 1 0 = 0 then 0
                                        else Suc (THE j. nextR M 1 j (FirstNodes M ! J))))
                                # tl (Br M ! J))))
                      [0..<Lng (Br M)])"
              have rM: "Red M = diagSeq 0 ?j1' @ ?tail"
                using Red.psimps[OF dom] nz nmu c0 c1 tne
                by (simp add: Let_def)
              have diag_ne: "diagSeq 0 ?j1' \<noteq> []"
                by (simp add: diagSeq_def)
              have "entry (Red M) 1 0 = entry (diagSeq 0 ?j1' @ ?tail) 1 0"
                by (simp add: rM)
              also have "\<dots> = entry (diagSeq 0 ?j1') 1 0"
                using diag_ne by (simp add: entry_def nth_append)
              also have "\<dots> = 0"
                using entry_diagSeq[where a=0 and b="?j1'" and j=0 and i=1]
                by simp
              finally show ?thesis using c1 by simp
            qed
          next
            \<comment> \<open>Non-core case.\<close>
            case nc: False
            show ?thesis
            proof (cases "?m10 = 0")
              \<comment> \<open>Branch 4: m10=0 shift.  Red M = Red (shiftRow0 M).\<close>
              case True
              have c0p: "0 < ?m00" using nc True by simp
              let ?shift = "map (\<lambda>j. (entry M 0 j - ?m00, entry M 1 j)) [0..<Suc ?j1]"
              have rM: "Red M = Red ?shift"
                using Red.psimps[OF dom] nz nmu nc True
                by (simp add: Let_def)
              have shift_T: "?shift \<in> T_PS" by (simp add: T_PS_def)
              have IH': "entry (Red ?shift) 1 0 = entry ?shift 1 0"
                using IH_nc3[OF nz nmu refl refl refl refl nc True] shift_T
                by blast
              have e_shift: "entry ?shift 1 0 = entry M 1 0"
                using LMpos by (simp add: entry_def)
              have "entry (Red M) 1 0 = entry (Red ?shift) 1 0"
                by (simp add: rM)
              also have "\<dots> = entry ?shift 1 0" using IH' .
              also have "\<dots> = entry M 1 0" using e_shift .
              finally show ?thesis .
            next
              \<comment> \<open>Branch 5: m10>0.\<close>
              case False
              hence c1p: "0 < ?m10" by simp
              let ?arg = "diagSeq 0 (?m10 - 1) @ (IncrFirst ^^ ?m10) M"
              have funpow_ne: "(IncrFirst ^^ ?m10) M \<noteq> []"
                using Mne by (metis Lng_funpow_IncrFirst length_0_conv)
              have arg_T: "?arg \<in> T_PS"
                using funpow_ne by (simp add: T_PS_def)
              let ?N = "Red ?arg"
              let ?jN = "Lng ?N - 1"
              have rM: "Red M = (let N = ?N; jN = ?jN in
                         if ?m10 \<le> jN \<and> seg N ?m10 jN \<in> PT_PS then
                           map (\<lambda>j. (entry N 0 j - entry N 0 ?m10 + entry N 1 ?m10,
                                     entry N 1 j))
                               [?m10..<Suc jN]
                         else M)"
                using Red.psimps[OF dom] nz nmu nc c1p
                by (simp add: Let_def)
              show ?thesis
              proof (cases "?m10 \<le> ?jN \<and> seg ?N ?m10 ?jN \<in> PT_PS")
                \<comment> \<open>Else branch: Red M = M.  Trivial.\<close>
                case else_nc: False
                have nc: "\<not> (?m10 \<le> ?jN \<and> seg ?N ?m10 ?jN \<in> PT_PS)" using else_nc .
                have rM_else: "Red M = M"
                proof -
                  have step1: "(let N = ?N; jN = ?jN in
                                 if ?m10 \<le> jN \<and> seg N ?m10 jN \<in> PT_PS
                                 then map (\<lambda>j. (entry N 0 j - entry N 0 ?m10 + entry N 1 ?m10,
                                                entry N 1 j)) [?m10..<Suc jN]
                                 else M) = M"
                    unfolding Let_def
                    by (rule if_not_P[OF nc])
                  show ?thesis using rM step1 by simp
                qed
                thus ?thesis by (simp add: rM_else)
              next
                \<comment> \<open>Then branch: entry N 1 m10 = m10 by structure of Red arg.\<close>
                case then_case: True
                have rM': "Red M = map (\<lambda>j. (entry ?N 0 j - entry ?N 0 ?m10
                                              + entry ?N 1 ?m10,
                                              entry ?N 1 j))
                                       [?m10..<Suc ?jN]"
                  using rM then_case by (simp add: Let_def del: upt_Suc)
                \<comment> \<open>entry (Red M) 1 0 = entry N 1 m10\<close>
                have rM_ne: "0 < length [?m10..<Suc ?jN]"
                  using then_case by simp
                have rM_e10: "entry (Red M) 1 0 = entry ?N 1 ?m10"
                proof -
                  have h1: "[?m10..<Suc ?jN] ! 0 = ?m10"
                    using then_case by (simp add: nth_upt del: upt_Suc)
                  have h2: "(Red M) ! 0 = (\<lambda>j. (entry ?N 0 j - entry ?N 0 ?m10
                                                  + entry ?N 1 ?m10, entry ?N 1 j)) ?m10"
                    using rM' rM_ne h1 by (simp add: nth_map del: upt_Suc)
                  have h3: "snd ((Red M) ! 0) = entry ?N 1 ?m10"
                    using h2 by simp
                  show ?thesis using h3 unfolding entry_def by simp
                qed
                \<comment> \<open>arg = coreReduce M is monoT\<close>
                have arg_eq_cr: "?arg = coreReduce M"
                  using c1p by (simp add: coreReduce_def)
                have arg_mono: "monoT ?arg"
                  using coreReduce_monoT_m10_pos[OF MT' mono c1p] arg_eq_cr
                  by simp
                \<comment> \<open>arg not zero: Lng arg = m10 + Lng M >= 2\<close>
                have Larg: "Lng ?arg = ?m10 + Lng M"
                  using c1p by (simp add: Lng_funpow_IncrFirst)
                have arg_nz: "\<not> zeroT ?arg"
                proof -
                  have Larg_ge: "Lng ?arg \<ge> 2" using c1p Larg LMpos by linarith
                  thus ?thesis unfolding zeroT_def using Larg_ge by linarith
                qed
                \<comment> \<open>arg not multi\<close>
                have arg_nmu: "\<not> multiT ?arg"
                  using arg_mono by (simp add: multiT_def)
                \<comment> \<open>entry arg 0 0 = 0 and entry arg 1 0 = 0\<close>
                have arg_c0: "entry ?arg 0 0 = 0"
                  using c1p by (simp add: entry_diagSeq_append_lo)
                have arg_c1: "entry ?arg 1 0 = 0"
                  using c1p by (simp add: entry_diagSeq_append_lo)
                \<comment> \<open>Red_dom arg\<close>
                have dom_arg: "Red_dom ?arg"
                  by (rule m_6_5_Red_welldef[OF arg_T])
                \<comment> \<open>TrMax arg >= m10\<close>
                have er0: "?m10 - 1 < entry ((IncrFirst ^^ ?m10) M) 0 0"
                proof -
                  have "entry ((IncrFirst ^^ ?m10) M) 0 0 = entry M 0 0 + ?m10"
                    by (rule entry_funpow_IncrFirst0[OF LMpos])
                  thus ?thesis using c1p by simp
                qed
                have er1: "?m10 - 1 < entry ((IncrFirst ^^ ?m10) M) 1 0"
                proof -
                  have "entry ((IncrFirst ^^ ?m10) M) 1 0 = entry M 1 0"
                    by (rule entry_funpow_IncrFirst1[OF LMpos])
                  thus ?thesis using c1p by simp
                qed
                have TrMax_ge: "?m10 \<le> TrMax ?arg"
                  using TrMax_diagSeq_append_ge[OF funpow_ne er0 er1] by simp
                \<comment> \<open>Red arg unfolds in core (m00=0, m10=0, monoT) case\<close>
                let ?tail_arg = "concat (map (\<lambda>J.
                        (IncrFirst ^^ (Joints ?arg ! J + 1
                            - (if entry (Br ?arg ! J) 1 0 = 0 then 0
                               else Suc (THE j. nextR ?arg 1 j (FirstNodes ?arg ! J)))))
                          (Red ((entry ?arg 0 0 + Joints ?arg ! J + 1,
                                 entry ?arg 1 0
                                 + (if entry (Br ?arg ! J) 1 0 = 0 then 0
                                    else Suc (THE j. nextR ?arg 1 j (FirstNodes ?arg ! J))))
                                # tl (Br ?arg ! J))))
                      [0..<Lng (Br ?arg)])"
                show ?thesis
                proof (cases "TrMax ?arg = Lng ?arg - 1")
                  \<comment> \<open>Trunk case: Red arg = diagSeq 0 (Lng arg - 1).\<close>
                  case tr: True
                  have rArg_tr: "Red ?arg = diagSeq 0 (Lng ?arg - 1)"
                    using Red.psimps[OF dom_arg] arg_nz arg_nmu arg_c0 arg_c1 tr
                    by (simp add: Let_def)
                  have NrArg: "?N = diagSeq 0 (Lng ?arg - 1)"
                    using rArg_tr by simp
                  have "entry ?N 1 ?m10
                       = entry (diagSeq 0 (Lng ?arg - 1)) 1 ?m10"
                    using NrArg by simp
                  also have "\<dots> = ?m10"
                    using entry_diagSeq[where a=0 and b="Lng ?arg - 1"
                                        and j="?m10" and i=1]
                    using Larg c1p LMpos by simp
                  finally show ?thesis using rM_e10 by simp
                next
                  \<comment> \<open>Non-trunk case: Red arg = diagSeq 0 (TrMax arg) @ ...\<close>
                  case ntr: False
                  have rArg_ntr: "Red ?arg = diagSeq 0 (TrMax ?arg) @ ?tail_arg"
                    using Red.psimps[OF dom_arg] arg_nz arg_nmu arg_c0 arg_c1 ntr
                    by (simp add: Let_def)
                  have NrArg_ntr: "?N = diagSeq 0 (TrMax ?arg) @ ?tail_arg"
                    using rArg_ntr by simp
                  have "entry ?N 1 ?m10
                       = entry (diagSeq 0 (TrMax ?arg) @ ?tail_arg) 1 ?m10"
                    using NrArg_ntr by simp
                  also have "\<dots> = ?m10"
                    by (rule entry_diagSeq_append_lo) (rule TrMax_ge)
                  finally show ?thesis using rM_e10 by simp
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  thus ?thesis using MT by blast
qed


subsection \<open>§6.7 標準形の始切片への遺伝性\<close>

text \<open>補助補題: \<open>ST_PS \<subseteq> T_PS\<close>  (diagSeq non-empty; oper preserves non-emptiness)\<close>

lemma ST_PS_T_PS:
  assumes "M \<in> ST_PS"
  shows "M \<in> T_PS"
using assms proof (induct M rule: ST_PS.induct)
  case (diag u v)
  \<comment> \<open>diag.hyps: u ≤ v\<close>
  have "diagSeq u v \<noteq> []"
    unfolding diagSeq_def using diag by simp
  thus "diagSeq u v \<in> T_PS" by (simp add: T_PS_def)
next
  case (oper M n)
  have MT: "M \<in> T_PS" by (rule oper.hyps(2))
  have n1: "1 \<le> n" by (rule oper.hyps(3))
  show "(M::pairseq)[n] \<in> T_PS"
  proof (cases "Lng M \<le> 1")
    case True
    have LM1: "Lng M = 1" using MT True
      by (simp add: T_PS_def; cases M; auto)
    hence "(M::pairseq)[n] = M"
      by (simp add: oper_def Let_def)
    thus ?thesis using MT by simp
  next
    case False
    hence L: "Lng M > 1" by simp
    have "(M::pairseq)[n] \<noteq> []"
      using poper_oper_nth0[OF MT L n1] by simp
    thus ?thesis by (simp add: T_PS_def)
  qed
qed

text \<open>補助補題: \<open>seg (diagSeq u v) 0 j1' = diagSeq u (u + j1')\<close>  (when \<open>j1' \<le> v - u\<close>)\<close>

lemma seg_0_diagSeq:
  assumes "u \<le> v" "j1' \<le> v - u"
  shows "seg (diagSeq u v) 0 j1' = diagSeq u (u + j1')"
proof -
  have lD: "Suc j1' \<le> Lng (diagSeq u v)" using assms by simp
  have step1: "seg (diagSeq u v) 0 j1' = take (Suc j1') (diagSeq u v)"
    by (rule seg_0_eq_take[OF lD])
  have luv: "Suc j1' \<le> Suc (u + j1') - u"
    by simp
  have step2: "take (Suc j1') (diagSeq u v) = diagSeq u (u + j1')"
  proof (intro nth_equalityI)
    show "length (take (Suc j1') (diagSeq u v)) = length (diagSeq u (u + j1'))"
      using lD by simp
    fix i
    assume "i < length (take (Suc j1') (diagSeq u v))"
    hence iS: "i < Suc j1'" using lD by simp
    have iDuv: "i < Suc v - u" using iS lD by (simp del: upt_Suc)
    have iDuj1: "i < Suc (u + j1') - u" using iS by simp
    have "take (Suc j1') (diagSeq u v) ! i = diagSeq u v ! i"
      using iS lD by (simp add: nth_take)
    also have "\<dots> = (u + i, u + i)"
      by (rule diagSeq_nth[OF iDuv])
    also have "\<dots> = diagSeq u (u + j1') ! i"
      by (rule diagSeq_nth[symmetric, OF iDuj1])
    finally show "take (Suc j1') (diagSeq u v) ! i = diagSeq u (u + j1') ! i" .
  qed
  show ?thesis using step1 step2 by simp
qed

text \<open>m: 命題（標準形の始切片への遺伝性） — discharges @{thm [source] p_6_7_standard_prefix}.
  (§6.7, 命題（標準形の始切片への遺伝性）)

  Proof: induction on \<open>d = Lng M - 1 - j1'\<close>.
  \<^item> Base (\<open>d = 0\<close>): \<open>j1' = Lng M - 1\<close>, so \<open>seg M 0 j1' = M \<in> ST_PS\<close>.
  \<^item> Step (\<open>d = Suc d'\<close>): \<open>j1' \<le> Lng M - 2\<close>, so \<open>Lng M > 1\<close>.
    Apply \<open>m_5_3_pred_is_oper1\<close> (requires \<open>M \<in> T_PS\<close>, \<open>Lng M > 1\<close>) to get
    \<open>M[1] = Pred M\<close>.  Then \<open>M[1] \<in> ST_PS\<close> (oper rule) and
    \<open>seg M 0 j1' = seg (M[1]) 0 j1'\<close> (both are \<open>take (Suc j1') M\<close>).
    IH applies to \<open>(M[1], j1')\<close> with measure \<open>d'\<close>.\<close>

text \<open>核心補題 (inner): induction on d = Lng M - 1 - j1'.\<close>

lemma ST_PS_seg_0_inner:
  "\<forall>M j1'. M \<in> ST_PS \<longrightarrow> j1' \<le> Lng M - 1 \<longrightarrow> Lng M - 1 - j1' = d \<longrightarrow> seg M 0 j1' \<in> ST_PS"
proof (induction d rule: less_induct)
  case (less d)
  show ?case
  proof (intro allI impI)
    fix M :: pairseq and j1' :: nat
    assume MST: "M \<in> ST_PS"
    assume j1'le: "j1' \<le> Lng M - 1"
    assume deq: "Lng M - 1 - j1' = d"
    have MT: "M \<in> T_PS" by (rule ST_PS_T_PS[OF MST])
    have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
    have lM: "Suc j1' \<le> Lng M" using j1'le Mne by (cases M; auto)
    show "seg M 0 j1' \<in> ST_PS"
    proof (cases "j1' = Lng M - 1")
      case True
      \<comment> \<open>j1' = Lng M - 1: seg M 0 j1' = M ∈ ST_PS.\<close>
      have "seg M 0 j1' = take (Suc j1') M"
        by (rule seg_0_eq_take[OF lM])
      also have "\<dots> = M" using lM True by simp
      finally show ?thesis using MST by simp
    next
      case False
      \<comment> \<open>j1' < Lng M - 1: use M[1] = Pred M.\<close>
      have j1'lt: "j1' < Lng M - 1" using j1'le False by linarith
      have L: "Lng M > 1" using j1'lt by linarith
      \<comment> \<open>M[1] = Pred M\<close>
      have pred_eq: "Pred M = (M::pairseq)[1]"
        by (rule m_5_3_pred_is_oper1[OF MT L])
      \<comment> \<open>M[1] ∈ ST_PS\<close>
      have M1ST: "(M::pairseq)[1] \<in> ST_PS"
        by (rule ST_PS.oper[OF MST]) simp
      \<comment> \<open>Lng(M[1]) = Lng M - 1\<close>
      have predL: "Lng (Pred M) = Lng M - 1"
        using L by (simp add: Pred_def)
      have M1L: "Lng ((M::pairseq)[1]) = Lng M - 1"
        using predL pred_eq by simp
      \<comment> \<open>j1' ≤ Lng(M[1]) - 1\<close>
      have j1'le': "j1' \<le> Lng ((M::pairseq)[1]) - 1"
        using j1'lt M1L by linarith
      \<comment> \<open>Measure d' = Lng(M[1]) - 1 - j1' < d = Lng M - 1 - j1'\<close>
      have d'eq: "Lng ((M::pairseq)[1]) - 1 - j1' = d - 1"
        using deq M1L by linarith
      have dlt: "d - 1 < d" using deq j1'lt by linarith
      \<comment> \<open>seg M 0 j1' = seg (M[1]) 0 j1'\<close>
      have Sj1'le: "Suc j1' \<le> Lng M - 1" using j1'lt by linarith
      have predM_take: "Pred M = take (Lng M - 1) M"
        using L by (simp add: Pred_def butlast_conv_take)
      have seg_M: "seg M 0 j1' = take (Suc j1') M"
        by (rule seg_0_eq_take[OF lM])
      have lM1: "Suc j1' \<le> Lng ((M::pairseq)[1])"
        using j1'lt M1L by linarith
      have seg_M1: "seg ((M::pairseq)[1]) 0 j1' = take (Suc j1') ((M::pairseq)[1])"
        by (rule seg_0_eq_take[OF lM1])
      have take_M1_eq_take_M: "take (Suc j1') ((M::pairseq)[1]) = take (Suc j1') M"
      proof -
        have "take (Suc j1') ((M::pairseq)[1]) = take (Suc j1') (Pred M)"
          using pred_eq by simp
        also have "\<dots> = take (Suc j1') (take (Lng M - 1) M)"
          using predM_take by simp
        also have "\<dots> = take (Suc j1') M"
          using Sj1'le by (simp add: take_take min_def)
        finally show ?thesis .
      qed
      have seg_same: "seg M 0 j1' = seg ((M::pairseq)[1]) 0 j1'"
        using seg_M seg_M1 take_M1_eq_take_M by simp
      \<comment> \<open>Apply IH to (M[1], j1') with d-1 < d.\<close>
      have "seg ((M::pairseq)[1]) 0 j1' \<in> ST_PS"
        using less.IH[rule_format, OF dlt M1ST j1'le' d'eq] .
      thus ?thesis using seg_same by simp
    qed
  qed
qed

lemma ST_PS_seg_0_aux:
  assumes MST: "M \<in> ST_PS" and j1'le: "j1' \<le> Lng M - 1"
  shows "seg M 0 j1' \<in> ST_PS"
proof -
  have h: "\<forall>M' j1''. M' \<in> ST_PS \<longrightarrow> j1'' \<le> Lng M' - 1 \<longrightarrow>
                Lng M' - 1 - j1'' = Lng M - 1 - j1' \<longrightarrow> seg M' 0 j1'' \<in> ST_PS"
    using ST_PS_seg_0_inner by blast
  have deq: "Lng M - 1 - j1' = Lng M - 1 - j1'" by simp
  show ?thesis using h[rule_format, OF MST j1'le deq] .
qed

lemma m_6_7_standard_prefix:
  \<comment> \<open>m: 命題（標準形の始切片への遺伝性） (§6.7)
     Discharges p_6_7_standard_prefix.\<close>
  assumes "M \<in> ST_PS" "j1' \<le> Lng M - 1"
  shows "seg M 0 j1' \<in> ST_PS"
  by (rule ST_PS_seg_0_aux[OF assms(1) assms(2)])


subsection \<open>§6.7 標準形の単項成分が標準形であること (P-components are standard, same rank)\<close>

text \<open>
  Proof of \<open>p_6_7_standard_P_components\<close> (\<open>M \<in> SkT_PS k \<Longrightarrow> P M ! J \<in> SkT_PS k\<close>).
  The article proof (content.md line 1392) is faulty (correction A6): it derives
  "the components of \<open>M'\<close> are in \<open>S\<^sub>k\<close>" from the induction hypothesis, which only
  yields \<open>S\<^bsub>k-1\<^esub>\<close>, and \<open>S\<^bsub>k-1\<^esub> \<subseteq> S\<^sub>k\<close> is false.  The repair uses two facts the
  article omits, both empirically verified in \<open>python/sk_67_audit.py\<close>:
    \<^item> (R) a non-last \<open>P\<close>-component has row 1 identically zero;
    \<^item> (U) a row-1-zero standard form in \<open>S\<^sub>k\<close> is also in \<open>S\<^bsub>k+1\<^esub>\<close>.
  Step 1 below is the self-contained part of (R): components of a row-1-zero
  sequence are themselves row-1-zero (they are sublists, and \<open>concat (P M) = M\<close>).
\<close>

text \<open>Auxiliary predicate: row 1 is identically zero (article: \<open>M\<^bsub>1,j\<^esub> = 0\<close> for all \<open>j\<close>).\<close>
definition Row1Zero :: "pairseq \<Rightarrow> bool" where
  "Row1Zero M \<longleftrightarrow> (\<forall>p \<in> set M. snd p = 0)"

lemma Row1Zero_iff_entry: "Row1Zero M \<longleftrightarrow> (\<forall>j < Lng M. entry M 1 j = 0)"
proof
  assume "Row1Zero M"
  thus "\<forall>j < Lng M. entry M 1 j = 0"
    unfolding Row1Zero_def entry_def by (auto simp: nth_mem)
next
  assume r: "\<forall>j < Lng M. entry M 1 j = 0"
  show "Row1Zero M" unfolding Row1Zero_def
  proof
    fix p assume "p \<in> set M"
    then obtain j where "j < Lng M" "p = M ! j" by (auto simp: in_set_conv_nth)
    thus "snd p = 0" using r unfolding entry_def by auto
  qed
qed

text \<open>Step 1 of (R): every \<open>P\<close>-component of a \<open>Row1Zero\<close> sequence is \<open>Row1Zero\<close>.\<close>
lemma row1z_P_component:
  assumes "Row1Zero M" "J < length (P M)"
  shows "Row1Zero (P M ! J)"
proof -
  from assms(2) have mem: "P M ! J \<in> set (P M)" by (rule nth_mem)
  have "set M = set (concat (P M))" by (simp add: idxsum_concat_P)
  also have "\<dots> = (\<Union>xs \<in> set (P M). set xs)" by (simp add: set_concat)
  finally have "set (P M ! J) \<subseteq> set M" using mem by auto
  thus ?thesis using assms(1) unfolding Row1Zero_def by blast
qed

text \<open>
  \<open>SkT_PS\<close> is monotone: \<open>SkT_PS k \<subseteq> SkT_PS (Suc k)\<close>.  This is the fact the
  article's §6.7 proof of standard_P_components silently relies on (correction
  A6): a rank-\<open>k\<close> standard form is also rank-\<open>(k+1)\<close>.  Witness for the base
  case: \<open>diagSeq u v = Pred (diagSeq u (v+1)) = (diagSeq u (v+1))[1]\<close>, and
  \<open>diagSeq u (v+1) \<in> SkT_PS 0\<close>.  (Monotonicity makes the \<open>Row1Zero\<close> route to
  the leading components unnecessary — see docs/standard-P-components.md.)
\<close>

text \<open>Auxiliary: \<open>diagSeq u (Suc v) = diagSeq u v @ [(Suc v, Suc v)]\<close> and hence
  \<open>Pred (diagSeq u (Suc v)) = diagSeq u v\<close>.\<close>
lemma diagSeq_Suc_snoc:
  assumes uv: "u \<le> v"
  shows "diagSeq u (Suc v) = diagSeq u v @ [(Suc v, Suc v)]"
  using uv by (simp add: diagSeq_def upt_Suc_append)

lemma Pred_diagSeq_Suc:
  assumes uv: "u \<le> v"
  shows "Pred (diagSeq u (Suc v)) = diagSeq u v"
proof -
  have Lgt1: "1 < Lng (diagSeq u (Suc v))" using uv by simp
  have "Pred (diagSeq u (Suc v)) = butlast (diagSeq u (Suc v))"
    using Lgt1 by (simp add: Pred_def)
  also have "\<dots> = butlast (diagSeq u v @ [(Suc v, Suc v)])"
    by (simp only: diagSeq_Suc_snoc[OF uv])
  also have "\<dots> = diagSeq u v" by simp
  finally show ?thesis .
qed

text \<open>A diagonal segment is never multi-term (row 0 is strictly increasing, so
  \<open>(0,0) \<le>\<^bsub>M\<^esub> (0, Lng-1)\<close>).  Used for the \<open>k = 0\<close> base of \<open>SkT_P_comp\<close>.\<close>
lemma not_multiT_diagSeq:
  assumes uv: "u \<le> v"
  shows "\<not> multiT (diagSeq u v)"
proof -
  have MT: "diagSeq u v \<in> T_PS" using uv by (simp add: T_PS_def diagSeq_def del: upt_Suc)
  show ?thesis
  proof (cases "1 < Lng (diagSeq u v)")
    case False
    thus ?thesis using MT multiT_imp_Lng_gt1[OF MT] by auto
  next
    case True
    let ?M = "diagSeq u v"
    have j1lt: "Lng ?M - 1 < Lng ?M" using True by simp
    have j0lt: "(0::nat) < Lng ?M - 1" using True by simp
    have "(nextrel0 ?M)\<^sup>*\<^sup>* 0 (Lng ?M - 1)"
    proof (rule le0_build[OF MT j1lt j0lt])
      show "\<forall>j. 0 < j \<and> j \<le> Lng ?M - 1 \<longrightarrow> entry ?M 0 0 < entry ?M 0 j"
      proof (intro allI impI)
        fix j assume jj: "0 < j \<and> j \<le> Lng ?M - 1"
        hence jLM: "j < Lng ?M" using True by linarith
        hence ej: "entry ?M 0 j = u + j" by (simp add: entry_diagSeq)
        have "entry ?M 0 0 = u" using True by (simp add: entry_diagSeq)
        thus "entry ?M 0 0 < entry ?M 0 j" using ej jj by simp
      qed
    qed
    hence "le0 ?M 0 (Lng ?M - 1)" using j1lt by (simp add: le0_def)
    hence "leR ?M 0 0 (Lng ?M - 1)" by (simp add: leR_def)
    thus ?thesis using m_6_2_not_multi_iff_le[OF MT] by simp
  qed
qed

lemma SkT_PS_mono: "SkT_PS k \<subseteq> SkT_PS (Suc k)"
proof (induction k)
  case 0
  show "SkT_PS 0 \<subseteq> SkT_PS (Suc 0)"
  proof
    fix M assume "M \<in> SkT_PS 0"
    then obtain u v where Muv: "M = diagSeq u v" and uv: "u \<le> v" by auto
    have NinS0: "diagSeq u (Suc v) \<in> SkT_PS 0" using uv by force
    have LN: "1 < Lng (diagSeq u (Suc v))" using uv by simp
    have NT: "diagSeq u (Suc v) \<in> T_PS"
      using diagSeq_Suc_snoc[OF uv] by (simp add: T_PS_def)
    have "M = diagSeq u v" by (rule Muv)
    also have "\<dots> = Pred (diagSeq u (Suc v))" by (simp add: Pred_diagSeq_Suc[OF uv])
    also have "\<dots> = (diagSeq u (Suc v))[1]" by (rule m_5_3_pred_is_oper1[OF NT LN])
    finally have Meq: "M = (diagSeq u (Suc v))[1]" .
    have "(diagSeq u (Suc v))[1] \<in> SkT_PS (Suc 0)" using NinS0 by auto
    thus "M \<in> SkT_PS (Suc 0)" using Meq by simp
  qed
next
  case (Suc k)
  show "SkT_PS (Suc k) \<subseteq> SkT_PS (Suc (Suc k))"
  proof
    fix M assume "M \<in> SkT_PS (Suc k)"
    then obtain N n where MNn: "M = (N::pairseq)[n]"
                      and NK: "N \<in> SkT_PS k" and n1: "1 \<le> n" by auto
    have "N \<in> SkT_PS (Suc k)" using Suc.IH NK by blast
    thus "M \<in> SkT_PS (Suc (Suc k))" using n1 MNn by auto
  qed
qed

text \<open>
  m: 命題（標準形の単項成分が標準形であること） (§6.7).  Discharges
  \<open>p_6_7_standard_P_components\<close>.  The article proof (content.md 1392, correction
  A6) is essentially right but omits the monotonicity lemma \<open>SkT_PS_mono\<close> on
  which it relies; here we use it explicitly.  Structure (docs/standard-P-components.md):
  outer induction on \<open>k\<close>, inner strong induction on \<open>Lng X\<close>; leading \<open>P\<close>-components
  come from the rank-\<open>k\<close> IH and are lifted by \<open>SkT_PS_mono\<close>; the relation-(2) tail
  \<open>(last (P M'))[n]\<close> is strictly shorter, handled by the inner IH.
\<close>

lemma SkT_P_comp:
  shows "X \<in> SkT_PS k \<Longrightarrow> c \<in> set (P X) \<Longrightarrow> c \<in> SkT_PS k"
proof -
  have "\<forall>X. X \<in> SkT_PS k \<longrightarrow> (\<forall>c \<in> set (P X). c \<in> SkT_PS k)"
  proof (induction k)
    case 0
    show ?case
    proof (intro allI impI ballI)
      fix X c assume X0: "X \<in> SkT_PS 0" and cP: "c \<in> set (P X)"
      from X0 obtain u v where Xuv: "X = diagSeq u v" and uv: "u \<le> v" by auto
      have "\<not> multiT X" using Xuv not_multiT_diagSeq[OF uv] by simp
      hence "P X = [X]" by (simp add: poper_P_nonmulti)
      with cP have "c = X" by simp
      thus "c \<in> SkT_PS 0" using X0 by simp
    qed
  next
    case (Suc k)
    note IHk = Suc.IH
    have inner: "\<forall>X. Lng X = L \<longrightarrow> X \<in> SkT_PS (Suc k) \<longrightarrow> (\<forall>c \<in> set (P X). c \<in> SkT_PS (Suc k))"
      for L
    proof (induction L rule: less_induct)
      case (less L)
      note IHL = less.IH
      show ?case
      proof (intro allI impI ballI)
        fix X c assume LX: "Lng X = L" and XS: "X \<in> SkT_PS (Suc k)" and cP: "c \<in> set (P X)"
        from XS obtain M' n where Xeq: "X = (M'::pairseq)[n]"
                              and M'S: "M' \<in> SkT_PS k" and n1: "1 \<le> n" by auto
        have M'T: "M' \<in> T_PS" using M'S SkT_PS_subset_ST_PS ST_PS_T_PS by blast
        show "c \<in> SkT_PS (Suc k)"
        proof (cases "multiT M'")
          case nonmulti: False
          show ?thesis
          proof (cases "nextR M' 0 0 (Lng M' - 1) \<and> entry M' 1 (Lng M' - 1) = 0")
            case cond1: True
            have PX: "P X = replicate n (Pred M')"
              using m_6_2_nonmulti_oper_1[OF M'T n1 nonmulti conjunct1[OF cond1] conjunct2[OF cond1]]
                    Xeq by simp
            from cP PX n1 have cpred: "c = Pred M'"
              by (auto simp: set_replicate_conv_if split: if_splits)
            have "Pred M' \<in> SkT_PS (Suc k)"
            proof (cases "1 < Lng M'")
              case True
              have "Pred M' = M'[1]" by (rule m_5_3_pred_is_oper1[OF M'T True])
              thus ?thesis using M'S by auto
            next
              case False
              hence "Pred M' = M'" by (simp add: Pred_def)
              thus ?thesis using rev_subsetD[OF M'S SkT_PS_mono] by simp
            qed
            thus ?thesis using cpred by simp
          next
            case cond2: False
            hence H: "\<not> nextR M' 0 0 (Lng M' - 1) \<or> entry M' 1 (Lng M' - 1) > 0" by auto
            have "P X = [X]"
              using m_6_2_nonmulti_oper_2[OF M'T n1 nonmulti H] Xeq by simp
            with cP have "c = X" by simp
            thus ?thesis using XS by simp
          qed
        next
          case multi: True
          have lenP: "length (P M') > 1" using multi m_6_2_P_components_2[OF M'T] by simp
          have LM': "1 < Lng M'" using multi multiT_imp_Lng_gt1[OF M'T] by simp
          show ?thesis
          proof (cases "Lng (last (P M')) = 1")
            case last1: True
            have PX: "P X = butlast (P M')"
            proof -
              have "P (M'[n]) = butlast (P M')"
                using conjunct2[OF m_6_2_P_oper_1[OF M'T n1 last1]] lenP by simp
              thus ?thesis using Xeq by simp
            qed
            from cP PX have "c \<in> set (butlast (P M'))" by simp
            hence "c \<in> set (P M')" using in_set_butlastD by fast
            hence "c \<in> SkT_PS k" using IHk M'S by blast
            thus ?thesis by (rule rev_subsetD[OF _ SkT_PS_mono])
          next
            case False
            have lastpos: "0 < Lng (last (P M'))"
              using idxsum_P_component_nonempty[OF M'T, of "length (P M') - 1"]
                    P_nonempty by (simp add: last_conv_nth)
            from False lastpos have lastgt: "Lng (last (P M')) > 1" by linarith
            have PX: "P X = butlast (P M') @ P ((last (P M'))[n])"
              using conjunct2[OF m_6_2_P_oper_2[OF M'T n1 lastgt]] Xeq by simp
            have Xsplit: "X = concat (butlast (P M')) @ (last (P M'))[n]"
              using conjunct1[OF m_6_2_P_oper_2[OF M'T n1 lastgt]] Xeq by simp
            from cP PX have "c \<in> set (butlast (P M')) \<or> c \<in> set (P ((last (P M'))[n]))"
              by auto
            thus ?thesis
            proof
              assume "c \<in> set (butlast (P M'))"
              hence "c \<in> set (P M')" using in_set_butlastD by fast
              hence "c \<in> SkT_PS k" using IHk M'S by blast
              thus ?thesis by (rule rev_subsetD[OF _ SkT_PS_mono])
            next
              assume cT: "c \<in> set (P ((last (P M'))[n]))"
              have lastM: "last (P M') \<in> set (P M')" using P_nonempty by simp
              hence lastSk: "last (P M') \<in> SkT_PS k" using IHk M'S by blast
              hence YS: "(last (P M'))[n] \<in> SkT_PS (Suc k)" using n1 by auto
              have cbut: "concat (butlast (P M')) = take (Pcut M') M'"
                using poper_last_P_multi[OF multi LM'] idxsum_concat_P by simp
              have Pcutpos: "0 < Pcut M'" using Pcut_le[OF LM'] by simp
              have Pcutle: "Pcut M' \<le> Lng M' - 1" using Pcut_le[OF LM'] by simp
              have "Lng (concat (butlast (P M'))) = Pcut M'"
                using cbut Pcutle LM' by simp
              hence "Lng ((last (P M'))[n]) < Lng X"
                using Xsplit Pcutpos by simp
              hence "Lng ((last (P M'))[n]) < L" using LX by simp
              with IHL YS cT show ?thesis by blast
            qed
          qed
        qed
      qed
    qed
    show ?case using inner by blast
  qed
  thus "X \<in> SkT_PS k \<Longrightarrow> c \<in> set (P X) \<Longrightarrow> c \<in> SkT_PS k" by blast
qed

lemma m_6_7_standard_P_components:
  \<comment> \<open>m: 命題（標準形の単項成分が標準形であること） (§6.7).
     Discharges p_6_7_standard_P_components.\<close>
  assumes "M \<in> SkT_PS k"
  shows "\<forall>J < Lng (P M). P M ! J \<in> SkT_PS k"
  using assms SkT_P_comp by (metis nth_mem)


subsection \<open>§6.8 降順性 (standard \<open>P\<close>-components are descending)\<close>

text \<open>
  Auxiliary facts for the §6.8 proposition «標準形の単項成分が降順であること».
  The oper \<open>M[n]\<close> preserves the left column \<open>entry _ i 0\<close>, and for a non-multi
  \<open>c\<close> every \<open>P\<close>-component of \<open>c[n]\<close> keeps \<open>c\<close>'s \<open>(0,0)\<close> and \<open>(1,0)\<close> entries.
\<close>

lemma oper_entry_0:
  assumes M: "M \<in> T_PS" and n: "1 \<le> n"
  shows "entry (M[n]) i 0 = entry M i 0"
proof (cases "1 < Lng M")
  case True
  have "(M[n]) ! 0 = M ! 0" using poper_oper_nth0[OF M True n] by simp
  thus ?thesis by (simp add: entry_def)
next
  case False
  hence "Lng M - 1 = 0" by simp
  hence "M[n] = M" by (simp add: oper_def Let_def)
  thus ?thesis by simp
qed

lemma nonmulti_oper_components_leftcol:
  assumes c: "c \<in> T_PS" and n: "1 \<le> n" and nm: "\<not> multiT c"
    and d: "d \<in> set (P ((c::pairseq)[n]))"
  shows "entry d 0 0 = entry c 0 0 \<and> entry d 1 0 = entry c 1 0"
proof (cases "nextR c 0 0 (Lng c - 1) \<and> entry c 1 (Lng c - 1) = 0")
  case cond1: True
  have PX: "P ((c::pairseq)[n]) = replicate n (Pred c)"
    using m_6_2_nonmulti_oper_1[OF c n nm conjunct1[OF cond1] conjunct2[OF cond1]] .
  from d PX n have deq: "d = Pred c"
    by (auto simp: set_replicate_conv_if split: if_splits)
  \<comment> \<open>\<open>cond1\<close>'s \<open>nextR c 0 0 (Lng c - 1)\<close> forces \<open>1 < Lng c\<close>\<close>
  have L: "1 < Lng c"
  proof -
    have "nextrel0 c 0 (Lng c - 1)" using conjunct1[OF cond1] by (simp add: nextR_def)
    hence "0 < Lng c - 1" by (simp add: nextrel0_def)
    thus ?thesis by linarith
  qed
  have pc: "Pred c = butlast c" using L by (simp add: Pred_def)
  have "butlast c ! 0 = c ! 0" using L by (simp add: nth_butlast)
  thus ?thesis using deq pc by (simp add: entry_def)
next
  case cond2: False
  hence H: "\<not> nextR c 0 0 (Lng c - 1) \<or> entry c 1 (Lng c - 1) > 0" by auto
  have PX: "P (c[n]) = [c[n]]" using m_6_2_nonmulti_oper_2[OF c n nm H] .
  from d PX have deq: "d = c[n]" by simp
  thus ?thesis using oper_entry_0[OF c n] by simp
qed

text \<open>
  Main §6.8 proposition (row-1 tie-break of \<open>P M\<close>).  We avoid the article's
  minimal-rank \<open>k\<^sub>0\<close> induction: thanks to @{thm [source] SkT_PS_mono} a plain
  induction on the level \<open>k\<close> with \<open>M \<in> SkT_PS k\<close> suffices, with the recursive
  step handled by @{thm [source] m_6_2_P_oper_1} / @{thm [source] m_6_2_P_oper_2}
  and the inductive hypothesis applied to the parent \<open>M'\<close>.
\<close>

lemma SkT_P_descending:
  shows "X \<in> SkT_PS k \<Longrightarrow> J0' \<le> J1' \<Longrightarrow> J1' \<le> Lng (P X) - 1
         \<Longrightarrow> entry (P X ! J0') 0 0 = entry (P X ! J1') 0 0
         \<Longrightarrow> entry (P X ! J0') 1 0 \<ge> entry (P X ! J1') 1 0"
proof -
  have "\<forall>X. X \<in> SkT_PS k \<longrightarrow>
          (\<forall>J0' J1'. J0' \<le> J1' \<and> J1' \<le> Lng (P X) - 1
             \<and> entry (P X ! J0') 0 0 = entry (P X ! J1') 0 0
             \<longrightarrow> entry (P X ! J0') 1 0 \<ge> entry (P X ! J1') 1 0)"
  proof (induction k)
    case 0
    show ?case
    proof (intro allI impI)
      fix X J0' J1'
      assume X0: "X \<in> SkT_PS 0"
        and A: "J0' \<le> J1' \<and> J1' \<le> Lng (P X) - 1
                \<and> entry (P X ! J0') 0 0 = entry (P X ! J1') 0 0"
      from X0 obtain u v where Xuv: "X = diagSeq u v" and uv: "u \<le> v" by auto
      have "\<not> multiT X" using Xuv not_multiT_diagSeq[OF uv] by simp
      hence PX: "P X = [X]" by (simp add: poper_P_nonmulti)
      have "Lng (P X) = 1" using PX by simp
      hence "J1' = 0" "J0' = 0" using A by auto
      thus "entry (P X ! J0') 1 0 \<ge> entry (P X ! J1') 1 0" by simp
    qed
  next
    case (Suc k)
    note IHk = Suc.IH
    show ?case
    proof (intro allI impI)
      fix X J0' J1'
      assume XS: "X \<in> SkT_PS (Suc k)"
        and A: "J0' \<le> J1' \<and> J1' \<le> Lng (P X) - 1
                \<and> entry (P X ! J0') 0 0 = entry (P X ! J1') 0 0"
      from XS obtain M' n where Xeq: "X = (M'::pairseq)[n]"
        and M'S: "M' \<in> SkT_PS k" and n1: "1 \<le> n" by auto
      have M'T: "M' \<in> T_PS" using M'S SkT_PS_subset_ST_PS ST_PS_T_PS by blast
      from A have le01: "J0' \<le> J1'" and J1le: "J1' \<le> Lng (P X) - 1"
        and r0eq: "entry (P X ! J0') 0 0 = entry (P X ! J1') 0 0" by auto
      show "entry (P X ! J0') 1 0 \<ge> entry (P X ! J1') 1 0"
        proof (cases "multiT M'")
          case nonmulti: False
          \<comment> \<open>all \<open>P X\<close>-components agree, so the goal is reflexive\<close>
          have "P X ! J0' = P X ! J1'"
          proof (cases "nextR M' 0 0 (Lng M' - 1) \<and> entry M' 1 (Lng M' - 1) = 0")
            case cond1: True
            have PX: "P X = replicate n (Pred M')"
              using m_6_2_nonmulti_oper_1[OF M'T n1 nonmulti conjunct1[OF cond1] conjunct2[OF cond1]] Xeq by simp
            have lpx: "Lng (P X) = n" using PX by simp
            have J1n: "J1' < n" using J1le lpx n1 by linarith
            have J0n: "J0' < n" using le01 J1n by linarith
            show ?thesis using PX J0n J1n by simp
          next
            case cond2: False
            hence H: "\<not> nextR M' 0 0 (Lng M' - 1) \<or> entry M' 1 (Lng M' - 1) > 0" by auto
            have PX: "P X = [X]" using m_6_2_nonmulti_oper_2[OF M'T n1 nonmulti H] Xeq by simp
            hence "J1' \<le> 0" using J1le by simp
            hence "J0' = 0 \<and> J1' = 0" using le01 by auto
            thus ?thesis by simp
          qed
          thus ?thesis by simp
        next
          case multi: True
          have lenP: "1 < length (P M')" using multi m_6_2_P_components_2[OF M'T] by simp
          let ?c = "last (P M')"
          have ne: "P M' \<noteq> []" by (rule P_nonempty)
          have cidx: "?c = P M' ! (Lng (P M') - 1)" using ne by (simp add: last_conv_nth)
          have cmem: "?c \<in> SkT_PS k"
          proof -
            have "Lng (P M') - 1 < Lng (P M')" using ne by (cases "P M'") auto
            hence "P M' ! (Lng (P M') - 1) \<in> SkT_PS k"
              using m_6_7_standard_P_components[OF M'S] by blast
            thus ?thesis using cidx by simp
          qed
          have cT: "?c \<in> T_PS" using cmem SkT_PS_subset_ST_PS ST_PS_T_PS by blast
          have cnm: "\<not> multiT ?c"
            using m_6_2_P_components_1[OF M'T] last_in_set[OF ne] by (auto simp: multiT_def)
          show ?thesis
          proof (cases "Lng (last (P M')) = 1")
            case last1: True
            \<comment> \<open>\<open>P X = butlast (P M')\<close>: every component agrees with \<open>P M'\<close>, IH on \<open>M'\<close>\<close>
            have PX: "P X = butlast (P M')"
              using conjunct2[OF m_6_2_P_oper_1[OF M'T n1 last1]] lenP Xeq by simp
            have J1lt: "J1' < length (butlast (P M'))"
              using J1le PX lenP by simp
            have J0lt: "J0' < length (butlast (P M'))" using le01 J1lt by linarith
            have e0: "P X ! J0' = P M' ! J0'" using PX J0lt by (simp add: nth_butlast)
            have e1: "P X ! J1' = P M' ! J1'" using PX J1lt by (simp add: nth_butlast)
            have J1leM': "J1' \<le> Lng (P M') - 1" using J1lt by simp
            have h0: "entry (P M' ! J0') 0 0 = entry (P M' ! J1') 0 0"
              using r0eq e0 e1 by simp
            have "entry (P M' ! J0') 1 0 \<ge> entry (P M' ! J1') 1 0"
              using IHk M'S le01 J1leM' h0 by blast
            thus ?thesis using e0 e1 by simp
          next
            case False
            have lastpos: "0 < Lng (last (P M'))"
              using idxsum_P_component_nonempty[OF M'T, of "length (P M') - 1"] P_nonempty
              by (simp add: last_conv_nth)
            from False lastpos have lastgt: "1 < Lng (last (P M'))" by linarith
            \<comment> \<open>\<open>P X = butlast (P M') @ P (c[n])\<close>\<close>
            have PX: "P X = butlast (P M') @ P (?c[n])"
              using conjunct2[OF m_6_2_P_oper_2[OF M'T n1 lastgt]] Xeq by simp
            define J0 where "J0 = length (butlast (P M'))"
            have J0eq: "J0 = Lng (P M') - 1" by (simp add: J0_def)
            have lenPX: "length (P X) = J0 + length (P (?c[n]))"
              using PX by (simp add: J0_def)
            have ccidx: "?c = P M' ! J0" using cidx J0eq by simp
            have pre: "P X ! J = P M' ! J" if "J < J0" for J
              using PX that by (simp add: nth_append nth_butlast J0_def)
            have tail: "P X ! J = P (?c[n]) ! (J - J0)" if "J0 \<le> J" for J
              using PX that by (simp add: nth_append J0_def)
            have neX: "P X \<noteq> []" by (rule P_nonempty)
            have J1ltX: "J1' < length (P X)" using J1le neX by (cases "P X") auto
            show ?thesis
            proof (cases "J1' < J0")
              case AA: True
              \<comment> \<open>both in the prefix: IH on \<open>M'\<close>\<close>
              have e0: "P X ! J0' = P M' ! J0'" using pre le01 AA by simp
              have e1: "P X ! J1' = P M' ! J1'" using pre AA by simp
              have J1leM': "J1' \<le> Lng (P M') - 1" using AA J0eq by linarith
              have h0: "entry (P M' ! J0') 0 0 = entry (P M' ! J1') 0 0"
                using r0eq e0 e1 by simp
              have "entry (P M' ! J0') 1 0 \<ge> entry (P M' ! J1') 1 0"
                using IHk M'S le01 J1leM' h0 by blast
              thus ?thesis using e0 e1 by simp
            next
              case AB: False
              hence J0leJ1: "J0 \<le> J1'" by simp
              have dmem: "P X ! J1' \<in> set (P (?c[n]))"
              proof -
                have "J1' - J0 < length (P (?c[n]))" using lenPX J0leJ1 J1ltX by linarith
                hence "P (?c[n]) ! (J1' - J0) \<in> set (P (?c[n]))" by (rule nth_mem)
                thus ?thesis using tail[OF J0leJ1] by simp
              qed
              have dlc0: "entry (P X ! J1') 0 0 = entry ?c 0 0"
                and dlc1: "entry (P X ! J1') 1 0 = entry ?c 1 0"
                using nonmulti_oper_components_leftcol[OF cT n1 cnm dmem] by auto
              show ?thesis
              proof (cases "J0' < J0")
                case BB: True
                \<comment> \<open>\<open>J0' < J0 \<le> J1'\<close>: prefix vs tail, IH on \<open>M'\<close> at \<open>(J0', J0)\<close>\<close>
                have e0: "P X ! J0' = P M' ! J0'" using pre BB by simp
                have r0M': "entry (P M' ! J0') 0 0 = entry (P M' ! J0) 0 0"
                  using r0eq e0 dlc0 ccidx by simp
                have J0leJ0: "J0' \<le> J0" using BB by linarith
                have J0leM': "J0 \<le> Lng (P M') - 1" using J0eq by simp
                have "entry (P M' ! J0') 1 0 \<ge> entry (P M' ! J0) 1 0"
                  using IHk M'S J0leJ0 J0leM' r0M' by blast
                hence "entry (P X ! J0') 1 0 \<ge> entry ?c 1 0" using e0 ccidx by simp
                thus ?thesis using dlc1 by simp
              next
                case BC: False
                \<comment> \<open>both in the tail: helper gives equal row-1\<close>
                hence J0leJ0': "J0 \<le> J0'" by simp
                have d0mem: "P X ! J0' \<in> set (P (?c[n]))"
                proof -
                  have "J0' < length (P X)" using le01 J1ltX by linarith
                  hence "J0' - J0 < length (P (?c[n]))" using lenPX J0leJ0' by linarith
                  hence "P (?c[n]) ! (J0' - J0) \<in> set (P (?c[n]))" by (rule nth_mem)
                  thus ?thesis using tail[OF J0leJ0'] by simp
                qed
                have "entry (P X ! J0') 1 0 = entry ?c 1 0"
                  using nonmulti_oper_components_leftcol[OF cT n1 cnm d0mem] by simp
                thus ?thesis using dlc1 by simp
              qed
            qed
          qed
        qed
      qed
    qed
  thus "X \<in> SkT_PS k \<Longrightarrow> J0' \<le> J1' \<Longrightarrow> J1' \<le> Lng (P X) - 1
         \<Longrightarrow> entry (P X ! J0') 0 0 = entry (P X ! J1') 0 0
         \<Longrightarrow> entry (P X ! J0') 1 0 \<ge> entry (P X ! J1') 1 0" by blast
qed

lemma m_6_8_standard_P_descending:
  \<comment> \<open>m: 命題（標準形の単項成分が降順であること） (§6.8).
     Discharges p_6_8_standard_P_descending.\<close>
  assumes "M \<in> ST_PS" "J0' \<le> J1'" "J1' \<le> Lng (P M) - 1"
    "entry (P M ! J0') 0 0 = entry (P M ! J1') 0 0"
  shows "entry (P M ! J0') 1 0 \<ge> entry (P M ! J1') 1 0"
proof -
  obtain k where "M \<in> SkT_PS k"
    using assms(1) ST_PS_subset_Union_SkT by auto
  thus ?thesis using SkT_P_descending assms(2,3,4) by blast
qed

text \<open>Corollary (article §6.8 «(1) P(M) は降順である»): for \<open>X \<in> ST\<^bsub>PS\<^esub>\<close> the
  component list \<open>P X\<close> is descending.  Combines the row-0 monotonicity
  @{thm [source] m_6_4_P_leftend_mono} with the row-1 tie-break
  @{thm [source] m_6_8_standard_P_descending}.\<close>

lemma descending_P_of_ST:
  assumes "X \<in> ST_PS"
  shows "descending (P X)"
  unfolding descending_def
proof (intro allI impI)
  fix J0 J1
  assume H: "J0 \<le> J1 \<and> J1 \<le> Lng (P X) - 1"
  have XT: "X \<in> T_PS" using assms ST_PS_T_PS by blast
  from H have le: "J0 \<le> J1" and j1: "J1 \<le> Lng (P X) - 1" by auto
  have r0: "entry (P X ! J1) 0 0 \<le> entry (P X ! J0) 0 0"
    by (rule m_6_4_P_leftend_mono[OF XT le j1])
  have tie: "entry (P X ! J0) 0 0 = entry (P X ! J1) 0 0
             \<Longrightarrow> entry (P X ! J1) 1 0 \<le> entry (P X ! J0) 1 0"
    using m_6_8_standard_P_descending[OF assms le j1] by simp
  from r0 tie show "entry (P X ! J1) 0 0 \<le> entry (P X ! J0) 0 0
        \<and> (entry (P X ! J0) 0 0 = entry (P X ! J1) 0 0
           \<longrightarrow> entry (P X ! J1) 1 0 \<le> entry (P X ! J0) 1 0)" by blast
qed


section \<open>§7.1 Buchholz notation: principal components (命題（順序数項の単項成分の基本性質）)\<close>

text \<open>
  Lemma m_7_1_term_components: for \<open>t = Trm ps\<close>, the component list \<open>P\<^bsub>B\<^esub> t\<close>
  is empty iff \<open>t = 0\<close>, and \<open>\<Sigma>\<^bsub>B\<^esub> (P\<^bsub>B\<^esub> t) = t\<close>.
\<close>

lemma m_7_1_term_components:
  \<comment> \<open>m: 命題（順序数項の単項成分の基本性質）(1)(2) (§7.1)\<close>
  assumes "t \<in> T_B"
  shows "(Lng (PB t) = 0 \<longleftrightarrow> t = Trm []) \<and> SigmaB (PB t) = t"
proof (cases t)
  case (Trm ps)
  show ?thesis
    unfolding Trm PB_def SigmaB_def
    by (auto simp: comp_def)
qed

text \<open>
  Mutual structural induction: both \<open>flatBT\<close> and \<open>flatBP\<close> produce paren-balanced strings.
  We prove the two claims simultaneously using the function induction rule
  \<open>flatBT_flatBP.induct\<close>.
\<close>

\<comment> \<open>Helper: equal LP/RP counts preserved under concat of balanced lists\<close>
lemma filter_concat_bal:
  "\<forall>xs \<in> set xss.
     length (filter ((=) LP) xs) = length (filter ((=) RP) xs) \<Longrightarrow>
   length (filter ((=) LP) (concat xss)) = length (filter ((=) RP) (concat xss))"
  by (induct xss) auto

lemma flatBT_paren_balance:
  "length (filter ((=) LP) (flatBT t)) = length (filter ((=) RP) (flatBT t))"
  and flatBP_paren_balance:
  "length (filter ((=) LP) (flatBP p)) = length (filter ((=) RP) (flatBP p))"
proof (induct rule: flatBT_flatBP.induct)
  \<comment> \<open>flatBT (Trm []) = [Zsym]: no parens\<close>
  case 1 show ?case by simp
next
  \<comment> \<open>flatBT (Trm [p]) = flatBP p: balance by IH for p\<close>
  case (2 p) show ?case using 2 by simp
next
  \<comment> \<open>flatBT (Trm (p#q#ps)) = LP # (flatBP p @ concat ...) @ [RP]\<close>
  case (3 p q ps)
  \<comment> \<open>IH(1): flatBP p is balanced; IH(2): flatBP r is balanced for r \<in> set(q#ps)\<close>
  have IH_p: "length (filter ((=) LP) (flatBP p)) =
              length (filter ((=) RP) (flatBP p))"
    using 3(1) by blast
  have IH_qps: "\<forall>r \<in> set (q # ps).
    length (filter ((=) LP) (flatBP r)) = length (filter ((=) RP) (flatBP r))"
    using 3(2) by simp
  have concat_bal:
    "length (filter ((=) LP) (concat (map (\<lambda>r. CM # flatBP r) (q # ps)))) =
     length (filter ((=) RP) (concat (map (\<lambda>r. CM # flatBP r) (q # ps))))"
  proof (rule filter_concat_bal)
    show "\<forall>xs \<in> set (map (\<lambda>r. CM # flatBP r) (q # ps)).
      length (filter ((=) LP) xs) = length (filter ((=) RP) xs)"
    proof
      fix xs assume "xs \<in> set (map (\<lambda>r. CM # flatBP r) (q # ps))"
      then obtain r where "r \<in> set (q # ps)" "xs = CM # flatBP r" by auto
      thus "length (filter ((=) LP) xs) = length (filter ((=) RP) xs)"
        using IH_qps by auto
    qed
  qed
  show ?case
  proof -
    define inner where "inner = flatBP p @ concat (map (\<lambda>r. CM # flatBP r) (q # ps))"
    have expand: "flatBT (Trm (p # q # ps)) = LP # inner @ [RP]"
      unfolding inner_def by simp
    have inner_bal: "length (filter ((=) LP) inner) = length (filter ((=) RP) inner)"
      unfolding inner_def
      by (simp only: filter_append length_append IH_p concat_bal)
    show ?thesis
      unfolding expand
      using inner_bal by simp
  qed
next
  \<comment> \<open>flatBP (DB u a) = Dsym u # flatBT a: balance by IH for a\<close>
  case (4 u a) show ?case using 4 by simp
qed

lemma m_7_1_paren_balance:
  \<comment> \<open>m: 命題（括弧の対応）(§7.1) — the \<open>(\<close>-count equals the \<open>)\<close>-count in \<open>flat t\<close>\<close>
  assumes "t \<in> T_B"
  shows "length (filter (\<lambda>x. x = LP) (flatBT t)) =
         length (filter (\<lambda>x. x = RP) (flatBT t))"
proof -
  have LP_eq: "filter (\<lambda>x. x = LP) (flatBT t) = filter ((=) LP) (flatBT t)"
    by (rule filter_cong) (auto simp: eq_commute)
  have RP_eq: "filter (\<lambda>x. x = RP) (flatBT t) = filter ((=) RP) (flatBT t)"
    by (rule filter_cong) (auto simp: eq_commute)
  show ?thesis unfolding LP_eq RP_eq using flatBT_paren_balance[of t] .
qed

end
