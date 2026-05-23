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
  m: 命題（F_M と基本列の関係）— corrected form (see @{file "amendments.md"} A1).
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

