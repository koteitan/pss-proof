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

