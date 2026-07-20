theory Frontier_6_010
  imports P_6_3_marked_slice
begin

text \<open>m: 命題（\<open>P\<close>と基本列の関係） — discharges @{text p_6_2_P_oper_1},
  @{text p_6_2_P_oper_2}.\<close>

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

text \<open>\<open>nextR\<close> / \<open>leR\<close> commute with left truncation.\<close>

lemma poper_nextR_drop:
  assumes "a < Lng M - c" "b < Lng M - c"
  shows "nextR (drop c M) i a b \<longleftrightarrow> nextR M i (c + a) (c + b)"
  unfolding nextR_def
  using poper_nextrel0_drop[OF assms] poper_nextrel1_drop[OF assms] by simp

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

end
