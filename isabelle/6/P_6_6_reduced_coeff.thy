theory P_6_6_reduced_coeff
  imports Support_6_046
begin

text \<open>補題（簡約性と係数の基本性質） — in a reduced sequence row 0 dominates row 1.\<close>

text \<open>
  m: §6.6 命題（簡約性と係数の関係）coefficient corollary.  For a REDUCED
  \<open>M \<in> RT_PS\<close>, row 0 dominates row 1 at EVERY column \<open>j\<close>:
  \<open>entry M 0 j \<ge> entry M 1 j\<close>.  This generalizes the column-0 case
  @{thm [source] kst_reduced_row1_le_row0} to all columns, and unlike
  @{thm [source] m_6_6_condAB_coeff} (Part 2) it needs NO core hypothesis
  (\<open>entry M 0 0 = 0 \<and> entry M 1 0 = 0\<close>) — a general reduced \<open>M\<close> is not core.

  Route: the FORWARD keystone @{thm [source] kst_reduced_imp_condAB_uncond}
  gives \<open>RedCondA M \<and> RedCondB M\<close> unconditionally for \<open>M \<in> RT_PS\<close>.  Then strong
  induction on \<open>j\<close>, splitting on whether column \<open>j\<close> has a row-1 parent:
  \<^item> row-1 parent \<open>p\<^sub>1\<close> exists: \<open>entry M 1 j = entry M 1 p\<^sub>1 + 1\<close> (RedCondA),
    \<open>leR M 0 p\<^sub>1 j\<close> (from \<open>nextR\<close>, @{thm [source] poper_nextR_imp_le0}), so
    \<open>entry M 0 p\<^sub>1 < entry M 0 j\<close> (@{thm [source] m_5_1_ancestor_basic_1}); with
    IH \<open>entry M 1 p\<^sub>1 \<le> entry M 0 p\<^sub>1\<close> we get the bound.
  \<^item> no row-1 parent:
      \<^item> no row-0 parent either: RedCondB pins \<open>entry M 0 j = entry M 1 j\<close>.
      \<^item> row-0 parent \<open>p\<^sub>0\<close> exists: were \<open>entry M 1 p\<^sub>0 < entry M 1 j\<close>, then with
        \<open>leR M 0 p\<^sub>0 j\<close> (\<open>nextR M 0 p\<^sub>0 j\<close>) @{thm [source] m_5_1_parent_exists_2}
        would produce a row-1 parent of \<open>j\<close> — contradiction.  Hence
        \<open>entry M 1 j \<le> entry M 1 p\<^sub>0\<close>; with IH \<open>entry M 1 p\<^sub>0 \<le> entry M 0 p\<^sub>0\<close> and
        \<open>entry M 0 p\<^sub>0 < entry M 0 j\<close> the bound follows.
  Empirically verified (red_charac enum maxlen3,val4): 0 failures.\<close>

lemma m_6_6_reduced_coeff:
  assumes M: "M \<in> RT_PS" and jL: "j < Lng M"
  shows "entry M 0 j \<ge> entry M 1 j"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have condAB: "RedCondA M \<and> RedCondB M"
    by (rule kst_reduced_imp_condAB_uncond[OF M])
  have condA: "RedCondA M" and condB: "RedCondB M" using condAB by simp_all
  \<comment> \<open>RedCondA: a node equals its parent value plus one.\<close>
  have condA_entry: "\<And>i j'. i \<le> 1 \<Longrightarrow> j' < Lng M \<Longrightarrow> hasParent M i j' \<Longrightarrow>
      entry M i (parent M i j') + 1 = entry M i j'"
    using condA unfolding RedCondA_def by blast
  \<comment> \<open>The parent witness is an actual \<open>nextR\<close> edge.\<close>
  have par_nextR: "\<And>i j'. hasParent M i j' \<Longrightarrow> nextR M i (parent M i j') j'"
    unfolding hasParent_def parent_def by (rule theI')
  \<comment> \<open>Main strong induction on the column \<open>j\<close>.\<close>
  have key: "\<forall>j. j < Lng M \<longrightarrow> entry M 0 j \<ge> entry M 1 j"
  proof (intro allI impI)
    fix j assume "j < Lng M"
    thus "entry M 0 j \<ge> entry M 1 j"
    proof (induction j rule: less_induct)
      case (less j)
      show "entry M 0 j \<ge> entry M 1 j"
      proof (cases "hasParent M 1 j")
        case hp1: True
        \<comment> \<open>Row-1 parent case (independent of core; mirrors @{thm [source] m_6_6_condAB_coeff} Part 2).\<close>
        let ?p1 = "parent M 1 j"
        have par1: "nextR M 1 ?p1 j" using par_nextR[OF hp1] .
        have p1lt: "?p1 < j" and leR0p1j: "leR M 0 ?p1 j"
          using poper_nextR_imp_le0[OF par1] by simp_all
        have p1L: "?p1 < Lng M" using p1lt less.prems by linarith
        have e1A: "entry M 1 ?p1 + 1 = entry M 1 j"
          using condA_entry[of 1 j] hp1 less.prems by simp
        have IH1: "entry M 0 ?p1 \<ge> entry M 1 ?p1" using less.IH[OF p1lt p1L] .
        have e0lt: "entry M 0 ?p1 < entry M 0 j"
          by (rule m_5_1_ancestor_basic_1[OF MT p1lt _ leR0p1j]) simp
        from e1A IH1 e0lt show ?thesis by linarith
      next
        case hp1: False
        show ?thesis
        proof (cases "hasParent M 0 j")
          case hp0: False
          \<comment> \<open>No parent in either row: RedCondB pins row 0 = row 1.\<close>
          have jle: "j \<le> Lng M - 1" using less.prems by linarith
          have "entry M 0 j = entry M 1 j"
            using condB hp0 jle unfolding RedCondB_def by blast
          thus ?thesis by simp
        next
          case hp0: True
          \<comment> \<open>Row-0 parent but no row-1 parent.\<close>
          let ?p0 = "parent M 0 j"
          have par0: "nextR M 0 ?p0 j" using par_nextR[OF hp0] .
          have p0lt: "?p0 < j" and leR0p0j: "leR M 0 ?p0 j"
            using poper_nextR_imp_le0[OF par0] by simp_all
          have p0L: "?p0 < Lng M" using p0lt less.prems by linarith
          \<comment> \<open>Were \<open>entry M 1 ?p0 < entry M 1 j\<close>, a row-1 parent of \<open>j\<close> would exist.\<close>
          have e1le: "entry M 1 j \<le> entry M 1 ?p0"
          proof (rule ccontr)
            assume "\<not> entry M 1 j \<le> entry M 1 ?p0"
            hence elt: "entry M 1 ?p0 < entry M 1 j" by simp
            obtain j' where j'par: "?p0 \<le> j'" "j' < j" "nextR M 1 j' j"
              using m_5_1_parent_exists_2[OF MT p0lt less.prems elt leR0p0j] by blast
            \<comment> \<open>Such an edge means \<open>hasParent M 1 j\<close>, contradicting hp1.\<close>
            have "hasParent M 1 j"
              unfolding hasParent_def
            proof (rule ex_ex1I)
              show "\<exists>a. nextR M 1 a j" using j'par(3) by blast
            next
              fix a b assume "nextR M 1 a j" "nextR M 1 b j"
              thus "a = b" by (rule nextR1_unique)
            qed
            thus False using hp1 by simp
          qed
          have IH0: "entry M 0 ?p0 \<ge> entry M 1 ?p0" using less.IH[OF p0lt p0L] .
          have e0lt: "entry M 0 ?p0 < entry M 0 j"
            by (rule m_5_1_ancestor_basic_1[OF MT p0lt _ leR0p0j]) simp
          from e1le IH0 e0lt show ?thesis by linarith
        qed
      qed
    qed
  qed
  show ?thesis using key jL by blast
qed


lemma p_6_6_reduced_coeff:
  assumes "M \<in> RT_PS" "j < Lng M"
  shows "entry M 0 j \<ge> entry M 1 j"
  using assms by (rule m_6_6_reduced_coeff)

end
