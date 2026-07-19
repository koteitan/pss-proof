theory Frontier_6_062
  imports P_6_6_reduced_leftend
begin

text \<open>STEP 2 (keystone) — partial: the \<open>zeroT\<close> base case of
  \<open>p_6_6_reduced_iff_cond\<close>.  For a \<open>zeroT\<close> \<open>M\<close> (so \<open>Lng M = 1\<close>, \<open>M\<^bsub>1,0\<^esub> = 0\<close>,
  \<open>M = [(m\<^sub>0\<^sub>0, 0)]\<close>):
  \<^item> No node has a parent (\<open>nextR\<close> needs two distinct columns but \<open>Lng M = 1\<close>), so
    \<open>RedCondA M\<close> is vacuously true and \<open>RedCondB M \<longleftrightarrow> m\<^sub>0\<^sub>0 = m\<^sub>1\<^sub>0 = 0\<close>.
  \<^item> \<open>Red M = [(0,0)]\<close> (zeroT branch), so \<open>M \<in> RT\<^bsub>PS\<^esub> \<longleftrightarrow> M = [(0,0)] \<longleftrightarrow> m\<^sub>0\<^sub>0 = 0\<close>.
  Both sides reduce to \<open>entry M 0 0 = 0\<close>.  This is one WLOG base case of the
  article's \<open>j\<^sub>1\<close>-induction (the others — \<open>multiT\<close> via
  @{thm [source] key_reduced_iff_cond_multi}, and the \<open>monoT\<close> \<open>j\<^sub>1\<close>-induction —
  remain).\<close>

lemma kst_no_parent_Lng1:
  assumes L1: "Lng M = 1"
  shows "\<not> hasParent M i j1"
proof -
  have noex: "\<not> (\<exists>j0. nextR M i j0 j1)"
  proof
    assume "\<exists>j0. nextR M i j0 j1"
    then obtain j0 where nx: "nextR M i j0 j1" by blast
    have "j0 < j1 \<and> j1 < Lng M"
    proof (cases "i = 0")
      case True
      thus ?thesis using nx by (simp add: nextR_def nextrel0_def)
    next
      case False
      thus ?thesis using nx by (simp add: nextR_def nextrel1_def)
    qed
    thus False using L1 by auto
  qed
  show ?thesis unfolding hasParent_def using noex by blast
qed

lemma kst_reduced_iff_cond_zeroT:
  assumes MT: "M \<in> T_PS" and z: "zeroT M"
  shows "(M \<in> RT_PS) \<longleftrightarrow> RedCondA M \<and> RedCondB M"
proof -
  have L1: "Lng M = 1" using z by (simp add: zeroT_def)
  have m10z: "entry M 1 0 = 0" using z by (simp add: zeroT_def)
  \<comment> \<open>\<open>M = [(m\<^sub>0\<^sub>0, 0)]\<close>.\<close>
  obtain p where Mp: "M = [p]" using L1 by (cases M) auto
  have Mpair: "M = [(entry M 0 0, entry M 1 0)]"
    using Mp by (cases p) (simp add: entry_def)
  \<comment> \<open>No parents (\<open>Lng M = 1\<close>): \<open>RedCondA\<close> vacuous, \<open>RedCondB \<longleftrightarrow> m\<^sub>0\<^sub>0 = m\<^sub>1\<^sub>0\<close>.\<close>
  have noP: "\<And>i j1. \<not> hasParent M i j1" by (rule kst_no_parent_Lng1[OF L1])
  have condA: "RedCondA M" using noP by (simp add: RedCondA_def)
  have condB_iff: "RedCondB M \<longleftrightarrow> entry M 0 0 = entry M 1 0"
  proof
    assume "RedCondB M"
    thus "entry M 0 0 = entry M 1 0"
      using noP L1 by (simp add: RedCondB_def)
  next
    assume eq: "entry M 0 0 = entry M 1 0"
    show "RedCondB M" unfolding RedCondB_def
    proof (intro allI impI)
      fix j1' assume "\<not> hasParent M 0 j1' \<and> j1' \<le> Lng M - 1"
      hence "j1' = 0" using L1 by simp
      thus "entry M 0 j1' = entry M 1 j1'" using eq by simp
    qed
  qed
  \<comment> \<open>\<open>Red M = [(0,0)]\<close>; \<open>M \<in> RT\<^bsub>PS\<^esub> \<longleftrightarrow> M = [(0,0)] \<longleftrightarrow> m\<^sub>0\<^sub>0 = 0\<close>.\<close>
  have dom: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have redEq: "Red M = [(0,0)]" using Red.psimps[OF dom] z by simp
  have RT_iff: "(M \<in> RT_PS) \<longleftrightarrow> entry M 0 0 = 0"
  proof
    assume "M \<in> RT_PS"
    hence "Red M = M" by (simp add: RT_PS_def)
    hence "M = [(0,0)]" using redEq by simp
    thus "entry M 0 0 = 0" by (simp add: entry_def)
  next
    assume e0: "entry M 0 0 = 0"
    have "M = [(0,0)]" using Mpair e0 m10z by simp
    hence "Red M = M" using redEq by simp
    thus "M \<in> RT_PS" using MT by (simp add: RT_PS_def)
  qed
  show ?thesis using RT_iff condA condB_iff m10z by simp
qed


subsection \<open>§6.6 keystone forward — \<open>M \<in> RT\<^bsub>PS\<^esub> \<Longrightarrow> RedCondA M \<and> RedCondB M\<close> (Front A)\<close>

text \<open>FWD brick: a diagonal \<open>diagSeq u v\<close> (\<open>u \<le> v\<close>) satisfies both \<open>RedCondA\<close> and
  \<open>RedCondB\<close>.  Every node \<open>j > 0\<close> has unique row-\<open>i\<close> parent \<open>j-1\<close> with
  \<open>entry i (j-1) + 1 = entry i j\<close> (entries are \<open>u + j\<close>); the only node with no
  row-0 parent is \<open>j = 0\<close>, where \<open>entry 0 0 = u = entry 1 0\<close>.  This discharges the
  \<open>monoT\<close>-core trunk subcase (\<open>TrMax M = Lng M - 1\<close>, where
  @{thm [source] m_6_6_RedCondA_core_diag}-style reasoning makes \<open>M\<close> a diagonal)
  and is the base shape of the article's \<open>j\<^sub>1\<close>-induction.\<close>

lemma kfwd_nextR_diagSeq_parent:
  assumes uv: "u \<le> v" and i: "i \<le> 1"
    and nx: "nextR (diagSeq u v) i j0 j1"
  shows "Suc j0 = j1"
proof -
  let ?M = "diagSeq u v"
  have L: "Lng ?M = Suc v - u" by simp
  consider (r0) "i = 0" | (r1) "i = 1" using i by linarith
  thus ?thesis
  proof cases
    case r0
    have nr0: "nextrel0 ?M j0 j1" using nx r0 by (simp add: nextR_def)
    have j0L: "j0 < Lng ?M" and j1L: "j1 < Lng ?M" and lt: "j0 < j1"
      and univ: "\<forall>j. j0 < j \<and> j < j1 \<longrightarrow> entry ?M 0 j \<ge> entry ?M 0 j1"
      using nr0 by (simp_all add: nextrel0_def)
    show ?thesis
    proof (rule ccontr)
      assume "Suc j0 \<noteq> j1"
      hence j0lt: "j0 < j1 - 1" using lt by linarith
      hence mid: "j0 < j1 - 1 \<and> j1 - 1 < j1" using lt by linarith
      have j1pos: "0 < j1" using lt by linarith
      have m1L: "j1 - 1 < Suc v - u" using j1L L by linarith
      have j1L': "j1 < Suc v - u" using j1L L by simp
      have em: "entry ?M 0 (j1 - 1) = u + (j1 - 1)"
        by (rule entry_diagSeq[OF m1L])
      have ej: "entry ?M 0 j1 = u + j1" by (rule entry_diagSeq[OF j1L'])
      have hi: "entry ?M 0 (j1 - 1) < entry ?M 0 j1"
        using em ej j1pos by simp
      have "entry ?M 0 (j1 - 1) \<ge> entry ?M 0 j1" using univ mid by blast
      thus False using hi by simp
    qed
  next
    case r1
    have nr1: "nextrel1 ?M j0 j1" using nx r1 by (simp add: nextR_def)
    have j0L: "j0 < Lng ?M" and j1L: "j1 < Lng ?M" and lt: "j0 < j1"
      and le0: "le0 ?M j0 j1"
      and univ: "\<forall>j. j0 < j \<and> le0 ?M j j1 \<longrightarrow> entry ?M 1 j \<ge> entry ?M 1 j1"
      using nr1 by (simp_all add: nextrel1_def)
    show ?thesis
    proof (rule ccontr)
      assume "Suc j0 \<noteq> j1"
      hence j0lt: "j0 < j1 - 1" using lt by linarith
      have m1L: "j1 - 1 < Suc v - u" using j1L L by linarith
      have j1L'': "j1 < Suc v - u" using j1L L by simp
      have le0mid: "le0 ?M (j1 - 1) j1"
        using le0_diagSeq[OF m1L j1L''] by simp
      have mid: "j0 < j1 - 1 \<and> le0 ?M (j1 - 1) j1" using j0lt le0mid by simp
      have j1pos: "0 < j1" using lt by linarith
      have em: "entry ?M 1 (j1 - 1) = u + (j1 - 1)"
        by (rule entry_diagSeq[OF m1L])
      have ej: "entry ?M 1 j1 = u + j1" by (rule entry_diagSeq[OF j1L''])
      have hi: "entry ?M 1 (j1 - 1) < entry ?M 1 j1"
        using em ej j1pos by simp
      have "entry ?M 1 (j1 - 1) \<ge> entry ?M 1 j1" using univ mid by blast
      thus False using hi by simp
    qed
  qed
qed

lemma kfwd_condAB_diagSeq:
  assumes uv: "u \<le> v"
  shows "RedCondA (diagSeq u v) \<and> RedCondB (diagSeq u v)"
proof
  let ?M = "diagSeq u v"
  have L: "Lng ?M = Suc v - u" by simp
  show "RedCondA ?M"
    unfolding RedCondA_def
  proof (intro allI impI)
    fix i j1' assume i: "i \<le> 1" and hp: "hasParent ?M i j1'"
    have exu: "\<exists>!p. nextR ?M i p j1'" using hp by (simp add: hasParent_def)
    have par: "nextR ?M i (parent ?M i j1') j1'"
      unfolding parent_def using exu by (rule theI')
    let ?p = "parent ?M i j1'"
    have suc: "Suc ?p = j1'" by (rule kfwd_nextR_diagSeq_parent[OF uv i par])
    have j1L: "j1' < Lng ?M"
      using par by (cases "i = 0") (auto simp: nextR_def nextrel0_def nextrel1_def)
    have pL: "?p < Suc v - u" using suc j1L L by linarith
    have j1L': "j1' < Suc v - u" using j1L L by simp
    have ep: "entry ?M i ?p = u + ?p" by (rule entry_diagSeq[OF pL])
    have ej: "entry ?M i j1' = u + j1'" by (rule entry_diagSeq[OF j1L'])
    have "entry ?M i ?p + 1 = u + ?p + 1" using ep by simp
    also have "\<dots> = u + j1'" using suc by simp
    also have "\<dots> = entry ?M i j1'" using ej by simp
    finally show "entry ?M i ?p + 1 = entry ?M i j1'" .
  qed
next
  let ?M = "diagSeq u v"
  have L: "Lng ?M = Suc v - u" by simp
  show "RedCondB ?M"
    unfolding RedCondB_def
  proof (intro allI impI)
    fix j1' assume H: "\<not> hasParent ?M 0 j1' \<and> j1' \<le> Lng ?M - 1"
    hence noP: "\<not> hasParent ?M 0 j1'" and hle: "j1' \<le> Lng ?M - 1" by simp_all
    have j1L: "j1' < Suc v - u" using hle L uv by linarith
    \<comment> \<open>If \<open>j1' > 0\<close>, then \<open>j1'-1\<close> is a unique row-0 parent (contradiction).\<close>
    have "j1' = 0"
    proof (rule ccontr)
      assume "j1' \<noteq> 0"
      hence j1pos: "0 < j1'" by simp
      have step: "nextrel0 ?M (j1' - 1) j1'"
        using nextrel0_diagSeq_step[of "j1' - 1" v u] uv j1pos j1L L
        by (metis Suc_diff_1 j1pos)
      have nx: "nextR ?M 0 (j1' - 1) j1'" using step by (simp add: nextR_def)
      have uniq: "\<And>q. nextR ?M 0 q j1' \<Longrightarrow> q = j1' - 1"
      proof -
        fix q assume nq: "nextR ?M 0 q j1'"
        have "Suc q = j1'"
          by (rule kfwd_nextR_diagSeq_parent[OF uv _ nq]) simp
        thus "q = j1' - 1" by simp
      qed
      have "hasParent ?M 0 j1'" unfolding hasParent_def using nx uniq by blast
      thus False using noP by simp
    qed
    thus "entry ?M 0 j1' = entry ?M 1 j1'"
      using entry_diagSeq[OF j1L, of 0] entry_diagSeq[OF j1L, of 1] by simp
  qed
qed

text \<open>FWD monoT-core-trunk subcase: a reduced \<open>monoT M\<close> with \<open>M\<^sub>0 = (0,0)\<close> and
  \<open>TrMax M = Lng M - 1\<close> is the diagonal \<open>diagSeq 0 (Lng M - 1)\<close> (the \<open>Red\<close>
  core-trunk branch outputs \<open>diagSeq m\<^sub>1\<^sub>0 (m\<^sub>1\<^sub>0 + j\<^sub>1) = diagSeq 0 j\<^sub>1\<close> and
  \<open>Red M = M\<close>); hence it satisfies \<open>RedCondA \<and> RedCondB\<close> by
  @{thm [source] kfwd_condAB_diagSeq}.  Unlike
  @{thm [source] m_6_6_RedCondA_core_diag} this needs no \<open>RedCondA\<close> hypothesis —
  it derives the diagonal directly from reducedness, which is what the forward
  direction requires.\<close>

lemma kfwd_reduced_core_trunk_diag:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and trmax: "TrMax M = Lng M - 1"
  shows "M = diagSeq 0 (Lng M - 1)"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have redM: "Red M = M" using M by (simp add: RT_PS_def)
  have nz: "\<not> zeroT M" using mono by (simp add: monoT_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  have dom: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  let ?j1 = "Lng M - 1"
  have rM: "Red M = diagSeq (entry M 1 0) (entry M 1 0 + ?j1)"
    using Red.psimps[OF dom] nz nmu e00 e10 trmax by (simp add: Let_def)
  have "M = diagSeq (entry M 1 0) (entry M 1 0 + ?j1)" using rM redM by simp
  thus ?thesis using e10 by simp
qed

lemma kfwd_reduced_core_trunk_condAB:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and trmax: "TrMax M = Lng M - 1"
  shows "RedCondA M \<and> RedCondB M"
proof -
  have Mdiag: "M = diagSeq 0 (Lng M - 1)"
    by (rule kfwd_reduced_core_trunk_diag[OF M mono e00 e10 trmax])
  have "RedCondA (diagSeq 0 (Lng M - 1)) \<and> RedCondB (diagSeq 0 (Lng M - 1))"
    by (rule kfwd_condAB_diagSeq) simp
  thus ?thesis using Mdiag by simp
qed

text \<open>FWD brick: a \<open>monoT\<close> core sequence (\<open>M\<^sub>0 = (0,0)\<close>) has \<open>entry (Red M) 0 0 = 0\<close>.
  Both \<open>Red\<close> core branches start with a leading diagonal \<open>diagSeq 0 _\<close> (trunk:
  \<open>diagSeq m\<^sub>1\<^sub>0 _ = diagSeq 0 _\<close>; nontrunk: \<open>diagSeq 0 (TrMax M) @ _\<close>), whose
  row-0 value at index 0 is 0.  (Standalone version of the core case of
  @{thm [source] m_6_5_Red_leftend_row0_min}.)\<close>

lemma kfwd_Red_core_leftend00:
  assumes MT: "M \<in> T_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
  shows "entry (Red M) 0 0 = 0"
proof -
  have nz: "\<not> zeroT M" using mono by (simp add: monoT_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  have dom: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  let ?j1 = "Lng M - 1" and ?j1' = "TrMax M"
  show ?thesis
  proof (cases "?j1' = ?j1")
    case True
    have rM: "Red M = diagSeq (entry M 1 0) (entry M 1 0 + ?j1)"
      using Red.psimps[OF dom] nz nmu e00 e10 True by (simp add: Let_def)
    have lt: "(0::nat) < Suc (entry M 1 0 + ?j1) - entry M 1 0" by simp
    have "entry (Red M) 0 0 = entry M 1 0 + 0"
      using rM entry_diagSeq[OF lt, of 0] by simp
    thus ?thesis using e10 by simp
  next
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
      using Red.psimps[OF dom] nz nmu e00 e10 tne by (simp add: Let_def)
    have "entry (Red M) 0 0 = entry (diagSeq 0 ?j1' @ ?tail) 0 0" by (simp add: rM)
    also have "\<dots> = 0" by (rule entry_diagSeq_append_lo) simp
    finally show ?thesis .
  qed
qed

text \<open>FWD monoT-shift subcase is VACUOUS: there is no reduced \<open>monoT M\<close> with
  \<open>entry M 1 0 = 0\<close> and \<open>entry M 0 0 \<noteq> 0\<close>.  The \<open>Red\<close> \<open>m\<^sub>1\<^sub>0 = 0\<close> branch gives
  \<open>Red M = Red (shiftRow0 M)\<close>, and \<open>shiftRow0 M\<close> is \<open>monoT\<close> core
  (\<open>entry _ 0 0 = m\<^sub>0\<^sub>0 - m\<^sub>0\<^sub>0 = 0\<close>, \<open>entry _ 1 0 = m\<^sub>1\<^sub>0 = 0\<close>), so
  \<open>entry (Red M) 0 0 = entry (Red (shiftRow0 M)) 0 0 = 0\<close>
  (@{thm [source] kfwd_Red_core_leftend00}); but \<open>Red M = M\<close> forces this to be
  \<open>entry M 0 0 = m\<^sub>0\<^sub>0 \<noteq> 0\<close> — contradiction.  Empirically 0 such reduced
  sequences (\<open>python/_shift_check.py\<close>).\<close>

lemma kfwd_reduced_monoT_shift_vacuous:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and e10: "entry M 1 0 = 0" and e00: "entry M 0 0 \<noteq> 0"
  shows "False"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have redM: "Red M = M" using M by (simp add: RT_PS_def)
  have nz: "\<not> zeroT M" using mono by (simp add: monoT_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  have dom: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  let ?j1 = "Lng M - 1"
  have nc: "\<not> (entry M 0 0 = 0 \<and> entry M 1 0 = 0)" using e00 by simp
  \<comment> \<open>\<open>Red M = Red (shiftRow0 M)\<close>.\<close>
  let ?shift = "map (\<lambda>j. (entry M 0 j - entry M 0 0, entry M 1 j)) [0..<Suc ?j1]"
  have rM: "Red M = Red ?shift"
    using Red.psimps[OF dom] nz nmu nc e10 by (simp add: Let_def)
  have shift_eq: "?shift = shiftRow0 M"
    using LMpos by (simp add: shiftRow0_def)
  have shift_T: "shiftRow0 M \<in> T_PS"
    using MT by (simp add: T_PS_def shiftRow0_def)
  have shift_mono: "monoT (shiftRow0 M)" by (rule monoT_shiftRow0[OF MT mono])
  \<comment> \<open>\<open>shiftRow0 M\<close> is core.\<close>
  have s00: "entry (shiftRow0 M) 0 0 = 0"
    using entry_shiftRow0_0[of 0 M] LMpos by simp
  have s10: "entry (shiftRow0 M) 1 0 = 0"
    using entry_shiftRow0_1[of 0 M] LMpos e10 by simp
  \<comment> \<open>core leftend gives \<open>entry (Red (shiftRow0 M)) 0 0 = 0\<close>.\<close>
  have e0: "entry (Red (shiftRow0 M)) 0 0 = 0"
    by (rule kfwd_Red_core_leftend00[OF shift_T shift_mono s00 s10])
  have "entry M 0 0 = entry (Red M) 0 0" using redM by simp
  also have "\<dots> = entry (Red (shiftRow0 M)) 0 0" using rM shift_eq by simp
  also have "\<dots> = 0" using e0 .
  finally have "entry M 0 0 = 0" .
  thus False using e00 by simp
qed

text \<open>
  RESIDUAL (precise).  What remains for the full conjuncts (4),(5) is the
  \<open>c\<close>-equality \<open>c\<^sub>0 = c\<^sub>1\<close> for two kind-\<open>k\<close> scb-decompositions of a nonempty \<open>t\<close>.
  The article proves it (content.md 1900..1960) by the \<open>RightNodes\<close> spine
  argument, whose Isabelle bricks are ALREADY GREEN here:
  @{text rnsub_RightNodes_t0_lastv}, @{text rnsub_flat_pre_post},
  @{text rnsub_align_lastZ}, @{text rnsub_RightNodes_last},
  @{text rnsub_RightNodes_spineSub}.  The two missing links are
  (i) \<open>RightNodes c\<^sub>i\<close> is the length-\<open>(j\<^sub>1\<^sub>,\<^sub>i+1)\<close> SUFFIX segment of \<open>RightNodes t\<close>
  (so the kind condition pins \<open>j\<^sub>1\<^sub>,\<^sub>0 = j\<^sub>1\<^sub>,\<^sub>1\<close> and \<open>v\<^sub>0 = v\<^sub>1\<close>), and
  (ii) MAXIMALITY of \<open>c\<close> as a term substring.  Both are multi-lemma.
\<close>




section \<open>§6.6 keystone forward (monoT core): \<open>reduced \<Longrightarrow> RedCondA \<and> RedCondB\<close>\<close>

text \<open>Pred-lift helper.  When \<open>M \<in> T\<^bsub>PS\<^esub>\<close> and \<open>Pred M = butlast M\<close>, the two
  sequences agree on the closed prefix \<open>[0, Lng M - 2]\<close>, so \<open>nextR\<close> (both rows)
  transfers between \<open>M\<close> and \<open>Pred M\<close> for indices \<open>\<le> Lng M - 2\<close>.  This is the
  article's \<open>j'\<^sub>1 < j\<^sub>1\<close> witness-translation: a row-\<open>i\<close> Next-parent of a node
  strictly below the last column lives entirely inside \<open>Pred M\<close>.\<close>

lemma kfwd_pred_agree:
  assumes MT: "M \<in> T_PS" and L: "1 < Lng M"
  shows "\<And>j. j \<le> Lng M - 2 \<Longrightarrow> M ! j = Pred M ! j"
proof -
  fix j assume jle: "j \<le> Lng M - 2"
  have predbl: "Pred M = butlast M" using L by (simp add: Pred_def)
  have jlt: "j < Lng (butlast M)" using jle L by (simp add: length_butlast)
  show "M ! j = Pred M ! j" using predbl jlt by (simp add: nth_butlast)
qed

lemma kfwd_nextR_Pred_imp:
  assumes MT: "M \<in> T_PS" and L: "1 < Lng M"
    and i: "i \<le> 1"
    and xy: "x \<le> Lng M - 2" "y \<le> Lng M - 2"
    and h: "nextR M i x y"
  shows "nextR (Pred M) i x y"
proof -
  let ?c = "Lng M - 2"
  have predbl: "Pred M = butlast M" using L by (simp add: Pred_def)
  have LP: "Lng (Pred M) = Lng M - 1" using predbl by (simp add: length_butlast)
  have cM: "?c < Lng M" using L by linarith
  have cN: "?c < Lng (Pred M)" using LP L by linarith
  have agree: "\<And>k. k \<le> ?c \<Longrightarrow> M ! k = Pred M ! k" using kfwd_pred_agree[OF MT L] .
  show ?thesis
  proof (cases "i = 0")
    case True
    have h0: "nextrel0 M x y" using h True by (simp add: nextR_def)
    have "nextrel0 (Pred M) x y"
      by (rule nextrel0_prefix_imp[OF agree cN xy(1) xy(2) h0])
    thus ?thesis using True by (simp add: nextR_def)
  next
    case False
    hence i1: "i = 1" using i by simp
    have h1: "nextrel1 M x y" using h i1 by (simp add: nextR_def)
    have "nextrel1 (Pred M) x y"
      by (rule nextrel1_prefix_imp[OF agree cM cN xy(1) xy(2) h1])
    thus ?thesis using i1 by (simp add: nextR_def)
  qed
qed

lemma kfwd_nextR_Pred_rev:
  assumes MT: "M \<in> T_PS" and L: "1 < Lng M"
    and i: "i \<le> 1"
    and xy: "x \<le> Lng M - 2" "y \<le> Lng M - 2"
    and h: "nextR (Pred M) i x y"
  shows "nextR M i x y"
proof -
  let ?c = "Lng M - 2"
  have predbl: "Pred M = butlast M" using L by (simp add: Pred_def)
  have LP: "Lng (Pred M) = Lng M - 1" using predbl by (simp add: length_butlast)
  have cM: "?c < Lng M" using L by linarith
  have cN: "?c < Lng (Pred M)" using LP L by linarith
  have agree: "\<And>k. k \<le> ?c \<Longrightarrow> Pred M ! k = M ! k"
    using kfwd_pred_agree[OF MT L] by simp
  show ?thesis
  proof (cases "i = 0")
    case True
    have h0: "nextrel0 (Pred M) x y" using h True by (simp add: nextR_def)
    have "nextrel0 M x y"
      by (rule nextrel0_prefix_imp[OF agree cM xy(1) xy(2) h0])
    thus ?thesis using True by (simp add: nextR_def)
  next
    case False
    hence i1: "i = 1" using i by simp
    have h1: "nextrel1 (Pred M) x y" using h i1 by (simp add: nextR_def)
    have "nextrel1 M x y"
      by (rule nextrel1_prefix_imp[OF agree cN cM xy(1) xy(2) h1])
    thus ?thesis using i1 by (simp add: nextR_def)
  qed
qed

text \<open>\<open>hasParent\<close> and \<open>parent\<close> transfer between \<open>M\<close> and \<open>Pred M\<close> for a node
  strictly below the last column (\<open>j\<^sub>1' < Lng M - 1\<close>), i.e. \<open>j\<^sub>1' \<le> Lng M - 2\<close>.
  A row-\<open>i\<close> Next-parent is unique and \<open>< j\<^sub>1'\<close>, hence also \<open>\<le> Lng M - 2\<close>, so
  @{thm [source] kfwd_nextR_Pred_imp}/@{thm [source] kfwd_nextR_Pred_rev} apply
  both ways and the unique witness is preserved.\<close>

lemma kfwd_hasParent_Pred_iff:
  assumes MT: "M \<in> T_PS" and L: "1 < Lng M"
    and i: "i \<le> 1" and jle: "j1' \<le> Lng M - 2"
  shows "hasParent (Pred M) i j1' = hasParent M i j1'"
proof
  assume "hasParent (Pred M) i j1'"
  then obtain j0' where j0': "nextR (Pred M) i j0' j1'"
    and uq: "\<And>q. nextR (Pred M) i q j1' \<Longrightarrow> q = j0'"
    unfolding hasParent_def by blast
  have j0lt: "j0' < j1'" using j0' unfolding nextR_def nextrel0_def nextrel1_def
    by (auto split: if_splits)
  have j0le: "j0' \<le> Lng M - 2" using j0lt jle by linarith
  have nM: "nextR M i j0' j1'" by (rule kfwd_nextR_Pred_rev[OF MT L i j0le jle j0'])
  have uqM: "\<And>q. nextR M i q j1' \<Longrightarrow> q = j0'"
  proof -
    fix q assume nq: "nextR M i q j1'"
    have qlt: "q < j1'" using nq unfolding nextR_def nextrel0_def nextrel1_def
      by (auto split: if_splits)
    have qle: "q \<le> Lng M - 2" using qlt jle by linarith
    have "nextR (Pred M) i q j1'" by (rule kfwd_nextR_Pred_imp[OF MT L i qle jle nq])
    thus "q = j0'" by (rule uq)
  qed
  show "hasParent M i j1'" unfolding hasParent_def using nM uqM by blast
next
  assume "hasParent M i j1'"
  then obtain j0' where j0': "nextR M i j0' j1'"
    and uq: "\<And>q. nextR M i q j1' \<Longrightarrow> q = j0'"
    unfolding hasParent_def by blast
  have j0lt: "j0' < j1'" using j0' unfolding nextR_def nextrel0_def nextrel1_def
    by (auto split: if_splits)
  have j0le: "j0' \<le> Lng M - 2" using j0lt jle by linarith
  have nP: "nextR (Pred M) i j0' j1'" by (rule kfwd_nextR_Pred_imp[OF MT L i j0le jle j0'])
  have uqP: "\<And>q. nextR (Pred M) i q j1' \<Longrightarrow> q = j0'"
  proof -
    fix q assume nq: "nextR (Pred M) i q j1'"
    have qlt: "q < j1'" using nq unfolding nextR_def nextrel0_def nextrel1_def
      by (auto split: if_splits)
    have qle: "q \<le> Lng M - 2" using qlt jle by linarith
    have "nextR M i q j1'" by (rule kfwd_nextR_Pred_rev[OF MT L i qle jle nq])
    thus "q = j0'" by (rule uq)
  qed
  show "hasParent (Pred M) i j1'" unfolding hasParent_def using nP uqP by blast
qed

lemma kfwd_parent_Pred_eq:
  assumes MT: "M \<in> T_PS" and L: "1 < Lng M"
    and i: "i \<le> 1" and jle: "j1' \<le> Lng M - 2"
    and hp: "hasParent M i j1'"
  shows "parent (Pred M) i j1' = parent M i j1'"
proof -
  have hpP: "hasParent (Pred M) i j1'"
    using hp kfwd_hasParent_Pred_iff[OF MT L i jle] by simp
  obtain j0' where j0': "nextR M i j0' j1'"
    and uq: "\<And>q. nextR M i q j1' \<Longrightarrow> q = j0'"
    using hp unfolding hasParent_def by blast
  have pM: "parent M i j1' = j0'"
    unfolding parent_def using j0' uq by (blast intro: the1_equality)
  have j0lt: "j0' < j1'" using j0' unfolding nextR_def nextrel0_def nextrel1_def
    by (auto split: if_splits)
  have j0le: "j0' \<le> Lng M - 2" using j0lt jle by linarith
  have nP: "nextR (Pred M) i j0' j1'" by (rule kfwd_nextR_Pred_imp[OF MT L i j0le jle j0'])
  obtain p where p: "nextR (Pred M) i p j1'"
    and uqP: "\<And>q. nextR (Pred M) i q j1' \<Longrightarrow> q = p"
    using hpP unfolding hasParent_def by blast
  have pP: "parent (Pred M) i j1' = p"
    unfolding parent_def using p uqP by (blast intro: the1_equality)
  have "p = j0'" using nP uqP by blast
  thus ?thesis using pM pP by simp
qed

text \<open>Entries of \<open>M\<close> and \<open>Pred M\<close> agree below the last column.\<close>

lemma kfwd_entry_Pred_eq:
  assumes L: "1 < Lng M" and jle: "j \<le> Lng M - 2"
  shows "entry (Pred M) i j = entry M i j"
proof -
  have predbl: "Pred M = butlast M" using L by (simp add: Pred_def)
  have jlt: "j < Lng (butlast M)" using jle L by (simp add: length_butlast)
  show ?thesis using predbl jlt by (simp add: entry_def nth_butlast)
qed

text \<open>\<S>6.6 keystone forward, monoT-core last-column row-0 parent.  For a
  \<open>monoT M\<close> (so \<open>(0,0) \<le>\<^sub>M (0, Lng M - 1)\<close>) with \<open>Lng M > 1\<close> the last column
  \<open>Lng M - 1\<close> always has a (unique) row-0 Next-parent.  GREEN reusable brick:
  it discharges the last-column \<open>RedCondB\<close> witness of the keystone vacuously
  (a monoT last column is never row-0 parentless).\<close>

lemma kfwd_monoT_hasParent_top:
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and L: "1 < Lng M"
  shows "hasParent M 0 (Lng M - 1)"
proof -
  let ?j1 = "Lng M - 1"
  have le0j1: "leR M 0 0 ?j1" using mono by (simp add: monoT_def)
  have j1pos: "0 < ?j1" using L by linarith
  have e0lt: "entry M 0 0 < entry M 0 ?j1"
    by (rule m_5_1_ancestor_basic_1[OF MT j1pos order.refl le0j1])
  have "\<exists>j. 0 \<le> j \<and> j < ?j1 \<and> nextR M 0 j ?j1"
    by (rule m_5_1_parent_exists_1[OF MT j1pos _ e0lt]) (use L in linarith)
  hence "\<exists>j0. nextR M 0 j0 ?j1" by blast
  thus ?thesis unfolding hasParent_def using idxsum_ex1_parent0_iff by blast
qed

text \<open>Row-0 entries gain \<open>k\<close>; row-1 entries are unchanged.\<close>

lemma incf_pow_entry0:
  "j < Lng X \<Longrightarrow> entry ((IncrFirst ^^ k) X) 0 j = entry X 0 j + k"
proof (induction k)
  case 0
  thus ?case by simp
next
  case (Suc k)
  have jl: "j < Lng ((IncrFirst ^^ k) X)" using Suc.prems by simp
  have "entry ((IncrFirst ^^ Suc k) X) 0 j
          = entry (IncrFirst ((IncrFirst ^^ k) X)) 0 j" by (simp add: funpow_swap1)
  also have "\<dots> = Suc (entry ((IncrFirst ^^ k) X) 0 j)"
    using entry_IncrFirst[OF jl, of 0] by simp
  also have "\<dots> = Suc (entry X 0 j + k)" using Suc.IH[OF Suc.prems] by simp
  finally show ?case by simp
qed

lemma incf_pow_entry1:
  "j < Lng X \<Longrightarrow> entry ((IncrFirst ^^ k) X) 1 j = entry X 1 j"
proof (induction k)
  case 0
  thus ?case by simp
next
  case (Suc k)
  have jl: "j < Lng ((IncrFirst ^^ k) X)" using Suc.prems by simp
  have "entry ((IncrFirst ^^ Suc k) X) 1 j
          = entry (IncrFirst ((IncrFirst ^^ k) X)) 1 j" by (simp add: funpow_swap1)
  also have "\<dots> = entry ((IncrFirst ^^ k) X) 1 j"
    using entry_IncrFirst[OF jl, of 1] by simp
  also have "\<dots> = entry X 1 j" using Suc.IH[OF Suc.prems] by simp
  finally show ?case .
qed

text \<open>\<open>nextrel0\<close>/\<open>nextrel1\<close> are preserved as functions (single step iterated),
  hence so is \<open>nextR\<close> for rows \<open>\<le> 1\<close>.\<close>

lemma nextrel0_incf_pow_eq: "nextrel0 ((IncrFirst ^^ k) X) = nextrel0 X"
proof (induction k)
  case 0
  thus ?case by simp
next
  case (Suc k)
  have "(IncrFirst ^^ Suc k) X = IncrFirst ((IncrFirst ^^ k) X)"
    by (simp add: funpow_swap1)
  thus ?case by (simp add: nextrel0_IncrFirst_eq Suc.IH)
qed

lemma nextrel1_incf_pow_eq: "nextrel1 ((IncrFirst ^^ k) X) = nextrel1 X"
proof (induction k)
  case 0
  thus ?case by simp
next
  case (Suc k)
  have "(IncrFirst ^^ Suc k) X = IncrFirst ((IncrFirst ^^ k) X)"
    by (simp add: funpow_swap1)
  thus ?case by (simp add: nextrel1_IncrFirst_eq Suc.IH)
qed

lemma incf_pow_nextR:
  assumes "i \<le> 1"
  shows "nextR ((IncrFirst ^^ k) X) i a b = nextR X i a b"
proof (cases "i = 0")
  case True
  thus ?thesis by (simp add: nextR_def nextrel0_incf_pow_eq)
next
  case False
  hence "i = 1" using assms by simp
  thus ?thesis by (simp add: nextR_def nextrel1_incf_pow_eq)
qed

text \<open>\<open>hasParent\<close> and \<open>parent\<close> are defined purely from \<open>nextR\<close>, so they
  transfer once \<open>nextR\<close> is shown equal (rows \<open>\<le> 1\<close>).\<close>

lemma incf_pow_hasParent:
  assumes "i \<le> 1"
  shows "hasParent ((IncrFirst ^^ k) X) i j = hasParent X i j"
  unfolding hasParent_def by (simp add: incf_pow_nextR[OF assms])

lemma incf_pow_parent:
  assumes "i \<le> 1"
  shows "parent ((IncrFirst ^^ k) X) i j = parent X i j"
  unfolding parent_def by (simp add: incf_pow_nextR[OF assms])



section \<open>Front A (wf12) — keystone-forward last-block locate (STEP b)\<close>

text \<open>
  STEP (b): for a reduced \<open>monoT\<close> core \<open>M\<close> with \<open>M\<^sub>0 = (0,0)\<close> and
  \<open>TrMax M \<noteq> Lng M - 1\<close> (so \<open>M = Red M\<close> is nontrunk and \<open>Br M \<noteq> []\<close>), the
  @{thm [source] d_Red_core_nontrunk_unfold} decomposition
    \<open>Red M = diagSeq 0 (TrMax M) @ concat (map (\<lambda>J. (IncrFirst ^^ e\<^sub>J) (Red (NJ M J)))
                                              [0..<Lng (Br M)])\<close>
  has, as its LAST concat block, \<open>(IncrFirst ^^ e\<^bsub>J\<^esub>) (Red (NJ M J\<^sup>*))\<close> at
  \<open>J\<^sup>* = Lng (Br M) - 1\<close>; its left endpoint inside \<open>Red M\<close> is the offset
    \<open>off = Suc (TrMax M) + Lng (concat (map blk [0..<J\<^sup>*]))\<close>,
  and the suffix of \<open>Red M\<close> from \<open>off\<close> equals exactly that block.  Moreover the
  underlying single branch \<open>NJ M J\<^sup>*\<close> is STRICTLY shorter than \<open>M\<close>
  (\<open>Lng (NJ M J\<^sup>*) = Lng (Br M ! J\<^sup>*) \<le> Lng (concat (Br M)) = Lng M - 1 - TrMax M < Lng M\<close>).
  This pins the last column \<open>Lng M - 1\<close> inside the IncrFirst-shifted last block,
  the gateway to the \<open>condA_top\<close> witness-translation.\<close>

text \<open>The last block of a nonempty mapped-concat is a suffix at the cumulative
  offset of the earlier blocks.  Pure list algebra.\<close>
lemma concat_map_last_block_drop:
  assumes ne: "0 < n"
  shows "drop (Lng (concat (map g [0..<n-1]))) (concat (map g [0..<n]))
           = g (n-1)"
proof -
  have split: "[0..<n] = [0..<n-1] @ [n-1]"
    using ne by (metis Suc_diff_1 upt_Suc_append zero_le)
  have "concat (map g [0..<n]) = concat (map g [0..<n-1]) @ g (n-1)"
    by (subst split) simp
  thus ?thesis by simp
qed

lemma kfwd_lastblock_locate:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
  defines "blk \<equiv> (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J)))"
  defines "Jstar \<equiv> Lng (Br M) - 1"
  defines "off \<equiv> Suc (TrMax M) + Lng (concat (map blk [0..<Jstar]))"
  shows "drop off (Red M) = blk Jstar
       \<and> blk Jstar = (IncrFirst ^^ (Joints M ! Jstar + 1 - npJ M Jstar)) (Red (NJ M Jstar))
       \<and> Lng (NJ M Jstar) = Lng (Br M ! Jstar)
       \<and> Lng (NJ M Jstar) < Lng M
       \<and> Lng (Br M) \<noteq> 0"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have redM: "Red M = M" using M by (simp add: RT_PS_def)
  have nz: "\<not> zeroT M" using mono by (simp add: monoT_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  have Mpt: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  \<comment> \<open>\<open>Br M \<noteq> []\<close> from nontrunk.\<close>
  have brne: "Br M \<noteq> []" using tne P_nonempty by (simp add: Br_def)
  hence nBpos: "0 < Lng (Br M)" by (cases "Br M") auto
  have nBne: "Lng (Br M) \<noteq> 0" using nBpos by simp
  have JstarBr: "Jstar < Lng (Br M)" unfolding Jstar_def using nBpos by simp
  \<comment> \<open>Nontrunk unfold of \<open>Red M\<close>.\<close>
  have rM: "Red M = diagSeq 0 (TrMax M) @ concat (map blk [0..<Lng (Br M)])"
    unfolding blk_def by (rule d_Red_core_nontrunk_unfold[OF MT nz nmu e00 e10 tne])
  \<comment> \<open>Length of the diagonal prefix.\<close>
  have ldiag: "Lng (diagSeq 0 (TrMax M)) = Suc (TrMax M)" by simp
  \<comment> \<open>Drop the diagonal prefix; then the last concat block is a suffix.\<close>
  have drop_pre: "drop (Suc (TrMax M)) (Red M) = concat (map blk [0..<Lng (Br M)])"
    by (simp add: rM ldiag)
  have last_blk: "drop (Lng (concat (map blk [0..<Jstar])))
                       (concat (map blk [0..<Lng (Br M)])) = blk Jstar"
    using concat_map_last_block_drop[OF nBpos] unfolding Jstar_def by simp
  have drop_off: "drop off (Red M) = blk Jstar"
  proof -
    have "drop off (Red M)
            = drop (Lng (concat (map blk [0..<Jstar])))
                   (drop (Suc (TrMax M)) (Red M))"
      unfolding off_def by (simp add: add.commute)
    also have "\<dots> = drop (Lng (concat (map blk [0..<Jstar])))
                         (concat (map blk [0..<Lng (Br M)]))"
      by (simp add: drop_pre)
    also have "\<dots> = blk Jstar" by (rule last_blk)
    finally show ?thesis .
  qed
  \<comment> \<open>Block identity (definitional).\<close>
  have blk_id: "blk Jstar
        = (IncrFirst ^^ (Joints M ! Jstar + 1 - npJ M Jstar)) (Red (NJ M Jstar))"
    unfolding blk_def ..
  \<comment> \<open>\<open>Lng (NJ M J\<^sup>*) = Lng (Br M ! J\<^sup>*)\<close>.\<close>
  have brJne: "Br M ! Jstar \<noteq> []" by (rule Br_component_nonempty[OF Mpt JstarBr])
  have lenNJ: "Lng (NJ M Jstar) = Lng (Br M ! Jstar)" using brJne by (rule Lng_NJ)
  \<comment> \<open>Strict length bound: the single branch sits inside \<open>concat (Br M)\<close>, of total
     length \<open>Lng M - 1 - TrMax M < Lng M\<close>.\<close>
  have trlt: "TrMax M < Lng M - 1"
    using TrMax_bound[OF MT] tne LMpos by linarith
  have memBr: "Lng (Br M ! Jstar) \<in> set (map Lng (Br M))"
    using JstarBr by (simp add: nth_mem)
  have br_in_concat: "Lng (Br M ! Jstar) \<le> Lng (concat (Br M))"
  proof -
    have "Lng (Br M ! Jstar) \<le> sum_list (map Lng (Br M))"
      by (rule member_le_sum_list[OF memBr]) simp
    thus ?thesis by (simp add: length_concat)
  qed
  have concat_Br: "Lng (concat (Br M)) = Lng (seg M (TrMax M + 1) (Lng M - 1))"
    using trlt by (simp add: Br_def poper_concat_P)
  have "Lng (seg M (TrMax M + 1) (Lng M - 1)) = Suc (Lng M - 1) - (TrMax M + 1)"
    by (simp only: Lng_seg)
  also have "\<dots> = Lng M - 1 - TrMax M" using LMpos by simp
  finally have lseg: "Lng (seg M (TrMax M + 1) (Lng M - 1)) = Lng M - 1 - TrMax M" .
  have brlt: "Lng (Br M ! Jstar) < Lng M"
    using br_in_concat concat_Br lseg LMpos by linarith
  have NJlt: "Lng (NJ M Jstar) < Lng M" using lenNJ brlt by simp
  show ?thesis using drop_off blk_id lenNJ NJlt nBne by blast
qed


section \<open>Front A (wf13) — keystone forward monoT core, full \<open>Lng\<close>-induction (Ncons)\<close>

text \<open>Diagonal-prefix entry: for a reduced \<open>monoT\<close> core \<open>M\<close> (\<open>M\<^sub>0 = (0,0)\<close>) on the
  core-NONTRUNK branch, the first \<open>Suc (TrMax M)\<close> columns of \<open>M = Red M\<close> are the
  diagonal: \<open>entry M i p = p\<close> for \<open>p \<le> TrMax M\<close> and \<open>i \<le> 1\<close>.  Read off from
  @{thm [source] d_Red_core_nontrunk_unfold} (\<open>M = diagSeq 0 (TrMax M) @ tail\<close>)
  via @{thm [source] entry_diagSeq_append_lo}.\<close>

lemma ncons_diag_prefix_entry:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
    and ple: "p \<le> TrMax M"
  shows "entry M i p = p"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have redM: "Red M = M" using M by (simp add: RT_PS_def)
  have nz: "\<not> zeroT M" using mono by (simp add: monoT_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  have rM: "Red M = diagSeq 0 (TrMax M)
             @ concat (map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J))
                                    (Red (NJ M J)))
                       [0..<Lng (Br M)])"
    by (rule d_Red_core_nontrunk_unfold[OF MT nz nmu e00 e10 tne])
  have "entry M i p = entry (diagSeq 0 (TrMax M)
             @ concat (map (\<lambda>J. (IncrFirst ^^ (Joints M ! J + 1 - npJ M J))
                                    (Red (NJ M J)))
                       [0..<Lng (Br M)])) i p"
    using rM redM by simp
  also have "\<dots> = p" by (rule entry_diagSeq_append_lo[OF ple])
  finally show ?thesis .
qed

text \<open>\<open>Pred M\<close> of a reduced \<open>monoT\<close> core on the NONTRUNK branch is again a reduced
  \<open>monoT\<close> core, strictly shorter.  \<open>Pred M = seg M 0 (Lng M - 2)\<close>, and nontrunk
  means \<open>TrMax M \<le> Lng M - 2\<close>, so @{thm [source] herd_6_6_reduced_slice} gives
  reducedness, @{thm [source] m_6_2_mono_prefix} gives \<open>monoT\<close>, the left ends
  inherit, and the length drops.\<close>

lemma ncons_Pred_core:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1" and L3: "2 < Lng M"
  shows "Pred M \<in> RT_PS \<and> monoT (Pred M)
           \<and> entry (Pred M) 0 0 = 0 \<and> entry (Pred M) 1 0 = 0
           \<and> Lng (Pred M) < Lng M \<and> Pred M = seg M 0 (Lng M - 2)"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have Mpt: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  have trlt: "TrMax M < Lng M - 1" using TrMax_bound[OF MT] tne by linarith
  have L2: "1 < Lng M" using trlt LMpos by linarith
  \<comment> \<open>\<open>Pred M = seg M 0 (Lng M - 2)\<close>.\<close>
  have predbl: "Pred M = butlast M" using L2 by (simp add: Pred_def)
  have predtake: "Pred M = take (Lng M - 1) M"
    using L2 by (simp add: Pred_def butlast_conv_take)
  have segtake: "seg M 0 (Lng M - 2) = take (Suc (Lng M - 2)) M"
    by (rule seg_0_eq_take) (use L2 in linarith)
  have suceq: "Suc (Lng M - 2) = Lng M - 1" using L2 by linarith
  have segeq: "Pred M = seg M 0 (Lng M - 2)"
    using predtake segtake suceq by simp
  \<comment> \<open>reduced (slice heredity), with \<open>TrMax M \<le> Lng M - 2\<close>.\<close>
  have tle: "TrMax M \<le> Lng M - 2" using trlt by linarith
  have hi: "Lng M - 2 \<le> Lng M - 1" by simp
  have predRT: "Pred M \<in> RT_PS"
    using herd_6_6_reduced_slice[OF M refl tle hi] segeq by simp
  \<comment> \<open>monoT (needs \<open>0 < Lng M - 2\<close>, i.e. \<open>2 < Lng M\<close>).\<close>
  have predmono: "monoT (Pred M)"
  proof -
    have "monoT (seg M 0 (Lng M - 2))"
      by (rule m_6_2_mono_prefix[OF Mpt _ _]) (use L3 in linarith)+
    thus ?thesis using segeq by simp
  qed
  \<comment> \<open>left-end values inherit.\<close>
  have LP: "Lng (Pred M) = Lng M - 1" using predbl by (simp add: length_butlast)
  have z2: "(0::nat) \<le> Lng M - 2" by simp
  have es00: "entry (Pred M) 0 0 = 0"
    using kfwd_entry_Pred_eq[OF L2 z2, where i=0] e00 by simp
  have es10: "entry (Pred M) 1 0 = 0"
    using kfwd_entry_Pred_eq[OF L2 z2, where i=1] e10 by simp
  have Llt: "Lng (Pred M) < Lng M" using LP LMpos L2 by linarith
  show ?thesis using predRT predmono es00 es10 Llt segeq by blast
qed

end
