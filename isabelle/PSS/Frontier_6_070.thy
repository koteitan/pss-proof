theory Frontier_6_070
  imports Support_6_049
begin

(* ======================================================================
   Front A: §6.6 KEYSTONE BACKWARD core per-branch Y-bundle (tag pss-fa-ybundle)
   ====================================================================== *)

text \<open>\<S>6.6 Front A helper: \<open>RedCondA\<close> is inherited by any \<open>M\<close>-slice \<open>seg M a b\<close>
  with \<open>b < Lng M\<close>.  \<open>RedCondA\<close> constrains only parent-bearing nodes; a slice
  node with a parent IN the slice has, through the \<open>nextR\<close> slice bridge
  @{thm [source] rcpb_nextR_seg}, the offset-shifted parent in \<open>M\<close> with the same
  \<open>+1\<close> row-\<open>i\<close> identity (entries shift by \<open>a\<close>, @{thm [source] entry_seg}).  Cuts of
  trunk parents only DROP constraints, so the slice keeps \<open>RedCondA\<close>.\<close>

lemma fa_RedCondA_seg:
  assumes MT: "M \<in> T_PS" and segT: "seg M a b \<in> T_PS"
    and bL: "b < Lng M" and condA: "RedCondA M"
  shows "RedCondA (seg M a b)"
  unfolding RedCondA_def
proof (intro allI impI)
  fix i jl assume i: "i \<le> (1::nat)" and hp: "hasParent (seg M a b) i jl"
  let ?S = "seg M a b"
  have ex1: "\<exists>!pl. nextR ?S i pl jl" using hp by (simp add: hasParent_def)
  then obtain pl0 where pl0: "nextR ?S i pl0 jl"
    and uS: "\<And>pl'. nextR ?S i pl' jl \<Longrightarrow> pl' = pl0" by blast
  have jlS: "jl < Lng ?S" and plS: "pl0 < Lng ?S" and plj: "pl0 < jl"
    using pl0 by (cases "i = 0"; simp_all add: nextR_def nextrel0_def nextrel1_def)+
  have pS: "parent ?S i jl = pl0"
    unfolding parent_def
    by (rule the_equality[where P="\<lambda>pl. nextR ?S i pl jl", OF pl0 uS])
  \<comment> \<open>slice parent corresponds to an \<open>M\<close>-parent at the offset.\<close>
  have nM: "nextR M i (a + pl0) (a + jl)"
    using rcpb_nextR_seg[OF bL i plS jlS] pl0 by simp
  \<comment> \<open>uniqueness of the \<open>M\<close>-parent of \<open>a + jl\<close>: row-0/row-1 parents are GLOBALLY
     unique in \<open>M\<close> (@{thm [source] idxsum_parent0_unique} / @{thm [source] nextR1_unique}),
     so any \<open>M\<close>-parent equals the in-slice one \<open>a + pl0\<close>.\<close>
  have uniqM: "\<And>p'. nextR M i p' (a + jl) \<Longrightarrow> p' = a + pl0"
  proof -
    fix p' assume Hp: "nextR M i p' (a + jl)"
    show "p' = a + pl0"
    proof (cases "i = 0")
      case True
      have h0: "nextR M 0 p' (a + jl)" using Hp True by simp
      have n0: "nextR M 0 (a + pl0) (a + jl)" using nM True by simp
      show ?thesis by (rule idxsum_parent0_unique[OF h0 n0])
    next
      case False
      hence i1: "i = 1" using i by simp
      have h1: "nextR M 1 p' (a + jl)" using Hp i1 by simp
      have n1: "nextR M 1 (a + pl0) (a + jl)" using nM i1 by simp
      show ?thesis by (rule nextR1_unique[OF h1 n1])
    qed
  qed
  have pM: "parent M i (a + jl) = a + pl0"
    unfolding parent_def
    by (rule the_equality[where P="\<lambda>p. nextR M i p (a + jl)", OF nM uniqM])
  have hpM: "hasParent M i (a + jl)"
    unfolding hasParent_def using nM uniqM by blast
  have baseM: "entry M i (parent M i (a + jl)) + 1 = entry M i (a + jl)"
    using condA i hpM unfolding RedCondA_def by blast
  \<comment> \<open>transfer back to slice entries.\<close>
  have e_par: "entry ?S i (parent ?S i jl) = entry M i (a + pl0)"
    using pS plS by (simp add: entry_seg)
  have e_jl: "entry ?S i jl = entry M i (a + jl)"
    using jlS by (simp add: entry_seg)
  show "entry ?S i (parent ?S i jl) + 1 = entry ?S i jl"
    using e_par e_jl baseM pM by simp
qed



text \<open>\<S>6.6 Front A helper: in a NONMULTI (monoT or zeroT) sequence \<open>X\<close>, every
  column \<open>k > 0\<close> HAS a row-0 parent; equivalently the only row-0 parentless column
  is the root \<open>k = 0\<close>.  For monoT \<open>X\<close> the root is the strict row-0 minimum
  (@{thm [source] monoT_row0_min}), so \<open>entry X 0 0 < entry X 0 k\<close>, which (via
  @{thm [source] idxsum_no_parent0_iff}, using \<open>j = 0\<close>) forces a row-0 parent.
  zeroT \<open>X\<close> has length 1, so no \<open>k > 0\<close> exists.\<close>

lemma fa_nonmulti_par0_pos:
  assumes XT: "X \<in> T_PS" and nm: "\<not> multiT X"
    and k: "0 < k" "k < Lng X"
  shows "hasParent X 0 k"
proof -
  have nz_or_mono: "monoT X" using nm k XT
  proof -
    have "\<not> zeroT X" using k(1,2) by (auto simp: zeroT_def)
    thus "monoT X" using nm by (simp add: monoT_def multiT_def)
  qed
  have rootlt: "entry X 0 0 < entry X 0 k"
    by (rule monoT_row0_min[OF XT nz_or_mono k(1) k(2)])
  show ?thesis
  proof (rule ccontr)
    assume "\<not> hasParent X 0 k"
    hence "\<not> (\<exists>!j0. nextR X 0 j0 k)" by (simp add: hasParent_def)
    hence allge: "\<forall>j<k. entry X 0 j \<ge> entry X 0 k"
      using idxsum_no_parent0_iff[OF XT k(2)] by simp
    have "entry X 0 0 \<ge> entry X 0 k" using allge k(1) by simp
    thus False using rootlt by simp
  qed
qed



text \<open>\<S>6.6 Front A helper: \<open>RedCondA\<close> alone is inherited by each \<open>P\<close>-block
  (the \<open>RedCondA\<close> half of @{thm [source] m_6_6_RedCond_P_block}, NOT needing
  \<open>RedCondB\<close> nor \<open>multiT\<close>).  A block is the slice \<open>seg M a (a+L-1)\<close>
  (@{thm [source] rcpb_block_eq}); an in-block parent edge shifts to an
  \<open>M\<close>-parent edge with the same \<open>+1\<close> row-\<open>i\<close> identity
  (@{thm [source] rcpb_hasParent_iff}, @{thm [source] entry_seg}).\<close>

lemma fa_RedCondA_P_block:
  assumes M: "M \<in> T_PS" and condA: "RedCondA M"
    and JL: "J < length (P M)"
  shows "RedCondA (P M ! J)"
  unfolding RedCondA_def
proof (intro allI impI)
  fix i jl assume i: "i \<le> 1" and hp: "hasParent (P M ! J) i jl"
  let ?B = "P M ! J"
  let ?a = "IdxSum (P M) ! J"
  let ?L = "Lng ?B"
  have be: "?B = seg M ?a (?a + ?L - 1)" and Lpos: "0 < ?L"
    and blt: "?a + ?L - 1 < Lng M"
    using rcpb_block_eq[OF M JL] by auto
  have eB: "\<And>i j. j < ?L \<Longrightarrow> entry ?B i j = entry M i (?a + j)"
  proof -
    fix i j assume jL: "j < ?L"
    have jseg: "j < Lng (seg M ?a (?a + ?L - 1))" using jL be by simp
    have "entry (seg M ?a (?a + ?L - 1)) i j = entry M i (?a + j)"
      by (rule entry_seg[OF jseg])
    thus "entry ?B i j = entry M i (?a + j)" using be by simp
  qed
  show "entry ?B i (parent ?B i jl) + 1 = entry ?B i jl"
  proof (cases "jl < ?L")
    case True
    have hpM: "hasParent M i (?a + jl)"
      using rcpb_hasParent_iff(1)[OF M JL i True] hp by simp
    have pval: "?a + parent ?B i jl = parent M i (?a + jl)"
      using rcpb_hasParent_iff(2)[OF M JL i True] hp by simp
    have ex1: "\<exists>!pl. nextR ?B i pl jl" using hp by (simp add: hasParent_def)
    then obtain pl0 where pl0: "nextR ?B i pl0 jl"
      and uB: "\<And>pl'. nextR ?B i pl' jl \<Longrightarrow> pl' = pl0" by blast
    have plj: "pl0 < jl"
      using pl0 by (cases "i = 0") (auto simp: nextR_def nextrel0_def nextrel1_def)
    have pB: "parent ?B i jl = pl0"
      unfolding parent_def
      by (rule the_equality[where P="\<lambda>pl. nextR ?B i pl jl", OF pl0 uB])
    have plL: "parent ?B i jl < ?L" using pB plj True by simp
    have "entry M i (parent M i (?a + jl)) + 1 = entry M i (?a + jl)"
      using condA hpM i unfolding RedCondA_def by blast
    hence "entry M i (?a + parent ?B i jl) + 1 = entry M i (?a + jl)"
      using pval by simp
    thus ?thesis using eB[OF plL] eB[OF True] by simp
  next
    case False
    have "\<not> nextR ?B i pl jl" for pl
    proof
      assume "nextR ?B i pl jl"
      hence "jl < ?L" by (cases "i = 0") (auto simp: nextR_def nextrel0_def nextrel1_def)
      thus False using False by simp
    qed
    hence "\<not> hasParent ?B i jl" by (auto simp: hasParent_def)
    thus ?thesis using hp by simp
  qed
qed


text \<open>\<S>6.6 Front A: the per-branch Y-bundle FACTS for the core keystone backward
  (tag pss-fa-ybundle).  For a core-nontrunk A&B \<open>M\<close> and a branch index
  \<open>J < Lng (Br M)\<close>, with \<open>X = N\<^sub>J M J\<close>, \<open>e = m\<^sub>0\<^sub>0(X) - m\<^sub>1\<^sub>0(X)\<close> and
  \<open>Y = rebaseRow0 e 0 X\<close>, the bundle gives: \<open>X \<in> T_PS\<close>, \<open>\<not> multiT X\<close>, the
  row-1 \<open>\<le>\<close> row-0 head order, the row-0 lower bound, \<open>RedCondA X\<close>, \<open>RedCondA Y\<close>,
  \<open>RedCondB Y\<close>, \<open>m\<^sub>0\<^sub>0(Y) = m\<^sub>1\<^sub>0(Y)\<close>, \<open>\<not> multiT Y\<close>, and \<open>nu Y < nu M\<close>.

  Mechanism.  \<open>X = Br M ! J\<close> (@{thm [source] kst_bwdcore_NJ_eq_Br}); \<open>Br M = P S\<close>
  for the branch slice \<open>S = seg M (TrMax M+1)(Lng M-1)\<close>, so \<open>X = P S ! J\<close> inherits
  \<open>RedCondA\<close> from \<open>S\<close> (@{thm [source] fa_RedCondA_P_block}) which inherits it from
  \<open>M\<close> (@{thm [source] fa_RedCondA_seg}).  The head order \<open>m\<^sub>1\<^sub>0(X) \<le> m\<^sub>0\<^sub>0(X)\<close> is
  \<open>npJ M J \<le> Joints M!J + 1\<close> (@{thm [source] npJ_le_Joints_Suc}) for a core \<open>M\<close>.
  The row-0 lb is \<open>e \<le> m\<^sub>0\<^sub>0(X) \<le> entry X 0 j\<close> (@{thm [source] entry0_ge_min}).
  \<open>RedCondA Y\<close> = @{thm [source] RedCondA_rebaseRow0}; \<open>m\<^sub>0\<^sub>0(Y) = m\<^sub>1\<^sub>0(Y)\<close> is the
  rebase head algebra; \<open>\<not> multiT Y\<close> from \<open>\<not> multiT X\<close> (rebase preserves
  mono/zero).  \<open>RedCondB Y\<close>: the ONLY row-0-parentless column of a NONMULTI
  sequence is the root (@{thm [source] fa_nonmulti_par0_pos}), where
  \<open>m\<^sub>0\<^sub>0(Y) = m\<^sub>1\<^sub>0(Y)\<close>.  \<open>nu Y < nu M\<close>: \<open>nu\<close> of a nonmulti sequence is bounded by
  \<open>2\<beta>+1 \<le> 2 Lng X - 1\<close> via @{thm [source] betaM_coreReduce_le}, and
  \<open>Lng X \<le> betaM M - 1\<close> (as in @{thm [source] nu_NJ_lt}), so \<open>nu Y \<le> 2 betaM M - 1
  < 2 betaM M = nu M\<close>.  All citations GREEN; no \<open>p_*\<close> stub, no self-reference.\<close>

lemma fa_NJ_Y_facts:
  assumes MT: "M \<in> T_PS" and mono: "monoT M"
    and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and condA: "RedCondA M" and condB: "RedCondB M"
    and tne: "TrMax M \<noteq> Lng M - 1"
    and JBr: "J < Lng (Br M)"
  defines "e \<equiv> entry (NJ M J) 0 0 - entry (NJ M J) 1 0"
  defines "Y \<equiv> rebaseRow0 e 0 (NJ M J)"
  shows "NJ M J \<in> T_PS \<and> \<not> multiT (NJ M J)
         \<and> entry (NJ M J) 1 0 \<le> entry (NJ M J) 0 0
         \<and> (\<forall>j < Lng (NJ M J). e \<le> entry (NJ M J) 0 j)
         \<and> RedCondA (NJ M J)
         \<and> RedCondA Y \<and> RedCondB Y \<and> entry Y 0 0 = entry Y 1 0
         \<and> \<not> multiT Y \<and> nu Y < nu M"
proof -
  let ?X = "NJ M J"
  have M_PT: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  \<comment> \<open>branch slice and its decomposition\<close>
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  have trlt: "TrMax M < Lng M - 1" using tne TrMax_bound[OF MT] LMpos by linarith
  let ?S = "seg M (TrMax M + 1) (Lng M - 1)"
  have brQ: "Br M = P ?S" using tne by (simp add: Br_def)
  have SL: "0 < Lng ?S" using trlt LMpos by (simp add: Lng_seg)
  have Sne: "?S \<noteq> []" using SL by (metis length_greater_0_conv)
  have ST: "?S \<in> T_PS" using Sne by (simp add: T_PS_def)
  have bL: "Lng M - 1 < Lng M" using LMpos by linarith
  have JL: "J < length (P ?S)" using JBr brQ by simp
  \<comment> \<open>\<open>X = Br M ! J = P S ! J\<close>\<close>
  have XeqBr: "?X = Br M ! J" by (rule kst_bwdcore_NJ_eq_Br[OF MT mono c0 c1 condA tne JBr])
  have XeqPS: "?X = P ?S ! J" using XeqBr brQ by simp
  have brJne: "Br M ! J \<noteq> []" by (rule Br_component_nonempty[OF M_PT JBr])
  have XT: "?X \<in> T_PS" using brJne XeqBr by (simp add: T_PS_def)
  have Xnm: "\<not> multiT ?X" by (rule NJ_nonmulti[OF M_PT c0 c1 JBr])
  have Xne: "?X \<noteq> []" using XT by (simp add: T_PS_def)
  have LX: "0 < Lng ?X" using Xne by (cases ?X) auto
  \<comment> \<open>RedCondA on the branch block\<close>
  have condAS: "RedCondA ?S" by (rule fa_RedCondA_seg[OF MT ST bL condA])
  have condAX: "RedCondA ?X" using XeqPS fa_RedCondA_P_block[OF ST condAS JL] by simp
  \<comment> \<open>head order \<open>m\<^sub>1\<^sub>0(X) \<le> m\<^sub>0\<^sub>0(X)\<close>\<close>
  have e00: "entry ?X 0 0 = Joints M ! J + 1" using entry_NJ_0_0[of M J] c0 by simp
  have e10: "entry ?X 1 0 = npJ M J" using entry_NJ_1_0[of M J] c1 by simp
  have nple: "npJ M J \<le> Joints M ! J + 1" by (rule npJ_le_Joints_Suc[OF M_PT c1 JBr])
  have headord: "entry ?X 1 0 \<le> entry ?X 0 0" using e00 e10 nple by simp
  \<comment> \<open>\<open>X\<close> is nonmulti: monoT or zeroT; either way row0 has the root as minimum\<close>
  have Xmz: "zeroT ?X \<or> monoT ?X" using Xnm LX by (auto simp: multiT_def)
  have row0min: "\<And>j. j < Lng ?X \<Longrightarrow> entry ?X 0 0 \<le> entry ?X 0 j"
  proof -
    fix j assume jL: "j < Lng ?X"
    show "entry ?X 0 0 \<le> entry ?X 0 j"
    proof (cases "zeroT ?X")
      case True hence "Lng ?X = 1" by (simp add: zeroT_def)
      hence "j = 0" using jL by simp
      thus ?thesis by simp
    next
      case False hence mo: "monoT ?X" using Xmz by simp
      show ?thesis by (rule entry0_ge_min[OF XT mo jL])
    qed
  qed
  \<comment> \<open>row-0 lower bound: \<open>e \<le> m\<^sub>0\<^sub>0(X) \<le> entry X 0 j\<close>\<close>
  have lb: "\<And>j. j < Lng ?X \<Longrightarrow> e \<le> entry ?X 0 j"
  proof -
    fix j assume jL: "j < Lng ?X"
    have "e \<le> entry ?X 0 0" using e_def by simp
    also have "\<dots> \<le> entry ?X 0 j" by (rule row0min[OF jL])
    finally show "e \<le> entry ?X 0 j" .
  qed
  \<comment> \<open>\<open>Y\<close> facts\<close>
  have YeqL: "Lng Y = Lng ?X" using Y_def by simp
  have YA: "RedCondA Y" using Y_def RedCondA_rebaseRow0[OF lb condAX] by simp
  \<comment> \<open>\<open>m\<^sub>0\<^sub>0(Y) = m\<^sub>1\<^sub>0(Y)\<close>\<close>
  have eY00: "entry Y 0 0 = entry ?X 0 0 - e"
    using Y_def entry_rebaseRow0_0[OF LX, of e 0] by simp
  have eY10: "entry Y 1 0 = entry ?X 1 0"
    using Y_def entry_rebaseRow0_1[OF LX, of e 0] by simp
  have Yeq: "entry Y 0 0 = entry Y 1 0"
    using eY00 eY10 headord e_def by simp
  \<comment> \<open>\<open>Y\<close> nonmulti (rebase preserves mono / zero)\<close>
  have Ynm: "\<not> multiT Y"
  proof (cases "zeroT ?X")
    case True
    have "Lng Y = 1" using YeqL True by (simp add: zeroT_def)
    moreover have "entry Y 1 0 = 0" using eY10 True by (simp add: zeroT_def)
    ultimately have "zeroT Y" by (simp add: zeroT_def)
    thus ?thesis by (simp add: multiT_def)
  next
    case False
    hence mo: "monoT ?X" using Xmz by simp
    have "monoT Y" using Y_def monoT_rebaseRow0[OF lb mo] by simp
    thus ?thesis by (simp add: multiT_def)
  qed
  have Yne: "Y \<noteq> []" using YeqL LX by (metis length_greater_0_conv)
  have YT: "Y \<in> T_PS" using Yne by (simp add: T_PS_def)
  \<comment> \<open>\<open>RedCondB Y\<close>: only the root is row-0-parentless, and there \<open>m\<^sub>0\<^sub>0(Y) = m\<^sub>1\<^sub>0(Y)\<close>\<close>
  have YB: "RedCondB Y"
    unfolding RedCondB_def
  proof (intro allI impI)
    fix k assume hyp: "\<not> hasParent Y 0 k \<and> k \<le> Lng Y - 1"
    have nhp: "\<not> hasParent Y 0 k" and kle: "k \<le> Lng Y - 1" using hyp by simp_all
    have kL: "k < Lng Y" using kle YeqL LX by linarith
    have k0: "k = 0"
    proof (rule ccontr)
      assume "k \<noteq> 0" hence kpos: "0 < k" by simp
      have "hasParent Y 0 k" by (rule fa_nonmulti_par0_pos[OF YT Ynm kpos kL])
      thus False using nhp by simp
    qed
    show "entry Y 0 k = entry Y 1 k" using k0 Yeq by simp
  qed
  \<comment> \<open>\<open>nu Y < nu M\<close>: \<open>nu M = 2 betaM M\<close>; \<open>nu Y \<le> 2 Lng X - 1 \<le> 2 betaM M - 1\<close>.\<close>
  have nmM: "\<not> multiT M" using mono by (simp add: multiT_def)
  have nuM: "nu M = 2 * betaM M" using nmM c0 c1 by (simp add: nu_def muMono_def)
  have bpos: "1 \<le> betaM M" by (rule betaM_pos[OF MT])
  have lenNJ: "Lng ?X = Lng (Br M ! J)" using XeqBr by simp
  have brbound: "Lng (Br M ! J) \<le> Lng M - TrMax M - 1" by (rule Lng_Br_le[OF JBr])
  have LXbound: "Lng ?X \<le> betaM M - 1" using lenNJ brbound by (simp add: betaM_def)
  \<comment> \<open>\<open>nu Y \<le> 2 Lng Y\<close> for a nonmulti \<open>Y\<close> (core: \<open>2\<beta> \<le> 2 Lng\<close>; noncore: \<open>2\<beta>(cr)+1\<close>,
     and \<open>\<beta>(coreReduce Y) \<le> Lng Y\<close> so \<open>\<le> 2 Lng Y\<close> too when \<open>Lng Y \<ge> 1\<close>).\<close>
  have LYpos: "0 < Lng Y" using YeqL LX by simp
  have nuYle: "nu Y \<le> 2 * Lng Y + 1"
  proof (cases "entry Y 0 0 = 0 \<and> entry Y 1 0 = 0")
    case True
    have muY: "muMono Y = 2 * betaM Y"
      unfolding muMono_def by (rule if_P[OF True])
    have ble: "betaM Y \<le> Lng Y" by (simp add: betaM_def)
    have "nu Y = muMono Y" using Ynm by (simp add: nu_def)
    hence "nu Y = 2 * betaM Y" using muY by simp
    thus ?thesis using ble by simp
  next
    case False
    have muY: "muMono Y = 2 * betaM (coreReduce Y) + 1"
      unfolding muMono_def by (rule if_not_P[OF False])
    have crle: "betaM (coreReduce Y) \<le> Lng Y" by (rule betaM_coreReduce_le[OF YT])
    have "nu Y = muMono Y" using Ynm by (simp add: nu_def)
    hence "nu Y = 2 * betaM (coreReduce Y) + 1" using muY by simp
    thus ?thesis using crle by simp
  qed
  have nuYlt: "nu Y < nu M"
  proof -
    have "nu Y \<le> 2 * Lng ?X + 1" using nuYle YeqL by simp
    thus ?thesis using LXbound nuM bpos by linarith
  qed
  \<comment> \<open>assemble\<close>
  show ?thesis
    using XT Xnm headord lb condAX YA YB Yeq Ynm nuYlt by blast
qed



text \<open>\<S>6.6 KEYSTONE BACKWARD monoT-core, UNCONDITIONAL (Front A, tag pss-fa-core).
  Proves \<open>Red M\<^sub>0 = M\<^sub>0\<close> for every monoT-core A&B \<open>M\<^sub>0\<close>, by \<open>nu\<close>-induction.  Per
  branch \<open>J\<close>, the G-obligation
    \<open>(IncrFirst ^^ e) (Red (N\<^sub>J M J)) = N\<^sub>J M J\<close>,  \<open>e = m\<^sub>0\<^sub>0(N\<^sub>J)-m\<^sub>1\<^sub>0(N\<^sub>J)\<close>
  is discharged through @{thm [source] bwd_invshift_via_rebase}, which reduces it
  to \<open>Red Y = Y\<close> for the rebased \<open>Y = rebaseRow0 e 0 (N\<^sub>J M J)\<close>.  The bundle facts
  (@{thm [source] fa_NJ_Y_facts}) make \<open>Y\<close> a nu-smaller A&B sequence; \<open>Red Y = Y\<close>
  then splits:
    \<^item> \<open>zeroT Y\<close> (\<open>Y = [(0,0)]\<close> since \<open>m\<^sub>0\<^sub>0(Y)=m\<^sub>1\<^sub>0(Y)=0\<close>): \<open>Red\<close> base case;
    \<^item> \<open>monoT Y\<close>, core (\<open>m\<^sub>1\<^sub>0(Y)=0\<close>): the \<open>nu\<close>-IH;
    \<^item> \<open>monoT Y\<close>, \<open>m\<^sub>1\<^sub>0(Y)>0\<close>: the nu-bounded m10pos brick
      @{thm [source] kst_condAB_imp_reduced_monoT_m10pos_nu}.
  The result plugs into the GREEN @{thm [source] kst_bwdcore_master_via_G}, which
  needs NO monoT-Y hypothesis (unlike @{thm [source] kst_condAB_imp_reduced_monoT_core_of_Ybundle},
  which cannot meet \<open>monoT Y\<close> for the zeroT-Y branches).  Cites only GREEN facts;
  the \<open>nu\<close>-IH is legitimate (strictly \<open>nu\<close>-smaller arguments); no \<open>p_*\<close> stub.\<close>

lemma fa_kst_condAB_imp_reduced_monoT_core:
  assumes MT0: "M0 \<in> T_PS" and mono0: "monoT M0"
    and c00: "entry M0 0 0 = 0" and c10: "entry M0 1 0 = 0"
    and condA0: "RedCondA M0" and condB0: "RedCondB M0"
  shows "Red M0 = M0"
proof -
  have "M0 \<in> T_PS \<and> monoT M0 \<and> entry M0 0 0 = 0 \<and> entry M0 1 0 = 0
          \<and> RedCondA M0 \<and> RedCondB M0 \<longrightarrow> Red M0 = M0"
  proof (induction M0 rule: measure_induct_rule[where f=nu])
    case (less M)
    show ?case
    proof (rule impI, elim conjE)
      assume MT: "M \<in> T_PS" and mono: "monoT M"
        and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
        and condA: "RedCondA M" and condB: "RedCondB M"
      show "Red M = M"
      proof (cases "TrMax M = Lng M - 1")
        case True
        show ?thesis by (rule kst_bwdcore_trunk[OF MT mono c0 c1 True condA])
      next
        case tne: False
        show ?thesis
        proof (rule kst_bwdcore_master_via_G[OF MT mono c0 c1 condA])
          fix J assume JBr: "J < Lng (Br M)"
          let ?X = "NJ M J"
          let ?e = "entry ?X 0 0 - entry ?X 1 0"
          let ?Y = "rebaseRow0 ?e 0 ?X"
          have bnd: "?X \<in> T_PS \<and> \<not> multiT ?X
                 \<and> entry ?X 1 0 \<le> entry ?X 0 0
                 \<and> (\<forall>j < Lng ?X. ?e \<le> entry ?X 0 j)
                 \<and> RedCondA ?X
                 \<and> RedCondA ?Y \<and> RedCondB ?Y \<and> entry ?Y 0 0 = entry ?Y 1 0
                 \<and> \<not> multiT ?Y \<and> nu ?Y < nu M"
            using fa_NJ_Y_facts[OF MT mono c0 c1 condA condB tne JBr]
            by (simp add: Let_def)
          have XT: "?X \<in> T_PS" using bnd by simp
          have lb: "\<And>j. j < Lng ?X \<Longrightarrow> ?e \<le> entry ?X 0 j" using bnd by simp
          have YA: "RedCondA ?Y" using bnd by simp
          have YB: "RedCondB ?Y" using bnd by simp
          have Yeq: "entry ?Y 0 0 = entry ?Y 1 0" using bnd by simp
          have Ynm: "\<not> multiT ?Y" using bnd by simp
          have YnuM: "nu ?Y < nu M" using bnd by simp
          have Yne: "?Y \<noteq> []"
          proof -
            have Xne: "?X \<noteq> []" using XT by (simp add: T_PS_def)
            have "Lng ?Y = Lng ?X" by simp
            thus ?thesis using Xne by (metis length_greater_0_conv)
          qed
          have YT: "?Y \<in> T_PS" using Yne by (simp add: T_PS_def)
          \<comment> \<open>\<open>Red Y = Y\<close>: zeroT base / core via nu-IH / m10>0 via m10pos brick.\<close>
          have Yred: "Red ?Y = ?Y"
          proof (cases "zeroT ?Y")
            case Yz: True
            have domY: "Red_dom ?Y" by (rule m_6_5_Red_welldef[OF YT])
            have rY: "Red ?Y = [(0, 0)]" using Red.psimps[OF domY] Yz by simp
            have L1: "Lng ?Y = 1" using Yz by (simp add: zeroT_def)
            have e1: "entry ?Y 1 0 = 0" using Yz by (simp add: zeroT_def)
            have e0: "entry ?Y 0 0 = 0" using Yeq e1 by simp
            have "?Y = [(0,0)]"
            proof (rule nth_equalityI)
              show "Lng ?Y = Lng [(0::nat,0::nat)]" using L1 by simp
            next
              fix j assume "j < Lng ?Y"
              hence j0: "j = 0" using L1 by simp
              have "fst (?Y ! 0) = 0" using e0 by (simp add: entry_def)
              moreover have "snd (?Y ! 0) = 0" using e1 by (simp add: entry_def)
              ultimately show "?Y ! j = [(0::nat,0::nat)] ! j" using j0 by (simp add: prod_eq_iff)
            qed
            thus ?thesis using rY by simp
          next
            case Ynz: False
            have Ymono: "monoT ?Y" using Ynm Ynz by (simp add: monoT_def multiT_def)
            show ?thesis
            proof (cases "entry ?Y 1 0 = 0")
              case Ycore: True
              have Ye00: "entry ?Y 0 0 = 0" using Yeq Ycore by simp
              show ?thesis
                using less.IH[OF YnuM] YT Ymono Ye00 Ycore YA YB by simp
            next
              case Ypos: False
              hence Ym10pos: "0 < entry ?Y 1 0" by simp
              have nuQlt: "nu (diagSeq 0 (entry ?Y 1 0 - 1) @ ?Y) < nu M"
              proof -
                have "nu (diagSeq 0 (entry ?Y 1 0 - 1) @ ?Y) < nu ?Y"
                  by (rule nu_diagSeq_m10pos_lt[OF Ymono Ym10pos Yeq])
                also have "\<dots> < nu M" using YnuM .
                finally show ?thesis .
              qed
              show ?thesis
              proof (rule kst_condAB_imp_reduced_monoT_m10pos_nu
                        [where B="nu M", OF _ YT Ymono Ym10pos YA YB nuQlt])
                fix N assume nuN: "nu N < nu M" and NT: "N \<in> T_PS" and Nmono: "monoT N"
                  and Ne00: "entry N 0 0 = 0" and Ne10: "entry N 1 0 = 0"
                  and NA: "RedCondA N" and NB: "RedCondB N"
                show "Red N = N"
                  using less.IH[OF nuN] NT Nmono Ne00 Ne10 NA NB by simp
              qed
            qed
          qed
          show "(IncrFirst ^^ (entry ?X 0 0 - entry ?X 1 0)) (Red ?X) = ?X"
            by (rule bwd_invshift_via_rebase[OF XT lb Yred])
        qed
      qed
    qed
  qed
  thus ?thesis using MT0 mono0 c00 c10 condA0 condB0 by blast
qed


text \<open>\<S>6.6 KEYSTONE BACKWARD, monoT \<open>m\<^sub>1\<^sub>0>0\<close> UNCONDITIONAL (Front A, tag
  pss-fa-core).  Instantiates the GREEN conditional
  @{thm [source] kst_condAB_imp_reduced_monoT_m10pos} with the now-unconditional
  core @{thm [source] fa_kst_condAB_imp_reduced_monoT_core}.\<close>

lemma fa_kst_condAB_imp_reduced_monoT_m10pos:
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and m10pos: "0 < entry M 1 0"
    and condA: "RedCondA M" and condB: "RedCondB M"
  shows "Red M = M"
proof (rule kst_condAB_imp_reduced_monoT_m10pos[OF _ MT mono m10pos condA condB])
  fix N assume NT: "N \<in> T_PS" and Nmono: "monoT N"
    and Ne00: "entry N 0 0 = 0" and Ne10: "entry N 1 0 = 0"
    and NA: "RedCondA N" and NB: "RedCondB N"
  show "Red N = N"
    by (rule fa_kst_condAB_imp_reduced_monoT_core[OF NT Nmono Ne00 Ne10 NA NB])
qed

text \<open>\<S>6.6 KEYSTONE BACKWARD, UNCONDITIONAL (Front A, tag pss-fa-core).
  \<open>RedCondA M \<and> RedCondB M \<Longrightarrow> Red M = M\<close> for every \<open>M \<in> T_PS\<close>, by discharging the
  two residual hypotheses of @{thm [source] kst_condAB_imp_reduced_cond} with the
  now-unconditional core and m10>0 bricks.\<close>

lemma fa_kst_condAB_imp_reduced:
  assumes MT: "M \<in> T_PS" and condA: "RedCondA M" and condB: "RedCondB M"
  shows "Red M = M"
proof (rule kst_condAB_imp_reduced_cond[OF _ _ MT condA condB])
  fix N assume NT: "N \<in> T_PS" and Nmono: "monoT N"
    and Ne00: "entry N 0 0 = 0" and Ne10: "entry N 1 0 = 0"
    and NA: "RedCondA N" and NB: "RedCondB N"
  show "Red N = N"
    by (rule fa_kst_condAB_imp_reduced_monoT_core[OF NT Nmono Ne00 Ne10 NA NB])
next
  fix N assume NT: "N \<in> T_PS" and Nmono: "monoT N" and Nm10: "0 < entry N 1 0"
    and NA: "RedCondA N" and NB: "RedCondB N"
  show "Red N = N"
    by (rule fa_kst_condAB_imp_reduced_monoT_m10pos[OF NT Nmono Nm10 NA NB])
qed

end
