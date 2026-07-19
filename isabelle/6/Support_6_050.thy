theory Support_6_050
  imports P_6_6_reduced_iff_cond
begin

subsection \<open>§6.5 \<open>Red\<close>-invariance of ancestor order via the \<open>congR\<close> bridge (Front A)\<close>

text \<open>
  \<^bold>\<open>Empirical scoping correction (Front A, verified in python/red_model.py)\<close>.
  The headline @{text p_6_5_Red_le} (\<open>leR M = leR (Red M)\<close>) is \<^emph>\<open>FALSE\<close>
  on all of \<open>T_PS = {M. M \<noteq> []}\<close>, and remains FALSE under the hypothesis
  \<open>RedCondA M\<close> \<^emph>\<open>alone\<close>: the minimal counterexample is \<open>M = (0,0)(0,1)\<close>
  (\<open>multiT M\<close>, \<open>RedCondA M\<close> holds, \<open>RedCondB M\<close> fails), where
  \<open>Red M = (0,0)(1,1)\<close>, so \<open>le0 M 0 1 = False\<close> but \<open>le0 (Red M) 0 1 = True\<close>.
  Over the raw enumeration enum(4,2) \<open>RedCondA\<close>-alone breaks \<open>le0\<close>-invariance on
  2502/4530 cases (all of them \<^emph>\<open>multiT\<close>).

  \<^bold>\<open>True T_PS-scopings\<close> (python, enum(4,2)/(5,2)/(4,3), 0-fail):
  \<^item> \<open>RedCondA M \<and> RedCondB M \<Longleftrightarrow> Red M = M\<close> (= the §6.6 keystone
    @{thm [source] m_6_6_reduced_iff_cond}); there \<open>leR\<close>-invariance is \<^emph>\<open>trivial\<close>.
  \<^item> \<open>RedCondA M \<and> monoT M \<Longrightarrow> congR M (Red M)\<close> — all three \<open>congR\<close> components
    (\<open>Lng\<close>, \<open>nextrel0\<close>, row-1 entries) hold 0-fail; this is the \<^emph>\<open>non-trivial\<close>
    scoping (it covers reduced \<^emph>\<open>and\<close> non-reduced monoT slices).
  \<^item> \<open>anchored_slice M \<Longrightarrow> RedCondA M\<close> holds 2575/2575, and
    \<open>anchored_slice M \<Longrightarrow> leR\<close>-invariance holds 2575/2575 (incl. 919 non-reduced
    slices), but \<open>anchored_slice M \<Longrightarrow> RedCondB M\<close> only 1656/2575 — so the
    anchored-slice bridge is genuinely stronger than the reduced (A\<and>B) case.

  \<^bold>\<open>Assembly bricks below.\<close>  Once \<open>congR M (Red M)\<close> is established (the remaining
  blocker; the natural route is the monoT branch of @{thm [source] cdn_red_cong}
  via @{thm [source] congR_self_shiftRow0} / @{thm [source] nextrel0_rebaseRow0_eq}),
  these convert it into the row-0 \<open>le0\<close>-invariance and the full \<open>leR\<close>-invariance
  (= @{text p_6_5_Red_le}'s mechanized statement) using only the already
  GREEN \<open>congR\<close>-projection lemmas.  They cite NO unproved \<open>p_*\<close> stub.\<close>

text \<open>Row-0 fragment: \<open>congR\<close> transports \<open>le0\<close> verbatim (it shares \<open>Lng\<close> and
  \<open>nextrel0\<close>, and \<open>le0\<close> is built solely from those).\<close>

lemma m_6_5_congR_imp_le0_inv:
  assumes R: "congR M (Red M)"
  shows "le0 M j0 j1 = le0 (Red M) j0 j1"
proof -
  have L: "Lng M = Lng (Red M)" by (rule congR_Lng[OF R])
  have N: "nextrel0 M = nextrel0 (Red M)" using R by (simp add: congR_def)
  show ?thesis by (simp add: le0_def L N)
qed

text \<open>Step-relation fragment: \<open>congR\<close> shares \<open>nextrel0\<close> outright.\<close>

lemma m_6_5_congR_imp_nextrel0_inv:
  assumes R: "congR M (Red M)"
  shows "nextrel0 M j0 j1 = nextrel0 (Red M) j0 j1"
  using R by (simp add: congR_def)

text \<open>Full bridge: \<open>congR\<close> transports the unified ancestor order \<open>leR\<close> at every
  row \<open>i\<close> (via the GREEN point-free @{thm [source] congR_leR}).  This is exactly
  the mechanized form of @{text p_6_5_Red_le}'s conclusion, modulo the
  \<open>congR M (Red M)\<close> hypothesis.\<close>

lemma m_6_5_congR_imp_leR_inv:
  assumes R: "congR M (Red M)"
  shows "leR M i j0 j1 = leR (Red M) i j0 j1"
proof -
  have "leR M = leR (Red M)" by (rule congR_leR[OF R])
  thus ?thesis by simp
qed

text \<open>Row-1 fragment falls out of the same bridge (specialise \<open>i = 1\<close>): once
  \<open>le0\<close> and the row-1 entries are shared, \<open>nextrel1\<close> and hence \<open>le1\<close> coincide.\<close>

lemma m_6_5_congR_imp_le1_inv:
  assumes R: "congR M (Red M)"
  shows "le1 M j0 j1 = le1 (Red M) j0 j1"
proof -
  have "leR M 1 j0 j1 = leR (Red M) 1 j0 j1" by (rule m_6_5_congR_imp_leR_inv[OF R])
  thus ?thesis by (simp add: leR_def)
qed

subsection \<open>§6.5 Anchored slices are never \<open>multiT\<close> (Front B reduction key)\<close>

text \<open>
  \<^bold>\<open>Reduction key (Front B, verified \<open>python/red_model.py\<close>, 463005 cases 0-fail
  for the abstract \<open>le0\<close>-segment form; 2059 genuine anchored slices 0-fail).\<close>

  An anchored slice \<open>M = seg S a b\<close> carries the hypothesis \<open>le0 S a b\<close>: index
  \<open>a\<close> is a row-0 ancestor of \<open>b\<close> in \<open>S\<close>.  Transported to the slice (via the
  GREEN @{thm [source] adm_le0_seg}), this says \<open>le0 M 0 (Lng M - 1)\<close>: the slice
  is row-0 monotone from its first to its last index.  By the §6.2 criterion
  @{thm [source] m_6_2_not_multi_iff_le} (\<open>\<not> multiT M \<longleftrightarrow> leR M 0 0 (Lng M-1)\<close>),
  this is exactly \<open>\<not> multiT M\<close>.

  \<^bold>\<open>Consequence.\<close>  Every anchored slice is \<open>zeroT\<close> or \<open>monoT\<close>; the \<open>multiT\<close>
  branch of @{const Red} is \<^emph>\<open>never\<close> reached on the §6.5 domain.  Hence the
  ancestor-order Red-invariance @{text p_6_5_Red_le} does \<^emph>\<open>not\<close> require
  any multi-term \<open>P\<close>-block lift: it reduces to the single obligation
  \<open>monoT M \<and> RedCondA M \<Longrightarrow> congR M (Red M)\<close> on the mono branch (the \<open>monoT\<close>-only
  form \<^bold>\<open>without\<close> \<open>RedCondA\<close> is FALSE — counterexample \<open>M = (0,0)(1,2)\<close>,
  \<open>Red M = (0,0)(1,1)\<close>, row-1 entry \<open>2 \<noteq> 1\<close>).  The \<open>zeroT\<close> case is trivial
  (\<open>Lng = 1\<close>, \<open>Red M = [(0,0)]\<close>).\<close>

lemma m_6_5_anchored_not_multiT:
  assumes M: "M \<in> anchored_slice"
  shows "\<not> multiT M"
proof -
  from M obtain S a b where ab: "a \<le> b" and bS: "b < Lng S"
      and leS: "le0 S a b" and Mseg: "M = seg S a b"
    unfolding anchored_slice_def by blast
  have MT: "M \<in> T_PS" by (rule anchored_slice_imp_T_PS[OF M])
  \<comment> \<open>The slice length is \<open>Suc b - a\<close>, so \<open>Lng M - 1 = b - a\<close>.\<close>
  have LM: "Lng M = Suc b - a" using Mseg by simp
  have LM1: "Lng M - 1 = b - a" using LM by simp
  \<comment> \<open>Transport the anchor \<open>le0 S a b\<close> into the slice as \<open>le0 M 0 (b-a)\<close>.\<close>
  have bnd0: "(0::nat) \<le> b - a" by simp
  have bndba: "b - a \<le> b - a" by simp
  have seg_to_S: "le0 (seg S a b) 0 (b - a) \<longleftrightarrow> le0 S (a + 0) (a + (b - a))"
    by (rule adm_le0_seg[OF bS bnd0 bndba ab])
  have abeq: "a + (b - a) = b" using ab by simp
  have leM: "le0 M 0 (b - a)" using seg_to_S leS Mseg abeq by simp
  \<comment> \<open>\<open>le0 M 0 (Lng M - 1)\<close> is exactly \<open>leR M 0 0 (Lng M - 1)\<close>, i.e. \<open>\<not> multiT M\<close>.\<close>
  have leRM: "leR M 0 0 (Lng M - 1)" using leM LM1 by (simp add: leR_def)
  show "\<not> multiT M" using m_6_2_not_multi_iff_le[OF MT] leRM by simp
qed

text \<open>Corollary: an anchored slice is \<open>zeroT\<close> or \<open>monoT\<close>.\<close>

lemma m_6_5_anchored_zeroT_or_monoT:
  assumes M: "M \<in> anchored_slice"
  shows "zeroT M \<or> monoT M"
  using m_6_5_anchored_not_multiT[OF M] by (simp add: multiT_def)


subsection \<open>Front A: \<open>congR M (Red M)\<close> for \<open>RedCondA\<close>+\<open>monoT\<close> (mono mono-core for \<open>p_6_5_Red_le\<close>)\<close>

text \<open>m: \<open>shiftRow0\<close> is \<open>rebaseRow0 m\<^sub>0\<^sub>0 0\<close>, and for \<open>monoT M\<close> the row-0 left end is
  the row-0 minimum, so @{thm [source] RedCondA_rebaseRow0} carries \<open>RedCondA\<close>
  across \<open>shiftRow0\<close>.\<close>

lemma m_6_5_RedCondA_shiftRow0:
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and condA: "RedCondA M"
  shows "RedCondA (shiftRow0 M)"
proof -
  have shr_eq: "shiftRow0 M = rebaseRow0 (entry M 0 0) 0 M"
  proof (rule nth_equalityI)
    show "Lng (shiftRow0 M) = Lng (rebaseRow0 (entry M 0 0) 0 M)" by simp
  next
    fix j assume "j < Lng (shiftRow0 M)"
    hence jl: "j < Lng M" by simp
    have s0: "entry (shiftRow0 M) 0 j = entry M 0 j - entry M 0 0"
      by (rule entry_shiftRow0_0[OF jl])
    have s1: "entry (shiftRow0 M) 1 j = entry M 1 j" by (rule entry_shiftRow0_1[OF jl])
    have r0: "entry (rebaseRow0 (entry M 0 0) 0 M) 0 j = entry M 0 j - entry M 0 0"
      using entry_rebaseRow0_0[OF jl] by simp
    have r1: "entry (rebaseRow0 (entry M 0 0) 0 M) 1 j = entry M 1 j"
      by (rule entry_rebaseRow0_1[OF jl])
    show "shiftRow0 M ! j = rebaseRow0 (entry M 0 0) 0 M ! j"
      using s0 s1 r0 r1 by (simp add: entry_def prod_eq_iff)
  qed
  have lb: "\<And>j. j < Lng M \<Longrightarrow> entry M 0 0 \<le> entry M 0 j"
  proof -
    fix j assume jl: "j < Lng M"
    show "entry M 0 0 \<le> entry M 0 j"
    proof (cases "0 < j")
      case True
      thus ?thesis using monoT_row0_min[OF MT mono True jl] by simp
    next
      case False thus ?thesis by simp
    qed
  qed
  show ?thesis using RedCondA_rebaseRow0[OF lb condA] shr_eq by simp
qed

text \<open>m: trunk-core under \<open>RedCondA\<close> forces the consecutive diagonal.  In the
  trunk every consecutive step \<open>k \<rightarrow> Suc k\<close> is a unique parent in both rows
  (row 1 by @{thm [source] nextR1_unique}, row 0 because \<open>entry M 0\<close> strictly
  increases on the trunk, @{thm [source] trunk_step_lt}, so the consecutive pair
  is a \<open>nextrel0\<close> edge with a unique parent).  \<open>RedCondA\<close> then steps each row by
  \<open>+1\<close>, and with \<open>entry M i 0 = 0\<close> the rows are the identity.\<close>

lemma m_6_5_trunk_core_diag_row:
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and condA: "RedCondA M"
    and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and trunk: "TrMax M = Lng M - 1"
  shows "\<forall>i\<le>1. \<forall>k<Lng M. entry M i k = k"
proof (intro allI impI)
  fix i k assume i: "i \<le> (1::nat)" and k: "k < Lng M"
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  have step: "\<And>j. j < TrMax M \<Longrightarrow> entry M i (Suc j) = entry M i j + 1"
  proof -
    fix j assume jTr: "j < TrMax M"
    have jL: "Suc j < Lng M" using jTr trunk LMpos by linarith
    have i01: "i = 0 \<or> i = 1" using i by linarith
    \<comment> \<open>consecutive step is a unique row-\<open>i\<close> parent of \<open>Suc j\<close>.\<close>
    have nxt: "nextR M i j (Suc j)"
    proof (cases "i = 0")
      case True
      have lt: "entry M 0 j < entry M 0 (Suc j)" by (rule trunk_step_lt[OF MT _ jTr]) simp
      have nr0: "nextrel0 M j (Suc j)"
        unfolding nextrel0_def using jL lt by simp
      thus ?thesis using True by (simp add: nextR_def)
    next
      case False
      hence i1: "i = 1" using i by linarith
      have "nextR M 1 j (j + 1)" by (rule TrMax_trunk_step[OF MT jTr])
      hence "nextR M 1 j (Suc j)" by simp
      thus ?thesis using i1 by simp
    qed
    have uniq: "\<And>j0. nextR M i j0 (Suc j) \<Longrightarrow> j0 = j"
    proof -
      fix j0 assume j0: "nextR M i j0 (Suc j)"
      show "j0 = j" using i01
      proof
        assume "i = 0"
        thus "j0 = j" using j0 nxt by (simp add: idxsum_parent0_unique)
      next
        assume "i = 1"
        thus "j0 = j" using j0 nxt by (simp add: nextR1_unique)
      qed
    qed
    have ex1: "\<exists>!j0. nextR M i j0 (Suc j)"
      by (rule ex1I[where P="\<lambda>j0. nextR M i j0 (Suc j)" and a=j, OF nxt uniq])
    have hp: "hasParent M i (Suc j)" unfolding hasParent_def using ex1 .
    have par: "parent M i (Suc j) = j"
      unfolding parent_def by (rule the1_equality[OF ex1 nxt])
    have "entry M i (parent M i (Suc j)) + 1 = entry M i (Suc j)"
      using condA i hp unfolding RedCondA_def by blast
    thus "entry M i (Suc j) = entry M i j + 1" using par by simp
  qed
  \<comment> \<open>induct the \<open>+1\<close> step from the zero left end.\<close>
  have base: "entry M i 0 = 0"
  proof (cases "i = 0")
    case True thus ?thesis using c0 by simp
  next
    case False
    hence "i = 1" using i by linarith
    thus ?thesis using c1 by simp
  qed
  have kTr: "k \<le> TrMax M" using k trunk LMpos by linarith
  have "entry M i k = k"
    using kTr
  proof (induction k)
    case 0 thus ?case using base by simp
  next
    case (Suc k)
    have kTr': "k < TrMax M" using Suc.prems by simp
    have ih: "entry M i k = k" using Suc.IH kTr' by simp
    show ?case using step[OF kTr'] ih by simp
  qed
  thus "entry M i k = k" .
qed

text \<open>m: the trunk-core \<open>congR M (Red M)\<close> brick.  By the row-identity above \<open>M\<close> is
  literally \<open>diagSeq 0 (Lng M-1)\<close>, and the trunk-core \<open>Red\<close> branch (with
  \<open>m\<^sub>1\<^sub>0 = 0\<close>) outputs the same diagonal, so \<open>Red M = M\<close> and \<open>congR\<close> is reflexive.\<close>

lemma m_6_5_congR_self_Red_trunk_core:
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and condA: "RedCondA M"
    and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and trunk: "TrMax M = Lng M - 1"
  shows "congR M (Red M)"
proof -
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  have rows: "\<forall>i\<le>1. \<forall>k<Lng M. entry M i k = k"
    by (rule m_6_5_trunk_core_diag_row[OF MT mono condA c0 c1 trunk])
  \<comment> \<open>\<open>M\<close> is literally the diagonal \<open>diagSeq 0 (Lng M-1)\<close>.\<close>
  have Mdiag: "M = diagSeq 0 (Lng M - 1)"
  proof (rule nth_equalityI)
    have Ld: "Lng (diagSeq 0 (Lng M - 1)) = Lng M" using LMpos by (simp del: upt_Suc)
    show "length M = length (diagSeq 0 (Lng M - 1))" using Ld by simp
    fix k assume k: "k < length M"
    hence kL: "k < Lng M" by simp
    have e0: "entry M 0 k = k" using rows kL by simp
    have e1: "entry M 1 k = k" using rows kL by simp
    have "M ! k = (entry M 0 k, entry M 1 k)" by (rule entry_pair[symmetric])
    hence Mk: "M ! k = (k, k)" using e0 e1 by simp
    have db: "k < Suc (Lng M - 1) - 0" using kL LMpos by simp
    have "diagSeq 0 (Lng M - 1) ! k = (0 + k, 0 + k)" by (rule diagSeq_nth[OF db])
    thus "M ! k = diagSeq 0 (Lng M - 1) ! k" using Mk by simp
  qed
  \<comment> \<open>trunk-core \<open>Red\<close> branch outputs the same diagonal.\<close>
  have dom: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have nz: "\<not> zeroT M" using mono by (simp add: monoT_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  have rM: "Red M = diagSeq (entry M 1 0) (entry M 1 0 + (Lng M - 1))"
    using Red.psimps[OF dom] nz nmu c0 c1 trunk by (simp add: Let_def)
  have "Red M = diagSeq 0 (Lng M - 1)" using rM c1 by simp
  hence "Red M = M" using Mdiag by simp
  thus ?thesis by (simp add: congR_refl)
qed

text \<open>FRONT B (tag pss-redle-assembly).  Target (1) \<open>m_6_5_anchored_imp_RedCondA\<close>
  and target (2) \<open>m_6_5_Red_le\<close> = the headline \<open>p_6_5_Red_le\<close>.

  \<^bold>\<open>Empirical truth-check\<close> (PYTHONPATH=python, red_model.py, /tmp/frontB_verify.py):
  \<^item> \<open>ST_PS \<Longrightarrow> RedCondA\<close>: 136/136 PASS (0 fail).
  \<^item> anchored slices from \<open>ST_PS\<close> (\<open>seg S a b\<close>, \<open>le0 S a b\<close>) \<Longrightarrow> \<open>RedCondA\<close>: 3208/3208 PASS.
  \<^item> reduced-source anchored \<Longrightarrow> \<open>RedCondA\<close>: 3208/3208 PASS.
  So both branches of \<open>anchored_slice\<close> satisfy \<open>RedCondA\<close>.\<close>


subsection \<open>Target (1): anchored slices satisfy \<open>RedCondA\<close>\<close>

text \<open>The \<^emph>\<open>reduced-and-mono\<close> branch (\<open>S \<in> RT_PS \<inter> PT_PS\<close>) is fully GREEN: \<open>S\<close>
  reduced gives \<open>RedCondA S\<close> via the forward keystone
  @{thm [source] kst_reduced_imp_condAB_uncond}, which the slice \<open>seg S a b\<close>
  inherits via @{thm [source] fa_RedCondA_seg}.\<close>

lemma m_6_5_anchored_reduced_imp_RedCondA:
  assumes M: "M \<in> anchored_slice"
    and src: "\<exists>S a b. S \<in> RT_PS \<and> S \<in> PT_PS \<and> a \<le> b \<and> b < Lng S
                        \<and> le0 S a b \<and> M = seg S a b"
  shows "RedCondA M"
proof -
  from src obtain S a b where SR: "S \<in> RT_PS" and ab: "a \<le> b"
      and bS: "b < Lng S" and Mseg: "M = seg S a b" by blast
  have ST: "S \<in> T_PS" using SR by (simp add: RT_PS_def)
  have condS: "RedCondA S \<and> RedCondB S" by (rule kst_reduced_imp_condAB_uncond[OF SR])
  hence condAS: "RedCondA S" by simp
  have MT: "M \<in> T_PS" by (rule anchored_slice_imp_T_PS[OF M])
  have segT: "seg S a b \<in> T_PS" using MT Mseg by simp
  show ?thesis using Mseg fa_RedCondA_seg[OF ST segT bS condAS] by simp
qed

text \<open>The \<^emph>\<open>standard\<close> branch (\<open>S \<in> ST_PS\<close>) inherits \<open>RedCondA\<close> from \<open>S\<close> the same
  way via @{thm [source] fa_RedCondA_seg}, ONCE \<open>S \<in> ST_PS \<Longrightarrow> RedCondA S\<close> is
  available.  That fact (\<open>stdCA\<close>) is exactly @{text p_6_7_standard_reduced}
  (\<open>ST_PS \<subseteq> RT_PS\<close>) composed with @{thm [source] kst_reduced_imp_condAB_uncond};
  but \<open>p_6_7_standard_reduced\<close> is an UNPROVEN stub, so — per the soundness rule
  — we do NOT cite it.  We carry \<open>stdCA\<close> as an EXPLICIT hypothesis to be
  discharged when \<open>ST_PS \<subseteq> RT_PS\<close> (or the direct \<open>oper\<close>-preservation of
  \<open>RedCondA\<close>) lands.  Empirically \<open>stdCA\<close> is 136/136 TRUE.\<close>

lemma m_6_5_anchored_imp_RedCondA:
  assumes M: "M \<in> anchored_slice"
    and stdCA: "\<And>S. S \<in> ST_PS \<Longrightarrow> RedCondA S"
  shows "RedCondA M"
proof -
  from M obtain S a b where SD: "S \<in> ST_PS \<or> (S \<in> RT_PS \<and> S \<in> PT_PS)"
      and ab: "a \<le> b" and bS: "b < Lng S" and leS: "le0 S a b" and Mseg: "M = seg S a b"
    unfolding anchored_slice_def by blast
  have MT: "M \<in> T_PS" by (rule anchored_slice_imp_T_PS[OF M])
  have segT: "seg S a b \<in> T_PS" using MT Mseg by simp
  from SD show ?thesis
  proof
    assume SS: "S \<in> ST_PS"
    have ST: "S \<in> T_PS" by (rule ST_PS_T_PS[OF SS])
    have condAS: "RedCondA S" by (rule stdCA[OF SS])
    show ?thesis using Mseg fa_RedCondA_seg[OF ST segT bS condAS] by simp
  next
    assume SR: "S \<in> RT_PS \<and> S \<in> PT_PS"
    have src: "\<exists>S a b. S \<in> RT_PS \<and> S \<in> PT_PS \<and> a \<le> b \<and> b < Lng S
                        \<and> le0 S a b \<and> M = seg S a b"
      using SR ab bS leS Mseg by blast
    show ?thesis by (rule m_6_5_anchored_reduced_imp_RedCondA[OF M src])
  qed
qed

end
