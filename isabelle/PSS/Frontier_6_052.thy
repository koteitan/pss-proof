theory Frontier_6_052
  imports P_6_5_Red_IncrFirst
begin

subsection \<open>§6.5 命題（\<open>Red\<close>の冪等性）— bankable branch bricks (idempotency)\<close>

text \<open>m: the \<open>zeroT\<close> branch of idempotency.  \<open>Red M = [(0,0)]\<close>, which is a zero
  term, so a second \<open>Red\<close> leaves it fixed.\<close>

lemma idem2_zeroT:
  assumes MT: "M \<in> T_PS" and z: "zeroT M"
  shows "Red (Red M) = Red M"
proof -
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have rM: "Red M = [(0,0)]" using Red.psimps[OF domM] z by simp
  have z2: "zeroT (Red M)" by (simp add: rM zeroT_def entry_def)
  have rM_T: "Red M \<in> T_PS" by (simp add: rM T_PS_def)
  have dom2: "Red_dom (Red M)" by (rule m_6_5_Red_welldef[OF rM_T])
  have "Red (Red M) = [(0,0)]" using Red.psimps[OF dom2] z2 by simp
  thus ?thesis using rM by simp
qed

text \<open>m: the core-trunk branch of idempotency.  \<open>Red M = diagSeq 0 (Lng M - 1)\<close>
  (a core diagonal), and @{thm [source] Red_core_diagSeq} pins it as a fixed
  point of \<open>Red\<close>.\<close>

lemma idem2_core_trunk:
  assumes MT: "M \<in> T_PS" and nz: "\<not> zeroT M" and nmu: "\<not> multiT M"
    and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and tr: "TrMax M = Lng M - 1"
  shows "Red (Red M) = Red M"
proof -
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have rM: "Red M = diagSeq (entry M 1 0) (entry M 1 0 + (Lng M - 1))"
    using Red.psimps[OF domM] nz nmu c0 c1 tr by (simp add: Let_def)
  have rM': "Red M = diagSeq 0 (Lng M - 1)" using rM c1 by simp
  have "Red (Red M) = Red (diagSeq 0 (Lng M - 1))" by (simp add: rM')
  also have "\<dots> = diagSeq 0 (Lng M - 1)" by (rule Red_core_diagSeq)
  finally show ?thesis using rM' by simp
qed

text \<open>m: the shift branch of idempotency, as a REDUCTION onto @{const coreReduce}.
  For a \<open>monoT\<close> \<open>M\<close> with \<open>m\<^sub>0\<^sub>0 > 0, m\<^sub>1\<^sub>0 = 0\<close>, the \<open>Red\<close> recursion takes the
  shift branch with argument \<open>coreReduce M\<close> (the \<open>m\<^sub>1\<^sub>0 = 0\<close> form of
  @{const coreReduce}), so \<open>Red M = Red (coreReduce M)\<close>.  Since \<open>coreReduce M\<close> is
  non-multi (@{thm [source] coreReduce_nonmulti}) and in \<open>T\<^sub>PS\<close>, idempotency on it
  (the induction hypothesis) transfers to \<open>M\<close>.\<close>

lemma idem2_shift_reduce:
  assumes MT: "M \<in> T_PS" and mono: "monoT M"
    and nc: "\<not> (entry M 0 0 = 0 \<and> entry M 1 0 = 0)" and c1: "entry M 1 0 = 0"
    and IH: "Red (Red (coreReduce M)) = Red (coreReduce M)"
  shows "Red (Red M) = Red M"
proof -
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have nz: "\<not> zeroT M" using mono by (simp add: monoT_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have LMpos: "0 < Lng M" using Mne by (cases M) auto
  let ?j1 = "Lng M - 1"
  let ?sh = "map (\<lambda>j. (entry M 0 j - entry M 0 0, entry M 1 j)) [0..<Suc ?j1]"
  have rM: "Red M = Red ?sh"
    using Red.psimps[OF domM] nz nmu nc c1 by (simp add: Let_def)
  \<comment> \<open>the shift argument is exactly \<open>coreReduce M\<close> (\<open>m\<^sub>1\<^sub>0 = 0\<close> form).\<close>
  have sh_eq: "?sh = coreReduce M"
    using c1 LMpos by (simp add: coreReduce_def del: upt_Suc)
  have rM_cr: "Red M = Red (coreReduce M)" using rM sh_eq by simp
  show ?thesis using rM_cr IH by simp
qed


subsection \<open>The MASTER-KEY ancestor-structure \<open>Red\<close> congruence engine\<close>

text \<open>STEP 0 (empirically pinned, \<open>python/cong_step0.py\<close>, 0-fail over
  >4000 ordered-relabel pairs across multiple sizes/seeds): @{const Red} is
  determined by the ancestor structure together with the full row-1 data.  The
  minimal sufficient hypothesis is
    \<open>Lng A = Lng X \<and> nextrel0 A = nextrel0 X \<and> (\<forall>j. entry A 1 j = entry X 1 j)\<close>.
  (Dropping any one fails; \<open>nextrel1\<close> equality is then redundant — it is implied,
  see \<open>cong_struct.nextrel1_eq\<close> below — and \<open>entry _ 0 0\<close> equality is
  not needed.)  This generalizes the green @{locale cut_bump} engine, whose
  \<open>row0_bump\<close> axiom is the uniform-@{const IncrFirst} special case of
  \<open>nextrel0 A = nextrel0 X\<close>.\<close>

locale cong_struct =
  fixes A X :: pairseq
  assumes len_eq:     "Lng A = Lng X"
    and nextrel0_eq': "nextrel0 A = nextrel0 X"
    and row1_eq:      "\<And>j. j < Lng X \<Longrightarrow> entry A 1 j = entry X 1 j"
begin

text \<open>All ancestor structure is shared.  The proofs are verbatim those of the
  @{locale tail_bump} downstream lemmas — they never used \<open>row0_bump\<close> except to
  derive \<open>nextrel0_eq\<close>, which here is an axiom.\<close>

lemma nextrel0_eq: "nextrel0 A = nextrel0 X" by (rule nextrel0_eq')

lemma le0_eq: "le0 A = le0 X"
  by (intro ext) (simp add: le0_def nextrel0_eq len_eq)

lemma nextrel1_eq: "nextrel1 A = nextrel1 X"
proof (intro ext)
  fix a b
  show "nextrel1 A a b = nextrel1 X a b"
  proof (cases "a < Lng X \<and> b < Lng X")
    case True
    hence aX: "a < Lng X" and bX: "b < Lng X" by auto
    have e1a: "entry A 1 a = entry X 1 a" by (rule row1_eq[OF aX])
    have e1b: "entry A 1 b = entry X 1 b" by (rule row1_eq[OF bX])
    have U: "(\<forall>j. a < j \<and> le0 X j b \<longrightarrow> entry A 1 b \<le> entry A 1 j)
              = (\<forall>j. a < j \<and> le0 X j b \<longrightarrow> entry X 1 b \<le> entry X 1 j)"
    proof (rule all_cong1)
      fix j
      show "(a < j \<and> le0 X j b \<longrightarrow> entry A 1 b \<le> entry A 1 j)
          = (a < j \<and> le0 X j b \<longrightarrow> entry X 1 b \<le> entry X 1 j)"
      proof (cases "a < j \<and> le0 X j b")
        case True
        hence jX: "j < Lng X" by (simp add: le0_def)
        show ?thesis using e1b row1_eq[OF jX] by simp
      next
        case False
        thus ?thesis by blast
      qed
    qed
    have "nextrel1 A a b =
       (a < Lng X \<and> b < Lng X \<and> a < b \<and>
        entry A 1 a < entry A 1 b \<and> le0 X a b \<and>
        (\<forall>j. a < j \<and> le0 X j b \<longrightarrow> entry A 1 b \<le> entry A 1 j))"
      unfolding nextrel1_def by (simp add: len_eq le0_eq)
    also have "\<dots> =
       (a < Lng X \<and> b < Lng X \<and> a < b \<and>
        entry X 1 a < entry X 1 b \<and> le0 X a b \<and>
        (\<forall>j. a < j \<and> le0 X j b \<longrightarrow> entry X 1 b \<le> entry X 1 j))"
      using e1a e1b U by simp
    also have "\<dots> = nextrel1 X a b"
      unfolding nextrel1_def by (simp add: len_eq le0_eq)
    finally show ?thesis .
  next
    case False
    thus ?thesis by (auto simp: nextrel1_def len_eq)
  qed
qed

lemma le1_eq: "le1 A = le1 X"
  by (intro ext) (simp add: le1_def nextrel1_eq len_eq)

lemma nextR_eq: "nextR A = nextR X"
  by (intro ext) (simp add: nextR_def nextrel0_eq nextrel1_eq)

lemma leR_eq: "leR A = leR X"
  by (intro ext) (simp add: leR_def le0_eq le1_eq)

lemma TrMax_eq: "TrMax A = TrMax X"
  by (simp add: TrMax_def nextR_eq)

lemma zeroT_eq: "zeroT A = zeroT X"
  using row1_eq[of 0]
  by (cases "Lng X = 0") (auto simp: zeroT_def len_eq)

lemma monoT_eq: "monoT A = monoT X"
  by (simp add: monoT_def zeroT_eq leR_eq len_eq)

lemma multiT_eq: "multiT A = multiT X"
  by (simp add: multiT_def zeroT_eq monoT_eq)

lemma Pcut_eq: "Pcut A = Pcut X"
  by (simp add: Pcut_def leR_eq len_eq)

end

text \<open>\<open>P\<close>, \<open>Br\<close>, \<open>FirstNodes\<close>, \<open>Joints\<close>, \<open>npJ\<close> are all functions of the shared
  ancestor structure.  Unlike @{locale cut_bump} (where \<open>Br A = map IncrFirst
  (Br X)\<close>), here \<open>Br A\<close> is \<^emph>\<open>not\<close> a fixed reshape of \<open>Br X\<close> — the row-0 values of
  the blocks differ — so we cannot conclude \<open>P A = P X\<close>.  Instead the
  \<^emph>\<open>combinatorial\<close> data of \<open>P\<close> (number of blocks and their boundary index sums)
  is shared, and each block \<open>P A ! J = seg A s e\<close> / \<open>P X ! J = seg X s e\<close> is over
  the \<^emph>\<open>same\<close> index window, hence again \<open>cong_struct\<close>-related (lemma
  \<open>congR_seg\<close> below).

  We carry the abstract structural relation \<open>R A X\<close> through the \<open>P\<close> recursion.\<close>

definition congR :: "pairseq \<Rightarrow> pairseq \<Rightarrow> bool" where
  "congR A X \<longleftrightarrow> Lng A = Lng X \<and> nextrel0 A = nextrel0 X
                  \<and> (\<forall>j < Lng X. entry A 1 j = entry X 1 j)"

lemma congR_cong_struct: "congR A X \<Longrightarrow> cong_struct A X"
  by (unfold_locales) (auto simp: congR_def)

end
