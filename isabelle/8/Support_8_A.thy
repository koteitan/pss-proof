theory Support_8_A
  imports After_7
begin

text \<open>
  Remaining mechanized support for the article after the completed §5 and §6
  proposition layers.  The relocated exact proofs and their dependency-ordered
  helpers live under \<open>5/\<close>, \<open>6/\<close>, and \<open>PSS/\<close>.
\<close>

text \<open>The §5 and §6 statements, proofs, and supporting facts have moved to
  their per-proposition and shared support theories.\<close>

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

lemma poper_leR_drop:
  assumes "a < Lng M - c" "b < Lng M - c"
  shows "leR (drop c M) i a b \<longleftrightarrow> leR M i (c + a) (c + b)"
  unfolding leR_def
  using poper_le0_drop[OF assms] poper_le1_drop[OF assms] by simp

text \<open>Row-0 entry of an \<open>n\<close>-fold concatenation, on the first copy.\<close>

lemma entry_concat_replicate_lt:
  assumes "j < Lng Q"
  shows "entry (concat (replicate (Suc m) Q)) i j = entry Q i j"
proof -
  have "concat (replicate (Suc m) Q) = Q @ concat (replicate m Q)"
    by (simp add: replicate_Suc)
  thus ?thesis using assms by (simp add: entry_def nth_append)
qed

section \<open>Faithfulness lemmas (忠実性補題)\<close>

text \<open>
  This section justifies the modelling choices in @{file "../pss_defs.thy"} by
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


text \<open>Row-1 reachability along a diagonal: same chain, lifted through
  @{thm [source] nextR1_diagSeq} (the diagonal has full row-1 \<open><\<^sup>Next\<close> edges,
  so \<open>\<le>\<^sub>M\<close> on row 1 is also the index order \<open>j0 \<le> j1\<close> \<open>-\<close> NOT \<open>j0 = j1\<close>).\<close>

lemma nextrel1_diagSeq_rtrancl:
  assumes "j1 < Suc b - a" and "j0 \<le> j1"
  shows "(nextrel1 (diagSeq a b))\<^sup>*\<^sup>* j0 j1"
proof -
  let ?M = "diagSeq a b"
  from assms obtain d where d: "j1 = j0 + d" using le_Suc_ex by blast
  have "j0 + d < Suc b - a \<Longrightarrow> (nextrel1 ?M)\<^sup>*\<^sup>* j0 (j0 + d)"
  proof (induction d)
    case 0 show ?case by simp
  next
    case (Suc d)
    have lt: "Suc (j0 + d) < Suc b - a" using Suc.prems by simp
    have rt: "(nextrel1 ?M)\<^sup>*\<^sup>* j0 (j0 + d)" using Suc.IH lt by simp
    have step: "nextrel1 ?M (j0 + d) (Suc (j0 + d))"
      using nextR1_diagSeq[OF lt] by (simp add: nextR_def)
    show ?case using rt step by (simp add: rtranclp.rtrancl_into_rtrancl)
  qed
  thus ?thesis using assms(1) d by simp
qed

text \<open>m (H1): row-1 \<open>\<le>\<^sub>M\<close> on a diagonal segment is the index order, too.\<close>

lemma le1_diagSeq:
  assumes "j0 < Suc b - a" and "j1 < Suc b - a"
  shows "le1 (diagSeq a b) j0 j1 \<longleftrightarrow> j0 \<le> j1"
proof
  assume "le1 (diagSeq a b) j0 j1"
  hence "(nextrel1 (diagSeq a b))\<^sup>*\<^sup>* j0 j1" by (simp add: le1_def)
  thus "j0 \<le> j1" by (rule nextrel1_rtrancl_mono)
next
  assume "j0 \<le> j1"
  hence "(nextrel1 (diagSeq a b))\<^sup>*\<^sup>* j0 j1"
    using assms(2) by (rule nextrel1_diagSeq_rtrancl[rotated])
  thus "le1 (diagSeq a b) j0 j1" using assms by (simp add: le1_def)
qed

text \<open>m (H1): the unified \<open>\<le>\<^sub>M\<close> on a diagonal segment, both rows.  This is the
  empirically-correct form: \<open>leR (diagSeq a b) i j0 j1 = (j0 \<le> j1)\<close> for
  \<open>i \<in> {0,1}\<close> (the task's \<open>i=1 \<Rightarrow> j0 = j1\<close> guess is FALSE \<open>-\<close> the diagonal
  carries full row-1 edges via @{thm [source] nextR1_diagSeq}).\<close>

lemma leR_diagSeq:
  assumes "i \<in> {0,1}" and "j0 < Suc b - a" and "j1 < Suc b - a"
  shows "leR (diagSeq a b) i j0 j1 \<longleftrightarrow> j0 \<le> j1"
  using assms le0_diagSeq[OF assms(2,3)] le1_diagSeq[OF assms(2,3)]
  by (auto simp: leR_def)

lemma le1_shiftRow0_eq:
  assumes M: "M \<in> T_PS" and mono: "monoT M"
  shows "le1 (shiftRow0 M) j0 j1 = le1 M j0 j1"
proof -
  have "nextrel1 (shiftRow0 M) = nextrel1 M"
    by (rule nextrel1_shiftRow0_eq[OF M mono])
  thus ?thesis by (simp add: le1_def Lng_shiftRow0)
qed

text \<open>m: full \<open>leR\<close> invariance under the row-0 shift \<open>shiftRow0\<close> (both rows).
  This is the §6.5 L4 helper: \<open>(i,j0) \<le>\<^sub>M (i,j1)\<close> is preserved for \<open>i \<in> {0,1}\<close>.\<close>

lemma leR_shiftRow0_eq:
  assumes M: "M \<in> T_PS" and mono: "monoT M"
  shows "leR (shiftRow0 M) i j0 j1 = leR M i j0 j1"
  by (simp add: leR_def le0_shiftRow0_eq[OF M mono] le1_shiftRow0_eq[OF M mono])

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

lemma le1_rebaseRow0_eq:
  assumes lb: "\<And>j. j < Lng M \<Longrightarrow> c \<le> entry M 0 j"
  shows "le1 (rebaseRow0 c d M) j0 j1 = le1 M j0 j1"
proof -
  have "nextrel1 (rebaseRow0 c d M) = nextrel1 M"
    by (intro ext) (rule nextrel1_rebaseRow0_eq[OF lb])
  thus ?thesis by (simp add: le1_def)
qed

lemma leR_rebaseRow0_eq:
  assumes lb: "\<And>j. j < Lng M \<Longrightarrow> c \<le> entry M 0 j"
  shows "leR (rebaseRow0 c d M) i j0 j1 = leR M i j0 j1"
  by (simp add: leR_def le0_rebaseRow0_eq[OF lb] le1_rebaseRow0_eq[OF lb])

text \<open>The branch-5 re-basing of the suffix \<open>seg N m\<^sub>1\<^sub>0 (Lng N - 1)\<close> preserves
  \<open>leR\<close> against \<open>N\<close> at the shifted indices.  The slice's being \<open>monoT\<close> (the
  article [18] \<open>PT\<^sub>PS\<close>-anchoring) makes its left end the row-0 minimum, hence the
  re-base is order-preserving.  Feeds L5 with
  @{thm [source] m_6_5_monoT_Red_fact2a_leR_shift}.\<close>

lemma redle_branch5_rebase:
  assumes Sps: "seg N m10 (Lng N - 1) \<in> T_PS"
    and Smono: "monoT (seg N m10 (Lng N - 1))"
    and m10lt: "m10 < Lng N"
    and i: "i = 0 \<or> i = 1"
    and aL: "a < Lng N - m10" and bL: "b < Lng N - m10"
  shows "leR (rebaseRow0 (entry N 0 m10) (entry N 1 m10) (seg N m10 (Lng N - 1)))
              i a b
         = leR N i (a + m10) (b + m10)"
proof -
  let ?S = "seg N m10 (Lng N - 1)"
  let ?c = "entry N 0 m10"
  let ?d = "entry N 1 m10"
  have jN: "Lng N - 1 < Lng N" using m10lt by simp
  have LS: "Lng ?S = Lng N - m10" using m10lt by (simp del: upt_Suc)
  \<comment> \<open>left end of the slice is its row-0 minimum (anchoring)\<close>
  have e0S0: "entry ?S 0 0 = ?c"
  proof -
    have "0 < Lng ?S" using LS aL bL by simp
    hence "entry ?S 0 0 = entry N 0 (m10 + 0)" by (rule entry_seg)
    thus ?thesis by simp
  qed
  have lb: "\<And>j. j < Lng ?S \<Longrightarrow> ?c \<le> entry ?S 0 j"
  proof -
    fix j assume jL: "j < Lng ?S"
    show "?c \<le> entry ?S 0 j"
    proof (cases "j = 0")
      case True thus ?thesis using e0S0 by simp
    next
      case False
      hence "0 < j" by simp
      from monoT_row0_min[OF Sps Smono this jL] have "entry ?S 0 0 < entry ?S 0 j" .
      thus ?thesis using e0S0 by simp
    qed
  qed
  \<comment> \<open>step (ii): row-0 affine shift invariance on the slice\<close>
  have shift: "leR (rebaseRow0 ?c ?d ?S) i a b = leR ?S i a b"
    by (rule leR_rebaseRow0_eq[OF lb])
  \<comment> \<open>step (i): seg-extraction transfer\<close>
  have aLS: "a \<le> (Lng N - 1) - m10" using aL by simp
  have bLS: "b \<le> (Lng N - 1) - m10" using bL by simp
  have m10le: "m10 \<le> Lng N - 1" using m10lt by simp
  have seg: "leR ?S i a b = leR N i (a + m10) (b + m10)"
  proof (cases "i = 0")
    case True
    have "leR ?S 0 a b = le0 ?S a b" by (simp add: leR_def)
    also have "\<dots> = le0 N (m10 + a) (m10 + b)"
      using adm_le0_seg[OF jN aLS bLS m10le] by simp
    also have "\<dots> = leR N 0 (a + m10) (b + m10)" by (simp add: leR_def add.commute)
    finally show ?thesis using True by simp
  next
    case False
    hence i1: "i = 1" using i by simp
    have "leR ?S 1 a b = le1 ?S a b" by (simp add: leR_def)
    also have "\<dots> = le1 N (m10 + a) (m10 + b)"
      using adm_le1_seg[OF jN aLS bLS m10le] by simp
    also have "\<dots> = leR N 1 (a + m10) (b + m10)" by (simp add: leR_def add.commute)
    finally show ?thesis using i1 by simp
  qed
  show ?thesis using shift seg by simp
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

text \<open>§6.8 prop1 reduction.  For a mono \<open>M'\<close>, \<open>descending (Br M')\<close> follows from
  the row-1 tie-break stated at the \<^emph>\<open>FirstNodes\<close> positions of \<open>M'\<close>: the row-0
  part is @{thm [source] m_6_4_P_leftend_mono} on the branch segment, and the
  row-1 part is the hypothesis \<open>tie\<close> transported through
  @{thm [source] entry_FirstNodes_eq_component_gen}.  This isolates the remaining
  hard obligation of \<open>p_6_8_standard_slice_Br_descending\<close> (see
  \<open>docs/slice-Br-descending.md\<close>) into the \<open>FirstNodes\<close> tie-break.\<close>

lemma descending_Br_of_FN_tiebreak:
  assumes M': "M' \<in> PT_PS"
    and tie: "\<And>J0 J1. J0 \<le> J1 \<Longrightarrow> J1 < length (Br M') \<Longrightarrow>
                entry M' 0 (FirstNodes M' ! J0) = entry M' 0 (FirstNodes M' ! J1) \<Longrightarrow>
                entry M' 1 (FirstNodes M' ! J1) \<le> entry M' 1 (FirstNodes M' ! J0)"
  shows "descending (Br M')"
proof (cases "Br M' = []")
  case True
  thus ?thesis by (simp add: descending_def)
next
  case False
  have MT: "M' \<in> T_PS" using M' by (simp add: PT_PS_def)
  have tb: "TrMax M' \<le> Lng M' - 1" by (rule TrMax_bound[OF MT])
  have trne: "TrMax M' \<noteq> Lng M' - 1"
  proof
    assume "TrMax M' = Lng M' - 1"
    hence "Br M' = []" by (simp add: Br_def)
    with False show False by simp
  qed
  from trne tb have trlt: "TrMax M' < Lng M' - 1" by linarith
  let ?Y = "seg M' (TrMax M' + 1) (Lng M' - 1)"
  have brQ: "Br M' = P ?Y" using trne by (simp add: Br_def)
  have NLpos: "Lng ?Y > 0" using trlt by simp
  have Yne: "?Y \<noteq> []" using NLpos length_greater_0_conv by blast
  have YT: "?Y \<in> T_PS" using Yne by (simp add: T_PS_def)
  show ?thesis
    unfolding descending_def
  proof (intro allI impI)
    fix J0 J1
    assume H: "J0 \<le> J1 \<and> J1 \<le> Lng (Br M') - 1"
    from H have le: "J0 \<le> J1" and j1: "J1 \<le> Lng (Br M') - 1" by auto
    have J1lt: "J1 < length (Br M')" using j1 False by (cases "Br M'") auto
    have J0lt: "J0 < length (Br M')" using le J1lt by linarith
    have j1Y: "J1 \<le> Lng (P ?Y) - 1" using j1 brQ by simp
    have r0: "entry (Br M' ! J1) 0 0 \<le> entry (Br M' ! J0) 0 0"
      using m_6_4_P_leftend_mono[OF YT le j1Y] brQ by simp
    have tieB: "entry (Br M' ! J0) 0 0 = entry (Br M' ! J1) 0 0
                \<Longrightarrow> entry (Br M' ! J1) 1 0 \<le> entry (Br M' ! J0) 1 0"
    proof -
      assume eq: "entry (Br M' ! J0) 0 0 = entry (Br M' ! J1) 0 0"
      have c00: "entry M' 0 (FirstNodes M' ! J0) = entry (Br M' ! J0) 0 0"
        by (rule entry_FirstNodes_eq_component_gen[OF M' J0lt])
      have c01: "entry M' 0 (FirstNodes M' ! J1) = entry (Br M' ! J1) 0 0"
        by (rule entry_FirstNodes_eq_component_gen[OF M' J1lt])
      have c10: "entry M' 1 (FirstNodes M' ! J0) = entry (Br M' ! J0) 1 0"
        by (rule entry_FirstNodes_eq_component_gen[OF M' J0lt])
      have c11: "entry M' 1 (FirstNodes M' ! J1) = entry (Br M' ! J1) 1 0"
        by (rule entry_FirstNodes_eq_component_gen[OF M' J1lt])
      have eqFN: "entry M' 0 (FirstNodes M' ! J0) = entry M' 0 (FirstNodes M' ! J1)"
        using c00 c01 eq by simp
      have "entry M' 1 (FirstNodes M' ! J1) \<le> entry M' 1 (FirstNodes M' ! J0)"
        by (rule tie[OF le J1lt eqFN])
      thus "entry (Br M' ! J1) 1 0 \<le> entry (Br M' ! J0) 1 0" using c10 c11 by simp
    qed
    from r0 tieB show "entry (Br M' ! J1) 0 0 \<le> entry (Br M' ! J0) 0 0
          \<and> (entry (Br M' ! J0) 0 0 = entry (Br M' ! J1) 0 0
             \<longrightarrow> entry (Br M' ! J1) 1 0 \<le> entry (Br M' ! J0) 1 0)" by blast
  qed
qed

text \<open>Fast accessor for \<open>descending\<close> (avoids unfolding the \<open>\<forall>\<close> in context, which
  makes \<open>blast\<close>/\<open>simp\<close> explode).\<close>

lemma descendingD:
  assumes "descending Q" "J0 \<le> J1" "J1 \<le> Lng Q - 1"
  shows "entry (Q ! J1) 0 0 \<le> entry (Q ! J0) 0 0
       \<and> (entry (Q ! J0) 0 0 = entry (Q ! J1) 0 0
          \<longrightarrow> entry (Q ! J1) 1 0 \<le> entry (Q ! J0) 1 0)"
  using assms unfolding descending_def by blast

text \<open>Appending one component preserves \<open>descending\<close> iff the new last component
  \<open>x\<close> is \<open>\<le>\<close> the previous last in the descending order — because in a descending
  list the last element is the \<open>\<le>\<close>-minimum.  This drives the slice-length
  induction for \<open>slice_P_descending\<close> (\<open>P (seg M a b) = P (prefix) @ [last]\<close>).\<close>

lemma descending_snoc:
  assumes dQ: "descending Q" and ne: "Q \<noteq> []"
    and r0: "entry x 0 0 \<le> entry (last Q) 0 0"
    and r1: "entry (last Q) 0 0 = entry x 0 0 \<longrightarrow> entry x 1 0 \<le> entry (last Q) 1 0"
  shows "descending (Q @ [x])"
  unfolding descending_def
proof (intro allI impI)
  fix J0 J1
  assume H: "J0 \<le> J1 \<and> J1 \<le> Lng (Q @ [x]) - 1"
  from H have le: "J0 \<le> J1" and j1: "J1 \<le> length Q" by auto
  let ?L = "length Q - 1"
  have lastQ: "last Q = Q ! ?L" using ne by (simp add: last_conv_nth)
  show "entry ((Q @ [x]) ! J1) 0 0 \<le> entry ((Q @ [x]) ! J0) 0 0
        \<and> (entry ((Q @ [x]) ! J0) 0 0 = entry ((Q @ [x]) ! J1) 0 0
           \<longrightarrow> entry ((Q @ [x]) ! J1) 1 0 \<le> entry ((Q @ [x]) ! J0) 1 0)"
  proof (cases "J1 < length Q")
    case True
    \<comment> \<open>both indices land in \<open>Q\<close>\<close>
    have e0: "(Q @ [x]) ! J0 = Q ! J0" using le True by (simp add: nth_append)
    have e1: "(Q @ [x]) ! J1 = Q ! J1" using True by (simp add: nth_append)
    have j1Q: "J1 \<le> Lng Q - 1" using True by simp
    show ?thesis using descendingD[OF dQ le j1Q] e0 e1 by simp
  next
    case False
    hence J1eq: "J1 = length Q" using j1 by linarith
    have ex1: "(Q @ [x]) ! J1 = x" using J1eq by (simp add: nth_append)
    show ?thesis
    proof (cases "J0 = length Q")
      case True
      \<comment> \<open>\<open>J0 = J1 = length Q\<close>: both point at \<open>x\<close>, reflexive\<close>
      have "(Q @ [x]) ! J0 = x" using True by (simp add: nth_append)
      thus ?thesis using ex1 by simp
    next
      case False
      hence J0lt: "J0 < length Q" using le J1eq by linarith
      have J0L: "J0 \<le> ?L" using J0lt by linarith
      have e0: "(Q @ [x]) ! J0 = Q ! J0" using J0lt by (simp add: nth_append)
      \<comment> \<open>\<open>Q ! J0\<close> dominates \<open>last Q\<close> (descending), which dominates \<open>x\<close>\<close>
      have dom: "entry (Q ! ?L) 0 0 \<le> entry (Q ! J0) 0 0
               \<and> (entry (Q ! J0) 0 0 = entry (Q ! ?L) 0 0
                  \<longrightarrow> entry (Q ! ?L) 1 0 \<le> entry (Q ! J0) 1 0)"
        by (rule descendingD[OF dQ J0L order.refl])
      show ?thesis
      proof (intro conjI impI)
        show "entry ((Q @ [x]) ! J1) 0 0 \<le> entry ((Q @ [x]) ! J0) 0 0"
          using ex1 e0 dom r0 lastQ by simp
      next
        assume eq: "entry ((Q @ [x]) ! J0) 0 0 = entry ((Q @ [x]) ! J1) 0 0"
        hence eqx: "entry (Q ! J0) 0 0 = entry x 0 0" using e0 ex1 by simp
        have mid: "entry (Q ! J0) 0 0 = entry (Q ! ?L) 0 0"
          using dom r0 eqx lastQ by simp
        have "entry x 1 0 \<le> entry (Q ! ?L) 1 0" using r1 eqx mid lastQ by simp
        also have "\<dots> \<le> entry (Q ! J0) 1 0" using dom mid by simp
        finally show "entry ((Q @ [x]) ! J1) 1 0 \<le> entry ((Q @ [x]) ! J0) 1 0"
          using ex1 e0 by simp
      qed
    qed
  qed
qed


lemma not_multiT_seg_diagSeq:
  assumes ab: "a \<le> b" and bv: "b \<le> v - u" and uv: "u \<le> v"
  shows "\<not> multiT (seg (diagSeq u v) a b)"
proof -
  have le: "u + a \<le> u + b" using ab by simp
  have "\<not> multiT (diagSeq (u + a) (u + b))" by (rule not_multiT_diagSeq[OF le])
  thus ?thesis using seg_diagSeq[OF ab bv uv] by simp
qed

lemma cdom_refl: "cdom C C" by (simp add: cdom_def)

text \<open>In particular a list of identical components is descending.\<close>

lemma descending_replicate: "descending (replicate m C)"
proof (rule descending_const_head)
  fix J assume "J < Lng (replicate m C)"
  hence "J < m" by simp
  thus "entry (replicate m C ! J) 0 0 = entry C 0 0
        \<and> entry (replicate m C ! J) 1 0 = entry C 1 0" by simp
qed

text \<open>§6.8 命題1 d0pos closure — the irreducible standardness core (N-local
  adjacent row-0 tie).  In a standard sequence \<open>N \<in> S\<^sub>kT\<^sub>PS k\<close>, an ADJACENT
  row-0 tie \<open>entry N 0 j = entry N 0 (Suc j)\<close> forces row-1 to weakly DECREASE:
  \<open>entry N 1 (Suc j) \<le> entry N 1 j\<close>.  Empirically (\<open>python/d1pos_b2_local.py\<close>):
  604/604 at len 6 / val 2, 0 failures.  Adjacency is essential — the non-
  adjacent version is FALSE (370/372), and it is NOT reducible to \<open>N\<close>'s
  P-components (23/142), nor to the cheap nextrel0-parent route
  (\<open>parent N 0 (Suc j) = j\<close> holds in 0/604 cases).  Proof: induction on the
  rank \<open>k\<close>, mirroring @{thm [source] SkT_P_descending}.  The boundary case of
  the \<open>oper\<close> step is the genuine content: a block-boundary tie either folds back
  through the \<open>nextrel1\<close>-parent (\<open>i\<^sub>1=1\<close>) or is vacuous/equality (\<open>i\<^sub>1=0\<close>).\<close>

lemma nlocal_adj_tie:
  shows "N \<in> SkT_PS k \<Longrightarrow> Suc j < Lng N \<Longrightarrow> entry N 0 j = entry N 0 (Suc j)
         \<Longrightarrow> entry N 1 (Suc j) \<le> entry N 1 j"
proof -
  have "\<forall>N. N \<in> SkT_PS k \<longrightarrow>
          (\<forall>j. Suc j < Lng N \<and> entry N 0 j = entry N 0 (Suc j)
             \<longrightarrow> entry N 1 (Suc j) \<le> entry N 1 j)"
  proof (induction k)
    case 0
    show ?case
    proof (intro allI impI)
      fix N j
      assume N0: "N \<in> SkT_PS 0"
        and A: "Suc j < Lng N \<and> entry N 0 j = entry N 0 (Suc j)"
      from N0 obtain u v where Nuv: "N = diagSeq u v" and uv: "u \<le> v" by auto
      have lt: "Suc j < Lng N" using A by simp
      have jlt: "j < Suc v - u" using lt Nuv by simp
      have sjlt: "Suc j < Suc v - u" using lt Nuv by simp
      have e0j: "entry N 0 j = u + j"
        using Nuv jlt by (simp add: entry_diagSeq)
      have e0sj: "entry N 0 (Suc j) = u + Suc j"
        using Nuv sjlt by (simp add: entry_diagSeq)
      have "entry N 0 j \<noteq> entry N 0 (Suc j)" using e0j e0sj by simp
      thus "entry N 1 (Suc j) \<le> entry N 1 j" using A by simp
    qed
  next
    case (Suc k)
    note IHk = Suc.IH
    show ?case
    proof (intro allI impI)
      fix N j
      assume NS: "N \<in> SkT_PS (Suc k)"
        and A: "Suc j < Lng N \<and> entry N 0 j = entry N 0 (Suc j)"
      from NS obtain M n where Neq: "N = (M::pairseq)[n]"
        and MS: "M \<in> SkT_PS k" and n1: "1 \<le> n" by auto
      have MT: "M \<in> T_PS" using MS SkT_PS_subset_ST_PS ST_PS_T_PS by blast
      from A have sjlt: "Suc j < Lng N" and r0eq: "entry N 0 j = entry N 0 (Suc j)" by auto
      let ?j1 = "Lng M - 1"  let ?i1 = "idx1 M ?j1"  let ?j0 = "parent M ?i1 ?j1"
      \<comment> \<open>Degenerate oper guards: \<open>N = Pred M\<close>.  Reduce adjacent ties to \<open>M\<close>, IH.\<close>
      have pred_case: "N = Pred M \<Longrightarrow> entry N 1 (Suc j) \<le> entry N 1 j"
      proof -
        assume Npred: "N = Pred M"
        show "entry N 1 (Suc j) \<le> entry N 1 j"
        proof (cases "Lng M \<le> 1")
          case True
          hence "Pred M = M" by (simp add: Pred_def)
          hence Nm: "N = M" using Npred by simp
          have sjM: "Suc j < Lng M" using sjlt Nm by simp
          have r0M: "entry M 0 j = entry M 0 (Suc j)" using r0eq Nm by simp
          have "entry M 1 (Suc j) \<le> entry M 1 j" using IHk MS sjM r0M by blast
          thus ?thesis using Nm by simp
        next
          case False
          hence Lgt: "1 < Lng M" by simp
          hence Nbl: "N = butlast M" using Npred by (simp add: Pred_def)
          have lbl: "Lng (butlast M) = Lng M - 1" by simp
          have sjbl: "Suc j < Lng M - 1" using sjlt Nbl lbl by simp
          have sjM: "Suc j < Lng M" using sjbl by simp
          have jblbl: "j < length (butlast M)" using sjbl lbl by simp
          have sjblbl: "Suc j < length (butlast M)" using sjbl lbl by simp
          have ej: "entry N i j = entry M i j" for i
            using Nbl jblbl by (simp add: entry_def nth_butlast)
          have esj: "entry N i (Suc j) = entry M i (Suc j)" for i
            using Nbl sjblbl by (simp add: entry_def nth_butlast)
          have r0M: "entry M 0 j = entry M 0 (Suc j)" using r0eq ej esj by simp
          have "entry M 1 (Suc j) \<le> entry M 1 j" using IHk MS sjM r0M by blast
          thus ?thesis using ej esj by simp
        qed
      qed
      show "entry N 1 (Suc j) \<le> entry N 1 j"
      proof (cases "?j1 = 0")
        case True
        hence Nm: "N = M" using Neq by (simp add: oper_def Let_def)
        have "Lng M \<le> 1" using True by simp
        hence "Pred M = M" by (simp add: Pred_def)
        hence "N = Pred M" using Nm by simp
        thus ?thesis using pred_case by simp
      next
        case j1pos: False
        hence Lgt: "1 < Lng M" by simp
        show ?thesis
        proof (cases "entry M 0 ?j1 = 0 \<and> entry M 1 ?j1 = 0")
          case True
          hence "N = Pred M" using Neq j1pos by (simp add: oper_def Let_def)
          thus ?thesis using pred_case by simp
        next
          case notzero: False
          show ?thesis
          proof (cases "hasParent M ?i1 ?j1")
            case False
            hence "N = Pred M" using Neq notzero j1pos by (simp add: oper_def Let_def)
            thus ?thesis using pred_case by simp
          next
            case hp: True
            \<comment> \<open>Expansion branch.  \<open>j\<^sub>0 < j\<^sub>1\<close>, \<open>w = j\<^sub>1 - j\<^sub>0 \<ge> 1\<close>.\<close>
            have parR: "nextR M ?i1 ?j0 ?j1"
              using hp unfolding hasParent_def parent_def by (rule theI')
            have j0lt: "?j0 < ?j1" using poper_nextR_imp_le0[OF parR] by simp
            let ?w = "?j1 - ?j0"
            let ?d0 = "if 0 < ?i1 then entry M 0 ?j1 - entry M 0 ?j0 else 0"
            have w1: "1 \<le> ?w" using j0lt by simp
            have lenN: "Lng N = ?j0 + n * ?w"
            proof -
              let ?B = "\<lambda>k. map (\<lambda>jj. (entry M 0 jj + k * ?d0, entry M 1 jj)) [?j0..<?j1]"
              let ?d1 = "if 1 < ?i1 then entry M 1 ?j1 - entry M 1 ?j0 else 0"
              let ?Braw = "\<lambda>k. map (\<lambda>jj. (entry M 0 jj + k * ?d0, entry M 1 jj + k * ?d1)) [?j0..<?j1]"
              have d1z: "?d1 = 0" using idx1_def[of M ?j1] by (cases "entry M 1 ?j1 > 0") simp_all
              have expand: "M[n] = take ?j0 M @ concat (map ?Braw [0..<n])"
                by (rule poper_oper_expand[OF Lgt notzero hp, of n, unfolded Let_def])
              have t: "length (take ?j0 M) = ?j0" using j0lt Lgt by simp
              have lmap: "map Lng (map ?Braw [0..<n]) = replicate n ?w"
              proof -
                have "map Lng (map ?Braw [0..<n]) = map (\<lambda>k. ?w) [0..<n]" by simp
                thus ?thesis by (simp add: map_replicate_const)
              qed
              have lc: "length (concat (map ?Braw [0..<n])) = n * ?w"
                by (subst length_concat, subst lmap) (simp add: sum_list_replicate)
              show ?thesis using expand t lc Neq by simp
            qed
            \<comment> \<open>Block read: any \<open>x = j\<^sub>0 + q\<cdot>w + s\<close> (\<open>q<n\<close>, \<open>s<w\<close>) reads
               \<open>(entry M 0 (j\<^sub>0+s) + q\<cdot>d\<^sub>0, entry M 1 (j\<^sub>0+s))\<close>.\<close>
            have blk0: "\<And>q s. q < n \<Longrightarrow> s < ?w \<Longrightarrow>
                          entry N 0 (?j0 + q * ?w + s) = entry M 0 (?j0 + s) + q * ?d0"
              using oper_gen_block_entry0[OF Lgt notzero hp j0lt] Neq by simp
            have blk1: "\<And>q s. q < n \<Longrightarrow> s < ?w \<Longrightarrow>
                          entry N 1 (?j0 + q * ?w + s) = entry M 1 (?j0 + s)"
              using oper_gen_block_entry1[OF Lgt notzero hp j0lt] Neq by simp
            have pre: "\<And>x i. x < ?j0 \<Longrightarrow> entry N i x = entry M i x"
              using oper_gen_nth_prefix[OF Lgt notzero hp] Neq by (simp add: entry_def)
            \<comment> \<open>Position decomposition of \<open>Suc j < Lng N = j\<^sub>0 + n\<cdot>w\<close>.\<close>
            have sjN: "Suc j < ?j0 + n * ?w" using sjlt lenN by simp
            show ?thesis
            proof (cases "Suc j \<le> ?j0")
              case prefix: True
              \<comment> \<open>both in prefix \<open>[0,j\<^sub>0]\<close>: junction \<open>j\<^sub>0\<close> reads block-0 \<open>= entry M _ j\<^sub>0\<close>.\<close>
              have jlt: "j < ?j0" using prefix by simp
              have ej: "\<And>i. entry N i j = entry M i j" using pre[OF jlt] by simp
              have esj: "\<And>i. entry N i (Suc j) = entry M i (Suc j)"
              proof (cases "Suc j < ?j0")
                case True
                fix i show "entry N i (Suc j) = entry M i (Suc j)" using pre[OF True] by simp
              next
                case False
                hence sjeq: "Suc j = ?j0" using prefix by linarith
                fix i
                have e0: "entry N 0 (?j0 + 0 * ?w + 0) = entry M 0 (?j0 + 0) + 0 * ?d0"
                  by (rule blk0[OF _ ]) (use n1 w1 in auto)
                have e1: "entry N 1 (?j0 + 0 * ?w + 0) = entry M 1 (?j0 + 0)"
                  by (rule blk1[OF _ ]) (use n1 w1 in auto)
                show "entry N i (Suc j) = entry M i (Suc j)"
                  using e0 e1 sjeq by (cases "i = 0") (simp_all add: entry_def)
              qed
              have r0M: "entry M 0 j = entry M 0 (Suc j)" using r0eq ej esj by simp
              have sjM: "Suc j < Lng M" using prefix j0lt by simp
              have "entry M 1 (Suc j) \<le> entry M 1 j" using IHk MS sjM r0M by blast
              thus ?thesis using ej esj by simp
            next
              case AB: False
              hence j0lej: "?j0 \<le> j" by simp
              \<comment> \<open>\<open>Suc j\<close> sits in some block; locate \<open>j\<close>'s block/offset.\<close>
              define s where "s = (j - ?j0) mod ?w"
              define q where "q = (j - ?j0) div ?w"
              have w0: "0 < ?w" using w1 by simp
              have sw: "s < ?w" using w0 by (simp add: s_def)
              have jsplit: "j = ?j0 + q * ?w + s"
                using j0lej div_mult_mod_eq[of "j - ?j0" ?w]
                by (simp add: s_def q_def algebra_simps)
              have jblk: "j < ?j0 + n * ?w" using sjN by simp
              have qn: "q < n"
              proof -
                have "q * ?w + s < n * ?w" using jblk jsplit by linarith
                hence "q * ?w < n * ?w" using sw by linarith
                thus ?thesis using w0 by simp
              qed
              show ?thesis
              proof (cases "s + 1 < ?w")
                case within: True
                \<comment> \<open>(ii) both inside block \<open>q\<close>: \<open>Suc j = j\<^sub>0 + q\<cdot>w + (s+1)\<close>.\<close>
                have sjsplit: "Suc j = ?j0 + q * ?w + (s + 1)" using jsplit by simp
                have e0j: "entry N 0 j = entry M 0 (?j0 + s) + q * ?d0"
                  using blk0[OF qn sw] jsplit by simp
                have e0sj: "entry N 0 (Suc j) = entry M 0 (?j0 + (s+1)) + q * ?d0"
                  using blk0[OF qn within] sjsplit by simp
                have e1j: "entry N 1 j = entry M 1 (?j0 + s)"
                  using blk1[OF qn sw] jsplit by simp
                have e1sj: "entry N 1 (Suc j) = entry M 1 (?j0 + (s+1))"
                  using blk1[OF qn within] sjsplit by simp
                have r0M: "entry M 0 (?j0 + s) = entry M 0 (?j0 + (s+1))"
                  using r0eq e0j e0sj by simp
                have sjM: "Suc (?j0 + s) < Lng M" using within sw j0lt by simp
                have r0M': "entry M 0 (?j0 + s) = entry M 0 (Suc (?j0 + s))" using r0M by simp
                have "entry M 1 (Suc (?j0 + s)) \<le> entry M 1 (?j0 + s)"
                  using IHk MS sjM r0M' by blast
                hence "entry M 1 (?j0 + (s+1)) \<le> entry M 1 (?j0 + s)" by simp
                thus ?thesis using e1j e1sj by simp
              next
                case boundary: False
                \<comment> \<open>(iii) \<open>s = w-1\<close> (end of block \<open>q\<close>), \<open>Suc j\<close> starts block \<open>q+1\<close>.
                   Abstract \<open>j\<^sub>0, w\<close> to fresh vars to avoid the \<open>w = Lng M-1-j\<^sub>0\<close>
                   double-nat-subtraction linarith loop.\<close>
                have seq: "s = ?w - 1" using boundary sw by linarith
                obtain WW where WWdef: "WW = ?w" and WW1: "1 \<le> WW" using w1 by blast
                obtain JJ where JJdef: "JJ = ?j0" by blast
                have jend: "j = JJ + q * WW + (WW - 1)"
                  using jsplit seq WWdef JJdef by simp
                have sjstart: "Suc j = JJ + (q+1) * WW + 0"
                  using jend WW1 by (simp add: algebra_simps)
                have sjstart': "Suc j = ?j0 + (q+1) * ?w + 0"
                  using sjstart WWdef JJdef by simp
                \<comment> \<open>\<open>q+1 < n\<close> because \<open>Suc j < j\<^sub>0 + n\<cdot>w\<close>.\<close>
                have q1n: "q + 1 < n"
                proof -
                  have sjNW: "Suc j < JJ + n * WW" using sjN WWdef JJdef by simp
                  have "JJ + (q+1) * WW < JJ + n * WW" using sjNW sjstart by simp
                  hence lt: "(q+1) * WW < n * WW" by simp
                  have W0: "0 < WW" using WW1 by simp
                  show ?thesis using lt W0 mult_less_cancel2[of "q+1" WW n] by simp
                qed
                have jend': "j = ?j0 + q * ?w + (?w - 1)"
                  using jend WWdef JJdef by simp
                have w1le: "?w - 1 < ?w" using w0 by simp
                \<comment> \<open>Left endpoint reads \<open>M\<close> at \<open>j\<^sub>1-1\<close> (since \<open>j\<^sub>0 + (w-1) = j\<^sub>1\<close>... wait
                   \<open>j\<^sub>0+(w-1) = j\<^sub>0 + (j\<^sub>1-j\<^sub>0-1) = j\<^sub>1-1\<close>) shifted \<open>q\<close>; right reads \<open>M\<close>
                   at \<open>j\<^sub>0\<close> shifted \<open>q+1\<close>.\<close>
                have j0w1: "?j0 + (?w - 1) = ?j1 - 1" using j0lt by simp
                have e0j: "entry N 0 j = entry M 0 (?j1 - 1) + q * ?d0"
                  using blk0[OF qn w1le] jend' j0w1 by simp
                have e1j: "entry N 1 j = entry M 1 (?j1 - 1)"
                  using blk1[OF qn w1le] jend' j0w1 by simp
                have e0sj: "entry N 0 (Suc j) = entry M 0 ?j0 + (q+1) * ?d0"
                  using blk0[OF q1n w0] sjstart' by simp
                have e1sj: "entry N 1 (Suc j) = entry M 1 ?j0"
                  using blk1[OF q1n w0] sjstart' by simp
                \<comment> \<open>Row-0 tie across the boundary: \<open>M\<^bsub>0,j\<^sub>1-1\<^esub> = M\<^bsub>0,j\<^sub>0\<^esub> + d\<^sub>0\<close>.\<close>
                have tie: "entry M 0 (?j1 - 1) + q * ?d0 = entry M 0 ?j0 + (q+1) * ?d0"
                  using r0eq e0j e0sj by simp
                have tie': "entry M 0 (?j1 - 1) = entry M 0 ?j0 + ?d0"
                  using tie by (simp add: algebra_simps)
                show ?thesis
                proof (cases "?i1 = 0")
                  case i0: True
                  hence d0z: "?d0 = 0" by simp
                  hence tie0: "entry M 0 (?j1 - 1) = entry M 0 ?j0" using tie' by simp
                  have nr0: "nextrel0 M ?j0 ?j1"
                    using parR i0 by (simp add: nextR_def)
                  show ?thesis
                  proof (cases "?w = 1")
                    case wone: True
                    \<comment> \<open>\<open>j\<^sub>0 = j\<^sub>1-1\<close>: both endpoints read \<open>M\<close> at \<open>j\<^sub>0\<close>, equality.\<close>
                    have "?j1 - 1 = ?j0" using wone j0lt by simp
                    hence "entry M 1 (?j1 - 1) = entry M 1 ?j0" by simp
                    thus ?thesis using e1j e1sj by simp
                  next
                    case wgt: False
                    \<comment> \<open>\<open>w \<ge> 2\<close>: \<open>j\<^sub>1-1\<close> is an interior index, so \<open>M\<^bsub>0,j\<^sub>1-1\<^esub> \<ge> M\<^bsub>0,j\<^sub>1\<^esub> > M\<^bsub>0,j\<^sub>0\<^esub>\<close>,
                       contradicting the tie \<open>M\<^bsub>0,j\<^sub>1-1\<^esub> = M\<^bsub>0,j\<^sub>0\<^esub>\<close>.  Vacuous.\<close>
                    have w2: "2 \<le> ?w" using wgt w1 by linarith
                    have interior: "?j0 < ?j1 - 1 \<and> ?j1 - 1 < ?j1" using w2 j0lt by linarith
                    have ge: "entry M 0 (?j1 - 1) \<ge> entry M 0 ?j1"
                      using nr0 interior by (simp add: nextrel0_def)
                    have lt0: "entry M 0 ?j0 < entry M 0 ?j1"
                      using nr0 by (simp add: nextrel0_def)
                    have "entry M 0 ?j0 < entry M 0 (?j1 - 1)" using ge lt0 by linarith
                    thus ?thesis using tie0 by simp
                  qed
                next
                  case i1: False
                  have i1one: "?i1 = 1"
                    using i1 unfolding idx1_def by (cases "entry M 1 ?j1 > 0") simp_all
                  \<comment> \<open>\<open>i\<^sub>1=1\<close>: \<open>d\<^sub>0 = M\<^bsub>0,j\<^sub>1\<^esub> - M\<^bsub>0,j\<^sub>0\<^esub>\<close>; the tie gives \<open>M\<^bsub>0,j\<^sub>1-1\<^esub> = M\<^bsub>0,j\<^sub>1\<^esub>\<close>,
                     an ADJACENT \<open>M\<close>-tie at \<open>(j\<^sub>1-1, j\<^sub>1)\<close>.\<close>
                  have d0v: "?d0 = entry M 0 ?j1 - entry M 0 ?j0" using i1one by simp
                  have nr1: "nextrel1 M ?j0 ?j1"
                    using parR i1one by (simp add: nextR_def)
                  have le0j: "le0 M ?j0 ?j1" using nr1 by (simp add: nextrel1_def)
                  have le0r: "entry M 0 ?j0 \<le> entry M 0 ?j1"
                    using le0j by (simp add: le0_def nextrel0_rtrancl_entry0_mono)
                  have tieM: "entry M 0 (?j1 - 1) = entry M 0 ?j1"
                    using tie' d0v le0r by simp
                  \<comment> \<open>IH on the adjacent \<open>M\<close>-pair \<open>(j\<^sub>1-1, j\<^sub>1)\<close>.\<close>
                  have j1ge1: "1 \<le> ?j1" using j0lt by linarith
                  have sucj1: "Suc (?j1 - 1) = ?j1" using j1ge1 by simp
                  have sjM: "Suc (?j1 - 1) < Lng M" using sucj1 Lgt by simp
                  have r0Madj: "entry M 0 (?j1 - 1) = entry M 0 (Suc (?j1 - 1))"
                    using tieM sucj1 by simp
                  have IHadj: "entry M 1 (Suc (?j1 - 1)) \<le> entry M 1 (?j1 - 1)"
                    using IHk MS sjM r0Madj by blast
                  have IHj1: "entry M 1 ?j1 \<le> entry M 1 (?j1 - 1)" using IHadj sucj1 by simp
                  \<comment> \<open>\<open>nextrel1\<close>: \<open>M\<^bsub>1,j\<^sub>0\<^esub> < M\<^bsub>1,j\<^sub>1\<^esub>\<close>.\<close>
                  have lt1: "entry M 1 ?j0 < entry M 1 ?j1" using nr1 by (simp add: nextrel1_def)
                  \<comment> \<open>Chain: \<open>M\<^bsub>1,j\<^sub>0\<^esub> < M\<^bsub>1,j\<^sub>1\<^esub> \<le> M\<^bsub>1,j\<^sub>1-1\<^esub>\<close>.  Goal: \<open>N\<^bsub>1,Suc j\<^esub> = M\<^bsub>1,j\<^sub>0\<^esub> \<le> M\<^bsub>1,j\<^sub>1-1\<^esub> = N\<^bsub>1,j\<^esub>\<close>.\<close>
                  have "entry M 1 ?j0 \<le> entry M 1 (?j1 - 1)" using lt1 IHj1 by linarith
                  thus ?thesis using e1j e1sj by simp
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  thus "N \<in> SkT_PS k \<Longrightarrow> Suc j < Lng N \<Longrightarrow> entry N 0 j = entry N 0 (Suc j)
         \<Longrightarrow> entry N 1 (Suc j) \<le> entry N 1 j" by blast
qed

lemma oper_d1pos_Br_comp_mono:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and Qdef: "Q = seg ((M::pairseq)[n]) a b"
    and QT: "Q \<in> T_PS"
    and JL: "J < Lng (P Q)"
  shows "monoT (P Q ! J) \<or> zeroT (P Q ! J)"
proof -
  \<comment> \<open>\<open>P\<close> decomposes \<open>Q \<in> T_PS\<close> into non-multi (zero/mono) components
     (@{thm [source] m_6_2_P_components_1}); read it at the index \<open>J\<close>.\<close>
  have mem: "P Q ! J \<in> set (P Q)" using JL by (rule nth_mem)
  have "zeroT (P Q ! J) \<or> monoT (P Q ! J)"
    using m_6_2_P_components_1[OF QT] mem by blast
  thus ?thesis by blast
qed

text \<open>§6.8 d0pos ¬brle take-map combinator (agent-A): if the \<open>Jm\<close>-prefixes of two
  \<open>Br\<close>-lists are \<open>P\<close> of an \<open>IncrFirst\<^sup>s\<close>-shift pair, the prefixes are the shift-map.
  A small helper toward the existential identification stub (uses @{thm [source]
  P_funpow_IncrFirst}).\<close>

lemma oper_d1pos_notbrle_take_map:
  fixes Jm :: nat
  assumes leg1: "take Jm B1 = P R1"
    and leg2: "take Jm B2 = P R2"
    and leg3: "R1 = (IncrFirst ^^ s) R2"
  shows "take Jm B1 = map (IncrFirst ^^ s) (take Jm B2)"
proof -
  have "take Jm B1 = P R1" by (rule leg1)
  also have "\<dots> = P ((IncrFirst ^^ s) R2)" using leg3 by simp
  also have "\<dots> = map (IncrFirst ^^ s) (P R2)" by (rule P_funpow_IncrFirst)
  also have "\<dots> = map (IncrFirst ^^ s) (take Jm B2)" using leg2 by simp
  finally show ?thesis .
qed

text \<open>§6.8 d1pos \<open>\<not>brle\<close> REGIME B lowshift — EXACT plug-in form (conc-A,
  \<open>j\<^sub>m\<^sub>2 \<le> j'\<^sub>0\<close>).  Repackages @{thm [source] oper_d1pos_branch_lowshift_regB}
  (whose base is the \<open>N\<close>-slice \<open>seg N (jm2+s0) (jm2+(s0+(cc-1)))\<close>) into the form
  that plugs DIRECTLY into @{thm [source] oper_d1pos_branch_collapse_concrete}:
  with \<open>base = seg Snside 0 (cN-1)\<close> (so @{thm [source] oper_d1pos_branch_butl}
  supplies \<open>butlast (P Snside) = P base\<close>), given the deep-verified base-equality
  \<open>baseEq\<close>: \<open>seg N (jm2+s0) (jm2+(s0+(cc-1))) = seg Snside 0 (cN-1)\<close> (the residual
  block-fold / first-node geometry, 1128/1128 at rank 8, /tmp/regB_base.py).
  Pure rewrite of the regime-B lowshift along \<open>baseEq\<close>.\<close>

lemma oper_d1pos_branch_lowshift_regB_plug:
  fixes N :: pairseq
  defines "jm2 \<equiv> parent N 1 (Lng N - 1)"
      and "w \<equiv> Lng N - 1 - parent N 1 (Lng N - 1)"
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and qn: "q < n"
    and Aform: "A = jm2 + q * w + s0"
    and s0e0: "s0 \<le> s0 + (cc - 1)"
    and e0lt: "s0 + (cc - 1) < w"
    and Ele: "A \<le> E" and ccle: "cc - 1 \<le> E - A"
    and baseEq: "seg N (jm2 + s0) (jm2 + (s0 + (cc - 1))) = seg Snside 0 (cN - 1)"
  shows "seg (seg ((N::pairseq)[n]) A E) 0 (cc - 1)
       = (IncrFirst ^^ (q * (entry N 0 (Lng N - 1) - entry N 0 jm2)))
            (seg Snside 0 (cN - 1))"
proof -
  have base: "seg (seg ((N::pairseq)[n]) A E) 0 (cc - 1)
       = (IncrFirst ^^ (q * (entry N 0 (Lng N - 1) - entry N 0 jm2)))
            (seg N (jm2 + s0) (jm2 + (s0 + (cc - 1))))"
    unfolding jm2_def w_def
    by (rule oper_d1pos_branch_lowshift_regB[OF L notzero hp i1z j0lt qn
          Aform[unfolded jm2_def w_def] s0e0 e0lt[unfolded w_def] Ele ccle])
  show ?thesis using base baseEq by simp
qed

text \<open>§6.8 d1pos FULL-PAIR verbatim agreement BELOW the boundary.  At every index
  \<open>x < Lng N-1\<close> the WHOLE pair of \<open>N[n]\<close> equals \<open>N\<close>'s (both rows): the prefix
  \<open>x < j\<^sub>m\<^sub>2\<close> is @{thm [source] oper_d1pos_nth_prefix}, and block 0 (\<open>j\<^sub>m\<^sub>2 \<le> x < Lng N-1\<close>,
  \<open>q=0\<close>, shift \<open>0\<cdot>\<delta>=0\<close>, row-1 unshifted) is @{thm [source] oper_d1pos_nth} at \<open>q=0\<close>.
  Unlike @{thm [source] oper_d1pos_row0_agree}, the boundary itself is EXCLUDED (where
  row-1 folds).  DEEP-VERIFIED (/tmp/fullpair_below.py: 0/3969 bad).\<close>

lemma oper_d1pos_nth_below:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and bnd: "Lng N - 1 < Lng ((N::pairseq)[n])"
    and x: "x < Lng N - 1"
  shows "((N::pairseq)[n]) ! x = N ! x"
proof -
  let ?j0 = "parent N 1 (Lng N - 1)"  let ?w = "Lng N - 1 - ?j0"
  let ?delta = "entry N 0 (Lng N - 1) - entry N 0 ?j0"
  have w0: "0 < ?w" using j0lt by linarith
  have LngNn: "Lng ((N::pairseq)[n]) = ?j0 + n * ?w"
    by (rule oper_d1pos_LngM[OF L notzero hp i1z j0lt])
  have n1: "1 < n"
  proof -
    have "?j0 + ?w < ?j0 + n * ?w" using bnd LngNn j0lt by linarith
    hence "?w < n * ?w" by linarith
    thus ?thesis using w0 by (cases n) auto
  qed
  show ?thesis
  proof (cases "x < ?j0")
    case True
    show ?thesis by (rule oper_d1pos_nth_prefix[OF L notzero hp i1z True])
  next
    case False
    hence ge: "?j0 \<le> x" by simp
    have s: "x - ?j0 < ?w" using x ge by linarith
    have q0n: "(0::nat) < n" using n1 by simp
    have split: "x = ?j0 + 0 * ?w + (x - ?j0)" using ge by simp
    have "((N::pairseq)[n]) ! (?j0 + 0 * ?w + (x - ?j0))
          = (entry N 0 (?j0 + (x - ?j0)) + 0 * ?delta, entry N 1 (?j0 + (x - ?j0)))"
      by (rule oper_d1pos_nth[OF L notzero hp i1z j0lt q0n s])
    hence "((N::pairseq)[n]) ! x = (entry N 0 x, entry N 1 x)"
      using split ge by simp
    thus ?thesis by (simp add: entry_def)
  qed
qed

text \<open>§6.8 d1pos \<open>tnc\<close>/\<open>stop\<close> context dischargers.  Both regime assembly lemmas use
  the witnesses \<open>j\<^sub>0\<^sup>red = j'\<^sub>0\<close>, \<open>j\<^sub>1\<^sup>red = Lng N-1\<close>, \<open>shamt = 0\<close>, so they need the
  reference-trunk confinement \<open>tnc : TrMax (seg N j'\<^sub>0 (Lng N-1)) \<le> Lng N-1-1-j'\<^sub>0\<close>
  and the boundary stop \<open>stop : \<not> nextR (seg (N[n]) j'\<^sub>0 j'\<^sub>1) 1 (TrMax (seg N j'\<^sub>0 (Lng N-1)))
  (TrMax (seg N j'\<^sub>0 (Lng N-1)) + 1)\<close>.  Both reduce to the keystone
  @{thm [source] TrMax_eq_of_prefix_agree_sym}: \<open>M' = seg (N[n]) j'\<^sub>0 j'\<^sub>1\<close> and
  \<open>N\<^sub>red = seg N j'\<^sub>0 (Lng N-1)\<close> agree pointwise on the shared prefix \<open>[0,c]\<close>
  (\<open>c = Lng N-1-1-j'\<^sub>0\<close>; both verbatim there by @{thm [source] oper_d1pos_nth_below}
  since the right end \<open>j'\<^sub>0+c = Lng N-2 < Lng N-1\<close>), the \<open>M'\<close>-side strict-2 confinement
  \<open>TrMax M'+1 \<le> c\<close> and the \<open>M'\<close>-side boundary stop \<open>\<not>nextR M' 1 (TrMax M')(TrMax M'+1)\<close>
  (@{thm [source] TrMax_stop} from \<open>Mlt\<close>) come from the FIRST \<open>\<not>brle\<close> conjunct exactly as
  in @{thm [source] TrMax_seg_oper_d1pos_eq_notbrle_uncapped} (the \<open>tncM1\<close>/\<open>stopM\<close> block),
  but here the CAPPED span \<open>j\<^sub>1\<^sup>red = Lng N-1 \<le> j'\<^sub>1\<close> is allowed.  This pins
  \<open>TrEq : TrMax M' = TrMax N\<^sub>red\<close>, whence \<open>tnc\<close> (\<open>= TrMax M' \<le> c\<close>) and \<open>stop\<close>
  (\<open>= stopM\<close> with \<open>TrMax M' = TrMax N\<^sub>red\<close>).  DEEP-VERIFIED rank 10
  (/tmp/d1pos_treq_tnc_stop.py 12 4 10: TrEq/tnc/tncM/stop/agree 3370/3370,
  capped 2157 + uncapped 1213).\<close>

text \<open>§6.8 d1pos \<open>stop\<close>-FROM-\<open>tnc\<close> brick.  Given the reference-trunk confinement
  \<open>tnc : TrMax N\<^sub>red \<le> c\<close> (\<open>c = Lng N\<^sub>red - 2\<close>, so \<open>TrMax N\<^sub>red < Lng N\<^sub>red - 1\<close>) and
  the pointwise prefix agreement \<open>M' = N\<^sub>red\<close> on \<open>[0,c]\<close>, the boundary stop
  \<open>\<not> nextR M' 1 (TrMax N\<^sub>red)(TrMax N\<^sub>red+1)\<close> transfers from the \<open>N\<^sub>red\<close>-side stop
  (@{thm [source] TrMax_stop}): a row-1 step of \<open>M'\<close> at \<open>(TrMax N\<^sub>red, TrMax N\<^sub>red+1)\<close>
  lives in the shared prefix (\<open>TrMax N\<^sub>red+1 \<le> c+1 = Lng N\<^sub>red-1\<close>... actually
  \<open>TrMax N\<^sub>red \<le> c\<close> and \<open>TrMax N\<^sub>red+1 \<le> c+1\<close>; we need both endpoints \<open>\<le> c\<close> which holds
  since \<open>TrMax N\<^sub>red < c\<close> in the strict-2 case, else handled) so transfers to \<open>N\<^sub>red\<close> via
  @{thm [source] nextrel1_prefix_imp}, contradicting @{thm [source] TrMax_stop}.
  This brick needs NO ST_PS and NO brle machinery — it is pure prefix-transfer.\<close>

lemma oper_d1pos_ctx_stop_of_tnc:
  fixes N :: pairseq and M :: pairseq
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and Neq: "M = (N::pairseq)[n]"
    and j0plt: "j0' < Lng N - 1"
    and lt: "j0' < j1'" and jM: "j1' < Lng M"
    and bge: "Lng N - 1 \<le> j1'"
    and tnc: "TrMax (seg N j0' (Lng N - 1)) < Lng N - 1 - 1 - j0'"
  shows "\<not> nextR (seg ((N::pairseq)[n]) j0' j1') 1
                  (TrMax (seg N j0' (Lng N - 1)))
                  (TrMax (seg N j0' (Lng N - 1)) + 1)"
proof -
  let ?M = "(N::pairseq)[n]"
  let ?j1red = "Lng N - 1"
  let ?Mp = "seg ?M j0' j1'"
  let ?Nred = "seg N j0' ?j1red"
  let ?c = "?j1red - 1 - j0'"
  let ?tN = "TrMax ?Nred"
  have MMn: "M = ?M" using Neq .
  have bnd: "?j1red < Lng ?M"
  proof -
    have "?j1red \<le> j1'" using bge .
    thus ?thesis using jM MMn by simp
  qed
  have LMp: "Lng ?Mp = Suc j1' - j0'" by simp
  have LNred: "Lng ?Nred = Suc ?j1red - j0'" by simp
  have j0le: "j0' \<le> j1'" using lt by linarith
  have NredT: "?Nred \<in> T_PS" using j0plt by (simp add: T_PS_def seg_def)
  have cNred: "?c = Lng ?Nred - 2" using LNred j0plt by linarith
  have cM: "?c < Lng ?Mp" using LMp j0plt bge lt by linarith
  have cN: "?c < Lng ?Nred" using LNred j0plt by linarith
  \<comment> \<open>pointwise agreement on \<open>[0,c]\<close>: index \<open>j'\<^sub>0+s \<le> Lng N-2 < Lng N-1\<close>, verbatim\<close>
  have agree: "\<And>s. s \<le> ?c \<Longrightarrow> ?Mp ! s = ?Nred ! s"
  proof -
    fix s assume sc: "s \<le> ?c"
    have sM: "s < Suc j1' - j0'" using sc cM LMp by linarith
    have sNp: "s < Suc ?j1red - j0'" using sc cN LNred by linarith
    have idxlt: "j0' + s < ?j1red" using sc j0plt by linarith
    have eMn: "?M ! (j0' + s) = N ! (j0' + s)"
      by (rule oper_d1pos_nth_below[OF L notzero hp i1z j0lt bnd idxlt])
    have "?Mp ! s = ?M ! (j0' + s)" using sM by (rule seg_nth_eq)
    also have "\<dots> = N ! (j0' + s)" by (rule eMn)
    also have "\<dots> = ?Nred ! s" using sNp by (simp add: seg_nth_eq)
    finally show "?Mp ! s = ?Nred ! s" .
  qed
  \<comment> \<open>\<open>tnc\<close> gives \<open>TrMax Nred < Lng Nred - 1\<close>, hence the \<open>Nred\<close>-side stop\<close>
  have tNlt: "?tN < Lng ?Nred - 1" using tnc cNred cN by linarith
  have stopN: "\<not> nextR ?Nred 1 ?tN (?tN + 1)"
    by (rule TrMax_stop[OF NredT tNlt])
  \<comment> \<open>transfer: a row-1 step of \<open>M'\<close> at \<open>(tN, tN+1)\<close> lies in \<open>[0,c]\<close> (\<open>tN+1 \<le> c\<close> from
     the STRICT \<open>tnc\<close>), so it pushes back to \<open>N\<^sub>red\<close> via @{thm [source] nextrel1_prefix_imp}\<close>
  have tNc: "?tN \<le> ?c" using tnc by linarith
  have tN1c: "?tN + 1 \<le> ?c" using tnc by linarith
  show ?thesis
  proof
    assume "nextR ?Mp 1 ?tN (?tN + 1)"
    hence stepM: "nextrel1 ?Mp ?tN (?tN + 1)" by (simp add: nextR_def)
    have "nextrel1 ?Nred ?tN (?tN + 1)"
      by (rule nextrel1_prefix_imp[OF agree cM cN tNc tN1c stepM])
    hence "nextR ?Nred 1 ?tN (?tN + 1)" by (simp add: nextR_def)
    thus False using stopN by simp
  qed
qed

text \<open>§6.8 d1pos CELL-4 (PERIODIC-TAIL) BOUNDARY sub-cell — the row-0 undercut at
  \<open>Lng N-1\<close>.  The period TOP value \<open>entry N 0 (Lng N-1)\<close> is \<open>\<le>\<close> EVERY interior
  row-0 value strictly between its row-0 parent and itself.  Pure consequence of
  the row-0 parent step @{thm [source] m_5_1_parent_basic_1}: \<open>nextR N 0 p
  (Lng N-1)\<close> means no smaller row-0 value sits in \<open>(p, Lng N-1)\<close>.  With \<open>p < A\<close>
  (the branch-region start sits strictly above the row-0 parent — DEEP-VERIFIED
  448/448 at rank 10, /tmp/perbnd_AN_p0.py, /tmp/perbnd_laststep.py) this undercut
  covers the whole branch tail \<open>[A, Lng N-1)\<close>.\<close>

lemma oper_d1pos_period_boundary_undercut:
  fixes N :: pairseq and p A x :: nat
  assumes NT: "N \<in> T_PS"
    and parR: "nextR N 0 p (Lng N - 1)"
    and pA: "p < A"
    and Ax: "A \<le> x"
    and xlt: "x < Lng N - 1"
  shows "entry N 0 (Lng N - 1) \<le> entry N 0 x"
proof -
  have px: "p < x" using pA Ax by linarith
  have xle: "x \<le> Lng N - 1" using xlt by linarith
  show ?thesis by (rule m_5_1_parent_basic_1[OF NT px xle parR])
qed

text \<open>§6.8 d1pos CELL-4 (PERIODIC-TAIL) BOUNDARY sub-cell — the \<open>mLmin_SnB\<close>
  discharger.  The boundary index \<open>m = Lng Snside - 1\<close> of the period-reduced branch
  region \<open>Snside = seg N A\<^sub>N (Lng N-1)\<close> (\<open>A\<^sub>N = j\<^sub>0\<^sup>red + TrMax N\<^sub>p + 1\<close>, boundary
  \<open>j\<^sub>1\<^sup>red = Lng N-1\<close>) is a row-0 LEFT-MINIMUM: \<open>entry Snside 0 m\<close> reads the period TOP
  \<open>entry N 0 (Lng N-1)\<close> (\<open>A\<^sub>N + m = Lng N-1\<close>) and every earlier \<open>entry Snside 0 j =
  entry N 0 (A\<^sub>N + j)\<close> with \<open>A\<^sub>N + j \<in> [A\<^sub>N, Lng N-1)\<close> is undercut by
  @{thm [source] oper_d1pos_period_boundary_undercut}.  This is the period-reduced
  analogue of the regime-B \<open>mLmin_Sn\<close> hypothesis.  DEEP-VERIFIED rank 10 (KMAX=10,
  len=12): mLmin_SnB 0/448, /tmp/perbnd_check.py.  Residual geometry \<open>parent N 0
  (Lng N-1) < A\<^sub>N\<close> supplied via @{thm [source] m_5_1_parent_exists_1} + uniqueness.\<close>

lemma oper_d1pos_period_boundary_mLmin:
  fixes N :: pairseq and AN :: nat
  assumes NT: "N \<in> T_PS"
    and parR: "nextR N 0 p (Lng N - 1)"
    and pA: "p < AN"
    and ANlt: "AN < Lng N - 1"
  shows "\<forall>j < Lng (seg N AN (Lng N - 1)) - 1.
           entry (seg N AN (Lng N - 1)) 0 (Lng (seg N AN (Lng N - 1)) - 1)
         \<le> entry (seg N AN (Lng N - 1)) 0 j"
proof (intro allI impI)
  let ?Sn = "seg N AN (Lng N - 1)"
  let ?m = "Lng ?Sn - 1"
  fix j assume jm: "j < ?m"
  \<comment> \<open>geometry: \<open>Lng Sn = Suc (Lng N-1) - A\<^sub>N\<close>, \<open>m = Lng N-1 - A\<^sub>N\<close>, \<open>A\<^sub>N + m = Lng N-1\<close>\<close>
  have LSn: "Lng ?Sn = Suc (Lng N - 1) - AN" by (rule Lng_seg)
  have mval: "?m = Lng N - 1 - AN" using LSn ANlt by linarith
  have ANm: "AN + ?m = Lng N - 1" using mval ANlt by linarith
  have mltSn: "?m < Lng ?Sn" using LSn ANlt by linarith
  have jltSn: "j < Lng ?Sn" using jm mltSn by linarith
  \<comment> \<open>read both endpoints off \<open>N\<close>\<close>
  have eSnm: "entry ?Sn 0 ?m = entry N 0 (Lng N - 1)"
    using entry_seg[OF mltSn] ANm by simp
  have eSnj: "entry ?Sn 0 j = entry N 0 (AN + j)" using entry_seg[OF jltSn] by simp
  \<comment> \<open>the interior index \<open>A\<^sub>N + j\<close> lies in \<open>[A\<^sub>N, Lng N-1)\<close>; undercut applies\<close>
  have ANjlt: "AN + j < Lng N - 1" using jm mval by linarith
  have ANjge: "AN \<le> AN + j" by simp
  have "entry N 0 (Lng N - 1) \<le> entry N 0 (AN + j)"
    by (rule oper_d1pos_period_boundary_undercut[OF NT parR pA ANjge ANjlt])
  thus "entry ?Sn 0 ?m \<le> entry ?Sn 0 j" using eSnm eSnj by simp
qed

text \<open>§6.8 d1pos CELL-4 (PERIODIC-TAIL) BOUNDARY sub-cell — the \<open>cleB\<close> discharger
  (the M-side anchor \<open>c = IdxSum (P S) ! (length (P S) - 1)\<close> sits exactly at the
  boundary index \<open>m = Lng Snside - 1\<close>).  Pins \<open>c = m\<close> from two M-side facts about
  \<open>S = seg M A\<^sub>M j'\<^sub>1\<close>:
  (a) \<open>c \<le> m\<close> — \<open>m\<close> STRICTLY undercuts its tail \<open>(m, Lng S-1]\<close>
      (@{thm [source] anchor_lt_of_uniform_witness} at \<open>jj = m\<close>, \<open>k = m+1\<close>);
  (b) \<open>c \<ge> m\<close> — \<open>m\<close> is a row-0 LEFT-MINIMUM of \<open>S\<close> (@{thm [source] anchor_ge_of_leftmin}).
  Both M-side row-0 facts are the period-shift image (\<open>+shamt\<close>, \<open>q\<^sub>0 \<ge> 1\<close>) of the
  \<open>N\<close>-side boundary undercut (@{thm [source] oper_d1pos_period_boundary_undercut} /
  @{thm [source] oper_d1pos_period_boundary_mLmin}); they are the parent's residual
  transfer (deep-verified rank 10: \<open>c=m\<close> 0/448, \<open>m\<close> left-min of \<open>S\<close> 0/448, \<open>m\<close>
  strict-tail-undercut 0/448, /tmp/perbnd_cleB.py).\<close>

lemma oper_d1pos_period_boundary_cle:
  fixes S :: pairseq and m :: nat
  defines "c \<equiv> IdxSum (P S) ! (length (P S) - 1)"
  assumes ST: "S \<in> T_PS" and multi: "1 < length (P S)"
    and mle: "m \<le> Lng S - 1"
    and lmin: "\<forall>j < m. entry S 0 m \<le> entry S 0 j"
    and tailgt: "\<forall>x. m < x \<and> x \<le> Lng S - 1 \<longrightarrow> entry S 0 m < entry S 0 x"
  shows "c = m"
proof -
  \<comment> \<open>\<open>c \<le> m\<close> via the uniform witness at \<open>jj = m\<close>, \<open>k = m+1\<close>\<close>
  have wit: "\<And>x. Suc m \<le> x \<Longrightarrow> x \<le> Lng S - 1 \<Longrightarrow> entry S 0 m < entry S 0 x"
  proof -
    fix x assume xlo: "Suc m \<le> x" and xhi: "x \<le> Lng S - 1"
    have "m < x" using xlo by simp
    thus "entry S 0 m < entry S 0 x" using tailgt xhi by blast
  qed
  have jjlt: "m < Suc m" by simp
  have cle: "c < Suc m" unfolding c_def
    by (rule anchor_lt_of_uniform_witness[OF ST multi jjlt wit])
  hence cleM: "c \<le> m" by simp
  \<comment> \<open>\<open>c \<ge> m\<close> via the left-min bridge\<close>
  have cge: "m \<le> c" unfolding c_def
    by (rule anchor_ge_of_leftmin[OF ST mle]) (use lmin in simp)
  show ?thesis using cleM cge by linarith
qed


lemma lessBP_irrefl: "\<not> lessBP p p"
  using lessBT_lessBP_irrefl[where t = "Trm []" and p = p] by blast

\<comment> \<open>========================================================================
   §8.7 補題（順序数項の基本例） — m_8_7_OT_examples
   content.md 6066-6120.  D_u t = Dpt (enat u) t = Trm [DB (enat u) t].
   ====================================================================== \<close>

\<comment> \<open>helper: D_u 0 is dfree and is an OT-principal with empty G-set, hence in OT_B.\<close>
lemma otb_Dpt_0: "Dpt (enat u) 0\<^sub>B \<in> OT_B"
  by (simp add: OT_B_def OT_def T_B_def)

\<comment> \<open>helper: abbreviation-free unfolding of the n-fold D_u tower.\<close>
lemma otb_tower_Suc:
  "(Dpt (enat u) ^^ Suc n) 0\<^sub>B = Trm [DB (enat u) ((Dpt (enat u) ^^ n) 0\<^sub>B)]"
  by (simp add: funpow_swap1)

\<comment> \<open>helper: the n-fold tower is dfree (in T_B).\<close>
lemma otb_tower_dfree: "dfree_BT ((Dpt (enat u) ^^ n) 0\<^sub>B)"
  by (induction n) (simp_all add: otb_tower_Suc)

\<comment> \<open>helper: strict monotonicity of the tower (content.md 6102–6106).
   m < n ==> D_u^m 0 < D_u^n 0.\<close>
lemma otb_tower_lessBT:
  "m < n \<Longrightarrow> lessBT ((Dpt (enat u) ^^ m) 0\<^sub>B) ((Dpt (enat u) ^^ n) 0\<^sub>B)"
proof (induction n arbitrary: m)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases m)
    case 0
    then show ?thesis
      by (simp add: otb_tower_Suc)
  next
    case (Suc k)
    with Suc.prems have "k < n" by simp
    from Suc.IH[OF this] have
      "lessBT ((Dpt (enat u) ^^ k) 0\<^sub>B) ((Dpt (enat u) ^^ n) 0\<^sub>B)" .
    then show ?thesis
      unfolding Suc
      by (simp add: otb_tower_Suc)
  qed
qed

\<comment> \<open>helper: the G-set of the tower (content.md 6110, 6118).
   G_u (D_u^n 0) = {D_u^m 0 | m < n} and the tower is an OT_B term.\<close>
lemma otb_tower_G_and_OT:
  "GBT (enat u) ((Dpt (enat u) ^^ n) 0\<^sub>B)
        = {(Dpt (enat u) ^^ m) 0\<^sub>B | m. m < n}
   \<and> isOT_BT ((Dpt (enat u) ^^ n) 0\<^sub>B)"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  let ?a = "\<lambda>m. (Dpt (enat u) ^^ m) 0\<^sub>B"
  from Suc.IH have G_n: "GBT (enat u) (?a n) = {?a m | m. m < n}"
    and OT_n: "isOT_BT (?a n)" by blast+
  \<comment> \<open>G-set: G_u (D_u^{Suc n} 0) = insert (D_u^n 0) (G_u (D_u^n 0))\<close>
  have G_Suc: "GBT (enat u) (?a (Suc n)) = insert (?a n) (GBT (enat u) (?a n))"
    by (simp add: otb_tower_Suc)
  have set_eq: "GBT (enat u) (?a (Suc n)) = {?a m | m. m < Suc n}"
    unfolding G_Suc G_n
    using less_Suc_eq by auto
  \<comment> \<open>OT: the isOT_BP condition for D_u^{Suc n} 0 = Trm [DB u (D_u^n 0)] quantifies over
     G_u (D_u^n 0) = {D_u^m 0 | m < n}, each of which is < D_u^n 0.\<close>
  have all_less: "\<forall>x \<in> GBT (enat u) (?a n). lessBT x (?a n)"
  proof
    fix x assume "x \<in> GBT (enat u) (?a n)"
    then obtain m where "m < n" and xeq: "x = ?a m"
      using G_n by blast
    then show "lessBT x (?a n)"
      using xeq otb_tower_lessBT by blast
  qed
  have OT_Suc: "isOT_BT (?a (Suc n))"
    unfolding otb_tower_Suc
    using OT_n all_less by simp
  show ?case using set_eq OT_Suc by blast
qed

\<comment> \<open>helper: descP of a list of identical principals (for part (3)).\<close>
lemma otb_descP_replicate:
  "descP (replicate m (DB (enat u) (Trm [])))"
proof (induction m)
  case 0 then show ?case by simp
next
  case (Suc m)
  show ?case
  proof (cases m)
    case 0 then show ?thesis by simp
  next
    case (Suc k)
    then show ?thesis using Suc.IH by simp
  qed
qed

\<comment> \<open>helper: (D_u 0) * m as an explicit replicate term.\<close>
lemma otb_mult_eq_replicate:
  "multBT (Dpt (enat u) 0\<^sub>B) m = Trm (replicate m (DB (enat u) (Trm [])))"
  by (induction m) (simp_all add: replicate_append_same)

\<comment> \<open>----  Main lemma: §8.7 順序数項の基本例  ---- \<close>
lemma m_8_7_OT_examples:
  \<comment> \<open>m: 補題（順序数項の基本例）(content.md 6066–6120)\<close>
  shows "Dpt (enat u) 0\<^sub>B \<in> OT_B"
    and "Dpt (enat u) (Dpt (enat v) 0\<^sub>B) \<in> OT_B"
    and "n \<ge> 1 \<Longrightarrow> multBT (Dpt (enat u) 0\<^sub>B) (n - 1) \<in> OT_B"
    and "(Dpt (enat u) ^^ n) 0\<^sub>B \<in> OT_B"
proof -
  \<comment> \<open>(1) D_u 0 in OT_B (content.md 6087)\<close>
  show "Dpt (enat u) 0\<^sub>B \<in> OT_B" by (rule otb_Dpt_0)
next
  \<comment> \<open>(2) D_u D_v 0 in OT_B (content.md 6089-6098):
     G_u (D_v 0) subset-of {0} < D_v 0, and D_v 0 in OT_B.\<close>
  show "Dpt (enat u) (Dpt (enat v) 0\<^sub>B) \<in> OT_B"
  proof -
    have "isOT_BT (Dpt (enat u) (Dpt (enat v) 0\<^sub>B))"
      by (auto simp: OT_def)
    moreover have "dfree_BT (Dpt (enat u) (Dpt (enat v) 0\<^sub>B))" by simp
    ultimately show ?thesis by (simp add: OT_B_def OT_def T_B_def)
  qed
next
  \<comment> \<open>(3) (D_u 0) * (n-1) in OT_B (content.md 6100):
     all components are the OT-principal D_u 0, and they are non-increasing.\<close>
  assume "n \<ge> 1"
  show "multBT (Dpt (enat u) 0\<^sub>B) (n - 1) \<in> OT_B"
  proof -
    have "isOT_BT (multBT (Dpt (enat u) 0\<^sub>B) (n - 1))"
      unfolding otb_mult_eq_replicate
      by (simp add: otb_descP_replicate)
    moreover have "dfree_BT (multBT (Dpt (enat u) 0\<^sub>B) (n - 1))"
      unfolding otb_mult_eq_replicate by simp
    ultimately show ?thesis by (simp add: OT_B_def OT_def T_B_def)
  qed
next
  \<comment> \<open>(4) D_u^n 0 in OT_B (content.md 6102-6120)\<close>
  show "(Dpt (enat u) ^^ n) 0\<^sub>B \<in> OT_B"
  proof -
    have "isOT_BT ((Dpt (enat u) ^^ n) 0\<^sub>B)"
      using otb_tower_G_and_OT by blast
    moreover have "dfree_BT ((Dpt (enat u) ^^ n) 0\<^sub>B)"
      by (rule otb_tower_dfree)
    ultimately show ?thesis by (simp add: OT_B_def OT_def T_B_def)
  qed
qed


text \<open>§6.5 branch-3b BC0, PIECE 3 ASSEMBLY (cross-block junction, row-0).
  This is the green ASSEMBLY of the cross-block junction edge from the trunk
  diagonal into a branch block leftend, on the explicit \<open>core-nontrunk\<close> form
  \<open>R = Red M = diagSeq 0 t @ rest\<close> (\<open>t = TrMax M\<close>, \<open>rest = concat (branch blocks)\<close>).

  It reduces \<open>le0 R 0 bs\<close> (the J-th block leftend \<open>bs\<close> is a row-0 descendant of
  the trunk root 0) to the SINGLE deeper residual @{term noint} (the cross-block
  ``no-smaller-intermediate'' condition: nothing strictly between the diagonal
  parent \<open>e-1\<close> and \<open>bs\<close> has a row-0 entry below \<open>e = entry R 0 bs\<close>).  Everything
  else is discharged by the GREEN bricks @{thm [source] le0_diagSeq_append_prefix}
  (trunk spine) and @{thm [source] entry_diagSeq_append_lo} (the diagonal parent
  \<open>e-1\<close> reads value \<open>e-1\<close>), plus a single @{const nextrel0} step.

  Empirically the residual @{term noint} is the cross-block fact
  ``\<open>entry R 0 bs = Joints M ! J + 1\<close> and every earlier-block / diagonal entry is
  \<open>\<ge> Joints M ! J + 1\<close>'', which on the NJ side becomes
  ``\<open>entry (Red (NJ M J)) 0 j \<ge> npJ M J\<close> for all \<open>j\<close>'' — a Red-recursive entry
  lower bound (see \<open>docs/red-le-domain.md\<close> \<S>9).  Empirically TRUE
  49669/49669 (rank\<le>5) + rank\<ge>12 (5003/0, 1657/0).\<close>

lemma le0_diagSeq_junction_into_block:
  fixes R :: pairseq
  assumes Rsplit: "R = diagSeq 0 t @ rest"
    and e_def: "e = entry R 0 bs"
    and e1: "1 \<le> e" and et: "e \<le> Suc t"
    and bsgt: "t < bs" and bsL: "bs < Lng R"
    and noint: "\<forall>j. e - 1 < j \<and> j < bs \<longrightarrow> entry R 0 j \<ge> e"
  shows "le0 R 0 bs"
proof -
  define p where "p = e - 1"
  \<comment> \<open>The diagonal parent \<open>p = e-1 \<le> t\<close> reads value \<open>p\<close>.\<close>
  have ple: "p \<le> t" using et e1 p_def by linarith
  have ep: "entry R 0 p = p"
  proof -
    have "entry (diagSeq 0 t @ rest) 0 p = p" by (rule entry_diagSeq_append_lo[OF ple])
    thus ?thesis using Rsplit by simp
  qed
  \<comment> \<open>Trunk spine: \<open>0 \<rightarrow>\<^sup>* p\<close> (GREEN @{thm le0_diagSeq_append_prefix}).\<close>
  have z0: "(0::nat) \<le> p" by simp
  have spine: "le0 R 0 p"
    using le0_diagSeq_append_prefix[OF z0 ple, of rest] Rsplit by simp
  \<comment> \<open>The single junction step \<open>p \<rightarrow> bs\<close> (a @{const nextrel0} step).\<close>
  have pbs: "p < bs" using bsgt ple by linarith
  have ebs: "entry R 0 bs = e" using e_def by simp
  have lt: "entry R 0 p < entry R 0 bs" using ep ebs e1 p_def by linarith
  have noint': "\<forall>j. p < j \<and> j < bs \<longrightarrow> entry R 0 j \<ge> entry R 0 bs"
    using noint ebs p_def by simp
  have pL: "p < Lng R" using pbs bsL by linarith
  have step: "nextrel0 R p bs"
    unfolding nextrel0_def using pL bsL pbs lt noint' by blast
  \<comment> \<open>Assemble: \<open>0 \<rightarrow>\<^sup>* p \<rightarrow> bs\<close>.\<close>
  have stepR: "(nextrel0 R)\<^sup>*\<^sup>* p bs" using step by (rule r_into_rtranclp)
  have spineR: "(nextrel0 R)\<^sup>*\<^sup>* 0 p" using spine by (simp add: le0_def)
  have rt: "(nextrel0 R)\<^sup>*\<^sup>* 0 bs" using spineR stepR by (rule rtranclp_trans)
  have b0: "(0::nat) < Lng R" using bsL by linarith
  show ?thesis using rt b0 bsL by (simp add: le0_def)
qed

lemma njA_length_Br_eq:
  assumes T: "M \<in> T_PS" and mono: "monoT M" and pos: "0 < entry M 1 0"
  shows "length (Br (coreReduce (IncrFirst M))) = length (Br (coreReduce M))"
  by (simp add: njA_Br_eq[OF T mono pos])

text \<open>(3) @{const FirstNodes} is shared (TrMax + IdxSum of branch lengths).\<close>

lemma njA_FirstNodes_eq:
  assumes T: "M \<in> T_PS" and mono: "monoT M" and pos: "0 < entry M 1 0"
  shows "FirstNodes (coreReduce (IncrFirst M)) = FirstNodes (coreReduce M)"
proof -
  have br: "Br (coreReduce (IncrFirst M)) = map IncrFirst (Br (coreReduce M))"
    by (rule njA_Br_eq[OF T mono pos])
  have idx: "IdxSum (Br (coreReduce (IncrFirst M))) = IdxSum (Br (coreReduce M))"
    by (simp add: br IdxSum_map_IncrFirst)
  show ?thesis
    by (simp add: FirstNodes_def njA_TrMax_eq[OF T pos] idx)
qed

text \<open>(4) @{const Joints} is shared (parent in row 0 of the shared first nodes;
  row-0 next-relation is preserved by the tail bump).\<close>

lemma njA_Joints_eq:
  assumes T: "M \<in> T_PS" and mono: "monoT M" and pos: "0 < entry M 1 0"
  shows "Joints (coreReduce (IncrFirst M)) = Joints (coreReduce M)"
proof -
  have nextR: "nextR (coreReduce (IncrFirst M)) = nextR (coreReduce M)"
    by (rule tail_bump.nextR_eq[OF tail_bump_coreReduce[OF T pos]])
  have fn: "FirstNodes (coreReduce (IncrFirst M)) = FirstNodes (coreReduce M)"
    by (rule njA_FirstNodes_eq[OF T mono pos])
  have br: "length (Br (coreReduce (IncrFirst M))) = length (Br (coreReduce M))"
    by (rule njA_length_Br_eq[OF T mono pos])
  show ?thesis
    by (simp add: Joints_def nextR fn br)
qed

text \<open>(5) @{const npJ} is shared.  It reads \<open>entry (Br!J) 1 0\<close> (row 1, preserved
  by @{const IncrFirst}) and the row-1 parent of the shared first node (row-1
  next-relation preserved).\<close>

lemma njA_npJ_eq:
  assumes T: "M \<in> T_PS" and mono: "monoT M" and pos: "0 < entry M 1 0"
    and J: "J < length (Br (coreReduce M))"
  shows "npJ (coreReduce (IncrFirst M)) J = npJ (coreReduce M) J"
proof -
  let ?A = "coreReduce (IncrFirst M)"
  let ?X = "coreReduce M"
  have br: "Br ?A = map IncrFirst (Br ?X)" by (rule njA_Br_eq[OF T mono pos])
  have JA: "J < length (Br ?A)" using J br by simp
  have brJ: "Br ?A ! J = IncrFirst (Br ?X ! J)" using J br by simp
  \<comment> \<open>row-1 left entry of the branch is unchanged by IncrFirst\<close>
  have e1: "entry (Br ?A ! J) 1 0 = entry (Br ?X ! J) 1 0"
  proof (cases "Lng (Br ?X ! J) = 0")
    case True
    hence brnil: "Br ?X ! J = []" by simp
    have "Br ?A ! J = []" using brJ brnil by (simp add: IncrFirst_def)
    thus ?thesis using brnil by simp
  next
    case False
    hence L0: "0 < Lng (Br ?X ! J)" by simp
    show ?thesis using entry_IncrFirst[OF L0, of 1] by (simp add: brJ)
  qed
  have nextR: "nextR ?A = nextR ?X"
    by (rule tail_bump.nextR_eq[OF tail_bump_coreReduce[OF T pos]])
  have fn: "FirstNodes ?A ! J = FirstNodes ?X ! J"
    by (simp add: njA_FirstNodes_eq[OF T mono pos])
  have theEq: "(THE j. nextR ?A 1 j (FirstNodes ?A ! J))
             = (THE j. nextR ?X 1 j (FirstNodes ?X ! J))"
    by (simp add: nextR fn)
  show ?thesis
    unfolding npJ_def by (simp only: e1 theEq)
qed

text \<open>(6) The block exponent \<open>e\<^sub>J = Joints!J + 1 - npJ\<close> is shared.\<close>

lemma njA_eJ_eq:
  assumes T: "M \<in> T_PS" and mono: "monoT M" and pos: "0 < entry M 1 0"
    and J: "J < length (Br (coreReduce M))"
  shows "Joints (coreReduce (IncrFirst M)) ! J + 1 - npJ (coreReduce (IncrFirst M)) J
       = Joints (coreReduce M) ! J + 1 - npJ (coreReduce M) J"
  by (simp add: njA_Joints_eq[OF T mono pos] njA_npJ_eq[OF T mono pos J])


lemma cong_struct_congR: "cong_struct A X \<Longrightarrow> congR A X"
proof -
  assume cs: "cong_struct A X"
  show "congR A X" unfolding congR_def
  proof (intro conjI allI impI)
    show "Lng A = Lng X" by (rule cong_struct.len_eq[OF cs])
    show "nextrel0 A = nextrel0 X" by (rule cong_struct.nextrel0_eq[OF cs])
    fix j assume "j < Lng X"
    thus "entry A 1 j = entry X 1 j" by (rule cong_struct.row1_eq[OF cs])
  qed
qed

lemma congR_monoT: "congR A X \<Longrightarrow> monoT A = monoT X"
  by (drule congR_cong_struct) (rule cong_struct.monoT_eq)
lemma rnsub_RightNodes_zero: "RightNodes (Trm []) = []"
  by simp

\<comment> \<open>flatBT of a single principal.\<close>
lemma rnsub_flat_single: "flatBT (Trm [DB u a]) = Dsym u # flatBT a"
  by simp

\<comment> \<open>The flat string of a single principal whose argument is \<open>0\<close>.\<close>
lemma rnsub_flat_Dpt0: "flatBT (Dpt (enat v) 0\<^sub>B) = [Dsym (enat v), Zsym]"
  by simp

\<comment> \<open>An all-\<open>RP\<close> list contains no \<open>Zsym\<close>.\<close>
lemma rnsub_allRP_no_Zsym: "\<forall>x \<in> set xs. x = RP \<Longrightarrow> Zsym \<notin> set xs"
  by auto

(* ===== block from workflow t2-elead ===== *)

subsection \<open>§6.6 補題（簡約性と左端の関係）— (e) keystone tool\<close>

text \<open>elead helpers for a general diagonal prefix \<open>diagSeq u v @ rest\<close> (starting
  at \<open>u\<close>, not necessarily \<open>0\<close>).  Length of the prefix is \<open>Suc v - u\<close>; entries on
  the prefix are \<open>u + i\<close>.\<close>

lemma elead_Lng_diag_append:
  "Lng (diagSeq u v @ rest) = (Suc v - u) + Lng rest"
  by simp

(* ===== block from workflow t2-scbtriv ===== *)
section \<open>§7.2 scb分解の自明性の判定条件 (p_7_2_scb_triviality)\<close>

text \<open>
  The article proves the three-way equivalence "at the string level": it
  identifies a term with its \<open>\<Sigma>\<close>-string \<open>flat\<close>, so "\<open>t = scb = c\<close>" is read as
  string equality.  At the \<^typ>\<open>BT\<close> level the missing ingredient is that
  \<^const>\<open>flatBT\<close> is injective (this is exactly what the §7.3 \<^const>\<open>unflatBT\<close>,
  defined by \<open>THE\<close>, presupposes).  We prove that injectivity here from the
  grammar, by the standard "unique readability of a balanced-bracket comma
  language" argument, then read off the three equivalences faithfully.

  Bracket depth: \<open>(\<close> counts \<open>+1\<close>, \<open>)\<close> counts \<open>-1\<close>, everything else \<open>0\<close>.
\<close>

definition scbtriv_dlt :: "Sym \<Rightarrow> int" where
  "scbtriv_dlt x = (if x = LP then 1 else if x = RP then -1 else 0)"

definition scbtriv_depth :: "Sym list \<Rightarrow> int" where
  "scbtriv_depth xs = sum_list (map scbtriv_dlt xs)"

lemma scbtriv_depth_append [simp]:
  "scbtriv_depth (xs @ ys) = scbtriv_depth xs + scbtriv_depth ys"
  by (simp add: scbtriv_depth_def)

lemma scbtriv_depth_Nil [simp]: "scbtriv_depth [] = 0"
  by (simp add: scbtriv_depth_def)

lemma scbtriv_depth_Cons [simp]:
  "scbtriv_depth (x # xs) = scbtriv_dlt x + scbtriv_depth xs"
  by (simp add: scbtriv_depth_def)

lemma scbtriv_dlt_simps [simp]:
  "scbtriv_dlt LP = 1" "scbtriv_dlt RP = -1"
  "scbtriv_dlt CM = 0" "scbtriv_dlt Zsym = 0" "scbtriv_dlt (Dsym u) = 0"
  by (simp_all add: scbtriv_dlt_def)

lemma scbtriv_depth_concat_CM:
  "scbtriv_depth (concat (map (\<lambda>r. CM # flatBP r) rs))
     = sum_list (map (\<lambda>r. scbtriv_depth (flatBP r)) rs)"
  by (induct rs) simp_all

lemma scbtriv_sum_list_zero:
  "(\<forall>x \<in> set xs. f x = (0::int)) \<Longrightarrow> sum_list (map f xs) = 0"
  by (induct xs) simp_all

text \<open>\<open>flat\<close>-strings are nonempty.\<close>

lemma scbtriv_flat_nonempty:
  "flatBT t \<noteq> []" "flatBP p \<noteq> []"
  by (induct t and p rule: flatBT_flatBP.induct) auto

text \<open>\<open>flat\<close>-strings are balanced: total depth \<open>0\<close>.\<close>

lemma scbtriv_depth_flat:
  "scbtriv_depth (flatBT t) = 0" "scbtriv_depth (flatBP p) = 0"
proof (induct t and p rule: flatBT_flatBP.induct)
  case 1 show ?case by simp
next
  case (2 p) thus ?case by simp
next
  case (3 p q ps)
  \<comment> \<open>IH 3(2): every segment \<open>r \<in> set (q#ps)\<close> has balanced \<open>flatBP r\<close>\<close>
  have seg0: "\<forall>r \<in> set (q # ps). scbtriv_depth (flatBP r) = 0"
    using 3(2) by auto
  have allz: "(\<Sum>r\<leftarrow>(q # ps). scbtriv_depth (flatBP r)) = 0"
    by (rule scbtriv_sum_list_zero) (rule seg0)
  have "scbtriv_depth (concat (map (\<lambda>r. CM # flatBP r) (q # ps))) = 0"
    by (simp only: scbtriv_depth_concat_CM allz)
  thus ?case using 3(1) by simp
next
  case (4 u a) thus ?case by simp
qed

text \<open>
  COUNTEREXAMPLE to the literal part (2) of \<open>p_7_2_scb_compose\<close>.  The statement
  there requires the conclusion \<open>scb_decomp (D\<^sub>v t) (D\<^sub>v \<frown> s) c b\<close>
  \<^emph>\<open>unconditionally\<close>; but \<open>scb_decomp\<close> demands \<open>isPTB_str c\<close> whenever the term is
  \<open>\<noteq> Trm []\<close>, and \<open>D\<^sub>v t\<close> is always \<open>\<noteq> Trm []\<close>.  Yet for \<open>t = Trm []\<close> the
  hypothesis \<open>scb_decomp (Trm []) s c b\<close> does NOT force \<open>isPTB_str c\<close>: take
  \<open>s = []\<close>, \<open>c = [Zsym]\<close>, \<open>b = []\<close>.  Then the conclusion would need
  \<open>isPTB_str [Zsym]\<close>, which is false because every principal string \<open>flatBP p\<close>
  begins with a \<open>Dsym\<close>, never \<open>Zsym\<close>.  So the literal part (2) is FALSE.
\<close>

lemma scbcomp_isPTB_Zsym_False: "\<not> isPTB_str [Zsym]"
proof
  assume "isPTB_str [Zsym]"
  then obtain p where p: "[Zsym] = flatBP p" unfolding isPTB_str_def by blast
  obtain u a where "p = DB u a" by (cases p)
  hence "flatBP p = Dsym u # flatBT a" by simp
  with p have "[Zsym] = Dsym u # flatBT a" by simp
  thus False by simp
qed

lemma scbcomp_compose2_counterexample:
  "scb_decomp (Trm []) [] [Zsym] []
   \<and> \<not> scb_decomp (Dpt (enat v) (Trm [])) (Dsym (enat v) # []) [Zsym] []"
proof
  show "scb_decomp (Trm []) [] [Zsym] []"
    unfolding scb_decomp_def by simp
next
  show "\<not> scb_decomp (Dpt (enat v) (Trm [])) (Dsym (enat v) # []) [Zsym] []"
    unfolding scb_decomp_def using scbcomp_isPTB_Zsym_False by simp
qed

text \<open>The branch segment of \<open>A = diagSeq 0 k @ M\<close> coincides with that of \<open>M\<close>:
  both pick the suffix of \<open>M\<close> right of its trunk, since past the diagonal+junction
  \<open>A\<close> is literally \<open>M\<close> (drop-shift), and the trunk end shifts by exactly \<open>Suc k\<close>.\<close>

lemma ecrux_branch_seg_eq:
  assumes mono: "monoT M" and r0: "k < entry M 0 0" and r1: "k < entry M 1 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
  shows "seg (diagSeq 0 k @ M) (TrMax (diagSeq 0 k @ M) + 1) (Lng (diagSeq 0 k @ M) - 1)
       = seg M (TrMax M + 1) (Lng M - 1)"
proof -
  let ?c = "Suc k"
  let ?A = "diagSeq 0 k @ M"
  have "0 < Lng M" using mono by (simp add: monoT_def leR_def le0_def)
  hence Mne: "M \<noteq> []" by auto
  have MT: "M \<in> T_PS" using Mne by (simp add: T_PS_def)
  have LM: "0 < Lng M" using Mne by (cases M) auto
  have LA: "Lng ?A = ?c + Lng M" using Lng_diagSeq[of 0 k] by simp
  have dropeq: "drop ?c ?A = M" by (rule ecrux_drop_tail)
  have trA: "TrMax ?A = ?c + TrMax M"
    by (rule ecrux_TrMax_diag_prefix[OF mono r0 r1])
  have trlt: "TrMax M < Lng M - 1" using tne TrMax_bound[OF MT] by simp
  \<comment> \<open>the \<open>A\<close>-branch is a \<open>drop\<close>, and that \<open>drop\<close> peels the diagonal off to land in \<open>M\<close>.\<close>
  have AltL: "TrMax ?A + 1 < Lng ?A" using trA LA trlt LM by linarith
  have MltL: "TrMax M + 1 < Lng M" using trlt LM by linarith
  have segA: "seg ?A (TrMax ?A + 1) (Lng ?A - 1) = drop (TrMax ?A + 1) ?A"
    by (rule drop_eq_seg[OF AltL, symmetric])
  have segM: "seg M (TrMax M + 1) (Lng M - 1) = drop (TrMax M + 1) M"
    by (rule drop_eq_seg[OF MltL, symmetric])
  have "drop (TrMax ?A + 1) ?A = drop ((TrMax M + 1) + ?c) ?A" using trA by (simp add: add.commute)
  also have "\<dots> = drop (TrMax M + 1) (drop ?c ?A)" by (simp add: drop_drop)
  also have "\<dots> = drop (TrMax M + 1) M" using dropeq by simp
  finally have "drop (TrMax ?A + 1) ?A = drop (TrMax M + 1) M" .
  thus ?thesis using segA segM by simp
qed

text \<open>m (§6.6 keystone (e)-CRUX, part 2): the branch decomposition is unchanged by
  prepending the diagonal (the branch region is the unchanged suffix of \<open>M\<close>).\<close>

lemma ecrux_Br_diag_prefix:
  assumes mono: "monoT M" and r0: "k < entry M 0 0" and r1: "k < entry M 1 0"
  shows "Br (diagSeq 0 k @ M) = Br M"
proof -
  let ?c = "Suc k"
  let ?A = "diagSeq 0 k @ M"
  have "0 < Lng M" using mono by (simp add: monoT_def leR_def le0_def)
  hence Mne: "M \<noteq> []" by auto
  have LM: "0 < Lng M" using Mne by (cases M) auto
  have LA: "Lng ?A = ?c + Lng M" using Lng_diagSeq[of 0 k] by simp
  have trA: "TrMax ?A = ?c + TrMax M"
    by (rule ecrux_TrMax_diag_prefix[OF mono r0 r1])
  \<comment> \<open>the trunk-saturation flag agrees between \<open>A\<close> and \<open>M\<close>.\<close>
  have flag: "(TrMax ?A = Lng ?A - 1) \<longleftrightarrow> (TrMax M = Lng M - 1)"
    using trA LA LM by linarith
  show ?thesis
  proof (cases "TrMax M = Lng M - 1")
    case True
    hence "TrMax ?A = Lng ?A - 1" using flag by simp
    hence "Br ?A = []" by (simp add: Br_def)
    moreover have "Br M = []" using True by (simp add: Br_def)
    ultimately show ?thesis by simp
  next
    case False
    hence "TrMax ?A \<noteq> Lng ?A - 1" using flag by simp
    hence "Br ?A = P (seg ?A (TrMax ?A + 1) (Lng ?A - 1))" by (simp add: Br_def)
    also have "\<dots> = P (seg M (TrMax M + 1) (Lng M - 1))"
      using ecrux_branch_seg_eq[OF mono r0 r1 False] by simp
    also have "\<dots> = Br M" using False by (simp add: Br_def)
    finally show ?thesis .
  qed
qed

text \<open>m (§6.6 keystone (e)-CRUX, part 3): the branch first-nodes all shift right by
  \<open>Suc k\<close> (their relative offsets within the unchanged branch region are fixed; only
  the trunk-end basepoint moves by \<open>Suc k\<close>).\<close>

lemma ecrux_FirstNodes_diag_prefix:
  assumes mono: "monoT M" and r0: "k < entry M 0 0" and r1: "k < entry M 1 0"
  shows "FirstNodes (diagSeq 0 k @ M) = map (\<lambda>x. Suc k + x) (FirstNodes M)"
proof -
  let ?c = "Suc k"
  let ?A = "diagSeq 0 k @ M"
  have trA: "TrMax ?A = ?c + TrMax M"
    by (rule ecrux_TrMax_diag_prefix[OF mono r0 r1])
  have brA: "Br ?A = Br M" by (rule ecrux_Br_diag_prefix[OF mono r0 r1])
  have "FirstNodes ?A = map (\<lambda>x. TrMax ?A + 1 + x) (IdxSum (Br ?A))"
    by (simp add: FirstNodes_def)
  also have "\<dots> = map (\<lambda>x. ?c + (TrMax M + 1 + x)) (IdxSum (Br M))"
    using trA brA by (simp add: add.assoc add.left_commute)
  also have "\<dots> = map (\<lambda>x. ?c + x) (map (\<lambda>x. TrMax M + 1 + x) (IdxSum (Br M)))"
    by simp
  also have "\<dots> = map (\<lambda>x. ?c + x) (FirstNodes M)"
    by (simp add: FirstNodes_def)
  finally show ?thesis .
qed

text \<open>FWD keystone, core-NONTRUNK initial slice (article content.md 1154):
  for a reduced \<open>monoT M\<close> with \<open>M\<^sub>0 = (0,0)\<close> and \<open>TrMax M \<noteq> Lng M - 1\<close>, the
  row-1-trunk initial slice \<open>seg M 0 (TrMax M)\<close> is reduced (slice-heredity
  @{thm [source] herd_6_6_reduced_slice}, with \<open>j\<^sub>0' = 0\<close> and
  \<open>TrMax M \<le> j\<^sub>1' = TrMax M \<le> Lng M - 1\<close>), has both left-end values \<open>0\<close>, and
  length \<open>Suc (TrMax M)\<close>.  This is the article's initial reduced segment
  \<open>(M\<^sub>j)\<^bsub>j=0\<^esub>\<^bsup>j\<^sub>0\<^esup>\<close> of the \<open>j\<^sub>1\<close>-induction core-nontrunk case (line 1154): a
  strictly shorter reduced core to which the induction hypothesis applies.
  (We do NOT claim \<open>monoT\<close> here: \<open>TrMax M = 0\<close> nontrunk reduced cores occur
  27/63 in \<open>red_model\<close>, val\<le>3 Lng\<le>4, and then the slice is the \<open>zeroT\<close>
  singleton \<open>[(0,0)]\<close>; reducedness and the left-end values hold uniformly.)
  Empirically TRUE: 63/0 reduced monoT-nontrunk cores.\<close>

lemma kfwd_reduced_core_nontrunk_initslice:
  assumes M: "M \<in> RT_PS"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
  shows "seg M 0 (TrMax M) \<in> RT_PS
           \<and> entry (seg M 0 (TrMax M)) 0 0 = 0
           \<and> entry (seg M 0 (TrMax M)) 1 0 = 0
           \<and> Lng (seg M 0 (TrMax M)) = Suc (TrMax M)"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
  let ?t = "TrMax M"
  let ?S = "seg M 0 ?t"
  \<comment> \<open>reduced (slice heredity).\<close>
  have segRT: "?S \<in> RT_PS"
    by (rule herd_6_6_reduced_slice[OF M refl order.refl tb])
  have Lseg: "Lng ?S = Suc ?t" using Lng_seg[of M 0 ?t] by simp
  \<comment> \<open>left-end values inherit from \<open>M\<close>.\<close>
  have es00: "entry ?S 0 0 = 0"
  proof -
    have jlt: "(0::nat) < Lng ?S" using Lseg by simp
    have "entry ?S 0 0 = entry M 0 (0 + 0)" by (rule entry_seg[OF jlt])
    thus ?thesis using e00 by simp
  qed
  have es10: "entry ?S 1 0 = 0"
  proof -
    have jlt: "(0::nat) < Lng ?S" using Lseg by simp
    have "entry ?S 1 0 = entry M 1 (0 + 0)" by (rule entry_seg[OF jlt])
    thus ?thesis using e10 by simp
  qed
  show ?thesis using segRT es00 es10 Lseg by simp
qed

\<comment> \<open>Front B (wf10): \<open>flatBP p\<close> always ends, after its rightmost-spine bottom
   \<open>Zsym\<close>, in an all-\<open>)\<close> tail.  Hence it splits as \<open>q @ Zsym # r\<close> with \<open>r\<close>
   all-\<open>)\<close> and \<open>Zsym \<notin> set r\<close> (the LAST \<open>Zsym\<close>).  Symmetric brick to
   @{thm [source] rnsub_Zsym_in_flat}; we only need existence of such a split.\<close>
lemma rnsub_flatBP_lastZ_split:
  "\<exists>q r. flatBP p = q @ Zsym # r \<and> (Zsym \<notin> set r)"
proof -
  have "Zsym \<in> set (flatBP p)" by (rule rnsub_Zsym_in_flatP)
  thus ?thesis by (meson split_list_last)
qed

text \<open>
  Front B (wf10/wf11) — the central RightNodes-suffix brick and the cut-pinning.

  \<^bold>\<open>Empirical truth.\<close>  Over the BT model (indices \<open>{0,1,2}\<close>, depth \<open>2\<close>):
  \<^item> \<open>RightNodes (Trm [p])\<close> is a SUFFIX of \<open>RightNodes t\<close> for every scb-shaped
    occurrence \<open>flatBT t = s \<frown> flatBP p \<frown> b\<close> (\<open>b\<close> all-\<open>)\<close>, \<open>t,Trm[p] \<in> T\<^bsub>B\<^esub>\<close>):
    \<open>python/_wf10_suffix_check.py\<close>, 0/3000.
  \<^item> MAXIMALITY DISCRIMINATOR: \<open>flatBP p\<close> is the WHOLE last principal of \<open>t\<close>
    (\<open>= flatBP (last component)\<close>) IFF \<open>length (RightNodes (Trm [p])) =
    length (RightNodes t)\<close>; strictly inside otherwise (\<open>python/_wf11_maxim.py\<close>,
    disc 0/3000).
  \<^item> CUT-PINNING: equal \<open>RightNodes (Trm [p])\<close> \<Longrightarrow> equal \<open>length s\<close>
    (\<open>python/_wf10_pin3_check.py\<close>, \<open>_wf11_occ_check.py\<close>: \<open>len(RN c)\<close> determines
    \<open>len s\<close>, 0 violations).

  The suffix brick below (\<open>rnsub_RightNodes_suffix\<close>) does the spine descent on
  \<open>length s\<close>: split \<open>flatBT (Trm xs)\<close> at the global last \<open>Zsym\<close> (inside
  \<open>flatBT a\<close>) and at the marked principal's last \<open>Zsym\<close>; the two align.  Either
  the marked principal IS the last principal \<open>Dsym u # flatBT a\<close> (maximal,
  \<open>RightNodes (Trm [p]) = RightNodes (Trm xs)\<close>, suffix with empty prefix) or it
  is strictly inside \<open>flatBT a\<close> with a shorter cut, and the IH appends
  \<open>the_enat u\<close>.  This is the article's MAXIMALITY of the marked principal
  (content.md ~1896/1918).
\<close>

\<comment> \<open>\<open>RightNodes (Trm [DB u a]) = the_enat u # RightNodes a\<close>; its length is
   \<open>1 + length (RightNodes a)\<close>, the descent depth invariant.\<close>
lemma rnsub_RN_single: "RightNodes (Trm [DB u a]) = the_enat u # RightNodes a"
  by simp

\<comment> \<open>GREEN weight brick.  In any \<open>flatBT t = pre \<frown> c \<frown> post\<close> where \<open>c\<close> is a
   complete principal/term string (\<open>flatinj_dsum c = -1\<close>) and \<open>post\<close> is all-\<open>)\<close>,
   the prefix \<open>pre\<close> has \<open>flatinj_dsum pre = int (length post)\<close>.  (Bookkeeping for
   the MAXIMALITY weight contradiction: a cut strictly inside the canonical
   \<open>pre\<close> would force a balanced principal to start at a positive-depth, all-\<open>)\<close>-
   terminated position.)  Sound — pure \<^const>\<open>flatinj_dsum\<close> algebra plus the
   GREEN @{thm [source] flatinj_dsum_flatBT}, @{thm [source] flatinj_dsum_allRP}.\<close>
lemma rnsub_dsum_pre_eq_post:
  assumes "flatBT t = pre @ c @ post"
      and "flatinj_dsum c = -1"
      and "\<forall>x \<in> set post. x = RP"
  shows "flatinj_dsum pre = int (length post)"
proof -
  have tot: "flatinj_dsum (flatBT t) = -1" by (rule flatinj_dsum_flatBT)
  have ptot: "flatinj_dsum post = - int (length post)"
    using flatinj_dsum_allRP[OF assms(3)] .
  have "flatinj_dsum (flatBT t) = flatinj_dsum pre + flatinj_dsum c + flatinj_dsum post"
    using assms(1) by simp
  thus ?thesis using tot assms(2) ptot by simp
qed

section \<open>Front A (wf11) — \<open>IncrFirst ^^ k\<close> structure bricks (incf_pow_*)\<close>

text \<open>
  Structural correspondence between \<open>(IncrFirst ^^ k) X\<close> and \<open>X\<close>: the
  \<open>k\<close>-fold top-row increment shifts row-0 entries by \<open>k\<close>, leaves row-1 entries,
  the length, the \<open>nextR\<close> relation (rows \<open>\<le> 1\<close>), and hence the parent/witness
  structure (\<open>hasParent\<close>, \<open>parent\<close>) unchanged.  These need no induction on the
  keystone, only on \<open>k\<close>, using the single-step \<open>IncrFirst\<close> lemmas
  (@{thm [source] nextrel0_IncrFirst_eq}, @{thm [source] nextrel1_IncrFirst_eq},
  @{thm [source] entry_IncrFirst}, @{thm [source] Lng_IncrFirst}).\<close>

lemma incf_pow_Lng[simp]: "Lng ((IncrFirst ^^ k) X) = Lng X"
  by (induction k) simp_all

section \<open>Front B (wf12) — global-last-\<open>Zsym\<close> alignment of the marked principal\<close>

text \<open>
  Front B (wf12).  The residual hypothesis \<open>length s\<^sub>0 = length s\<^sub>1\<close> of the GREEN
  central \<open>c\<close>-equality @{thm [source] m_7_2_scb_c_unique} is the article's
  "\<open>s = s\<^sub>i\<close>" (content.md 1896/1918): both marked principals begin at the unique
  LAST occurrence of \<open>D\<^bsub>v\<^sub>0\<^esub>\<close> in \<open>t\<close>.  The GREEN brick below isolates the SOUND
  kernel of that pinning that this round established: the marked principal of an
  scb-shaped occurrence (all-\<open>)\<close> tail) and the canonical last principal of \<open>t\<close>
  share the GLOBAL LAST \<open>Zsym\<close>, hence their pre-\<open>Zsym\<close> prefixes are EQUAL:

    \<open>s \<frown> Dsym up # qpre = pre \<frown> Dsym u # fpre\<close>

  where \<open>flatBT ap = qpre \<frown> Zsym # qpost\<close>, \<open>flatBT a = fpre \<frown> Zsym # fpost\<close> are the
  last-\<open>Zsym\<close> splits.  This is the article's "\<open>t\<close> から \<open>)\<close> を除いた文字列の末尾は
  \<open>D\<^sub>u 0\<close>" alignment (content.md 1884), and it is the spine equation feeding the
  cut-pinning \<open>length s\<^sub>0 = length s\<^sub>1\<close>.

  SOUNDNESS: cites only GREEN bricks (@{thm [source] rnsub_align_lastZ},
  @{thm [source] rnsub_Zsym_in_flat}) and the library — never a \<open>p_*\<close> stub.

  RESIDUAL / BLOCKER (reported, not faked).  The remaining step
  \<open>rnsub_cut_ge_pre\<close> (\<open>length pre \<le> length s\<close>: the cut never lands strictly
  before the canonical last-principal start) is NOT a recursion into the marked
  principal's argument \<open>ap\<close>: empirically (\<open>/tmp/wf12_A.py\<close>, 0/3000 holds, but
  the inner occurrence \<open>flatBT ap = rest' \<frown> flatBP(DB u a) \<frown> w\<close> obtained by
  descending into \<open>ap\<close> yields only a LOWER bound \<open>length pre\<^bsub>ap\<^esub> \<le> length rest'\<close>
  via the IH, never the contradiction \<open>length s < length pre \<Longrightarrow> False\<close>).  The
  property \<open>length pre \<le> length s\<close> is FALSE for an arbitrary canonical-SHAPE
  \<open>pre\<close> (1440/5880 violations) and even for \<open>pre = [] \<or> last pre = CM\<close> (1080
  violations): it holds ONLY for the genuine canonical \<open>pre\<close> of
  @{thm [source] rnsub_flat_pre_post}, whose distinguishing property is that
  \<open>Dsym u # flatBT a\<close> is the LAST TOP-LEVEL component (its trailing \<open>CM\<close> is at
  tuple-depth 0).  Proving \<open>rnsub_cut_ge_pre\<close> therefore needs a FIRST-component
  unique-readability peel (descend into the first top-level principal when the
  cut is strictly inside \<open>pre\<close>), not the argument recursion — a separate
  multi-lemma program.  Once \<open>rnsub_cut_ge_pre\<close> is GREEN, the GREEN
  @{thm [source] rnsub_cut_ge_pre_dichotomy} + a strong induction on \<open>length s\<close>
  give \<open>rnsub_RN_pins_len\<close> and hence the UNCONDITIONAL conjuncts (4),(5).
\<close>

\<comment> \<open>An all-\<open>)\<close> string has no \<open>Zsym\<close> and remains all-\<open>)\<close> on prefixes/suffixes.\<close>
lemma wf12_allRP_prefix:
  "\<forall>x \<in> set (xs @ ys). x = RP \<Longrightarrow> (\<forall>x \<in> set xs. x = RP) \<and> (\<forall>x \<in> set ys. x = RP)"
  by auto

\<comment> \<open>GREEN spine-alignment brick.  For an scb-shaped principal occurrence
   \<open>flatBT t0 = s @ flatBP P @ b\<close> (\<open>b\<close> all-\<open>)\<close>) and ANY canonical last-principal
   split \<open>flatBT t0 = pre @ (Dsym u # flatBT a) @ post\<close> (\<open>post\<close> all-\<open>)\<close>), the
   marked principal and the canonical principal share the GLOBAL LAST \<open>Zsym\<close>, so
   their pre-\<open>Zsym\<close> prefixes coincide and their post-\<open>Zsym\<close> all-\<open>)\<close> tails coincide.
   This is the article's末尾 \<open>D\<^sub>u 0\<close> alignment (content.md 1884), and the spine
   equation underlying the cut-pinning.  Sound — cites only GREEN
   @{thm [source] rnsub_align_lastZ}, @{thm [source] rnsub_Zsym_in_flat}.\<close>
lemma rnsub_marked_canon_lastZ:
  assumes occ: "flatBT t0 = s @ flatBP (DB up ap) @ b"
      and bRP: "\<forall>x \<in> set b. x = RP"
      and PP:  "flatBT t0 = pre @ (Dsym u # flatBT a) @ post"
      and postRP: "\<forall>x \<in> set post. x = RP"
  shows "\<exists>qpre qpost fpre fpost.
            flatBT ap = qpre @ Zsym # qpost
          \<and> flatBT a = fpre @ Zsym # fpost
          \<and> (s @ Dsym up # qpre = pre @ Dsym u # fpre)
          \<and> (qpost @ b = fpost @ post)"
proof -
  \<comment> \<open>Split each principal's argument at its last \<open>Zsym\<close>.\<close>
  have "Zsym \<in> set (flatBT ap)" by (rule rnsub_Zsym_in_flat)
  then obtain qpre qpost where
    ap_split: "flatBT ap = qpre @ Zsym # qpost" and no_Z_qpost: "Zsym \<notin> set qpost"
    by (meson split_list_last)
  have "Zsym \<in> set (flatBT a)" by (rule rnsub_Zsym_in_flat)
  then obtain fpre fpost where
    a_split: "flatBT a = fpre @ Zsym # fpost" and no_Z_fpost: "Zsym \<notin> set fpost"
    by (meson split_list_last)
  have no_Z_b: "Zsym \<notin> set b" using bRP by auto
  have no_Z_post: "Zsym \<notin> set post" using postRP by auto
  \<comment> \<open>Two decompositions of \<open>flatBT t0\<close>, each \<open>(\<dots>) @ Zsym # (\<dots>)\<close> with a \<open>Zsym\<close>-free
     tail; align at the global last \<open>Zsym\<close>.\<close>
  have markedZ: "flatBT t0 = (s @ Dsym up # qpre) @ Zsym # (qpost @ b)"
    using occ ap_split by simp
  have canonZ: "flatBT t0 = (pre @ Dsym u # fpre) @ Zsym # (fpost @ post)"
    using PP a_split by simp
  have eqZ: "(s @ Dsym up # qpre) @ Zsym # (qpost @ b)
           = (pre @ Dsym u # fpre) @ Zsym # (fpost @ post)"
    using markedZ canonZ by simp
  have noZ_qb: "Zsym \<notin> set (qpost @ b)" using no_Z_qpost no_Z_b by simp
  have noZ_fp: "Zsym \<notin> set (fpost @ post)" using no_Z_fpost no_Z_post by simp
  have al: "s @ Dsym up # qpre = pre @ Dsym u # fpre \<and> qpost @ b = fpost @ post"
    using rnsub_align_lastZ[OF eqZ noZ_qb noZ_fp] .
  show ?thesis using ap_split a_split al by blast
qed




lemma flatBP_last_not_CM': "last (flatBP p) \<noteq> CM"
  using flatBP_last_not_CM[of p] by simp

\<comment> \<open>Suffix-weight bookkeeping.\<close>
lemma flatinj_dsum_suffix:
  "w = pre @ suf \<Longrightarrow> flatinj_dsum suf = flatinj_dsum w - flatinj_dsum pre"
  by simp

text \<open>The \<S>6.6 keystone forward (monoT core) in the TARGET name form, reduced to the
  single \<open>r1cross\<close> residual (Front B's \<open>wf19_valpin\<close>: the row-1 cross-block \<open>kk>0\<close>
  value pin).  Once \<open>wf19_valpin\<close> lands on HEAD, @{thm [source] wf18_crossblock_row1_kkpos}
  discharges \<open>r1cross\<close> (it derives the relation from \<open>pTr\<close> + \<open>valpin\<close>), making this
  UNCONDITIONAL; the keystone then unblocks \<S>6.5 \<open>Red_le\<close> via the
  \<open>reduced \<Longrightarrow> RedCondA \<Longrightarrow> red_le\<close> lead.  All other cases are GREEN here.\<close>

lemma kst_reduced_imp_condAB_monoT_core_via_wf19:
  assumes r1cross:
    "\<And>N. N \<in> RT_PS \<Longrightarrow> monoT N \<Longrightarrow> entry N 0 0 = 0 \<Longrightarrow> entry N 1 0 = 0
       \<Longrightarrow> TrMax N \<noteq> Lng N - 1
       \<Longrightarrow> 0 < Lng (NJ N (Lng (Br N) - 1)) - 1
       \<Longrightarrow> hasParent N 1 (Lng N - 1)
       \<Longrightarrow> parent N 1 (Lng N - 1) < FirstNodes N ! (Lng (Br N) - 1)
       \<Longrightarrow> entry N 1 (parent N 1 (Lng N - 1)) + 1 = entry N 1 (Lng N - 1)"
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
  shows "RedCondA M \<and> RedCondB M"
  by (rule condAB_all_cond[OF r1cross M mono e00 e10])


text \<open>The unconditional last-column \<open>condA_top\<close> witness translation (TARGET
  \<open>condA_top_all\<close>) in conditional form: it is exactly the \<open>RedCondA\<close> half of
  @{thm [source] kst_reduced_imp_condAB_monoT_core_via_wf19} read at the last column,
  so it follows by projecting \<open>RedCondA M\<close> and unfolding \<^const>\<open>RedCondA\<close>.  This is
  the witness consumed by @{thm [source] kst_reduced_imp_condAB_monoT_core_cond}.\<close>

lemma condA_top_all_cond:
  assumes r1cross:
    "\<And>N. N \<in> RT_PS \<Longrightarrow> monoT N \<Longrightarrow> entry N 0 0 = 0 \<Longrightarrow> entry N 1 0 = 0
       \<Longrightarrow> TrMax N \<noteq> Lng N - 1
       \<Longrightarrow> 0 < Lng (NJ N (Lng (Br N) - 1)) - 1
       \<Longrightarrow> hasParent N 1 (Lng N - 1)
       \<Longrightarrow> parent N 1 (Lng N - 1) < FirstNodes N ! (Lng (Br N) - 1)
       \<Longrightarrow> entry N 1 (parent N 1 (Lng N - 1)) + 1 = entry N 1 (Lng N - 1)"
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1" and i: "i \<le> 1"
    and hp: "hasParent M i (Lng M - 1)"
  shows "entry M i (parent M i (Lng M - 1)) + 1 = entry M i (Lng M - 1)"
proof -
  have rca: "RedCondA M"
    by (rule conjunct1[OF condAB_all_cond[OF r1cross M mono e00 e10]])
  show ?thesis using rca i hp unfolding RedCondA_def by blast
qed





section \<open>Front B (wf20) — \<open>parpin\<close>: diagonal-prefix parent reconstruction of the last column\<close>

text \<open>WF20 BRICK (\<open>parpin\<close>, structural half).  This is the diagonal-prefix
  parent-reconstruction half of the \<open>parpin\<close> residual of @{thm [source] wf19_valpin}
  (template @{thm [source] a1_if_npJ_Red_pos}).  For the diagonal-prefixed core
  \<open>N = diagSeq 0 d \<oplus> R\<^sup>*\<close> (\<open>d = R\<^sup>*\<^bsub>1,0\<^esub>-1\<close>) of the keystone forward in-block
  regime, the LAST column \<open>lastN = Lng N - 1 = Suc d + kk\<close> (\<open>kk = Lng R\<^sup>*-1\<close>)
  acquires its row-1 parent FROM the diagonal prefix: it is the diagonal column at
  index \<open>q = R\<^sup>*\<^bsub>1,kk\<^esub> - 1\<close> (whose row-1 value is \<open>q\<close>, a diagonal entry), PROVIDED
  \<open>q \<le> d\<close> (i.e. \<open>R\<^sup>*\<^bsub>1,kk\<^esub> \<le> R\<^sup>*\<^bsub>1,0\<^esub>\<close>: the last branch-tail row-1 value is below the
  branch head).

  We assemble the \<open>nextrel1 N 1 q lastN\<close> EDGE explicitly (mirroring the
  nextrel1/uniqueness construction of @{thm [source] a1_if_npJ_Red_pos}):
  \<^item> the \<open>le0\<close> spine \<open>q \<rightarrow>\<^sup>* d \<rightarrow> Suc d \<rightarrow>\<^sup>* lastN\<close> through the diagonal prefix
    (@{thm [source] le0_diagSeq_append_prefix}), a junction step (a @{const nextrel0}
    step, valid since the tail head sits strictly above the diagonal:
    \<open>R\<^sup>*\<^bsub>0,0\<^esub> \<ge> R\<^sup>*\<^bsub>1,0\<^esub> = Suc d > d\<close>), and the lifted tail spine
    @{thm [source] poper_le0_drop} (\<open>drop (Suc d) N = R\<^sup>*\<close> by
    @{thm [source] ecrux_drop_tail}, with \<open>le0 R\<^sup>* 0 kk\<close>);
  \<^item> the value gap \<open>entry N 1 q = q < R\<^sup>*\<^bsub>1,kk\<^esub> = entry N 1 lastN\<close>;
  \<^item> the minimality: any \<open>le0\<close>-ancestor \<open>x > q\<close> of \<open>lastN\<close> in \<open>N\<close> reads
    \<open>entry N 1 x \<ge> R\<^sup>*\<^bsub>1,kk\<^esub>\<close> — on the diagonal (\<open>x \<le> d\<close>) because \<open>entry N 1 x = x \<ge> kk\<close>
    (as \<open>x > q = R\<^sup>*\<^bsub>1,kk\<^esub>-1\<close>), and on the tail (\<open>x \<ge> Suc d\<close>) because
    \<open>le0 N x lastN\<close> pulls back to \<open>le0 R\<^sup>* (x - Suc d) kk\<close> and the supplied
    row-1 minimality of \<open>R\<^sup>*\<close>'s last column (\<open>tailmin\<close>) gives
    \<open>entry R\<^sup>* 1 (x - Suc d) \<ge> R\<^sup>*\<^bsub>1,kk\<^esub>\<close>.
  Parents in row 1 are unique (@{thm [source] nextR1_unique}), so
  \<open>hasParent N 1 lastN\<close> with \<open>parent N 1 lastN = q\<close>, and the parent VALUE reads
  \<open>entry N 1 (parent N 1 lastN) = q = R\<^sup>*\<^bsub>1,kk\<^esub> - 1\<close>.

  EMPIRICAL TRUTH-CHECK (\<open>red_model.py\<close>, reduced \<open>monoT\<close> cores maxlen 5 value 3; the
  34 row-1 cross-block \<open>kk>0\<close> cases of @{thm [source] wf19_valpin}).  Over those 34
  cases: the side conditions \<open>q \<le> d\<close>, \<open>R\<^sup>*\<^bsub>1,0\<^esub> \<le> R\<^sup>*\<^bsub>0,0\<^esub>\<close>, \<open>le0 R\<^sup>* 0 kk\<close>, and the
  row-1 tail minimality \<open>tailmin\<close> hold 0/34; the assembled facts \<open>nextrel1 N 1 q
  lastN\<close>, \<open>hasParent N 1 lastN\<close>, \<open>parent N 1 lastN = q\<close> hold 0/34; and the parent
  value \<open>entry N 1 (parent N 1 lastN) = q\<close> holds 0/34.  (The GENERAL form WITHOUT
  the \<open>tailmin\<close> hypothesis is FALSE: 13397/15987 random \<open>(R\<^sup>*,d)\<close> pairs fail the
  edge — the row-1 minimality of \<open>R\<^sup>*\<close>'s last column is genuinely required, so it is
  carried as an explicit hypothesis rather than re-derived from \<open>R\<^sup>*\<close>'s reducedness
  here.)

  RESIDUAL (reported honestly, NOT faked — see [[subagent-worktree-pitfalls]]).
  The literal \<open>parpin\<close> of @{thm [source] wf19_valpin} pins the parent value to the
  cross-block parent \<open>p = parent M 1 (Lng M-1)\<close>; here it is pinned to
  \<open>q = R\<^sup>*\<^bsub>1,kk\<^esub> - 1\<close>.  The identification \<open>q = p\<close> is EXACTLY
  \<open>R\<^sup>*\<^bsub>1,kk\<^esub> = Suc p\<close>, which is the conclusion of @{thm [source] wf19_valpin} itself
  (the keystone-forward cross-block \<open>r1cross\<close> obligation): deriving it here would be
  circular, so it is NOT discharged in this brick.  Likewise the side conditions
  (\<open>q \<le> d\<close>, \<open>R\<^sup>*\<^bsub>1,0\<^esub> \<le> R\<^sup>*\<^bsub>0,0\<^esub>\<close>, \<open>le0 R\<^sup>* 0 kk\<close>, \<open>tailmin\<close>) are properties of the
  reduced \<open>R\<^sup>* = Red (NJ M J\<^sup>*)\<close>; they are TRUE (verified) but carried as hypotheses,
  not re-derived from \<open>R\<^sup>*\<close>'s reducedness in this standalone brick.

  SOUND — cites only GREEN @{thm [source] le0_diagSeq_append_prefix},
  @{thm [source] poper_le0_drop}, @{thm [source] ecrux_drop_tail},
  @{thm [source] entry_diagSeq_append_lo}, @{thm [source] wf17_entry_diag_tail},
  @{thm [source] nextR1_unique}, the \<^const>\<open>nextrel1\<close>/\<^const>\<open>hasParent\<close>/\<^const>\<open>parent\<close>
  definitions and the library; no \<open>p_*\<close> stub, and it does NOT cite
  @{thm [source] wf19_valpin} nor any keystone goal (it pins to \<open>q\<close>, not to \<open>p\<close>).\<close>

lemma wf20_parpin:
  fixes Rs :: pairseq and d :: nat
  defines "kk \<equiv> Lng Rs - 1"
  defines "N \<equiv> diagSeq 0 d @ Rs"
  defines "q \<equiv> entry Rs 1 kk - 1"
  assumes Rspos: "0 < Lng Rs"
    and ekkpos: "0 < entry Rs 1 kk"
    and qled: "entry Rs 1 kk - 1 \<le> d"
    and headge: "entry Rs 1 0 \<le> entry Rs 0 0"
    and hd: "entry Rs 1 0 = Suc d"
    and le0kk: "le0 Rs 0 kk"
    and tailmin: "\<And>t. le0 Rs t kk \<Longrightarrow> entry Rs 1 kk \<le> entry Rs 1 t"
  shows "nextrel1 N q (Lng N - 1)
       \<and> hasParent N 1 (Lng N - 1)
       \<and> parent N 1 (Lng N - 1) = q
       \<and> entry N 1 (parent N 1 (Lng N - 1)) = q"
proof -
  \<comment> \<open>Basic length facts: \<open>Lng N = Suc d + Lng R\<^sup>*\<close>, \<open>lastN = Suc d + kk\<close>.\<close>
  have lenN: "Lng N = Suc d + Lng Rs" unfolding N_def by simp
  have kklt: "kk < Lng Rs" unfolding kk_def using Rspos by linarith
  have lastNeq: "Lng N - 1 = Suc d + kk"
    unfolding kk_def using lenN Rspos by linarith
  have qle: "q \<le> d" unfolding q_def using qled by simp
  have qlt: "q < Lng N" using qle lenN by linarith
  have lastNlt: "Lng N - 1 < Lng N" using lenN Rspos by linarith
  \<comment> \<open>Row-1 entries: \<open>entry N 1 q = q\<close> (diagonal), \<open>entry N 1 lastN = entry R\<^sup>* 1 kk\<close>.\<close>
  have e1q: "entry N 1 q = q"
    unfolding N_def
    using entry_diagSeq_append_lo[where i=q and k=d and p=1 and rest=Rs, OF qle] .
  have e1last: "entry N 1 (Lng N - 1) = entry Rs 1 kk"
    using lastNeq wf17_entry_diag_tail[of d Rs 1 kk] unfolding N_def by simp
  \<comment> \<open>The value gap: \<open>q = entry R\<^sup>* 1 kk - 1 < entry R\<^sup>* 1 kk = entry N 1 lastN\<close>.\<close>
  have qval: "q < entry Rs 1 kk" unfolding q_def using ekkpos by linarith
  have gap: "entry N 1 q < entry N 1 (Lng N - 1)"
    using e1q e1last qval by simp
  \<comment> \<open>\<open>le0\<close> spine \<open>q \<rightarrow>\<^sup>* d \<rightarrow> Suc d \<rightarrow>\<^sup>* lastN\<close>.\<close>
  \<comment> \<open>(1) diagonal prefix piece \<open>q \<rightarrow>\<^sup>* d\<close>.\<close>
  have le0_qd: "le0 N q d"
    using le0_diagSeq_append_prefix[OF qle order.refl, of Rs] unfolding N_def .
  have spine_qd: "(nextrel0 N)\<^sup>*\<^sup>* q d"
    using le0_qd by (simp add: le0_def)
  \<comment> \<open>(2) junction step \<open>d \<rightarrow> Suc d\<close>: the tail head sits strictly above the diagonal.\<close>
  have e0d: "entry N 0 d = d"
    unfolding N_def
    using entry_diagSeq_append_lo[where i=d and k=d and p=0 and rest=Rs, OF order.refl] .
  have e0sd: "entry N 0 (Suc d) = entry Rs 0 0"
    unfolding N_def
    using entry_diagSeq_append_junction[where k=d and rest=Rs and p=0] by simp
  have dlt: "Suc d < Lng N" using lenN Rspos by linarith
  have headgt: "d < entry Rs 0 0" using headge hd by linarith
  have junc: "nextrel0 N d (Suc d)"
    unfolding nextrel0_def
  proof (intro conjI allI impI)
    show "d < Lng N" using dlt by linarith
    show "Suc d < Lng N" by (rule dlt)
    show "d < Suc d" by simp
    show "entry N 0 d < entry N 0 (Suc d)" using e0d e0sd headgt by simp
    fix j assume "d < j \<and> j < Suc d"
    thus "entry N 0 (Suc d) \<le> entry N 0 j" by simp
  qed
  have spine_dsd: "(nextrel0 N)\<^sup>*\<^sup>* d (Suc d)" using junc by (rule r_into_rtranclp)
  \<comment> \<open>(3) lifted tail spine \<open>Suc d \<rightarrow>\<^sup>* lastN\<close> from \<open>le0 R\<^sup>* 0 kk\<close>.\<close>
  have dropN: "drop (Suc d) N = Rs" unfolding N_def by (rule ecrux_drop_tail)
  have tailrt0: "(nextrel0 Rs)\<^sup>*\<^sup>* 0 kk" using le0kk by (simp add: le0_def)
  have spine_tail: "(nextrel0 N)\<^sup>*\<^sup>* (Suc d + 0) (Suc d + kk)"
  proof -
    have "(nextrel0 (drop (Suc d) N))\<^sup>*\<^sup>* 0 kk" using tailrt0 dropN by simp
    thus ?thesis by (rule poper_le0_drop_fwd)
  qed
  have spine_sdlast: "(nextrel0 N)\<^sup>*\<^sup>* (Suc d) (Lng N - 1)"
    using spine_tail lastNeq by simp
  \<comment> \<open>Assemble the \<open>le0\<close> spine.\<close>
  have rt_qlast: "(nextrel0 N)\<^sup>*\<^sup>* q (Lng N - 1)"
    using spine_qd spine_dsd spine_sdlast by (meson rtranclp_trans)
  have le0_qlast: "le0 N q (Lng N - 1)"
    using rt_qlast qlt lastNlt by (simp add: le0_def)
  \<comment> \<open>Minimality: any \<open>le0\<close>-ancestor \<open>x > q\<close> of \<open>lastN\<close> has \<open>entry N 1 x \<ge> entry R\<^sup>* 1 kk\<close>.\<close>
  have minim: "\<And>x. q < x \<Longrightarrow> le0 N x (Lng N - 1)
                  \<Longrightarrow> entry N 1 (Lng N - 1) \<le> entry N 1 x"
  proof -
    fix x assume xq: "q < x" and xle: "le0 N x (Lng N - 1)"
    have xlt: "x < Lng N" using xle by (simp add: le0_def)
    show "entry N 1 (Lng N - 1) \<le> entry N 1 x"
    proof (cases "x \<le> d")
      case True
      \<comment> \<open>Diagonal column: \<open>entry N 1 x = x \<ge> kk_val\<close> since \<open>x > q = kk_val - 1\<close>.\<close>
      have e1x: "entry N 1 x = x"
        unfolding N_def
        using entry_diagSeq_append_lo[where i=x and k=d and p=1 and rest=Rs, OF True] .
      have "entry Rs 1 kk \<le> x" using xq unfolding q_def using ekkpos by linarith
      thus ?thesis using e1x e1last by simp
    next
      case False
      \<comment> \<open>Tail column: \<open>x = Suc d + a\<close>, pull back \<open>le0 N x lastN\<close> to \<open>le0 R\<^sup>* a kk\<close>.\<close>
      hence dx: "Suc d \<le> x" by simp
      define a where "a \<equiv> x - Suc d"
      have xa: "x = Suc d + a" unfolding a_def using dx by simp
      have alt: "a < Lng Rs" using xlt lenN xa by simp
      have lift: "le0 N (Suc d + a) (Suc d + kk) = le0 Rs a kk"
      proof -
        have b1: "a < Lng N - Suc d" using alt lenN by simp
        have b2: "kk < Lng N - Suc d" using kklt lenN by simp
        have "le0 (drop (Suc d) N) a kk = le0 N (Suc d + a) (Suc d + kk)"
          by (rule poper_le0_drop[OF b1 b2])
        thus ?thesis using dropN by simp
      qed
      have le0a: "le0 Rs a kk"
      proof -
        have "le0 N (Suc d + a) (Suc d + kk)" using xle xa lastNeq by simp
        thus ?thesis using lift by simp
      qed
      have e1xa: "entry N 1 x = entry Rs 1 a"
        unfolding N_def xa using wf17_entry_diag_tail[of d Rs 1 a] by simp
      have "entry Rs 1 kk \<le> entry Rs 1 a" using le0a by (rule tailmin)
      thus ?thesis using e1xa e1last by simp
    qed
  qed
  \<comment> \<open>Assemble \<open>nextrel1 N 1 q lastN\<close>.\<close>
  have nr1: "nextrel1 N q (Lng N - 1)"
    unfolding nextrel1_def
  proof (intro conjI allI impI)
    show "q < Lng N" by (rule qlt)
    show "Lng N - 1 < Lng N" by (rule lastNlt)
    show "q < Lng N - 1" using lastNeq qle by linarith
    show "entry N 1 q < entry N 1 (Lng N - 1)" by (rule gap)
    show "le0 N q (Lng N - 1)" by (rule le0_qlast)
    fix x assume hx: "q < x \<and> le0 N x (Lng N - 1)"
    show "entry N 1 (Lng N - 1) \<le> entry N 1 x" using hx minim by blast
  qed
  have nx1: "nextR N 1 q (Lng N - 1)" unfolding nextR_def using nr1 by simp
  \<comment> \<open>Uniqueness via @{thm [source] nextR1_unique}.\<close>
  have uq: "\<And>r. nextR N 1 r (Lng N - 1) \<Longrightarrow> r = q"
  proof -
    fix r assume "nextR N 1 r (Lng N - 1)"
    thus "r = q" using nx1 by (rule nextR1_unique)
  qed
  have hpN: "hasParent N 1 (Lng N - 1)"
    unfolding hasParent_def using nx1 uq by blast
  have parN: "parent N 1 (Lng N - 1) = q"
    unfolding parent_def using nx1 by (rule the_equality) (rule uq)
  have parval: "entry N 1 (parent N 1 (Lng N - 1)) = q"
    using parN e1q by simp
  show ?thesis using nr1 hpN parN parval by blast
qed



section \<open>Front A (wf21) — RAW-branch \<open>N\<close> for the non-circular \<open>r1cross\<close> route\<close>

text \<open>WF21 BRICK 1 (\<open>wf21_rawN_core\<close>): the RAW last-branch diagonal-prefixed core.
  The non-circular keystone route (docs/reducedness.md \<S>16, content.md 1182-1216)
  uses, for the row-1 cross-block last-column witness, the RAW branch block
  \<open>B := Br M ! J\<^sup>*\<close> (\<open>J\<^sup>* = Lng (Br M) - 1\<close>) rather than the head-replaced
  \<open>NJ M J\<^sup>*\<close>.  With \<open>R\<^sup>B := Red B\<close> and the diagonal prefix \<open>diagSeq 0 (R\<^sup>B\<^bsub>1,0\<^esub>-1)\<close>,
    \<open>N := (if 0 < R\<^sup>B\<^bsub>1,0\<^esub> then diagSeq 0 (R\<^sup>B\<^bsub>1,0\<^esub>-1) else []) @ R\<^sup>B\<close>
  is reduced \<open>monoT\<close> with left end \<open>(0,0)\<close>.  This is the \<open>N\<close> reduced/core fact of the
  raw route (article: "簡約性と左端の関係から \<open>N\<close> は簡約である").

  STRUCTURE.  \<open>kkpos\<close> gives \<open>Lng (NJ M J\<^sup>*) > 1\<close>; since \<open>Lng (NJ M J\<^sup>*) = Lng B\<close>
  (@{thm [source] Lng_NJ}) we get \<open>Lng B > 1\<close>, so \<open>\<not> zeroT B\<close>; with
  @{thm [source] Br_component_nonmulti} this pins \<open>monoT B\<close>, hence \<open>B \<in> PT_PS\<close>.
  Then \<open>R\<^sup>B = Red B\<close> is \<open>monoT\<close> (@{thm [source] m_6_5_Red_preserves_monoT}), reduced
  (@{thm [source] idem_nonmulti}, \<open>B\<close> non-multi as it is mono), and has the SAME
  row-1 left end as \<open>B\<close> (@{thm [source] m_6_6_Red_leftend_1}).  Finally
  @{thm [source] m_6_6_reduced_leftend} (with \<open>u = 0\<close>) gives \<open>N\<close> reduced \<open>monoT\<close>,
  and the diagonal prefix / @{thm [source] kst_reduced_row1_le_row0} pin its left end.

  EMPIRICAL TRUTH-CHECK (\<open>python/_wf21_check.py\<close>, \<open>_wf21_redB.py\<close>: reduced \<open>monoT\<close>
  cores maxlen 5 value \<le>3; all 34 row-1 cross-block \<open>kk>0\<close> cases): \<open>B\<close> monoT 34/34,
  \<open>R\<^sup>B\<close> reduced+monoT 34/34, \<open>entry R\<^sup>B 1 0 = entry M 1 off\<close> 34/34, \<open>N\<close> reduced+monoT
  +left-end-(0,0) 34/34.

  SOUND — cites only GREEN @{thm [source] Br_component_nonmulti},
  @{thm [source] m_6_5_Red_preserves_monoT}, @{thm [source] idem_nonmulti},
  @{thm [source] m_6_6_Red_leftend_1}, @{thm [source] m_6_6_reduced_leftend},
  @{thm [source] kst_reduced_row1_le_row0} and the library; no \<open>p_*\<close> stub, no goal
  self-citation.\<close>

lemma wf21_rawN_core:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
    and kkpos: "0 < Lng (NJ M (Lng (Br M) - 1)) - 1"
    \<comment> \<open>The diagonal prefix is nonempty (\<open>R\<^sup>B\<^bsub>1,0\<^esub> > 0\<close>); empirically 34/34 in r1cross
       (\<open>python/_wf21_fast.py\<close>: \<open>entry (Red B) 1 0 = 0\<close> never occurs in the row-1
       cross-block \<open>kk>0\<close> domain — the last-column row-1 parent then exists).
       Front A supplies it (as wf18/wf19 supply \<open>eRs10pos\<close>).\<close>
    and eRBpos: "0 < entry (Red (Br M ! (Lng (Br M) - 1))) 1 0"
  defines "Jstar \<equiv> Lng (Br M) - 1"
  defines "B \<equiv> Br M ! Jstar"
  defines "RB \<equiv> Red B"
  defines "N \<equiv> diagSeq 0 (entry RB 1 0 - 1) @ RB"
  shows "Red N = N \<and> monoT N \<and> entry N 0 0 = 0 \<and> entry N 1 0 = 0
       \<and> B \<in> PT_PS \<and> RB \<in> RT_PS \<and> RB \<in> PT_PS \<and> entry RB 1 0 = entry B 1 0
       \<and> 0 < entry RB 1 0"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have Mpt: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  have brne: "Br M \<noteq> []" using tne P_nonempty by (simp add: Br_def)
  hence nBpos: "0 < Lng (Br M)" by (cases "Br M") auto
  have JBr: "Jstar < Lng (Br M)" unfolding Jstar_def using nBpos by simp
  \<comment> \<open>\<open>B\<close> is nonempty and (with \<open>kkpos\<close>) has \<open>Lng B > 1\<close>, so \<open>monoT B\<close>.\<close>
  have Bne: "B \<noteq> []" unfolding B_def by (rule Br_component_nonempty[OF Mpt JBr])
  have LBeq: "Lng (NJ M Jstar) = Lng B" unfolding B_def by (rule Lng_NJ[OF Bne[unfolded B_def]])
  have LBgt1: "1 < Lng B" using kkpos LBeq unfolding Jstar_def by linarith
  have nzB: "\<not> zeroT B" using LBgt1 by (simp add: zeroT_def)
  have monoB: "monoT B"
    using Br_component_nonmulti[OF Mpt JBr] nzB unfolding B_def by blast
  have BT: "B \<in> T_PS" using Bne by (simp add: T_PS_def)
  have BPT: "B \<in> PT_PS" using BT monoB by (simp add: PT_PS_def)
  \<comment> \<open>\<open>R\<^sup>B = Red B\<close> is monoT, reduced, with the same row-1 left end.\<close>
  have monoRB: "monoT RB" unfolding RB_def by (rule m_6_5_Red_preserves_monoT[OF BPT])
  have nmuB: "\<not> multiT B" using monoB by (simp add: multiT_def)
  have redRB: "Red RB = RB" unfolding RB_def by (rule idem_nonmulti[OF BT nmuB])
  have LRB: "Lng RB = Lng B" unfolding RB_def by (rule m_6_5_Lng_Red[OF BT])
  have RBne: "RB \<noteq> []" using LRB Bne by (cases RB) auto
  have RBT: "RB \<in> T_PS" using RBne by (simp add: T_PS_def)
  have RBRT: "RB \<in> RT_PS" using RBT redRB by (simp add: RT_PS_def)
  have RBPT: "RB \<in> PT_PS" using RBT monoRB by (simp add: PT_PS_def)
  have e1RB: "entry RB 1 0 = entry B 1 0"
    unfolding RB_def by (rule m_6_6_Red_leftend_1[OF BT])
  have RBpos: "0 < entry RB 1 0" using eRBpos unfolding RB_def B_def Jstar_def by simp
  \<comment> \<open>\<open>N\<close> reduced \<open>monoT\<close> via @{thm [source] m_6_6_reduced_leftend} (\<open>u = 0\<close>; the guard
     fires since \<open>R\<^sup>B\<^bsub>1,0\<^esub> > 0\<close>).\<close>
  have u0: "(0::nat) \<le> entry RB 1 0" by simp
  have Nif: "N = (if (0::nat) < entry RB 1 0 then diagSeq 0 (entry RB 1 0 - 1) else []) @ RB"
    unfolding N_def using RBpos by simp
  have redmonoN: "Red N = N \<and> monoT N"
    using m_6_6_reduced_leftend[OF RBRT RBPT u0] Nif by simp
  have redN: "Red N = N" using redmonoN by simp
  have monoN: "monoT N" using redmonoN by simp
  \<comment> \<open>left end \<open>(0,0)\<close>: from the (nonempty) diagonal prefix head \<open>(0,0)\<close>.\<close>
  have dpos: "0 < Lng (diagSeq 0 (entry RB 1 0 - 1))" using RBpos by simp
  have eN00: "entry N 0 0 = 0"
    unfolding N_def using dpos by (simp add: entry_def diagSeq_def nth_append)
  have eN10: "entry N 1 0 = 0"
    unfolding N_def using dpos by (simp add: entry_def diagSeq_def nth_append)
  show ?thesis
    using redN monoN eN00 eN10 BPT RBRT RBPT e1RB RBpos by blast
qed


text \<open>===== Front B: raw-branch \<open>N\<close> foundational bricks (tag pss-wf21-rawN) =====

  The non-circular route of docs §16 builds, for the last-column cross-block
  witness, the sequence \<open>N := (guarded diagSeq prefix) @ Red B\<close> where
  \<open>B = Br M ! Jstar\<close> is the RAW last branch block (NOT the head-replaced
  \<open>NJ M Jstar\<close>) and \<open>m = FirstNodes M ! Jstar\<close> is its left endpoint in \<open>M\<close>.
  These bricks de-risk Front A's close.\<close>

text \<open>\<open>wf21_Red_row1zero_leftend\<close>: if \<open>M\<close> is monoT with row-1 left end \<open>0\<close>, then
  \<open>Red M\<close> has row-0 left end \<open>0\<close>.  Proof by \<open>Red.pinduct\<close> (modeled on
  @{thm [source] m_6_5_Red_leftend_row0_min}): the core case opens with a
  \<open>diagSeq 0 _\<close> prefix (value \<open>0\<close> at column \<open>0\<close>), the \<open>m\<^sub>1\<^sub>0=0, m\<^sub>0\<^sub>0>0\<close> shift case
  recurses on \<open>shiftRow0 M\<close> (still row-1 leftend \<open>0\<close>, IH), and the \<open>m\<^sub>1\<^sub>0>0\<close> branch
  is vacuous.  Truth-checked: 11/11 reduced monoT seqs with row-1 leftend \<open>0\<close>
  have row-0 leftend \<open>0\<close>.\<close>

lemma wf21_Red_row1zero_leftend:
  assumes MT: "M \<in> T_PS" and monoM: "monoT M" and z0: "entry M 1 0 = 0"
  shows "entry (Red M) 0 0 = 0"
proof -
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
  have "M \<in> T_PS \<longrightarrow> monoT M \<longrightarrow> entry M 1 0 = 0 \<longrightarrow> entry (Red M) 0 0 = 0"
    using domM
  proof (induction M rule: Red.pinduct)
    case (1 M)
    note dom    = 1(1)
    note IH_nc3 = 1(4)  \<comment> \<open>non-core m10=0 shift IH\<close>
    show ?case
    proof (rule impI, rule impI, rule impI)
      assume MT': "M \<in> T_PS" and mono: "monoT M" and zr: "entry M 1 0 = 0"
      have Mne: "M \<noteq> []" using MT' by (simp add: T_PS_def)
      have LMpos: "0 < Lng M" using Mne by (cases M) auto
      have nz: "\<not> zeroT M" using mono by (simp add: monoT_def)
      have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
      let ?j1  = "Lng M - 1"
      let ?j1' = "TrMax M"
      let ?m00 = "entry M 0 0"
      let ?m10 = "entry M 1 0"
      show "entry (Red M) 0 0 = 0"
      proof (cases "?m00 = 0 \<and> ?m10 = 0")
        case core: True
        hence c0: "?m00 = 0" and c1: "?m10 = 0" by simp_all
        show ?thesis
        proof (cases "?j1' = ?j1")
          case True
          have rM: "Red M = diagSeq ?m10 (?m10 + ?j1)"
            using Red.psimps[OF dom] nz nmu c0 c1 True by (simp add: Let_def)
          have "entry (Red M) 0 0 = ?m10 + 0"
            using rM entry_diagSeq[where a="?m10" and b="?m10 + ?j1" and j=0 and i=0]
            by (simp add: LMpos)
          thus ?thesis using c1 by simp
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
            using Red.psimps[OF dom] nz nmu c0 c1 tne by (simp add: Let_def)
          have "entry (Red M) 0 0 = entry (diagSeq 0 ?j1' @ ?tail) 0 0"
            by (simp add: rM)
          also have "\<dots> = 0"
            by (rule entry_diagSeq_append_lo) simp
          finally show ?thesis .
        qed
      next
        case nc: False
        show ?thesis
        proof (cases "?m10 = 0")
          case True
          let ?shift = "map (\<lambda>j. (entry M 0 j - ?m00, entry M 1 j)) [0..<Suc ?j1]"
          have rM: "Red M = Red ?shift"
            using Red.psimps[OF dom] nz nmu nc True by (simp add: Let_def)
          have shift_eq: "?shift = shiftRow0 M"
            using LMpos by (simp add: shiftRow0_def)
          have shift_T: "?shift \<in> T_PS" by (simp add: T_PS_def)
          have shift_mono: "monoT ?shift"
            using monoT_shiftRow0[OF MT' mono] shift_eq by simp
          have shift_z: "entry ?shift 1 0 = 0"
          proof -
            have "entry (shiftRow0 M) 1 0 = entry M 1 0"
              using LMpos by (rule entry_shiftRow0_1)
            thus ?thesis using shift_eq zr by simp
          qed
          have IH': "entry (Red ?shift) 0 0 = 0"
            using IH_nc3[OF nz nmu refl refl refl refl nc True] shift_T shift_mono shift_z
            by blast
          show ?thesis using IH' rM by simp
        next
          case False
          \<comment> \<open>\<open>m\<^sub>1\<^sub>0 > 0\<close> contradicts \<open>entry M 1 0 = 0\<close>: vacuous.\<close>
          thus ?thesis using zr by simp
        qed
      qed
    qed
  qed
  thus ?thesis using MT monoM z0 by blast
qed

text \<open>\<open>wf21_rawN_props\<close>: the raw-branch \<open>N\<close> is reduced, mono, and has left end
  \<open>(0,0)\<close>; its last index satisfies \<open>Lng N - 1 = (Lng M - 1) - m + entry M 1 m\<close>.
  Here \<open>B = Br M ! Jstar\<close> is the raw last branch block (assumed \<open>monoT\<close> — the
  cross-block witness case), \<open>m\<close> its left endpoint \<open>FirstNodes M ! Jstar\<close>, and
  \<open>N = (if 0 < entry M 1 m then diagSeq 0 (entry M 1 m - 1) else []) @ Red B\<close> —
  the guarded form matching @{thm [source] m_6_6_reduced_leftend} at \<open>u = 0\<close>.
  The prefix length matches because
  \<open>entry (Red B) 1 0 = entry B 1 0 = entry M 1 m\<close>
  (@{thm [source] m_6_6_Red_leftend_1}, @{thm [source] wf21_Br_eq_seg}).
  Reducedness/mono come from @{thm [source] m_6_6_reduced_leftend} applied to
  \<open>Red B\<close> (in \<open>RT_PS \<inter> PT_PS\<close> by @{thm [source] idem_nonmulti} and
  @{thm [source] m_6_5_Red_preserves_monoT}).  Truth-checked (red_model.py): all
  329 reduced mono nontrunk cores (mono last branch, len \<le> 5, vals \<le> 3, incl.
  the 17 \<open>entry M 1 m = 0\<close> cases at len \<le> 4) satisfy \<open>Red N = N\<close>, \<open>monoT N\<close>,
  \<open>entry N 0 0 = entry N 1 0 = 0\<close>, and the \<open>Lng N - 1\<close> formula.\<close>

lemma wf21_rawN_props:
  assumes M: "M \<in> RT_PS" and mono: "monoT M"
    and tne: "TrMax M \<noteq> Lng M - 1"
    and monoB: "monoT (Br M ! (Lng (Br M) - 1))"
  defines "Jstar \<equiv> Lng (Br M) - 1"
  defines "B \<equiv> Br M ! Jstar"
  defines "m \<equiv> FirstNodes M ! Jstar"
  defines "N \<equiv> (if 0 < entry M 1 m then diagSeq 0 (entry M 1 m - 1) else []) @ Red B"
  shows "Red N = N \<and> monoT N
       \<and> entry N 0 0 = 0 \<and> entry N 1 0 = 0
       \<and> Lng N - 1 = (Lng M - 1) - m + entry M 1 m
       \<and> B = seg M m (Lng M - 1) \<and> entry B 1 0 = entry M 1 m
       \<and> entry (Red B) 1 0 = entry M 1 m"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have Mpt: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  \<comment> \<open>\<open>Br M \<noteq> []\<close>, \<open>Jstar\<close> valid index.\<close>
  have brne: "Br M \<noteq> []" using tne P_nonempty by (simp add: Br_def)
  hence nBpos: "0 < Lng (Br M)" by (cases "Br M") auto
  have JBr: "Jstar < Lng (Br M)" unfolding Jstar_def using nBpos by simp
  \<comment> \<open>\<open>B\<close> nonempty, in \<open>T_PS\<close>, mono \<Rightarrow> in \<open>PT_PS\<close>, non-multi.\<close>
  have Bne: "B \<noteq> []" unfolding B_def Jstar_def
    by (rule Br_component_nonempty[OF Mpt JBr[unfolded Jstar_def]])
  have BT: "B \<in> T_PS" using Bne by (simp add: T_PS_def)
  have monoB': "monoT B" using monoB unfolding B_def Jstar_def .
  have Bpt: "B \<in> PT_PS" using BT monoB' by (simp add: PT_PS_def)
  have Bnm: "\<not> multiT B" using monoB' by (simp add: multiT_def)
  \<comment> \<open>\<open>Rs = Red B\<close> in \<open>T_PS\<close>, reduced (idempotence), mono.\<close>
  let ?Rs = "Red B"
  have LRs: "Lng ?Rs = Lng B" by (rule m_6_5_Lng_Red[OF BT])
  have RsT: "?Rs \<in> T_PS"
  proof -
    have "?Rs \<noteq> []" using LRs Bne by (cases B) auto
    thus ?thesis by (simp add: T_PS_def)
  qed
  have RsRT: "?Rs \<in> RT_PS"
  proof -
    have "Red (Red B) = Red B" by (rule idem_nonmulti[OF BT Bnm])
    thus ?thesis using RsT by (simp add: RT_PS_def)
  qed
  have monoRs: "monoT ?Rs" by (rule m_6_5_Red_preserves_monoT[OF Bpt])
  have RsPT: "?Rs \<in> PT_PS" using RsT monoRs by (simp add: PT_PS_def)
  \<comment> \<open>\<open>B = seg M m (Lng M - 1)\<close>, so \<open>entry B 1 0 = entry M 1 m\<close>.\<close>
  have Beq: "B = seg M m (Lng M - 1)"
    unfolding B_def m_def Jstar_def
    by (rule wf21_Br_eq_seg[OF Mpt brne])
  have LBpos: "0 < Lng B" using Bne by (cases B) auto
  have LsegPos: "0 < Lng (seg M m (Lng M - 1))" using LBpos Beq by simp
  have mlt: "m < Lng M"
  proof -
    have "0 < Suc (Lng M - 1) - m" using LsegPos by simp
    thus ?thesis using LMpos by linarith
  qed
  have eB10: "entry B 1 0 = entry M 1 m"
  proof -
    have "entry (seg M m (Lng M - 1)) 1 0 = entry M 1 (m + 0)"
      by (rule entry_seg[OF LsegPos])
    thus ?thesis using Beq by simp
  qed
  \<comment> \<open>\<open>entry (Red B) 1 0 = entry B 1 0 = entry M 1 m\<close>.\<close>
  have eRs10: "entry ?Rs 1 0 = entry M 1 m"
    using m_6_6_Red_leftend_1[OF BT] eB10 by simp
  \<comment> \<open>\<open>N\<close> matches the \<open>m_6_6_reduced_leftend\<close> form at \<open>u = 0\<close>.\<close>
  have Ndef': "N = (if 0 < entry M 1 m then diagSeq 0 (entry M 1 m - 1) else []) @ ?Rs"
    unfolding N_def B_def Jstar_def by simp
  have NeqA: "N = (if (0::nat) < entry ?Rs 1 0 then diagSeq 0 (entry ?Rs 1 0 - 1) else []) @ ?Rs"
    using Ndef' eRs10 by simp
  have z: "(0::nat) \<le> entry ?Rs 1 0" by simp
  have rl: "Red ((if (0::nat) < entry ?Rs 1 0 then diagSeq 0 (entry ?Rs 1 0 - 1) else []) @ ?Rs)
            = ((if (0::nat) < entry ?Rs 1 0 then diagSeq 0 (entry ?Rs 1 0 - 1) else []) @ ?Rs)
            \<and> monoT ((if (0::nat) < entry ?Rs 1 0 then diagSeq 0 (entry ?Rs 1 0 - 1) else []) @ ?Rs)"
    using m_6_6_reduced_leftend[OF RsRT RsPT z] by simp
  have rN: "Red N = N \<and> monoT N" using rl NeqA by simp
  \<comment> \<open>left end of \<open>N\<close>: in both guard branches, column 0 is \<open>(0,0)\<close>
      (diagSeq prefix or \<open>Rs\<close> with \<open>entry Rs i 0 = 0\<close>).\<close>
  have e0N: "entry N 0 0 = 0 \<and> entry N 1 0 = 0"
  proof (cases "0 < entry M 1 m")
    case True
    have NeqU: "N = diagSeq 0 (entry M 1 m - 1) @ ?Rs" unfolding N_def B_def Jstar_def using True by simp
    have c0: "entry (diagSeq 0 (entry M 1 m - 1) @ ?Rs) 0 0 = 0"
      by (rule entry_diagSeq_append_lo[where i=0]) simp
    have c1: "entry (diagSeq 0 (entry M 1 m - 1) @ ?Rs) 1 0 = 0"
      by (rule entry_diagSeq_append_lo[where i=0]) simp
    show ?thesis using NeqU c0 c1 by simp
  next
    case False
    hence z': "entry M 1 m = 0" by simp
    have NeqU: "N = ?Rs" unfolding N_def B_def Jstar_def using False by simp
    \<comment> \<open>\<open>entry Rs 1 0 = entry M 1 m = 0\<close>; \<open>entry Rs 0 0 \<ge> entry Rs 1 0\<close> not needed:
        \<open>Rs\<close> reduced mono with row-1 leftend 0 forces row-0 leftend 0.\<close>
    have rs10: "entry ?Rs 1 0 = 0" using eRs10 z' by simp
    \<comment> \<open>\<open>entry B 1 0 = entry M 1 m = 0\<close>, so \<open>Red B\<close> has row-0 leftend \<open>0\<close>.\<close>
    have b10z: "entry B 1 0 = 0" using eB10 z' by simp
    have rs00: "entry ?Rs 0 0 = 0"
      by (rule wf21_Red_row1zero_leftend[OF BT monoB' b10z])
    show ?thesis using NeqU rs00 rs10 by simp
  qed
  \<comment> \<open>length: \<open>Lng N - 1 = (Lng M - 1) - m + entry M 1 m\<close>.\<close>
  have LB: "Lng B = Lng M - m"
  proof -
    have "Lng B = Suc (Lng M - 1) - m" using Beq by simp
    thus ?thesis using mlt LMpos by linarith
  qed
  have LRsB: "Lng ?Rs = Lng M - m" using LRs LB by simp
  have mpos: "0 < m"
  proof -
    have "FirstNodes M ! Jstar = TrMax M + 1 + IdxSum (Br M) ! Jstar"
      by (rule FirstNodes_nth[OF JBr])
    hence "m = TrMax M + 1 + IdxSum (Br M) ! Jstar" unfolding m_def by simp
    thus ?thesis by simp
  qed
  have LNm1: "Lng N - 1 = (Lng M - 1) - m + entry M 1 m"
  proof (cases "0 < entry M 1 m")
    case True
    have NeqU: "N = diagSeq 0 (entry M 1 m - 1) @ ?Rs" unfolding N_def B_def Jstar_def using True by simp
    have LdiagN: "Lng (diagSeq 0 (entry M 1 m - 1)) = entry M 1 m"
      using True by (simp add: diagSeq_def)
    have "Lng N = entry M 1 m + (Lng M - m)" using NeqU LdiagN LRsB by simp
    thus ?thesis using mlt mpos True by simp
  next
    case False
    hence z': "entry M 1 m = 0" by simp
    have NeqU: "N = ?Rs" unfolding N_def B_def Jstar_def using False by simp
    have "Lng N = Lng M - m" using NeqU LRsB by simp
    thus ?thesis using mlt mpos z' by simp
  qed
  show ?thesis
    using rN e0N LNm1 Beq eB10 eRs10 by blast
qed




text \<open>\<open>Lng N - 1 = j'\<^sub>1 - j'\<^sub>0 + M\<^bsub>1,j'\<^sub>0\<^esub>\<close> (content.md 1228).\<close>

lemma Lng_bwdN_minus1:
  shows "Lng (bwdN M j0' j1') - 1 = (j1' - j0') + entry M 1 j0'"
  by (simp add: Lng_bwdN)

text \<open>The backward IH-decrease (content.md 1228): given the row-1 coefficient bound
  \<open>M\<^bsub>1,j'\<^sub>0\<^esub> < j'\<^sub>0\<close> (supplied by condAB_coeff (3) at the next-tie \<open>j'\<^sub>0\<close>) and
  \<open>j'\<^sub>1 \<le> j\<^sub>1\<close>, the backward column \<open>N\<close> is strictly shorter: \<open>Lng N - 1 < j\<^sub>1\<close>.
  Hence the IH applies to \<open>N\<close>.  Pure arithmetic on @{thm [source] Lng_bwdN_minus1}.\<close>

lemma bwdN_Lng_lt:
  assumes m1lt: "entry M 1 j0' < j0'" and jord: "j0' \<le> j1'" and jle: "j1' \<le> j1"
  shows "Lng (bwdN M j0' j1') - 1 < j1"
proof -
  have "Lng (bwdN M j0' j1') - 1 = (j1' - j0') + entry M 1 j0'"
    by (rule Lng_bwdN_minus1)
  also have "\<dots> < (j1' - j0') + j0'" using m1lt by simp
  also have "(j1' - j0') + j0' = j1'" using jord by simp
  finally show ?thesis using jle by simp
qed

text \<open>Brick A' (junction-and-prefix entry): \<open>entry N 0 p = p\<close> for \<open>p < m\<^sub>1\<^sub>0\<close> and the
  junction \<open>entry N i m\<^sub>1\<^sub>0 = entry M i 0\<close>.\<close>

lemma cAm10_entry_prefix:
  assumes m10pos: "0 < m10" and p: "p \<le> m10 - 1"
  shows "entry (diagSeq 0 (m10 - 1) @ M) i p = p"
  using p by (rule entry_diagSeq_append_lo)

text \<open>\<S>6.6 KEYSTONE BACKWARD monoT-core, PER-BRANCH REFORMULATION (Front B, tag
  pss-bwdcore-master).  Restates the per-branch obligation
    \<open>(IncrFirst ^^ e\<^sub>J) (Red (N\<^sub>J M J)) = Br M ! J\<close>
  in the EQUIVALENT form \<open>N\<^sub>J (Red M) J = Br M ! J\<close>, via the GREEN
  @{thm [source] a1_NJ_Red_eq} (which states
  \<open>N\<^sub>J (Red M) J = (IncrFirst ^^ e\<^sub>J) (Red (N\<^sub>J M J))\<close>).  EMPIRICAL: both forms hold
  96/96 over the core-nontrunk A&B branches; also \<open>Br (Red M) ! J = Br M ! J\<close>
  96/96.  This packages the obligation so the remaining induction only has to
  characterise \<open>N\<^sub>J (Red M) J\<close> (equivalently the J-th fundamental block of
  \<open>Red M\<close>) and match it to \<open>Br M ! J\<close>.\<close>

lemma kst_bwdcore_master_NJReform:
  assumes MT: "M \<in> T_PS" and mono: "monoT M"
    and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and condA: "RedCondA M"
    and tne: "TrMax M \<noteq> Lng M - 1"
    and njblocks: "\<And>J. J < Lng (Br M) \<Longrightarrow> NJ (Red M) J = Br M ! J"
  shows "Red M = M"
proof -
  have M_PT: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  have blocks: "\<And>J. J < Lng (Br M) \<Longrightarrow>
      (IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J)) = Br M ! J"
  proof -
    fix J assume JBr: "J < Lng (Br M)"
    have "NJ (Red M) J = (IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J))"
      by (rule a1_NJ_Red_eq[OF M_PT c0 c1 tne JBr])
    moreover have "NJ (Red M) J = Br M ! J" by (rule njblocks[OF JBr])
    ultimately show "(IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J)) = Br M ! J"
      by simp
  qed
  show ?thesis by (rule kst_bwdcore_master[OF MT mono c0 c1 condA blocks])
qed


text \<open>\<S>6.6 KEYSTONE BACKWARD, G-INSTANCE WIRING (Front A, tag pss-bwdcore-G).
  Confirms that the keystone's per-branch obligation is LITERALLY G specialised
  to \<open>N\<^sub>J M J\<close> (with the IncrFirst-power read off \<open>N\<^sub>J M J\<close>'s own head): if a
  generalized statement \<open>Gstmt\<close> of the shape

    \<open>\<And>N. N \<in> T_PS \<Longrightarrow> monoT N \<Longrightarrow> RedCondA N \<Longrightarrow> entry N 1 0 \<le> entry N 0 0
        \<Longrightarrow> (IncrFirst ^^ (entry N 0 0 - entry N 1 0)) (Red N) = N\<close>

  is available, it discharges the keystone via @{thm [source]
  kst_bwdcore_master_via_G}, provided each \<open>N\<^sub>J M J\<close> meets G's hypotheses
  (\<open>N\<^sub>J M J \<in> T_PS\<close>, monoT-or-zeroT, RedCondA, row-1 \<open>\<le>\<close> row-0).  This is the
  single open obligation that unblocks \<S>6.5 \<open>Red_le\<close>.  Cites only GREEN facts.\<close>

lemma kst_bwdcore_master_of_Gstmt:
  assumes MT: "M \<in> T_PS" and mono: "monoT M"
    and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and condA: "RedCondA M"
    and Gstmt: "\<And>N. N \<in> T_PS \<Longrightarrow> monoT N \<Longrightarrow> RedCondA N
        \<Longrightarrow> entry N 1 0 \<le> entry N 0 0
        \<Longrightarrow> (IncrFirst ^^ (entry N 0 0 - entry N 1 0)) (Red N) = N"
    and Ghyp: "\<And>J. J < Lng (Br M) \<Longrightarrow>
        NJ M J \<in> T_PS \<and> monoT (NJ M J) \<and> RedCondA (NJ M J)
          \<and> entry (NJ M J) 1 0 \<le> entry (NJ M J) 0 0"
  shows "Red M = M"
proof (rule kst_bwdcore_master_via_G[OF MT mono c0 c1 condA])
  fix J assume JBr: "J < Lng (Br M)"
  have h: "NJ M J \<in> T_PS \<and> monoT (NJ M J) \<and> RedCondA (NJ M J)
            \<and> entry (NJ M J) 1 0 \<le> entry (NJ M J) 0 0"
    by (rule Ghyp[OF JBr])
  show "(IncrFirst ^^ (entry (NJ M J) 0 0 - entry (NJ M J) 1 0)) (Red (NJ M J)) = NJ M J"
    by (rule Gstmt) (use h in auto)
qed



text \<open>\<S>6.6 KEYSTONE BACKWARD, INVERSE-SHIFT REDUCTION (Front B, tag
  pss-bwdcore-invshift).  Reduces the inverse-shift identity
  \<open>IncrFirst\<^bsup>e\<^esup> (Red X) = X\<close> (\<open>e = m\<^sub>0\<^sub>0 - m\<^sub>1\<^sub>0\<close>) to the UNIFORM \<open>Red\<close>-CHARACTERISATION
    \<open>Red X = rebaseRow0 e 0 X\<close>      (= \<open>X\<close> with row 0 lowered uniformly by \<open>e\<close>).
  EMPIRICAL (\<open>/tmp/fb_uniform.py\<close>): the uniform characterisation
  \<open>Red X = rebaseRow0 (m\<^sub>0\<^sub>0-m\<^sub>1\<^sub>0) 0 X\<close> holds 1975/1975 over the non-multi
  \<open>RedCondA\<close> sequences with \<open>m\<^sub>1\<^sub>0 \<le> m\<^sub>0\<^sub>0\<close> (len\<le>5, vals\<le>3).  Given that
  characterisation and the lower-bound \<open>e \<le> entry X 0 j\<close> (from \<open>monoT\<close>:
  \<open>e = m\<^sub>0\<^sub>0 - m\<^sub>1\<^sub>0 \<le> m\<^sub>0\<^sub>0 \<le> entry X 0 j\<close>), the inverse-shift identity follows by
  pure entry algebra (@{thm [source] bwd_IncrFirst_e_rebaseRow0}).\<close>

lemma bwd_invshift_from_uniform_Red:
  assumes lb: "\<And>j. j < Lng X \<Longrightarrow> entry X 0 0 - entry X 1 0 \<le> entry X 0 j"
    and redchar: "Red X = rebaseRow0 (entry X 0 0 - entry X 1 0) 0 X"
  shows "(IncrFirst ^^ (entry X 0 0 - entry X 1 0)) (Red X) = X"
proof -
  let ?e = "entry X 0 0 - entry X 1 0"
  have "(IncrFirst ^^ ?e) (Red X) = (IncrFirst ^^ ?e) (rebaseRow0 ?e 0 X)"
    using redchar by simp
  also have "\<dots> = X" by (rule bwd_IncrFirst_e_rebaseRow0[OF lb])
  finally show ?thesis .
qed

text \<open>\<S>6.6 KEYSTONE BACKWARD INVERSE-SHIFT, zeroT BASE CASE (Front B, tag
  pss-bwdcore-invshift).  For \<open>zeroT X\<close> (\<open>Lng X = 1\<close>, \<open>m\<^sub>1\<^sub>0 = 0\<close>, so
  \<open>X = [(m\<^sub>0\<^sub>0,0)]\<close>) the \<open>Red\<close> base case gives \<open>Red X = [(0,0)] = rebaseRow0 m\<^sub>0\<^sub>0 0 X\<close>
  and \<open>e = m\<^sub>0\<^sub>0 - 0 = m\<^sub>0\<^sub>0\<close>, so the inverse-shift identity is pure entry algebra.
  This base case has NO IH dependency.  EMPIRICAL (\<open>/tmp/fb_gen3.py\<close>): part of
  the 396/396 inverse-shift population (the 37 zeroT branches of the keystone).\<close>

lemma bwd_invshift_zeroT:
  assumes z: "zeroT X" and XT: "X \<in> T_PS"
  shows "(IncrFirst ^^ (entry X 0 0 - entry X 1 0)) (Red X) = X"
proof -
  let ?e = "entry X 0 0 - entry X 1 0"
  have c1: "entry X 1 0 = 0" using z by (simp add: zeroT_def)
  have L1: "Lng X = 1" using z by (simp add: zeroT_def)
  have e_m00: "?e = entry X 0 0" using c1 by simp
  have domX: "Red_dom X" by (rule m_6_5_Red_welldef[OF XT])
  have rX: "Red X = [(0, 0)]" using Red.psimps[OF domX] z by simp
  \<comment> \<open>\<open>Red X = rebaseRow0 e 0 X\<close>: both are the single pair \<open>(0,0)\<close>.\<close>
  have redchar: "Red X = rebaseRow0 ?e 0 X"
  proof (rule nth_equalityI)
    show "Lng (Red X) = Lng (rebaseRow0 ?e 0 X)" using rX L1 by simp
  next
    fix j assume "j < Lng (Red X)"
    hence j0: "j = 0" using rX by simp
    have e0: "entry (rebaseRow0 ?e 0 X) 0 0 = 0"
      using entry_rebaseRow0_0[of 0 X ?e 0] L1 e_m00 by simp
    have e1: "entry (rebaseRow0 ?e 0 X) 1 0 = 0"
      using entry_rebaseRow0_1[of 0 X ?e 0] L1 c1 by simp
    have "rebaseRow0 ?e 0 X ! 0 = (0, 0)"
      using e0 e1 by (simp add: entry_def prod_eq_iff)
    thus "Red X ! j = rebaseRow0 ?e 0 X ! j" using rX j0 by simp
  qed
  \<comment> \<open>lower bound: \<open>e = m\<^sub>0\<^sub>0 \<le> entry X 0 j\<close> (\<open>j = 0\<close> is the only index).\<close>
  have lb: "\<And>j. j < Lng X \<Longrightarrow> ?e \<le> entry X 0 j"
  proof -
    fix j assume "j < Lng X"
    hence "j = 0" using L1 by simp
    thus "?e \<le> entry X 0 j" using e_m00 by simp
  qed
  show ?thesis by (rule bwd_invshift_from_uniform_Red[OF lb redchar])
qed

text \<open>\<S>6.6 KEYSTONE BACKWARD INVERSE-SHIFT, \<open>m\<^sub>1\<^sub>0 = 0\<close> monoT CASE (Front B, tag
  pss-bwdcore-invshift).  For monoT \<open>X\<close> with \<open>m\<^sub>1\<^sub>0 = 0\<close> (so \<open>e = m\<^sub>0\<^sub>0\<close>),
  @{thm [source] cdn_Red_shiftRow0_m10z} gives \<open>Red X = Red (shiftRow0 X)\<close>, and
  \<open>shiftRow0 X\<close> is CORE (\<open>m\<^sub>0\<^sub>0 = m\<^sub>1\<^sub>0 = 0\<close>) and nu-smaller (it equals
  \<open>coreReduce X\<close> when \<open>m\<^sub>1\<^sub>0 = 0\<close>, @{thm [source] nu_coreReduce_lt}).  GIVEN the
  reducedness of \<open>shiftRow0 X\<close> (\<open>Red (shiftRow0 X) = shiftRow0 X\<close>) — supplied by
  the core-keystone IH in the master nu-induction — the inverse-shift identity
  follows: \<open>Red X = shiftRow0 X = rebaseRow0 m\<^sub>0\<^sub>0 0 X\<close>, then entry algebra.
  EMPIRICAL (\<open>/tmp/fb_m10z_self.py\<close>): \<open>shiftRow0 X\<close> is core, has \<open>RedCondA\<close> &
  \<open>RedCondB\<close>, and \<open>Red (shiftRow0 X) = shiftRow0 X\<close> 700/700 over the \<open>m\<^sub>1\<^sub>0 = 0\<close>
  non-multi \<open>RedCondA\<close> population.\<close>

lemma bwd_invshift_m10z_monoT:
  assumes XT: "X \<in> T_PS" and mono: "monoT X" and c1: "entry X 1 0 = 0"
    and shred: "Red (shiftRow0 X) = shiftRow0 X"
  shows "(IncrFirst ^^ (entry X 0 0 - entry X 1 0)) (Red X) = X"
proof -
  let ?e = "entry X 0 0 - entry X 1 0"
  have e_m00: "?e = entry X 0 0" using c1 by simp
  \<comment> \<open>\<open>Red X = shiftRow0 X\<close>.\<close>
  have rX: "Red X = shiftRow0 X"
    using cdn_Red_shiftRow0_m10z[OF XT mono c1] shred by simp
  \<comment> \<open>\<open>shiftRow0 X = rebaseRow0 m\<^sub>0\<^sub>0 0 X\<close>.\<close>
  have shr_eq: "shiftRow0 X = rebaseRow0 (entry X 0 0) 0 X"
  proof (rule nth_equalityI)
    show "Lng (shiftRow0 X) = Lng (rebaseRow0 (entry X 0 0) 0 X)" by simp
  next
    fix j assume "j < Lng (shiftRow0 X)"
    hence jl: "j < Lng X" by simp
    have s0: "entry (shiftRow0 X) 0 j = entry X 0 j - entry X 0 0"
      by (rule entry_shiftRow0_0[OF jl])
    have s1: "entry (shiftRow0 X) 1 j = entry X 1 j" by (rule entry_shiftRow0_1[OF jl])
    have r0: "entry (rebaseRow0 (entry X 0 0) 0 X) 0 j = entry X 0 j - entry X 0 0"
      using entry_rebaseRow0_0[OF jl] by simp
    have r1: "entry (rebaseRow0 (entry X 0 0) 0 X) 1 j = entry X 1 j"
      by (rule entry_rebaseRow0_1[OF jl])
    show "shiftRow0 X ! j = rebaseRow0 (entry X 0 0) 0 X ! j"
      using s0 s1 r0 r1 by (simp add: entry_def prod_eq_iff)
  qed
  have redchar: "Red X = rebaseRow0 ?e 0 X" using rX shr_eq e_m00 by simp
  \<comment> \<open>lower bound: \<open>e = m\<^sub>0\<^sub>0 \<le> entry X 0 j\<close> by \<open>monoT\<close>.\<close>
  have lb: "\<And>j. j < Lng X \<Longrightarrow> ?e \<le> entry X 0 j"
  proof -
    fix j assume jl: "j < Lng X"
    have "entry X 0 0 \<le> entry X 0 j" by (rule entry0_ge_min[OF XT mono jl])
    thus "?e \<le> entry X 0 j" using e_m00 by simp
  qed
  show ?thesis by (rule bwd_invshift_from_uniform_Red[OF lb redchar])
qed

text \<open>
  \<S>6.5 ROW-1 FRAGMENT of the ancestor-order Red-invariance (Front B).

  The goal \<open>leR M i j0 j1 = leR (Red M) i j0 j1\<close> splits (via @{thm leR_def})
  into a row-0 fragment (\<open>le0 M = le0 (Red M)\<close>) and a row-1 fragment
  (\<open>le1 M = le1 (Red M)\<close>).  The row-1 relation \<open>nextrel1\<close> (@{thm nextrel1_def})
  is built ENTIRELY from \<open>le0\<close> plus the row-1 entries \<open>entry \<cdot> 1 \<cdot>\<close>.  Hence,
  once the row-0 fragment (\<open>le0\<close>-invariance) is in hand and the row-1 entries
  agree column-wise, the row-1 fragment follows with no further reference to
  \<open>Red\<close>.

  We bank this as a clean, \<open>Red\<close>-independent abstract brick: it takes the
  \<open>le0\<close>-equality (the row-0 fragment) and the column-wise row-1 equality as
  explicit hypotheses, and concludes \<open>nextrel1\<close>-, \<open>le1\<close>-, and \<open>leR\<close>-equality.
  This mirrors @{thm [source] tail_bump.leR_eq} but is decoupled from the
  \<open>bumpv\<close> shape, so it composes with whatever route establishes \<open>le0\<close>-invariance
  (e.g. Front A's row-0 fragment).
\<close>

lemma row1_le0_imp_nextrel1_eq:
  assumes Llen: "Lng A = Lng X"
    and le0eq: "le0 A = le0 X"
    and row1:  "\<And>j. j < Lng X \<Longrightarrow> entry A 1 j = entry X 1 j"
  shows "nextrel1 A = nextrel1 X"
proof (intro ext)
  fix a b
  show "nextrel1 A a b = nextrel1 X a b"
  proof (cases "a < Lng X \<and> b < Lng X")
    case True
    hence aX: "a < Lng X" and bX: "b < Lng X" by auto
    have e1a: "entry A 1 a = entry X 1 a" by (rule row1[OF aX])
    have e1b: "entry A 1 b = entry X 1 b" by (rule row1[OF bX])
    \<comment> \<open>The universal tail of \<open>nextrel1\<close> is over \<open>le0\<close>-reachable \<open>j\<close>; on those
        \<open>j < Lng X\<close>, so the row-1 entries agree.\<close>
    have U: "(\<forall>j. a < j \<and> le0 X j b \<longrightarrow> entry A 1 b \<le> entry A 1 j)
              = (\<forall>j. a < j \<and> le0 X j b \<longrightarrow> entry X 1 b \<le> entry X 1 j)"
    proof (rule all_cong1)
      fix j
      show "(a < j \<and> le0 X j b \<longrightarrow> entry A 1 b \<le> entry A 1 j)
          = (a < j \<and> le0 X j b \<longrightarrow> entry X 1 b \<le> entry X 1 j)"
      proof (cases "a < j \<and> le0 X j b")
        case True
        hence jX: "j < Lng X" by (simp add: le0_def)
        show ?thesis using e1b row1[OF jX] by simp
      next
        case False
        thus ?thesis by blast
      qed
    qed
    have "nextrel1 A a b =
       (a < Lng X \<and> b < Lng X \<and> a < b \<and>
        entry A 1 a < entry A 1 b \<and> le0 X a b \<and>
        (\<forall>j. a < j \<and> le0 X j b \<longrightarrow> entry A 1 b \<le> entry A 1 j))"
      unfolding nextrel1_def by (simp add: Llen le0eq)
    also have "\<dots> =
       (a < Lng X \<and> b < Lng X \<and> a < b \<and>
        entry X 1 a < entry X 1 b \<and> le0 X a b \<and>
        (\<forall>j. a < j \<and> le0 X j b \<longrightarrow> entry X 1 b \<le> entry X 1 j))"
      using e1a e1b U by simp
    also have "\<dots> = nextrel1 X a b"
      unfolding nextrel1_def by (simp add: Llen le0eq)
    finally show ?thesis .
  next
    case False
    thus ?thesis by (auto simp: nextrel1_def Llen)
  qed
qed

lemma row1_le0_imp_le1_eq:
  assumes Llen: "Lng A = Lng X"
    and le0eq: "le0 A = le0 X"
    and row1:  "\<And>j. j < Lng X \<Longrightarrow> entry A 1 j = entry X 1 j"
  shows "le1 A = le1 X"
  by (intro ext)
     (simp add: le1_def row1_le0_imp_nextrel1_eq[OF Llen le0eq row1] Llen)

text \<open>
  Assembling the two fragments: given \<open>Lng\<close>-equality, \<open>le0\<close>-equality (row-0
  fragment) and column-wise row-1 agreement, the full ancestor order \<open>leR\<close>
  coincides on both rows.  This is the shape of the \<S>6.5 conclusion; with
  \<open>X = M\<close>, \<open>A = Red M\<close> it is exactly \<open>leR M = leR (Red M)\<close> once the row-0
  fragment and the row-1 column agreement are supplied.
\<close>

lemma row1_le0_imp_leR_eq:
  assumes Llen: "Lng A = Lng X"
    and le0eq: "le0 A = le0 X"
    and row1:  "\<And>j. j < Lng X \<Longrightarrow> entry A 1 j = entry X 1 j"
  shows "leR A = leR X"
proof (intro ext)
  fix i j0 j1
  show "leR A i j0 j1 = leR X i j0 j1"
    by (cases "i = 0")
       (simp_all add: leR_def le0eq row1_le0_imp_le1_eq[OF Llen le0eq row1])
qed


text \<open>§6.7 oper-tiling brick (Front B, ROW 1): the verbatim row-1 READING at a
  WITHIN-BLOCK column \<open>j\<^sub>0 \<le> x < Lng (N[n])\<close>.  Since \<open>d\<^sub>1 = 0\<close> (\<open>i\<^sub>1 \<le> 1\<close>), the
  row-1 value of \<open>N[n]\<close> at \<open>x\<close> is the row-1 value of \<open>N\<close> at the period base
  \<open>j\<^sub>0 + (x - j\<^sub>0) mod w\<close>.  Specializes @{thm [source] operCA_tiling_entry1_base}
  (the \<open>z \<ge> j\<^sub>0\<close> branch), discharging its range hypothesis \<open>zlt\<close> from
  \<open>x < Lng (N[n]) = j\<^sub>0 + n\<cdot>w\<close> (@{thm [source] operB_gen_LngM}).  This is the
  \<open>x'\<close>-supplier (and the \<open>ex\<close> input) for
  @{thm [source] operCA_tiling_within1_via_reflect}.\<close>

lemma operCA_tiling_within1_ex:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> x"
    and xlt: "x < Lng ((N::pairseq)[n])"
  shows "entry ((N::pairseq)[n]) 1 x
       = entry N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
            + (x - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
               mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  have zlt: "x < ?j0 + n * ?w"
    using xlt operB_gen_LngM[OF L notzero hp j0lt] by simp
  have nge: "\<not> x < ?j0" using ge by simp
  show ?thesis
    using operCA_tiling_entry1_base[OF L notzero hp j0lt zlt] nge by simp
qed


text \<open>Helper (i0, BACKWARD in-block \<open>le0\<close>): a row-0 reachability chain
  \<open>le0 (N[n]) (j\<^sub>0+q\<cdot>w+s\<^sub>p) x\<close> starting at block \<open>q\<close> (offset \<open>s\<^sub>p < w\<close>) is, by
  block-confinement @{thm [source] oper_d0zero_le0_confined}, entirely inside block
  \<open>q\<close>; each step folds back to the base slice by
  @{thm [source] oper_d0zero_nextrel0_inblock_back}, so the whole chain reflects to
  \<open>le0 N (j\<^sub>0+s\<^sub>p) (base x)\<close>.\<close>

lemma oper_d0zero_le0_inblock_back:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 0"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and qn: "q < n"
    and sp: "sp < Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and reach: "le0 ((N::pairseq)[n])
                  (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                     + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)) + sp) x"
  shows "le0 N (parent N (idx1 N (Lng N - 1)) (Lng N - 1) + sp)
              (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                 + (x - (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                          + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))))"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?Nn = "(N::pairseq)[n]"
  let ?p = "?j0 + q * ?w + sp"
  let ?j0eq = "?j0 = parent N 0 ?j1"
  have w0: "0 < ?w" using j0lt by linarith
  have j0eq: "?j0 = parent N 0 ?j1" using i1z by simp
  have j0lt0: "parent N 0 ?j1 < ?j1" using j0lt j0eq by simp
  have lenNn: "Lng ?Nn = ?j0 + n * ?w"
    by (rule operB_gen_LngM[OF L notzero hp j0lt])
  have pge: "?j0 \<le> ?p" by simp
  have plt: "?p < Lng ?Nn"
  proof -
    have "?p < ?j0 + q * ?w + ?w" using sp by linarith
    also have "\<dots> = ?j0 + (q + 1) * ?w" by simp
    also have "\<dots> \<le> ?j0 + n * ?w" using mult_le_mono1[of "q+1" n ?w] qn by simp
    finally show ?thesis using lenNn by simp
  qed
  have p0ge: "parent N 0 ?j1 \<le> ?p" using pge j0eq by simp
  \<comment> \<open>the reachability part of \<open>le0\<close>\<close>
  have chain: "(nextrel0 ?Nn)\<^sup>*\<^sup>* ?p x" using reach by (simp add: le0_def)
  \<comment> \<open>block confinement: every node \<open>y\<close> with \<open>(nextrel0 N[n])^** p y\<close> stays in block \<open>q\<close>\<close>
  have qdiv: "(?p - ?j0) div ?w = q" using sp by simp
  \<comment> \<open>strengthened: chain to \<open>y\<close> implies the base reflection holds for \<open>y\<close>\<close>
  have main: "\<And>y. (nextrel0 ?Nn)\<^sup>*\<^sup>* ?p y \<Longrightarrow>
        ?j0 + q * ?w \<le> y \<and> y < ?j0 + (q + 1) * ?w
          \<and> le0 N (?j0 + sp) (?j0 + (y - (?j0 + q * ?w)))"
  proof -
    fix y assume "(nextrel0 ?Nn)\<^sup>*\<^sup>* ?p y"
    thus "?j0 + q * ?w \<le> y \<and> y < ?j0 + (q + 1) * ?w
            \<and> le0 N (?j0 + sp) (?j0 + (y - (?j0 + q * ?w)))"
    proof (induction rule: rtranclp_induct)
      case base
      have le0refl: "le0 N (?j0 + sp) (?j0 + sp)"
      proof -
        have "?j0 + sp < Lng N" using sp L j0lt by linarith
        thus ?thesis by (simp add: le0_def)
      qed
      have b1: "?j0 + q * ?w \<le> ?p" by simp
      have b2: "?p < ?j0 + (q + 1) * ?w"
      proof -
        have "?p < ?j0 + q * ?w + ?w" using sp by linarith
        also have "\<dots> = ?j0 + (q + 1) * ?w" by simp
        finally show ?thesis .
      qed
      have b3: "?p - (?j0 + q * ?w) = sp" by simp
      have le0refl': "le0 N (?j0 + sp) (?j0 + (?p - (?j0 + q * ?w)))"
        using le0refl b3 by simp
      show ?case using b1 b2 le0refl' by (intro conjI)
    next
      case (step y z)
      have Py: "?j0 + q * ?w \<le> y" and Pyb: "y < ?j0 + (q + 1) * ?w"
        and IHle: "le0 N (?j0 + sp) (?j0 + (y - (?j0 + q * ?w)))"
        using step.IH by auto
      have nyz: "nextrel0 ?Nn y z" by (rule step.hyps(2))
      \<comment> \<open>confine \<open>z\<close>: \<open>(nextrel0 N[n])^** p z\<close>, start \<open>p \<ge> parent N 0 j\<^sub>1\<close>\<close>
      have chPz: "(nextrel0 ?Nn)\<^sup>*\<^sup>* ?p z"
        using step.hyps(1) nyz by (simp add: rtranclp.rtrancl_into_rtrancl)
      have zconf: "z < parent N 0 ?j1
                     + ((?p - parent N 0 ?j1) div (?j1 - parent N 0 ?j1) + 1) * (?j1 - parent N 0 ?j1)"
        by (rule oper_d0zero_le0_confined[OF L notzero hp i1z p0ge plt chPz])
      have qdiv0: "(?p - parent N 0 ?j1) div (?j1 - parent N 0 ?j1) = q"
        using qdiv j0eq by simp
      have zconf2: "z < parent N 0 ?j1 + (q + 1) * (?j1 - parent N 0 ?j1)"
        using zconf qdiv0 by simp
      have zub: "z < ?j0 + (q + 1) * ?w"
        using zconf2 unfolding j0eq[symmetric] .
      have ylez: "y < z" using nyz by (simp add: nextrel0_def)
      have zge: "?j0 + q * ?w \<le> z" using Py ylez by linarith
      \<comment> \<open>offsets of \<open>y, z\<close> in block \<open>q\<close>\<close>
      let ?sy = "y - (?j0 + q * ?w)"  let ?sz = "z - (?j0 + q * ?w)"
      have q1w: "?j0 + (q + 1) * ?w = ?j0 + q * ?w + ?w" by simp
      have syw: "?sy < ?w" using Pyb Py q1w by linarith
      have szw: "?sz < ?w" using zub zge q1w by linarith
      have ysplit: "y = ?j0 + q * ?w + ?sy" using Py by simp
      have zsplit: "z = ?j0 + q * ?w + ?sz" using zge by simp
      have nyz': "nextrel0 ?Nn (?j0 + q * ?w + ?sy) (?j0 + q * ?w + ?sz)"
        using nyz ysplit zsplit by simp
      have baseStep: "nextrel0 N (?j0 + ?sy) (?j0 + ?sz)"
        by (rule oper_d0zero_nextrel0_inblock_back[OF L notzero hp i1z j0lt qn syw szw nyz'])
      \<comment> \<open>extend the base chain\<close>
      have zN: "?j0 + ?sz < Lng N" using szw L j0lt by linarith
      have leExt: "le0 N (?j0 + sp) (?j0 + ?sz)"
      proof -
        have c1: "(nextrel0 N)\<^sup>*\<^sup>* (?j0 + sp) (?j0 + ?sy)"
          using IHle by (simp add: le0_def)
        have c2: "(nextrel0 N)\<^sup>*\<^sup>* (?j0 + ?sy) (?j0 + ?sz)"
          using baseStep by (rule r_into_rtranclp)
        have "(nextrel0 N)\<^sup>*\<^sup>* (?j0 + sp) (?j0 + ?sz)"
          using c1 c2 by (rule rtranclp_trans)
        moreover have "?j0 + sp < Lng N" using sp L j0lt by linarith
        ultimately show ?thesis using zN by (simp add: le0_def)
      qed
      show ?case using zge zub leExt by simp
    qed
  qed
  show ?thesis using main[OF chain] by (elim conjE)
qed

text \<open>§6.7 oper-tiling brick (Front B, ROW 1, \<open>i\<^sub>1=1\<close>): \<open>le0 (N[n]) j\<^sub>0 x\<close> for any
  within-block column \<open>j\<^sub>0 \<le> x < Lng(N[n])\<close>.  The block-0 start \<open>j\<^sub>0\<close> reaches every
  column \<open>x \<ge> j\<^sub>0\<close> by the row-0 reachability of @{thm [source]
  oper_d1pos_le0_start_to_any} (specialised to the start block \<open>k=0\<close>).  This is
  the \<open>le0 (N[n]) p x\<close> witness's anchor for the row-1 parent reflection.\<close>

lemma operCA_tiling_fb_d1pos_le0_j0_to_x:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and n1: "1 \<le> n"
    and ge: "parent N 1 (Lng N - 1) \<le> x"
    and xlt: "x < Lng ((N::pairseq)[n])"
  shows "le0 ((N::pairseq)[n]) (parent N 1 (Lng N - 1)) x"
proof -
  have NT: "N \<in> T_PS" using L by (cases N) (auto simp: T_PS_def)
  have k0n: "(0::nat) < n" using n1 by simp
  have ge0: "parent N 1 (Lng N - 1) + 0 * (Lng N - 1 - parent N 1 (Lng N - 1)) \<le> x"
    using ge by simp
  have "le0 ((N::pairseq)[n])
            (parent N 1 (Lng N - 1) + 0 * (Lng N - 1 - parent N 1 (Lng N - 1))) x"
    by (rule oper_d1pos_le0_start_to_any[OF NT L notzero hp i1z j0lt k0n ge0 xlt])
  thus ?thesis by simp
qed


text \<open>§6.7 oper-tiling ROW-1 (Front A, i1=1) VALLEY reduced to per-competitor
  BASE COMPARABILITY.  The valley obligation of @{thm [source]
  operCA_tiling_bcorr_reduced} (any competitor j with pstar<j and le0 (N[n]) j y
  has entry (N[n]) 1 y \<le> entry (N[n]) 1 j) is closed once each such competitor's
  base (base j = if j<j0 then j else j0+(j-j0) mod w) satisfies EITHER base j = y'
  (period base of y) OR (parent N 1 y' < base j \<and> le0 N (base j) y').  Route:
  entry (N[n]) 1 j = entry N 1 (base j), entry (N[n]) 1 y = entry N 1 y'
  (@{thm [source] operCA_tiling_entry1_base'}, row-1 periodicity); in the second
  disjunct N's row-1 valley nextrel1 N (parent N 1 y') y' (from hpN) gives
  entry N 1 y' \<le> entry N 1 (base j).  Empirically the disjunction holds 136084/136084
  (/tmp/simple_route.py).\<close>

lemma operCA_tiling_bcorr_valley_reduced:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y"
    and hpny: "hasParent ((N::pairseq)[n]) 1 y"
    and hpN: "hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                   mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
    and comp: "parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                       + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                          mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                    < (if j < parent N (idx1 N (Lng N - 1)) (Lng N - 1) then j
                       else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                            + (j - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                               mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                  \<and> le0 N (if j < parent N (idx1 N (Lng N - 1)) (Lng N - 1) then j
                          else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                               + (j - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                                  mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                         (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                            + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                               mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                \<or> (if j < parent N (idx1 N (Lng N - 1)) (Lng N - 1) then j
                    else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                         + (j - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                            mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                   = parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                       + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                          mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
    and pstar_lt: "(if parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                              + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                                 mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                          < parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                       then parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                              + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                                 mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                       else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                              + ((y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                                 div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                                * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                              + (parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                                    + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                                       mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                                 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                        < j"
    and reach: "le0 ((N::pairseq)[n]) j y"
  shows "entry ((N::pairseq)[n]) 1 y \<le> entry ((N::pairseq)[n]) 1 j"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?Nn = "(N::pairseq)[n]"
  let ?sy = "(y - ?j0) mod ?w"
  let ?yp = "?j0 + ?sy"
  let ?pN = "parent N 1 ?yp"
  let ?bj = "if j < ?j0 then j else ?j0 + (j - ?j0) mod ?w"
  have w0: "0 < ?w" using j0lt by linarith
  have j0w1: "?j0 + ?w = ?j1" using j0lt by simp
  \<comment> \<open>row-1 reading at y: entry (N[n]) 1 y = entry N 1 y'\<close>
  have yNn: "y < Lng ?Nn"
  proof -
    have "\<exists>!a. nextR ?Nn 1 a y" using hpny unfolding hasParent_def by simp
    hence "nextR ?Nn 1 (parent ?Nn 1 y) y" unfolding parent_def by (rule theI')
    hence "nextrel1 ?Nn (parent ?Nn 1 y) y" by (simp add: nextR_def)
    thus ?thesis by (simp add: nextrel1_def)
  qed
  have nge: "\<not> y < ?j0" using ge by simp
  have e1y: "entry ?Nn 1 y = entry N 1 ?yp"
  proof -
    have "entry ?Nn 1 y = entry N 1 (if y < ?j0 then y else ?j0 + (y - ?j0) mod ?w)"
      by (rule operCA_tiling_entry1_base'[OF L notzero hp j0lt yNn])
    thus ?thesis using nge by simp
  qed
  \<comment> \<open>row-1 reading at j: entry (N[n]) 1 j = entry N 1 (base j)\<close>
  have jNn: "j < Lng ?Nn" using reach by (simp add: le0_def)
  have e1j: "entry ?Nn 1 j = entry N 1 ?bj"
    by (rule operCA_tiling_entry1_base'[OF L notzero hp j0lt jNn])
  \<comment> \<open>N's row-1 valley at y' from hpN\<close>
  have hpN': "hasParent N 1 ?yp" using hpN by simp
  have nrelN: "nextrel1 N ?pN ?yp"
  proof -
    have "\<exists>!a. nextR N 1 a ?yp" using hpN' unfolding hasParent_def by simp
    hence "nextR N 1 ?pN ?yp" unfolding parent_def by (rule theI')
    thus ?thesis by (simp add: nextR_def)
  qed
  have Nvalley: "\<And>c. ?pN < c \<Longrightarrow> le0 N c ?yp \<Longrightarrow> entry N 1 ?yp \<le> entry N 1 c"
    using nrelN by (simp add: nextrel1_def)
  \<comment> \<open>apply comparability\<close>
  have disj: "(?pN < ?bj \<and> le0 N ?bj ?yp) \<or> ?bj = ?yp"
    using comp by simp
  have e1yle: "entry N 1 ?yp \<le> entry N 1 ?bj"
  proof (cases "?bj = ?yp")
    case True thus ?thesis by simp
  next
    case False
    hence "?pN < ?bj \<and> le0 N ?bj ?yp" using disj by blast
    thus ?thesis using Nvalley by blast
  qed
  show ?thesis using e1y e1j e1yle by simp
qed



text \<open>Front B: §6.7/§6.5 cascade conditional on hpN+valley assembled.\<close>


text \<open>§6.7 oper-tiling ROW-1 (Front A, i1=1) per-competitor BASE COMPARABILITY
  \<open>comp\<close> (the input of @{thm [source] operCA_tiling_bcorr_valley_reduced}), REDUCED
  to the two soundly-carried per-competitor OFFSET residuals:
  \<^item> \<open>antimono\<close>: within-tiling row-0 anti-monotonicity \<open>base j \<le> y'\<close>
    (\<open>(j-j\<^sub>0) mod w \<le> (y-j\<^sub>0) mod w\<close>; empirically 0-fail under the \<open>pstar<j\<close> barrier:
    /tmp/fa_valley_route.py 136084/136084, and the violation analysis
    /tmp/fa_why.py shows every anti-monotonicity violation has \<open>j \<le> pstar\<close>, so the
    barrier excludes all of them; structurally cross-block competitors surviving
    the barrier have \<open>pN < j\<^sub>0\<close>, /tmp/fa_pNlt.py 3424/3424), and
  \<^item> \<open>pNbj\<close>: \<open>parent N 1 y' < base j\<close> (empirically 0-fail, same enumeration).
  Given these two, the \<open>base j \<noteq> y'\<close> branch produces the first \<open>comp\<close> disjunct:
  \<open>le0 N (base j) y'\<close> is the cross/same-block backward reflection
  @{thm [source] oper_d1pos_ctx_period_le0Np} (instantiated at j's block-\<open>q\<^sub>j\<close>,
  offset-\<open>s\<^sub>j\<close> decode, target span \<open>y'\<close>, with the strict offset bound
  \<open>base j < y'\<close> from \<open>antimono\<close>+\<open>\<noteq>\<close>); the \<open>base j = y'\<close> branch is the second
  disjunct directly.  This packages ALL of \<open>comp\<close>'s machinery, leaving the two
  offset residuals as the sole obligations.\<close>

lemma operCA_tiling_valley_comp_reduced:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> j"
    and reach: "le0 ((N::pairseq)[n]) j y"
    and antimono: "(if j < parent N (idx1 N (Lng N - 1)) (Lng N - 1) then j
                      else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                           + (j - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                              mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                   \<le> parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                      + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                         mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
    and pNbj: "parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                  + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                     mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                 < (if j < parent N (idx1 N (Lng N - 1)) (Lng N - 1) then j
                    else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                         + (j - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                            mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
  shows "parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                       + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                          mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                    < (if j < parent N (idx1 N (Lng N - 1)) (Lng N - 1) then j
                       else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                            + (j - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                               mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                  \<and> le0 N (if j < parent N (idx1 N (Lng N - 1)) (Lng N - 1) then j
                          else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                               + (j - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                                  mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                         (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                            + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                               mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                \<or> (if j < parent N (idx1 N (Lng N - 1)) (Lng N - 1) then j
                    else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                         + (j - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                            mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                   = parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                       + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                          mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?Nn = "(N::pairseq)[n]"
  let ?sy = "(y - ?j0) mod ?w"
  let ?yp = "?j0 + ?sy"
  let ?pN = "parent N 1 ?yp"
  let ?sj = "(j - ?j0) mod ?w"
  let ?qj = "(j - ?j0) div ?w"
  let ?bj = "if j < ?j0 then j else ?j0 + ?sj"
  have w0: "0 < ?w" using j0lt by linarith
  have j0w1: "?j0 + ?w = ?j1" using j0lt by simp
  have jge: "?j0 \<le> j" using ge by simp
  have nge: "\<not> j < ?j0" using jge by simp
  have bjeq: "?bj = ?j0 + ?sj" using nge by simp
  \<comment> \<open>decode j: block \<open>q\<^sub>j\<close>, offset \<open>s\<^sub>j\<close>\<close>
  have lenNn: "Lng ?Nn = ?j0 + n * ?w"
    by (rule operB_gen_LngM[OF L notzero hp j0lt])
  from reach have jlt: "j < Lng ?Nn" and ylt: "y < Lng ?Nn" and jley: "j \<le> y"
    by (auto simp: le0_def nextrel0_rtrancl_mono)
  have sjw: "?sj < ?w" using w0 by simp
  have jmj: "j - ?j0 < n * ?w" using jlt lenNn jge by linarith
  have qjn: "?qj < n" using less_mult_imp_div_less[OF jmj] .
  have jsplit: "j = ?j0 + ?qj * ?w + ?sj"
  proof -
    have "?qj * ?w + ?sj = j - ?j0"
      using div_mult_mod_eq[of "j - ?j0" ?w] by (simp add: mult.commute)
    thus ?thesis using jge by linarith
  qed
  \<comment> \<open>\<open>y'\<close> bounds\<close>
  have syw: "?sy < ?w" using w0 by simp
  have ypj1: "?yp \<le> ?j1" using syw j0w1 by linarith
  show ?thesis
  proof (cases "?bj = ?yp")
    case True
    thus ?thesis by simp
  next
    case False
    have bjlt: "?bj < ?yp" using antimono False nge by simp
    \<comment> \<open>\<open>le0 N (base j) y'\<close> via the period backward reflection\<close>
    have jy: "j < y"
    proof -
      have "j \<noteq> y"
      proof
        assume "j = y"
        hence "?sj = ?sy" by simp
        hence "?bj = ?yp" using bjeq by simp
        thus False using False by simp
      qed
      thus ?thesis using jley by simp
    qed
    have j0reds: "?j0 + ?sj = parent N 1 (Lng N - 1) + ?sj" using i1z by simp
    have j0'eq: "j = parent N 1 (Lng N - 1)
                  + ?qj * (Lng N - 1 - parent N 1 (Lng N - 1)) + ?sj"
      using jsplit i1z by simp
    have shamteq: "?qj * (entry N 0 (Lng N - 1) - entry N 0 (?j0 + 0))
                    = ?qj * (entry N 0 (Lng N - 1) - entry N 0 (parent N 1 (Lng N - 1)))"
      using i1z by simp
    have s0lt: "?sj < Lng N - 1 - parent N 1 (Lng N - 1)" using sjw i1z by simp
    have j1redle: "?yp \<le> Lng N - 1" using ypj1 by simp
    have j0j1red: "?j0 + ?sj < ?yp" using bjlt bjeq by simp
    \<comment> \<open>key span ingredient: \<open>q\<^sub>j*w + s\<^sub>y \<le> y - j\<^sub>0\<close> (since \<open>q\<^sub>j \<le> q\<^sub>y\<close>)\<close>
    obtain w where wdef: "?w = w" by blast
    have w0w: "0 < w" using w0 wdef by simp
    define qy where "qy = (y - ?j0) div w"
    define sy' where "sy' = (y - ?j0) mod w"
    have syeq: "?sy = sy'" using wdef sy'_def by simp
    have qjeq: "?qj = (j - ?j0) div w" using wdef by simp
    have qjw: "j = ?j0 + ?qj * w + ?sj" using jsplit wdef by simp
    have ysplit2: "y = ?j0 + qy * w + sy'"
    proof -
      have "qy * w + sy' = y - ?j0"
        using div_mult_mod_eq[of "y - ?j0" w] qy_def sy'_def by (simp add: mult.commute)
      thus ?thesis using jge jley by linarith
    qed
    have jmy: "j - ?j0 \<le> y - ?j0" using jley jge by linarith
    have qjqy: "?qj \<le> qy" using div_le_mono[OF jmy] qjeq qy_def by simp
    have yge2: "?qj * w + sy' \<le> y - ?j0"
    proof -
      have "?qj * w \<le> qy * w" using qjqy mult_le_mono1 by simp
      thus ?thesis using ysplit2 jge by linarith
    qed
    have j1redspan: "?yp \<le> (?j0 + ?sj) + (y - j)"
    proof -
      have j0y: "?j0 \<le> y" using jge jley by linarith
      have ywge: "?j0 + ?qj * w + sy' \<le> y" using yge2 j0y by linarith
      have "?yp = ?j0 + sy'" using syeq by simp
      also have "?j0 + sy' \<le> (?j0 + ?sj) + (y - j)"
        using ywge qjw bjlt bjeq syeq by linarith
      finally show ?thesis .
    qed
    have j0lt1: "parent N 1 (Lng N - 1) < Lng N - 1" using j0lt i1z by simp
    have le0bj: "le0 N (?j0 + ?sj) ?yp"
      by (rule oper_d1pos_ctx_period_le0Np[OF L notzero hp i1z j0lt1 refl reach jy ylt
            qjn s0lt j0reds j0'eq shamteq j1redle j0j1red j1redspan])
    have le0bj': "le0 N ?bj ?yp" using le0bj bjeq by simp
    show ?thesis using pNbj le0bj' by blast
  qed
qed



text \<open>§6.7 hpN \<open>le0baseN\<close> PREFIX discharge (Front B, \<open>i\<^sub>1=1\<close>): when the
  \<open>N[n]\<close>-parent \<open>p = parent (N[n]) 1 y\<close> sits in the verbatim PREFIX \<open>[0, j\<^sub>0)\<close>
  (\<open>p < j\<^sub>0\<close>, so \<open>base p = p\<close>), the row-0 reachability \<open>le0 (N[n]) p y\<close> projects to
  \<open>le0 N p (base y)\<close>, where \<open>base y = j\<^sub>0 + (y-j\<^sub>0) mod w\<close>.  Route (mirror of
  @{thm [source] oper_d1pos_le0_prefix_lift_fwd} backward):
  (a) restrict the \<open>N[n]\<close> path \<open>p \<rightsquigarrow> y\<close> down to \<open>j\<^sub>0\<close> by
      @{thm [source] m_5_1_ancestor_tree_1} (\<open>p \<le> j\<^sub>0 \<le> y\<close>), giving \<open>le0 (N[n]) p j\<^sub>0\<close>;
  (b) row-0 prefix transfer \<open>N[n] \<rightarrow> N\<close> on \<open>[0, j\<^sub>0]\<close> via
      @{thm [source] le0_prefix_row0} (the prefix is verbatim, the block-0 start
      \<open>j\<^sub>0\<close> reads \<open>entry N 0 j\<^sub>0\<close>), giving \<open>le0 N p j\<^sub>0\<close>;
  (c) within \<open>N\<close> itself, \<open>le0 N j\<^sub>0 (j\<^sub>0 + s\<^sub>y)\<close> for \<open>s\<^sub>y = (y-j\<^sub>0) mod w < w\<close> by
      @{thm [source] le0_build} on the row-0 ancestry chain \<open>j\<^sub>0 \<rightsquigarrow> j\<^sub>1\<close>
      (@{thm [source] le0_ances_aux});
  compose (a)+(b)+(c) by @{thm [source] le0_trans}.  Empirically 1596/1596.\<close>

lemma operCA_tiling_hpN_le0baseN_prefix:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y"
    and hpny: "hasParent ((N::pairseq)[n]) 1 y"
    and plt: "parent ((N::pairseq)[n]) 1 y < parent N (idx1 N (Lng N - 1)) (Lng N - 1)"
  shows "le0 N (if parent ((N::pairseq)[n]) 1 y < parent N (idx1 N (Lng N - 1)) (Lng N - 1)
               then parent ((N::pairseq)[n]) 1 y
               else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                 + (parent ((N::pairseq)[n]) 1 y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                    mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
              (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                 + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                    mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?Nn = "(N::pairseq)[n]"
  let ?p = "parent ?Nn 1 y"
  let ?sy = "(y - ?j0) mod ?w"
  let ?yp = "?j0 + ?sy"
  have NT: "N \<in> T_PS" using L by (cases N) (auto simp: T_PS_def)
  have i1z': "idx1 N ?j1 = 1" using i1z .
  have j0lt1: "parent N 1 ?j1 < ?j1" using j0lt i1z by simp
  have j0eq1: "?j0 = parent N 1 ?j1" using i1z by simp
  have w0: "0 < ?w" using j0lt by linarith
  have j0w1: "?j0 + ?w = ?j1" using j0lt by simp
  have lenNn: "Lng ?Nn = ?j0 + n * ?w"
    by (rule operB_gen_LngM[OF L notzero hp j0lt])
  \<comment> \<open>parent edge of \<open>y\<close> in \<open>N[n]\<close>\<close>
  have nrely: "nextrel1 ?Nn ?p y"
  proof -
    have "\<exists>!a. nextR ?Nn 1 a y" using hpny unfolding hasParent_def by simp
    hence "nextR ?Nn 1 ?p y" unfolding parent_def by (rule theI')
    thus ?thesis by (simp add: nextR_def)
  qed
  from nrely have py: "?p < y" and yNn: "y < Lng ?Nn"
    and le0py: "le0 ?Nn ?p y"
    by (auto simp: nextrel1_def)
  \<comment> \<open>\<open>n \<ge> 1\<close> is forced: otherwise \<open>Lng (N[n]) = j\<^sub>0 \<le> y\<close> contradicts \<open>y < Lng (N[n])\<close>\<close>
  have nw0: "0 < n * ?w" using ge yNn lenNn by linarith
  have n1: "1 \<le> n" using nw0 by (cases n) auto
  \<comment> \<open>various bounds\<close>
  have syw: "?sy < ?w" using w0 by simp
  have ypj1: "?yp < ?j1" using syw j0w1 by linarith
  have ypN: "?yp < Lng N" using ypj1 L by linarith
  have pj0: "?p < ?j0" using plt by simp
  have j0N: "?j0 < Lng N" using j0lt L by linarith
  have j0Nn: "?j0 < Lng ?Nn"
  proof -
    have "?j0 \<le> y" using ge by simp
    thus ?thesis using yNn by linarith
  qed
  \<comment> \<open>(a) restrict the \<open>N[n]\<close> path \<open>p \<rightsquigarrow> y\<close> down to \<open>j\<^sub>0\<close>\<close>
  have NnT: "?Nn \<in> T_PS" using yNn unfolding T_PS_def by (cases ?Nn) auto
  have leRpy: "leR ?Nn 0 ?p y" using le0py by (simp add: leR_def)
  have pj0le: "?p \<le> ?j0" using pj0 by simp
  have j0yle: "?j0 \<le> y" using ge by simp
  have leRpj0: "leR ?Nn 0 ?p ?j0"
    by (rule m_5_1_ancestor_tree_1[OF NnT leRpy pj0le j0yle])
  have le0Nnpj0: "le0 ?Nn ?p ?j0" using leRpj0 by (simp add: leR_def)
  \<comment> \<open>(b) row-0 prefix agreement on \<open>[0, j\<^sub>0]\<close>: verbatim below \<open>j\<^sub>0\<close>, block-0 start at \<open>j\<^sub>0\<close>\<close>
  have agree: "\<And>z. z \<le> ?j0 \<Longrightarrow> entry N 0 z = entry ((N::pairseq)[n]) 0 z"
  proof -
    fix z assume zj0: "z \<le> ?j0"
    show "entry N 0 z = entry ((N::pairseq)[n]) 0 z"
    proof (cases "z < ?j0")
      case True
      have zlt1: "z < parent N 1 ?j1" using True j0eq1 by simp
      have "((N::pairseq)[n]) ! z = N ! z"
        by (rule oper_d1pos_nth_prefix[OF L notzero hp i1z' zlt1])
      thus ?thesis by (simp add: entry_def)
    next
      case False
      hence zeq: "z = ?j0" using zj0 by simp
      have k0n0: "(0::nat) < n" using n1 by simp
      have w0': "(0::nat) < Lng N - 1 - parent N 1 ?j1" using j0lt1 by linarith
      have "((N::pairseq)[n]) ! (parent N 1 ?j1 + 0 * (Lng N - 1 - parent N 1 ?j1) + 0)
              = (entry N 0 (parent N 1 ?j1 + 0)
                   + 0 * (entry N 0 (Lng N - 1) - entry N 0 (parent N 1 ?j1)),
                 entry N 1 (parent N 1 ?j1 + 0))"
        by (rule oper_d1pos_nth[OF L notzero hp i1z' j0lt1 k0n0 w0'])
      hence "((N::pairseq)[n]) ! (parent N 1 ?j1)
               = (entry N 0 (parent N 1 ?j1), entry N 1 (parent N 1 ?j1))" by simp
      hence "((N::pairseq)[n]) ! ?j0 = (entry N 0 ?j0, entry N 1 ?j0)"
        using j0eq1 by simp
      thus ?thesis using zeq by (simp add: entry_def)
    qed
  qed
  have agree': "\<And>z. z \<le> ?j0 \<Longrightarrow> entry ?Nn 0 z = entry N 0 z"
    using agree by simp
  have le0Npj0: "le0 N ?p ?j0"
    by (rule le0_prefix_row0[OF agree' j0Nn j0N pj0le order.refl le0Nnpj0])
  \<comment> \<open>(c) within \<open>N\<close>: \<open>le0 N j\<^sub>0 (j\<^sub>0 + s\<^sub>y)\<close> from the row-0 ancestry chain \<open>j\<^sub>0 \<rightsquigarrow> j\<^sub>1\<close>\<close>
  have hp1: "hasParent N 1 ?j1" using hp i1z by simp
  have parR0: "nextR N 1 (parent N 1 ?j1) ?j1"
    using hp1 unfolding hasParent_def parent_def by (rule theI')
  have parR: "nextR N 1 ?j0 ?j1" using parR0 j0eq1 by simp
  have "leR N 0 ?j0 ?j1" using poper_nextR_imp_le0[OF parR] by simp
  hence baseR: "(nextrel0 N)\<^sup>*\<^sup>* ?j0 ?j1" by (simp add: leR_def le0_def)
  have ances: "\<forall>j. ?j0 < j \<and> j \<le> ?j1 \<longrightarrow> entry N 0 ?j0 < entry N 0 j"
    by (rule le0_ances_aux[OF baseR])
  have le0Nj0yp: "le0 N ?j0 ?yp"
  proof (cases "?sy = 0")
    case True
    have "?j0 < Lng N" using j0N .
    thus ?thesis using True by (simp add: le0_refl)
  next
    case False
    hence j0lt': "?j0 < ?yp" by simp
    have "(nextrel0 N)\<^sup>*\<^sup>* ?j0 ?yp"
    proof (rule le0_build[OF NT ypN j0lt'])
      show "\<forall>j. ?j0 < j \<and> j \<le> ?yp \<longrightarrow> entry N 0 ?j0 < entry N 0 j"
        using ances ypj1 by auto
    qed
    thus ?thesis using j0lt' ypN by (simp add: le0_def)
  qed
  \<comment> \<open>compose (a)+(b)+(c)\<close>
  have le0Npyp: "le0 N ?p ?yp" by (rule le0_trans[OF le0Npj0 le0Nj0yp])
  have lhs: "(if ?p < ?j0 then ?p else ?j0 + (?p - ?j0) mod ?w) = ?p"
    using pj0 by simp
  show ?thesis using le0Npyp lhs by simp
qed


text \<open>§6.7 hpN \<open>le0baseN\<close> FULL (Front B, \<open>i\<^sub>1=1\<close>): the row-0 base-back
  \<open>le0 N (base p) (base y)\<close> for BOTH branches, assembled by case split on the
  \<open>N[n]\<close>-parent location \<open>p = parent (N[n]) 1 y\<close>:
  \<^item> PREFIX \<open>p < j\<^sub>0\<close> : the UNCONDITIONAL @{thm [source] operCA_tiling_hpN_le0baseN_prefix};
  \<^item> NON-PREFIX \<open>p \<ge> j\<^sub>0\<close> : the @{thm [source] operCA_tiling_hpN_le0baseN_sameblock},
    which needs the same-block residual \<open>sblk\<close> (the \<open>N[n]\<close>-parent of \<open>y\<close> lies in
    \<open>y\<close>'s period block, \<open>(p-j\<^sub>0) div w = (y-j\<^sub>0) div w\<close>).  Empirically the non-prefix
    case is ALWAYS same-block (38856/38856), so \<open>sblk\<close> is the sole remaining
    obligation of the full base-back; it is the d1pos argmin-coincidence brick.\<close>

lemma operCA_tiling_hpN_le0baseN_full:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y"
    and hpny: "hasParent ((N::pairseq)[n]) 1 y"
    and sblk: "\<not> parent ((N::pairseq)[n]) 1 y < parent N (idx1 N (Lng N - 1)) (Lng N - 1)
               \<Longrightarrow> (parent ((N::pairseq)[n]) 1 y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                     div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                   = (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                     div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
  shows "le0 N (if parent ((N::pairseq)[n]) 1 y < parent N (idx1 N (Lng N - 1)) (Lng N - 1)
               then parent ((N::pairseq)[n]) 1 y
               else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                 + (parent ((N::pairseq)[n]) 1 y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                    mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
              (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                 + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                    mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
proof (cases "parent ((N::pairseq)[n]) 1 y < parent N (idx1 N (Lng N - 1)) (Lng N - 1)")
  case True
  show ?thesis
    by (rule operCA_tiling_hpN_le0baseN_prefix[OF L notzero hp i1z j0lt ge hpny True])
next
  case False
  hence pge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> parent ((N::pairseq)[n]) 1 y"
    by simp
  have sblk': "(parent ((N::pairseq)[n]) 1 y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                 div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
               = (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                 div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
    using sblk False by simp
  show ?thesis
    by (rule operCA_tiling_hpN_le0baseN_sameblock[OF L notzero hp i1z j0lt ge hpny pge sblk'])
qed


text \<open>§6.7 hpN reduced to the same-block residual \<open>sblk\<close> only (Front B, \<open>i\<^sub>1=1\<close>):
  feeding the assembled base-back @{thm [source] operCA_tiling_hpN_le0baseN_full}
  into @{thm [source] operCA_tiling_hpN_via_le0baseN} yields the hpN conclusion
  \<open>hasParent N 1 (base y)\<close>, with the PREFIX branch fully discharged and the only
  remaining hypothesis the non-prefix same-block fact \<open>sblk\<close>.\<close>

lemma operCA_tiling_hpN_reduced_sblk:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y"
    and hpny: "hasParent ((N::pairseq)[n]) 1 y"
    and sblk: "\<not> parent ((N::pairseq)[n]) 1 y < parent N (idx1 N (Lng N - 1)) (Lng N - 1)
               \<Longrightarrow> (parent ((N::pairseq)[n]) 1 y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                     div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                   = (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                     div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
  shows "hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                   mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
proof -
  have le0baseN: "le0 N (if parent ((N::pairseq)[n]) 1 y < parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                         then parent ((N::pairseq)[n]) 1 y
                         else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                           + (parent ((N::pairseq)[n]) 1 y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                              mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                        (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                           + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                              mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
    by (rule operCA_tiling_hpN_le0baseN_full[OF L notzero hp i1z j0lt ge hpny sblk])
  show ?thesis
    by (rule operCA_tiling_hpN_via_le0baseN[OF L notzero hp i1z j0lt ge hpny le0baseN])
qed


text \<open>6.7 Qprime -- the pure-N crux of the whole 6.5/6.7 cascade, attempt R.

  The keystone @{thm [source] spsy_keystone_via_Q} reduces the entire spsy
  obligation to the base-sequence fact @{text Q}:
  \<open>w = 1 \<or> entry N 1 j\<^sub>0 < entry N 1 (j\<^sub>0 + (y-j\<^sub>0) mod w)\<close>.  For the arising
  @{text y} this in turn (via the bridge: @{text "hasParent N 1 (j\<^sub>0+s\<^sub>y)"},
  \<open>parent N 1 (j\<^sub>0+s\<^sub>y) \<ge> j\<^sub>0\<close>) is exactly @{text Qprime} below, instantiated at
  @{text "z = j\<^sub>0+s\<^sub>y"}.

  @{text Qprime} is proved by @{text ST_PS.induct}.  Its @{text diag} base
  (this lemma, @{text Qprime_diag}) is VACUOUS: for \<open>N = diagSeq u v\<close> the row-1
  parent of the last index \<open>j\<^sub>1 = Lng N - 1\<close> is the IMMEDIATELY preceding index
  \<open>j\<^sub>1 - 1\<close> (the diagonal is row-1 strictly increasing by 1, so the unique row-1
  predecessor of \<open>j\<^sub>1\<close> is \<open>j\<^sub>1 - 1\<close>).  Hence the period \<open>w = j\<^sub>1 - (j\<^sub>1-1) = 1\<close>,
  the strict @{text "j\<^sub>0 < z < j\<^sub>1"} window is empty, and the Qprime premise
  \<open>j\<^sub>0 < z < Lng N - 1\<close> is contradictory.  Non-circular: uses only
  @{thm [source] nextR1_diagSeq} / @{thm [source] nextR1_unique}, no spsy / sblk /
  via_spsy / RedCond.\<close>

lemma Qprime_diag:
  fixes u v :: nat
  assumes uv: "u \<le> v"
    and L: "1 < Lng (diagSeq u v)"
    and i1z: "idx1 (diagSeq u v) (Lng (diagSeq u v) - 1) = 1"
    and hp: "hasParent (diagSeq u v) 1 (Lng (diagSeq u v) - 1)"
    and zlo: "parent (diagSeq u v) 1 (Lng (diagSeq u v) - 1) < z"
    and zhi: "z < Lng (diagSeq u v) - 1"
    and w1: "1 < Lng (diagSeq u v) - 1
                 - parent (diagSeq u v) 1 (Lng (diagSeq u v) - 1)"
  shows "entry (diagSeq u v) 1
              (parent (diagSeq u v) 1 (Lng (diagSeq u v) - 1)) < entry (diagSeq u v) 1 z"
proof -
  let ?N = "diagSeq u v"
  let ?j1 = "Lng ?N - 1"
  \<comment> \<open>\<open>Lng (diagSeq u v) = Suc v - u\<close>, and \<open>j\<^sub>1 = v - u\<close>\<close>
  have lenN: "Lng ?N = Suc v - u" by simp
  have j1eq: "?j1 = v - u" using lenN uv by simp
  \<comment> \<open>\<open>j\<^sub>1 \<ge> 1\<close> from \<open>1 < Lng N\<close>\<close>
  have j1pos: "0 < ?j1" using L by linarith
  \<comment> \<open>the row-1 predecessor of \<open>j\<^sub>1\<close> is \<open>j\<^sub>1 - 1\<close> (diagonal increases by 1)\<close>
  have suc: "Suc (?j1 - 1) = ?j1" using j1pos by simp
  have rng: "Suc (?j1 - 1) < Suc v - u" using suc j1eq j1pos by linarith
  have nR: "nextR ?N 1 (?j1 - 1) (Suc (?j1 - 1))"
    by (rule nextR1_diagSeq[OF rng])
  have nRj1: "nextR ?N 1 (?j1 - 1) ?j1" using nR suc by simp
  \<comment> \<open>so the parent is exactly \<open>j\<^sub>1 - 1\<close> by uniqueness\<close>
  have parR: "nextR ?N 1 (parent ?N 1 ?j1) ?j1"
    using hp unfolding hasParent_def parent_def by (rule theI')
  have peq: "parent ?N 1 ?j1 = ?j1 - 1" by (rule nextR1_unique[OF parR nRj1])
  \<comment> \<open>hence the period \<open>w = j\<^sub>1 - (j\<^sub>1-1) = 1\<close>, contradicting \<open>w > 1\<close>\<close>
  have weq: "?j1 - parent ?N 1 ?j1 = 1" using peq j1pos by linarith
  show ?thesis using w1 weq by simp
qed


text \<open>6.7 RESIDUAL 1 (tree) -- DIAG base case (attempt T), GREEN and VACUOUS.

  For \<open>N = diagSeq u v\<close> the row-1 ancestor tree of the tail is trivial: the row-1
  predecessor of the last index \<open>j\<^sub>1 = Lng N - 1\<close> is the IMMEDIATELY preceding
  index \<open>j\<^sub>1 - 1\<close> (the diagonal increases row-1 by exactly \<open>1\<close> each step), so
  \<open>j\<^sub>0 = parent N 1 j\<^sub>1 = j\<^sub>1 - 1\<close> and the period \<open>w = j\<^sub>1 - j\<^sub>0 = 1\<close>.  Hence the
  strict window \<open>j\<^sub>0 < z < j\<^sub>1\<close> is EMPTY and the tree premises \<open>j\<^sub>0 < z\<close>, \<open>z < j\<^sub>1\<close>
  are contradictory; the conclusion holds vacuously.  This is the exact \<open>ST_PS.induct\<close>
  base of @{text tree_wellformed} (RESIDUAL 1); the \<open>oper\<close> step (\<open>N = M[n]\<close>) is the
  remaining open part.

  Non-circular: uses only @{thm [source] nextR1_diagSeq} / @{thm [source] nextR1_unique}
  (the same diagonal facts as @{thm [source] Qprime_diag}); no spsy, sblk, via_spsy,
  RedCondA/RedCondB, oper.\<close>

lemma tree_wellformed_diag:
  fixes u v :: nat
  assumes uv: "u \<le> v"
    and L: "1 < Lng (diagSeq u v)"
    and i1z: "idx1 (diagSeq u v) (Lng (diagSeq u v) - 1) = 1"
    and hp: "hasParent (diagSeq u v) 1 (Lng (diagSeq u v) - 1)"
    and zlo: "parent (diagSeq u v) 1 (Lng (diagSeq u v) - 1) < z"
    and zhi: "z < Lng (diagSeq u v) - 1"
    and hpz: "hasParent (diagSeq u v) 1 z"
    and pge: "parent (diagSeq u v) 1 z \<ge> parent (diagSeq u v) 1 (Lng (diagSeq u v) - 1)"
    and pgt: "parent (diagSeq u v) 1 z > parent (diagSeq u v) 1 (Lng (diagSeq u v) - 1)"
  shows "hasParent (diagSeq u v) 1 (parent (diagSeq u v) 1 z)
         \<and> parent (diagSeq u v) 1 (parent (diagSeq u v) 1 z)
             \<ge> parent (diagSeq u v) 1 (Lng (diagSeq u v) - 1)"
proof -
  let ?N = "diagSeq u v"  let ?j1 = "Lng ?N - 1"
  have lenN: "Lng ?N = Suc v - u" by simp
  have j1eq: "?j1 = v - u" using lenN uv by simp
  have j1pos: "0 < ?j1" using L by linarith
  \<comment> \<open>the row-1 predecessor of \<open>j\<^sub>1\<close> is \<open>j\<^sub>1 - 1\<close> (diagonal increases by 1)\<close>
  have suc: "Suc (?j1 - 1) = ?j1" using j1pos by simp
  have rng: "Suc (?j1 - 1) < Suc v - u" using suc j1eq j1pos by linarith
  have nR: "nextR ?N 1 (?j1 - 1) (Suc (?j1 - 1))" by (rule nextR1_diagSeq[OF rng])
  have nRj1: "nextR ?N 1 (?j1 - 1) ?j1" using nR suc by simp
  have parR: "nextR ?N 1 (parent ?N 1 ?j1) ?j1"
    using hp unfolding hasParent_def parent_def by (rule theI')
  have peq: "parent ?N 1 ?j1 = ?j1 - 1" by (rule nextR1_unique[OF parR nRj1])
  \<comment> \<open>so the tail period \<open>w = j\<^sub>1 - (j\<^sub>1-1) = 1\<close>, and the window \<open>j\<^sub>0 < z < j\<^sub>1\<close> is empty\<close>
  have "parent ?N 1 ?j1 < z" using zlo .
  hence "?j1 - 1 < z" using peq by simp
  hence "?j1 \<le> z" using j1pos by linarith
  hence False using zhi by linarith
  thus ?thesis by blast
qed


text \<open>§6.7 BRICK, tail-affine invariant -- DIAG base of the ST_PS induction
  (attempt C), GREEN and trivial.  For \<open>N = diagSeq u v\<close> the row-0 reading is the
  GLOBAL affine ramp \<open>entry N 0 x = u + x\<close> (@{thm [source] entry_diagSeq}); in
  particular on the tail \<open>[j\<^sub>0, j\<^sub>1]\<close> it equals \<open>entry N 0 j\<^sub>0 + (x - j\<^sub>0)\<close>.
  Non-circular: uses only @{thm [source] entry_diagSeq}; no spsy / sblk / oper.\<close>

lemma tail_affine_diag:
  fixes u v x :: nat
  assumes uv: "u \<le> v"
    and xge: "parent (diagSeq u v) 1 (Lng (diagSeq u v) - 1) \<le> x"
    and xle: "x \<le> Lng (diagSeq u v) - 1"
  shows "entry (diagSeq u v) 0 x
           = entry (diagSeq u v) 0 (parent (diagSeq u v) 1 (Lng (diagSeq u v) - 1))
             + (x - parent (diagSeq u v) 1 (Lng (diagSeq u v) - 1))"
proof -
  let ?N = "diagSeq u v"  let ?j1 = "Lng ?N - 1"  let ?j0 = "parent ?N 1 ?j1"
  have lenN: "Lng ?N = Suc v - u" by simp
  have j1eq: "?j1 = v - u" using lenN uv by simp
  have xlt: "x < Suc v - u" using xle j1eq uv by linarith
  have j0le: "?j0 \<le> x" using xge .
  have j0lt: "?j0 < Suc v - u" using j0le xlt by linarith
  have ex: "entry ?N 0 x = u + x" by (rule entry_diagSeq[OF xlt])
  have ej0: "entry ?N 0 ?j0 = u + ?j0" by (rule entry_diagSeq[OF j0lt])
  show ?thesis using ex ej0 j0le by linarith
qed


lemma subramp_diag_base:
  fixes u v :: nat
  assumes x: "Suc x < Lng (diagSeq u v)"
  shows "entry (diagSeq u v) 0 (Suc x) = Suc (entry (diagSeq u v) 0 x)"
proof -
  let ?N = "diagSeq u v"
  have sx: "Suc x < Suc v - u" using x by simp
  have lx: "x < Suc v - u" using sx by simp
  have e1: "entry ?N 0 (Suc x) = u + Suc x" by (rule entry_diagSeq[OF sx])
  have e0: "entry ?N 0 x = u + x" by (rule entry_diagSeq[OF lx])
  show ?thesis using e1 e0 by simp
qed


text \<open>§6.7 SUBRAMP oper-step CORE (d0pos tiling readback, GREEN).  In the
  \<open>i\<^sub>1=1\<close> tiling regime the operand \<open>M\<close> tiles \<open>[j\<^sub>0\<^sup>M, j\<^sub>1\<^sup>M)\<close> \<open>n\<close> times into
  \<open>M[n]\<close> with the per-block row-0 shift \<open>d\<^sub>0 = entry M 0 j\<^sub>1\<^sup>M - entry M 0 j\<^sub>0\<^sup>M\<close>.
  If \<open>M\<close>'s row-0 is a consecutive \<open>+1\<close> ramp on the WHOLE tail \<open>[j\<^sub>0\<^sup>M, j\<^sub>1\<^sup>M]\<close>
  (every step from \<open>j\<^sub>0\<^sup>M\<close> up to and including the last step \<open>j\<^sub>1\<^sup>M-1 \<rightarrow> j\<^sub>1\<^sup>M\<close>),
  then \<open>M[n]\<close>'s row-0 is a \<open>+1\<close> ramp on its OWN tail \<open>[j\<^sub>0\<^sup>M, Lng (M[n]) - 1)\<close>.
  EMPIRICALLY 2047/0 on the broad ST_PS closure (the operand of every
  strict-ancestor \<open>M[n]\<close> satisfies this whole-tail \<open>+1\<close> hypothesis).

  Readback: with \<open>x = j\<^sub>0\<^sup>M + q\<cdot>w + s\<close> (\<open>q<n\<close>, \<open>0\<le>s<w\<close>), within a block
  (\<open>s+1<w\<close>) the increment equals \<open>M\<close>'s in-tail step (\<open>+1\<close>); at a block boundary
  (\<open>s=w-1\<close>, \<open>x+1 = j\<^sub>0\<^sup>M+(q+1)\<cdot>w\<close>, with \<open>q+1<n\<close>) the boundary reading
  (@{thm [source] oper_d1pos_entry0_boundary}) gives the increment
  \<open>entry M 0 j\<^sub>1\<^sup>M - entry M 0 (j\<^sub>1\<^sup>M-1) = +1\<close>, \<open>M\<close>'s last step.  Cites only the
  GREEN \<open>oper_d1pos_entry0\<close> / \<open>_boundary\<close> readback bricks and
  @{thm [source] oper_d1pos_LngM}; no spsy / sblk / RedCond.\<close>

lemma subramp_oper_core:
  fixes M :: pairseq and n :: nat
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and Mramp: "\<And>y. parent M 1 (Lng M - 1) \<le> y \<Longrightarrow> y < Lng M - 1
                  \<Longrightarrow> entry M 0 (Suc y) = Suc (entry M 0 y)"
    and xlo: "parent M 1 (Lng M - 1) \<le> x"
    and xhi: "x < Lng (M[n]) - 1"
  shows "entry ((M::pairseq)[n]) 0 (Suc x) = Suc (entry (M[n]) 0 x)"
proof -
  let ?j1 = "Lng M - 1"  let ?j0 = "parent M 1 ?j1"  let ?w = "?j1 - ?j0"
  let ?d0 = "entry M 0 ?j1 - entry M 0 ?j0"
  have w0: "0 < ?w" using j0lt by linarith
  have lenMn: "Lng (M[n]) = ?j0 + n * ?w"
    using oper_d1pos_LngM[OF L notzero hp i1z j0lt] by simp
  \<comment> \<open>\<open>d\<^sub>0 = w\<close>: \<open>M\<close>'s ramp on \<open>[j\<^sub>0, j\<^sub>1]\<close> gives slope 1, so \<open>entry M 0 j\<^sub>1 = entry M 0 j\<^sub>0 + w\<close>\<close>
  have Mabs: "\<And>t. ?j0 + t \<le> ?j1 \<Longrightarrow> entry M 0 (?j0 + t) = entry M 0 ?j0 + t"
  proof -
    fix t assume "?j0 + t \<le> ?j1"
    thus "entry M 0 (?j0 + t) = entry M 0 ?j0 + t"
    proof (induction t)
      case 0 show ?case by simp
    next
      case (Suc t)
      have le1: "?j0 + t \<le> ?j1" using Suc.prems by simp
      have lt: "?j0 + t < ?j1" using Suc.prems by simp
      have ge: "?j0 \<le> ?j0 + t" by simp
      have step: "entry M 0 (Suc (?j0 + t)) = Suc (entry M 0 (?j0 + t))"
        by (rule Mramp[OF ge lt])
      have ih: "entry M 0 (?j0 + t) = entry M 0 ?j0 + t" using Suc.IH[OF le1] .
      show ?case using step ih by simp
    qed
  qed
  have wle: "?j0 + ?w \<le> ?j1" using w0 by simp
  have d0w: "?d0 = ?w"
  proof -
    have "entry M 0 (?j0 + ?w) = entry M 0 ?j0 + ?w" by (rule Mabs[OF wle])
    moreover have "?j0 + ?w = ?j1" using j0lt by simp
    ultimately have "entry M 0 ?j1 = entry M 0 ?j0 + ?w" by simp
    thus ?thesis by simp
  qed
  \<comment> \<open>block decomposition of \<open>x\<close>: \<open>x = j\<^sub>0 + q\<cdot>w + s\<close>, \<open>q<n\<close>, \<open>s<w\<close>\<close>
  have xge: "?j0 \<le> x" using xlo .
  obtain r where xr: "x = ?j0 + r" using xge le_Suc_ex by blast
  have rlt: "r < n * ?w"
  proof -
    have "?j0 + r < ?j0 + n * ?w - 1" using xhi xr lenMn by simp
    thus ?thesis by linarith
  qed
  define q where "q = r div ?w"
  define s where "s = r mod ?w"
  have rqs: "r = q * ?w + s" using q_def s_def by (simp add: mult_div_mod_eq mult.commute)
  have slt: "s < ?w" using w0 s_def by simp
  have qn: "q < n" using rlt rqs slt w0
    by (metis add.commute add_lessD1 div_eq_0_iff less_mult_imp_div_less mult.commute nat_neq_iff not_less0 q_def)
  have xqs: "x = ?j0 + q * ?w + s" using xr rqs by (simp add: add.assoc)
  \<comment> \<open>row-0 value at \<open>x\<close> (block \<open>q\<close>, offset \<open>s\<close>)\<close>
  have ex: "entry (M[n]) 0 x = entry M 0 (?j0 + s) + q * ?d0"
    using oper_d1pos_entry0[OF L notzero hp i1z j0lt qn slt] xqs by simp
  show ?thesis
  proof (cases "Suc s < ?w")
    case True
    \<comment> \<open>within block \<open>q\<close>: \<open>x+1 = j\<^sub>0 + q\<cdot>w + (s+1)\<close>\<close>
    have xsuc: "Suc x = ?j0 + q * ?w + Suc s" using xqs by simp
    have esx: "entry (M[n]) 0 (Suc x) = entry M 0 (?j0 + Suc s) + q * ?d0"
      using oper_d1pos_entry0[OF L notzero hp i1z j0lt qn True] xsuc by simp
    have sj0: "?j0 \<le> ?j0 + s" by simp
    have sj1: "?j0 + s < ?j1" using slt by simp
    have mstep: "entry M 0 (Suc (?j0 + s)) = Suc (entry M 0 (?j0 + s))"
      by (rule Mramp[OF sj0 sj1])
    have "entry (M[n]) 0 (Suc x) = entry M 0 (Suc (?j0 + s)) + q * ?d0"
      using esx by simp
    also have "\<dots> = Suc (entry M 0 (?j0 + s)) + q * ?d0" using mstep by simp
    also have "\<dots> = Suc (entry M 0 (?j0 + s) + q * ?d0)" by simp
    finally show ?thesis using ex by simp
  next
    case False
    \<comment> \<open>block boundary: \<open>s = w-1\<close>, \<open>x+1 = j\<^sub>0 + (q+1)\<cdot>w\<close>\<close>
    have sw1: "Suc s = ?w" using False slt by linarith
    have xsuc: "Suc x = ?j0 + (q + 1) * ?w"
    proof -
      have "Suc x = ?j0 + q * ?w + Suc s" using xqs by simp
      also have "\<dots> = ?j0 + q * ?w + ?w" using sw1 by simp
      also have "\<dots> = ?j0 + (q + 1) * ?w" by (simp add: add.assoc)
      finally show ?thesis .
    qed
    \<comment> \<open>\<open>q+1<n\<close> from \<open>x < Lng(M[n])-1\<close>\<close>
    have xup: "?j0 + q * ?w + s < ?j0 + n * ?w - 1" using xhi xqs lenMn by simp
    have q1n: "q + 1 < n"
    proof -
      have a: "q * ?w + s < n * ?w - 1" using xup by linarith
      have b: "q * ?w + Suc s \<le> n * ?w - 1" using a by linarith
      have c: "q * ?w + ?w \<le> n * ?w - 1" using b unfolding sw1[symmetric] .
      have d: "Suc q * ?w \<le> n * ?w - 1" using c by (simp add: mult.commute)
      have nwpos: "0 < n * ?w" using d w0 by (cases "n * ?w") auto
      have e: "Suc q * ?w < n * ?w" using d nwpos by linarith
      have "Suc q < n" using e w0 mult_less_cancel2[of "Suc q" ?w n] by blast
      thus ?thesis by simp
    qed
    have esx: "entry (M[n]) 0 (?j0 + (q + 1) * ?w)
             = entry M 0 ?j1 + q * ?d0"
      using oper_d1pos_entry0_boundary[OF L notzero hp i1z j0lt q1n] by simp
    \<comment> \<open>boundary increment \<open>= entry M 0 j\<^sub>1 - entry M 0 (j\<^sub>0+s) = +1\<close> (M's last step)\<close>
    have s_eq: "?j0 + s = ?j1 - 1" using sw1 j0lt by simp
    have j1pos: "0 < ?j1" using L by simp
    have lastlo: "?j0 \<le> ?j1 - 1" using j0lt by simp
    have lasthi: "?j1 - 1 < ?j1" using j1pos by simp
    have mlast: "entry M 0 (Suc (?j1 - 1)) = Suc (entry M 0 (?j1 - 1))"
      by (rule Mramp[OF lastlo lasthi])
    have suc_j1: "Suc (?j1 - 1) = ?j1" using j1pos by simp
    have ej1: "entry M 0 ?j1 = Suc (entry M 0 (?j0 + s))"
      using mlast suc_j1 s_eq by simp
    have "entry (M[n]) 0 (Suc x) = entry M 0 ?j1 + q * ?d0"
      using esx xsuc by simp
    also have "\<dots> = Suc (entry M 0 (?j0 + s)) + q * ?d0" using ej1 by simp
    also have "\<dots> = Suc (entry M 0 (?j0 + s) + q * ?d0)" by simp
    finally show ?thesis using ex by simp
  qed
qed


text \<open>§6.7 STRICT-INCREASE GROUNDWORK (attempt V).  The companion LOWER bound to
  the GREEN per-step UPPER bound @{thm [source] SkT_row0_step_le}.  The new
  ingredient (the only thing beyond the \<open>\<le>\<close> mirror) is \<open>d\<^sub>0 > 0\<close> at the
  block-junction: when the root parent is a row-1 edge, the row-0 increment
  across the parent slice is STRICTLY positive.  EMPIRICALLY 1575/0 on the broad
  ST_PS closure (/tmp/_d0fam.py).  Cites only @{thm [source] le0_def},
  @{thm [source] nextrel1_def}, @{thm [source] le0_ances_aux}: from
  \<open>nextrel1 M j\<^sub>0 j\<^sub>1\<close> the embedded \<open>le0 M j\<^sub>0 j\<^sub>1\<close> is a row-0 rtrancl chain, and with
  \<open>j\<^sub>0 < j\<^sub>1\<close> @{thm [source] le0_ances_aux} turns weak monotonicity into the STRICT
  increase.\<close>

lemma le0_strict_entry0:
  fixes M :: pairseq
  assumes le0: "le0 M a b"
    and ab: "a < b"
  shows "entry M 0 a < entry M 0 b"
proof -
  have chain: "(nextrel0 M)\<^sup>*\<^sup>* a b" using le0 by (simp add: le0_def)
  have "\<forall>j. a < j \<and> j \<le> b \<longrightarrow> entry M 0 a < entry M 0 j"
    by (rule le0_ances_aux[OF chain])
  thus ?thesis using ab by simp
qed

lemma d0_pos_row1_parent:
  fixes M :: pairseq
  assumes nr1: "nextrel1 M j0 j1"
    and ab: "j0 < j1"
  shows "entry M 0 j0 < entry M 0 j1"
proof -
  have le0j: "le0 M j0 j1" using nr1 by (simp add: nextrel1_def)
  show ?thesis by (rule le0_strict_entry0[OF le0j ab])
qed


text \<open>§6.7 WITHIN-BLOCK STRICT step (attempt V): the \<open>within\<close> case of the strict
  mirror, in isolation.  For \<open>N = M[n]\<close>, two consecutive interior offsets
  \<open>s, s+1\<close> of the SAME block \<open>q\<close> read off \<open>M\<close>'s row-0 entries shifted by the same
  \<open>q\<cdot>d\<^sub>0\<close> (@{thm [source] oper_gen_block_entry0}), so the N-step at that junction is
  EXACTLY the M-step \<open>(j\<^sub>0+s, j\<^sub>0+s+1)\<close>: it is strict iff M's is.  This is the
  unconditional block-internal reduction (no \<open>d\<^sub>0\<close> needed); the residual
  difficulty in the FULL strict-increase is confined to the inter-block junctions
  and the prefix, where the d0pos family invariant (NOT a clean local invariant;
  it is NOT closed under oper, /tmp/_inv.out 480 ctrex) must be threaded.\<close>

lemma oper_within_block_strict:
  fixes M :: pairseq
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and j0lt: "parent M (idx1 M (Lng M - 1)) (Lng M - 1) < Lng M - 1"
    and q: "q < n"
    and s1: "s + 1 < Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and Mstep: "entry M 0 (parent M (idx1 M (Lng M - 1)) (Lng M - 1) + s)
                  < entry M 0 (parent M (idx1 M (Lng M - 1)) (Lng M - 1) + (s + 1))"
  shows "entry ((M::pairseq)[n]) 0
              (parent M (idx1 M (Lng M - 1)) (Lng M - 1)
                 + q * (Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1)) + s)
       < entry ((M::pairseq)[n]) 0
              (parent M (idx1 M (Lng M - 1)) (Lng M - 1)
                 + q * (Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1)) + (s + 1))"
proof -
  let ?j0 = "parent M (idx1 M (Lng M - 1)) (Lng M - 1)"
  let ?w = "Lng M - 1 - ?j0"
  let ?d0 = "if 0 < idx1 M (Lng M - 1)
               then entry M 0 (Lng M - 1) - entry M 0 ?j0 else 0"
  have sw: "s < ?w" using s1 by simp
  have e0s: "entry ((M::pairseq)[n]) 0 (?j0 + q * ?w + s)
               = entry M 0 (?j0 + s) + q * ?d0"
    by (rule oper_gen_block_entry0[OF L notzero hp j0lt q sw])
  have e0s1: "entry ((M::pairseq)[n]) 0 (?j0 + q * ?w + (s + 1))
               = entry M 0 (?j0 + (s + 1)) + q * ?d0"
    by (rule oper_gen_block_entry0[OF L notzero hp j0lt q s1])
  show ?thesis using e0s e0s1 Mstep by simp
qed


lemma Ez_diag_base:
  fixes a b :: nat
  assumes ab: "a \<le> b"
    and zle: "z \<le> Lng (diagSeq a b) - 1"
  shows "entry (diagSeq a b) 0 (Lng (diagSeq a b) - 1)
       = entry (diagSeq a b) 0 z + ((Lng (diagSeq a b) - 1) - z)"
proof -
  let ?N = "diagSeq a b"
  let ?j1 = "Lng ?N - 1"
  \<comment> \<open>\<open>Lng N = Suc b - a > 0\<close> since \<open>a \<le> b\<close>, so both endpoints are in range\<close>
  have Lpos: "0 < Suc b - a" using ab by simp
  have j1lt: "?j1 < Suc b - a" using Lpos by simp
  have zlt: "z < Suc b - a" using zle Lpos by simp
  have eN_j1: "entry ?N 0 ?j1 = a + ?j1"
    by (rule entry_diagSeq[OF j1lt])
  have eN_z: "entry ?N 0 z = a + z"
    by (rule entry_diagSeq[OF zlt])
  \<comment> \<open>slope-1 line: \<open>(a + j\<^sub>1) = (a + z) + (j\<^sub>1 - z)\<close> since \<open>z \<le> j\<^sub>1\<close>\<close>
  show ?thesis using eN_j1 eN_z zle by simp
qed


lemma ez_inblock_lift:
  fixes M :: pairseq
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and qn: "q < n"
    and s0: "0 < s"
    and sw: "s < Lng M - 1 - parent M 1 (Lng M - 1)"
    \<comment> \<open>the IH content: the M-side block \<open>[j\<^sub>0, j\<^sub>1]\<close> is an exact \<open>+1\<close> row-0 ramp\<close>
    and ramp: "\<And>t. t \<le> Lng M - 1 - parent M 1 (Lng M - 1)
                 \<Longrightarrow> entry M 0 (parent M 1 (Lng M - 1) + t)
                       = entry M 0 (parent M 1 (Lng M - 1)) + t"
  shows "entry ((M::pairseq)[n]) 0 (Lng ((M::pairseq)[n]) - 1)
       = entry ((M::pairseq)[n]) 0
              (parent M 1 (Lng M - 1)
                 + q * (Lng M - 1 - parent M 1 (Lng M - 1)) + s)
         + ((Lng ((M::pairseq)[n]) - 1)
              - (parent M 1 (Lng M - 1)
                   + q * (Lng M - 1 - parent M 1 (Lng M - 1)) + s))"
proof -
  let ?j1 = "Lng M - 1"  let ?j0 = "parent M 1 ?j1"  let ?w = "?j1 - ?j0"
  let ?Mn = "(M::pairseq)[n]"
  let ?d0 = "entry M 0 ?j1 - entry M 0 ?j0"
  let ?z = "?j0 + q * ?w + s"          \<comment> \<open>the in-block column\<close>
  let ?jN = "Lng ?Mn - 1"              \<comment> \<open>the N-endpoint\<close>
  have w0: "0 < ?w" using j0lt by linarith
  have n0: "0 < n" using qn by simp
  \<comment> \<open>(1) length of \<open>N\<close>, and the endpoint as block \<open>n-1\<close>, offset \<open>w-1\<close>\<close>
  have lenN: "Lng ?Mn = ?j0 + n * ?w"
    by (rule oper_d1pos_LngM[OF L notzero hp i1z j0lt])
  have jNflat: "Lng ?Mn = ?j0 + (n - 1) * ?w + ?w"
  proof -
    have "?j0 + n * ?w = ?j0 + (Suc (n - 1)) * ?w" using n0 by simp
    also have "\<dots> = ?j0 + (n - 1) * ?w + ?w" by simp
    finally show ?thesis using lenN by simp
  qed
  have jNeq: "?jN = ?j0 + (n - 1) * ?w + (?w - 1)"
    using jNflat w0 by linarith
  \<comment> \<open>(2) the IH-ramp at the two offsets \<open>s\<close> and \<open>w-1\<close>, and \<open>d\<^sub>0 = w\<close>\<close>
  have e_s: "entry M 0 (?j0 + s) = entry M 0 ?j0 + s"
    using ramp[of s] sw by simp
  have e_wm1: "entry M 0 (?j0 + (?w - 1)) = entry M 0 ?j0 + (?w - 1)"
    using ramp[of "?w - 1"] by simp
  have e_w: "entry M 0 (?j0 + ?w) = entry M 0 ?j0 + ?w"
    using ramp[of ?w] by simp
  have j0pw: "?j0 + ?w = ?j1" using j0lt by simp
  have d0w: "?d0 = ?w"
  proof -
    have "entry M 0 ?j1 = entry M 0 ?j0 + ?w" using e_w j0pw by simp
    thus ?thesis by simp
  qed
  \<comment> \<open>(3) row-0 readback at \<open>z\<close> (in-block) and at the endpoint (block \<open>n-1\<close>, offset \<open>w-1\<close>)\<close>
  have rb_z: "entry ?Mn 0 ?z = entry M 0 (?j0 + s) + q * ?d0"
    by (rule oper_d1pos_entry0[OF L notzero hp i1z j0lt qn sw])
  have wm1w: "?w - 1 < ?w" using w0 by simp
  have nm1n: "n - 1 < n" using n0 by simp
  have rb_end: "entry ?Mn 0 (?j0 + (n - 1) * ?w + (?w - 1))
                  = entry M 0 (?j0 + (?w - 1)) + (n - 1) * ?d0"
    by (rule oper_d1pos_entry0[OF L notzero hp i1z j0lt nm1n wm1w])
  have e_end: "entry ?Mn 0 ?jN = entry M 0 ?j0 + (?w - 1) + (n - 1) * ?w"
    using rb_end e_wm1 d0w jNeq by simp
  have e_z: "entry ?Mn 0 ?z = entry M 0 ?j0 + s + q * ?w"
    using rb_z e_s d0w by simp
  \<comment> \<open>(4) the width \<open>jN - z\<close>, with \<open>z < jN\<close>\<close>
  have qle_nm1: "q \<le> n - 1" using qn by simp
  have width: "?jN - ?z = (n - 1) * ?w + (?w - 1) - (q * ?w + s)"
    using jNeq by simp
  \<comment> \<open>(5) close the endpoint equation by flat arithmetic\<close>
  have rhs: "entry ?Mn 0 ?z + (?jN - ?z)
             = entry M 0 ?j0 + s + q * ?w
               + ((n - 1) * ?w + (?w - 1) - (q * ?w + s))"
    using e_z width by simp
  have qle: "q * ?w + s \<le> (n - 1) * ?w + (?w - 1)"
  proof -
    have "q * ?w \<le> (n - 1) * ?w" using qle_nm1 by (rule mult_le_mono1)
    moreover have "s \<le> ?w - 1" using sw w0 by simp
    ultimately show ?thesis by linarith
  qed
  have arith: "s + q * ?w + ((n - 1) * ?w + (?w - 1) - (q * ?w + s))
                 = (?w - 1) + (n - 1) * ?w"
    using qle by simp
  show ?thesis
    using rhs e_end arith by simp
qed


lemma Mtail_ramp_from_Ez:
  fixes M :: pairseq
  assumes N: "M \<in> ST_PS"
    and L: "1 < Lng M"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and zlo: "parent M 1 (Lng M - 1) < z"
    and zhi: "z < Lng M - 1"
    and Ez: "entry M 0 (Lng M - 1) = entry M 0 z + ((Lng M - 1) - z)"
    and segReach: "\<And>x. parent M 1 (Lng M - 1) \<le> x \<Longrightarrow> x \<le> z \<Longrightarrow> le0 M x z"
    and t: "t \<le> Lng M - 1 - parent M 1 (Lng M - 1)"
  shows "entry M 0 (parent M 1 (Lng M - 1) + t)
           = entry M 0 (parent M 1 (Lng M - 1)) + t"
proof -
  let ?j1 = "Lng M - 1"  let ?j0 = "parent M 1 ?j1"
  have j0z: "?j0 < z" using zlo .
  have zj1: "z < ?j1" using zhi .
  \<comment> \<open>the \<open>+1\<close> step on \<open>[z, j\<^sub>1)\<close> from \<open>E\<^sub>z M z\<close>\<close>
  have rampZ: "\<And>x. z \<le> x \<Longrightarrow> x < ?j1 \<Longrightarrow> entry M 0 (Suc x) = Suc (entry M 0 x)"
    by (rule subramp_from_Ep[OF N zhi Ez])
  have strictZ: "\<And>y. z \<le> y \<Longrightarrow> y < ?j1 \<Longrightarrow> entry M 0 y < entry M 0 (Suc y)"
  proof -
    fix y assume yz: "z \<le> y" and yj1: "y < ?j1"
    have "entry M 0 (Suc y) = Suc (entry M 0 y)" by (rule rampZ[OF yz yj1])
    thus "entry M 0 y < entry M 0 (Suc y)" by simp
  qed
  \<comment> \<open>\<open>le0 M z j\<^sub>1\<close> from \<open>E\<^sub>z M z\<close>\<close>
  have le0zj1: "le0 M z ?j1" by (rule le0_z_j1_from_Ez[OF N zhi Ez])
  have j1L: "?j1 < Lng M" using L by simp
  \<comment> \<open>tailReach above \<open>z\<close>: \<open>le0 M x j\<^sub>1\<close> for \<open>z \<le> x < j\<^sub>1\<close>\<close>
  have reachAbove: "\<And>x. z \<le> x \<Longrightarrow> x < ?j1 \<Longrightarrow> le0 M x ?j1"
  proof -
    fix x assume xz: "z \<le> x" and xj1: "x < ?j1"
    show "le0 M x ?j1" by (rule tailReach_from_row0_strict[OF j1L strictZ xz xj1])
  qed
  \<comment> \<open>tailReach below \<open>z\<close>: \<open>le0 M x j\<^sub>1\<close> for \<open>j\<^sub>0 \<le> x \<le> z\<close> via segment chain\<close>
  have reachBelow: "\<And>x. ?j0 \<le> x \<Longrightarrow> x \<le> z \<Longrightarrow> le0 M x ?j1"
  proof -
    fix x assume xlo: "?j0 \<le> x" and xz: "x \<le> z"
    have sx: "le0 M x z" by (rule segReach[OF xlo xz])
    show "le0 M x ?j1" by (rule le0_trans[OF sx le0zj1])
  qed
  \<comment> \<open>full tailReach on \<open>[j\<^sub>0, j\<^sub>1)\<close>\<close>
  have tailReach: "\<And>x. ?j0 \<le> x \<Longrightarrow> x < ?j1 \<Longrightarrow> le0 M x ?j1"
  proof -
    fix x assume xlo: "?j0 \<le> x" and xhi: "x < ?j1"
    show "le0 M x ?j1"
    proof (cases "x \<le> z")
      case True show ?thesis by (rule reachBelow[OF xlo True])
    next
      case False
      have zx: "z \<le> x" using False by simp
      show ?thesis by (rule reachAbove[OF zx xhi])
    qed
  qed
  \<comment> \<open>\<open>E\<^sub>p\<close> at \<open>j\<^sub>0\<close>, then cumulate to the exact \<open>+1\<close> ramp\<close>
  have Ep0: "entry M 0 ?j1 = entry M 0 ?j0 + (?j1 - ?j0)"
    by (rule Ep_from_le0_tail[OF N j0lt tailReach])
  \<comment> \<open>the \<open>+1\<close> step on \<open>[j\<^sub>0, j\<^sub>1)\<close> via the glue, cumulated to absolute form\<close>
  have ramp0: "\<And>x. ?j0 \<le> x \<Longrightarrow> x < ?j1 \<Longrightarrow> entry M 0 (Suc x) = Suc (entry M 0 x)"
    by (rule subramp_from_Ep[OF N j0lt Ep0])
  have ramp_abs: "\<And>tt. ?j0 + tt \<le> ?j1 \<Longrightarrow> entry M 0 (?j0 + tt) = entry M 0 ?j0 + tt"
  proof -
    fix tt assume "?j0 + tt \<le> ?j1"
    thus "entry M 0 (?j0 + tt) = entry M 0 ?j0 + tt"
    proof (induction tt)
      case 0 show ?case by simp
    next
      case (Suc tt)
      have le1: "?j0 + tt \<le> ?j1" using Suc.prems by simp
      have lt: "?j0 + tt < ?j1" using Suc.prems by simp
      have ge: "?j0 \<le> ?j0 + tt" by simp
      have step: "entry M 0 (Suc (?j0 + tt)) = Suc (entry M 0 (?j0 + tt))"
        by (rule ramp0[OF ge lt])
      have ih: "entry M 0 (?j0 + tt) = entry M 0 ?j0 + tt" using Suc.IH[OF le1] .
      show ?case using step ih by simp
    qed
  qed
  have prem: "?j0 + t \<le> ?j1" using t j0lt by linarith
  show ?thesis by (rule ramp_abs[OF prem])
qed


text \<open>§6.7 IN-BLOCK oper STEP for \<open>E\<^sub>z\<close> (attempt C): the combiner that feeds the
  IH-supply @{thm [source] Mtail_ramp_from_Ez} into @{thm [source] ez_inblock_lift}.
  For \<open>N = M[n]\<close> in the expansion case, and an IN-BLOCK column
  \<open>z\<^sub>N = j\<^sub>0 + q\<cdot>w + s\<close> (\<open>q<n\<close>, \<open>0<s<w\<close>), the M-side IH-INPUT --- the endpoint
  slope-1 \<open>E\<^sub>z M z\<close> at a gated M-node \<open>z\<close> whose row-1 parent is the block start
  \<open>j\<^sub>0 = parent M 1 (Lng M-1)\<close>, plus the segment reachability \<open>le0 M x z\<close> on
  \<open>[j\<^sub>0, z]\<close> --- yields the N-side endpoint slope-1 equation \<open>E\<^sub>z N z\<^sub>N\<close>:
  \<open>entry N 0 (Lng N-1) = entry N 0 z\<^sub>N + ((Lng N-1) - z\<^sub>N)\<close>.
  Route: @{thm [source] Mtail_ramp_from_Ez} converts the IH input to the whole
  M-tail \<open>+1\<close> ramp on \<open>[j\<^sub>0, Lng M-1]\<close>, which is exactly the ramp hypothesis of
  @{thm [source] ez_inblock_lift}.  Cites only those two already-GREEN bricks; no
  spsy / sblk / RedCond / oper-tiling / tail_affine.  This is the IN-BLOCK arm of
  the \<open>E\<^sub>z\<close> ST_PS.induct oper step (the s=0 boundary is vacuous for gated z; the
  PREFIX \<open>z\<^sub>N < j\<^sub>0\<close> arm is the named residual).\<close>

lemma ez_inblock_oper_step:
  fixes M :: pairseq
  assumes MST: "M \<in> ST_PS"
    and L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and qn: "q < n"
    and s0: "0 < s"
    and sw: "s < Lng M - 1 - parent M 1 (Lng M - 1)"
    \<comment> \<open>the IH input on the M side: \<open>E\<^sub>z M z\<close> at a gated M-node \<open>z\<close> over \<open>j\<^sub>0\<close>\<close>
    and zlo: "parent M 1 (Lng M - 1) < z"
    and zhi: "z < Lng M - 1"
    and Ez: "entry M 0 (Lng M - 1) = entry M 0 z + ((Lng M - 1) - z)"
    and segReach: "\<And>x. parent M 1 (Lng M - 1) \<le> x \<Longrightarrow> x \<le> z \<Longrightarrow> le0 M x z"
  shows "entry ((M::pairseq)[n]) 0 (Lng ((M::pairseq)[n]) - 1)
       = entry ((M::pairseq)[n]) 0
              (parent M 1 (Lng M - 1)
                 + q * (Lng M - 1 - parent M 1 (Lng M - 1)) + s)
         + ((Lng ((M::pairseq)[n]) - 1)
              - (parent M 1 (Lng M - 1)
                   + q * (Lng M - 1 - parent M 1 (Lng M - 1)) + s))"
proof -
  \<comment> \<open>the whole M-tail \<open>+1\<close> ramp from the IH input\<close>
  have ramp: "\<And>t. t \<le> Lng M - 1 - parent M 1 (Lng M - 1)
                 \<Longrightarrow> entry M 0 (parent M 1 (Lng M - 1) + t)
                       = entry M 0 (parent M 1 (Lng M - 1)) + t"
    by (rule Mtail_ramp_from_Ez[OF MST L j0lt zlo zhi Ez segReach])
  \<comment> \<open>lift to the N-side in-block endpoint equation\<close>
  show ?thesis
    by (rule ez_inblock_lift[OF L notzero hp i1z j0lt qn s0 sw ramp])
qed


lemma ez_prefix_lift:
  fixes M :: pairseq
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and n0: "0 < n"
    and zlt: "z < parent M 1 (Lng M - 1)"
    \<comment> \<open>the IH content: the M-side row-0 reading is the exact \<open>+1\<close> ramp on the whole
       tail \<open>[z, Lng M-1]\<close> from base \<open>z\<close>\<close>
    and ramp: "\<And>t. z + t \<le> Lng M - 1
                 \<Longrightarrow> entry M 0 (z + t) = entry M 0 z + t"
  shows "entry ((M::pairseq)[n]) 0 (Lng ((M::pairseq)[n]) - 1)
       = entry ((M::pairseq)[n]) 0 z
         + ((Lng ((M::pairseq)[n]) - 1) - z)"
proof -
  let ?j1 = "Lng M - 1"  let ?j0 = "parent M 1 ?j1"  let ?w = "?j1 - ?j0"
  let ?Mn = "(M::pairseq)[n]"
  let ?d0 = "entry M 0 ?j1 - entry M 0 ?j0"
  let ?jN = "Lng ?Mn - 1"              \<comment> \<open>the N-endpoint\<close>
  have w0: "0 < ?w" using j0lt by linarith
  have zlej0: "z \<le> ?j0" using zlt by linarith
  have zlej1: "z \<le> ?j1" using zlej0 j0lt by linarith
  \<comment> \<open>(1) length of \<open>N\<close>, and the endpoint as block \<open>n-1\<close>, offset \<open>w-1\<close>\<close>
  have lenN: "Lng ?Mn = ?j0 + n * ?w"
    by (rule oper_d1pos_LngM[OF L notzero hp i1z j0lt])
  have jNflat: "Lng ?Mn = ?j0 + (n - 1) * ?w + ?w"
  proof -
    have "?j0 + n * ?w = ?j0 + (Suc (n - 1)) * ?w" using n0 by simp
    also have "\<dots> = ?j0 + (n - 1) * ?w + ?w" by simp
    finally show ?thesis using lenN by simp
  qed
  have jNeq: "?jN = ?j0 + (n - 1) * ?w + (?w - 1)"
    using jNflat w0 by linarith
  \<comment> \<open>(2) ramp in ABSOLUTE form for any \<open>y \<in> [z, j\<^sub>1]\<close>, then read at \<open>j\<^sub>0\<close>, \<open>j\<^sub>1\<close>, \<open>j\<^sub>0+(w-1)\<close>\<close>
  have ramp_abs: "\<And>y. z \<le> y \<Longrightarrow> y \<le> ?j1 \<Longrightarrow> entry M 0 y = entry M 0 z + (y - z)"
  proof -
    fix y assume zy: "z \<le> y" and yj1: "y \<le> ?j1"
    obtain t where yt: "y = z + t" using zy le_Suc_ex by blast
    have "z + t \<le> ?j1" using yt yj1 by simp
    from ramp[OF this] have "entry M 0 (z + t) = entry M 0 z + t" .
    thus "entry M 0 y = entry M 0 z + (y - z)" using yt by simp
  qed
  have e_j0: "entry M 0 ?j0 = entry M 0 z + (?j0 - z)"
    by (rule ramp_abs[OF zlej0]) (use j0lt in linarith)
  have e_j1: "entry M 0 ?j1 = entry M 0 z + (?j1 - z)"
    by (rule ramp_abs[OF zlej1 le_refl])
  have d0w: "?d0 = ?w"
  proof -
    have "entry M 0 ?j1 - entry M 0 ?j0
            = (entry M 0 z + (?j1 - z)) - (entry M 0 z + (?j0 - z))"
      using e_j0 e_j1 by simp
    also have "\<dots> = (?j1 - z) - (?j0 - z)" by simp
    also have "\<dots> = ?w" using zlej0 j0lt by simp
    finally show ?thesis .
  qed
  \<comment> \<open>the slice value at offset \<open>w-1\<close> (still inside the ramp, \<open>j\<^sub>0+(w-1) \<le> j\<^sub>1\<close>).
     AVOID handing the decision procedure a goal where \<open>?w = ?j1 - ?j0\<close> re-expands
     the \<open>parent\<close> atom twice under nested nat-subtraction (CLAUDE.md gotcha): chain
     through the cheap assoc step \<open>?j0 + (?w-1) = ?j0 + ?w - 1\<close> (w0-only) plus the
     flat equation \<open>?j0 + ?w = ?j1\<close>.\<close>
  have j0pw: "?j0 + ?w = ?j1" using j0lt by simp
  have j0wm1assoc: "?j0 + (?w - 1) = ?j1 - 1"
  proof -
    have "?j0 + (?w - 1) = ?j0 + ?w - 1" using w0 by simp
    also have "\<dots> = ?j1 - 1" using j0pw by simp
    finally show ?thesis .
  qed
  have j0wm1le: "?j0 + (?w - 1) \<le> ?j1" using j0wm1assoc by simp
  have zle_j0wm1: "z \<le> ?j0 + (?w - 1)"
  proof -
    have "z \<le> ?j1 - 1" using zlej0 j0lt by simp
    thus ?thesis using j0wm1assoc by simp
  qed
  have e_wm1: "entry M 0 (?j0 + (?w - 1)) = entry M 0 z + (?j0 + (?w - 1) - z)"
    by (rule ramp_abs[OF zle_j0wm1 j0wm1le])
  \<comment> \<open>(3) row-0 readback at the endpoint (block \<open>n-1\<close>, offset \<open>w-1\<close>) and at \<open>z\<close> (prefix).
     Abstract the block-base \<open>A = j\<^sub>0+(w-1)\<close> and carry \<open>B = (n-1)\<cdot>w\<close> as opaque nats
     so the decision procedure never re-expands the \<open>?w = j\<^sub>1 - j\<^sub>0\<close> atom (CLAUDE.md).\<close>
  have wm1w: "?w - 1 < ?w" using w0 by simp
  have nm1n: "n - 1 < n" using n0 by simp
  have rb_end: "entry ?Mn 0 (?j0 + (n - 1) * ?w + (?w - 1))
                  = entry M 0 (?j0 + (?w - 1)) + (n - 1) * ?d0"
    by (rule oper_d1pos_entry0[OF L notzero hp i1z j0lt nm1n wm1w])
  define A where "A = ?j0 + (?w - 1)"
  define B where "B = (n - 1) * ?w"
  have jN_AB: "?jN = A + B" using jNeq by (simp add: A_def B_def add.commute add.left_commute)
  have zleA: "z \<le> A" using zle_j0wm1 by (simp add: A_def)
  have e_wm1A: "entry M 0 A = entry M 0 z + (A - z)" using e_wm1 by (simp add: A_def)
  have rb_endA: "entry ?Mn 0 (A + B) = entry M 0 A + B"
  proof -
    have base: "entry ?Mn 0 (?j0 + (n - 1) * ?w + (?w - 1)) = entry M 0 A + B"
      using rb_end d0w by (simp add: A_def B_def)
    have idx: "?j0 + (n - 1) * ?w + (?w - 1) = A + B"
      by (simp add: A_def B_def add.commute add.left_commute)
    show ?thesis using base idx by simp
  qed
  have e_end: "entry ?Mn 0 ?jN = entry M 0 z + ((A - z) + B)"
  proof -
    have "entry ?Mn 0 ?jN = entry ?Mn 0 (A + B)" using jN_AB by simp
    also have "\<dots> = entry M 0 A + B" using rb_endA .
    also have "\<dots> = entry M 0 z + (A - z) + B" using e_wm1A by simp
    finally show ?thesis by simp
  qed
  have rb_z: "entry ?Mn 0 z = entry M 0 z"
  proof -
    have "?Mn ! z = M ! z"
      by (rule oper_d1pos_nth_prefix[OF L notzero hp i1z zlt])
    thus ?thesis by (simp add: entry_def)
  qed
  \<comment> \<open>(4) the two closed forms coincide on the slope-1 line (opaque \<open>A\<close>, \<open>B\<close>)\<close>
  have width: "?jN - z = (A - z) + B" using jN_AB zleA by simp
  have "entry ?Mn 0 z + (?jN - z) = entry M 0 z + ((A - z) + B)"
    using rb_z width by simp
  thus ?thesis using e_end by simp
qed


lemma segReach_from_row0_strict:
  fixes N :: pairseq
  assumes bL: "b < Lng N"
    and strict: "\<And>y. p \<le> y \<Longrightarrow> y < b \<Longrightarrow> entry N 0 y < entry N 0 (Suc y)"
    and xlo: "p \<le> x"
    and xhi: "x \<le> b"
  shows "le0 N x b"
proof -
  \<comment> \<open>chain upward from any base \<open>c \<in> [p, b]\<close> to \<open>b\<close>, by induction on the gap \<open>b - c\<close>\<close>
  have chain: "\<And>c. p \<le> c \<Longrightarrow> c \<le> b \<Longrightarrow> le0 N c b"
  proof -
    fix c assume "p \<le> c" and "c \<le> b"
    then show "le0 N c b"
    proof (induction "b - c" arbitrary: c)
      case 0
      have "c = b" using 0 by linarith
      thus ?case using bL by (simp add: le0_refl)
    next
      case (Suc d)
      have clt: "c < b" using Suc.hyps(2) by linarith
      have pc: "p \<le> c" using Suc.prems(1) .
      have inc: "entry N 0 c < entry N 0 (Suc c)" by (rule strict[OF pc clt])
      have scL: "Suc c < Lng N" using clt bL by simp
      have step: "le0 N c (Suc c)" by (rule le0_step_consec[OF scL inc])
      have dEq: "d = b - Suc c" using Suc.hyps(2) by linarith
      have psc: "p \<le> Suc c" using pc by simp
      have scle: "Suc c \<le> b" using clt by simp
      have rest: "le0 N (Suc c) b" using Suc.hyps(1)[OF dEq psc scle] .
      show ?case by (rule le0_trans[OF step rest])
    qed
  qed
  show ?thesis by (rule chain[OF xlo xhi])
qed


text \<open>§6.7 IN-BLOCK oper STEP for \<open>E\<^sub>z\<close> with the \<open>segReach\<close> input REPLACED by the
  cleaner M-side ROW-0 \<open>+1\<close> STEP on the lower segment \<open>[j\<^sub>0, z)\<close> (attempt E).  The
  \<open>segReach\<close> hypothesis of @{thm [source] ez_inblock_oper_step} (the row-0 reach
  \<open>le0 M x z\<close> on \<open>[j\<^sub>0, z]\<close>) is exactly what the new GREEN brick
  @{thm [source] segReach_from_row0_strict} produces from the per-consecutive
  STRICT row-0 increase on \<open>[j\<^sub>0, z)\<close>.  That strict increase, together with the
  endpoint slope-1 \<open>E\<^sub>z M z\<close> (which carries the per-step increase on \<open>[z, j\<^sub>1)\<close>),
  is precisely the row-0 \<open>+1\<close> structure of the gated M-node \<open>z\<close> supplied by the
  \<open>E\<^sub>z\<close> induction hypothesis on \<open>M\<close> (EMPIRICALLY 0-fail: for the N-side in-block
  gated column the M-witness \<open>z\<^sub>0 = j\<^sub>0 + s\<close> is itself M-gated with \<open>E\<^sub>z M z\<^sub>0\<close> and
  the strict step on \<open>[j\<^sub>0, z\<^sub>0)\<close> both holding).  Cites only the GREEN bricks
  @{thm [source] segReach_from_row0_strict} and
  @{thm [source] ez_inblock_oper_step}; no spsy / sblk / RedCond / oper-tiling /
  tail_affine.\<close>

lemma ez_inblock_oper_step_via_strict:
  fixes M :: pairseq
  assumes MST: "M \<in> ST_PS"
    and L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and qn: "q < n"
    and s0: "0 < s"
    and sw: "s < Lng M - 1 - parent M 1 (Lng M - 1)"
    and zlo: "parent M 1 (Lng M - 1) < z"
    and zhi: "z < Lng M - 1"
    and Ez: "entry M 0 (Lng M - 1) = entry M 0 z + ((Lng M - 1) - z)"
    \<comment> \<open>the M-side IH input on the LOWER segment: row-0 \<open>+1\<close> step on \<open>[j\<^sub>0, z)\<close>\<close>
    and lowstrict: "\<And>y. parent M 1 (Lng M - 1) \<le> y \<Longrightarrow> y < z
                        \<Longrightarrow> entry M 0 y < entry M 0 (Suc y)"
  shows "entry ((M::pairseq)[n]) 0 (Lng ((M::pairseq)[n]) - 1)
       = entry ((M::pairseq)[n]) 0
              (parent M 1 (Lng M - 1)
                 + q * (Lng M - 1 - parent M 1 (Lng M - 1)) + s)
         + ((Lng ((M::pairseq)[n]) - 1)
              - (parent M 1 (Lng M - 1)
                   + q * (Lng M - 1 - parent M 1 (Lng M - 1)) + s))"
proof -
  let ?j1 = "Lng M - 1"  let ?j0 = "parent M 1 ?j1"
  have zL: "z < Lng M" using zhi by simp
  \<comment> \<open>the lower-segment reach from the strict step via the GREEN reach brick\<close>
  have segReach: "\<And>x. ?j0 \<le> x \<Longrightarrow> x \<le> z \<Longrightarrow> le0 M x z"
  proof -
    fix x assume xlo: "?j0 \<le> x" and xz: "x \<le> z"
    show "le0 M x z" by (rule segReach_from_row0_strict[OF zL lowstrict xlo xz])
  qed
  show ?thesis
    by (rule ez_inblock_oper_step
          [OF MST L notzero hp i1z j0lt qn s0 sw zlo zhi Ez segReach])
qed


text \<open>§6.7 PREFIX oper STEP for \<open>E\<^sub>z\<close> with the whole-tail ramp REPLACED by the
  M-side ENDPOINT slope-1 \<open>E\<^sub>z M z\<close> (attempt E).  For \<open>N = M[n]\<close> and a PREFIX
  column \<open>z < j\<^sub>0 = parent M 1 (Lng M-1)\<close> the input @{thm [source] ez_prefix_lift}
  consumes is the exact \<open>+1\<close> row-0 ramp on the WHOLE M-tail \<open>[z, Lng M-1]\<close> from
  base \<open>z\<close>.  That ramp is exactly @{thm [source] subramp_from_Ep} (base \<open>z\<close>)
  cumulated: the per-step \<open>entry M 0 (Suc x) = Suc (entry M 0 x)\<close> on \<open>[z, j\<^sub>1)\<close>
  is upgraded from the endpoint slope-1 \<open>E\<^sub>z M z\<close>
  (\<open>entry M 0 (Lng M-1) = entry M 0 z + ((Lng M-1) - z)\<close>) via the global per-step
  \<open>\<le> +1\<close> cap.  \<open>E\<^sub>z M z\<close> at the PREFIX node \<open>z\<close> (on \<open>M\<close>'s OWN endpoint) is the
  natural M-side IH fact (EMPIRICALLY 0-fail on the broad ST_PS closure: for the
  N-side prefix gated column the same column \<open>z < j\<^sub>0\<close> in \<open>M\<close> satisfies
  \<open>E\<^sub>z M z\<close>).  Cites only @{thm [source] subramp_from_Ep} and
  @{thm [source] ez_prefix_lift}; no spsy / sblk / RedCond / oper-tiling /
  tail_affine.\<close>

lemma ez_prefix_oper_step_via_Ez:
  fixes M :: pairseq
  assumes MST: "M \<in> ST_PS"
    and L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and n0: "0 < n"
    and zlt: "z < parent M 1 (Lng M - 1)"
    \<comment> \<open>the M-side IH input: the endpoint slope-1 \<open>E\<^sub>z M z\<close> at the prefix node \<open>z\<close>\<close>
    and EzM: "entry M 0 (Lng M - 1) = entry M 0 z + ((Lng M - 1) - z)"
  shows "entry ((M::pairseq)[n]) 0 (Lng ((M::pairseq)[n]) - 1)
       = entry ((M::pairseq)[n]) 0 z
         + ((Lng ((M::pairseq)[n]) - 1) - z)"
proof -
  let ?j1 = "Lng M - 1"
  have zj1: "z < ?j1" using zlt j0lt by linarith
  \<comment> \<open>the exact \<open>+1\<close> sub-ramp on \<open>[z, j\<^sub>1)\<close> from the endpoint slope-1\<close>
  have step: "\<And>x. z \<le> x \<Longrightarrow> x < ?j1 \<Longrightarrow> entry M 0 (Suc x) = Suc (entry M 0 x)"
    by (rule subramp_from_Ep[OF MST zj1 EzM])
  \<comment> \<open>cumulate to the absolute \<open>+1\<close> ramp on \<open>[z, j\<^sub>1]\<close> from base \<open>z\<close>\<close>
  have ramp: "\<And>t. z + t \<le> ?j1 \<Longrightarrow> entry M 0 (z + t) = entry M 0 z + t"
  proof -
    fix t assume "z + t \<le> ?j1"
    thus "entry M 0 (z + t) = entry M 0 z + t"
    proof (induction t)
      case 0 show ?case by simp
    next
      case (Suc t)
      have le1: "z + t \<le> ?j1" using Suc.prems by simp
      have lt: "z + t < ?j1" using Suc.prems by simp
      have ge: "z \<le> z + t" by simp
      have st: "entry M 0 (Suc (z + t)) = Suc (entry M 0 (z + t))"
        by (rule step[OF ge lt])
      have ih: "entry M 0 (z + t) = entry M 0 z + t" using Suc.IH[OF le1] .
      show ?case using st ih by simp
    qed
  qed
  show ?thesis
    by (rule ez_prefix_lift[OF L notzero hp i1z j0lt n0 zlt ramp])
qed


text \<open>§6.7 IN-BLOCK IH-APPLICATION BRIDGE (attempt H).  This packages the two
  M-side hypotheses that @{thm [source] ez_inblock_oper_step_via_strict} consumes
  --- the endpoint slope-1 \<open>E\<^sub>z M (j\<^sub>0+s)\<close> AND the lower-segment strict \<open>+1\<close> step
  on \<open>[j\<^sub>0, j\<^sub>0+s)\<close> --- directly from the strong-induction IH content presented as a
  full \<open>+1\<close> row-0 ramp on the whole M-tail \<open>[j\<^sub>0, j\<^sub>1]\<close> (the \<open>fullramp(M)\<close> form
  recommended by the prior round).  It then chains to deliver \<open>E\<^sub>z N\<close> at the
  N-side in-block column \<open>j\<^sub>0 + q\<cdot>w + s\<close>.  Cites only the already-GREEN
  @{thm [source] ez_inblock_oper_step_via_strict}; no spsy / sblk / RedCond /
  oper-tiling / tail_affine.  EMPIRICALLY 0-fail on the broad ST_PS closure
  (in-block gated z: 229/0, python/_bridge_H.py).\<close>

lemma ez_inblock_oper_step_via_fullramp:
  fixes M :: pairseq
  assumes MST: "M \<in> ST_PS"
    and L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and qn: "q < n"
    and s0: "0 < s"
    and sw: "s < Lng M - 1 - parent M 1 (Lng M - 1)"
    \<comment> \<open>the IH content: the whole M-tail \<open>[j\<^sub>0, j\<^sub>1]\<close> is an exact \<open>+1\<close> row-0 ramp\<close>
    and ramp: "\<And>t. t \<le> Lng M - 1 - parent M 1 (Lng M - 1)
                 \<Longrightarrow> entry M 0 (parent M 1 (Lng M - 1) + t)
                       = entry M 0 (parent M 1 (Lng M - 1)) + t"
  shows "entry ((M::pairseq)[n]) 0 (Lng ((M::pairseq)[n]) - 1)
       = entry ((M::pairseq)[n]) 0
              (parent M 1 (Lng M - 1)
                 + q * (Lng M - 1 - parent M 1 (Lng M - 1)) + s)
         + ((Lng ((M::pairseq)[n]) - 1)
              - (parent M 1 (Lng M - 1)
                   + q * (Lng M - 1 - parent M 1 (Lng M - 1)) + s))"
proof -
  let ?j1 = "Lng M - 1"  let ?j0 = "parent M 1 ?j1"
  let ?z0 = "?j0 + s"
  \<comment> \<open>the M-side child column \<open>?z0 = j\<^sub>0 + s\<close> is a strict interior point of \<open>M\<close>\<close>
  have zlo: "?j0 < ?z0" using s0 by simp
  have zhi: "?z0 < ?j1" using sw by linarith
  \<comment> \<open>the endpoint slope-1 \<open>E\<^sub>z M ?z0\<close> from the M-tail ramp at offsets \<open>s\<close> and \<open>w\<close>\<close>
  have e_s: "entry M 0 ?z0 = entry M 0 ?j0 + s"
    using ramp[of s] sw by simp
  have wle: "?j1 - ?j0 \<le> ?j1 - ?j0" by simp
  have e_w: "entry M 0 (?j0 + (?j1 - ?j0)) = entry M 0 ?j0 + (?j1 - ?j0)"
    using ramp[of "?j1 - ?j0"] by simp
  have j0pw: "?j0 + (?j1 - ?j0) = ?j1" using j0lt by simp
  have e_j1: "entry M 0 ?j1 = entry M 0 ?j0 + (?j1 - ?j0)"
    using e_w j0pw by simp
  have Ez0: "entry M 0 ?j1 = entry M 0 ?z0 + (?j1 - ?z0)"
  proof -
    have "entry M 0 ?z0 + (?j1 - ?z0) = entry M 0 ?j0 + s + (?j1 - (?j0 + s))"
      using e_s by simp
    also have "\<dots> = entry M 0 ?j0 + (?j1 - ?j0)" using zhi by simp
    also have "\<dots> = entry M 0 ?j1" using e_j1 by simp
    finally show ?thesis by simp
  qed
  \<comment> \<open>the lower-segment strict \<open>+1\<close> step on \<open>[j\<^sub>0, ?z0)\<close> from the same ramp\<close>
  have lowstrict: "\<And>y. ?j0 \<le> y \<Longrightarrow> y < ?z0 \<Longrightarrow> entry M 0 y < entry M 0 (Suc y)"
  proof -
    fix y assume yl: "?j0 \<le> y" and yh: "y < ?z0"
    define t where "t = y - ?j0"
    have yt: "y = ?j0 + t" using t_def yl by simp
    have tw: "t \<le> ?j1 - ?j0" using yh yt zhi by linarith
    have tw1: "Suc t \<le> ?j1 - ?j0" using yh yt zhi by linarith
    have ey: "entry M 0 y = entry M 0 ?j0 + t" using ramp[of t] tw yt by simp
    have eSy: "entry M 0 (Suc y) = entry M 0 ?j0 + Suc t"
    proof -
      have "Suc y = ?j0 + Suc t" using yt by simp
      thus ?thesis using ramp[of "Suc t"] tw1 by simp
    qed
    show "entry M 0 y < entry M 0 (Suc y)" using ey eSy by simp
  qed
  show ?thesis
    by (rule ez_inblock_oper_step_via_strict
          [OF MST L notzero hp i1z j0lt qn s0 sw zlo zhi Ez0 lowstrict])
qed


text \<open>§6.7 PREFIX IH-APPLICATION BRIDGE (attempt H).  Re-presents the M-side
  IH input that @{thm [source] ez_prefix_oper_step_via_Ez} consumes (the endpoint
  slope-1 \<open>E\<^sub>z M z\<close> at the prefix node \<open>z < j\<^sub>0\<close>) as the equivalent full \<open>+1\<close>
  row-0 ramp on the M-tail \<open>[z, j\<^sub>1]\<close> from base \<open>z\<close> --- the same \<open>fullramp\<close> shape
  used by the in-block bridge, so a single strong-induction IH (the M-tail ramp)
  feeds BOTH oper arms.  Cites only the already-GREEN
  @{thm [source] ez_prefix_oper_step_via_Ez} and
  @{thm [source] le0_z_j1_from_Ez}; no spsy / sblk / RedCond / oper-tiling /
  tail_affine.  EMPIRICALLY 0-fail (prefix gated z: 852/0, python/_bridge_H.py).\<close>

lemma ez_prefix_oper_step_via_ramp:
  fixes M :: pairseq
  assumes MST: "M \<in> ST_PS"
    and L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and n0: "0 < n"
    and zlt: "z < parent M 1 (Lng M - 1)"
    \<comment> \<open>the IH content: \<open>+1\<close> row-0 ramp on the M-tail \<open>[z, j\<^sub>1]\<close> from base \<open>z\<close>\<close>
    and ramp: "\<And>t. z + t \<le> Lng M - 1
                 \<Longrightarrow> entry M 0 (z + t) = entry M 0 z + t"
  shows "entry ((M::pairseq)[n]) 0 (Lng ((M::pairseq)[n]) - 1)
       = entry ((M::pairseq)[n]) 0 z
         + ((Lng ((M::pairseq)[n]) - 1) - z)"
proof -
  let ?j1 = "Lng M - 1"
  have zj1: "z < ?j1" using zlt j0lt by linarith
  \<comment> \<open>the endpoint slope-1 \<open>E\<^sub>z M z\<close> from the ramp at offset \<open>j\<^sub>1 - z\<close>\<close>
  have EzM: "entry M 0 ?j1 = entry M 0 z + (?j1 - z)"
  proof -
    have "z + (?j1 - z) \<le> ?j1" using zj1 by simp
    hence "entry M 0 (z + (?j1 - z)) = entry M 0 z + (?j1 - z)"
      using ramp[of "?j1 - z"] by simp
    moreover have "z + (?j1 - z) = ?j1" using zj1 by simp
    ultimately show ?thesis by simp
  qed
  show ?thesis
    by (rule ez_prefix_oper_step_via_Ez
          [OF MST L notzero hp i1z j0lt n0 zlt EzM])
qed




text \<open>§6.7 STRONG-INDUCTION INVARIANT pieces for \<open>E\<^sub>z\<close> (attempt G).

  The strong/size induction on \<open>Lng N\<close> carries the FULLRAMP invariant: for a
  gated \<open>N\<close> (interior row-1 ancestor structure) the WHOLE tail \<open>[j\<^sub>0, j\<^sub>1)\<close> is an
  exact \<open>+1\<close> row-0 ramp.  The corollaries below convert the invariant to / from
  the \<open>E\<^sub>z\<close> endpoint form and to the tree well-formedness clause, and supply the
  \<open>diag\<close> base.  All RedCondA-free (cite only diagonal entry facts and the GREEN
  @{thm [source] m_6_7_tree_wellformed_via_subramp}).\<close>

text \<open>DIAG base of fullramp: the diagonal row 0 increases by exactly 1 each step
  (\<open>entry (diagSeq a b) 0 j = a + j\<close>), so every step on \<open>[p, j\<^sub>1)\<close> is \<open>+1\<close>.\<close>

lemma fullramp_diag:
  fixes a b :: nat
  assumes ab: "a \<le> b"
    and xhi: "x < Lng (diagSeq a b) - 1"
  shows "entry (diagSeq a b) 0 (Suc x) = Suc (entry (diagSeq a b) 0 x)"
proof -
  let ?N = "diagSeq a b"
  have Lpos: "0 < Suc b - a" using ab by simp
  have sxlt: "Suc x < Suc b - a" using xhi Lpos by simp
  have xlt: "x < Suc b - a" using sxlt by simp
  have e_x: "entry ?N 0 x = a + x" by (rule entry_diagSeq[OF xlt])
  have e_sx: "entry ?N 0 (Suc x) = a + Suc x" by (rule entry_diagSeq[OF sxlt])
  show ?thesis using e_x e_sx by simp
qed


text \<open>From the FULLRAMP invariant (the exact \<open>+1\<close> step on the whole tail
  \<open>[j\<^sub>0, j\<^sub>1)\<close>) the \<open>E\<^sub>z\<close> endpoint slope-1 fact at any gated column \<open>z \<ge> j\<^sub>0\<close>
  follows by cumulating the step from \<open>z\<close> to \<open>j\<^sub>1\<close>.\<close>

lemma Ez_from_fullramp:
  fixes N :: pairseq
  assumes j0le: "parent N 1 (Lng N - 1) \<le> z"
    and zhi: "z < Lng N - 1"
    and ramp: "\<And>x. parent N 1 (Lng N - 1) \<le> x \<Longrightarrow> x < Lng N - 1
                 \<Longrightarrow> entry N 0 (Suc x) = Suc (entry N 0 x)"
  shows "entry N 0 (Lng N - 1) = entry N 0 z + ((Lng N - 1) - z)"
proof -
  let ?j1 = "Lng N - 1"
  \<comment> \<open>cumulate the \<open>+1\<close> step from base \<open>z\<close> up to any \<open>z + t \<le> j\<^sub>1\<close>\<close>
  have cum: "\<And>t. z + t \<le> ?j1 \<Longrightarrow> entry N 0 (z + t) = entry N 0 z + t"
  proof -
    fix t assume "z + t \<le> ?j1"
    thus "entry N 0 (z + t) = entry N 0 z + t"
    proof (induction t)
      case 0 show ?case by simp
    next
      case (Suc t)
      have le1: "z + t \<le> ?j1" using Suc.prems by simp
      have lt: "z + t < ?j1" using Suc.prems by simp
      have ge: "parent N 1 ?j1 \<le> z + t" using j0le by simp
      have st: "entry N 0 (Suc (z + t)) = Suc (entry N 0 (z + t))"
        by (rule ramp[OF ge lt])
      have ih: "entry N 0 (z + t) = entry N 0 z + t" using Suc.IH[OF le1] .
      show ?case using st ih by simp
    qed
  qed
  have zj1: "z \<le> ?j1" using zhi by simp
  have "z + (?j1 - z) \<le> ?j1" using zj1 by simp
  hence "entry N 0 (z + (?j1 - z)) = entry N 0 z + (?j1 - z)" using cum by simp
  moreover have "z + (?j1 - z) = ?j1" using zj1 by simp
  ultimately show ?thesis by simp
qed


text \<open>§6.7 fullramp: WIDTH-1 degenerate brick.  When the last block has width 1
  (\<open>parent N 1 (Lng N - 1) = Lng N - 2\<close>), the per-step range \<open>[j\<^sub>0, j\<^sub>1)\<close> is the
  single point \<open>x = Lng N - 2\<close> (forced by \<open>xlo\<close>/\<open>xhi\<close>), and the conclusion is
  literally the \<open>laststep\<close> hypothesis.  Purely finite-arith; cites nothing.\<close>

lemma fr_width1_step:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and j0eq: "parent N 1 (Lng N - 1) = Lng N - 2"
    and laststep: "entry N 0 (Lng N - 1) = Suc (entry N 0 (Lng N - 2))"
    and xlo: "parent N 1 (Lng N - 1) \<le> x"
    and xhi: "x < Lng N - 1"
  shows "entry N 0 (Suc x) = Suc (entry N 0 x)"
proof -
  have xj2: "x = Lng N - 2" using xlo xhi j0eq L by linarith
  have sxj1: "Suc x = Lng N - 1" using xj2 L by linarith
  show ?thesis using laststep xj2 sxj1 by simp
qed


text \<open>§6.7 fullramp: the BLOCK-REGION per-step ramp for the \<open>i\<^sub>1=1\<close> oper
  \<open>N = M[n]\<close>.  Every row-0 step \<open>x \<to> x+1\<close> with \<open>x\<close> in the blocks region
  \<open>[j\<^sub>0\<^sup>M, Lng N - 1)\<close> is exactly \<open>+1\<close>, given (a) the M-tail \<open>+1\<close> ramp on
  \<open>[j\<^sub>0\<^sup>M, Lng M - 1]\<close> (the absolute form \<open>entry M 0 (j\<^sub>0\<^sup>M+t)=entry M 0 j\<^sub>0\<^sup>M+t\<close>,
  i.e. \<open>fullramp(M)\<close>) and (b) the single \<open>laststep(M)\<close>.  A step is either
  interior to a block (a shifted \<open>M\<close>-step, \<open>+1\<close> by the ramp) or a block boundary
  (\<open>s = w-1\<close>, where the jump is \<open>entry M 0 j\<^sub>1\<^sup>M - entry M 0 (j\<^sub>1\<^sup>M-1) = +1\<close> by
  \<open>laststep(M)\<close>).  Cites only @{thm [source] oper_d1pos_entry0} and
  @{thm [source] oper_d1pos_LngM}; no spsy / sblk / RedCond / tail_affine.\<close>

lemma fr_block_step:
  fixes M :: pairseq
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and n0: "0 < n"
    and ramp: "\<And>t. t \<le> Lng M - 1 - parent M 1 (Lng M - 1)
                 \<Longrightarrow> entry M 0 (parent M 1 (Lng M - 1) + t)
                       = entry M 0 (parent M 1 (Lng M - 1)) + t"
    and laststep: "entry M 0 (Lng M - 1) = Suc (entry M 0 (Lng M - 2))"
    and xlo: "parent M 1 (Lng M - 1) \<le> x"
    and xhi: "x < Lng ((M::pairseq)[n]) - 1"
  shows "entry ((M::pairseq)[n]) 0 (Suc x) = Suc (entry ((M::pairseq)[n]) 0 x)"
proof -
  let ?j1 = "Lng M - 1"  let ?j0 = "parent M 1 ?j1"  let ?w = "?j1 - ?j0"
  let ?Mn = "(M::pairseq)[n]"
  let ?delta = "entry M 0 ?j1 - entry M 0 ?j0"
  have w0: "0 < ?w" using j0lt by linarith
  \<comment> \<open>\<open>delta = w\<close> from the M-tail ramp at offset \<open>w\<close>\<close>
  have e_j1: "entry M 0 ?j1 = entry M 0 ?j0 + ?w"
  proof -
    have "entry M 0 (?j0 + ?w) = entry M 0 ?j0 + ?w" using ramp[of ?w] by simp
    moreover have "?j0 + ?w = ?j1" using j0lt by simp
    ultimately show ?thesis by simp
  qed
  have dw: "?delta = ?w" using e_j1 by simp
  \<comment> \<open>length of \<open>N\<close>, hence \<open>j\<^sub>1\<^sup>N = j\<^sub>0 + n*w - 1\<close>\<close>
  have lenN: "Lng ?Mn = ?j0 + n * ?w"
    by (rule oper_d1pos_LngM[OF L notzero hp i1z j0lt])
  \<comment> \<open>block coordinates of \<open>x\<close>\<close>
  define d where "d = x - ?j0"
  have xd: "x = ?j0 + d" using d_def xlo by simp
  let ?q = "d div ?w"  let ?s = "d mod ?w"
  have sw: "?s < ?w" using w0 by simp
  have qsd: "?q * ?w + ?s = d"
    using div_mult_mod_eq[of d ?w] by (simp add: mult.commute)
  have xqs: "x = ?j0 + ?q * ?w + ?s" using xd qsd by simp
  \<comment> \<open>\<open>x < j\<^sub>0 + n*w - 1\<close> gives \<open>d < n*w\<close>, hence \<open>q < n\<close>\<close>
  have dlt: "d < n * ?w"
  proof -
    have "x < ?j0 + n * ?w - 1" using xhi lenN by simp
    thus ?thesis using xd by linarith
  qed
  have qn: "?q < n" using less_mult_imp_div_less[OF dlt] .
  \<comment> \<open>row-0 readback at \<open>x\<close>\<close>
  have e_x: "entry ?Mn 0 x = entry M 0 (?j0 + ?s) + ?q * ?delta"
    using oper_d1pos_entry0[OF L notzero hp i1z j0lt qn sw] xqs by simp
  show ?thesis
  proof (cases "Suc ?s = ?w")
    case False
    \<comment> \<open>INTERIOR step: same block \<open>q\<close>, offset \<open>s+1 < w\<close>\<close>
    have ss: "Suc ?s < ?w" using sw False by simp
    have sxqs: "Suc x = ?j0 + ?q * ?w + Suc ?s" using xqs by simp
    have e_sx: "entry ?Mn 0 (Suc x) = entry M 0 (?j0 + Suc ?s) + ?q * ?delta"
      using oper_d1pos_entry0[OF L notzero hp i1z j0lt qn ss] sxqs by simp
    \<comment> \<open>the M-side interior step is \<open>+1\<close> by the ramp at \<open>s\<close> and \<open>s+1\<close>\<close>
    have sle: "?s \<le> ?w" using sw by simp
    have ssle: "Suc ?s \<le> ?w" using ss by simp
    have eMs: "entry M 0 (?j0 + ?s) = entry M 0 ?j0 + ?s" using ramp[of ?s] sle by simp
    have eMss: "entry M 0 (?j0 + Suc ?s) = entry M 0 ?j0 + Suc ?s"
      using ramp[of "Suc ?s"] ssle by simp
    have stepM: "entry M 0 (?j0 + Suc ?s) = Suc (entry M 0 (?j0 + ?s))"
      using eMs eMss by simp
    show ?thesis using e_x e_sx stepM by simp
  next
    case True
    \<comment> \<open>BOUNDARY step: \<open>s = w-1\<close>, \<open>Suc x\<close> starts block \<open>q+1\<close> at offset 0\<close>
    have sw1: "?s = ?w - 1" using True by simp
    \<comment> \<open>\<open>x \<noteq> j\<^sub>1\<^sup>N\<close> forces \<open>q+1 < n\<close> (else \<open>x = j\<^sub>0 + n*w - 1 = j\<^sub>1\<^sup>N\<close>)\<close>
    have q1n: "Suc ?q < n"
    proof (rule ccontr)
      assume "\<not> Suc ?q < n"
      hence qn1: "Suc ?q = n" using qn by linarith
      \<comment> \<open>abstract \<open>w\<close>, \<open>q\<close>, \<open>j\<^sub>0\<close> into opaque nats (CLAUDE.md: avoid re-expanding \<open>?w\<close>)\<close>
      define W where "W = ?w"
      define Q where "Q = ?q"
      define J where "J = ?j0"
      have W0: "0 < W" using w0 W_def by simp
      have xJ: "x = J + (Q * W + (W - 1))" using xqs sw1 J_def W_def Q_def by simp
      have lenNJ: "Lng ?Mn = J + n * W" using lenN J_def W_def by simp
      have nQ: "n = Suc Q" using qn1 Q_def by simp
      have step: "Q * W + (W - 1) = n * W - 1"
      proof -
        have "Q * W + (W - 1) = Q * W + W - 1" using W0 by simp
        also have "\<dots> = Suc Q * W - 1" by simp
        also have "\<dots> = n * W - 1" using nQ by simp
        finally show ?thesis .
      qed
      have nw1: "1 \<le> n * W"
      proof -
        have "W \<le> n * W" using nQ by simp
        thus ?thesis using W0 by linarith
      qed
      have "x = J + (n * W - 1)" using xJ step by simp
      hence "x = J + n * W - 1" using nw1 by simp
      hence "x = Lng ?Mn - 1" using lenNJ by simp
      thus False using xhi by simp
    qed
    have sxqs: "Suc x = ?j0 + Suc ?q * ?w + 0"
    proof -
      have "Suc x = ?j0 + ?q * ?w + Suc ?s" using xqs by simp
      also have "\<dots> = ?j0 + ?q * ?w + ?w" using True by simp
      also have "\<dots> = ?j0 + Suc ?q * ?w + 0" by simp
      finally show ?thesis .
    qed
    have e_sx: "entry ?Mn 0 (Suc x) = entry M 0 (?j0 + 0) + Suc ?q * ?delta"
      using oper_d1pos_entry0[OF L notzero hp i1z j0lt q1n w0] sxqs by simp
    \<comment> \<open>abstract \<open>w\<close>, \<open>q\<close>, \<open>entry M 0 j\<^sub>0\<close> into opaque nats so the decision procedure
       never re-expands the \<open>?w = Lng M - Suc (parent ..)\<close> atom (CLAUDE.md gotcha)\<close>
    define W where "W = ?w"
    define Q where "Q = ?q"
    define E where "E = entry M 0 ?j0"
    have W0: "0 < W" using w0 W_def by simp
    \<comment> \<open>read off both sides via \<open>delta = w\<close> and \<open>laststep(M)\<close>\<close>
    have eMs: "entry M 0 (?j0 + ?s) = E + (W - 1)"
      using ramp[of ?s] sw1 sw E_def W_def by simp
    have lhs: "entry ?Mn 0 (Suc x) = E + Suc Q * W"
      using e_sx dw E_def W_def Q_def by simp
    have rhs: "entry ?Mn 0 x = E + (W - 1) + Q * W"
      using e_x eMs dw E_def W_def Q_def by simp
    have arith: "E + Suc Q * W = Suc (E + (W - 1) + Q * W)"
      using W0 by simp
    show ?thesis using lhs rhs arith by simp
  qed
qed


text \<open>§6.7 fullramp: the PREFIX-REGION per-step ramp for the \<open>i\<^sub>1=1\<close> oper
  \<open>N = M[n]\<close>.  In the prefix region \<open>[?, j\<^sub>0\<^sup>M)\<close> the \<open>N\<close>-entries read straight off
  \<open>M\<close> (the prefix \<open>take j\<^sub>0\<^sup>M M\<close> is verbatim, @{thm [source] oper_d1pos_nth_prefix}),
  and the boundary node \<open>j\<^sub>0\<^sup>M\<close> is block 0 offset 0 (\<open>entry N 0 j\<^sub>0\<^sup>M = entry M 0 j\<^sub>0\<^sup>M\<close>,
  @{thm [source] oper_d1pos_entry0}).  Hence every step \<open>x \<to> x+1\<close> with
  \<open>x < j\<^sub>0\<^sup>M\<close> equals the corresponding \<open>M\<close>-row-0 step, so the conclusion follows
  from the supplied \<open>M\<close>-prefix \<open>+1\<close> step \<open>preM\<close>.  Cites only
  @{thm [source] oper_d1pos_nth_prefix} and @{thm [source] oper_d1pos_entry0}; no
  spsy / sblk / RedCond / tail_affine.\<close>

lemma fr_prefix_step:
  fixes M :: pairseq
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and n0: "0 < n"
    and xlt: "x < parent M 1 (Lng M - 1)"
    and preM: "entry M 0 (Suc x) = Suc (entry M 0 x)"
  shows "entry ((M::pairseq)[n]) 0 (Suc x) = Suc (entry ((M::pairseq)[n]) 0 x)"
proof -
  let ?j1 = "Lng M - 1"  let ?j0 = "parent M 1 ?j1"  let ?w = "?j1 - ?j0"
  let ?Mn = "(M::pairseq)[n]"
  have w0: "0 < ?w" using j0lt by linarith
  \<comment> \<open>row-0 of \<open>N\<close> at \<open>x\<close> equals row-0 of \<open>M\<close> (prefix verbatim)\<close>
  have e_x: "entry ?Mn 0 x = entry M 0 x"
    using oper_d1pos_nth_prefix[OF L notzero hp i1z xlt, of n] by (simp add: entry_def)
  show ?thesis
  proof (cases "Suc x < ?j0")
    case True
    \<comment> \<open>both \<open>x\<close> and \<open>x+1\<close> in the verbatim prefix\<close>
    have e_sx: "entry ?Mn 0 (Suc x) = entry M 0 (Suc x)"
      using oper_d1pos_nth_prefix[OF L notzero hp i1z True, of n] by (simp add: entry_def)
    show ?thesis using e_x e_sx preM by simp
  next
    case False
    \<comment> \<open>boundary: \<open>x = j\<^sub>0 - 1\<close>, \<open>Suc x = j\<^sub>0\<close> is block 0 offset 0\<close>
    have sxj0: "Suc x = ?j0" using xlt False by simp
    have rb0: "entry ?Mn 0 (?j0 + 0 * ?w + 0)
                 = entry M 0 (?j0 + 0) + 0 * (entry M 0 ?j1 - entry M 0 ?j0)"
      by (rule oper_d1pos_entry0[OF L notzero hp i1z j0lt n0 w0])
    have e_sx': "entry ?Mn 0 ?j0 = entry M 0 ?j0" using rb0 by simp
    have e_sx: "entry ?Mn 0 (Suc x) = entry M 0 ?j0" using e_sx' sxj0 by simp
    have "entry M 0 ?j0 = entry M 0 (Suc x)" using sxj0 by simp
    thus ?thesis using e_x e_sx preM by simp
  qed
qed


text \<open>§6.7 fullramp: the OPER per-step ramp for \<open>N = M[n]\<close>, ASSEMBLED from the
  three region bricks.  Every step \<open>x \<to> x+1\<close> with \<open>j\<^sub>0\<^sup>N \<le> x < j\<^sub>1\<^sup>N\<close> is split
  on \<open>x < j\<^sub>0\<^sup>M\<close> (prefix, @{thm [source] fr_prefix_step}, fed the supplied
  \<open>M\<close>-prefix step) vs \<open>x \<ge> j\<^sub>0\<^sup>M\<close> (block region, @{thm [source] fr_block_step},
  fed the \<open>M\<close>-tail ramp \<open>ramp\<close> and \<open>laststep(M)\<close>).  Cites only the two GREEN
  region bricks; no spsy / sblk / RedCond / tail_affine.  The two supplied
  premises \<open>ramp\<close> (the \<open>M\<close>-tail \<open>+1\<close> ramp, i.e. fullramp of \<open>M\<close>) and
  \<open>preM\<close> (the \<open>M\<close>-prefix \<open>+1\<close> step on \<open>[j\<^sub>0\<^sup>N, j\<^sub>0\<^sup>M)\<close>) are the IH content plus the
  named prefix-ramp residual.\<close>

lemma fr_oper_step:
  fixes M :: pairseq
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and n0: "0 < n"
    and ramp: "\<And>t. t \<le> Lng M - 1 - parent M 1 (Lng M - 1)
                 \<Longrightarrow> entry M 0 (parent M 1 (Lng M - 1) + t)
                       = entry M 0 (parent M 1 (Lng M - 1)) + t"
    and laststep: "entry M 0 (Lng M - 1) = Suc (entry M 0 (Lng M - 2))"
    and preM: "\<And>y. parent ((M::pairseq)[n]) 1 (Lng ((M::pairseq)[n]) - 1) \<le> y
                 \<Longrightarrow> y < parent M 1 (Lng M - 1)
                 \<Longrightarrow> entry M 0 (Suc y) = Suc (entry M 0 y)"
    and xlo: "parent ((M::pairseq)[n]) 1 (Lng ((M::pairseq)[n]) - 1) \<le> x"
    and xhi: "x < Lng ((M::pairseq)[n]) - 1"
  shows "entry ((M::pairseq)[n]) 0 (Suc x) = Suc (entry ((M::pairseq)[n]) 0 x)"
proof (cases "x < parent M 1 (Lng M - 1)")
  case True
  have stepM: "entry M 0 (Suc x) = Suc (entry M 0 x)" using preM[OF xlo True] .
  show ?thesis
    by (rule fr_prefix_step[OF L notzero hp i1z j0lt n0 True stepM])
next
  case False
  have xge: "parent M 1 (Lng M - 1) \<le> x" using False by simp
  show ?thesis
    by (rule fr_block_step[OF L notzero hp i1z j0lt n0 ramp laststep xge xhi])
qed


text \<open>§6.7 fullramp: the GLOBAL per-step ramp of \<open>N = M[n]\<close> on \<open>[0, j\<^sub>1\<^sup>N)\<close>,
  assembled from the GLOBAL per-step ramp of \<open>M\<close> on \<open>[0, j\<^sub>1\<^sup>M)\<close> (the strong
  induction hypothesis) and \<open>laststep(M)\<close>.  A step \<open>x \<to> x+1\<close> with \<open>x < j\<^sub>0\<^sup>M\<close>
  reads off the verbatim prefix (@{thm [source] fr_prefix_step}, fed the
  \<open>M\<close>-global step at \<open>x\<close>), and a step with \<open>x \<ge> j\<^sub>0\<^sup>M\<close> is a block-region step
  (@{thm [source] fr_block_step}, fed the \<open>M\<close>-tail ramp derived by cumulating
  the \<open>M\<close>-global step on \<open>[j\<^sub>0\<^sup>M, j\<^sub>1\<^sup>M]\<close>).  Cites only the two GREEN region bricks;
  no spsy / sblk / RedCond / tail_affine.  This is the genuine TILING oper step
  of the global-ramp strong induction.\<close>

lemma fr_global_oper:
  fixes M :: pairseq
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and n0: "0 < n"
    and Mglob: "\<And>y. y < Lng M - 1 \<Longrightarrow> entry M 0 (Suc y) = Suc (entry M 0 y)"
    and laststep: "entry M 0 (Lng M - 1) = Suc (entry M 0 (Lng M - 2))"
    and xhi: "x < Lng ((M::pairseq)[n]) - 1"
  shows "entry ((M::pairseq)[n]) 0 (Suc x) = Suc (entry ((M::pairseq)[n]) 0 x)"
proof -
  let ?j1 = "Lng M - 1"  let ?j0 = "parent M 1 ?j1"
  \<comment> \<open>cumulate the M-global step to the absolute tail ramp on \<open>[j\<^sub>0, j\<^sub>1]\<close>\<close>
  have ramp: "\<And>t. t \<le> ?j1 - ?j0 \<Longrightarrow> entry M 0 (?j0 + t) = entry M 0 ?j0 + t"
  proof -
    fix t assume "t \<le> ?j1 - ?j0"
    thus "entry M 0 (?j0 + t) = entry M 0 ?j0 + t"
    proof (induction t)
      case 0 show ?case by simp
    next
      case (Suc t)
      have lt: "?j0 + t < ?j1" using Suc.prems j0lt by linarith
      have step: "entry M 0 (Suc (?j0 + t)) = Suc (entry M 0 (?j0 + t))"
        by (rule Mglob[OF lt])
      have ih: "entry M 0 (?j0 + t) = entry M 0 ?j0 + t" using Suc.IH Suc.prems by simp
      show ?case using step ih by simp
    qed
  qed
  show ?thesis
  proof (cases "x < ?j0")
    case True
    have stepM: "entry M 0 (Suc x) = Suc (entry M 0 x)"
      using Mglob[of x] True j0lt by simp
    show ?thesis
      by (rule fr_prefix_step[OF L notzero hp i1z j0lt n0 True stepM])
  next
    case False
    have xge: "?j0 \<le> x" using False by simp
    show ?thesis
      by (rule fr_block_step[OF L notzero hp i1z j0lt n0 ramp laststep xge xhi])
  qed
qed

text \<open>(fr bricks above land the DIAG-free tiling oper step of the global fullramp
  strong induction; the non-tiling \<open>M[n] = Pred M\<close> sub-case is the named residual.)\<close>


text \<open>§6.7 FULLRAMP, width-1 degenerate base.  When the last block has WIDTH 1,
  i.e. \<open>parent N 1 (Lng N - 1) = Lng N - 2\<close>, the range \<open>[j\<^sub>0, j\<^sub>1)\<close> is the singleton
  \<open>{Lng N - 2}\<close>, so the gated \<open>x\<close> is forced to \<open>x = Lng N - 2\<close> and the per-step ramp
  conclusion is literally the \<open>laststep\<close> premise.  Cites nothing.\<close>

lemma fr_wid1_trivial:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and laststep: "entry N 0 (Lng N - 1) = Suc (entry N 0 (Lng N - 2))"
    and wid1: "parent N 1 (Lng N - 1) = Lng N - 2"
    and xlo: "parent N 1 (Lng N - 1) \<le> x"
    and xhi: "x < Lng N - 1"
  shows "entry N 0 (Suc x) = Suc (entry N 0 x)"
proof -
  have xge: "Lng N - 2 \<le> x" using xlo wid1 by simp
  have xlt: "x < Lng N - 1" using xhi .
  have xeq: "x = Lng N - 2" using xge xlt L by linarith
  have sxeq: "Suc x = Lng N - 1" using xeq L by simp
  show ?thesis using laststep xeq sxeq by simp
qed


text \<open>§6.7 FULLRAMP from the endpoint at \<open>j\<^sub>0\<close>.  For a gated \<open>N \<in> ST\<^sub>PS\<close>, GIVEN the
  single ENDPOINT slope-1 fact \<open>E\<^sub>{j\<^sub>0}\<close> (\<open>entry N 0 j\<^sub>1 = entry N 0 j\<^sub>0 + (j\<^sub>1 - j\<^sub>0)\<close>),
  the row-0 step \<open>\<le> +1\<close> cap (@{thm [source] subramp_from_Ep}) forces EVERY step on
  \<open>[j\<^sub>0, j\<^sub>1)\<close> to be exactly \<open>+1\<close> --- the per-step fullramp conclusion.  This is the
  final glue of the spsy cascade: it converts the bridge output (Ez endpoint at
  \<open>j\<^sub>0\<close> for \<open>N\<close>) into the @{thm [source] Ez_from_fullramp} /
  @{thm [source] tree_from_fullramp} input shape.  Cites only the already-GREEN
  @{thm [source] subramp_from_Ep}; no spsy / sblk / RedCond / oper-tiling /
  tail_affine.\<close>

lemma fr_ramp_from_Ep_at_j0:
  fixes N :: pairseq
  assumes N: "N \<in> ST_PS"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and Ep: "entry N 0 (Lng N - 1)
               = entry N 0 (parent N 1 (Lng N - 1))
                 + ((Lng N - 1) - parent N 1 (Lng N - 1))"
    and xlo: "parent N 1 (Lng N - 1) \<le> x"
    and xhi: "x < Lng N - 1"
  shows "entry N 0 (Suc x) = Suc (entry N 0 x)"
  by (rule subramp_from_Ep[OF N j0lt Ep xlo xhi])


text \<open>§6.7 GS, STEP B (assembly), Ep-form.  The spsy TREE clause from JUST the
  ENDPOINT slope-1 fact \<open>E\<^sub>{j\<^sub>0}\<close> of \<open>N\<close> (no full \<open>gstrict_full\<close> needed): the
  per-step tail ramp on \<open>[j\<^sub>0, j\<^sub>1)\<close> follows from \<open>E\<^sub>{j\<^sub>0}\<close> by the row-0 \<open>\<le> +1\<close>
  cap (@{thm [source] fr_ramp_from_Ep_at_j0}, i.e. @{thm [source] subramp_from_Ep}),
  then feed @{thm [source] tree_from_fullramp}.  This is the weakest-hypothesis
  assembly: it needs only \<open>N \<in> ST\<^sub>PS\<close> and \<open>E\<^sub>{j\<^sub>0}\<close>.  Cites only already-GREEN
  bricks; no spsy / sblk / RedCond / tail_affine.\<close>

lemma gs_tree_from_Ep:
  fixes N :: pairseq
  assumes N: "N \<in> ST_PS"
    and L: "1 < Lng N"
    and hp1: "hasParent N 1 (Lng N - 1)"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and zlo: "parent N 1 (Lng N - 1) < z"
    and zhi: "z < Lng N - 1"
    and hpz: "hasParent N 1 z"
    and pge: "parent N 1 z \<ge> parent N 1 (Lng N - 1)"
    and pgt: "parent N 1 z > parent N 1 (Lng N - 1)"
    and Ep: "entry N 0 (Lng N - 1)
               = entry N 0 (parent N 1 (Lng N - 1))
                 + ((Lng N - 1) - parent N 1 (Lng N - 1))"
  shows "hasParent N 1 (parent N 1 z)
         \<and> parent N 1 (parent N 1 z) \<ge> parent N 1 (Lng N - 1)"
proof -
  have ramp: "\<And>x. parent N 1 (Lng N - 1) \<le> x \<Longrightarrow> x < Lng N - 1
                 \<Longrightarrow> entry N 0 (Suc x) = Suc (entry N 0 x)"
    by (rule fr_ramp_from_Ep_at_j0[OF N j0lt Ep])
  show ?thesis
    by (rule tree_from_fullramp[OF L hp1 j0lt zlo zhi hpz pge pgt ramp])
qed


text \<open>§6.7 GS, STEP A DIAG case.  Row-0 of \<open>diagSeq a b\<close> is the \<open>+1\<close> ramp at
  EVERY step, i.e. \<open>gstrict_full(diagSeq a b)\<close>.  Direct from
  @{thm [source] fullramp_diag}; cites nothing else.\<close>

lemma gs_diag_gstrict:
  fixes a b :: nat
  assumes ab: "a \<le> b"
    and y: "y < Lng (diagSeq a b) - 1"
  shows "entry (diagSeq a b) 0 (Suc y) = Suc (entry (diagSeq a b) 0 y)"
  by (rule fullramp_diag[OF ab y])


text \<open>§6.7 GS, STEP A OPER assembly.  GIVEN the global ramp \<open>gstrict_full(M)\<close> and
  that \<open>M\<close> is gated (the five gate facts), \<open>gstrict_full(M[n])\<close> follows by applying
  the GREEN per-step tiling brick @{thm [source] fr_global_oper} at each \<open>x\<close>.  The
  \<open>laststep(M)\<close> premise of @{thm [source] fr_global_oper} is the \<open>y = Lng M - 2\<close>
  instance of \<open>gstrict_full(M)\<close> (\<open>1 < Lng M\<close>).  Cites only the already-GREEN
  @{thm [source] fr_global_oper}; no spsy / sblk / RedCond / tail_affine.  This
  isolates the crux to obtaining \<open>gstrict_full(M)\<close> from \<open>has_gz(M[n])\<close>.\<close>

lemma gs_oper_gstrict_from_M:
  fixes M :: pairseq
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and n0: "0 < n"
    and Mglob: "\<And>y. y < Lng M - 1 \<Longrightarrow> entry M 0 (Suc y) = Suc (entry M 0 y)"
    and xhi: "x < Lng ((M::pairseq)[n]) - 1"
  shows "entry ((M::pairseq)[n]) 0 (Suc x) = Suc (entry ((M::pairseq)[n]) 0 x)"
proof -
  have lastlt: "Lng M - 2 < Lng M - 1" using L by linarith
  have laststep: "entry M 0 (Lng M - 1) = Suc (entry M 0 (Lng M - 2))"
  proof -
    have "entry M 0 (Suc (Lng M - 2)) = Suc (entry M 0 (Lng M - 2))"
      by (rule Mglob[OF lastlt])
    moreover have "Suc (Lng M - 2) = Lng M - 1" using L by linarith
    ultimately show ?thesis by simp
  qed
  show ?thesis
    by (rule fr_global_oper[OF L notzero hp i1z j0lt n0 Mglob laststep xhi])
qed


text \<open>§6.7 GS, STEP A OPER reduction (wiring).  For the \<open>ST\<^sub>PS.induct\<close> oper case
  \<open>N = M[n]\<close> this PACKAGES the full reduction of \<open>gstrict_full(M[n])\<close> to its two
  genuine inputs: (i) the IH \<open>P(M)\<close> --- \<open>has_gz(M) \<Longrightarrow> gstrict_full(M)\<close> --- as
  handed by @{thm [source] ST_PS.induct}, and (ii) the ONE residual BACKWARD
  parent-reflection \<open>refl\<close> --- \<open>has_gz(M[n]) \<Longrightarrow> has_gz(M)\<close> --- together with the
  five gate facts of \<open>M\<close> (which @{text "F3"} supplies from \<open>has_gz(M[n])\<close>).
  Under \<open>has_gz(M[n])\<close>: fire \<open>refl\<close> to get \<open>has_gz(M)\<close>, fire the IH to get
  \<open>gstrict_full(M)\<close>, then tile via @{thm [source] gs_oper_gstrict_from_M}.  Cites
  only the GREEN @{thm [source] gs_oper_gstrict_from_M}; no spsy / sblk / RedCond
  / tail_affine.  This is the exact green integration point of the crux: the SOLE
  remaining open input is \<open>refl\<close> (equivalently fact @{text "F2"}).\<close>

lemma gs_oper_gstrict_reduction:
  fixes M :: pairseq
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and n0: "0 < n"
    and IH: "(\<exists>z. parent M 1 (Lng M - 1) < z \<and> z < Lng M - 1
                  \<and> hasParent M 1 z \<and> parent M 1 z > parent M 1 (Lng M - 1))
             \<Longrightarrow> (\<And>y. y < Lng M - 1 \<Longrightarrow> entry M 0 (Suc y) = Suc (entry M 0 y))"
    and refl: "(\<exists>z. parent ((M::pairseq)[n]) 1 (Lng ((M::pairseq)[n]) - 1) < z
                    \<and> z < Lng ((M::pairseq)[n]) - 1 \<and> hasParent ((M::pairseq)[n]) 1 z
                    \<and> parent ((M::pairseq)[n]) 1 z
                        > parent ((M::pairseq)[n]) 1 (Lng ((M::pairseq)[n]) - 1))
               \<Longrightarrow> (\<exists>z. parent M 1 (Lng M - 1) < z \<and> z < Lng M - 1
                        \<and> hasParent M 1 z \<and> parent M 1 z > parent M 1 (Lng M - 1))"
    and gz: "\<exists>z. parent ((M::pairseq)[n]) 1 (Lng ((M::pairseq)[n]) - 1) < z
                  \<and> z < Lng ((M::pairseq)[n]) - 1 \<and> hasParent ((M::pairseq)[n]) 1 z
                  \<and> parent ((M::pairseq)[n]) 1 z
                      > parent ((M::pairseq)[n]) 1 (Lng ((M::pairseq)[n]) - 1)"
    and xhi: "x < Lng ((M::pairseq)[n]) - 1"
  shows "entry ((M::pairseq)[n]) 0 (Suc x) = Suc (entry ((M::pairseq)[n]) 0 x)"
proof -
  have gzM: "\<exists>z. parent M 1 (Lng M - 1) < z \<and> z < Lng M - 1
                  \<and> hasParent M 1 z \<and> parent M 1 z > parent M 1 (Lng M - 1)"
    by (rule refl[OF gz])
  have Mglob: "\<And>y. y < Lng M - 1 \<Longrightarrow> entry M 0 (Suc y) = Suc (entry M 0 y)"
    by (rule IH[OF gzM])
  show ?thesis
    by (rule gs_oper_gstrict_from_M[OF L notzero hp i1z j0lt n0 Mglob xhi])
qed



text \<open>§6.7 F2 brick: \<open>gstrict_full(M[n])\<close> from \<open>M \<in> ST\<^sub>PS\<close>, the five gate facts
  of \<open>M\<close>, and the GLOBAL endpoint slope-1 \<open>D(M)\<close> at base 0.  \<open>D(M)\<close> upgrades to
  the full per-step ramp \<open>gstrict_full(M)\<close> via @{thm [source] f2_gstrict_from_D}
  (which needs \<open>M \<in> ST\<^sub>PS\<close>), then the GREEN tiling brick
  @{thm [source] gs_oper_gstrict_from_M} delivers \<open>gstrict_full(M[n])\<close>.  Cites
  only the GREEN @{thm [source] f2_gstrict_from_D},
  @{thm [source] gs_oper_gstrict_from_M}; no spsy / sblk / RedCond / tail_affine.
  This is the reduction of the oper-case goal to the SINGLE input \<open>D(M)\<close>.\<close>

lemma f2_gstrict_oper_from_D_M:
  fixes M :: pairseq
  assumes MST: "M \<in> ST_PS"
    and L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and n0: "0 < n"
    and DM: "entry M 0 (Lng M - 1) = entry M 0 0 + (Lng M - 1)"
    and xhi: "x < Lng ((M::pairseq)[n]) - 1"
  shows "entry ((M::pairseq)[n]) 0 (Suc x) = Suc (entry ((M::pairseq)[n]) 0 x)"
proof -
  have Mglob: "\<And>y. y < Lng M - 1 \<Longrightarrow> entry M 0 (Suc y) = Suc (entry M 0 y)"
    by (rule f2_gstrict_from_D[OF MST L DM])
  show ?thesis
    by (rule gs_oper_gstrict_from_M[OF L notzero hp i1z j0lt n0 Mglob xhi])
qed



text \<open>§6.7 WITHIN-N crux groundwork.  \<open>cd_D_from_consec_strict\<close>: if row-0 is
  STRICTLY increasing at every consecutive step on \<open>[0, j\<^sub>1)\<close> then \<open>D(N)\<close> holds.
  The ST_PS per-step UPPER cap (@{thm [source] ST_row0_step_le}) together with the
  strict per-step LOWER bound forces every step to be EXACTLY \<open>+1\<close>, so the row-0
  endpoint sits the full width above the base.  Cites only
  @{thm [source] ST_row0_step_le}; no spsy / sblk / RedCond / tail_affine / oper.\<close>

lemma cd_D_from_consec_strict:
  fixes N :: pairseq
  assumes N: "N \<in> ST_PS"
    and L: "1 < Lng N"
    and strict: "\<And>x. x < Lng N - 1 \<Longrightarrow> entry N 0 x < entry N 0 (Suc x)"
  shows "entry N 0 (Lng N - 1) = entry N 0 0 + (Lng N - 1)"
proof -
  let ?j1 = "Lng N - 1"
  \<comment> \<open>every step on \<open>[0, j\<^sub>1)\<close> is exactly \<open>+1\<close>: strict lower, cap upper\<close>
  have step1: "\<And>x. x < ?j1 \<Longrightarrow> entry N 0 (Suc x) = Suc (entry N 0 x)"
  proof -
    fix x assume xj1: "x < ?j1"
    have sxL: "Suc x < Lng N" using xj1 by linarith
    have lo: "entry N 0 x < entry N 0 (Suc x)" by (rule strict[OF xj1])
    have hi: "entry N 0 (Suc x) \<le> Suc (entry N 0 x)" by (rule ST_row0_step_le[OF N sxL])
    show "entry N 0 (Suc x) = Suc (entry N 0 x)" using lo hi by linarith
  qed
  \<comment> \<open>accumulate the \<open>+1\<close> steps to the endpoint\<close>
  have cum: "\<And>s. s \<le> ?j1 \<Longrightarrow> entry N 0 s = entry N 0 0 + s"
  proof -
    fix s assume "s \<le> ?j1"
    thus "entry N 0 s = entry N 0 0 + s"
    proof (induction s)
      case 0 show ?case by simp
    next
      case (Suc s)
      have sj1: "s < ?j1" using Suc.prems by linarith
      have ih: "entry N 0 s = entry N 0 0 + s" using Suc.IH sj1 by linarith
      have "entry N 0 (Suc s) = Suc (entry N 0 s)" by (rule step1[OF sj1])
      thus ?case using ih by simp
    qed
  qed
  show ?thesis by (rule cum[OF le_refl])
qed


text \<open>§6.7 WITHIN-N crux groundwork.  \<open>cd_le0_first_step\<close>: the FIRST edge of any
  row-0 reach chain is strictly increasing at the immediate successor.  If
  \<open>le0 N x b\<close> with \<open>x < b\<close>, the chain \<open>x \<rightarrow>\<^sup>* b\<close> has a first \<open>nextrel0\<close> edge
  \<open>x \<rightarrow> x'\<close> (\<open>x < x'\<close>); its row-0 strict increase together with its valley clause
  (every interior column \<open>\<ge> entry N 0 x'\<close>) makes \<open>entry N 0 (Suc x) > entry N 0 x\<close>.
  EMPIRICALLY 52856/0.  Cites only @{thm [source] le0_def},
  @{thm [source] nextrel0_def}; no spsy / sblk / RedCond / tail_affine / oper.\<close>

lemma cd_le0_first_step:
  fixes N :: pairseq
  assumes le0: "le0 N x b"
    and xb: "x < b"
  shows "entry N 0 x < entry N 0 (Suc x)"
proof -
  have chain: "(nextrel0 N)\<^sup>*\<^sup>* x b" using le0 by (simp add: le0_def)
  have xneb: "x \<noteq> b" using xb by simp
  \<comment> \<open>peel the first edge \<open>x \<rightarrow> x'\<close> of the chain\<close>
  from converse_rtranclpE[OF chain] obtain x'
    where xx': "nextrel0 N x x'" and rest: "(nextrel0 N)\<^sup>*\<^sup>* x' b"
    using xneb by metis
  have xltx': "x < x'" using xx' by (simp add: nextrel0_def)
  have inc: "entry N 0 x < entry N 0 x'" using xx' by (simp add: nextrel0_def)
  have valley: "\<forall>j. x < j \<and> j < x' \<longrightarrow> entry N 0 j \<ge> entry N 0 x'"
    using xx' by (simp add: nextrel0_def)
  show ?thesis
  proof (cases "Suc x = x'")
    case True
    show ?thesis using inc True by simp
  next
    case False
    have "x < Suc x" by simp
    moreover have "Suc x < x'" using xltx' False by linarith
    ultimately have "entry N 0 (Suc x) \<ge> entry N 0 x'" using valley by blast
    thus ?thesis using inc by linarith
  qed
qed


text \<open>§6.7 WITHIN-N crux groundwork.  \<open>cd_D_from_reachend\<close>: \<open>D(N)\<close> from the
  \<open>reachend\<close> reachability hypothesis --- EVERY column \<open>x < j\<^sub>1\<close> reaches the row-0
  endpoint \<open>j\<^sub>1\<close> (\<open>le0 N x (Lng N-1)\<close>).  Each \<open>le0 N x j\<^sub>1\<close> gives, by
  @{thm [source] cd_le0_first_step}, the consecutive strict increase
  \<open>entry N 0 x < entry N 0 (Suc x)\<close>; @{thm [source] cd_D_from_consec_strict} then
  upgrades (under the ST_PS \<open>\<le> +1\<close> cap) to the full-width endpoint \<open>D(N)\<close>.  Cites
  only @{thm [source] cd_le0_first_step}, @{thm [source] cd_D_from_consec_strict};
  no spsy / sblk / RedCond / tail_affine / oper.\<close>

lemma cd_D_from_reachend:
  fixes N :: pairseq
  assumes N: "N \<in> ST_PS"
    and L: "1 < Lng N"
    and reach: "\<And>x. x < Lng N - 1 \<Longrightarrow> le0 N x (Lng N - 1)"
  shows "entry N 0 (Lng N - 1) = entry N 0 0 + (Lng N - 1)"
proof (rule cd_D_from_consec_strict[OF N L])
  fix x assume xj1: "x < Lng N - 1"
  have "le0 N x (Lng N - 1)" by (rule reach[OF xj1])
  thus "entry N 0 x < entry N 0 (Suc x)" by (rule cd_le0_first_step[OF _ xj1])
qed


text \<open>§6.7 WITHIN-N crux, OUTPUT shape \<open>D(N)\<close>, reduced to the SINGLE
  reachability input \<open>reachend\<close>.  \<open>cd_oper_gstrict_via_reachend\<close> packages the crux
  @{text m_6_7_oper_gstrict} so that its conclusion \<open>D(N)\<close> follows GREEN from the
  lone hypothesis \<open>reachend\<close> (every column \<open>x < j\<^sub>1\<close> reaches the row-0 endpoint
  \<open>j\<^sub>1\<close> in row 0).  EMPIRICALLY \<open>has_gz(N) \<Longrightarrow> reachend\<close> holds 222/0 on the broad
  ST_PS closure; \<open>reachend\<close> is thus the precise scalar carrier of the crux.  Cites
  only @{thm [source] cd_D_from_reachend}; no spsy / sblk / RedCond / tail_affine /
  oper.\<close>

lemma cd_oper_gstrict_via_reachend:
  fixes N :: pairseq
  assumes N: "N \<in> ST_PS"
    and L: "1 < Lng N"
    and hp1: "hasParent N 1 (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and gz: "\<exists>z. parent N 1 (Lng N - 1) < z \<and> z < Lng N - 1
                  \<and> hasParent N 1 z \<and> parent N 1 z > parent N 1 (Lng N - 1)"
    and reachend: "\<And>x. x < Lng N - 1 \<Longrightarrow> le0 N x (Lng N - 1)"
  shows "entry N 0 (Lng N - 1) = entry N 0 0 + (Lng N - 1)"
  by (rule cd_D_from_reachend[OF N L reachend])


text \<open>§6.7 WITHIN-N crux, TREE-clause output, reduced to the SINGLE reachability
  input \<open>reachend\<close>.  \<open>cd_tree_via_reachend\<close>: from \<open>reachend\<close> the crux first yields
  \<open>D(N)\<close> (@{thm [source] cd_D_from_reachend}); @{thm [source] f2_gstrict_from_D}
  turns \<open>D(N)\<close> into the global row-0 \<open>+1\<close> ramp \<open>gstrict_full(N)\<close>; and
  @{thm [source] gs_tree_from_gstrict} converts that into the §6.7 tree clause
  (@{text m_6_7_tree_via_gstrict}).  Cites only the already-GREEN
  @{thm [source] cd_D_from_reachend}, @{thm [source] f2_gstrict_from_D},
  @{thm [source] gs_tree_from_gstrict}; no spsy / sblk / RedCond / tail_affine /
  oper.\<close>

lemma cd_tree_via_reachend:
  fixes N :: pairseq
  assumes N: "N \<in> ST_PS"
    and L: "1 < Lng N"
    and hp1: "hasParent N 1 (Lng N - 1)"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and zlo: "parent N 1 (Lng N - 1) < z"
    and zhi: "z < Lng N - 1"
    and hpz: "hasParent N 1 z"
    and pge: "parent N 1 z \<ge> parent N 1 (Lng N - 1)"
    and pgt: "parent N 1 z > parent N 1 (Lng N - 1)"
    and reachend: "\<And>x. x < Lng N - 1 \<Longrightarrow> le0 N x (Lng N - 1)"
  shows "hasParent N 1 (parent N 1 z)
         \<and> parent N 1 (parent N 1 z) \<ge> parent N 1 (Lng N - 1)"
proof -
  have D: "entry N 0 (Lng N - 1) = entry N 0 0 + (Lng N - 1)"
    by (rule cd_D_from_reachend[OF N L reachend])
  have gstrict: "\<And>y. y < Lng N - 1 \<Longrightarrow> entry N 0 (Suc y) = Suc (entry N 0 y)"
    by (rule f2_gstrict_from_D[OF N L D])
  show ?thesis
    by (rule gs_tree_from_gstrict[OF L hp1 j0lt zlo zhi hpz pge pgt gstrict])
qed


text \<open>§6.7 CD reduction brick 1 (GREEN, within-N row-0 chaining).  The scalar
  crux \<open>D(N)\<close> (row-0 endpoint at base 0 sits at the full width:
  \<open>entry N 0 j\<^sub>1 = entry N 0 0 + j\<^sub>1\<close>) follows from a SINGLE clean within-N
  hypothesis: the row-0 sequence is STRICTLY consecutive-increasing on the whole
  span \<open>[0, j\<^sub>1)\<close> (\<open>entry N 0 x < entry N 0 (Suc x)\<close> for every \<open>x < j\<^sub>1\<close>).  Chain:
  @{thm [source] tailReach_from_row0_strict} (base \<open>p = 0\<close>) lifts the per-step
  strict increase to \<open>le0 N x j\<^sub>1\<close> for every \<open>x \<in> [0, j\<^sub>1)\<close> (the \<open>tailReach\<close>
  shape), then @{thm [source] Ep_from_le0_tail} (also \<open>p = 0\<close>) cumulates the
  resulting exact \<open>+1\<close> ramp to the endpoint equation \<open>D(N)\<close>.  EMPIRICALLY the
  strict-increase hypothesis holds 4248/0 on the broad gated ST_PS closure
  (\<open>has_gz(N)\<close>), exactly the population on which \<open>D(N)\<close> holds 423/0.  Cites only
  the already-GREEN @{thm [source] tailReach_from_row0_strict},
  @{thm [source] Ep_from_le0_tail}; no spsy / sblk / via_spsy / RedCond / oper /
  tail_affine.  This packages the entire \<open>D(N)\<close> crux as the lone within-N
  strict-monotonicity input.\<close>

lemma cd_D_from_strictmono:
  fixes N :: pairseq
  assumes N: "N \<in> ST_PS"
    and L: "1 < Lng N"
    and strict: "\<And>x. x < Lng N - 1 \<Longrightarrow> entry N 0 x < entry N 0 (Suc x)"
  shows "entry N 0 (Lng N - 1) = entry N 0 0 + (Lng N - 1)"
proof -
  let ?j1 = "Lng N - 1"
  have j1L: "?j1 < Lng N" using L by linarith
  have p0: "(0::nat) < ?j1" using L by linarith
  \<comment> \<open>per-step strict increase on \<open>[0, j\<^sub>1)\<close> in the base-0 (\<open>p \<le> y\<close>) shape\<close>
  have strict0: "\<And>y. (0::nat) \<le> y \<Longrightarrow> y < ?j1 \<Longrightarrow> entry N 0 y < entry N 0 (Suc y)"
    using strict by simp
  \<comment> \<open>every \<open>x \<in> [0, j\<^sub>1)\<close> row-0-reaches the endpoint (the \<open>tailReach\<close> hypothesis)\<close>
  have tailReach: "\<And>x. (0::nat) \<le> x \<Longrightarrow> x < ?j1 \<Longrightarrow> le0 N x ?j1"
  proof -
    fix x assume xlo: "(0::nat) \<le> x" and xhi: "x < ?j1"
    show "le0 N x ?j1"
      by (rule tailReach_from_row0_strict[OF j1L strict0 xlo xhi])
  qed
  \<comment> \<open>cumulate to the endpoint via the GREEN arithmetic glue at base 0\<close>
  have Ep0: "entry N 0 ?j1 = entry N 0 0 + (?j1 - 0)"
    by (rule Ep_from_le0_tail[OF N p0 tailReach])
  show ?thesis using Ep0 by simp
qed


text \<open>§6.7 FORWARD-CRUX brick (flat step from \<open>~D(M)\<close>).  \<open>fc_flat_step_from_notD\<close>:
  for \<open>M \<in> ST\<^sub>PS\<close> with \<open>1 < Lng M\<close>, if \<open>D(M)\<close> FAILS (row-0 endpoint is NOT the full
  width above the base) then there is a FLAT/non-increasing consecutive step
  \<open>entry M 0 (Suc c) \<le> entry M 0 c\<close> at some column \<open>c < Lng M - 1\<close>.  Contrapositive
  of @{thm [source] cd_D_from_consec_strict}: if EVERY consecutive step were
  strict then \<open>D(M)\<close> would hold.  Cites only
  @{thm [source] cd_D_from_consec_strict}; no spsy / sblk / RedCond / oper /
  tail_affine.\<close>

lemma fc_flat_step_from_notD:
  fixes M :: pairseq
  assumes MST: "M \<in> ST_PS"
    and L: "1 < Lng M"
    and notD: "entry M 0 (Lng M - 1) \<noteq> entry M 0 0 + (Lng M - 1)"
  shows "\<exists>c. c < Lng M - 1 \<and> entry M 0 (Suc c) \<le> entry M 0 c"
proof (rule ccontr)
  assume "\<not> (\<exists>c. c < Lng M - 1 \<and> entry M 0 (Suc c) \<le> entry M 0 c)"
  hence strict: "\<And>x. x < Lng M - 1 \<Longrightarrow> entry M 0 x < entry M 0 (Suc x)"
    by force
  have "entry M 0 (Lng M - 1) = entry M 0 0 + (Lng M - 1)"
    by (rule cd_D_from_consec_strict[OF MST L strict])
  thus False using notD by simp
qed


text \<open>§6.7 FORWARD-CRUX brick (contrapositive of D-propagation).
  \<open>fc_notD_M_from_notD_oper\<close>: for a GATED \<open>M \<in> ST\<^sub>PS\<close> and \<open>n \<ge> 1\<close>, if \<open>D(M[n])\<close>
  FAILS then \<open>D(M)\<close> FAILS.  This is the direct contrapositive of
  @{thm [source] fc_D_oper}: had \<open>D(M)\<close> held, \<open>D(M[n])\<close> would too.  Empirically
  \<open>gated(M) & ~D(M[n]) \<Longrightarrow> ~D(M)\<close> is 0-fail (red_model.py).  This is the FIRST
  step of the gated branch of the ST_PS.cases contrapositive (it transports the
  hypothesis \<open>~D(N)\<close>, \<open>N = M[n]\<close>, down to \<open>~D(M)\<close>, where the flat-step argument
  @{text fc_flat_no_gz} then applies).  Cites only the already-GREEN
  @{thm [source] fc_D_oper}; no spsy / sblk / RedCond / tail_affine.\<close>

lemma fc_notD_M_from_notD_oper:
  fixes M :: pairseq
  assumes MST: "M \<in> ST_PS"
    and L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and n1: "1 \<le> n"
    and notDN: "entry ((M::pairseq)[n]) 0 (Lng ((M::pairseq)[n]) - 1)
                  \<noteq> entry ((M::pairseq)[n]) 0 0 + (Lng ((M::pairseq)[n]) - 1)"
  shows "entry M 0 (Lng M - 1) \<noteq> entry M 0 0 + (Lng M - 1)"
proof
  assume DM: "entry M 0 (Lng M - 1) = entry M 0 0 + (Lng M - 1)"
  have "entry ((M::pairseq)[n]) 0 (Lng ((M::pairseq)[n]) - 1)
      = entry ((M::pairseq)[n]) 0 0 + (Lng ((M::pairseq)[n]) - 1)"
    by (rule fc_D_oper[OF MST L notzero hp i1z j0lt n1 DM])
  thus False using notDN by simp
qed


subsection \<open>(v) Residual discharge — \<open>diag_red\<close>, \<open>predRdegen\<close>, and the \<open>anch\<close> domain gap\<close>

text \<open>
  Three of the four named residuals carried by
  @{thm [source] m_6_7_standard_reduced_faithful} are LIGHT and are discharged
  here, leaving \<^emph>\<open>only\<close> the tiling \<open>shift\<close> case of \<open>Red\<close>-\<open>oper\<close>-commutativity.

  \<^enum> \<open>diag_red\<close>: a diagonal \<open>diagSeq u v\<close> (\<open>u \<le> v\<close>) is reduced.  Discharged by
    @{text bf_diagSeq_reduced} below, via the §6.6 keystone
    @{thm [source] m_6_6_reduced_iff_cond} (簡約 \<longleftrightarrow> (A)\<and>(B)) and the GREEN
    @{thm [source] kfwd_condAB_diagSeq} (the diagonal satisfies both \<open>RedCondA\<close>
    and \<open>RedCondB\<close>).
  \<^enum> \<open>predRdegen\<close>: when the \<open>oper\<close>-step degenerates on \<open>M\<close> (\<open>M[n] = Pred M\<close>) it
    also degenerates on \<open>Red M\<close> (\<open>(Red M)[n] = Pred (Red M)\<close>).  At every site
    where this is needed \<open>M\<close> is already \<^emph>\<open>reduced\<close> (\<open>M \<in> RT\<^sub>PS\<close>, i.e. \<open>Red M = M\<close>),
    where it is \<^emph>\<open>trivial\<close>: \<open>(Red M)[n] = M[n] = Pred M = Pred (Red M)\<close>.
    (Empirically, on a non-reduced \<open>M\<close> the bare \<open>predRdegen\<close> is FALSE — e.g.
    \<open>M = (0,0)(0,1)\<close>, \<open>Red M = (0,0)(1,1)\<close>, where \<open>(Red M)[2] \<noteq> Pred (Red M)\<close> —
    so it is discharged \<^emph>\<open>only\<close> at the reduced site, never globally.)
  \<^enum> \<open>anch\<close> (DOMAIN GAP, correction A4): the skeleton threaded
    \<open>M \<in> anchored_slice\<close> because it routed preservation through the
    \<open>anchored_slice\<close>-scoped @{thm [source] m_6_5_Red_oper}, whose anchor
    \<open>le0 M 0 (Lng M - 1) (\<equiv> \<not> multiT M)\<close> can FAIL for \<open>multiT\<close> standard forms.
    Empirically (red_model.py) \<open>Red\<close>-\<open>oper\<close>-commutativity holds for ALL
    reduced \<open>M\<close> including \<open>multiT\<close> ones, so \<open>anchored_slice\<close> is merely an
    under-approximation.  We DISSOLVE the gap by stating preservation directly
    on the reduced domain \<open>M \<in> RT\<^sub>PS\<close> (@{text bf_red_preserved_by_oper_ST}),
    proving the non-shift branch trivially (reduced \<open>predRdegen\<close>) and carrying
    \<^emph>\<open>only\<close> the \<open>ST\<^sub>PS\<close>-scoped \<open>shift\<close> case as the lone hypothesis.  No
    \<open>anchored_slice\<close> appears.
\<close>

text \<open>
  Residual 1 — \<open>diag_red\<close>: the diagonal \<open>diagSeq u v\<close> (\<open>u \<le> v\<close>) is reduced.
\<close>

lemma bf_diagSeq_reduced:
  assumes uv: "u \<le> v"
  shows "diagSeq u v \<in> RT_PS"
proof -
  have MT: "diagSeq u v \<in> T_PS"
    using uv by (simp add: T_PS_def diagSeq_def del: upt_Suc)
  have AB: "RedCondA (diagSeq u v) \<and> RedCondB (diagSeq u v)"
    by (rule kfwd_condAB_diagSeq[OF uv])
  show ?thesis
    using m_6_6_reduced_iff_cond[OF MT] AB by blast
qed

text \<open>
  Residual 2 — \<open>predRdegen\<close> at the reduced site is trivial.  Since \<open>Red M = M\<close>,
  the \<open>oper\<close>-step degeneracy of \<open>M\<close> transfers verbatim to \<open>Red M\<close>.
\<close>

lemma bf_predRdegen_reduced:
  assumes Mred: "M \<in> RT_PS"
    and opM: "(M::pairseq)[n] = Pred M"
  shows "(Red M)[n] = Pred (Red M)"
proof -
  have redM: "Red M = M" using Mred by (simp add: RT_PS_def)
  show ?thesis using opM redM by simp
qed

text \<open>
  The DOMAIN-GAP-FREE preservation step on the \<^emph>\<open>reduced\<close> domain.  For a reduced
  \<open>M\<close> (\<open>M \<in> RT\<^sub>PS\<close>) and \<open>n \<ge> 1\<close> with \<open>M[n] \<in> T\<^sub>PS\<close>, \<open>M[n]\<close> is again reduced —
  conditional ONLY on the \<open>shift\<close> case of \<open>Red\<close>-\<open>oper\<close>-commutativity on the
  given (reduced) \<open>M\<close>.  No \<open>anchored_slice\<close> hypothesis.

  Proof by the \<open>oper\<close>-step case split:
  \<^item> NON-SHIFT (\<open>M[n] = Pred M\<close>): \<open>Red (M[n]) = Red (Pred M) = Pred (Red M)
      = Pred M = M[n]\<close> using @{thm [source] m_6_5_Red_Pred} and \<open>Red M = M\<close>, so
      \<open>M[n]\<close> is a \<open>Red\<close>-fixpoint, i.e. reduced.  (This folds in the trivial
      reduced \<open>predRdegen\<close>.)
  \<^item> SHIFT (\<open>M[n] \<noteq> Pred M\<close>): the lone hypothesis gives
      \<open>(Red M)[n] = Red (M[n])\<close>; with \<open>Red M = M\<close> this reads
      \<open>M[n] = Red (M[n])\<close>, i.e. \<open>M[n]\<close> reduced.
\<close>

lemma bf_red_preserved_by_oper_ST:
  fixes M :: pairseq and n :: nat
  assumes Mred: "M \<in> RT_PS"
    and opnT: "(M::pairseq)[n] \<in> T_PS"
    and shift_resid: "(M::pairseq)[n] \<noteq> Pred M \<Longrightarrow> (Red M)[n] = Red (M[n])"
  shows "(M::pairseq)[n] \<in> RT_PS"
proof -
  have MT: "M \<in> T_PS" using Mred by (simp add: RT_PS_def)
  have redM: "Red M = M" using Mred by (simp add: RT_PS_def)
  have fix_oper: "Red (M[n]) = (M::pairseq)[n]"
  proof (cases "(M::pairseq)[n] = Pred M")
    case True
    \<comment> \<open>NON-SHIFT: trivial reduced \<open>predRdegen\<close> + @{thm [source] m_6_5_Red_Pred}.\<close>
    have "Red ((M::pairseq)[n]) = Red (Pred M)" using True by simp
    also have "\<dots> = Pred (Red M)" by (rule m_6_5_Red_Pred[OF MT])
    also have "\<dots> = Pred M" using redM by simp
    also have "\<dots> = (M::pairseq)[n]" using True by simp
    finally show ?thesis .
  next
    case False
    \<comment> \<open>SHIFT: the lone residual on this (reduced) \<open>M\<close>.\<close>
    have comm: "(Red M)[n] = Red ((M::pairseq)[n])" by (rule shift_resid[OF False])
    have "(M::pairseq)[n] = Red ((M::pairseq)[n])" using comm redM by simp
    thus ?thesis by (rule sym)
  qed
  thus ?thesis using opnT by (simp add: RT_PS_def)
qed

text \<open>
  標準形の簡約性（§6.7）, the \<^bold>\<open>domain-gap-free\<close> chain: \<open>ST\<^sub>PS \<subseteq> RT\<^sub>PS\<close>, by
  @{thm [source] ST_PS.induct}.  The diagonal base is now fully discharged
  (@{thm [source] bf_diagSeq_reduced}); the \<open>oper\<close> step uses
  @{thm [source] bf_red_preserved_by_oper_ST}.  The \<^emph>\<open>only\<close> remaining hypothesis
  is the \<open>ST\<^sub>PS\<close>-scoped \<open>shift\<close> case of \<open>Red\<close>-\<open>oper\<close>-commutativity — NO
  \<open>diag_red\<close>, NO \<open>predRdegen\<close>, NO \<open>anch\<close>/\<open>anchored_slice\<close>.
\<close>

lemma bf_m_6_7_standard_reduced_modulo_shift:
  assumes shift_resid: "\<And>M n. \<lbrakk>M \<in> ST_PS; M \<in> RT_PS; 1 \<le> n; (M::pairseq)[n] \<noteq> Pred M\<rbrakk>
                          \<Longrightarrow> (Red M)[n] = Red (M[n])"
  shows "ST_PS \<subseteq> RT_PS"
proof
  fix N assume N: "N \<in> ST_PS"
  thus "N \<in> RT_PS"
  proof (induct N rule: ST_PS.induct)
    case (diag u v)
    show ?case by (rule bf_diagSeq_reduced[OF diag.hyps])
  next
    case (oper M n)
    have MST: "M \<in> ST_PS" by (rule oper.hyps(1))
    have Mred: "M \<in> RT_PS" by (rule oper.hyps(2))
    have n1: "1 \<le> n" by (rule oper.hyps(3))
    have opST: "(M::pairseq)[n] \<in> ST_PS" by (rule ST_PS.oper[OF MST n1])
    have opnT: "(M::pairseq)[n] \<in> T_PS" by (rule ST_PS_T_PS[OF opST])
    show "(M::pairseq)[n] \<in> RT_PS"
      by (rule bf_red_preserved_by_oper_ST[OF Mred opnT shift_resid[OF MST Mred n1]])
  qed
qed

text \<open>
  \<open>stdCA\<close> on the domain-gap-free chain: \<open>\<forall>S \<in> ST\<^sub>PS. RedCondA S\<close>, conditional
  ONLY on the \<open>ST\<^sub>PS\<close> \<open>shift\<close> residual.
\<close>

lemma bf_stdCA_modulo_shift:
  assumes shift_resid: "\<And>M n. \<lbrakk>M \<in> ST_PS; M \<in> RT_PS; 1 \<le> n; (M::pairseq)[n] \<noteq> Pred M\<rbrakk>
                          \<Longrightarrow> (Red M)[n] = Red (M[n])"
    and S: "S \<in> ST_PS"
  shows "RedCondA S"
proof -
  have sub: "ST_PS \<subseteq> RT_PS" by (rule bf_m_6_7_standard_reduced_modulo_shift[OF shift_resid])
  have Sred: "S \<in> RT_PS" using sub S by blast
  have ST: "S \<in> T_PS" by (rule ST_PS_T_PS[OF S])
  have "RedCondA S \<and> RedCondB S"
    using m_6_6_reduced_iff_cond[OF ST] Sred by blast
  thus ?thesis by simp
qed

text \<open>
  The \<open>shift\<close> residual carried by @{thm [source] bf_m_6_7_standard_reduced_modulo_shift}
  and @{thm [source] bf_stdCA_modulo_shift} is \<^emph>\<open>implied\<close> by the \<open>operCA\<close>/\<open>operCB\<close>
  tiling bricks (Front A).  For a reduced \<open>M\<close> (\<open>Red M = M\<close>), the conclusion
  \<open>(Red M)[n] = Red (M[n])\<close> collapses to \<open>M[n] = Red (M[n])\<close>, i.e. \<open>M[n]\<close> reduced.
  Since \<open>M\<close> is reduced it satisfies \<open>RedCondA M \<and> RedCondB M\<close>
  (@{thm [source] m_6_6_reduced_iff_cond}); the discriminator \<open>M[n] \<noteq> Pred M\<close>
  gives \<open>\<not> ?nontile\<close> (@{thm [source] oper_nontile_eq_Pred}); so \<open>operCA\<close>/\<open>operCB\<close>
  deliver \<open>RedCondA (M[n]) \<and> RedCondB (M[n])\<close>, whence \<open>M[n] \<in> RT\<^sub>PS\<close> by the §6.6
  keystone.  This shows route B introduces \<^bold>\<open>no extra strength\<close> over the original
  \<open>operCA\<close>/\<open>operCB\<close> route (@{thm [source] m_6_7_standard_reduced}): both bottom out
  at the same tiling bricks (= the \<open>D(N)\<close> crux).
\<close>

lemma bf_shift_resid_via_operCAB:
  assumes operCA: "\<And>N n. \<lbrakk>N \<in> ST_PS; RedCondA N; RedCondB N; 1 \<le> n;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1))\<rbrakk>
                  \<Longrightarrow> RedCondA ((N::pairseq)[n])"
    and operCB: "\<And>N n. \<lbrakk>N \<in> ST_PS; RedCondA N; RedCondB N; 1 \<le> n;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1))\<rbrakk>
                  \<Longrightarrow> RedCondB ((N::pairseq)[n])"
    and MST: "M \<in> ST_PS"
    and Mred: "M \<in> RT_PS"
    and n1: "1 \<le> n"
    and shift: "(M::pairseq)[n] \<noteq> Pred M"
  shows "(Red M)[n] = Red (M[n])"
proof -
  have redM: "Red M = M" using Mred by (simp add: RT_PS_def)
  have MT: "M \<in> T_PS" using Mred by (simp add: RT_PS_def)
  have AB_M: "RedCondA M \<and> RedCondB M"
    using m_6_6_reduced_iff_cond[OF MT] Mred by blast
  have nontile_false: "\<not> (Lng M - 1 = 0
                          \<or> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)
                          \<or> \<not> hasParent M (idx1 M (Lng M - 1)) (Lng M - 1))"
    using shift oper_nontile_eq_Pred by blast
  have cA: "RedCondA ((M::pairseq)[n])"
    by (rule operCA[OF MST conjunct1[OF AB_M] conjunct2[OF AB_M] n1 nontile_false])
  have cB: "RedCondB ((M::pairseq)[n])"
    by (rule operCB[OF MST conjunct1[OF AB_M] conjunct2[OF AB_M] n1 nontile_false])
  have opST: "(M::pairseq)[n] \<in> ST_PS" by (rule ST_PS.oper[OF MST n1])
  have opT: "(M::pairseq)[n] \<in> T_PS" by (rule ST_PS_T_PS[OF opST])
  have opRed: "(M::pairseq)[n] \<in> RT_PS"
    using m_6_6_reduced_iff_cond[OF opT] cA cB by blast
  hence "Red ((M::pairseq)[n]) = (M::pairseq)[n]" by (simp add: RT_PS_def)
  thus ?thesis using redM by simp
qed

text \<open>
  Route B's standard-reducedness, \<^bold>\<open>conditional only on \<open>operCA\<close>/\<open>operCB\<close>\<close>: the
  faithful (\<open>Red\<close>-\<open>oper\<close>-commutativity) chain
  @{thm [source] bf_m_6_7_standard_reduced_modulo_shift} with its lone \<open>shift\<close>
  residual discharged by @{thm [source] bf_shift_resid_via_operCAB}.  Same
  premises as the original @{thm [source] m_6_7_standard_reduced}, confirming the
  two routes converge.
\<close>

lemma bf_m_6_7_standard_reduced_via_operCAB:
  assumes operCA: "\<And>N n. \<lbrakk>N \<in> ST_PS; RedCondA N; RedCondB N; 1 \<le> n;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1))\<rbrakk>
                  \<Longrightarrow> RedCondA ((N::pairseq)[n])"
    and operCB: "\<And>N n. \<lbrakk>N \<in> ST_PS; RedCondA N; RedCondB N; 1 \<le> n;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1))\<rbrakk>
                  \<Longrightarrow> RedCondB ((N::pairseq)[n])"
  shows "ST_PS \<subseteq> RT_PS"
  by (rule bf_m_6_7_standard_reduced_modulo_shift,
      rule bf_shift_resid_via_operCAB[OF operCA operCB])

text \<open>\<open>stdCA\<close> on the faithful route, conditional only on \<open>operCA\<close>/\<open>operCB\<close>.\<close>

lemma bf_stdCA_via_operCAB:
  assumes operCA: "\<And>N n. \<lbrakk>N \<in> ST_PS; RedCondA N; RedCondB N; 1 \<le> n;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1))\<rbrakk>
                  \<Longrightarrow> RedCondA ((N::pairseq)[n])"
    and operCB: "\<And>N n. \<lbrakk>N \<in> ST_PS; RedCondA N; RedCondB N; 1 \<le> n;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1))\<rbrakk>
                  \<Longrightarrow> RedCondB ((N::pairseq)[n])"
    and S: "S \<in> ST_PS"
  shows "RedCondA S"
  by (rule bf_stdCA_modulo_shift[OF _ S],
      rule bf_shift_resid_via_operCAB[OF operCA operCB])


subsection \<open>(viii) §6.7 \<open>DISJ\<close> residual — WG reflection core (\<open>wg_reflect_core\<close>)\<close>

text \<open>
  The heart of the \<open>w > 1\<close> branch of \<open>disj\<close> (\<open>has_gz(M[n]) \<Longrightarrow> has_gz M\<close>): an
  N-side row-1 parent edge \<open>nextrel1 (M[n]) p\<^sub>z z\<close> with both endpoints in the SAME
  block \<open>q\<close> (\<open>p\<^sub>z = j\<^sub>0 + q\<cdot>w + sp\<close>, \<open>z = j\<^sub>0 + q\<cdot>w + s\<close>, \<open>sp < s < w\<close>) reflects to a
  row-1 parent of the M-side child \<open>j\<^sub>0 + s\<close>: \<open>hasParent M 1 (j\<^sub>0 + s)\<close> with parent
  \<open>\<ge> j\<^sub>0 + sp\<close>.  GREEN, RedCondA-free, NO boundary valley / NO row-1 tree / NO
  \<open>D\<close>: it uses only the periodic row-1 read @{thm [source] oper_d1pos_entry1}, the
  N\<rightarrow>M same-block \<open>le0\<close> reflection @{thm [source] oper_d1pos_le0_base_back}, the
  §5.1 parent-existence criterion @{thm [source] m_5_1_parent_exists_2} and
  uniqueness @{thm [source] nextR1_unique}.  Verified 162/0 on the broad ST_PS
  closure (\<open>w > 1\<close> gated oper-steps).
\<close>

lemma wg_reflect_core:
  fixes M :: pairseq and n q sp s :: nat
  assumes MT: "M \<in> T_PS"
    and L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and qn: "q < n"
    and sps: "sp < s"
    and sw: "s < Lng M - 1 - parent M 1 (Lng M - 1)"
    and edge: "nextrel1 ((M::pairseq)[n])
                 (parent M 1 (Lng M - 1)
                    + q * (Lng M - 1 - parent M 1 (Lng M - 1)) + sp)
                 (parent M 1 (Lng M - 1)
                    + q * (Lng M - 1 - parent M 1 (Lng M - 1)) + s)"
  shows "hasParent M 1 (parent M 1 (Lng M - 1) + s)
         \<and> parent M 1 (Lng M - 1) + sp \<le> parent M 1 (parent M 1 (Lng M - 1) + s)"
proof -
  let ?j1 = "Lng M - 1"  let ?j0 = "parent M 1 ?j1"
  let ?w = "?j1 - ?j0"   let ?Mn = "(M::pairseq)[n]"
  let ?pz = "?j0 + q * ?w + sp"  let ?z = "?j0 + q * ?w + s"
  let ?pp = "?j0 + sp"   let ?zp = "?j0 + s"
  have spw: "sp < ?w" using sps sw by linarith
  \<comment> \<open>periodic row-1 reads: the two endpoints reflect to M-side columns\<close>
  have e_pz: "entry ?Mn 1 ?pz = entry M 1 ?pp"
    by (rule oper_d1pos_entry1[OF L notzero hp i1z j0lt qn spw])
  have e_z: "entry ?Mn 1 ?z = entry M 1 ?zp"
    by (rule oper_d1pos_entry1[OF L notzero hp i1z j0lt qn sw])
  \<comment> \<open>decompose the N-side parent edge\<close>
  have elt: "entry ?Mn 1 ?pz < entry ?Mn 1 ?z"
    using edge by (simp add: nextrel1_def)
  have eMlt: "entry M 1 ?pp < entry M 1 ?zp" using elt e_pz e_z by simp
  have le0N: "le0 ?Mn ?pz ?z" using edge by (simp add: nextrel1_def)
  \<comment> \<open>N\<rightarrow>M same-block \<open>le0\<close> reflection\<close>
  have le0M: "le0 M ?pp ?zp"
    by (rule oper_d1pos_le0_base_back[OF L notzero hp i1z j0lt qn sps sw le0N])
  \<comment> \<open>§5.1 parent existence for the M-side child \<open>?zp\<close>\<close>
  have zpL: "?zp < Lng M" using sw j0lt by linarith
  have ppzp: "?pp < ?zp" using sps by simp
  have leR: "leR M 0 ?pp ?zp" using le0M by (simp add: leR_def)
  obtain j where j: "?pp \<le> j" "j < ?zp" "nextR M 1 j ?zp"
    using m_5_1_parent_exists_2[OF MT ppzp zpL eMlt leR] by auto
  \<comment> \<open>existence + uniqueness give \<open>hasParent\<close> and pin the parent value to \<open>j\<close>\<close>
  have hpzp: "hasParent M 1 ?zp"
    unfolding hasParent_def using j(3) nextR1_unique by blast
  have parR: "nextR M 1 (parent M 1 ?zp) ?zp"
    using hpzp unfolding hasParent_def parent_def by (rule theI')
  have parj: "parent M 1 ?zp = j" by (rule nextR1_unique[OF parR j(3)])
  have "?pp \<le> parent M 1 ?zp" using parj j(1) by simp
  thus ?thesis using hpzp by simp
qed


subsection \<open>(ix) §6.7 \<open>DISJ\<close> \<open>w = 1\<close> foundation — verbatim prefix parent agreement\<close>

text \<open>
  In the tiling \<open>M[n]\<close> the prefix \<open>[0, j\<^sub>0)\<close> (\<open>j\<^sub>0 = parent M (idx\<^sub>1) (Lng M-1)\<close>)
  is a VERBATIM copy of \<open>M\<close> (@{thm [source] oper_gen_nth_prefix}).  For a prefix
  column \<open>z < j\<^sub>0\<close> the whole row-1 parent structure is determined inside that
  agreement region — its \<open>le0\<close>-predecessors all sit at index \<open>\<le> z < j\<^sub>0\<close> — so
  \<open>hasParent\<close> and \<open>parent\<close> at \<open>z\<close> COINCIDE between \<open>M[n]\<close> and \<open>M\<close>
  (@{thm [source] nextrel1_prefix_imp} both ways).  This is the foundation of the
  \<open>w = 1\<close> branch of \<open>disj\<close>, where every gated \<open>z\<close> of \<open>M[n]\<close> lies in this prefix
  (verified 774/0, tail 0).  GREEN, no tiling-tail row-1 locality.
\<close>

lemma oper_parent1_prefix_agree:
  fixes M :: pairseq and n z :: nat
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and j0lt: "parent M (idx1 M (Lng M - 1)) (Lng M - 1) < Lng M - 1"
    and zlt: "z < parent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and zL: "z < Lng ((M::pairseq)[n])"
  shows "hasParent ((M::pairseq)[n]) 1 z = hasParent M 1 z
         \<and> parent ((M::pairseq)[n]) 1 z = parent M 1 z"
proof -
  let ?j0 = "parent M (idx1 M (Lng M - 1)) (Lng M - 1)"
  let ?Mn = "(M::pairseq)[n]"
  have zLM: "z < Lng M" using zlt j0lt by linarith
  have agree: "\<And>j. j \<le> z \<Longrightarrow> M ! j = ?Mn ! j"
  proof -
    fix j assume jz: "j \<le> z"
    have "j < ?j0" using jz zlt by linarith
    thus "M ! j = ?Mn ! j"
      using oper_gen_nth_prefix[OF L notzero hp, of j n] by simp
  qed
  have agreeS: "\<And>j. j \<le> z \<Longrightarrow> ?Mn ! j = M ! j" using agree by simp
  have nx_iff: "\<And>j0. nextR ?Mn 1 j0 z = nextR M 1 j0 z"
  proof -
    fix j0
    show "nextR ?Mn 1 j0 z = nextR M 1 j0 z"
    proof (cases "j0 \<le> z")
      case True
      have jz: "j0 \<le> z" by (rule True)
      show ?thesis
      proof
        assume "nextR ?Mn 1 j0 z"
        hence nr: "nextrel1 ?Mn j0 z" by (simp add: nextR_def)
        have "nextrel1 M j0 z"
          by (rule nextrel1_prefix_imp[OF agreeS zL zLM jz order.refl nr])
        thus "nextR M 1 j0 z" by (simp add: nextR_def)
      next
        assume "nextR M 1 j0 z"
        hence nr: "nextrel1 M j0 z" by (simp add: nextR_def)
        have "nextrel1 ?Mn j0 z"
          by (rule nextrel1_prefix_imp[OF agree zLM zL jz order.refl nr])
        thus "nextR ?Mn 1 j0 z" by (simp add: nextR_def)
      qed
    next
      case False
      hence zj0: "z < j0" by simp
      have "\<not> nextR ?Mn 1 j0 z" using zj0 by (auto simp: nextR_def nextrel1_def)
      moreover have "\<not> nextR M 1 j0 z" using zj0 by (auto simp: nextR_def nextrel1_def)
      ultimately show ?thesis by simp
    qed
  qed
  have hpiff: "hasParent ?Mn 1 z = hasParent M 1 z"
    unfolding hasParent_def using nx_iff by simp
  have pariff: "parent ?Mn 1 z = parent M 1 z"
    unfolding parent_def using nx_iff by simp
  show ?thesis using hpiff pariff by blast
qed


text \<open>The last-node \<open>TreeWF\<close> is the \<open>y = Lng M-1\<close> instance of \<open>GTWF\<close> when the last
  node has a row-1 parent (the gated case used downstream).\<close>

lemma treewf_of_gtw:
  assumes gtw: "GTWF M" and hp: "hasParent M 1 (Lng M - 1)"
  shows "TreeWF M"
  using gtw hp by blast

lemma RedCondAB_ST_PS:
  assumes "M \<in> ST_PS"
  shows "RedCondA M \<and> RedCondB M"
  by (rule m_6_7_standard_RedCondAB[OF assms operCA_tiling_full operCB_tiling])


lemma coreReduce_le0_fwd:
  assumes MT: "M \<in> T_PS" and pos: "0 < entry M 1 0"
    and r: "le0 M k k'"
  shows "le0 (diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ entry M 1 0) M)
           (entry M 1 0 + k) (entry M 1 0 + k')"
proof -
  let ?m = "entry M 1 0"
  let ?A = "diagSeq 0 (?m - 1) @ (IncrFirst ^^ ?m) M"
  have kM: "k < Lng M" and kM': "k' < Lng M" and ch: "(nextrel0 M)\<^sup>*\<^sup>* k k'"
    using r by (simp_all add: le0_def)
  have Ld: "Lng (diagSeq 0 (?m - 1)) = ?m" using pos by (simp del: upt_Suc)
  have LA: "Lng ?A = ?m + Lng M" using Ld by simp
  have main: "(nextrel0 ?A)\<^sup>*\<^sup>* (?m + k) (?m + k')"
    using ch kM
  proof (induction rule: converse_rtranclp_induct)
    case base show ?case by simp
  next
    case (step x y)
    have xy: "x < y" using step.hyps(1) by (simp add: nextrel0_def)
    have yM: "y < Lng M"
    proof -
      have "y \<le> k'" using step.hyps(2) nextrel0_rtrancl_mono by blast
      thus ?thesis using kM' by linarith
    qed
    have xM: "x < Lng M" using xy yM by linarith
    have "nextrel0 ?A (?m + x) (?m + y)"
      using coreReduce_nextrel0_transfer[OF MT pos xM yM] step.hyps(1) by simp
    moreover have "(nextrel0 ?A)\<^sup>*\<^sup>* (?m + y) (?m + k')" using step.IH yM by simp
    ultimately show ?case by (rule converse_rtranclp_into_rtranclp)
  qed
  show ?thesis
    unfolding le0_def using main LA kM kM' by simp
qed

end
