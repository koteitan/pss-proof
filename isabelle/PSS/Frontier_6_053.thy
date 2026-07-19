theory Frontier_6_053
  imports Support_6_035
begin

lemma congR_trans: "congR A X \<Longrightarrow> congR X Y \<Longrightarrow> congR A Y"
  by (simp add: congR_def)

text \<open>Structural sharing, restated point-free off \<open>congR\<close> (for use outside the locale).\<close>
lemma congR_Lng: "congR A X \<Longrightarrow> Lng A = Lng X" by (simp add: congR_def)
lemma congR_nextR: "congR A X \<Longrightarrow> nextR A = nextR X"
  by (drule congR_cong_struct) (rule cong_struct.nextR_eq)
lemma congR_leR: "congR A X \<Longrightarrow> leR A = leR X"
  by (drule congR_cong_struct) (rule cong_struct.leR_eq)
lemma congR_TrMax: "congR A X \<Longrightarrow> TrMax A = TrMax X"
  by (drule congR_cong_struct) (rule cong_struct.TrMax_eq)
lemma congR_zeroT: "congR A X \<Longrightarrow> zeroT A = zeroT X"
  by (drule congR_cong_struct) (rule cong_struct.zeroT_eq)
lemma congR_multiT: "congR A X \<Longrightarrow> multiT A = multiT X"
  by (drule congR_cong_struct) (rule cong_struct.multiT_eq)
lemma congR_Pcut: "congR A X \<Longrightarrow> Pcut A = Pcut X"
  by (drule congR_cong_struct) (rule cong_struct.Pcut_eq)

text \<open>A segment of \<open>A\<close> and \<open>X\<close> over the \<^emph>\<open>same\<close> index window inherits \<open>congR\<close>:
  row-1 is shared pointwise, length is shared, and \<open>nextrel0\<close> on a segment is
  determined by \<open>nextrel0\<close> on the whole (@{thm [source] adm_nextrel0_seg}).\<close>

lemma congR_seg:
  assumes R: "congR A X" and b: "bb < Lng X"
  shows "congR (seg A aa bb) (seg X aa bb)"
proof -
  have LAX: "Lng A = Lng X" using R by (simp add: congR_def)
  have bA: "bb < Lng A" using b LAX by simp
  have n0AX: "nextrel0 A = nextrel0 X" using R by (simp add: congR_def)
  have lenseg: "Lng (seg A aa bb) = Lng (seg X aa bb)" by (simp add: Lng_seg)
  show ?thesis
  proof (unfold congR_def, intro conjI allI impI)
    show "Lng (seg A aa bb) = Lng (seg X aa bb)" by (rule lenseg)
  next
    show "nextrel0 (seg A aa bb) = nextrel0 (seg X aa bb)"
    proof (intro ext)
      fix p q
      show "nextrel0 (seg A aa bb) p q = nextrel0 (seg X aa bb) p q"
      proof (cases "p < Lng (seg X aa bb) \<and> q < Lng (seg X aa bb)")
        case True
        hence pX: "p < Lng (seg X aa bb)" and qX: "q < Lng (seg X aa bb)" by auto
        have pA: "p < Lng (seg A aa bb)" using pX lenseg by simp
        have qA: "q < Lng (seg A aa bb)" using qX lenseg by simp
        have "nextrel0 (seg A aa bb) p q = nextrel0 A (aa + p) (aa + q)"
          by (rule adm_nextrel0_seg[OF bA pA qA])
        also have "\<dots> = nextrel0 X (aa + p) (aa + q)" using n0AX by simp
        also have "\<dots> = nextrel0 (seg X aa bb) p q"
          by (rule adm_nextrel0_seg[OF b pX qX, symmetric])
        finally show ?thesis .
      next
        case False
        thus ?thesis by (auto simp: nextrel0_def lenseg)
      qed
    qed
  next
    fix j assume jl: "j < Lng (seg X aa bb)"
    have jA: "j < Lng (seg A aa bb)" using jl lenseg by simp
    have idxX: "aa + j < Lng X" using jl by (simp add: Lng_seg) (insert b, simp)
    have "entry (seg A aa bb) 1 j = entry A 1 (aa + j)" using jA by (simp add: entry_seg)
    also have "\<dots> = entry X 1 (aa + j)"
      using R idxX by (simp add: congR_def)
    also have "\<dots> = entry (seg X aa bb) 1 j" using jl by (simp add: entry_seg)
    finally show "entry (seg A aa bb) 1 j = entry (seg X aa bb) 1 j" .
  qed
qed

text \<open>\<open>take c A\<close> / \<open>take c X\<close> and \<open>drop c A\<close> / \<open>drop c X\<close> inherit \<open>congR\<close> (special
  windows of @{thm [source] congR_seg}).\<close>

lemma congR_take:
  assumes R: "congR A X" and c: "c \<le> Lng X"
  shows "congR (take c A) (take c X)"
proof (cases "c = 0")
  case True thus ?thesis by (simp add: congR_def)
next
  case False
  hence cpos: "0 < c" by simp
  have LAX: "Lng A = Lng X" using R by (simp add: congR_def)
  have sb: "c - 1 < Lng X" using c cpos by simp
  have segR: "congR (seg A 0 (c - 1)) (seg X 0 (c - 1))" by (rule congR_seg[OF R sb])
  have tA: "seg A 0 (c - 1) = take c A" using c cpos LAX by (simp add: seg_0_eq_take)
  have tX: "seg X 0 (c - 1) = take c X" using c cpos by (simp add: seg_0_eq_take)
  show ?thesis using segR tA tX by simp
qed

lemma congR_drop:
  assumes R: "congR A X" and L0: "0 < Lng X"
  shows "congR (drop c A) (drop c X)"
proof -
  have LAX: "Lng A = Lng X" using R by (simp add: congR_def)
  have LA0: "0 < Lng A" using L0 LAX by simp
  have sb: "Lng X - 1 < Lng X" using L0 by simp
  have segR: "congR (seg A c (Lng X - 1)) (seg X c (Lng X - 1))" by (rule congR_seg[OF R sb])
  have dA: "seg A c (Lng X - 1) = drop c A"
    using LA0 LAX seg_to_last_eq_drop[OF LA0, of c] by simp
  have dX: "seg X c (Lng X - 1) = drop c X" using L0 seg_to_last_eq_drop[OF L0, of c] by simp
  show ?thesis using segR dA dX by simp
qed

text \<open>The \<open>P\<close>-decomposition has the same block count and per-position block
  lengths: \<open>map length (P A) = map length (P X)\<close> (hence \<open>length (P A) =
  length (P X)\<close>, \<open>IdxSum (P A) = IdxSum (P X)\<close>).  By @{thm [source] P.induct}
  carrying \<open>congR\<close>: \<open>multiT\<close> and \<open>Pcut\<close> are shared, the prefix \<open>take (Pcut) _\<close>
  inherits \<open>congR\<close> (IH), and the suffix \<open>drop (Pcut) _\<close> has shared length.\<close>

lemma congR_P_maplen:
  "congR A X \<Longrightarrow> map length (P A) = map length (P X)"
proof (induction A arbitrary: X rule: P.induct)
  case (1 A)
  note R = "1.prems"
  have LAX: "Lng A = Lng X" using R by (simp add: congR_def)
  have muAX: "multiT A = multiT X" by (rule congR_multiT[OF R])
  show ?case
  proof (cases "multiT A \<and> 1 < Lng A")
    case mu: True
    hence muX: "multiT X \<and> 1 < Lng X" using muAX LAX by simp
    let ?cA = "Pcut A"
    have pcAX: "Pcut A = Pcut X" by (rule congR_Pcut[OF R])
    have LX1: "1 < Lng X" using muX by (rule conjunct2)
    have L0: "0 < Lng X" using LX1 by linarith
    have "Pcut X \<le> Lng X - 1" using Pcut_le[OF LX1] by simp
    hence cle: "Pcut A \<le> Lng X" using pcAX by simp
    have RtakeA: "congR (take ?cA A) (take ?cA X)" by (rule congR_take[OF R cle])
    have RdropA: "congR (drop ?cA A) (drop ?cA X)" by (rule congR_drop[OF R L0])
    have ih: "map length (P (take ?cA A)) = map length (P (take ?cA X))"
      using "1.IH"[OF mu RtakeA] by simp
    have PA: "P A = P (take ?cA A) @ [drop ?cA A]"
      by (subst P.simps) (rule if_P[OF mu])
    have PX: "P X = P (take (Pcut X) X) @ [drop (Pcut X) X]"
      by (subst P.simps) (rule if_P[OF muX])
    have lenDrop: "length (drop ?cA A) = length (drop ?cA X)"
      using RdropA by (simp add: congR_def)
    show ?thesis using PA PX ih lenDrop pcAX by simp
  next
    case nmu: False
    have ncX: "\<not> (multiT X \<and> 1 < Lng X)" using muAX LAX nmu by simp
    have PX: "P X = [X]" by (subst P.simps) (rule if_not_P[OF ncX])
    have PA: "P A = [A]" by (subst P.simps) (rule if_not_P[OF nmu])
    show ?thesis using PA PX LAX by simp
  qed
qed

lemma congR_P_length: "congR A X \<Longrightarrow> length (P A) = length (P X)"
  by (drule congR_P_maplen) (metis length_map)

lemma congR_P_IdxSum: "congR A X \<Longrightarrow> IdxSum (P A) = IdxSum (P X)"
proof -
  assume "congR A X"
  hence ml: "map length (P A) = map length (P X)" by (rule congR_P_maplen)
  hence ll: "length (P A) = length (P X)" by (metis length_map)
  have "\<And>x. sum_list (map length (take x (P A))) = sum_list (map length (take x (P X)))"
    using ml by (metis take_map)
  thus ?thesis using ll by (simp add: IdxSum_def)
qed

text \<open>Each \<open>P\<close>-block pair inherits \<open>congR\<close>: both are the segment over the same
  IdxSum window of \<open>A\<close>, \<open>X\<close> respectively.\<close>

lemma congR_P_block:
  assumes R: "congR A X" and AT: "A \<in> T_PS" and XT: "X \<in> T_PS"
    and J: "J < length (P X)"
  shows "congR (P A ! J) (P X ! J)"
proof -
  have LAX: "Lng A = Lng X" using R by (simp add: congR_def)
  have idxAX: "IdxSum (P A) = IdxSum (P X)" by (rule congR_P_IdxSum[OF R])
  have lenAX: "length (P A) = length (P X)" by (rule congR_P_length[OF R])
  have JA: "J \<le> Lng (P A) - 1" using J lenAX by simp
  have JX: "J \<le> Lng (P X) - 1" using J by simp
  let ?s = "IdxSum (P X) ! J" let ?e = "IdxSum (P X) ! (J + 1) - 1"
  have blkA: "P A ! J = seg A (IdxSum (P A) ! J) (IdxSum (P A) ! (J + 1) - 1)"
    by (rule m_6_4_P_IdxSum[OF AT JA])
  have blkX: "P X ! J = seg X ?s ?e" by (rule m_6_4_P_IdxSum[OF XT JX])
  have blkA': "P A ! J = seg A ?s ?e" using blkA idxAX by simp
  have Xne: "X \<noteq> []" using XT by (simp add: T_PS_def)
  have JL: "J < length (P X)" using J .
  have eltX: "?e < Lng X"
  proof -
    have concatM: "concat (P X) = X" by (rule idxsum_concat_P)
    hence lensum: "Lng X = sum_list (map length (P X))" by (metis length_concat)
    have J1: "J + 1 \<le> length (P X)" using JL by simp
    have idx1: "IdxSum (P X) ! (J + 1) = sum_list (map length (take (J + 1) (P X)))"
      using J1 by (rule idxsum_nth)
    have mono': "sum_list (map length (take (J + 1) (P X)))
                  \<le> sum_list (map length (take (length (P X)) (P X)))"
      using idxsum_sum_take_mono[OF J1, of "P X"] by simp
    have "sum_list (map length (take (J + 1) (P X))) \<le> sum_list (map length (P X))"
      using mono' by (simp add: take_all)
    hence le1: "IdxSum (P X) ! (J + 1) \<le> Lng X" using idx1 lensum by simp
    have diff: "IdxSum (P X) ! (J + 1) = ?s + length (P X ! J)" by (rule idxsum_diff[OF JL])
    have bnonempty: "0 < length (P X ! J)"
      using P_blocks_nonempty[OF Xne] JL nth_mem by (metis length_greater_0_conv)
    have pos: "0 < IdxSum (P X) ! (J + 1)" using diff bnonempty by simp
    show "?e < Lng X" using le1 pos by simp
  qed
  show ?thesis using congR_seg[OF R eltX] blkA' blkX by simp
qed

text \<open>\<open>IncrFirst\<close> (and its funpow) preserves \<open>congR\<close>: it preserves \<open>nextrel0\<close>
  (@{thm [source] nextrel0_IncrFirst_eq}) and row-1 (@{thm [source] entry_IncrFirst}).\<close>

lemma congR_IncrFirst:
  assumes R: "congR A X" shows "congR (IncrFirst A) (IncrFirst X)"
proof -
  have LAX: "Lng A = Lng X" using R by (simp add: congR_def)
  have n0: "nextrel0 A = nextrel0 X" using R by (simp add: congR_def)
  show ?thesis unfolding congR_def
  proof (intro conjI allI impI)
    show "Lng (IncrFirst A) = Lng (IncrFirst X)" using LAX by (simp add: IncrFirst_def)
    show "nextrel0 (IncrFirst A) = nextrel0 (IncrFirst X)"
      by (simp add: nextrel0_IncrFirst_eq n0)
    fix j assume j: "j < Lng (IncrFirst X)"
    hence jX: "j < Lng X" by (simp add: IncrFirst_def)
    have jA: "j < Lng A" using jX LAX by simp
    have "entry (IncrFirst A) 1 j = entry A 1 j" using entry_IncrFirst[OF jA, of 1] by simp
    also have "\<dots> = entry X 1 j" using R jX by (simp add: congR_def)
    also have "\<dots> = entry (IncrFirst X) 1 j" using entry_IncrFirst[OF jX, of 1] by simp
    finally show "entry (IncrFirst A) 1 j = entry (IncrFirst X) 1 j" .
  qed
qed

end
