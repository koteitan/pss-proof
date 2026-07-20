theory Frontier_6_014
  imports P_6_4_P_leftend_mono
begin

subsection \<open>§6.2 単項性: 非複項列の基本列 (non-multi expansion)\<close>

text \<open>
  For a non-multi \<open>M\<close>, \<open>M[n]\<close> is either \<open>n\<close> copies of \<open>Pred M\<close> (when the last
  index is a row-0 child of index 0 with zero second coordinate) or a single
  non-multi sequence \<open>[M[n]]\<close>.  These two lemmas discharge
  @{text p_6_2_nonmulti_oper_1} / @{text p_6_2_nonmulti_oper_2}.
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

end
