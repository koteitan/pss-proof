theory Frontier_6_093
  imports P_6_6_ancestor_slice_Red_IncrFirst
begin

section \<open>§6.6 命題（簡約性が基本列で保たれること）\<close>

text \<open>\<open>oper\<close> keeps \<open>T\<^sub>PS\<close> (nonemptiness): degenerate steps return \<open>M\<close> or
  \<open>Pred M\<close>; the tiling step has length \<open>j\<^sub>0 + n\<cdot>w\<close>
  (@{thm [source] operB_gen_LngM}) with \<open>w > 0\<close>.\<close>

lemma oper_T_PS:
  assumes MT: "M \<in> T_PS" and n1: "1 \<le> n"
  shows "(M::pairseq)[n] \<in> T_PS"
proof (cases "Lng M - 1 = 0
              \<or> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)
              \<or> \<not> hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)")
  case True
  have or: "(M::pairseq)[n] = M \<or> (M::pairseq)[n] = Pred M"
    using True by (auto simp: oper_def Let_def)
  have PT: "Pred M \<in> T_PS"
  proof (cases "Lng M \<le> 1")
    case True thus ?thesis using MT by (simp add: Pred_def)
  next
    case False
    have "Pred M = butlast M" using False by (simp add: Pred_def)
    moreover have "0 < Lng (butlast M)" using False by simp
    ultimately show ?thesis
      using length_greater_0_conv by (fastforce simp: T_PS_def)
  qed
  show ?thesis using or MT PT by auto
next
  case False
  let ?j1 = "Lng M - 1"  let ?i1 = "idx1 M ?j1"  let ?j0 = "parent M ?i1 ?j1"
  let ?w = "Lng M - 1 - ?j0"
  have L: "1 < Lng M" using False by (cases "Lng M - 1 = 0") auto
  have notzero: "\<not> (entry M 0 ?j1 = 0 \<and> entry M 1 ?j1 = 0)" using False by blast
  have hp: "hasParent M ?i1 ?j1" using False by blast
  have parR: "nextR M ?i1 ?j0 ?j1"
    using hp unfolding hasParent_def parent_def by (rule theI')
  have j0lt: "?j0 < ?j1" using poper_nextR_imp_le0[OF parR] by simp
  have w0: "0 < ?w" using j0lt by linarith
  have LngMn: "Lng ((M::pairseq)[n]) = ?j0 + n * ?w"
    by (rule operB_gen_LngM[OF L notzero hp j0lt])
  have "0 < n * ?w" using w0 n1 by simp
  hence "0 < Lng ((M::pairseq)[n])" using LngMn by simp
  hence "(M::pairseq)[n] \<noteq> []" using length_greater_0_conv by blast
  thus ?thesis by (simp add: T_PS_def)
qed

text \<open>operCA tiling, \<open>T\<^sub>PS\<close>-general form: the @{thm [source] operCA_tiling_full}
  body never used the standardness/\<open>RedCondB\<close> hypotheses (gate-free escape
  readback is unconditional).\<close>

lemma operCA_tiling_T:
  assumes condA: "RedCondA N" and n1: "1 \<le> n"
    and tile: "\<not> (Lng N - 1 = 0
                  \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                  \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1))"
  shows "RedCondA ((N::pairseq)[n])"
proof -
  from tile have ndeg: "Lng N - 1 \<noteq> 0"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)" by auto
  have L: "1 < Lng N" using ndeg by linarith
  show ?thesis
  proof (cases "idx1 N (Lng N - 1) = 1")
    case True
    note i1z = True
    have hpj1: "hasParent N 1 (Lng N - 1)" using hp i1z by simp
    have parRj1: "nextR N 1 (parent N 1 (Lng N - 1)) (Lng N - 1)"
      using hpj1 unfolding hasParent_def parent_def by (rule theI')
    have j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
      using parRj1 by (simp add: nextR_def nextrel1_def)
    show ?thesis by (rule operCA_d1pos[OF L notzero hp i1z j0lt condA n1])
  next
    case False
    have i1z0: "idx1 N (Lng N - 1) = 0"
      using False by (simp add: idx1_def split: if_split_asm)
    have parRj0: "nextR N (idx1 N (Lng N - 1))
                    (parent N (idx1 N (Lng N - 1)) (Lng N - 1)) (Lng N - 1)"
      using hp unfolding hasParent_def parent_def by (rule theI')
    have j0lt0: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
      using parRj0 i1z0 by (simp add: nextR_def nextrel0_def)
    show ?thesis by (rule operCA_d0zero[OF L notzero hp i1z0 j0lt0 condA n1])
  qed
qed

end
