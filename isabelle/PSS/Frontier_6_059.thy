theory Frontier_6_059
  imports Support_6_040
begin

(* ===== block from workflow t3-ecrux : §6.6 簡約性と左端の関係 (e)-lemma support ===== *)

subsection \<open>§6.6 対角セグメントの分割 (diagonal split, ecrux)\<close>

text \<open>ecrux helper: a diagonal \<open>diagSeq a b\<close> splits at any interior point \<open>m\<close>
  (\<open>a \<le> m < b\<close>) as \<open>diagSeq a m @ diagSeq (Suc m) b\<close>.  The assembly of the
  \<open>(e)\<close>-lemma needs the two instances
  \<open>diagSeq 0 (u-1) @ diagSeq u (m\<^sub>1\<^sub>0-1) = diagSeq 0 (m\<^sub>1\<^sub>0-1)\<close> (gluing the two
  leading diagonals) and
  \<open>diagSeq 0 (m\<^sub>1\<^sub>0-1) @ diagSeq m\<^sub>1\<^sub>0 (m\<^sub>1\<^sub>0 + j\<^sub>1) = diagSeq 0 (m\<^sub>1\<^sub>0 + j\<^sub>1)\<close>
  (gluing the prepended diagonal onto the reduced trunk).\<close>

lemma ecrux_diagSeq_split:
  assumes alm: "a \<le> m" and mb: "m < b"
  shows "diagSeq a m @ diagSeq (Suc m) b = diagSeq a b"
proof -
  have "diagSeq a m @ diagSeq (Suc m) b
          = map (\<lambda>j. (j, j)) [a..<Suc m] @ map (\<lambda>j. (j, j)) [Suc m..<Suc b]"
    by (simp add: diagSeq_def)
  also have "\<dots> = map (\<lambda>j. (j, j)) ([a..<Suc m] @ [Suc m..<Suc b])" by simp
  also have "[a..<Suc m] @ [Suc m..<Suc b] = [a..<Suc b]"
  proof -
    have a1: "a \<le> Suc m" using alm by simp
    have a2: "Suc m \<le> Suc b" using mb by simp
    show ?thesis using upt_add_eq_append[OF a1, of "Suc b - Suc m"] a2 by simp
  qed
  also have "map (\<lambda>j. (j, j)) [a..<Suc b] = diagSeq a b" by (simp add: diagSeq_def)
  finally show ?thesis .
qed


(* ===== §6.6 命題（簡約性の切片への遺伝性） herd block (t3-herd) ===== *)

text \<open>herd helper: iterated \<open>Pred\<close> preserves \<open>T\<^sub>PS\<close>.  \<open>Pred\<close> alone preserves
  \<open>T\<^sub>PS\<close> (@{thm [source] Pred_preserves_T_PS}), so iterate by induction on \<open>k\<close>.\<close>

lemma herd_Pred_pow_T_PS:
  assumes "M \<in> T_PS"
  shows "(Pred ^^ k) M \<in> T_PS"
proof (induction k)
  case 0
  thus ?case using assms by simp
next
  case (Suc k)
  have step: "(Pred ^^ Suc k) M = Pred ((Pred ^^ k) M)"
    by (simp only: funpow.simps o_apply)
  show ?case
    unfolding step by (rule Pred_preserves_T_PS[OF Suc.IH])
qed

text \<open>herd helper: for \<open>k < Lng M\<close>, iterating \<open>Pred\<close> \<open>k\<close> times is an initial
  \<open>take\<close>.  Each \<open>Pred\<close> with length \<open>> 1\<close> drops the last column
  (\<open>Pred = butlast\<close>); the bound \<open>k < Lng M\<close> keeps every intermediate length
  \<open>> 1\<close>, so no \<open>Pred\<close> is a no-op.\<close>

lemma herd_Pred_pow_take:
  assumes "k < Lng M"
  shows "(Pred ^^ k) M = take (Lng M - k) M"
  using assms
proof (induction k)
  case 0
  thus ?case by simp
next
  case (Suc k)
  have kLt: "k < Lng M" using Suc.prems by simp
  have IH: "(Pred ^^ k) M = take (Lng M - k) M" by (rule Suc.IH[OF kLt])
  \<comment> \<open>the inner take has length \<open>Lng M - k > 1\<close>, so \<open>Pred\<close> is \<open>butlast\<close>.\<close>
  have lenTake: "Lng (take (Lng M - k) M) = Lng M - k"
    using kLt by simp
  have gt1: "1 < Lng (take (Lng M - k) M)"
    using lenTake Suc.prems by simp
  have "(Pred ^^ Suc k) M = Pred (take (Lng M - k) M)"
    using IH by simp
  also have "\<dots> = butlast (take (Lng M - k) M)"
    using gt1 by (simp add: Pred_def)
  also have "\<dots> = take (Lng M - k - 1) M"
    by (simp add: butlast_take)
  also have "\<dots> = take (Lng M - Suc k) M" by simp
  finally show ?case .
qed

text \<open>herd helper: \<open>Red\<close> commutes with iterated \<open>Pred\<close> on \<open>T\<^sub>PS\<close>.  Single-step
  commutativity is @{thm [source] m_6_5_Red_Pred}; iterate by induction, using
  @{thm [source] herd_Pred_pow_T_PS} to keep the inner argument in \<open>T\<^sub>PS\<close>.\<close>

lemma herd_Red_Pred_pow:
  assumes "M \<in> T_PS"
  shows "Red ((Pred ^^ k) M) = (Pred ^^ k) (Red M)"
proof (induction k)
  case 0
  show ?case by simp
next
  case (Suc k)
  have argT: "(Pred ^^ k) M \<in> T_PS" by (rule herd_Pred_pow_T_PS[OF assms])
  have e1: "(Pred ^^ Suc k) M = Pred ((Pred ^^ k) M)"
    by (simp only: funpow.simps o_apply)
  have e2: "(Pred ^^ Suc k) (Red M) = Pred ((Pred ^^ k) (Red M))"
    by (simp only: funpow.simps o_apply)
  have "Red ((Pred ^^ Suc k) M) = Red (Pred ((Pred ^^ k) M))"
    by (simp only: e1)
  also have "\<dots> = Pred (Red ((Pred ^^ k) M))"
    by (rule m_6_5_Red_Pred[OF argT])
  also have "\<dots> = Pred ((Pred ^^ k) (Red M))"
    by (rule arg_cong[OF Suc.IH])
  also have "\<dots> = (Pred ^^ Suc k) (Red M)" by (simp only: e2)
  finally show ?case .
qed

end
