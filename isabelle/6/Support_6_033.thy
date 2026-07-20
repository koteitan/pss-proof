theory Support_6_033
  imports P_6_6_P_reduced
begin

text \<open>§6.5 (A4) helper: an ancestor-anchored slice is never \<open>multiT\<close>.

  For \<open>M \<in> anchored_slice\<close> we have \<open>M = seg S a b\<close> with \<open>a \<le> b < Lng S\<close>,
  \<open>le0 S a b\<close>, and \<open>S \<in> T_PS\<close> (from \<open>S \<in> ST_PS\<close> via @{thm [source] ST_PS_T_PS},
  or from \<open>S \<in> PT_PS \<subseteq> T_PS\<close>).  The ancestor relation \<open>le0 S a b = leR S 0 a b\<close>
  makes the slice monotone:
  \<^item> \<open>a = b\<close>: \<open>Lng M = 1\<close>, so \<open>M\<close> is \<open>zeroT\<close> or (\<open>\<not> zeroT\<close> and \<open>le0 M 0 0\<close> by
    @{thm [source] le0_refl}) \<open>monoT\<close>;
  \<^item> \<open>a < b\<close>: @{thm [source] m_6_2_mono_ancestor_slice} gives \<open>monoT (seg S a b)\<close>.
  Either way \<open>\<not> multiT M\<close>.  Empirically verified: 0/1709 anchored slices are
  \<open>multiT\<close> (len\<le>5,val\<le>2 and len\<le>4,val\<le>3, python/red_model.py).  This removes the
  \<open>multiT\<close> branch (the P-Red-equivariance blocker) from the \<open>p_6_5_Red_idem\<close>
  Red.pinduct: the recursion entry is always zero/mono.\<close>

lemma idem_anchored_not_multi:
  assumes "M \<in> anchored_slice"
  shows "\<not> multiT M"
proof -
  obtain S a b where SD: "S \<in> ST_PS \<or> (S \<in> RT_PS \<and> S \<in> PT_PS)"
      and ab: "a \<le> b" and bL: "b < Lng S" and le: "le0 S a b" and Mdef: "M = seg S a b"
    using assms by (auto simp: anchored_slice_def)
  have ST: "S \<in> T_PS"
    using SD ST_PS_T_PS by (auto simp: PT_PS_def)
  show ?thesis
  proof (cases "a = b")
    case True
    \<comment> \<open>length-1 slice: zero or mono, never multi.\<close>
    have L1: "Lng M = 1" using True by (simp add: Mdef Lng_seg)
    show ?thesis
    proof (cases "zeroT M")
      case True thus ?thesis by (simp add: multiT_def)
    next
      case nz: False
      have "le0 M 0 0" by (rule le0_refl) (simp add: L1)
      hence "leR M 0 0 (Lng M - 1)" using L1 by (simp add: leR_def)
      hence "monoT M" using nz by (simp add: monoT_def)
      thus ?thesis by (simp add: multiT_def)
    qed
  next
    case False
    hence altb: "a < b" using ab by simp
    have lr: "leR S 0 a b" using le by (simp add: leR_def)
    have "monoT (seg S a b)" by (rule m_6_2_mono_ancestor_slice[OF ST altb lr])
    thus ?thesis using Mdef by (simp add: multiT_def)
  qed
qed

end
