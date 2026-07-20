theory Frontier_6_090
  imports Support_6_068
begin

text \<open>§6.5 monoCong COROLLARIES: the original congR target, and the headline
  系（直系先祖の Red 不変性） m_6_5_Red_le now UNCONDITIONAL -- its two carried
  hypotheses are discharged by @{thm [source] stdCA_ST_PS} (the gate-free §6.7
  bricks) and the closed form @{thm [source] m_6_5_Red_rebase}.\<close>

lemma congR_self_funpow_IncrFirst: "congR Z ((IncrFirst ^^ k) Z)"
  unfolding congR_def
proof (intro conjI allI impI)
  show "Lng Z = Lng ((IncrFirst ^^ k) Z)" by simp
next
  show "nextrel0 Z = nextrel0 ((IncrFirst ^^ k) Z)"
    using nextrel0_funpow_IncrFirst_eq by simp
next
  fix j assume "j < Lng ((IncrFirst ^^ k) Z)"
  hence "j < Lng Z" by simp
  thus "entry Z 1 j = entry ((IncrFirst ^^ k) Z) 1 j"
    using entry_funpow_IncrFirst1 by simp
qed

end
