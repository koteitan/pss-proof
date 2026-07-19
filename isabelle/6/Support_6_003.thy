theory Support_6_003
  imports Frontier_6_019
begin

subsection \<open>§5.4 the uniform expansion step\<close>

text \<open>
  The article's system \<open>F\<close> sends \<open>M\<close> to \<open>Pred M\<close> in the two degenerate
  sub-cases (\<open>M\<^bsub>j\<^sub>1\<^esub> = (0,0)\<close>, or no unique parent) and to \<open>M[n]\<close> otherwise.
  Since \<open>M[n] = Pred M\<close> in exactly those degenerate sub-cases, the uniform
  step "\<open>M \<mapsto> M[n]\<close>" used by @{const Fval} / @{const Fdom} is faithful.
\<close>

lemma oper_degenerate_eq_Pred:
  assumes L: "Lng M > 1"
    and D: "entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0
            \<or> \<not> hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
  shows "M[n] = Pred M"
proof -
  have nz: "Lng M - 1 \<noteq> 0" using L by simp
  from D show ?thesis
  proof
    assume "entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0"
    thus ?thesis using nz by (simp add: oper_def Let_def)
  next
    assume "\<not> hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    thus ?thesis using nz by (auto simp: oper_def Let_def)
  qed
qed

end
