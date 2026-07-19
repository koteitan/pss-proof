theory Support_6_014
  imports Frontier_6_031
begin

text \<open>§6.8 d1pos H1 brick (empirical \<open>python/d1pos_fold_shape.py\<close>, 550/0): a
  block-start-anchored \<open>le0\<close> slice \<open>seg (M[n]) a b\<close> of a d0pos (\<open>i\<^sub>1=1\<close>) oper is a
  single \<open>monoT\<close> P-component.  \<open>monoT S = (\<not> zeroT S \<and> leR S 0 0 (Lng S-1))\<close>;
  \<open>\<not> zeroT\<close> from \<open>1 < Lng S\<close> (as \<open>a < b\<close>); the \<open>leR\<close>/\<open>le0\<close> body transfers from the
  hypothesis \<open>le0 (M[n]) a b\<close> across the slice via @{thm [source] adm_le0_seg}.\<close>

lemma oper_d1pos_seg_mono:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and aq: "a = parent M 1 (Lng M - 1)
                + q * (Lng M - 1 - parent M 1 (Lng M - 1))"
    and qn: "q < n"
    and ab: "a < b"
    and blt: "b < Lng ((M::pairseq)[n])"
    and leab: "le0 ((M::pairseq)[n]) a b"
  shows "monoT (seg ((M::pairseq)[n]) a b)"
proof -
  let ?N = "(M::pairseq)[n]"
  let ?S = "seg ?N a b"
  \<comment> \<open>\<open>Lng ?S = Suc b - a > 1\<close> since \<open>a < b\<close>; hence \<open>\<not> zeroT ?S\<close> (which needs \<open>Lng = 1\<close>)\<close>
  have LS: "Lng ?S = Suc b - a" by (simp only: Lng_seg)
  have LSgt1: "1 < Lng ?S" using LS ab by simp
  have nzS: "\<not> zeroT ?S"
  proof
    assume "zeroT ?S"
    hence "Lng ?S = 1" by (simp add: zeroT_def)
    thus False using LSgt1 by simp
  qed
  \<comment> \<open>endpoint bookkeeping: \<open>Lng ?S - 1 = b - a\<close>\<close>
  have LSm1: "Lng ?S - 1 = b - a" using LS ab by simp
  \<comment> \<open>transfer \<open>le0\<close> from \<open>?N\<close> to the slice \<open>?S\<close> (@{thm [source] adm_le0_seg})\<close>
  have aleb: "a \<le> b" using ab by simp
  have b0le: "b - a \<le> b - a" by (rule order.refl)
  have z0le: "(0::nat) \<le> b - a" by simp
  have tr: "le0 ?S 0 (b - a) = le0 ?N (a + 0) (a + (b - a))"
    by (rule adm_le0_seg[where M="?N" and j0'=a and j1'=b and a=0 and b="b - a",
          OF blt z0le b0le aleb])
  have ab0: "a + 0 = a" by simp
  have abb: "a + (b - a) = b" using aleb by simp
  have le0S: "le0 ?S 0 (b - a)" using tr ab0 abb leab by simp
  \<comment> \<open>\<open>leR ?S 0 0 (Lng ?S - 1) = le0 ?S 0 (b - a)\<close>\<close>
  have leRS: "leR ?S 0 0 (Lng ?S - 1)" using le0S LSm1 by (simp add: leR_def)
  show ?thesis using nzS leRS by (simp add: monoT_def)
qed

end
