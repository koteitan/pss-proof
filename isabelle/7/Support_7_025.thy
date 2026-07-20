theory Support_7_025
  imports P_7_4_Mark_nextAdm
begin

text \<open>\<open>MarkedB\<close> is antisymmetric: a Buchholz term and a marked block of it that
  each contain the other as a marked block must coincide (length count forces the
  surrounding scb-strings empty, then \<open>flatBT\<close> injectivity).  Used for the (2)\<Rightarrow>(1)
  direction of "Mark preserves order".\<close>

lemma MarkedB_antisym:
  assumes A1: "(t, c) \<in> MarkedB" and A2: "(c, t) \<in> MarkedB"
  shows "t = c"
proof -
  from A1 obtain s b where d1: "scb_decomp t s (flatBT c) b" by (auto simp: MarkedB_def)
  from A2 obtain s' b' where d2: "scb_decomp c s' (flatBT t) b'" by (auto simp: MarkedB_def)
  have e1: "flatBT t = s @ flatBT c @ b" using d1 by (simp add: scb_decomp_def)
  have e2: "flatBT c = s' @ flatBT t @ b'" using d2 by (simp add: scb_decomp_def)
  have l1: "length (flatBT t) = length s + length (flatBT c) + length b"
    using arg_cong[OF e1, of length] by simp
  have l2: "length (flatBT c) = length s' + length (flatBT t) + length b'"
    using arg_cong[OF e2, of length] by simp
  have ls: "length s = 0" using l1 l2 by linarith
  have lb: "length b = 0" using l1 l2 by linarith
  have "flatBT t = flatBT c" using e1 ls lb by simp
  thus "t = c" by (rule m_7_flatBT_inj)
qed

end
