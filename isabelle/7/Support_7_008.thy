theory Support_7_008
  imports Frontier_7_011
begin

text \<open>
  Part (2): if \<open>(s, c, b)\<close> is an scb-decomposition of \<open>t\<close>, then
  \<open>(D\<^sub>v s, c, b)\<close> is one of \<open>D\<^sub>v t\<close>.  This holds whenever the principal-component
  side-condition on \<open>c\<close> is already available (\<open>isPTB_str c\<close>) — which is the case
  for every \<open>t \<noteq> Trm []\<close> via \<open>scb_decomp\<close>, and for \<open>t = Trm []\<close> only when the
  chosen \<open>c\<close> happens to be a principal string.  The flat string prepends the
  \<open>D\<^sub>v\<close> symbol: \<open>flat (D\<^sub>v t) = D\<^sub>v \<frown> flat t = (D\<^sub>v \<frown> s) \<frown> c \<frown> b\<close>.
\<close>

lemma scbcomp_compose2_PT:
  assumes d: "scb_decomp t s c b"
    and pc: "isPTB_str c"
  shows "scb_decomp (Dpt (enat v) t) (Dsym (enat v) # s) c b"
proof -
  from d have ft: "flatBT t = s @ c @ b" unfolding scb_decomp_def by simp
  have fD: "flatBT (Dpt (enat v) t) = (Dsym (enat v) # s) @ c @ b"
    using ft by simp
  from d have rb: "\<forall>x \<in> set b. x = RP" unfolding scb_decomp_def by simp
  show ?thesis
    unfolding scb_decomp_def
    using fD pc rb by simp
qed

end
