theory Frontier_7_011
  imports Support_7_007
begin

subsection \<open>§7.2 命題（scb分解の合成則） — m_7_2_scb_compose\<close>

text \<open>
  Part (1) (the composition rule proper): if \<open>(s\<^sub>0, flat c\<^sub>0, b\<^sub>0)\<close> is an
  scb-decomposition of \<open>t\<close> with \<open>c\<^sub>0\<close> principal (\<open>c\<^sub>0 = Trm [p]\<close>), and
  \<open>(s\<^sub>1, c\<^sub>1, b\<^sub>1)\<close> is an scb-decomposition of \<open>c\<^sub>0\<close>, then
  \<open>(s\<^sub>0 \<frown> s\<^sub>1, c\<^sub>1, b\<^sub>1 \<frown> b\<^sub>0)\<close> is an scb-decomposition of \<open>t\<close>.

  The article ("scb分解の定義より即座に従う") proves this directly from the
  definition.  The flat string splits as
  \<open>flat t = s\<^sub>0 \<frown> flat c\<^sub>0 \<frown> b\<^sub>0 = s\<^sub>0 \<frown> (s\<^sub>1 \<frown> c\<^sub>1 \<frown> b\<^sub>1) \<frown> b\<^sub>0\<close>; the
  right-tail \<open>b\<^sub>1 \<frown> b\<^sub>0\<close> is all \<open>\<^bold>)\<close>; and the principal-component condition on
  \<open>c\<^sub>1\<close> holds because \<open>c\<^sub>0 = Trm [p] \<noteq> Trm []\<close>, so \<open>(s\<^sub>1, c\<^sub>1, b\<^sub>1)\<close> being an
  scb-decomposition of \<open>c\<^sub>0\<close> already forces \<open>isPTB_str c\<^sub>1\<close>.
\<close>

lemma scbcomp_compose1:
  assumes c0prin: "\<exists>p. c\<^sub>0 = Trm [p]"
    and d0: "scb_decomp t s\<^sub>0 (flatBT c\<^sub>0) b\<^sub>0"
    and d1: "scb_decomp c\<^sub>0 s\<^sub>1 c\<^sub>1 b\<^sub>1"
  shows "scb_decomp t (s\<^sub>0 @ s\<^sub>1) c\<^sub>1 (b\<^sub>1 @ b\<^sub>0)"
proof -
  from c0prin obtain p where c0: "c\<^sub>0 = Trm [p]" by blast
  hence c0ne: "c\<^sub>0 \<noteq> Trm []" by simp
  \<comment> \<open>flat split\<close>
  from d0 have ft: "flatBT t = s\<^sub>0 @ flatBT c\<^sub>0 @ b\<^sub>0"
    unfolding scb_decomp_def by simp
  from d1 have fc0: "flatBT c\<^sub>0 = s\<^sub>1 @ c\<^sub>1 @ b\<^sub>1"
    unfolding scb_decomp_def by simp
  have split: "flatBT t = (s\<^sub>0 @ s\<^sub>1) @ c\<^sub>1 @ (b\<^sub>1 @ b\<^sub>0)"
    using ft fc0 by simp
  \<comment> \<open>principal-component condition on \<open>c\<^sub>1\<close>: from \<open>c\<^sub>0 \<noteq> 0\<close>\<close>
  from d1 c0ne have pc1: "isPTB_str c\<^sub>1"
    unfolding scb_decomp_def by simp
  \<comment> \<open>right tail all \<open>\<^bold>)\<close>\<close>
  from d0 have rb0: "\<forall>x \<in> set b\<^sub>0. x = RP" unfolding scb_decomp_def by simp
  from d1 have rb1: "\<forall>x \<in> set b\<^sub>1. x = RP" unfolding scb_decomp_def by simp
  have rtail: "\<forall>x \<in> set (b\<^sub>1 @ b\<^sub>0). x = RP" using rb0 rb1 by auto
  show ?thesis
    unfolding scb_decomp_def
    using split pc1 rtail by simp
qed

end
