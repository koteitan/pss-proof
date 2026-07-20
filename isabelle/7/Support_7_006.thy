theory Support_7_006
  imports Frontier_7_009
begin

text \<open>命題（scb分解の一意性）(1) (§7.2): the \<open>(s,b)\<close>-part of an scb-decomposition
  with a fixed principal \<open>c\<close> is unique.\<close>

lemma m_7_2_scb_unique_sb:
  assumes d0: "scb_decomp t s\<^sub>0 c b\<^sub>0"
      and d1: "scb_decomp t s\<^sub>1 c b\<^sub>1"
      and tne: "t \<noteq> Trm []"
  shows "s\<^sub>0 = s\<^sub>1 \<and> b\<^sub>0 = b\<^sub>1"
proof -
  \<comment> \<open>Unfold the two scb-decompositions.\<close>
  from d0 have e0: "flatBT t = s\<^sub>0 @ c @ b\<^sub>0"
    and pc0: "isPTB_str c" and rb0: "\<forall>x \<in> set b\<^sub>0. x = RP"
    using tne by (auto simp: scb_decomp_def)
  from d1 have e1: "flatBT t = s\<^sub>1 @ c @ b\<^sub>1"
    and rb1: "\<forall>x \<in> set b\<^sub>1. x = RP"
    using tne by (auto simp: scb_decomp_def)
  \<comment> \<open>\<open>c\<close> contains a non-\<open>RP\<close> letter.\<close>
  have cne: "\<exists>x \<in> set c. x \<noteq> RP" by (rule scbuniq_isPTB_has_nonRP[OF pc0])
  \<comment> \<open>Trailing-\<open>RP\<close> count of \<open>flat t\<close> computed two ways.\<close>
  have t0: "trailRP (flatBT t) = length b\<^sub>0 + trailRP c"
    by (simp only: e0 append_assoc[symmetric]
                   scbuniq_trailRP_append_RP[OF rb0]
                   scbuniq_trailRP_prefix_indep[OF cne])
  have t1: "trailRP (flatBT t) = length b\<^sub>1 + trailRP c"
    by (simp only: e1 append_assoc[symmetric]
                   scbuniq_trailRP_append_RP[OF rb1]
                   scbuniq_trailRP_prefix_indep[OF cne])
  have lenb: "length b\<^sub>0 = length b\<^sub>1" using t0 t1 by simp
  \<comment> \<open>Equal-length all-\<open>RP\<close> blocks coincide.\<close>
  have beq: "b\<^sub>0 = b\<^sub>1" by (rule scbuniq_all_RP_eq[OF rb0 rb1 lenb])
  \<comment> \<open>Total length then pins down \<open>s\<close>.\<close>
  have eqstr: "s\<^sub>0 @ c @ b\<^sub>0 = s\<^sub>1 @ c @ b\<^sub>1" using e0 e1 by simp
  have lentot: "length s\<^sub>0 + (length c + length b\<^sub>0) = length s\<^sub>1 + (length c + length b\<^sub>1)"
    using arg_cong[OF eqstr, of length] by simp
  hence lens: "length s\<^sub>0 = length s\<^sub>1" using lenb by simp
  have "s\<^sub>0 @ (c @ b\<^sub>0) = s\<^sub>1 @ (c @ b\<^sub>1)" using eqstr by simp
  hence "s\<^sub>0 = s\<^sub>1" using lens by (simp add: append_eq_append_conv)
  thus ?thesis using beq by blast
qed

end
