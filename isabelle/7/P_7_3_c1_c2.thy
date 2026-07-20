theory P_7_3_c1_c2
  imports Frontier_7_021
begin

text \<open>命題（\<open>c\<^sub>1\<close>と\<open>c\<^sub>2\<close>の大小関係）claim (3), now UNCONDITIONAL: \<open>lessBT c\<^sub>1 c\<^sub>2\<close>.\<close>

lemma transC1_lessBT_transC2_full:
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and J1pos: "transJ1 M > 0" and T1: "transT1 M \<noteq> 0\<^sub>B"
  shows "lessBT (transC1 M) (transC2 M)"
  by (rule transC1_lessBT_transC2_modNA[OF MR MP J1pos T1 NAbound_holds[OF MR MP T1]])


text \<open>命題（\<open>c\<^sub>1\<close>と\<open>c\<^sub>2\<close>の大小関係） (§7.3, article 2270): for \<open>M \<in> RT\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close>,
  using the symbols of the recursive definition of \<open>Trans\<close> (now exposed as
  \<open>transC1\<close>/\<open>transC2\<close>), if \<open>j\<^sub>1 > 0\<close> and \<open>t\<^sub>1 \<noteq> 0\<close> then \<open>c\<^sub>1\<close> and \<open>c\<^sub>2\<close> are
  principal (単項 = a single principal component, \<open>Lng (PB \<cdot>) = 1\<close>) and
  \<open>c\<^sub>1 < c\<^sub>2\<close> (\<open>lessBT\<close>).\<close>

lemma p_7_3_c1_c2:
  assumes "M \<in> RT_PS" "M \<in> PT_PS" "transJ1 M > 0" "transT1 M \<noteq> 0\<^sub>B"
  shows "Lng (PB (transC1 M)) = 1" and "Lng (PB (transC2 M)) = 1"
    and "lessBT (transC1 M) (transC2 M)"
proof -
  show "Lng (PB (transC1 M)) = 1"
    by (rule transC1_single_principal[OF assms])
  show "Lng (PB (transC2 M)) = 1"
    by (rule transC2_single_principal)
  show "lessBT (transC1 M) (transC2 M)"
    by (rule transC1_lessBT_transC2_full[OF assms])
qed

end
