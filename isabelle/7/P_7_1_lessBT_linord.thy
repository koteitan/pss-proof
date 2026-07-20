theory P_7_1_lessBT_linord
  imports Frontier_7_003
begin

\<comment> \<open>----  Main lemma  ----\<close>

lemma m_7_1_lessBT_linord:
  \<comment> \<open>m: 補題（\<open><\<close> は狭義全順序）([Buc1] Lemma 2.1, §7.1)\<close>
  shows "\<not> lessBT t t"
    and "lessBT a b \<Longrightarrow> lessBT b c \<Longrightarrow> lessBT a c"
    and "lessBT a b \<or> a = b \<or> lessBT b a"
  using lessBT_irrefl lessBT_trans lessBT_total by blast+

text \<open>[Buc1] Lemma 2.1: \<open><\<close> is a strict linear order on \<open>T\<close> — irreflexive,
  transitive, and trichotomous (the latter gives totality and asymmetry).\<close>

lemma p_7_1_lessBT_linord:
  shows "\<not> lessBT t t"
    and "lessBT a b \<Longrightarrow> lessBT b c \<Longrightarrow> lessBT a c"
    and "lessBT a b \<or> a = b \<or> lessBT b a"
  using m_7_1_lessBT_linord by blast+

end
