theory Frontier_7_044
  imports Support_7_038
begin

text \<open>\<open>Lng (PB)\<close> is additive over \<open>+\<^sub>B\<close> (which concatenates the principal-component
  lists): \<open>Lng (PB (a +\<^sub>B b)) = Lng (PB a) + Lng (PB b)\<close>.\<close>

lemma Lng_PB_addBT: "Lng (PB (a +\<^sub>B b)) = Lng (PB a) + Lng (PB b)"
proof -
  obtain as where a: "a = Trm as" by (cases a)
  obtain bs where b: "b = Trm bs" by (cases b)
  show ?thesis using a b by (simp add: PB_def)
qed

text \<open>\<open>Lng (PB t) = 0\<close> exactly when \<open>t = 0\<^sub>B\<close>.\<close>

lemma Lng_PB_eq0_iff: "Lng (PB t) = 0 \<longleftrightarrow> t = 0\<^sub>B"
proof -
  obtain ps where tps: "t = Trm ps" by (cases t)
  show ?thesis using tps by (simp add: PB_def)
qed

end
