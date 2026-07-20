theory P_7_3_Mark_IncrFirst_Red
  imports P_7_3_Trans_IncrFirst_Red
begin

text \<open>Hence \<open>RedStab\<close> --- the side condition of the four \<section>7 propositions proved in
  the previous round --- is ALL of \<open>T\<^bsub>PS\<^esub>\<close>, with \<open>k = 2\<close>.\<close>

theorem y3r_RedStab_TPS:
  assumes MT: "M \<in> T_PS"
  shows "RedStab M"
  by (rule y3s_RedStab_of_Red2[OF y3r_RED2[OF MT]])

text \<open>命題（\<open>Mark\<close>の\<open>(IncrFirst,Red,P)\<close>不変性） (1) (§7.3, 2246).\<close>

lemma p_7_3_Mark_IncrFirst_Red:
  assumes "(M, m) \<in> Marked"
  shows "Mark M m = Mark (Red M) m" and "Mark M m = Mark (IncrFirst M) m"
proof -
  have MT: "M \<in> T_PS" using assms by (simp add: Marked_def)
  have F: "(Red ^^ 2) M \<in> RT_PS"
    using y3r_RED2[OF MT] by (simp add: numeral_2_eq_2)
  have FM: "Mark M m = Mark ((Red ^^ 2) M) m"
    by (rule y3s_Mark_funpow_Red[OF F])
  have FR: "(Red ^^ 1) (Red M) \<in> RT_PS"
    using F by (simp add: numeral_2_eq_2)
  have RM: "Mark (Red M) m = Mark ((Red ^^ 1) (Red M)) m"
    by (rule y3s_Mark_funpow_Red[OF FR])
  show "Mark M m = Mark (Red M) m" using FM RM by (simp add: numeral_2_eq_2)
  have RI: "Red (IncrFirst M) = Red M" by (rule m_6_5_Red_IncrFirst[OF MT])
  have FI: "(Red ^^ 2) (IncrFirst M) \<in> RT_PS"
    using F RI by (simp add: numeral_2_eq_2)
  have IM: "Mark (IncrFirst M) m = Mark ((Red ^^ 2) (IncrFirst M)) m"
    by (rule y3s_Mark_funpow_Red[OF FI])
  show "Mark M m = Mark (IncrFirst M) m"
    using FM IM RI by (simp add: numeral_2_eq_2)
qed

end
