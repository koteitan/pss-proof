theory P_7_3_Trans_IncrFirst_Red
  imports Support_7_051
begin

text \<open>\<^bold>\<open>RED2\<close> --- the \<section>6 fact that closes the \<section>7 scope gap.\<close>

theorem y3r_RED2:
  assumes MT: "M \<in> T_PS"
  shows "Red (Red M) \<in> RT_PS"
  by (rule y3r_Red_reduced_of_diag[OF y3r_Red_TPS[OF MT] y3r_Red_comp_diag[OF MT]])

text \<open>命題（\<open>Trans\<close>の\<open>(IncrFirst,Red)\<close>不変\<open>P\<close>同変性） (1) (§7.3, 2234).\<close>

lemma p_7_3_Trans_IncrFirst_Red:
  assumes "M \<in> T_PS"
  shows "Trans M = Trans (Red M)" and "Trans M = Trans (IncrFirst M)"
proof -
  have F: "(Red ^^ 2) M \<in> RT_PS"
    using y3r_RED2[OF assms] by (simp add: numeral_2_eq_2)
  have FM: "Trans M = Trans ((Red ^^ 2) M)"
    by (rule y3s_Trans_funpow_Red[OF F])
  have FR: "(Red ^^ 1) (Red M) \<in> RT_PS"
    using F by (simp add: numeral_2_eq_2)
  have RM: "Trans (Red M) = Trans ((Red ^^ 1) (Red M))"
    by (rule y3s_Trans_funpow_Red[OF FR])
  show "Trans M = Trans (Red M)" using FM RM by (simp add: numeral_2_eq_2)
  have RI: "Red (IncrFirst M) = Red M" by (rule m_6_5_Red_IncrFirst[OF assms])
  have FI: "(Red ^^ 2) (IncrFirst M) \<in> RT_PS"
    using F RI by (simp add: numeral_2_eq_2)
  have IM: "Trans (IncrFirst M) = Trans ((Red ^^ 2) (IncrFirst M))"
    by (rule y3s_Trans_funpow_Red[OF FI])
  show "Trans M = Trans (IncrFirst M)"
    using FM IM RI by (simp add: numeral_2_eq_2)
qed

end
