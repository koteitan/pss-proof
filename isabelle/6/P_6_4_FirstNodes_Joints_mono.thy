theory P_6_4_FirstNodes_Joints_mono
  imports Support_6_002
begin

text \<open>系（\<open>FirstNodes\<close>と\<open>Joints\<close>の単調性）.  (\<open>J\<^sub>1' < Lng (Br M)\<close>: see above.)\<close>

text \<open>NOTE (correction A3): the article's statement (4),
  \<open>\<forall>i\<in>{0,1}. M\<^bsub>i,Joints J0'\<^esub> > M\<^bsub>i,Joints J1'\<^esub>\<close> (strict), is \<^bold>\<open>false\<close>: distinct
  branches may share a trunk joint, e.g. for the standard mono pair sequence
  \<open>(0,0)(1,1)(2,1)(3,1)(2,0)\<close> both branches join at index 1, so
  \<open>Joints = [1,1]\<close> and (4) reads \<open>1 > 1\<close>.  We transcribe the corrected statement
  with parts (1)(2)(3) only (the article's "(4) follows immediately from (3)"
  overlooks that (3) is non-strict).  See @{file "../../corrections.md"} A3.\<close>

text \<open>m: 系（\<open>FirstNodes\<close>と\<open>Joints\<close>の単調性） — discharges the corrected
  @{text p_6_4_FirstNodes_Joints_mono} (parts (1)(2)(3); the article's
  strict part (4) is false, correction A3).  Identical to
  @{thm [source] m_6_4_FirstNodes_Joints_mono_aux}.\<close>

lemma m_6_4_FirstNodes_Joints_mono:
  assumes "M \<in> PT_PS" "J0' < J1'" "J1' < Lng (Br M)"
  shows "FirstNodes M ! J0' \<le> FirstNodes M ! J1'
       \<and> Joints M ! J0' \<ge> Joints M ! J1'
       \<and> entry M 0 (FirstNodes M ! J0') \<ge> entry M 0 (FirstNodes M ! J1')"
  by (rule m_6_4_FirstNodes_Joints_mono_aux[OF assms])

lemma p_6_4_FirstNodes_Joints_mono:
  assumes "M \<in> PT_PS" "J0' < J1'" "J1' < Lng (Br M)"
  shows "FirstNodes M ! J0' \<le> FirstNodes M ! J1'
       \<and> Joints M ! J0' \<ge> Joints M ! J1'
       \<and> entry M 0 (FirstNodes M ! J0') \<ge> entry M 0 (FirstNodes M ! J1')"
  using assms by (rule m_6_4_FirstNodes_Joints_mono)

end
