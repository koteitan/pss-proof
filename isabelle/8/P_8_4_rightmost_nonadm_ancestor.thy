theory P_8_4_rightmost_nonadm_ancestor
  imports Support_8_C
begin

text \<open>補題（右端の非許容直系先祖の基本性質） (§8.4): a \<open>Trans\<close>-free basic property
  of the rightmost non-admissible direct ancestor.  For \<open>M \<in> ST\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close>
  and \<open>m\<^sub>0, m\<^sub>1\<close>, with \<open>j\<^sub>1 = Lng M - 1\<close>, \<open>m\<^sub>-\<^sub>1 = Adm M m\<^sub>0\<close>,
  \<open>N = (M\<^sub>j)\<^bsub>j=m\<^sub>-\<^sub>1\<^esub>\<^bsup>j\<^sub>1\<^esup>\<close>, given \<open>(0,m\<^sub>0) <\<^bsub>M\<^esub>\<^sup>Next (0,m\<^sub>1) \<le>\<^bsub>M\<^esub> (0,j\<^sub>1)\<close>,
  if \<open>\<not> (1,m\<^sub>1-1) <\<^bsub>M\<^esub>\<^sup>Next (1,m\<^sub>1)\<close> and \<open>m\<^sub>0\<close> is non-\<open>M\<close>-admissible, then with
  \<open>J\<^sub>1 = Lng (Br (Red N)) - 1\<close>: \<open>J\<^sub>1 \<ge> 0\<close>, \<open>0 < m\<^sub>0-m\<^sub>-\<^sub>1 < TrMax (Red N)\<close>,
  \<open>m\<^sub>0-m\<^sub>-\<^sub>1 = Joints (Red N) ! J\<^sub>1\<close>, and \<open>FirstNodes (Red N) ! J\<^sub>1 = m\<^sub>1-m\<^sub>-\<^sub>1\<close>.
  This statement is \<open>Trans\<close>-free and uses only exposed defs (\<open>Adm\<close>, \<open>seg\<close>,
  \<open>Red\<close>, \<open>Br\<close>, \<open>TrMax\<close>, \<open>Joints\<close>, \<open>FirstNodes\<close>, \<open>nextR\<close>, \<open>leR\<close>, \<open>adm\<close>) — hence
  it is transcribable.  Modelling: \<open>(1,m\<^sub>1-1) <\<^bsub>M\<^esub>\<^sup>Next (1,m\<^sub>1)\<close> is
  \<open>nextR M 1 (m\<^sub>1-1) m\<^sub>1\<close>; the \<open>Joints\<close>/\<open>FirstNodes\<close> indices follow §6.4.\<close>

lemma p_8_4_rightmost_nonadm_ancestor:
  fixes M :: pairseq and m0 m1 :: nat
  defines "j1 \<equiv> Lng M - 1"
    and "mm1 \<equiv> Adm M m0"
  assumes "M \<in> ST_PS" "M \<in> PT_PS"
    and "nextR M 0 m0 m1" "leR M 0 m1 j1"
    and "\<not> nextR M 1 (m1 - 1) m1"
    and "\<not> adm M m0"
  shows "Lng (Br (Red (seg M mm1 j1))) \<ge> 1"  \<comment> \<open>article \<open>J\<^sub>1 \<ge> 0\<close> with \<open>J\<^sub>1 = Lng(Br(Red N))-1\<close>\<close>
    and "0 < m0 - mm1 \<and> m0 - mm1 < TrMax (Red (seg M mm1 j1))"
    and "m0 - mm1 = Joints (Red (seg M mm1 j1)) ! (Lng (Br (Red (seg M mm1 j1))) - 1)"
    and "FirstNodes (Red (seg M mm1 j1)) ! (Lng (Br (Red (seg M mm1 j1))) - 1) = m1 - mm1"
  unfolding j1_def mm1_def
  apply (rule m_8_4_rightmost_nonadm_ancestor(1)[OF assms(3) assms(4) assms(5)
        assms(6)[unfolded j1_def] assms(7) assms(8)])
  apply (rule m_8_4_rightmost_nonadm_ancestor(2)[OF assms(3) assms(4) assms(5)
        assms(6)[unfolded j1_def] assms(7) assms(8)])
  apply (rule m_8_4_rightmost_nonadm_ancestor(3)[OF assms(3) assms(4) assms(5)
        assms(6)[unfolded j1_def] assms(7) assms(8)])
  apply (rule m_8_4_rightmost_nonadm_ancestor(4)[OF assms(3) assms(4) assms(5)
        assms(6)[unfolded j1_def] assms(7) assms(8)])
  done

end
