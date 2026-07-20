theory P_7_4_Mark_Trans_repr
  imports Support_7_033
begin

\<comment> \<open>§7.4 keystone fully proven (Step 4): Mark = Trans of the backward slice.\<close>
lemma m_7_4_Mark_Trans_repr:
  assumes "(M, m) \<in> Marked" and "M \<in> RT_PS" and "m < Lng M - 1"
  shows "Mark M m = Trans (seg M m (Lng M - 1))"
  using m_7_4_Mark_Trans_repr_aux assms by blast

text \<open>命題（\<open>Mark\<close>の\<open>Trans\<close>による表示） (§7.4, article 2490): for any
  \<open>(M,m) \<in> T\<^bsub>PS\<^esub>\<^sup>Marked\<close>, set \<open>j\<^sub>1 := Lng M - 1\<close>; if \<open>j\<^sub>1 - m > 0\<close> then
  \<open>Mark(M, m) = Trans((M\<^sub>j)\<^bsub>j=m\<^esub>\<^bsup>j\<^sub>1\<^esup>)\<close>, i.e. the marked value at column \<open>m\<close> equals
  the \<open>Trans\<close> of the backward slice from \<open>m\<close> to the last column.  The article
  reduces to \<open>M \<in> RT\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close> via the \<open>(IncrFirst,Red,P)\<close>-invariances; as with
  the other §7.4 propositions we transcribe the \<open>M \<in> RT\<^bsub>PS\<^esub>\<close> form (the general
  \<open>T\<^bsub>PS\<^esub>\<close> form awaits the §6 \<open>P\<close>-\<open>Red\<close>-equivariance).  \<open>(M\<^sub>j)\<^bsub>j=m\<^esub>\<^bsup>j\<^sub>1\<^esup> = seg M m (Lng M - 1)\<close>.
  Mechanized immediately above as \<open>m_7_4_Mark_Trans_repr\<close> (fully proven, no
  \<open>sorry\<close>).\<close>

lemma p_7_4_Mark_Trans_repr:
  assumes "(M, m) \<in> Marked" "M \<in> RT_PS"
    and "m < Lng M - 1"
  shows "Mark M m = Trans (seg M m (Lng M - 1))"
  using assms by (rule m_7_4_Mark_Trans_repr)

end
