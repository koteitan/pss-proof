theory Support_6_005
  imports P_6_5_Lng_Red
begin

subsection \<open>§6.5 命題（単項性と Red の関係）の補助事実 (content.md 946-958)\<close>

text \<open>m: fact1 (length).  With \<open>m\<^sub>1\<^sub>0 = M\<^bsub>1,0\<^esub> > 0\<close> and
  \<open>arg = ((j,j))\<^bsub>j=0\<^esub>\<^bsup>m\<^sub>1\<^sub>0-1\<^esup> \<oplus> IncrFirst\<^bsup>m\<^sub>1\<^sub>0\<^esup>(M)\<close>, the diagonal prefix has length
  \<open>m\<^sub>1\<^sub>0\<close> and \<open>IncrFirst\<^bsup>m\<^sub>1\<^sub>0\<^esup>(M)\<close> has length \<open>Lng M\<close>; since \<open>arg \<in> T\<^sub>PS\<close>,
  @{thm [source] m_6_5_Lng_Red} gives \<open>Lng (Red arg) = Lng arg = Lng M + m\<^sub>1\<^sub>0\<close>.
  (At \<open>m\<^sub>1\<^sub>0 = 0\<close> the diagonal prefix is \<open>diagSeq 0 (0-1) = [(0,0)]\<close> of length 1, so
  the formula needs \<open>m\<^sub>1\<^sub>0 > 0\<close>, which is exactly the §6.5 branch [17] regime.)\<close>

lemma m_6_5_monoT_Red_fact1_Lng:
  assumes MT: "M \<in> T_PS" and m10pos: "0 < entry M 1 0"
  shows "Lng (Red (diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ (entry M 1 0)) M))
           = Lng M + entry M 1 0"
proof -
  let ?m10 = "entry M 1 0"
  let ?arg = "diagSeq 0 (?m10 - 1) @ (IncrFirst ^^ ?m10) M"
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have funpow_ne: "(IncrFirst ^^ ?m10) M \<noteq> []"
    using Mne by (metis Lng_funpow_IncrFirst length_0_conv)
  have arg_T: "?arg \<in> T_PS" using funpow_ne by (simp add: T_PS_def)
  have Ldiag: "Lng (diagSeq 0 (?m10 - 1)) = ?m10"
    using m10pos by (simp del: upt_Suc)
  have Lfun: "Lng ((IncrFirst ^^ ?m10) M) = Lng M" by simp
  have Larg: "Lng ?arg = Lng M + ?m10"
    using Ldiag Lfun by simp
  show ?thesis using m_6_5_Lng_Red[OF arg_T] Larg by simp
qed

end
