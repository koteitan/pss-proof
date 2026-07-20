theory P_8_3_TransCondII_oper_descend
  imports Support_8_C
begin

text \<open>命題（条件(II)の下での\<open>Trans\<close>と基本列の交換関係） (§8.3, article 3958): for
  \<open>M \<in> ST\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close> and \<open>n \<in> \<nat>\<^sub>+\<close>, with the symbols introduced in the
  \<open>Trans\<close> recursion, \<open>L := Red((M\<^sub>j)\<^bsub>j=j\<^sub>-\<^sub>1\<^esub>\<^bsup>j\<^sub>1\<^esup>)\<close>, if \<open>j\<^sub>1 > 1\<close> and \<open>M\<close>
  satisfies condition (II), then, with \<open>m\<^sub>n := n-1\<close> or \<open>m\<^sub>n := n-2\<close> according to
  whether the left end of \<open>P\<^bsub>B\<^esub>(t\<^sub>2)\<^bsub>J\<^sub>1\<^esub>\<close> is \<open>D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>0\<^esub>\<close> or not:
  (1) if \<open>m\<^sub>n = -1\<close> then \<open>Trans(M[n]) = s\<^sub>1 D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>-\<^sub>1\<^esub> t\<^sub>2 b\<^sub>1\<close>;
  (2) if \<open>m\<^sub>n \<ge> 0\<close> then \<open>Trans(M[n]) = Trans(M)[m\<^sub>n]\<close>;
  (3) \<open>Mark(M[n], j\<^sub>-\<^sub>1) = D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>-\<^sub>1\<^esub>(t\<^sub>3 + (D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>0\<^esub> t\<^sub>4) \<times> (m\<^sub>n+1)))\<close>;
  (4) \<open>Trans(M[n]) < Trans(M)\<close>.

  MODELLING NOTE: conclusions (1)–(3) are stated in terms of the \<open>Trans\<close>-recursion
  locals \<open>s\<^sub>1, b\<^sub>1, t\<^sub>2, t\<^sub>3, t\<^sub>4, c\<^sub>1, c\<^sub>2, v, J\<^sub>1\<close> and the integer-valued index
  \<open>m\<^sub>n \<in> \<nat> \<union> {-1}\<close>, which the \<open>Trans\<close> / \<open>Mark\<close> \<open>function\<close> does not expose as
  separate functions (cf. the deferred §7.3 命題（\<open>c\<^sub>1\<close>と\<open>c\<^sub>2\<close>の大小関係）, which
  is likewise "to be stated once they are exposed").  They are therefore deferred
  to the mechanization, where these locals will be defined.  Only the
  self-contained descent conclusion (4) is transcribed here.\<close>

lemma p_8_3_TransCondII_oper_descend:
  fixes M :: pairseq
  assumes "M \<in> ST_PS" "M \<in> PT_PS" "0 < n"
    and "Lng M - 1 > 1"
    and "transCondII M"
  shows "lessBT (Trans (M[n])) (Trans M)"
  by (rule y5_8_3_TransCondII_oper_descend[OF assms])

end
