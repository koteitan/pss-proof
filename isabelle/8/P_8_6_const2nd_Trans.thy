theory P_8_6_const2nd_Trans
  imports Support_8_C
begin

text \<open>補題（条件(V)の下での各種scb分解） (§8.5, article 5213): DEFERRED.  With
  \<open>N' = (M\<^sub>j)\<^bsub>j=j\<^sub>0\<^esub>\<^bsup>j\<^sub>1\<^esup>\<close>, \<open>L' = (M\<^sub>j)\<^bsub>j=j\<^sub>0\<^esub>\<^bsup>j\<^sub>1-\<^sub>1\<^esup> \<oplus> ((M\<^bsub>0,j\<^sub>1\<^esub>,M\<^bsub>1,j\<^sub>0\<^esub>)))\<close> and
  \<open>L\<^sub>n = M[n] \<oplus> ((M\<^bsub>0,j\<^sub>0\<^esub>+n(M\<^bsub>0,j\<^sub>1\<^esub>-M\<^bsub>0,j\<^sub>0\<^esub>), M\<^bsub>1,j\<^sub>0\<^esub>)))\<close>, the lemma asserts a unique
  \<open>(s'\<^sub>1,b'\<^sub>1) \<in> (\<Sigma>\<^bsup><\<omega>\<^esup>)\<^sup>2\<close> such that parts (1)–(5) describe scb-decompositions of
  \<open>c\<^sub>2\<close>, \<open>Trans(N')\<close>, \<open>Trans(L')\<close>, \<open>Trans(Pred N')\<close>, and closed forms for
  \<open>Trans(L\<^sub>n)\<close> and \<open>Trans(M[n])\<close> — all stated through the unexposed internal
  \<open>Trans\<close>-recursion symbols \<open>s\<^sub>1\<close>, \<open>b\<^sub>1\<close>, \<open>s'\<^sub>1\<close>, \<open>b'\<^sub>1\<close>, \<open>t\<^sub>2\<close>, \<open>c\<^sub>2\<close> (string
  concatenation/exponentiation of unexposed scb-strings).  Not faithfully
  expressible without inventing that exposure.  BLOCKING SYMBOLS:
  \<open>s\<^sub>1\<close>, \<open>b\<^sub>1\<close>, \<open>s'\<^sub>1\<close>, \<open>b'\<^sub>1\<close>, \<open>t\<^sub>2\<close>, \<open>c\<^sub>2\<close>.\<close>

text \<open>補題（条件(V)の下での基本列のscb分解） (§8.5, article 5352): DEFERRED.  Asserts a
  unique \<open>u \<in> \<nat>\<close>, \<open>(s'\<^sub>0,b'\<^sub>0) \<in> (\<Sigma>\<^bsup><\<omega>\<^esup>)\<^sup>2\<close> and \<open>t' \<in> T\<^bsub>B\<^esub>\<close> such that
  \<open>(s'\<^sub>0, D\<^sub>u t\<^sub>2, b'\<^sub>0)\<close>, \<open>(s'\<^sub>0, D\<^sub>u(t\<^sub>2 + D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>0\<^esub> 0), b'\<^sub>0)\<close>,
  \<open>(s'\<^sub>0, D\<^sub>u(t\<^sub>2 + D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>0\<^esub> t'), b'\<^sub>0)\<close> are scb-decompositions of \<open>Trans(M[n])\<close>,
  \<open>Trans(M)[m\<^sub>n]\<close>, \<open>Trans(M[n+1])\<close> respectively.  The scb-components name the
  unexposed internal \<open>Trans\<close>-recursion term \<open>t\<^sub>2\<close> (and the scb-strings
  \<open>s'\<^sub>0\<close>/\<open>b'\<^sub>0\<close>); not faithfully expressible.  BLOCKING SYMBOLS: \<open>t\<^sub>2\<close>,
  \<open>s'\<^sub>0\<close>, \<open>b'\<^sub>0\<close>.\<close>


subsection \<open>§8.6 条件(VI)の下での展開規則 (Expansion rule under condition (VI))\<close>

text \<open>This subsection (article ## 条件(VI)の下での展開規則, content.md 5482–5848)
  proves the exchange relation between \<open>Trans\<close> and the pair-sequence fundamental
  sequence under condition (VI), via three auxiliary lemmas.

  COMMON SETUP / NOTATION (as in §8.1/§8.3/§8.4):
    \<^item> \<open>j\<^sub>1 = Lng M - 1\<close>; \<open>j\<^sub>0 = parent M 0 j\<^sub>1\<close> (the row-0 nearest ancestor of
      \<open>j\<^sub>1\<close>); "\<open>M\<close> satisfies condition (VI)" is \<open>transCondVI M\<close>.
    \<^item> The Buchholz-side fundamental sequence \<open>t[k]\<close> is \<open>operB t (numBT k)\<close>; \<open><\<close> on
      \<open>T\<^bsub>B\<^esub>\<close> is \<open>lessBT\<close>; \<open>n \<in> \<nat>\<^sub>+\<close> is \<open>n \<ge> 1\<close>.  The article's iterated
      principal \<open>D\<^sub>u\<^sup>k 0\<close> (\<open>D\<^sub>u(D\<^sub>u(\<dots>(D\<^sub>u 0)))\<close>, \<open>k\<close> times) is the function
      iteration \<open>(Dpt (enat u) ^^ k) 0\<^sub>B\<close>; the iterated fundamental sequence
      \<open>t[0]\<^sup>k\<close> is \<open>((\<lambda>a. operB a (numBT 0)) ^^ k) t\<close>.
    \<^item> 公差\<open>(1,0)\<close> sequence \<open>((m+j,u))\<^bsub>j=0\<^esub>\<^bsup>j\<^sub>1\<^esup>\<close> = \<open>map (\<lambda>j. (m+j, u)) [0..<Suc j\<^sub>1]\<close>
      (first coordinate increments by \<open>1\<close>, second is constant \<open>u\<close>); 公差\<open>(1,1)\<close>
      sequence \<open>((u+j,u+j))\<^bsub>j=0\<^esub>\<^bsup>j\<^sub>1\<^esup>\<close> = \<open>diagSeq u (u+j\<^sub>1)\<close>.\<close>

text \<open>補題（公差\<open>(1,0)\<close>のペア数列の\<open>Trans\<close>の基本性質） (§8.6, content.md 5496):
  for \<open>u, m, j\<^sub>1 \<in> \<nat>\<close>, with \<open>M := ((m+j,u))\<^bsub>j=0\<^esub>\<^bsup>j\<^sub>1\<^esup> \<in> T\<^bsub>PS\<^esub>\<close>,
  \<open>Trans(M) = 0\<close> if \<open>j\<^sub>1 = 0 \<and> u = 0\<close>, and \<open>Trans(M) = D\<^sub>u\<^sup>j\<^sub>1\<^sup>+\<^sup>1 0\<close> if
  \<open>j\<^sub>1 > 0 \<or> u > 0\<close>.  Transcribable: states only \<open>Trans\<close> of an explicit sequence
  against an iterated principal term \<open>(Dpt (enat u) ^^ (j\<^sub>1+1)) 0\<^sub>B\<close>.\<close>

lemma p_8_6_const2nd_Trans:
  fixes u m j1 :: nat
  defines "M \<equiv> map (\<lambda>j. (m + j, u)) [0..<Suc j1]"
  assumes "M \<in> T_PS"
  shows "(j1 = 0 \<and> u = 0 \<longrightarrow> Trans M = 0\<^sub>B)
       \<and> (j1 > 0 \<or> u > 0 \<longrightarrow> Trans M = (Dpt (enat u) ^^ (j1 + 1)) 0\<^sub>B)"
  unfolding M_def
  by (rule m_8_6_const2nd_Trans_paper[OF assms(2)[unfolded M_def]])

end
