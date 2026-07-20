theory P_8_1_condI_III_c1_around
  imports Support_8_C
begin

text \<open>補題（条件(I)か(III)の下での\<open>c\<^sub>1\<close>前後の具体表示） (§8.1, article 2923):
  for \<open>M \<in> RT\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close>, using the symbols of the recursive definition of
  \<open>Trans\<close> (\<open>j\<^sub>1 = Lng M - 1\<close>, \<open>j\<^sub>0 = parent M 0 j\<^sub>1\<close>, \<open>j\<^sub>-\<^sub>1 = Adm M j\<^sub>0\<close>,
  \<open>c\<^sub>1 = Mark (Pred M) j\<^sub>-\<^sub>1\<close>), if \<open>j\<^sub>0\<close> is \<open>M\<close>-admissible (\<open>adm M j\<^sub>0\<close>), \<open>j\<^sub>1 > 1\<close>
  and \<open>M\<^bsub>1,j\<^sub>0\<^esub> \<ge> M\<^bsub>1,j\<^sub>1\<^esub>\<close>, then several things hold.  Modelling notes:
    \<^item> \<open>(M\<^sub>j)\<^bsub>j=a\<^esub>\<^bsup>b\<^esup> = seg M a b\<close>; \<open>(M,m) \<in> T\<^bsub>PS\<^esub>\<^sup>Marked\<close> = \<open>(M,m) \<in> Marked\<close>;
      \<open>c\<^sub>1 \<in> PT\<^bsub>B\<^esub>\<close> = \<open>c\<^sub>1 \<in> PT_B\<close>.
    \<^item> The internal \<open>t\<^sub>2, t\<^sub>3, t\<^sub>4 \<in> T\<^bsub>B\<^esub>\<close> of \<open>Trans\<close> are not exposed, so parts
      (3)/(4) are stated with the explicit \<open>Mark\<close>-values they evaluate to:
      (3-1)/(4-1) give \<open>Mark (Pred M) j'\<^sub>-\<^sub>1 = D[M\<^sub>1\<^sub>,\<^sub>j'\<^sub>-\<^sub>1](t' +\<^sub>B c\<^sub>1)\<close> for a
      unique \<open>t' \<in> T\<^bsub>B\<^esub>\<close> (with \<open>t' = 0\<close> in the \<open>j'\<^sub>0+1 = j\<^sub>0\<close> sub-case), and
      (3-2)/(4-2) give \<open>Mark (Pred M) j'\<^sub>-\<^sub>1 = D[M\<^sub>1\<^sub>,\<^sub>j'\<^sub>-\<^sub>1](t'\<^sub>3 +\<^sub>B D[M\<^sub>1\<^sub>,\<^sub>j'\<^sub>0](t'\<^sub>4 +\<^sub>B c\<^sub>1))\<close>
      for unique \<open>(t'\<^sub>3,t'\<^sub>4) \<in> T\<^bsub>B\<^esub>\<^sup>2\<close>.
    \<^item> Part (5) is stated for \<open>n > 1\<close> with \<open>N := seg (M[n]) 0 (j\<^sub>0+(n-1)(j\<^sub>1-j\<^sub>0))\<close>;
      the internal \<open>Trans\<close>-symbols \<open>j\<^sub>1\<^sup>N, j\<^sub>0\<^sup>N, j\<^sub>-\<^sub>1\<^sup>N, t\<^sub>1\<^sup>N\<close> of \<open>N\<close> are recovered
      as \<open>Lng N - 1\<close>, \<open>parent N 0 (Lng N - 1)\<close>, \<open>Adm N (parent N 0 (Lng N - 1))\<close>,
      \<open>Trans (Pred N)\<close> respectively.

  FAITHFUL ARTICLE-FALSE STUB.  The statement below deliberately reproduces the
  article as printed.  It is false in part (1) (A20) and part (5) (A21), is a
  dependency leaf, and therefore remains a documented \<open>sorry\<close> exactly as it did in
  \<open>pss_paper\<close>.  The true content is not lost: the fully proved
  \<open>m_8_1_c1_around_part*\<close> family in \<open>Support_8_B\<close>, together with
  @{thm [source] y3u_p_8_1_c1_around_part1} and
  @{thm [source] y3u_p_8_1_c1_around_part5}, records the A20/A21-corrected parts.\<close>

lemma p_8_1_condI_III_c1_around:
  fixes M :: pairseq
  defines "j1 \<equiv> Lng M - 1"
  defines "j0 \<equiv> parent M 0 j1"
  defines "jm1 \<equiv> Adm M j0"
  defines "c1 \<equiv> Mark (Pred M) jm1"
  assumes "M \<in> RT_PS" "M \<in> PT_PS"
    and "adm M j0" "j1 > 1" "entry M 1 j0 \<ge> entry M 1 j1"
  shows
    "\<comment> \<open>(1)\<close>
     Trans (Pred M) \<noteq> 0\<^sub>B \<and> (transCondI M \<or> transCondIII M)
       \<and> Trans (seg M j0 (j1 - 1)) = c1 \<and> c1 \<in> T_B \<and> (\<exists>p. c1 = Trm [p])
   \<and> \<comment> \<open>(2)–(5): under existence of the unique next-parent \<open>j'\<^sub>0\<close> of \<open>j\<^sub>0\<close>\<close>
     (\<forall>j0'. nextR M 0 j0' j0 \<longrightarrow>
        (let jm1' = Adm M j0' in
         \<comment> \<open>(2)\<close>
         (j0' \<le> j1 - 2 \<and> (Pred M, jm1') \<in> Marked
            \<and> (seg M jm1' (j1 - 1), j0 - jm1') \<in> Marked)
         \<comment> \<open>(3) \<open>j'\<^sub>0+1 = j\<^sub>0\<close>\<close>
       \<and> (j0' + 1 = j0 \<longrightarrow>
            \<comment> \<open>(3-1)\<close>
            ((jm1' = j0' \<or> entry M 1 j0' + 1 = entry M 1 j0)
               \<longrightarrow> Mark (Pred M) jm1' = Dpt (enat (entry M 1 jm1')) c1)
          \<and> \<comment> \<open>(3-2)\<close>
            ((jm1' < j0' \<and> entry M 1 j0' \<ge> entry M 1 j0)
               \<longrightarrow> Mark (Pred M) jm1'
                     = Dpt (enat (entry M 1 jm1')) (Dpt (enat (entry M 1 j0')) c1)))
         \<comment> \<open>(4) \<open>j'\<^sub>0+1 < j\<^sub>0\<close>\<close>
       \<and> (j0' + 1 < j0 \<longrightarrow>
            \<comment> \<open>(4-1)\<close>
            ((jm1' = j0' \<or> entry M 1 j0' + 1 = entry M 1 j0)
               \<longrightarrow> (\<exists>!t2'. Mark (Pred M) jm1'
                            = Dpt (enat (entry M 1 jm1')) (t2' +\<^sub>B c1)))
          \<and> \<comment> \<open>(4-2)\<close>
            ((jm1' < j0' \<and> entry M 1 j0' \<ge> entry M 1 j0)
               \<longrightarrow> (\<exists>!t34. Mark (Pred M) jm1'
                            = Dpt (enat (entry M 1 jm1'))
                                  (fst t34 +\<^sub>B Dpt (enat (entry M 1 j0'))
                                                  (snd t34 +\<^sub>B c1)))))
         \<comment> \<open>(5)\<close>
       \<and> (\<forall>n. n > 1 \<longrightarrow>
            (let N = seg (M[n]) 0 (j0 + (n - 1) * (j1 - j0)) in
             (M[n], j0 + (n - 1) * (j1 - j0)) \<in> Marked
             \<and> nextR (M[n]) 0 j0' (j0 + (n - 1) * (j1 - j0))
             \<and> Lng N - 1 = j0 + (n - 1) * (j1 - j0)
             \<and> parent N 0 (Lng N - 1) = j0'
             \<and> Adm N (parent N 0 (Lng N - 1)) = jm1'
             \<and> Trans (Pred N) \<noteq> 0\<^sub>B
             \<and> \<not> transCondVI N))))"
  sorry

end
