theory P_8_6_Trans_fseq_condVI
  imports P_8_6_trailing_principal_annihilable
begin

text \<open>命題（条件(VI)の下での\<open>Trans\<close>と基本列の交換関係） (§8.6, content.md 5484):
  for \<open>M \<in> ST\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close> and \<open>n \<in> \<nat>\<^sub>+\<close>, using the symbols of the \<open>Trans\<close>
  recursion, set \<open>m\<^sub>n := n-2\<close> if \<open>j\<^sub>0\<close> is \<open>M\<close>-admissible (\<open>adm M j\<^sub>0\<close>) and
  \<open>m\<^sub>n := n-1\<close> otherwise; if \<open>j\<^sub>1 > 1\<close> and \<open>M\<close> satisfies condition (VI), then:
    (1) if \<open>m\<^sub>n = -1\<close> (i.e. \<open>n = 1\<close> and \<open>j\<^sub>0\<close> is \<open>M\<close>-admissible), there is
        \<open>k \<in> \<nat>\<close> with \<open>1 < k \<le> M\<^bsub>1,j\<^sub>1\<^esub>+1\<close> and
        \<open>Trans(M[n]) = Trans(M)[0]\<^sup>k\<close>;
    (2) if \<open>m\<^sub>n \<ge> 0\<close>, then \<open>Trans(M[n]) = Trans(M)[m\<^sub>n]\<close>;
    (3) \<open>Trans(M[n]) < Trans(M)\<close>.
  Modelling note: the integer-valued index \<open>m\<^sub>n \<in> \<nat> \<union> {-1}\<close> is fully determined
  by \<open>n\<close> and the exposed predicate \<open>adm M j\<^sub>0\<close> (\<open>j\<^sub>0 = parent M 0 (Lng M - 1)\<close>),
  so it need not be exposed as a separate \<open>Trans\<close>-internal: the case \<open>m\<^sub>n = -1\<close>
  is \<open>n = 1 \<and> adm M j\<^sub>0\<close>, the value of \<open>m\<^sub>n\<close> in case (2) is \<open>n - 2\<close> under
  \<open>adm M j\<^sub>0\<close> (here \<open>n \<ge> 2\<close>) and \<open>n - 1\<close> otherwise.  Hence all three conclusions
  are transcribable without exposing the \<open>Trans\<close>-recursion locals
  \<open>s\<^sub>1/c\<^sub>1/c\<^sub>2/b\<^sub>1/t\<^sub>2/v\<close>.  \<open>Trans(M)[0]\<^sup>k = ((\<lambda>a. operB a (numBT 0)) ^^ k) (Trans M)\<close>;
  \<open>Trans(M)[m\<^sub>n] = operB (Trans M) (numBT m\<^sub>n)\<close>.

  FAITHFUL UNPROVEN STUB.  Main proves the non-admissible exchange and the
  admissible \<open>n \<ge> 2\<close>/strict-descent parts separately as
  @{thm [source] c6nx_condVI_exch_nadm_uncond},
  @{thm [source] c613x_condVI_exch_adm}, and @{thm [source] y5_Trans_descend}.
  It does not prove the full printed conjunction as one theorem.  The former
  A34/A37 objections to the exceptional \<open>[0]\<close>-orbit leg are retracted in
  \<open>corrections-old.md\<close>: with the post-A23 \<open>operB\<close>, the printed
  existential claim is true.  The article wrapper therefore remains a documented
  \<open>sorry\<close> only because it is unproved in main, with all proved parts retained.\<close>

lemma p_8_6_Trans_fseq_condVI:
  fixes M :: pairseq and n :: nat
  defines "j0 \<equiv> parent M 0 (Lng M - 1)"
  assumes "M \<in> ST_PS" "M \<in> PT_PS" "0 < n"
    and "Lng M - 1 > 1" "transCondVI M"
  shows "\<comment> \<open>(1) the case \<open>m\<^sub>n = -1\<close>, i.e. \<open>n = 1 \<and> adm M j\<^sub>0\<close>\<close>
         (n = 1 \<and> adm M j0 \<longrightarrow>
            (\<exists>k. 1 < k \<and> k \<le> entry M 1 (Lng M - 1) + 1
               \<and> Trans (M[n]) = ((\<lambda>a. operB a (numBT 0)) ^^ k) (Trans M)))
       \<and> \<comment> \<open>(2) the case \<open>m\<^sub>n \<ge> 0\<close>, with \<open>m\<^sub>n = n-2\<close> if \<open>adm M j\<^sub>0\<close> else \<open>n-1\<close>\<close>
         (\<not> (n = 1 \<and> adm M j0) \<longrightarrow>
            Trans (M[n]) = operB (Trans M) (numBT (if adm M j0 then n - 2 else n - 1)))
       \<and> \<comment> \<open>(3)\<close>
         lessBT (Trans (M[n])) (Trans M)"
  sorry

end
