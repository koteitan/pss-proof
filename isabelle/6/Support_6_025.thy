theory Support_6_025
  imports P_6_8_standard_slice_Br_descending
begin

subsection \<open>§6.6 補題（簡約性と係数の基本性質）への部品: branch-6 rebase は row0\<ge>row1 を保つ\<close>

text \<open>
  m: The §6.5 \<open>Red\<close> non-core branch [17] (\<open>m\<^sub>1\<^sub>0 = M\<^bsub>1,0\<^esub> > 0\<close>, map-branch firing)
  outputs
    \<open>map (\<lambda>j. (N\<^bsub>0,j\<^esub> - N\<^bsub>0,m\<^esub> + N\<^bsub>1,m\<^esub>, N\<^bsub>1,j\<^esub>)) [m..<Suc jN]\<close>
  where \<open>N = Red(\<dots>)\<close> and \<open>m = m\<^sub>1\<^sub>0\<close>.  Empirically (python/red_model, 16704/16704
  branch-6 firings) the rebase node is diagonal: \<open>N\<^bsub>0,m\<^esub> = N\<^bsub>1,m\<^esub>\<close>; and the inner
  Red output \<open>N\<close> satisfies \<open>N\<^bsub>0,j\<^esub> \<ge> N\<^bsub>1,j\<^esub>\<close> (the structural row-0-dominance fact,
  verified 7380/7380).  This lemma is the purely-algebraic consequence: under
  exactly those two hypotheses the rebased output is again row-0-dominant.

  It is A4-INDEPENDENT (no \<open>Red\<close> unfolding, no §6.5 / \<open>p_*\<close> citation): it is the
  local bridge step the article's 補題（簡約性と係数の基本性質） uses in the
  non-core \<open>M\<^bsub>1,0\<^esub> > 0\<close> case once the §6.5 firing/diagonality facts are available.

  Key arithmetic: with \<open>N\<^bsub>0,m\<^esub> = N\<^bsub>1,m\<^esub> = c\<close> the rebased row 0 at \<open>j\<close> is
  \<open>N\<^bsub>0,j\<^esub> - c + c \<ge> N\<^bsub>0,j\<^esub> \<ge> N\<^bsub>1,j\<^esub>\<close> (nat: \<open>x - c + c \<ge> x\<close> always), while the
  rebased row 1 is \<open>N\<^bsub>1,j\<^esub>\<close>.
\<close>

lemma m_6_6_rebase_row0_ge_row1:
  fixes N :: pairseq and m jN :: nat
  defines "R \<equiv> map (\<lambda>j. (entry N 0 j - entry N 0 m + entry N 1 m, entry N 1 j))
                    [m..<Suc jN]"
  assumes diag: "entry N 0 m = entry N 1 m"
    and dom: "\<And>j. m \<le> j \<Longrightarrow> j \<le> jN \<Longrightarrow> entry N 1 j \<le> entry N 0 j"
    and jl: "k < Lng R"
  shows "entry R 1 k \<le> entry R 0 k"
proof -
  \<comment> \<open>\<open>Lng R = Suc jN - m\<close>, so \<open>k < Suc jN - m\<close>, i.e. \<open>m + k \<le> jN\<close>.\<close>
  have LR: "Lng R = Suc jN - m" using R_def by (simp del: upt_Suc)
  have klt: "k < Suc jN - m" using jl LR by simp
  hence mk: "m + k \<le> jN" by simp
  \<comment> \<open>The \<open>k\<close>-th element of \<open>R\<close> is the rebase of position \<open>m + k\<close>.\<close>
  have nth_upt: "[m..<Suc jN] ! k = m + k"
    using klt by (simp add: nth_upt del: upt_Suc)
  have klen: "k < length [m..<Suc jN]" using klt by (simp add: length_upt del: upt_Suc)
  let ?j = "m + k"
  have e0: "entry R 0 k = entry N 0 ?j - entry N 0 m + entry N 1 m"
    using R_def klen nth_upt by (simp add: entry_def del: upt_Suc)
  have e1: "entry R 1 k = entry N 1 ?j"
    using R_def klen nth_upt by (simp add: entry_def del: upt_Suc)
  \<comment> \<open>Substitute the diagonal-rebase identity \<open>N\<^bsub>0,m\<^esub> = N\<^bsub>1,m\<^esub>\<close>.\<close>
  have e0': "entry R 0 k = entry N 0 ?j - entry N 1 m + entry N 1 m"
    using e0 diag by simp
  \<comment> \<open>Nat fact: \<open>x - c + c \<ge> x\<close>.\<close>
  have ge0: "entry N 0 ?j \<le> entry R 0 k"
    using e0' by simp
  \<comment> \<open>Row-0 dominance of \<open>N\<close> at \<open>?j\<close>.\<close>
  have domj: "entry N 1 ?j \<le> entry N 0 ?j"
    using dom[of ?j] mk by simp
  show "entry R 1 k \<le> entry R 0 k"
    using e1 ge0 domj by simp
qed

end
