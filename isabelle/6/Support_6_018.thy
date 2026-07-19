theory Support_6_018
  imports Frontier_6_035
begin

text \<open>§6.8 d1pos N-side boundary B3N — keystone form (\<open>oper_d1pos_ctx_b3n\<close>).

  STEP-0 RESOLUTION (sub-agent b3nresolve, \<open>python/d1pos_b3n_skt_resolve2.py\<close> +
  \<open>python/d1pos_b3n_skt_deep.py\<close>, the CORRECT rank-stratified standard generator:
  diagSeq base \<rightarrow> oper-closure \<rightarrow> SkT_PS).  RESULT: the BARE claim B3N
  \<open>entry N 1 jm2 \<le> entry N 1 (Lng N-2)\<close> over d0pos (\<open>i1=1\<close>) in-context
  \<open>N \<in> SkT_PS\<close> is \<open>FALSE\<close> on the standard domain: at shallow rank (KMAX\<le>6,
  4378 in-context N) it shows 0 counterexamples, but at rank up to 10 (KMAX=10,
  \<open>|allN|=4703\<close>, 2046 in-context N) it has 18 genuine counterexamples, and the
  claimed CE \<open>N=(0,0)(1,1)(2,2)(3,0)(2,2)\<close> IS SkT_PS-reachable (only at higher
  rank): there \<open>jm2=1\<close>, \<open>entry N 1 jm2 = 1 > entry N 1 (Lng N-2) = 0\<close>.  So bare
  B3N does NOT follow from standardness alone.

  The operative SOUND condition is the \<open>keystone\<close> \<open>le0 N (Lng N-2)(Lng N-1)\<close>
  (the last trunk step reaching the final column): \<open>keystone \<Longrightarrow> B3N\<close> has
  \<open>0 counterexamples\<close> over all 1421 keystone-true in-context N at rank 10 (every
  one of the 18 bare counterexamples is keystone-FALSE — e.g. the CE has
  \<open>le0 N 3 4 = False\<close>).  This lemma proves exactly that kernel.  The capped closer
  @{thm [source] oper_d1pos_b3n_boundary} supplies the keystone from the available
  \<open>fill\<close> hypothesis (@{thm [source] trunk_le0}, @{thm [source] adm_le0_seg}), so the
  main theorem closes through this kernel without needing the IH.

  Route: the row-1 parent relation \<open>nextrel1 N jm2 (Lng N-1)\<close> gives \<open>H1\<close>
  (\<open>entry N 1 jm2 < entry N 1 (Lng N-1)\<close>) and, via its minimality clause applied
  to the keystone-reachable predecessor \<open>Lng N-2\<close>,
  \<open>entry N 1 (Lng N-1) \<le> entry N 1 (Lng N-2)\<close>; the reflexive case
  \<open>jm2 = Lng N-2\<close> is immediate.\<close>

lemma oper_d1pos_ctx_b3n:
  fixes N :: pairseq
  assumes hp1: "hasParent N 1 (Lng N - 1)"
    and L: "1 < Lng N"
    and key: "le0 N (Lng N - 2) (Lng N - 1)"
  shows "entry N 1 (parent N 1 (Lng N - 1)) \<le> entry N 1 (Lng N - 2)"
proof -
  let ?j1N = "Lng N - 1"
  let ?jm2 = "parent N 1 ?j1N"
  \<comment> \<open>the row-1 parent relation \<open>nextrel1 N jm2 (Lng N-1)\<close>\<close>
  have parR1: "nextR N 1 ?jm2 ?j1N"
    using hp1 unfolding hasParent_def parent_def by (rule theI')
  have nr1: "nextrel1 N ?jm2 ?j1N" using parR1 by (simp add: nextR_def)
  have H1: "entry N 1 ?jm2 < entry N 1 ?j1N" using nr1 by (simp add: nextrel1_def)
  have jm2lt: "?jm2 < ?j1N" using nr1 by (simp add: nextrel1_def)
  have minim: "\<And>j. ?jm2 < j \<Longrightarrow> le0 N j ?j1N \<Longrightarrow> entry N 1 ?j1N \<le> entry N 1 j"
    using nr1 by (simp add: nextrel1_def)
  show ?thesis
  proof (cases "?jm2 = ?j1N - 1")
    case True
    have "?j1N - 1 = Lng N - 2" by simp
    thus ?thesis using True by simp
  next
    case False
    hence jm2s: "?jm2 < ?j1N - 1" using jm2lt by linarith
    have idxeq2: "?j1N - 1 = Lng N - 2" by simp
    \<comment> \<open>keystone supplies \<open>le0 N (Lng N-2)(Lng N-1)\<close>, i.e.\ \<open>le0 N (?j1N-1) ?j1N\<close>\<close>
    have le0N: "le0 N (?j1N - 1) ?j1N" using key idxeq2 by simp
    have step: "entry N 1 ?j1N \<le> entry N 1 (?j1N - 1)"
      using minim[OF jm2s le0N] .
    have "entry N 1 ?jm2 \<le> entry N 1 (?j1N - 1)" using step H1 by linarith
    thus ?thesis using idxeq2 by simp
  qed
qed

text \<open>§6.8 d1pos strict trunk-confinement from B3 (\<open>oper_d1pos_ctx_tnc\<close>).

  The "capped boundary-stop route", now FILL-FREE (B3 / B3N is the only
  N-side input).  Given the boundary row-1 NON-increase
  \<open>B3 : entry M' 1 (c+1) \<le> entry M' 1 c\<close> (the M'-image of B3N) the trunk step
  \<open>c \<rightarrow> c+1\<close> fails, so by @{thm [source] TrMax_trunk_step} (contrapositive)
  \<open>TrMax M' \<le> c\<close>; combined with the boundary \<open>le0\<close>
  (@{thm [source] oper_d1pos_seg_le0_boundary}, instantiated as \<open>bdry\<close>) and the
  \<open>\<not>brle\<close> witness \<open>notle\<close> (\<open>\<not> le0 M' (TrMax M'+1)(Lng M'-1)\<close>) the case
  \<open>TrMax M' = c\<close> is excluded, giving the strict \<open>TrMax M' + 1 \<le> c\<close>.

  DEEP-VERIFIED with the strict-2 confinement (the capped \<open>\<not>brle\<close> context, kernel-2
  of \<open>python/d1pos_b3n_skt_deep.py\<close>): 0 failures of \<open>B3 \<and> bdry \<and> notle \<Longrightarrow> TrMax+1\<le>c\<close>
  over all SkT_PS-derived \<open>\<not>brle\<close> slices at rank 10; also the capped lemma
  \<open>TrMax_seg_oper_d1pos_brle_capped\<close> (defined below) 1688/1688.\<close>

lemma oper_d1pos_ctx_tnc:
  fixes Mp :: pairseq
  assumes MpT: "Mp \<in> T_PS"
    and B3: "entry Mp 1 (c + 1) \<le> entry Mp 1 c"
    and bdry: "le0 Mp (c + 1) (Lng Mp - 1)"
    and notle: "\<not> le0 Mp (TrMax Mp + 1) (Lng Mp - 1)"
  shows "TrMax Mp + 1 \<le> c"
proof -
  \<comment> \<open>boundary stop: the trunk step \<open>c \<rightarrow> c+1\<close> cannot fire\<close>
  have boundary_stop: "\<not> nextR Mp 1 c (c + 1)"
  proof
    assume "nextR Mp 1 c (c + 1)"
    hence "nextrel1 Mp c (c + 1)" by (simp add: nextR_def)
    hence "entry Mp 1 c < entry Mp 1 (c + 1)" by (simp add: nextrel1_def)
    thus False using B3 by simp
  qed
  \<comment> \<open>confinement \<open>TrMax Mp \<le> c\<close>\<close>
  have tncM: "TrMax Mp \<le> c"
  proof (rule ccontr)
    assume "\<not> TrMax Mp \<le> c"
    hence "c < TrMax Mp" by simp
    hence "nextR Mp 1 c (c + 1)" by (rule TrMax_trunk_step[OF MpT])
    thus False using boundary_stop by simp
  qed
  \<comment> \<open>strict-2: \<open>TrMax Mp = c\<close> would make \<open>bdry\<close> contradict \<open>notle\<close>\<close>
  have "TrMax Mp \<noteq> c"
  proof
    assume eq: "TrMax Mp = c"
    have "le0 Mp (TrMax Mp + 1) (Lng Mp - 1)" using bdry eq by simp
    thus False using notle by simp
  qed
  with tncM show ?thesis by linarith
qed

end
