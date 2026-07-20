theory Frontier_6_033
  imports Support_6_015
begin

text \<open>If \<open>M\<close> and \<open>N\<close> agree on the closed prefix \<open>[0,c]\<close> then row-0 reachability
  among indices \<open>\<le> c\<close> coincides: a \<open>nextrel0\<close> chain to a target \<open>\<le> c\<close> stays
  \<open>\<le> c\<close> (indices increase along the chain), where the two sequences are equal.
  Used to pull \<open>(0,j'\<^sub>0) \<le> (0,j\<^sub>0\<^sup>N)\<close> from \<open>M = N[n]\<close> back to \<open>N\<close> (article 1476).\<close>

lemma nextrel0_prefix_imp:
  assumes agree: "\<And>j. j \<le> c \<Longrightarrow> M ! j = N ! j"
    and cN: "c < Lng N"
    and xy: "x \<le> c" "y \<le> c"
    and h: "nextrel0 M x y"
  shows "nextrel0 N x y"
proof -
  have e: "\<And>j. j \<le> c \<Longrightarrow> entry M 0 j = entry N 0 j"
    using agree by (simp add: entry_def)
  from h have hx: "x < y" and hv: "entry M 0 x < entry M 0 y"
    and hmid: "\<And>j. x < j \<Longrightarrow> j < y \<Longrightarrow> entry M 0 y \<le> entry M 0 j"
    by (auto simp: nextrel0_def)
  show ?thesis
    unfolding nextrel0_def
  proof (intro conjI allI impI)
    show "x < Lng N" using xy(1) cN by linarith
    show "y < Lng N" using xy(2) cN by linarith
    show "x < y" by (rule hx)
    show "entry N 0 x < entry N 0 y" using hv e[OF xy(1)] e[OF xy(2)] by simp
    fix j assume "x < j \<and> j < y"
    hence j1: "x < j" and j2: "j < y" by auto
    have jc: "j \<le> c" using j2 xy(2) by linarith
    show "entry N 0 y \<le> entry N 0 j" using hmid[OF j1 j2] e[OF xy(2)] e[OF jc] by simp
  qed
qed

lemma le0_prefix_agree:
  assumes agree: "\<And>j. j \<le> c \<Longrightarrow> M ! j = N ! j"
    and cM: "c < Lng M" and cN: "c < Lng N"
    and ac: "a \<le> c" and bc: "b \<le> c"
    and le: "le0 M a b"
  shows "le0 N a b"
proof -
  have rM: "(nextrel0 M)\<^sup>*\<^sup>* a b" using le by (simp add: le0_def)
  have "b \<le> c \<longrightarrow> (nextrel0 N)\<^sup>*\<^sup>* a b"
    using rM
  proof (induction rule: rtranclp_induct)
    case base show ?case by simp
  next
    case (step y z)
    show ?case
    proof
      assume zc: "z \<le> c"
      have yz: "nextrel0 M y z" using step.hyps(2) .
      have ylt: "y < z" using yz by (simp add: nextrel0_def)
      have yc: "y \<le> c" using ylt zc by linarith
      have "(nextrel0 N)\<^sup>*\<^sup>* a y" using step.IH yc by simp
      moreover have "nextrel0 N y z"
        by (rule nextrel0_prefix_imp[OF agree cN yc zc yz])
      ultimately show "(nextrel0 N)\<^sup>*\<^sup>* a z" by simp
    qed
  qed
  hence "(nextrel0 N)\<^sup>*\<^sup>* a b" using bc by simp
  thus ?thesis using ac bc cN by (simp add: le0_def)
qed

text \<open>Row-1 next-relation transfers across a shared prefix \<open>[0,c]\<close>.  The
  \<open>nextrel1\<close> minimality quantifier ranges over \<open>j\<close> with \<open>le0 _ j y\<close>; since
  \<open>le0\<close> is index-monotone (@{thm [source] nextrel0_rtrancl_mono}) such \<open>j\<close>
  satisfy \<open>j \<le> y \<le> c\<close>, so the whole condition is confined to the agreement
  region and transfers (using @{thm [source] le0_prefix_agree} both ways and the
  pointwise row-1 agreement).\<close>

lemma nextrel1_prefix_imp:
  assumes agree: "\<And>j. j \<le> c \<Longrightarrow> M ! j = N ! j"
    and cM: "c < Lng M" and cN: "c < Lng N"
    and xy: "x \<le> c" "y \<le> c"
    and h: "nextrel1 M x y"
  shows "nextrel1 N x y"
proof -
  have e: "\<And>j. j \<le> c \<Longrightarrow> entry M 1 j = entry N 1 j"
    using agree by (simp add: entry_def)
  from h have hx: "x < y" and hv: "entry M 1 x < entry M 1 y"
    and hle: "le0 M x y"
    and hmin: "\<And>j. x < j \<Longrightarrow> le0 M j y \<Longrightarrow> entry M 1 y \<le> entry M 1 j"
    by (auto simp: nextrel1_def)
  show ?thesis
    unfolding nextrel1_def
  proof (intro conjI allI impI)
    show "x < Lng N" using xy(1) cN by linarith
    show "y < Lng N" using xy(2) cN by linarith
    show "x < y" by (rule hx)
    show "entry N 1 x < entry N 1 y" using hv e[OF xy(1)] e[OF xy(2)] by simp
    show "le0 N x y" by (rule le0_prefix_agree[OF agree cM cN xy hle])
    fix j assume j: "x < j \<and> le0 N j y"
    hence xj: "x < j" and lej: "le0 N j y" by auto
    have "(nextrel0 N)\<^sup>*\<^sup>* j y" using lej by (simp add: le0_def)
    hence jy: "j \<le> y" by (rule nextrel0_rtrancl_mono)
    hence jc: "j \<le> c" using xy(2) by linarith
    have leMjy: "le0 M j y"
      using le0_prefix_agree[OF _ cN cM jc xy(2) lej] agree by simp
    have "entry M 1 y \<le> entry M 1 j" using hmin[OF xj leMjy] .
    thus "entry N 1 y \<le> entry N 1 j" using e[OF xy(2)] e[OF jc] by simp
  qed
qed

text \<open>Characterisation of \<open>TrMax\<close>.  \<open>TrMax M\<close> is by definition
  \<open>Max {j. \<forall>j'<j. nextR M 1 j' (j'+1)}\<close>.  The set is bounded by \<open>Lng M - 1\<close>
  (proof reused from @{thm [source] TrMax_bound}) and contains \<open>0\<close>, so its \<open>Max\<close>
  is well-defined; a value \<open>j\<close> with the full row-1 chain below it and the step
  failing at it is exactly the maximum.  This is the brick the §6.8 block cases
  need to pin \<open>TrMax (seg M' \<dots>)\<close> without re-deriving from \<open>Max\<close>.\<close>

lemma TrMax_eqI:
  assumes M: "M \<in> T_PS"
    and below: "\<And>j'. j' < j \<Longrightarrow> nextR M 1 j' (j' + 1)"
    and stop: "\<not> nextR M 1 j (j + 1)"
  shows "TrMax M = j"
proof -
  let ?S = "{i. \<forall>j'<i. nextR M 1 j' (j' + 1)}"
  have LM: "Lng M > 0" using M by (cases M) (auto simp: T_PS_def)
  have sub: "?S \<subseteq> {..Lng M - 1}"
  proof
    fix i assume "i \<in> ?S"
    hence H: "\<forall>j'<i. nextR M 1 j' (j' + 1)" by simp
    show "i \<in> {..Lng M - 1}"
    proof (rule ccontr)
      assume "i \<notin> {..Lng M - 1}"
      hence "Lng M - 1 < i" by simp
      hence "nextR M 1 (Lng M - 1) ((Lng M - 1) + 1)" using H by blast
      hence "(Lng M - 1) + 1 < Lng M" by (simp add: nextR_def nextrel1_def)
      thus False using LM by simp
    qed
  qed
  hence fin: "finite ?S" by (rule finite_subset) simp
  have jin: "j \<in> ?S" using below by simp
  hence ne: "?S \<noteq> {}" by blast
  \<comment> \<open>\<open>j\<close> is an upper bound of \<open>?S\<close>: any \<open>i > j\<close> would force the step at \<open>j\<close>\<close>
  have ub: "\<And>i. i \<in> ?S \<Longrightarrow> i \<le> j"
  proof -
    fix i assume "i \<in> ?S"
    hence H: "\<forall>j'<i. nextR M 1 j' (j' + 1)" by simp
    show "i \<le> j"
    proof (rule ccontr)
      assume "\<not> i \<le> j"
      hence "j < i" by simp
      hence "nextR M 1 j (j + 1)" using H by blast
      thus False using stop by simp
    qed
  qed
  have "Max ?S = j" using fin ne jin ub by (intro Max_eqI) auto
  thus ?thesis by (simp add: TrMax_def)
qed

text \<open>\<open>TrMax\<close> transfers across a shared prefix \<open>[0,c]\<close> when the trunk of \<open>N\<close>
  is confined to that prefix (\<open>TrMax N \<le> c\<close>) and the \<open>M\<close>-side stop step at
  \<open>TrMax N\<close> is given.  The below-trunk row-1 chain of \<open>N\<close> (@{thm [source]
  TrMax_trunk_step}) lands inside \<open>[0,c]\<close> (since \<open>j'+1 \<le> TrMax N \<le> c\<close>) and
  transfers to \<open>M\<close> via @{thm [source] nextrel1_prefix_imp}; the stop step is the
  hypothesis; @{thm [source] TrMax_eqI} then pins \<open>TrMax M\<close>.  This is the
  trunk-confinement half of the §6.8 d0zero block-spanning argument: with
  \<open>c = min(j'\<^sub>1, Lng N - 2) - j'\<^sub>0\<close> the slices \<open>M' = seg (N[n]) j'\<^sub>0 j'\<^sub>1\<close> and
  \<open>N' = seg N j'\<^sub>0 (Lng N-1)\<close> agree on \<open>[0,c]\<close> and \<open>TrMax N' \<le> c\<close>; the boundary
  stop is the only residual.\<close>

lemma TrMax_eq_of_prefix_agree:
  assumes M: "M \<in> T_PS" and N: "N \<in> T_PS"
    and agree: "\<And>j. j \<le> c \<Longrightarrow> M ! j = N ! j"
    and cM: "c < Lng M" and cN: "c < Lng N"
    and tnc: "TrMax N \<le> c"
    and stop: "\<not> nextR M 1 (TrMax N) (TrMax N + 1)"
  shows "TrMax M = TrMax N"
proof (rule TrMax_eqI[OF M _ stop])
  fix j' assume j': "j' < TrMax N"
  \<comment> \<open>below-trunk step of \<open>N\<close> (lives in the prefix) transfers to \<open>M\<close>\<close>
  have stepN: "nextrel1 N j' (j' + 1)"
    using TrMax_trunk_step[OF N j'] by (simp add: nextR_def)
  have y_le: "j' + 1 \<le> c" using j' tnc by linarith
  have x_le: "j' \<le> c" using y_le by linarith
  have agree': "\<And>j. j \<le> c \<Longrightarrow> N ! j = M ! j" using agree by simp
  have "nextrel1 M j' (j' + 1)"
    by (rule nextrel1_prefix_imp[OF agree' cN cM x_le y_le stepN])
  thus "nextR M 1 j' (j' + 1)" by (simp add: nextR_def)
qed

text \<open>SYMMETRIC companion of @{thm [source] TrMax_eq_of_prefix_agree}: when the
  trunk of the FIRST sequence \<open>M\<close> (rather than the reference \<open>N\<close>) is the one
  known to be confined to the shared prefix \<open>[0,c]\<close> (\<open>tncM : TrMax M \<le> c\<close>) and
  the \<open>M\<close>-side boundary step fails (\<open>stopM\<close>), the two trunks still coincide.  This
  is just @{thm [source] TrMax_eq_of_prefix_agree} with the roles of \<open>M\<close> and \<open>N\<close>
  exchanged (agreement is symmetric); we pin \<open>TrMax N = TrMax M\<close> by
  @{thm [source] TrMax_eqI} on \<open>N\<close>, transferring each below-trunk step of \<open>M\<close> into
  \<open>N\<close> via @{thm [source] nextrel1_prefix_imp}.  Needed for the d1pos \<open>\<not>brle\<close>
  closure, where the confinement is an intrinsic \<open>M\<close>-side (\<open>\<not>brle\<close>) fact, not a
  reference-side one.\<close>

lemma TrMax_eq_of_prefix_agree_sym:
  assumes M: "M \<in> T_PS" and N: "N \<in> T_PS"
    and agree: "\<And>j. j \<le> c \<Longrightarrow> M ! j = N ! j"
    and cM: "c < Lng M" and cN: "c < Lng N"
    and tncM1: "TrMax M + 1 \<le> c"
    and stopM: "\<not> nextR M 1 (TrMax M) (TrMax M + 1)"
  shows "TrMax M = TrMax N"
proof -
  have "TrMax N = TrMax M"
  proof (rule TrMax_eqI[OF N])
    \<comment> \<open>below-trunk step of \<open>M\<close> (lives in the prefix) transfers to \<open>N\<close>\<close>
    fix j' assume j': "j' < TrMax M"
    have stepM: "nextrel1 M j' (j' + 1)"
      using TrMax_trunk_step[OF M j'] by (simp add: nextR_def)
    have y_le: "j' + 1 \<le> c" using j' tncM1 by linarith
    have x_le: "j' \<le> c" using y_le by linarith
    have "nextrel1 N j' (j' + 1)"
      by (rule nextrel1_prefix_imp[OF agree cM cN x_le y_le stepM])
    thus "nextR N 1 j' (j' + 1)" by (simp add: nextR_def)
  next
    \<comment> \<open>\<open>N\<close>-side boundary stop at \<open>TrMax M\<close>: stop index \<open>TrMax M + 1 \<le> c\<close> is in the
       shared prefix (strict-2 confinement \<open>tncM1\<close>), so the \<open>M\<close>-side stop transfers\<close>
    have inrange: "TrMax M + 1 \<le> c" by (rule tncM1)
    have x_le: "TrMax M \<le> c" using inrange by linarith
    have agree'': "\<And>j. j \<le> c \<Longrightarrow> N ! j = M ! j" using agree by simp
    show "\<not> nextR N 1 (TrMax M) (TrMax M + 1)"
    proof
      assume "nextR N 1 (TrMax M) (TrMax M + 1)"
      hence stepN: "nextrel1 N (TrMax M) (TrMax M + 1)" by (simp add: nextR_def)
      have "nextrel1 M (TrMax M) (TrMax M + 1)"
        by (rule nextrel1_prefix_imp[OF agree'' cN cM x_le inrange stepN])
      thus False using stopM by (simp add: nextR_def)
    qed
  qed
  thus ?thesis by simp
qed

text \<open>Maximality of \<open>TrMax\<close>: when the trunk does not fill the whole sequence
  (\<open>TrMax M < Lng M - 1\<close>) the row-1 step at the trunk's right end fails (else
  \<open>TrMax M + 1\<close> would also be a valid trunk length, contradicting maximality).
  This is the stop step every \<open>TrMax\<close>-equality argument needs on the reference
  side.\<close>

lemma TrMax_stop:
  assumes M: "M \<in> T_PS" and lt: "TrMax M < Lng M - 1"
  shows "\<not> nextR M 1 (TrMax M) (TrMax M + 1)"
proof
  assume step: "nextR M 1 (TrMax M) (TrMax M + 1)"
  let ?S = "{j. \<forall>j'<j. nextR M 1 j' (j' + 1)}"
  have LM: "Lng M > 0" using M by (cases M) (auto simp: T_PS_def)
  have sub: "?S \<subseteq> {..Lng M - 1}"
  proof
    fix j assume "j \<in> ?S"
    hence H: "\<forall>j'<j. nextR M 1 j' (j' + 1)" by simp
    show "j \<in> {..Lng M - 1}"
    proof (rule ccontr)
      assume "j \<notin> {..Lng M - 1}"
      hence "Lng M - 1 < j" by simp
      hence "nextR M 1 (Lng M - 1) ((Lng M - 1) + 1)" using H by blast
      hence "(Lng M - 1) + 1 < Lng M" by (simp add: nextR_def nextrel1_def)
      thus False using LM by simp
    qed
  qed
  hence fin: "finite ?S" by (rule finite_subset) simp
  \<comment> \<open>\<open>TrMax M + 1\<close> is a valid trunk length: below it every step holds\<close>
  have below: "\<forall>j'<TrMax M. nextR M 1 j' (j' + 1)" by (rule TrMax_in_S[OF M])
  have "\<forall>j'<TrMax M + 1. nextR M 1 j' (j' + 1)"
  proof (intro allI impI)
    fix j' assume "j' < TrMax M + 1"
    hence "j' < TrMax M \<or> j' = TrMax M" by linarith
    thus "nextR M 1 j' (j' + 1)" using below step by auto
  qed
  hence inS: "TrMax M + 1 \<in> ?S" by simp
  have "TrMax M + 1 \<le> Max ?S" by (rule Max_ge[OF fin inS])
  thus False by (simp add: TrMax_def)
qed

text \<open>If the last row-1 entry is \<open>0\<close> the trunk cannot reach the right end: the
  final trunk step would need \<open>entry M 1 (Lng M-2) < entry M 1 (Lng M-1) = 0\<close>,
  impossible.  In the §6.8 d0zero case the slice \<open>N' = seg N j'\<^sub>0 (Lng N-1)\<close> ends
  at \<open>N\<^bsub>j\<^sub>1\<^sup>N\<^esub>\<close> with \<open>N\<^bsub>1,j\<^sub>1\<^sup>N\<^esub> = 0\<close>, so this gives article 1480 (\<open>Br N' \<noteq> []\<close>).\<close>

lemma TrMax_lt_last_of_row1_zero:
  assumes M: "M \<in> T_PS" and L: "1 < Lng M" and z: "entry M 1 (Lng M - 1) = 0"
  shows "TrMax M < Lng M - 1"
proof -
  have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF M])
  have "TrMax M \<noteq> Lng M - 1"
  proof
    assume eq: "TrMax M = Lng M - 1"
    have pos: "0 < Lng M - 1" using L by linarith
    have prev: "Lng M - 2 < TrMax M" using eq pos by linarith
    have "nextR M 1 (Lng M - 2) ((Lng M - 2) + 1)"
      using TrMax_in_S[OF M] prev by blast
    moreover have "(Lng M - 2) + 1 = Lng M - 1" using L by simp
    ultimately have "nextrel1 M (Lng M - 2) (Lng M - 1)" by (simp add: nextR_def)
    hence "entry M 1 (Lng M - 2) < entry M 1 (Lng M - 1)" by (simp add: nextrel1_def)
    thus False using z by simp
  qed
  with tb show ?thesis by linarith
qed

text \<open>Row-1 monotonicity along a row-1 ancestor chain: \<open>le1 M a b\<close> (the reflexive-
  transitive closure of \<open>nextrel1\<close>) implies \<open>entry M 1 a \<le> entry M 1 b\<close>, because
  every \<open>nextrel1\<close> step strictly increases row-1.  Used to compare the row-1 value
  at the row-0 parent \<open>j\<^sub>0\<^sup>N\<close> (which lies on the trunk of \<open>N'\<close>) with the row-1 value
  at the trunk's right end in the d0zero case-A boundary stop.\<close>

lemma le1_imp_entry1_le:
  assumes "le1 M a b"
  shows "entry M 1 a \<le> entry M 1 b"
proof -
  have "(nextrel1 M)\<^sup>*\<^sup>* a b" using assms by (simp add: le1_def)
  thus ?thesis
  proof (induction rule: rtranclp_induct)
    case base show ?case by simp
  next
    case (step y z)
    have "entry M 1 y < entry M 1 z" using step.hyps(2) by (simp add: nextrel1_def)
    thus ?case using step.IH by linarith
  qed
qed

text \<open>§6.8 d0zero case-A (article 1466) trunk-confinement: the slice
  \<open>M' = seg (N[n]) j'\<^sub>0 j'\<^sub>1\<close> and the reference slice \<open>N' = seg N j'\<^sub>0 (Lng N-1)\<close>
  have the SAME trunk right end (\<open>TrMax M' = TrMax N'\<close>), as long as \<open>j'\<^sub>1\<close> reaches
  the parent region (\<open>Lng N - 2 \<le> j'\<^sub>1\<close>).  This packages the trunk-confinement
  half of the d0zero block-spanning decomposition: \<open>M'\<close> and \<open>N'\<close> agree on
  \<open>[0, Lng N - 2 - j'\<^sub>0]\<close> (period of \<open>N[n]\<close> intact below \<open>Lng N - 1\<close>, via
  @{thm [source] oper_nth_lt}); the \<open>N'\<close>-trunk is confined there because its last
  row-1 entry is \<open>N\<^bsub>1,j\<^sub>1\<^sup>N\<^esub> = 0\<close> (d0zero, @{thm [source] TrMax_lt_last_of_row1_zero});
  so @{thm [source] TrMax_eq_of_prefix_agree} reduces \<open>TrMax M' = TrMax N'\<close> to the
  single \<^emph>\<open>boundary stop\<close> \<open>\<not> nextR M' 1 (TrMax N') (TrMax N' + 1)\<close>, taken here as
  a hypothesis.  Empirically (\<open>python/slice_trmaxeq_audit*.py\<close>, UB5/NMAX4/KMAX4)
  the equality holds 6129/6129 and the boundary stop holds 6129/6129; the residual
  boundary stop is automatic whenever its index lies in the agreement region
  (6057 cases), and otherwise (\<open>TrMax N' = Lng N' - 2\<close>, all with block width 1)
  reduces to the within-block row-1 inequality \<open>N\<^bsub>1,j\<^sub>0\<^sup>N\<^esub> \<le> N\<^bsub>1,Lng N-2\<^esub>\<close> (72/72).\<close>

text \<open>Boundary-stop transfer (the \<^emph>\<open>easy direction\<close> of the d0zero boundary):
  when the stop index \<open>TrMax N + 1\<close> also lies in the shared prefix \<open>[0,c]\<close>, the
  \<open>N\<close>-side stop (@{thm [source] TrMax_stop}) transfers to \<open>M\<close>.  If
  \<open>nextrel1 M (TrMax N) (TrMax N+1)\<close> held it would push back to \<open>N\<close> via
  @{thm [source] nextrel1_prefix_imp}, contradicting \<open>TrMax N\<close>'s maximality.  The
  remaining (hard) direction is when \<open>TrMax N + 1 > c\<close>, i.e. \<open>TrMax N = c\<close> at the
  agreement boundary, handled separately (block width 1, equal row-1 values).\<close>

lemma nextR1_boundary_stop_of_prefix:
  assumes M: "M \<in> T_PS" and N: "N \<in> T_PS"
    and agree: "\<And>j. j \<le> c \<Longrightarrow> M ! j = N ! j"
    and cM: "c < Lng M" and cN: "c < Lng N"
    and tnlt: "TrMax N < Lng N - 1"
    and inrange: "TrMax N + 1 \<le> c"
  shows "\<not> nextR M 1 (TrMax N) (TrMax N + 1)"
proof
  assume "nextR M 1 (TrMax N) (TrMax N + 1)"
  hence stepM: "nextrel1 M (TrMax N) (TrMax N + 1)" by (simp add: nextR_def)
  have x_le: "TrMax N \<le> c" using inrange by linarith
  have stepN: "nextrel1 N (TrMax N) (TrMax N + 1)"
    by (rule nextrel1_prefix_imp[OF agree cM cN x_le inrange stepM])
  have "\<not> nextR N 1 (TrMax N) (TrMax N + 1)" by (rule TrMax_stop[OF N tnlt])
  thus False using stepN by (simp add: nextR_def)
qed

text \<open>§6.8 d0zero case-A boundary stop (the residual discharged here).  On the
  faithful case-A domain (standard \<open>N\<close>, d0zero, \<open>j'\<^sub>0 < j\<^sub>0\<^sup>N = parent N 0 (Lng N-1)\<close>,
  \<open>Lng N - 2 \<le> j'\<^sub>1\<close>), the row-1 step at the trunk's right end of \<open>N'\<close> fails in
  \<open>M' = seg (N[n]) j'\<^sub>0 j'\<^sub>1\<close>:
  \<open>\<not> nextrel1 M' (TrMax N') (TrMax N' + 1)\<close>, \<open>N' = seg N j'\<^sub>0 (Lng N-1)\<close>.

  Two cases on \<open>TrMax N'\<close> (which is \<open>\<le> Lng N' - 2\<close> since \<open>N\<^bsub>1,Lng N-1\<^esub> = 0\<close>,
  @{thm [source] TrMax_lt_last_of_row1_zero}):
  \<^item> EASY (\<open>TrMax N' < Lng N' - 2\<close>): the stop index \<open>TrMax N' + 1\<close> lies in the
    \<open>M'/N'\<close> prefix-agreement region \<open>[0, Lng N' - 2]\<close>, so
    @{thm [source] nextR1_boundary_stop_of_prefix} transfers the \<open>N'\<close>-side stop.
  \<^item> HARD (\<open>TrMax N' = Lng N' - 2\<close>): the stop index \<open>= Lng N' - 1\<close> reaches the block
    boundary.  If it leaves \<open>M'\<close> (\<open>\<ge> Lng M'\<close>) the step fails for length reasons.
    Otherwise \<open>M' ! (TrMax N') = N ! (Lng N - 2)\<close> (block-0 last interior) and
    \<open>M' ! (TrMax N' + 1) = N ! j\<^sub>0\<^sup>N\<close> (block-1 start), by the d0zero periodicity
    (@{thm [source] oper_d0zero_nth}).  Since \<open>j\<^sub>0\<^sup>N\<close> lies on the trunk of \<open>N'\<close>
    (\<open>j\<^sub>0\<^sup>N - j'\<^sub>0 \<le> TrMax N'\<close>) and row-1 weakly increases along the trunk
    (@{thm [source] trunk_le1}, @{thm [source] le1_imp_entry1_le}), we get
    \<open>entry M' 1 (TrMax N' + 1) = N\<^bsub>1,j\<^sub>0\<^sup>N\<^esub> \<le> N\<^bsub>1,Lng N-2\<^esub> = entry M' 1 (TrMax N')\<close>,
    so the strict row-1 increase \<open>nextrel1\<close> needs is impossible.

  Empirically (\<open>python/slice_caseA_boundary_stop_recheck.py\<close>, is_standard +
  enumeration to length 5, the exact hypotheses): the stop holds 738/738 and the
  hard-case inequality \<open>entry M' 1 (TrMax N') \<ge> entry M' 1 (TrMax N' + 1)\<close>
  holds on all hard instances (block widths \<open>w \<in> {1,2,3}\<close>).\<close>

lemma nextR1_boundary_stop_d0zero_caseA:
  assumes N: "N \<in> T_PS" and L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 0"
    and parR0: "nextrel0 N (parent N 0 (Lng N - 1)) (Lng N - 1)"
    and n1: "1 \<le> n"
    and j0'lt0N: "j0' < parent N 0 (Lng N - 1)"
    and bge: "Lng N - 2 \<le> j1'"
    and j1lt: "j1' < Lng ((N::pairseq)[n])"
  shows "\<not> nextR (seg ((N::pairseq)[n]) j0' j1') 1
            (TrMax (seg N j0' (Lng N - 1)))
            (TrMax (seg N j0' (Lng N - 1)) + 1)"
proof -
  let ?M = "(N::pairseq)[n]"
  let ?j1N = "Lng N - 1"
  let ?j0N = "parent N 0 ?j1N"
  let ?w = "?j1N - ?j0N"
  let ?Mp = "seg ?M j0' j1'"
  let ?Np = "seg N j0' ?j1N"
  let ?t = "TrMax ?Np"
  \<comment> \<open>basic facts\<close>
  have j0Nlt: "?j0N < ?j1N" using parR0 by (simp add: nextrel0_def)
  have j0'lt: "j0' < ?j1N" using j0'lt0N j0Nlt by linarith
  have j0lt1: "j0' \<le> ?j1N" using j0'lt by linarith
  have j0ltM: "j0' \<le> j1'" using j0'lt bge by linarith
  have w0: "0 < ?w" using j0Nlt by linarith
  have MpT: "?Mp \<in> T_PS" using j0ltM by (simp add: T_PS_def seg_def)
  have NpT: "?Np \<in> T_PS" using j0lt1 by (simp add: T_PS_def seg_def)
  have LMp: "Lng ?Mp = Suc j1' - j0'" by simp
  have LNp: "Lng ?Np = Suc ?j1N - j0'" by simp
  have LNp2: "1 < Lng ?Np" using j0'lt by simp
  \<comment> \<open>last row-1 entry of \<open>N'\<close> is \<open>N\<^bsub>1,j\<^sub>1\<^sup>N\<^esub> = 0\<close> (d0zero)\<close>
  have d0zero: "entry N 1 ?j1N = 0" using i1z by (simp add: idx1_def split: if_splits)
  have lastNp_idx: "Lng ?Np - 1 = ?j1N - j0'" using LNp by simp
  have lastNp: "?Np ! (Lng ?Np - 1) = N ! ?j1N"
  proof -
    have lt: "?j1N - j0' < Suc ?j1N - j0'" using j0'lt by linarith
    have "?Np ! (?j1N - j0') = N ! (j0' + (?j1N - j0'))" using lt by (rule seg_nth_eq)
    also have "j0' + (?j1N - j0') = ?j1N" using j0lt1 by simp
    finally show ?thesis using lastNp_idx by simp
  qed
  have zNp: "entry ?Np 1 (Lng ?Np - 1) = 0" using lastNp d0zero by (simp add: entry_def)
  \<comment> \<open>\<open>N'\<close>-trunk confined: \<open>TrMax N' < Lng N' - 1 = Lng N' - 1\<close>, i.e. \<open>?t \<le> Lng N' - 2\<close>\<close>
  have tNlt: "?t < Lng ?Np - 1"
    by (rule TrMax_lt_last_of_row1_zero[OF NpT LNp2 zNp])
  have tle: "?t \<le> Lng ?Np - 2" using tNlt by linarith
  have LNpval: "Lng ?Np - 2 = ?j1N - 1 - j0'" using LNp by simp
  show ?thesis
  proof (cases "?t < Lng ?Np - 2")
    case easy: True
    \<comment> \<open>stop index inside the prefix-agreement region \<open>[0, Lng N' - 2]\<close>\<close>
    let ?c = "Lng ?Np - 2"
    have agree: "\<And>s. s \<le> ?c \<Longrightarrow> ?Mp ! s = ?Np ! s"
    proof -
      fix s assume sc: "s \<le> ?c"
      have idxlt: "j0' + s < ?j1N" using sc LNpval j0'lt by linarith
      have sM: "s < Suc j1' - j0'" using sc LNpval bge j0'lt by linarith
      have sN: "s < Suc ?j1N - j0'" using sc LNpval j0'lt by linarith
      have "?Mp ! s = ?M ! (j0' + s)" using sM by (rule seg_nth_eq)
      also have "\<dots> = N ! (j0' + s)" using oper_nth_lt[OF N L n1 idxlt] by simp
      also have "\<dots> = ?Np ! s" using sN by (simp add: seg_nth_eq)
      finally show "?Mp ! s = ?Np ! s" .
    qed
    have cM: "?c < Lng ?Mp" using LMp LNpval bge j0'lt by linarith
    have cN: "?c < Lng ?Np" using LNp2 by linarith
    have inrange: "?t + 1 \<le> ?c" using easy by linarith
    show ?thesis
      by (rule nextR1_boundary_stop_of_prefix[OF MpT NpT agree cM cN tNlt inrange])
  next
    case hard: False
    have teq: "?t = Lng ?Np - 2" using tle hard by linarith
    \<comment> \<open>stop index \<open>?t + 1 = Lng N' - 1 = ?j1N - j0'\<close>\<close>
    have t1: "?t + 1 = ?j1N - j0'" using teq LNpval j0'lt by linarith
    show ?thesis
    proof
      assume "nextR ?Mp 1 ?t (?t + 1)"
      hence step: "nextrel1 ?Mp ?t (?t + 1)" by (simp add: nextR_def)
      have rng: "?t + 1 < Lng ?Mp" using step by (simp add: nextrel1_def)
      \<comment> \<open>index of \<open>?t+1\<close> in \<open>M\<close> is \<open>?j1N\<close>; \<open>n \<ge> 2\<close> follows (else it leaves \<open>M\<close>)\<close>
      have j1pge: "?j1N - j0' < Suc j1' - j0'" using rng LMp t1 by linarith
      have idxM_t1: "j0' + (?t + 1) = ?j1N" using t1 j0lt1 by linarith
      have idxM_t: "j0' + ?t = ?j1N - 1" using t1 j0Nlt j0'lt0N by linarith
      \<comment> \<open>\<open>M' ! (?t+1) = M ! ?j1N\<close> and \<open>M' ! ?t = M ! (?j1N - 1)\<close>\<close>
      have segt1: "?Mp ! (?t + 1) = ?M ! ?j1N"
      proof -
        have "?Mp ! (?t + 1) = ?M ! (j0' + (?t + 1))" using j1pge t1 by (simp add: seg_nth_eq)
        thus ?thesis using idxM_t1 by simp
      qed
      have tlt: "?t < ?t + 1" by simp
      have segt: "?Mp ! ?t = ?M ! (?j1N - 1)"
      proof -
        have "?t < Suc j1' - j0'" using rng LMp by linarith
        hence "?Mp ! ?t = ?M ! (j0' + ?t)" by (rule seg_nth_eq)
        thus ?thesis using idxM_t by simp
      qed
      \<comment> \<open>identify the two \<open>M\<close>-entries via d0zero periodicity\<close>
      have LngM: "Lng ?M = ?j0N + n * ?w"
      proof -
        have ex: "?M = take ?j0N N @ concat (replicate n (map ((!) N) [?j0N..<?j1N]))"
          using oper_d0zero_expand[OF L notzero hp i1z] by simp
        have t: "length (take ?j0N N) = ?j0N" using j0Nlt L by simp
        have b: "length (map ((!) N) [?j0N..<?j1N]) = ?w" by simp
        show ?thesis using ex t b by (simp add: length_concat sum_list_replicate)
      qed
      \<comment> \<open>\<open>n \<ge> 2\<close>: else \<open>Lng M = ?j0N + ?w = ?j1N\<close> and \<open>?t+1 = ?j1N - j0' \<ge> Lng M'\<close>\<close>
      have n2: "2 \<le> n"
      proof (rule ccontr)
        assume "\<not> 2 \<le> n"
        hence "n = 1" using n1 by linarith
        hence LMn1: "Lng ?M = ?j1N" using LngM w0 j0Nlt by simp
        have "j1' < ?j1N" using j1lt LMn1 by linarith
        hence "Lng ?Mp \<le> ?j1N - j0'" using LMp j0lt1 by linarith
        thus False using rng t1 by linarith
      qed
      \<comment> \<open>\<open>M ! ?j1N = M ! (?j0N + 1*?w + 0) = N ! ?j0N\<close> (block 1, offset 0)\<close>
      have valt1: "?M ! ?j1N = N ! ?j0N"
      proof -
        have e: "?j1N = ?j0N + 1 * ?w + 0" using j0Nlt by simp
        have "?M ! (?j0N + 1 * ?w + 0) = N ! (?j0N + 0)"
          by (rule oper_d0zero_nth[OF L notzero hp i1z j0Nlt _ w0]) (use n2 in simp)
        thus ?thesis using e by simp
      qed
      \<comment> \<open>\<open>M ! (?j1N - 1) = M ! (?j0N + 0*?w + (?w-1)) = N ! (?j1N - 1)\<close> (block 0)\<close>
      have valt: "?M ! (?j1N - 1) = N ! (?j1N - 1)"
      proof -
        have e: "?j1N - 1 = ?j0N + 0 * ?w + (?w - 1)" using j0Nlt w0 by simp
        have sw: "?w - 1 < ?w" using w0 by simp
        have q0: "(0::nat) < n" using n1 by simp
        have "?M ! (?j0N + 0 * ?w + (?w - 1)) = N ! (?j0N + (?w - 1))"
          by (rule oper_d0zero_nth[OF L notzero hp i1z j0Nlt q0 sw])
        also have "?j0N + (?w - 1) = ?j1N - 1" using j0Nlt w0 by linarith
        finally show ?thesis using e by simp
      qed
      \<comment> \<open>row-1 values: \<open>entry M' 1 (?t+1) = N\<^bsub>1,?j0N\<^esub>\<close>, \<open>entry M' 1 ?t = N\<^bsub>1,?j1N-1\<^esub>\<close>\<close>
      have e_t1: "entry ?Mp 1 (?t + 1) = entry N 1 ?j0N"
        using segt1 valt1 by (simp add: entry_def)
      have e_t: "entry ?Mp 1 ?t = entry N 1 (?j1N - 1)"
        using segt valt by (simp add: entry_def)
      \<comment> \<open>\<open>j\<^sub>0\<^sup>N\<close> is on the trunk of \<open>N'\<close>; relate its row-1 value to that of the trunk end\<close>
      have jjle: "?j0N - j0' \<le> ?t"
        using teq LNpval j0Nlt j0'lt0N by linarith
      have le1Np: "leR ?Np 1 (?j0N - j0') ?t"
        by (rule trunk_le1[OF NpT jjle le_refl])
      have e_jj: "entry ?Np 1 (?j0N - j0') = entry N 1 ?j0N"
      proof -
        have lt: "?j0N - j0' < Suc ?j1N - j0'" using j0Nlt j0'lt0N by linarith
        have "?Np ! (?j0N - j0') = N ! (j0' + (?j0N - j0'))" using lt by (rule seg_nth_eq)
        also have "j0' + (?j0N - j0') = ?j0N" using j0'lt0N by linarith
        finally show ?thesis by (simp add: entry_def)
      qed
      have e_te: "entry ?Np 1 ?t = entry N 1 (?j1N - 1)"
      proof -
        have lt: "?t < Suc ?j1N - j0'" using tNlt LNp by linarith
        have "?Np ! ?t = N ! (j0' + ?t)" using lt by (rule seg_nth_eq)
        also have "j0' + ?t = ?j1N - 1" using idxM_t by simp
        finally show ?thesis by (simp add: entry_def)
      qed
      have le1Np': "le1 ?Np (?j0N - j0') ?t" using le1Np by (simp add: leR_def)
      have mono: "entry ?Np 1 (?j0N - j0') \<le> entry ?Np 1 ?t"
        by (rule le1_imp_entry1_le[OF le1Np'])
      have key: "entry N 1 ?j0N \<le> entry N 1 (?j1N - 1)"
        using mono e_jj e_te by simp
      \<comment> \<open>contradiction: \<open>nextrel1\<close> needs strict row-1 increase \<open>?t \<to> ?t+1\<close>\<close>
      have "entry ?Mp 1 ?t < entry ?Mp 1 (?t + 1)" using step by (simp add: nextrel1_def)
      hence "entry N 1 (?j1N - 1) < entry N 1 ?j0N" using e_t e_t1 by simp
      thus False using key by linarith
    qed
  qed
qed

text \<open>§6.8 d1pos CAPPED regime-A boundary stop (the d1pos analogue of
  @{thm [source] nextR1_boundary_stop_d0zero_caseA}, the LAST hard brick of the
  d0pos \<open>\<not>brle\<close> closure).  On the faithful d1pos domain (standard \<open>N\<close>,
  \<open>i\<^sub>1 = 1\<close>, regime A \<open>j'\<^sub>0 \<le> j\<^sub>-\<^sub>2 = parent N 1 (Lng N-1)\<close>, capped \<open>Lng N-1 \<le> j'\<^sub>1\<close>),
  the row-1 step at the right end of the reduced trunk fails in
  \<open>M' = seg (N[n]) j'\<^sub>0 j'\<^sub>1\<close>:
  \<open>\<not> nextR M' 1 (TrMax N\<^sub>p) (TrMax N\<^sub>p + 1)\<close>, \<open>N\<^sub>p = seg N j'\<^sub>0 (Lng N-1)\<close>.

  Unlike d0zero, the last row-1 entry \<open>N\<^bsub>1,Lng N-1\<^esub>\<close> is NONZERO (\<open>i\<^sub>1=1\<close>), so there
  is no intrinsic trunk-confinement.  The boundary argument is instead the
  block-boundary row-1 RESET: along the d1pos oper, row 1 carries NO per-block
  shift (\<open>d\<^sub>1 = 0\<close>, @{thm [source] oper_d1pos_entry1}), so at the block boundary the
  row-1 value drops back to the block-start value
  \<open>entry (N[n]) 1 (Lng N-1) = N\<^bsub>1,j\<^sub>-\<^sub>2\<^esub>\<close>; combined with the row-1 weak increase
  along the reduced trunk (@{thm [source] trunk_le1}/@{thm [source] le1_imp_entry1_le})
  from \<open>j\<^sub>-\<^sub>2 - j'\<^sub>0\<close> to \<open>TrMax N\<^sub>p\<close>, this makes the strict row-1 increase that
  \<open>nextrel1\<close> needs impossible.  Two cases (mirroring d0zero):
  \<^item> EASY (\<open>TrMax N\<^sub>p + 1 \<le> Lng N\<^sub>p - 2\<close>): the stop index lies in the verbatim prefix
    \<open>[0, Lng N-2-j'\<^sub>0]\<close> (@{thm [source] oper_nth_lt}), so the \<open>N\<^sub>p\<close>-side stop
    (@{thm [source] TrMax_stop}, available since \<open>TrMax N\<^sub>p < Lng N\<^sub>p - 1\<close> there)
    transfers via @{thm [source] nextR1_boundary_stop_of_prefix}.
  \<^item> HARD (\<open>TrMax N\<^sub>p \<in> {Lng N\<^sub>p-2, Lng N\<^sub>p-1}\<close>): the stop index reaches the boundary.
    If it leaves \<open>M'\<close> the step fails for length reasons; otherwise the M-index of
    \<open>TrMax N\<^sub>p + 1\<close> sits at the start of block 1 (offset 0), where the row-1 reset
    gives \<open>entry M' 1 (TrMax N\<^sub>p + 1) = N\<^bsub>1,j\<^sub>-\<^sub>2\<^esub> \<le> entry M' 1 (TrMax N\<^sub>p)\<close>.

  DEEP-VERIFIED (rank-stratified standard generator, len\<le>12 KMAX\<le>8,
  \<open>/tmp/d1pos_capped_stop_check.py\<close>): the stop holds 18969/18969 on the EXACT
  hypotheses, and the unified boundary inequality
  \<open>entry M' 1 (TrMax N\<^sub>p + 1) \<le> entry M' 1 (TrMax N\<^sub>p)\<close> holds 584/584 on the hard
  (boundary-reaching) cases.\<close>

lemma nextR1_boundary_stop_d1pos:
  fixes N :: pairseq
  assumes N: "N \<in> T_PS" and L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and n1: "1 \<le> n"
    and j0'le: "j0' \<le> parent N 1 (Lng N - 1)"
    and bge: "Lng N - 1 \<le> j1'"
    and j1lt: "j1' < Lng ((N::pairseq)[n])"
  shows "\<not> nextR (seg ((N::pairseq)[n]) j0' j1') 1
            (TrMax (seg N j0' (Lng N - 1)))
            (TrMax (seg N j0' (Lng N - 1)) + 1)"
proof -
  let ?M = "(N::pairseq)[n]"
  let ?j1N = "Lng N - 1"
  let ?jm2 = "parent N 1 ?j1N"
  let ?w = "?j1N - ?jm2"
  let ?delta = "entry N 0 ?j1N - entry N 0 ?jm2"
  let ?Mp = "seg ?M j0' j1'"
  let ?Np = "seg N j0' ?j1N"
  let ?t = "TrMax ?Np"
  \<comment> \<open>basic facts\<close>
  have w0: "0 < ?w" using j0lt by linarith
  have j0'lt: "j0' < ?j1N" using j0'le j0lt by linarith
  have j0lt1: "j0' \<le> ?j1N" using j0'lt by linarith
  have j0ltM: "j0' \<le> j1'" using j0'lt bge by linarith
  have MpT: "?Mp \<in> T_PS" using j0ltM by (simp add: T_PS_def seg_def)
  have NpT: "?Np \<in> T_PS" using j0lt1 by (simp add: T_PS_def seg_def)
  have LMp: "Lng ?Mp = Suc j1' - j0'" by simp
  have LNp: "Lng ?Np = Suc ?j1N - j0'" by simp
  have LNp2: "1 < Lng ?Np" using j0'lt by simp
  have LNpval: "Lng ?Np - 2 = ?j1N - 1 - j0'" using LNp by simp
  \<comment> \<open>boundary index of \<open>?M\<close>: \<open>?j1N < Lng ?M\<close>\<close>
  have bnd: "?j1N < Lng ?M"
  proof -
    have "?j1N \<le> j1'" using bge .
    thus ?thesis using j1lt by simp
  qed
  have tb: "?t \<le> Lng ?Np - 1" by (rule TrMax_bound[OF NpT])
  \<comment> \<open>verbatim prefix agreement on \<open>[0, Lng N - 2 - j'\<^sub>0]\<close> (period intact below \<open>Lng N-1\<close>)\<close>
  let ?c = "Lng ?Np - 2"
  have agree: "\<And>s. s \<le> ?c \<Longrightarrow> ?Mp ! s = ?Np ! s"
  proof -
    fix s assume sc: "s \<le> ?c"
    have idxlt: "j0' + s < ?j1N" using sc LNpval j0'lt by linarith
    have sM: "s < Suc j1' - j0'" using sc LNpval bge j0'lt by linarith
    have sN: "s < Suc ?j1N - j0'" using sc LNpval j0'lt by linarith
    have "?Mp ! s = ?M ! (j0' + s)" using sM by (rule seg_nth_eq)
    also have "\<dots> = N ! (j0' + s)"
      by (rule oper_nth_lt[OF N L n1 idxlt])
    also have "\<dots> = ?Np ! s" using sN by (simp add: seg_nth_eq)
    finally show "?Mp ! s = ?Np ! s" .
  qed
  have cM: "?c < Lng ?Mp" using LMp LNpval bge j0'lt by linarith
  have cN: "?c < Lng ?Np" using LNp2 by linarith
  show ?thesis
  proof (cases "?t + 1 \<le> ?c")
    case easy: True
    \<comment> \<open>stop index inside the prefix; \<open>N\<^sub>p\<close>-side confinement from \<open>?t+1 \<le> c = Lng N\<^sub>p - 2\<close>\<close>
    have tNlt: "?t < Lng ?Np - 1" using easy by linarith
    show ?thesis
      by (rule nextR1_boundary_stop_of_prefix[OF MpT NpT agree cM cN tNlt easy])
  next
    case hard: False
    \<comment> \<open>\<open>?t \<ge> Lng N\<^sub>p - 2\<close>: the stop index reaches the block boundary\<close>
    have tge: "Lng ?Np - 2 \<le> ?t" using hard by linarith
    show ?thesis
    proof
      assume "nextR ?Mp 1 ?t (?t + 1)"
      hence step: "nextrel1 ?Mp ?t (?t + 1)" by (simp add: nextR_def)
      have rng: "?t + 1 < Lng ?Mp" using step by (simp add: nextrel1_def)
      \<comment> \<open>\<open>?t \<le> Lng N\<^sub>p - 1\<close> and \<open>j'\<^sub>0 + ?t \<le> Lng N - 1\<close> (block 0 or boundary)\<close>
      have t_le: "?t \<le> Lng ?Np - 1" by (rule tb)
      have idx_t_le: "j0' + ?t \<le> ?j1N" using t_le LNp j0'lt by linarith
      \<comment> \<open>HARD: \<open>?t \<ge> Lng N\<^sub>p - 2\<close> gives \<open>j'\<^sub>0+?t \<ge> Lng N - 2\<close>\<close>
      have idx_t_ge: "?j1N - 1 \<le> j0' + ?t" using tge LNp j0'lt by linarith
      \<comment> \<open>\<open>n \<ge> 2\<close>: the boundary node \<open>Lng N-1\<close> already sits in block 1 of \<open>?M\<close>\<close>
      have n2: "2 \<le> n"
      proof -
        have "?j1N < Lng ?M" by (rule bnd)
        also have "Lng ?M = ?jm2 + n * ?w"
          by (rule oper_d1pos_LngM[OF L notzero hp i1z j0lt])
        finally have "?jm2 + 1 * ?w < ?jm2 + n * ?w" using j0lt by simp
        hence "1 * ?w < n * ?w" by linarith
        thus ?thesis using w0 by (cases n) auto
      qed
      have qn: "1 < n" using n2 by simp
      \<comment> \<open>row-1 value at the boundary \<open>?t+1\<close>: it reduces to \<open>N\<^bsub>1, j\<^sub>-\<^sub>2\<^esub>\<close> (block-1 start)\<close>
      have idx_t1_le: "j0' + (?t + 1) \<le> ?j1N + 1" using idx_t_le by linarith
      \<comment> \<open>two boundary positions: \<open>j'\<^sub>0+(?t+1) = Lng N-1\<close> or \<open>= Lng N\<close> (only with \<open>w=1\<close>)\<close>
      have segt1: "entry ?Mp 1 (?t + 1) = entry N 1 ?jm2"
      proof -
        have t1lt: "?t + 1 < Suc j1' - j0'" using rng LMp by linarith
        have Mp_t1: "?Mp ! (?t + 1) = ?M ! (j0' + (?t + 1))" using t1lt by (rule seg_nth_eq)
        show ?thesis
        proof (cases "j0' + (?t + 1) = ?j1N")
          case True
          \<comment> \<open>\<open>?j1N = j\<^sub>-\<^sub>2 + 1\<cdot>w + 0\<close> (block 1, offset 0)\<close>
          have e1: "?j1N = ?jm2 + 1 * ?w + 0" using j0lt by simp
          have "?M ! (?jm2 + 1 * ?w + 0)
                  = (entry N 0 (?jm2 + 0) + 1 * ?delta, entry N 1 (?jm2 + 0))"
            by (rule oper_d1pos_nth[OF L notzero hp i1z j0lt qn]) (use w0 in simp)
          hence "?M ! ?j1N = (entry N 0 ?jm2 + ?delta, entry N 1 ?jm2)" using e1 by simp
          thus ?thesis using Mp_t1 True by (simp add: entry_def)
        next
          case False
          \<comment> \<open>then \<open>j'\<^sub>0+(?t+1) = Lng N\<close> (one past the boundary); this forces \<open>w = 1\<close>\<close>
          have eqLN: "j0' + (?t + 1) = ?j1N + 1" using False idx_t1_le idx_t_ge by linarith
          \<comment> \<open>boundary reachability: \<open>?j1N + 1 = j'\<^sub>0+?t+1 < Lng M' \<le> Lng M\<close>\<close>
          have ltM: "?j1N + 1 < Lng ?M"
          proof -
            have "j0' + (?t + 1) < Lng ?Mp + j0'" using rng by simp
            also have "\<dots> = Suc j1'" using LMp j0ltM by simp
            finally have "?j1N + 1 < Suc j1'" using eqLN by simp
            thus ?thesis using j1lt by simp
          qed
          \<comment> \<open>\<open>?t = Lng N\<^sub>p - 1\<close>: the trunk of \<open>N\<^sub>p\<close> fills, so its last step transfers to
            \<open>nextrel1 N (Lng N-2) (Lng N-1)\<close>; minimality of the row-1 parent \<open>j\<^sub>-\<^sub>2\<close>
            then forces \<open>j\<^sub>-\<^sub>2 = Lng N-2\<close>, i.e. \<open>w = 1\<close>\<close>
          have tLNp: "?t = Lng ?Np - 1" using eqLN LNp j0'lt by linarith
          have pre_lt: "Lng ?Np - 2 < ?t" using tLNp LNp2 by linarith
          have stepNp: "nextrel1 ?Np (Lng ?Np - 2) (Lng ?Np - 1)"
          proof -
            have "nextR ?Np 1 (Lng ?Np - 2) ((Lng ?Np - 2) + 1)"
              by (rule TrMax_trunk_step[OF NpT pre_lt])
            moreover have "(Lng ?Np - 2) + 1 = Lng ?Np - 1" using LNp2 by simp
            ultimately show ?thesis by (simp add: nextR_def)
          qed
          have aN: "Lng ?Np - 2 < Lng (seg N j0' ?j1N)" using LNp2 by simp
          have bN: "Lng ?Np - 1 < Lng (seg N j0' ?j1N)" using LNp2 by simp
          have idxlo: "j0' + (Lng ?Np - 2) = ?j1N - 1" using LNp j0'lt by simp
          have idxhi: "j0' + (Lng ?Np - 1) = ?j1N" using LNp j0'lt by simp
          have j1NltN: "?j1N < Lng N" using L by linarith
          have stepN: "nextrel1 N (?j1N - 1) ?j1N"
          proof -
            have "nextrel1 (seg N j0' ?j1N) (Lng ?Np - 2) (Lng ?Np - 1)
                    = nextrel1 N (j0' + (Lng ?Np - 2)) (j0' + (Lng ?Np - 1))"
              by (rule adm_nextrel1_seg[OF j1NltN aN bN])
            thus ?thesis using stepNp idxlo idxhi by simp
          qed
          \<comment> \<open>row-1 parent relation \<open>nextrel1 N j\<^sub>-\<^sub>2 (Lng N-1)\<close> and its minimality\<close>
          have hp1: "hasParent N 1 ?j1N" using hp i1z by simp
          have parR1: "nextR N 1 ?jm2 ?j1N"
            using hp1 unfolding hasParent_def parent_def by (rule theI')
          have nr1: "nextrel1 N ?jm2 ?j1N" using parR1 by (simp add: nextR_def)
          have w1: "?w = 1"
          proof (rule ccontr)
            assume "?w \<noteq> 1"
            hence "?jm2 < ?j1N - 1" using w0 j0lt by linarith
            have le0pred: "le0 N (?j1N - 1) ?j1N" using stepN by (simp add: nextrel1_def)
            have "entry N 1 ?j1N \<le> entry N 1 (?j1N - 1)"
              using nr1 \<open>?jm2 < ?j1N - 1\<close> le0pred by (simp add: nextrel1_def)
            moreover have "entry N 1 (?j1N - 1) < entry N 1 ?j1N"
              using stepN by (simp add: nextrel1_def)
            ultimately show False by linarith
          qed
          \<comment> \<open>\<open>Lng N = j\<^sub>-\<^sub>2 + 1\<cdot>1 + 1 = j\<^sub>-\<^sub>2 + 2\<cdot>1 + 0\<close>: block 2 offset 0 (with \<open>w=1\<close>)\<close>
          have e2: "?j1N + 1 = ?jm2 + 2 * ?w + 0" using w1 j0lt by simp
          have qn3: "2 < n"
          proof -
            have "?j1N + 1 < Lng ?M" by (rule ltM)
            also have "Lng ?M = ?jm2 + n * ?w"
              by (rule oper_d1pos_LngM[OF L notzero hp i1z j0lt])
            finally have "?jm2 + 2 * ?w < ?jm2 + n * ?w" using e2 by simp
            hence "2 * ?w < n * ?w" by linarith
            thus ?thesis using w1 by simp
          qed
          have "?M ! (?jm2 + 2 * ?w + 0)
                  = (entry N 0 (?jm2 + 0) + 2 * ?delta, entry N 1 (?jm2 + 0))"
            by (rule oper_d1pos_nth[OF L notzero hp i1z j0lt qn3]) (use w0 in simp)
          hence "?M ! (?j1N + 1) = (entry N 0 ?jm2 + 2 * ?delta, entry N 1 ?jm2)"
            using e2 by simp
          thus ?thesis using Mp_t1 eqLN by (simp add: entry_def)
        qed
      qed
      \<comment> \<open>row-1 weak increase along the reduced trunk: \<open>N\<^bsub>1,j\<^sub>-\<^sub>2\<^esub> \<le> entry M' 1 ?t\<close>\<close>
      have jjle: "?jm2 - j0' \<le> ?t"
      proof -
        have "?jm2 \<le> ?j1N - 1" using j0lt by linarith
        hence "?jm2 - j0' \<le> ?j1N - 1 - j0'" by linarith
        also have "\<dots> = Lng ?Np - 2" using LNpval by simp
        also have "\<dots> \<le> ?t" using tge by simp
        finally show ?thesis .
      qed
      have le1Np: "leR ?Np 1 (?jm2 - j0') ?t"
        by (rule trunk_le1[OF NpT jjle le_refl])
      have le1Np': "le1 ?Np (?jm2 - j0') ?t" using le1Np by (simp add: leR_def)
      have mono: "entry ?Np 1 (?jm2 - j0') \<le> entry ?Np 1 ?t"
        by (rule le1_imp_entry1_le[OF le1Np'])
      have e_jj: "entry ?Np 1 (?jm2 - j0') = entry N 1 ?jm2"
      proof -
        have lt: "?jm2 - j0' < Suc ?j1N - j0'" using j0lt j0'le by linarith
        have "?Np ! (?jm2 - j0') = N ! (j0' + (?jm2 - j0'))" using lt by (rule seg_nth_eq)
        also have "j0' + (?jm2 - j0') = ?jm2" using j0'le by simp
        finally show ?thesis by (simp add: entry_def)
      qed
      \<comment> \<open>\<open>entry M' 1 ?t\<close>: \<open>N\<^bsub>1,j\<^sub>-\<^sub>2\<^esub>\<close> (boundary reset, \<open>j'\<^sub>0+?t = Lng N-1\<close>) or
        \<open>entry N\<^sub>p 1 ?t\<close> (block 0, \<open>j'\<^sub>0+?t < Lng N-1\<close>) which is \<open>\<ge> N\<^bsub>1,j\<^sub>-\<^sub>2\<^esub>\<close> by \<open>mono\<close>\<close>
      have e_Mt: "entry N 1 ?jm2 \<le> entry ?Mp 1 ?t"
      proof (cases "j0' + ?t < ?j1N")
        case True
        \<comment> \<open>block-0: verbatim period, \<open>entry M' 1 ?t = entry N\<^sub>p 1 ?t\<close>\<close>
        have tlt: "?t < Suc j1' - j0'" using rng LMp by linarith
        have ltN: "?t < Suc ?j1N - j0'" using True by linarith
        have "?Mp ! ?t = ?M ! (j0' + ?t)" using tlt by (rule seg_nth_eq)
        also have "\<dots> = N ! (j0' + ?t)" by (rule oper_nth_lt[OF N L n1 True])
        also have "\<dots> = ?Np ! ?t" using ltN by (simp add: seg_nth_eq)
        finally have "entry ?Mp 1 ?t = entry ?Np 1 ?t" by (simp add: entry_def)
        thus ?thesis using e_jj mono by simp
      next
        case False
        \<comment> \<open>boundary: \<open>j'\<^sub>0+?t = Lng N-1 = j\<^sub>-\<^sub>2 + 1\<cdot>w + 0\<close> reset to \<open>N\<^bsub>1,j\<^sub>-\<^sub>2\<^esub>\<close>\<close>
        have eqj: "j0' + ?t = ?j1N" using idx_t_le False by linarith
        have tlt: "?t < Suc j1' - j0'" using rng LMp by linarith
        have e1: "?j1N = ?jm2 + 1 * ?w + 0" using j0lt by simp
        have "?Mp ! ?t = ?M ! (j0' + ?t)" using tlt by (rule seg_nth_eq)
        also have "\<dots> = ?M ! (?jm2 + 1 * ?w + 0)" using eqj e1 by simp
        also have "\<dots> = (entry N 0 (?jm2 + 0) + 1 * ?delta, entry N 1 (?jm2 + 0))"
          by (rule oper_d1pos_nth[OF L notzero hp i1z j0lt qn]) (use w0 in simp)
        finally have "entry ?Mp 1 ?t = entry N 1 ?jm2" by (simp add: entry_def)
        thus ?thesis by simp
      qed
      \<comment> \<open>combine: \<open>entry M' 1 (?t+1) = N\<^bsub>1,j\<^sub>-\<^sub>2\<^esub> \<le> entry M' 1 ?t\<close>\<close>
      have key: "entry ?Mp 1 (?t + 1) \<le> entry ?Mp 1 ?t"
        using segt1 e_Mt by simp
      \<comment> \<open>contradiction: \<open>nextrel1\<close> needs strict row-1 increase\<close>
      have "entry ?Mp 1 ?t < entry ?Mp 1 (?t + 1)" using step by (simp add: nextrel1_def)
      thus False using key by linarith
    qed
  qed
qed

lemma TrMax_seg_oper_d0zero_eq:
  assumes N: "N \<in> T_PS" and L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 0"
    and n1: "1 \<le> n"
    and j0'lt: "j0' < Lng N - 1"
    and bge: "Lng N - 2 \<le> j1'"
    and j1lt: "j1' < Lng ((N::pairseq)[n])"
    and stop: "\<not> nextR (seg ((N::pairseq)[n]) j0' j1') 1
                  (TrMax (seg N j0' (Lng N - 1)))
                  (TrMax (seg N j0' (Lng N - 1)) + 1)"
  shows "TrMax (seg ((N::pairseq)[n]) j0' j1') = TrMax (seg N j0' (Lng N - 1))"
proof -
  let ?M = "(N::pairseq)[n]"
  let ?j1N = "Lng N - 1"
  let ?Mp = "seg ?M j0' j1'"
  let ?Np = "seg N j0' ?j1N"
  let ?c = "?j1N - 1 - j0'"
  \<comment> \<open>both slices are non-empty, hence in \<open>T_PS\<close>\<close>
  have j0lt1: "j0' \<le> ?j1N" using j0'lt by linarith
  have j0ltM: "j0' \<le> j1'" using j0'lt bge by linarith
  have MpT: "?Mp \<in> T_PS" using j0ltM by (simp add: T_PS_def seg_def)
  have NpT: "?Np \<in> T_PS" using j0lt1 by (simp add: T_PS_def seg_def)
  \<comment> \<open>lengths\<close>
  have LMp: "Lng ?Mp = Suc j1' - j0'" by simp
  have LNp: "Lng ?Np = Suc ?j1N - j0'" by simp
  have LNp2: "1 < Lng ?Np" using j0'lt by simp
  \<comment> \<open>last row-1 entry of \<open>N'\<close> is \<open>N\<^bsub>1,j\<^sub>1\<^sup>N\<^esub> = 0\<close> (d0zero)\<close>
  have d0zero: "entry N 1 ?j1N = 0" using i1z by (simp add: idx1_def split: if_splits)
  have lastNp_idx: "Lng ?Np - 1 = ?j1N - j0'" using LNp by simp
  have lastNp: "?Np ! (Lng ?Np - 1) = N ! ?j1N"
  proof -
    have lt: "?j1N - j0' < Suc ?j1N - j0'" using j0'lt by linarith
    have "?Np ! (?j1N - j0') = N ! (j0' + (?j1N - j0'))" using lt by (rule seg_nth_eq)
    also have "j0' + (?j1N - j0') = ?j1N" using j0lt1 by simp
    finally show ?thesis using lastNp_idx by simp
  qed
  have zNp: "entry ?Np 1 (Lng ?Np - 1) = 0" using lastNp d0zero by (simp add: entry_def)
  \<comment> \<open>\<open>N'\<close>-trunk confined: \<open>TrMax N' < Lng N' - 1\<close>\<close>
  have tNlt: "TrMax ?Np < Lng ?Np - 1"
    by (rule TrMax_lt_last_of_row1_zero[OF NpT LNp2 zNp])
  have tnc: "TrMax ?Np \<le> ?c" using tNlt LNp by linarith
  \<comment> \<open>\<open>c\<close> within both slices\<close>
  have cN: "?c < Lng ?Np" using LNp j0'lt by linarith
  have cM: "?c < Lng ?Mp" using LMp bge j0'lt by linarith
  \<comment> \<open>pointwise agreement on \<open>[0, c]\<close>: period of \<open>N[n]\<close> intact below \<open>Lng N - 1\<close>\<close>
  have agree: "\<And>s. s \<le> ?c \<Longrightarrow> ?Mp ! s = ?Np ! s"
  proof -
    fix s assume sc: "s \<le> ?c"
    have sM: "s < Suc j1' - j0'" using sc cM LMp by linarith
    have sN: "s < Suc ?j1N - j0'" using sc cN LNp by linarith
    have idxlt: "j0' + s < ?j1N" using sc j0'lt by linarith
    have "?Mp ! s = ?M ! (j0' + s)" using sM by (rule seg_nth_eq)
    also have "\<dots> = N ! (j0' + s)" using oper_nth_lt[OF N L n1 idxlt] by simp
    also have "\<dots> = ?Np ! s" using sN by (simp add: seg_nth_eq)
    finally show "?Mp ! s = ?Np ! s" .
  qed
  show ?thesis
    by (rule TrMax_eq_of_prefix_agree[OF MpT NpT agree cM cN tnc stop])
qed

text \<open>Unconditional d0zero case-A \<open>TrMax\<close>-equality: discharge the boundary-stop
  hypothesis of @{thm [source] TrMax_seg_oper_d0zero_eq} via
  @{thm [source] nextR1_boundary_stop_d0zero_caseA}.  On the faithful case-A domain
  (\<open>j'\<^sub>0 < j\<^sub>0\<^sup>N\<close>, the article-1466 sub-case), \<open>TrMax (seg (N[n]) j'\<^sub>0 j'\<^sub>1) =
  TrMax (seg N j'\<^sub>0 (Lng N-1))\<close> holds without any extra assumption.\<close>

lemma TrMax_seg_oper_d0zero_eq_caseA:
  assumes N: "N \<in> T_PS" and L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 0"
    and parR0: "nextrel0 N (parent N 0 (Lng N - 1)) (Lng N - 1)"
    and n1: "1 \<le> n"
    and j0'lt0N: "j0' < parent N 0 (Lng N - 1)"
    and bge: "Lng N - 2 \<le> j1'"
    and j1lt: "j1' < Lng ((N::pairseq)[n])"
  shows "TrMax (seg ((N::pairseq)[n]) j0' j1') = TrMax (seg N j0' (Lng N - 1))"
proof -
  have j0Nlt: "parent N 0 (Lng N - 1) < Lng N - 1" using parR0 by (simp add: nextrel0_def)
  have j0'lt: "j0' < Lng N - 1" using j0'lt0N j0Nlt by linarith
  have stop: "\<not> nextR (seg ((N::pairseq)[n]) j0' j1') 1
                (TrMax (seg N j0' (Lng N - 1)))
                (TrMax (seg N j0' (Lng N - 1)) + 1)"
    by (rule nextR1_boundary_stop_d0zero_caseA[OF N L notzero hp i1z parR0 n1 j0'lt0N bge j1lt])
  show ?thesis
    by (rule TrMax_seg_oper_d0zero_eq[OF N L notzero hp i1z n1 j0'lt bge j1lt stop])
qed

end
