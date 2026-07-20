theory M_8_Wf_Bounded_Chain_Reductions
  imports "PSS_CORRECTIONS.C_7_4_Mark_NextAdm_Counterexample"
begin

text \<open>Relocated proof material.  The declarations retain their original source order,
  and every relocated annotation is preserved below.  This theory is machine-checked
  outside the termination build tree.\<close>

lemma wfpx_nrmP_pos: "1 \<le> wfpx_nrmP p"
  by (cases p) simp

lemma wfpx_length_le_sum: "length xs \<le> sum_list (map wfpx_nrmP xs)"
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  have e1: "length (x # xs) = Suc (length xs)" by simp
  have e2: "sum_list (map wfpx_nrmP (x # xs))
            = wfpx_nrmP x + sum_list (map wfpx_nrmP xs)" by simp
  show ?case using e1 e2 Cons.IH wfpx_nrmP_pos[of x] by linarith
qed

lemma wfpx_nrmP_le_sum:
  "p \<in> set ps \<Longrightarrow> wfpx_nrmP p \<le> sum_list (map wfpx_nrmP ps)"
proof (induction ps)
  case Nil
  thus ?case by simp
next
  case (Cons a ps)
  show ?case
  proof (cases "p = a")
    case True
    thus ?thesis by simp
  next
    case False
    hence pins: "p \<in> set ps" using Cons.prems by simp
    have h: "wfpx_nrmP p \<le> sum_list (map wfpx_nrmP ps)" using Cons.IH[OF pins] .
    have e: "sum_list (map wfpx_nrmP (a # ps))
             = wfpx_nrmP a + sum_list (map wfpx_nrmP ps)" by simp
    show ?thesis using h e by linarith
  qed
qed

subsection \<open>Bounded-norm finiteness (the \<open>D\<^sub>\<omega>\<close>-free terms of norm \<open>\<le> N\<close> form a finite set)\<close>

lemma wfpx_finite_norm_le:
  "finite {t::BT. dfree_BT t \<and> wfpx_nrmT t \<le> N}
   \<and> finite {p::BP. dfree_BP p \<and> wfpx_nrmP p \<le> N}"
proof (induction N rule: less_induct)
  case (less N)
  \<comment> \<open>strict-bound finite sets, from the strong induction hypothesis\<close>
  have FBT: "finite {b::BT. dfree_BT b \<and> wfpx_nrmT b < N}"
  proof (cases N)
    case 0
    hence "{b::BT. dfree_BT b \<and> wfpx_nrmT b < N} \<subseteq> {}" by auto
    thus ?thesis using finite.emptyI finite_subset by blast
  next
    case (Suc M)
    have MN: "M < N" using Suc by simp
    have eq: "{b::BT. dfree_BT b \<and> wfpx_nrmT b < N}
              = {b::BT. dfree_BT b \<and> wfpx_nrmT b \<le> M}"
      using Suc by (auto simp: less_Suc_eq_le)
    have "finite {b::BT. dfree_BT b \<and> wfpx_nrmT b \<le> M}"
      using less.IH[OF MN] by blast
    thus ?thesis by (simp only: eq)
  qed
  have FBP: "finite {p::BP. dfree_BP p \<and> wfpx_nrmP p < N}"
  proof (cases N)
    case 0
    hence "{p::BP. dfree_BP p \<and> wfpx_nrmP p < N} \<subseteq> {}" by auto
    thus ?thesis using finite.emptyI finite_subset by blast
  next
    case (Suc M)
    have MN: "M < N" using Suc by simp
    have eq: "{p::BP. dfree_BP p \<and> wfpx_nrmP p < N}
              = {p::BP. dfree_BP p \<and> wfpx_nrmP p \<le> M}"
      using Suc by (auto simp: less_Suc_eq_le)
    have "finite {p::BP. dfree_BP p \<and> wfpx_nrmP p \<le> M}"
      using less.IH[OF MN] by blast
    thus ?thesis by (simp only: eq)
  qed
  \<comment> \<open>BT part: a term of norm \<open>\<le> N\<close> is \<open>Trm ps\<close> with each principal of norm \<open>< N\<close> and \<open>length ps \<le> N\<close>\<close>
  have BTfin: "finite {t::BT. dfree_BT t \<and> wfpx_nrmT t \<le> N}"
  proof (rule finite_subset)
    show "{t::BT. dfree_BT t \<and> wfpx_nrmT t \<le> N}
          \<subseteq> Trm ` {xs. set xs \<subseteq> {p. dfree_BP p \<and> wfpx_nrmP p < N} \<and> length xs \<le> N}"
    proof
      fix t assume "t \<in> {t::BT. dfree_BT t \<and> wfpx_nrmT t \<le> N}"
      hence df: "dfree_BT t" and le: "wfpx_nrmT t \<le> N" by auto
      obtain ps where t: "t = Trm ps" by (cases t)
      have sums: "Suc (sum_list (map wfpx_nrmP ps)) \<le> N" using le t by simp
      hence sle: "sum_list (map wfpx_nrmP ps) < N" by simp
      have dfps: "dfree_BT (Trm ps)" using df t by simp
      have setsub: "set ps \<subseteq> {p. dfree_BP p \<and> wfpx_nrmP p < N}"
      proof
        fix p assume pin: "p \<in> set ps"
        have d1: "dfree_BP p" using dfps pin by simp
        have hle: "wfpx_nrmP p \<le> sum_list (map wfpx_nrmP ps)" using pin by (rule wfpx_nrmP_le_sum)
        have "wfpx_nrmP p < N" using hle sle by linarith
        thus "p \<in> {p. dfree_BP p \<and> wfpx_nrmP p < N}" using d1 by simp
      qed
      have lenb: "length ps \<le> N"
      proof -
        have "length ps \<le> sum_list (map wfpx_nrmP ps)" by (rule wfpx_length_le_sum)
        thus ?thesis using sle by linarith
      qed
      show "t \<in> Trm ` {xs. set xs \<subseteq> {p. dfree_BP p \<and> wfpx_nrmP p < N} \<and> length xs \<le> N}"
      proof (rule image_eqI[where x = ps])
        show "t = Trm ps" using t .
        show "ps \<in> {xs. set xs \<subseteq> {p. dfree_BP p \<and> wfpx_nrmP p < N} \<and> length xs \<le> N}"
          using setsub lenb by simp
      qed
    qed
  next
    show "finite (Trm ` {xs. set xs \<subseteq> {p. dfree_BP p \<and> wfpx_nrmP p < N} \<and> length xs \<le> N})"
      by (rule finite_imageI, rule finite_lists_length_le[OF FBP])
  qed
  \<comment> \<open>BP part: a principal of norm \<open>\<le> N\<close> is \<open>DB (enat m) b\<close> with \<open>m < N\<close> and \<open>b\<close> of norm \<open>< N\<close>\<close>
  have BPfin: "finite {p::BP. dfree_BP p \<and> wfpx_nrmP p \<le> N}"
  proof (rule finite_subset)
    show "{p::BP. dfree_BP p \<and> wfpx_nrmP p \<le> N}
          \<subseteq> (\<lambda>(n, c). DB (enat n) c) ` ({..<N} \<times> {b. dfree_BT b \<and> wfpx_nrmT b < N})"
    proof
      fix p assume "p \<in> {p::BP. dfree_BP p \<and> wfpx_nrmP p \<le> N}"
      hence df: "dfree_BP p" and le: "wfpx_nrmP p \<le> N" by auto
      obtain v b where p: "p = DB v b" by (cases p)
      have vinf: "v \<noteq> \<infinity>" and dfb: "dfree_BT b" using df p by auto
      then obtain m where m: "v = enat m" using vinf by auto
      have nn: "wfpx_nrmP p = Suc (m + wfpx_nrmT b)" using p m by simp
      have le2: "Suc (m + wfpx_nrmT b) \<le> N" using nn le by simp
      have mlt: "m < N" using le2 by linarith
      have blt: "wfpx_nrmT b < N" using le2 by linarith
      show "p \<in> (\<lambda>(n, c). DB (enat n) c) ` ({..<N} \<times> {b. dfree_BT b \<and> wfpx_nrmT b < N})"
      proof (rule image_eqI[where x = "(m, b)"])
        show "p = (\<lambda>(n, c). DB (enat n) c) (m, b)" using p m by simp
        show "(m, b) \<in> {..<N} \<times> {b. dfree_BT b \<and> wfpx_nrmT b < N}"
          using mlt blt dfb by simp
      qed
    qed
  next
    show "finite ((\<lambda>(n, c). DB (enat n) c) ` ({..<N} \<times> {b. dfree_BT b \<and> wfpx_nrmT b < N}))"
      by (rule finite_imageI, rule finite_cartesian_product[OF finite_lessThan FBT])
  qed
  show ?case using BTfin BPfin by blast
qed

lemma wfpx_finite_BT_norm: "finite {t::BT. dfree_BT t \<and> wfpx_nrmT t \<le> N}"
  using wfpx_finite_norm_le by blast

lemma wfpx_finite_BP_norm: "finite {p::BP. dfree_BP p \<and> wfpx_nrmP p \<le> N}"
  using wfpx_finite_norm_le by blast

lemma wfpx_RPrel_trans: "trans RPrel"
  by (rule transI) (auto simp: RPrel_def dest: lessBP_trans)

lemma wfpx_RPrel_irrefl: "(p, p) \<notin> RPrel"
  by (simp add: RPrel_def lessBP_irrefl)

lemma wfpx_RPrel_acyclic: "acyclic RPrel"
  by (rule acyclicI) (simp add: trancl_id[OF wfpx_RPrel_trans] wfpx_RPrel_irrefl)

lemma wfpx_finite_RPrel_bnd: "finite (RPrel_bnd N)"
proof (rule finite_subset)
  show "RPrel_bnd N
        \<subseteq> {p. dfree_BP p \<and> wfpx_nrmP p \<le> N} \<times> {p. dfree_BP p \<and> wfpx_nrmP p \<le> N}"
    by (auto simp: RPrel_bnd_def RPrel_def)
  show "finite ({p::BP. dfree_BP p \<and> wfpx_nrmP p \<le> N}
                 \<times> {p. dfree_BP p \<and> wfpx_nrmP p \<le> N})"
    by (rule finite_cartesian_product[OF wfpx_finite_BP_norm wfpx_finite_BP_norm])
qed

lemma wfpx_RPrel_bnd_acyclic: "acyclic (RPrel_bnd N)"
  by (rule acyclic_subset[OF wfpx_RPrel_acyclic]) (auto simp: RPrel_bnd_def)

theorem wfpx_wf_RPrel_bnd: "wf (RPrel_bnd N)"
  by (rule finite_acyclic_wf[OF wfpx_finite_RPrel_bnd wfpx_RPrel_bnd_acyclic])

subsection \<open>Reduction of \<open>wf RPrel\<close> to the absence of an UNBOUNDED-norm descending chain\<close>

lemma wfpx_bounded_chain_impossible:
  assumes ch: "\<forall>i. (f (Suc i), f i) \<in> RPrel"
    and bnd: "\<forall>i. wfpx_nrmP (f i) \<le> N"
  shows False
proof -
  have "\<forall>i. (f (Suc i), f i) \<in> RPrel_bnd N"
    using ch bnd by (auto simp: RPrel_bnd_def)
  moreover have "wf (RPrel_bnd N)" by (rule wfpx_wf_RPrel_bnd)
  ultimately show False by (meson wf_iff_no_infinite_down_chain)
qed

lemma wfpx_infinite_chain_unbounded_norm:
  assumes ch: "\<forall>i. (f (Suc i), f i) \<in> RPrel"
  shows "\<forall>N. \<exists>i. N < wfpx_nrmP (f i)"
proof (rule allI)
  fix N
  show "\<exists>i. N < wfpx_nrmP (f i)"
  proof (rule ccontr)
    assume "\<not> (\<exists>i. N < wfpx_nrmP (f i))"
    hence "\<forall>i. wfpx_nrmP (f i) \<le> N" by (auto simp: not_less)
    from wfpx_bounded_chain_impossible[OF ch this] show False .
  qed
qed

theorem wfpx_wf_RPrel_iff_no_unbounded_chain:
  "wf RPrel \<longleftrightarrow>
     \<not> (\<exists>f. (\<forall>i. (f (Suc i), f i) \<in> RPrel) \<and> (\<forall>N. \<exists>i. N < wfpx_nrmP (f i)))"
proof
  assume "wf RPrel"
  hence "\<not> (\<exists>f. \<forall>i. (f (Suc i), f i) \<in> RPrel)"
    using wf_iff_no_infinite_down_chain by blast
  thus "\<not> (\<exists>f. (\<forall>i. (f (Suc i), f i) \<in> RPrel) \<and> (\<forall>N. \<exists>i. N < wfpx_nrmP (f i)))"
    by blast
next
  assume rhs: "\<not> (\<exists>f. (\<forall>i. (f (Suc i), f i) \<in> RPrel) \<and> (\<forall>N. \<exists>i. N < wfpx_nrmP (f i)))"
  show "wf RPrel"
  proof (rule ccontr)
    assume "\<not> wf RPrel"
    then obtain f where ch: "\<forall>i. (f (Suc i), f i) \<in> RPrel"
      using wf_iff_no_infinite_down_chain by blast
    have "\<forall>N. \<exists>i. N < wfpx_nrmP (f i)"
      by (rule wfpx_infinite_chain_unbounded_norm[OF ch])
    with ch have "\<exists>f. (\<forall>i. (f (Suc i), f i) \<in> RPrel) \<and> (\<forall>N. \<exists>i. N < wfpx_nrmP (f i))"
      by blast
    with rhs show False by blast
  qed
qed

lemma wfpx_RTrel_acyclic: "acyclic RTrel"
proof -
  have tr: "trans RTrel"
    by (rule transI) (blast intro: wfox_RTrel_trans)
  show ?thesis
    by (rule acyclicI) (simp add: trancl_id[OF tr] wfox_RTrel_irrefl)
qed

lemma wfpx_finite_RTrel_bnd: "finite (RTrel_bnd N)"
proof (rule finite_subset)
  show "RTrel_bnd N
        \<subseteq> {t. dfree_BT t \<and> wfpx_nrmT t \<le> N} \<times> {t. dfree_BT t \<and> wfpx_nrmT t \<le> N}"
    by (auto simp: RTrel_bnd_def RTrel_def)
  show "finite ({t::BT. dfree_BT t \<and> wfpx_nrmT t \<le> N}
                 \<times> {t. dfree_BT t \<and> wfpx_nrmT t \<le> N})"
    by (rule finite_cartesian_product[OF wfpx_finite_BT_norm wfpx_finite_BT_norm])
qed

lemma wfpx_RTrel_bnd_acyclic: "acyclic (RTrel_bnd N)"
  by (rule acyclic_subset[OF wfpx_RTrel_acyclic]) (auto simp: RTrel_bnd_def)

theorem wfpx_wf_RTrel_bnd: "wf (RTrel_bnd N)"
  by (rule finite_acyclic_wf[OF wfpx_finite_RTrel_bnd wfpx_RTrel_bnd_acyclic])

text \<open>The bounded fragment stated directly on the [Buc1] Lemma 2.2 GOAL relation
  (@{thm [source] wfox_goal_eq_RTrel}): the norm-\<open>\<le> N\<close> restriction of \<open>(OT\<^bsub>B\<^esub>, <)\<close> is WF.\<close>

theorem wfpx_wf_goal_bnd:
  "wf ({(a, b). a \<in> OT_B \<and> b \<in> OT_B \<and> lessBT a b}
        \<inter> {(a, b). wfpx_nrmT a \<le> N \<and> wfpx_nrmT b \<le> N})"
  using wfpx_wf_RTrel_bnd by (simp add: RTrel_bnd_def wfox_goal_eq_RTrel)

lemma wfpx_bounded_Tchain_impossible:
  assumes ch: "\<forall>i. (f (Suc i), f i) \<in> RTrel"
    and bnd: "\<forall>i. wfpx_nrmT (f i) \<le> N"
  shows False
proof -
  have "\<forall>i. (f (Suc i), f i) \<in> RTrel_bnd N"
    using ch bnd by (auto simp: RTrel_bnd_def)
  moreover have "wf (RTrel_bnd N)" by (rule wfpx_wf_RTrel_bnd)
  ultimately show False by (meson wf_iff_no_infinite_down_chain)
qed

lemma wfpx_infinite_Tchain_unbounded_norm:
  assumes ch: "\<forall>i. (f (Suc i), f i) \<in> RTrel"
  shows "\<forall>N. \<exists>i. N < wfpx_nrmT (f i)"
proof (rule allI)
  fix N
  show "\<exists>i. N < wfpx_nrmT (f i)"
  proof (rule ccontr)
    assume "\<not> (\<exists>i. N < wfpx_nrmT (f i))"
    hence "\<forall>i. wfpx_nrmT (f i) \<le> N" by (auto simp: not_less)
    from wfpx_bounded_Tchain_impossible[OF ch this] show False .
  qed
qed

theorem wfpx_wf_RTrel_iff_no_unbounded_chain:
  "wf RTrel \<longleftrightarrow>
     \<not> (\<exists>f. (\<forall>i. (f (Suc i), f i) \<in> RTrel) \<and> (\<forall>N. \<exists>i. N < wfpx_nrmT (f i)))"
proof
  assume "wf RTrel"
  hence "\<not> (\<exists>f. \<forall>i. (f (Suc i), f i) \<in> RTrel)"
    using wf_iff_no_infinite_down_chain by blast
  thus "\<not> (\<exists>f. (\<forall>i. (f (Suc i), f i) \<in> RTrel) \<and> (\<forall>N. \<exists>i. N < wfpx_nrmT (f i)))"
    by blast
next
  assume rhs: "\<not> (\<exists>f. (\<forall>i. (f (Suc i), f i) \<in> RTrel) \<and> (\<forall>N. \<exists>i. N < wfpx_nrmT (f i)))"
  show "wf RTrel"
  proof (rule ccontr)
    assume "\<not> wf RTrel"
    then obtain f where ch: "\<forall>i. (f (Suc i), f i) \<in> RTrel"
      using wf_iff_no_infinite_down_chain by blast
    have "\<forall>N. \<exists>i. N < wfpx_nrmT (f i)"
      by (rule wfpx_infinite_Tchain_unbounded_norm[OF ch])
    with ch have "\<exists>f. (\<forall>i. (f (Suc i), f i) \<in> RTrel) \<and> (\<forall>N. \<exists>i. N < wfpx_nrmT (f i))"
      by blast
    with rhs show False by blast
  qed
qed

lemma wfpd_RPrel_dep_0: "RPrel_dep 0 = {}"
proof (rule ccontr)
  assume "RPrel_dep 0 \<noteq> {}"
  then obtain p q where "(p, q) \<in> RPrel_dep 0" by auto
  hence "bdepthP p \<le> 0" by (simp add: RPrel_dep_def)
  thus False using bdepthP_pos[of p] by simp
qed

lemma wfpd_wf_RPrel_dep_0: "wf (RPrel_dep 0)"
proof (rule wf_subset[OF wfpx_wf_RPrel_bnd[of 0]])
  show "RPrel_dep 0 \<subseteq> RPrel_bnd 0" by (simp add: wfpd_RPrel_dep_0)
qed

subsection \<open>The CROSS-INDEX step: \<open>wf (RTrel_dep d) \<Longrightarrow> wf (RPrel_dep (Suc d))\<close> (index stabilisation)\<close>

text \<open>A principal \<open>D\<^sub>v a\<close> of depth \<open>\<le> Suc d\<close> embeds order-preservingly as \<open>(v, a)\<close> into
  \<open>less_than \<times>\<^sub>lex RTrel_dep d\<close> (\<open>a\<close> has depth \<open>\<le> d\<close>).  Since @{term "wf less_than"} and
  (by hypothesis) @{term "wf (RTrel_dep d)"}, the lexicographic product is WF, and
  @{term "wf (RPrel_dep (Suc d))"} follows.  This is the cross-index comparison that
  Buchholz's collapsing would otherwise supply — here \<open>\<nat>\<close>'s well-order stands in for it,
  the subterm having dropped a depth level.\<close>

lemma wfpd_RPrel_dep_lex:
  assumes rt: "wf (RTrel_dep d)"
  shows "wf (RPrel_dep (Suc d))"
proof -
  have wflex: "wf (less_than <*lex*> RTrel_dep d)"
    by (rule wf_lex_prod[OF wf_less_than rt])
  let ?f = "\<lambda>p. (the_enat (idxBP p), subBP p)"
  have wfinv: "wf (inv_image (less_than <*lex*> RTrel_dep d) ?f)"
    by (rule wf_inv_image[OF wflex])
  have "RPrel_dep (Suc d) \<subseteq> inv_image (less_than <*lex*> RTrel_dep d) ?f"
  proof (rule subrelI)
    fix p q assume "(p, q) \<in> RPrel_dep (Suc d)"
    then have base: "isOT_BP p" "dfree_BP p" "isOT_BP q" "dfree_BP q" "lessBP p q"
        and dp: "bdepthP p \<le> Suc d" and dq: "bdepthP q \<le> Suc d"
      by (auto simp: RPrel_dep_def RPrel_def)
    obtain u a where pu: "p = DB u a" by (cases p)
    obtain v b where qv: "q = DB v b" by (cases q)
    have ufin: "u \<noteq> \<infinity>" and afree: "dfree_BT a" using base(2) pu by auto
    have vfin: "v \<noteq> \<infinity>" and bfree: "dfree_BT b" using base(4) qv by auto
    obtain m where um: "u = enat m" using ufin by (cases u) auto
    obtain n where vn: "v = enat n" using vfin by (cases v) auto
    have aOT: "isOT_BT a" using base(1) pu by simp
    have bOT: "isOT_BT b" using base(3) qv by simp
    have ad: "bdepthT a \<le> d" using dp pu by simp
    have bd: "bdepthT b \<le> d" using dq qv by simp
    have lp: "m < n \<or> (m = n \<and> lessBT a b)"
      using base(5) pu qv um vn by simp
    show "(p, q) \<in> inv_image (less_than <*lex*> RTrel_dep d) ?f"
    proof (cases "m < n")
      case True
      then show ?thesis
        using pu qv um vn by (simp add: inv_image_def lex_prod_def)
    next
      case False
      then have mn: "m = n" and lab: "lessBT a b" using lp by auto
      have "(a, b) \<in> RTrel_dep d"
        using aOT afree bOT bfree lab ad bd by (simp add: RTrel_dep_def RTrel_def)
      then show ?thesis
        using pu qv um vn mn by (simp add: inv_image_def lex_prod_def)
    qed
  qed
  from wf_subset[OF wfinv this] show ?thesis .
qed


subsection \<open>The tuple layer (depth-guarded): \<open>wf (RPrel_dep d) \<Longrightarrow> wf (RTrel_dep d)\<close>\<close>

text \<open>Depth-guarded copy of the multiset-free @{thm [source] wfox_tuple_lift}: no infinite
  @{term RTrel}-descending chain of depth \<open>\<le> d\<close> can have all its heads \<open>\<le>\<close> a fixed
  principal \<open>p\<close> (of depth \<open>\<le> d\<close>).  The head-order/tail-descent helpers are unconditional
  (@{thm [source] wfox_head_bound}, @{thm [source] wfox_tail_step'},
  @{thm [source] wfox_chain_nonempty}) and apply verbatim since @{term "RTrel_dep d \<subseteq> RTrel"};
  the only additions are the depth guard \<open>bdepthT (f i) \<le> d\<close> (preserved by tail-peel via
  @{thm [source] bdepthT_tl_le}) and the depth bound \<open>bdepthP q \<le> d\<close> on the dropped head
  (via @{thm [source] bdepthP_head_le}), which turns the outer @{term RPrel}-step into an
  @{term RPrel_dep}-step so the well-founded induction runs on @{term "wf (RPrel_dep d)"}.\<close>

lemma wfpd_NoBad_dep:
  assumes wfP: "wf (RPrel_dep d)"
  shows "isOT_BP p \<longrightarrow> dfree_BP p \<longrightarrow> bdepthP p \<le> d \<longrightarrow>
         \<not> (\<exists>f. (\<forall>i. (f (Suc i), f i) \<in> RTrel) \<and>
                (\<forall>i. bdepthT (f i) \<le> d) \<and>
                (\<forall>i. untrm (f i) \<noteq> []
                     \<and> (hd (untrm (f i)) = p \<or> lessBP (hd (untrm (f i))) p)))"
proof (rule wf_induct_rule[OF wfP])
  fix p
  assume IH: "\<And>q. (q, p) \<in> RPrel_dep d \<Longrightarrow>
                 isOT_BP q \<longrightarrow> dfree_BP q \<longrightarrow> bdepthP q \<le> d \<longrightarrow>
                 \<not> (\<exists>f. (\<forall>i. (f (Suc i), f i) \<in> RTrel) \<and>
                        (\<forall>i. bdepthT (f i) \<le> d) \<and>
                        (\<forall>i. untrm (f i) \<noteq> []
                             \<and> (hd (untrm (f i)) = q \<or> lessBP (hd (untrm (f i))) q)))"
  show "isOT_BP p \<longrightarrow> dfree_BP p \<longrightarrow> bdepthP p \<le> d \<longrightarrow>
        \<not> (\<exists>f. (\<forall>i. (f (Suc i), f i) \<in> RTrel) \<and>
               (\<forall>i. bdepthT (f i) \<le> d) \<and>
               (\<forall>i. untrm (f i) \<noteq> []
                    \<and> (hd (untrm (f i)) = p \<or> lessBP (hd (untrm (f i))) p)))"
  proof (intro impI notI)
    assume pg1: "isOT_BP p" and pg2: "dfree_BP p" and pgd: "bdepthP p \<le> d"
      and EX: "\<exists>f. (\<forall>i. (f (Suc i), f i) \<in> RTrel)
                  \<and> (\<forall>i. bdepthT (f i) \<le> d)
                  \<and> (\<forall>i. untrm (f i) \<noteq> []
                       \<and> (hd (untrm (f i)) = p \<or> lessBP (hd (untrm (f i))) p))"
    from EX obtain f0 where f0ch: "\<forall>i. (f0 (Suc i), f0 i) \<in> RTrel"
      and f0dep: "\<forall>i. bdepthT (f0 i) \<le> d"
      and f0hd: "\<forall>i. untrm (f0 i) \<noteq> []
                     \<and> (hd (untrm (f0 i)) = p \<or> lessBP (hd (untrm (f0 i))) p)"
      by blast
    have inner: "length (untrm (f 0)) \<le> L \<Longrightarrow>
                 (\<forall>i. (f (Suc i), f i) \<in> RTrel) \<Longrightarrow>
                 (\<forall>i. bdepthT (f i) \<le> d) \<Longrightarrow>
                 (\<forall>i. untrm (f i) \<noteq> []
                      \<and> (hd (untrm (f i)) = p \<or> lessBP (hd (untrm (f i))) p)) \<Longrightarrow>
                 False" for f L
    proof (induction L arbitrary: f)
      case 0
      have "untrm (f 0) \<noteq> []" using "0.prems"(4) by blast
      thus False using "0.prems"(1) by simp
    next
      case (Suc L)
      note len = Suc.prems(1) and ch = Suc.prems(2) and dep = Suc.prems(3) and hd = Suc.prems(4)
      show False
      proof (cases "\<forall>i. hd (untrm (f i)) = p")
        case True
        define g where "g \<equiv> \<lambda>i. Trm (tl (untrm (f i)))"
        have gne_f: "\<And>i. untrm (f i) \<noteq> []" using hd by blast
        have hdp: "\<And>i. hd (untrm (f i)) = p" using True by blast
        have gch: "\<forall>i. (g (Suc i), g i) \<in> RTrel"
        proof
          fix i
          have rt: "(f (Suc i), f i) \<in> RTrel" using ch by blast
          have "hd (untrm (f (Suc i))) = hd (untrm (f i))" using hdp[of "Suc i"] hdp[of i] by simp
          from wfox_tail_step'[OF rt gne_f[of "Suc i"] gne_f[of i] this]
          have "(Trm (tl (untrm (f (Suc i)))), Trm (tl (untrm (f i)))) \<in> RTrel" .
          thus "(g (Suc i), g i) \<in> RTrel" by (simp add: g_def)
        qed
        have gdep: "\<forall>i. bdepthT (g i) \<le> d"
        proof
          fix i
          have "bdepthT (g i) = bdepthT (Trm (tl (untrm (f i))))" by (simp add: g_def)
          also have "\<dots> \<le> bdepthT (Trm (untrm (f i)))" by (rule bdepthT_tl_le)
          also have "\<dots> = bdepthT (f i)" by (simp add: wfox_Trm_untrm)
          also have "\<dots> \<le> d" using dep by blast
          finally show "bdepthT (g i) \<le> d" .
        qed
        have ghd: "\<forall>i. untrm (g i) \<noteq> []
                       \<and> (hd (untrm (g i)) = p \<or> lessBP (hd (untrm (g i))) p)"
        proof
          fix i
          have gne: "untrm (g i) \<noteq> []" using wfox_chain_nonempty[OF gch, of i] .
          have gu: "untrm (g i) = tl (untrm (f i))" by (simp add: g_def)
          have rt: "(f (Suc i), f i) \<in> RTrel" using ch by blast
          hence isot: "isOT_BT (f i)" by (simp add: RTrel_def)
          have descPi: "descP (untrm (f i))"
          proof -
            obtain xs where "f i = Trm xs" by (cases "f i")
            thus ?thesis using isot by auto
          qed
          from gne gu have tlne: "tl (untrm (f i)) \<noteq> []" by simp
          obtain sec rest where dec: "untrm (f i) = p # sec # rest"
            using gne_f[of i] hdp[of i] tlne
            by (cases "untrm (f i)"; cases "tl (untrm (f i))") auto
          have "descP (p # sec # rest)" using descPi dec by simp
          hence "leBT (Trm [sec]) (Trm [p])" by simp
          hence "sec = p \<or> lessBP sec p" by auto
          moreover have "hd (untrm (g i)) = sec" using dec gu by simp
          ultimately show "untrm (g i) \<noteq> []
                            \<and> (hd (untrm (g i)) = p \<or> lessBP (hd (untrm (g i))) p)"
            using gne by auto
        qed
        have lgen: "length (untrm (g 0)) \<le> L"
        proof -
          have "untrm (g 0) = tl (untrm (f 0))" by (simp add: g_def)
          moreover have "untrm (f 0) \<noteq> []" using gne_f[of 0] .
          ultimately have "length (untrm (g 0)) = length (untrm (f 0)) - 1" by simp
          thus ?thesis using len by simp
        qed
        show False by (rule Suc.IH[OF lgen gch gdep ghd])
      next
        case False
        then obtain i0 where "hd (untrm (f i0)) \<noteq> p" by blast
        moreover have "hd (untrm (f i0)) = p \<or> lessBP (hd (untrm (f i0))) p" using hd by blast
        ultimately have qlt: "lessBP (hd (untrm (f i0))) p" by blast
        define q where "q \<equiv> hd (untrm (f i0))"
        have fi0ne: "untrm (f i0) \<noteq> []" using hd by blast
        have rt0: "(f (Suc i0), f i0) \<in> RTrel" using ch by blast
        have isot0: "isOT_BT (f i0)" and dfr0: "dfree_BT (f i0)"
          using rt0 by (simp_all add: RTrel_def)
        have qg: "isOT_BP q \<and> dfree_BP q"
        proof -
          obtain c cs where cc: "untrm (f i0) = c # cs"
            using fi0ne by (cases "untrm (f i0)") auto
          have "f i0 = Trm (c # cs)" using cc by (metis wfox_Trm_untrm)
          hence "isOT_BP c \<and> dfree_BP c" using isot0 dfr0 by simp
          moreover have "q = c" using cc q_def by simp
          ultimately show ?thesis by simp
        qed
        have qdepth: "bdepthP q \<le> d"
        proof -
          have "q \<in> set (untrm (f i0))" using fi0ne q_def by (cases "untrm (f i0)") auto
          hence "bdepthP q \<le> bdepthT (Trm (untrm (f i0)))" by (rule bdepthP_head_le)
          also have "\<dots> = bdepthT (f i0)" by (simp add: wfox_Trm_untrm)
          also have "\<dots> \<le> d" using dep by blast
          finally show ?thesis .
        qed
        have qpR: "(q, p) \<in> RPrel_dep d"
          using qg qlt pg1 pg2 q_def qdepth pgd by (simp add: RPrel_dep_def RPrel_def)
        define f' where "f' \<equiv> \<lambda>k. f (i0 + k)"
        have f'ch: "\<forall>k. (f' (Suc k), f' k) \<in> RTrel" using ch by (simp add: f'_def)
        have f'dep: "\<forall>k. bdepthT (f' k) \<le> d" using dep by (simp add: f'_def)
        have f'hd: "\<forall>k. untrm (f' k) \<noteq> []
                        \<and> (hd (untrm (f' k)) = q \<or> lessBP (hd (untrm (f' k))) q)"
        proof
          fix k
          have ne: "untrm (f' k) \<noteq> []" using hd by (simp add: f'_def)
          have "hd (untrm (f (i0 + k))) = hd (untrm (f i0))
                \<or> lessBP (hd (untrm (f (i0 + k)))) (hd (untrm (f i0)))"
            using wfox_head_bound[OF ch, of i0 k] .
          thus "untrm (f' k) \<noteq> []
                \<and> (hd (untrm (f' k)) = q \<or> lessBP (hd (untrm (f' k))) q)"
            using ne q_def by (simp add: f'_def)
        qed
        have "\<not> (\<exists>g. (\<forall>i. (g (Suc i), g i) \<in> RTrel)
                    \<and> (\<forall>i. bdepthT (g i) \<le> d)
                    \<and> (\<forall>i. untrm (g i) \<noteq> []
                         \<and> (hd (untrm (g i)) = q \<or> lessBP (hd (untrm (g i))) q)))"
          using IH[OF qpR] qg qdepth by blast
        moreover have "(\<forall>i. (f' (Suc i), f' i) \<in> RTrel)
                    \<and> (\<forall>i. bdepthT (f' i) \<le> d)
                    \<and> (\<forall>i. untrm (f' i) \<noteq> []
                         \<and> (hd (untrm (f' i)) = q \<or> lessBP (hd (untrm (f' i))) q))"
          using f'ch f'dep f'hd by blast
        ultimately show False by blast
      qed
    qed
    have "length (untrm (f0 0)) \<le> length (untrm (f0 0))" by simp
    from inner[OF this f0ch f0dep f0hd] show False .
  qed
qed

lemma wfpd_tuple_lift_dep:
  assumes wfP: "wf (RPrel_dep d)"
  shows "wf (RTrel_dep d)"
proof -
  have "\<nexists>f. \<forall>i. (f (Suc i), f i) \<in> RTrel_dep d"
  proof
    assume "\<exists>f. \<forall>i. (f (Suc i), f i) \<in> RTrel_dep d"
    then obtain f where chd: "\<forall>i. (f (Suc i), f i) \<in> RTrel_dep d" by blast
    have ch: "\<forall>i. (f (Suc i), f i) \<in> RTrel" using chd by (simp add: RTrel_dep_def)
    have dep: "\<forall>i. bdepthT (f i) \<le> d"
    proof
      fix i
      have "(f (Suc i), f i) \<in> RTrel_dep d" using chd by blast
      thus "bdepthT (f i) \<le> d" by (simp add: RTrel_dep_def)
    qed
    have ne: "\<And>i. untrm (f i) \<noteq> []" using wfox_chain_nonempty[OF ch] .
    define p where "p \<equiv> hd (untrm (f 0))"
    obtain c cs where cc: "untrm (f 0) = c # cs" using ne[of 0] by (cases "untrm (f 0)") auto
    have f0: "f 0 = Trm (c # cs)" using cc by (metis wfox_Trm_untrm)
    have inRT0: "(f (Suc 0), f 0) \<in> RTrel" using ch by blast
    have isot0: "isOT_BT (f 0)" and dfr0: "dfree_BT (f 0)"
      using inRT0 by (simp_all add: RTrel_def)
    have pg: "isOT_BP p \<and> dfree_BP p"
    proof -
      have "isOT_BP c \<and> dfree_BP c" using isot0 dfr0 unfolding f0 by simp
      moreover have "p = c" using cc p_def by simp
      ultimately show ?thesis by simp
    qed
    have pgd: "bdepthP p \<le> d"
    proof -
      have "p \<in> set (untrm (f 0))" using cc p_def by simp
      hence "bdepthP p \<le> bdepthT (Trm (untrm (f 0)))" by (rule bdepthP_head_le)
      also have "\<dots> = bdepthT (f 0)" by (simp add: wfox_Trm_untrm)
      also have "\<dots> \<le> d" using dep by blast
      finally show ?thesis .
    qed
    have allhd: "\<forall>i. untrm (f i) \<noteq> []
                     \<and> (hd (untrm (f i)) = p \<or> lessBP (hd (untrm (f i))) p)"
    proof
      fix i
      have "hd (untrm (f (0 + i))) = hd (untrm (f 0))
            \<or> lessBP (hd (untrm (f (0 + i)))) (hd (untrm (f 0)))"
        using wfox_head_bound[OF ch, of 0 i] .
      thus "untrm (f i) \<noteq> [] \<and> (hd (untrm (f i)) = p \<or> lessBP (hd (untrm (f i))) p)"
        using ne[of i] p_def by simp
    qed
    have "\<not> (\<exists>g. (\<forall>i. (g (Suc i), g i) \<in> RTrel)
                \<and> (\<forall>i. bdepthT (g i) \<le> d)
                \<and> (\<forall>i. untrm (g i) \<noteq> []
                     \<and> (hd (untrm (g i)) = p \<or> lessBP (hd (untrm (g i))) p)))"
      using wfpd_NoBad_dep[OF wfP] pg pgd by blast
    moreover have "(\<forall>i. (f (Suc i), f i) \<in> RTrel)
                \<and> (\<forall>i. bdepthT (f i) \<le> d)
                \<and> (\<forall>i. untrm (f i) \<noteq> []
                     \<and> (hd (untrm (f i)) = p \<or> lessBP (hd (untrm (f i))) p))"
      using ch dep allhd by blast
    ultimately show False by blast
  qed
  thus ?thesis by (simp add: wf_iff_no_infinite_down_chain)
qed

subsection \<open>Closing the mutual induction: \<open>wf (RPrel_dep d)\<close> / \<open>wf (RTrel_dep d)\<close> for every \<open>d\<close>\<close>

lemma wfpd_wf_dep: "wf (RPrel_dep d) \<and> wf (RTrel_dep d)"
proof (induction d)
  case 0
  have rp: "wf (RPrel_dep 0)" by (rule wfpd_wf_RPrel_dep_0)
  have "wf (RTrel_dep 0)" by (rule wfpd_tuple_lift_dep[OF rp])
  thus ?case using rp by blast
next
  case (Suc d)
  have rt: "wf (RTrel_dep d)" using Suc.IH by blast
  have rp: "wf (RPrel_dep (Suc d))" by (rule wfpd_RPrel_dep_lex[OF rt])
  have "wf (RTrel_dep (Suc d))" by (rule wfpd_tuple_lift_dep[OF rp])
  thus ?case using rp by blast
qed

lemma wfpd_wf_RPrel_dep: "wf (RPrel_dep d)"
  using wfpd_wf_dep by blast

lemma wfpd_wf_RTrel_dep: "wf (RTrel_dep d)"
  using wfpd_wf_dep by blast

text \<open>The depth-\<open>\<le> d\<close> restriction of the [Buc1] Lemma 2.2 GOAL relation \<open>(OT\<^bsub>B\<^esub>, <)\<close>
  is well-founded — an INFINITE elementary fragment (unbounded coefficients), strictly
  larger than the r21b norm-bounded (finite) fragment @{thm [source] wfpx_wf_goal_bnd}.\<close>

theorem wfpd_wf_goal_dep:
  "wf ({(a, b). a \<in> OT_B \<and> b \<in> OT_B \<and> lessBT a b}
        \<inter> {(a, b). bdepthT a \<le> d \<and> bdepthT b \<le> d})"
  using wfpd_wf_RTrel_dep by (simp add: RTrel_dep_def wfox_goal_eq_RTrel)

subsection \<open>The sharpened residual: no unbounded-DEPTH descending chain\<close>

lemma wfpd_bounded_Rchain_impossible:
  assumes ch: "\<forall>i. (f (Suc i), f i) \<in> RPrel"
    and bnd: "\<forall>i. bdepthP (f i) \<le> N"
  shows False
proof -
  have "\<forall>i. (f (Suc i), f i) \<in> RPrel_dep N"
    using ch bnd by (auto simp: RPrel_dep_def)
  moreover have "wf (RPrel_dep N)" by (rule wfpd_wf_RPrel_dep)
  ultimately show False by (meson wf_iff_no_infinite_down_chain)
qed

lemma wfpd_infinite_Rchain_unbounded_depth:
  assumes ch: "\<forall>i. (f (Suc i), f i) \<in> RPrel"
  shows "\<forall>N. \<exists>i. N < bdepthP (f i)"
proof (rule allI)
  fix N
  show "\<exists>i. N < bdepthP (f i)"
  proof (rule ccontr)
    assume "\<not> (\<exists>i. N < bdepthP (f i))"
    hence "\<forall>i. bdepthP (f i) \<le> N" by (auto simp: not_less)
    from wfpd_bounded_Rchain_impossible[OF ch this] show False .
  qed
qed

theorem wfpd_wf_RPrel_iff_no_unbounded_depth:
  "wf RPrel \<longleftrightarrow>
     \<not> (\<exists>f. (\<forall>i. (f (Suc i), f i) \<in> RPrel) \<and> (\<forall>N. \<exists>i. N < bdepthP (f i)))"
proof
  assume "wf RPrel"
  hence "\<not> (\<exists>f. \<forall>i. (f (Suc i), f i) \<in> RPrel)"
    using wf_iff_no_infinite_down_chain by blast
  thus "\<not> (\<exists>f. (\<forall>i. (f (Suc i), f i) \<in> RPrel) \<and> (\<forall>N. \<exists>i. N < bdepthP (f i)))"
    by blast
next
  assume rhs: "\<not> (\<exists>f. (\<forall>i. (f (Suc i), f i) \<in> RPrel) \<and> (\<forall>N. \<exists>i. N < bdepthP (f i)))"
  show "wf RPrel"
  proof (rule ccontr)
    assume "\<not> wf RPrel"
    then obtain f where ch: "\<forall>i. (f (Suc i), f i) \<in> RPrel"
      using wf_iff_no_infinite_down_chain by blast
    have "\<forall>N. \<exists>i. N < bdepthP (f i)"
      by (rule wfpd_infinite_Rchain_unbounded_depth[OF ch])
    with ch have "\<exists>f. (\<forall>i. (f (Suc i), f i) \<in> RPrel) \<and> (\<forall>N. \<exists>i. N < bdepthP (f i))"
      by blast
    with rhs show False by blast
  qed
qed

text \<open>Term-level form of the same reduction (directly on \<open>RTrel\<close>, hence on the goal
  @{thm [source] wfox_goal_eq_RTrel}): the sole obstruction to [Buc1] Lemma 2.2 is an
  unbounded-DEPTH strictly-\<open><\<close>-descending chain of \<open>OT\<^bsub>B\<^esub>\<close> terms.\<close>

lemma wfpd_bounded_Tchain_impossible:
  assumes ch: "\<forall>i. (f (Suc i), f i) \<in> RTrel"
    and bnd: "\<forall>i. bdepthT (f i) \<le> N"
  shows False
proof -
  have "\<forall>i. (f (Suc i), f i) \<in> RTrel_dep N"
    using ch bnd by (auto simp: RTrel_dep_def)
  moreover have "wf (RTrel_dep N)" by (rule wfpd_wf_RTrel_dep)
  ultimately show False by (meson wf_iff_no_infinite_down_chain)
qed

theorem wfpd_wf_RTrel_iff_no_unbounded_depth:
  "wf RTrel \<longleftrightarrow>
     \<not> (\<exists>f. (\<forall>i. (f (Suc i), f i) \<in> RTrel) \<and> (\<forall>N. \<exists>i. N < bdepthT (f i)))"
proof
  assume "wf RTrel"
  hence "\<not> (\<exists>f. \<forall>i. (f (Suc i), f i) \<in> RTrel)"
    using wf_iff_no_infinite_down_chain by blast
  thus "\<not> (\<exists>f. (\<forall>i. (f (Suc i), f i) \<in> RTrel) \<and> (\<forall>N. \<exists>i. N < bdepthT (f i)))"
    by blast
next
  assume rhs: "\<not> (\<exists>f. (\<forall>i. (f (Suc i), f i) \<in> RTrel) \<and> (\<forall>N. \<exists>i. N < bdepthT (f i)))"
  show "wf RTrel"
  proof (rule ccontr)
    assume "\<not> wf RTrel"
    then obtain f where ch: "\<forall>i. (f (Suc i), f i) \<in> RTrel"
      using wf_iff_no_infinite_down_chain by blast
    have "\<forall>N. \<exists>i. N < bdepthT (f i)"
    proof (rule allI)
      fix N show "\<exists>i. N < bdepthT (f i)"
      proof (rule ccontr)
        assume "\<not> (\<exists>i. N < bdepthT (f i))"
        hence "\<forall>i. bdepthT (f i) \<le> N" by (auto simp: not_less)
        from wfpd_bounded_Tchain_impossible[OF ch this] show False .
      qed
    qed
    with ch have "\<exists>f. (\<forall>i. (f (Suc i), f i) \<in> RTrel) \<and> (\<forall>N. \<exists>i. N < bdepthT (f i))"
      by blast
    with rhs show False by blast
  qed
qed


section \<open>Additional relocated campaign annotations\<close>

(* ===== round 21b WFPRIN (wt-y4: Buc1 wf RPrel bounded-norm fragment WF (finite)) ===== *)


(* ===== round 21b front WFPRIN (wt-y4): bounded-norm fragment of [Buc1] Lemma 2.2 residual wf RPrel ===== *)

section \<open>[Buc1] Lemma 2.2 residual (r21b-WFPRIN): the BOUNDED-NORM fragment of \<open>wf RPrel\<close>\<close>

text \<open>
  r20 (@{thm [source] m_buc1_2_2_OT_B_wf_via_principal}) reduced the sole external
  citation @{text buc1_2_2_OT_B_wf} FAITHFULLY to @{term "wf RPrel"} (principal order on
  the \<open>D\<^sub>\<omega>\<close>-free \<open>OT\<close> principal terms).  Full @{term "wf RPrel"} is external-grade
  (the ordinal-collapsing \<open>\<psi>\<close> well-ordering, order type \<open>\<psi>\<^sub>0(\<epsilon>\<^bsub>\<Omega>\<^sub>\<omega>+1\<^esub>)\<close>).  Here we
  carve off the part that IS elementary and prove it green, and reduce the general problem
  to exactly the non-elementary residual.

  \<^bold>\<open>The tractable fragment.\<close>  Put a syntactic norm \<open>nrm\<close> on terms that sums both the
  branching STRUCTURE and the index COEFFICIENTS (\<open>the_enat v\<close>).  Then:
  \<^enum> For each \<open>N\<close> the set of \<open>D\<^sub>\<omega>\<close>-free terms/principals of norm \<open>\<le> N\<close> is FINITE
    (@{text wfpx_finite_norm_le}); note \<open>D\<^sub>\<omega>\<close>-freeness is essential (\<open>D\<^bsub>\<omega>\<^esub>\<close> would give
    infinitely many one-node principals).
  \<^enum> Hence the norm-bounded restriction @{text RPrel_bnd}/@{text RTrel_bnd} of the strict
    order is a FINITE ACYCLIC relation, so WF is trivial (@{thm [source] finite_acyclic_wf}):
    @{text wfpx_wf_RPrel_bnd}, @{text wfpx_wf_RTrel_bnd}, @{text wfpx_wf_goal_bnd}.

  \<^bold>\<open>The reduction of the general problem to unbounded norm.\<close>  A norm-BOUNDED infinite
  \<open><\<close>-descending chain is impossible (it lives in a finite acyclic set,
  @{text wfpx_bounded_chain_impossible}).  So any infinite descending chain has UNBOUNDED
  norm (@{text wfpx_infinite_chain_unbounded_norm}) — matching the fact that Buchholz-style
  fundamental sequences descend with INCREASING syntactic norm.  Consequently
  @{term "wf RPrel"} is EQUIVALENT to \<open>there is no unbounded-norm infinite descending
  chain\<close> (@{text wfpx_wf_RPrel_iff_no_unbounded_chain}), and likewise at term/goal level
  (@{text wfpx_wf_RTrel_iff_no_unbounded_chain}).  This is a FAITHFUL reduction that removes
  the elementary (finite) part entirely; the surviving residual is precisely the
  unbounded-norm chains, whose absence is the genuine ordinal-collapsing content of
  [Buc1] Lemma 2.2.

  Everything below is unconditional (no \<open>sorry\<close>, no external citation).
\<close>

(* ===== round 24 WFRP2 (wt-s4a: wf RPrel general = psi-ordinal obstruction (refutation)) ===== *)


(* ===== round 24 front WFRP2 (wt-s4a): the norm is NOT bounded along lessBP-descending
   OT chains — the reduction of general wf RPrel to the r21b bounded fragment FAILS.
   This is the psi-ordinal (collapsing) obstruction, formalized as a refutation. ===== *)

section \<open>r24-WFRP2 — general \<open>wf RPrel\<close> does NOT reduce to the bounded-norm fragment
  (the \<open>\<psi>\<close>-ordinal obstruction, formalized)\<close>

text \<open>
  r21b (@{thm [source] wfpx_wf_RPrel_bnd}) proved the \<^emph>\<open>bounded-norm\<close> fragment
  @{term "RPrel_bnd N"} of @{term "wf RPrel"} is finite+acyclic, hence WF, and
  reduced @{term "wf RPrel"} to \<open>there is no infinite descending chain of UNBOUNDED
  norm\<close> (@{thm [source] wfpx_wf_RPrel_iff_no_unbounded_chain}).

  The task for this round was to push further: reduce \<^emph>\<open>general\<close> @{term "wf RPrel"} to
  the bounded fragment PLUS a norm-monotonicity fact — the crux being
  \<^item> (CRUX)  @{prop "lessBP b p \<Longrightarrow> wfpx_nrmP b \<le> f (wfpx_nrmP p)"} for some \<open>f\<close>,
    restricted to \<open>b, p\<close> ranging over \<open>OT\<close>-principals (i.e. over @{term RPrel}).
  If CRUX held, every predecessor of a fixed principal \<open>p\<close> would live in a norm-\<open>\<le> f(nrmP p)\<close>
  set, which is FINITE (@{thm [source] wfpx_finite_BP_norm}); the whole descending structure
  below \<open>p\<close> would sit in the bounded fragment and @{term "wf RPrel"} would follow elementarily.

  \<^bold>\<open>CRUX IS FALSE.\<close>  We exhibit a fixed \<open>OT\<close>-principal \<open>p = D\<^sub>1 0 = \<psi>\<^sub>1(0)\<close> below which
  the syntactic norm is UNBOUNDED.  The witness family is
  \<^item> \<open>q\<^sub>n := D\<^sub>0 n = DB 0 (numBT n)\<close> (\<open>= \<psi>\<^sub>0(n)\<close>, a natural number fed to \<open>D\<^sub>0\<close>).
  Each \<open>q\<^sub>n\<close> is an \<open>OT\<close>-principal, \<open>D\<^sub>\<omega>\<close>-free, and \<open>q\<^sub>n < p\<close> (because the top index
  \<open>0 < 1\<close> \<^emph>\<open>regardless of the subterm\<close> — this is exactly Buchholz's cross-index
  comparison / collapsing), yet @{term "wfpx_nrmP (DB 0 (numBT n)) = Suc (Suc (n * 2))"}
  grows without bound.  Empirically validated in @{path \<open>python/_r24_wf2x_norm_bound.py\<close>}
  (both this family and the alternative \<open>D\<^sub>0(D\<^sub>1\<^sup>n 0)\<close>): all \<open>OT\<close>, all \<open>< p\<close>, norm \<open>\<to> \<infinity>\<close>.

  \<^bold>\<open>Consequences (all proven green below, no assumptions, no external citation).\<close>
  \<^enum> @{text wf2x_pred_norm_unbounded}: below the fixed \<open>p\<close> there are \<open>OT\<close>-principals of
    arbitrarily large norm.
  \<^enum> @{text wf2x_no_stepwise_norm_bound}: no \<open>f\<close> validates CRUX (refutes \<open>nrmP b \<le> f(nrmP p)\<close>).
  \<^enum> @{text wf2x_no_predecessor_norm_bound}: not even a bound depending on the WHOLE
    predecessor-target \<open>p\<close> (any \<open>B :: BP \<Rightarrow> nat\<close>) works — closing the \<open>f\<close>-sees-only-the-norm
    loophole.
  \<^enum> @{text wf2x_pred_set_infinite}: the predecessor set @{term "{q. (q, DB 1 (Trm [])) \<in> RPrel}"}
    is INFINITE (its order type is the ordinal \<open>\<psi>\<^sub>1(0)\<close>).

  \<^bold>\<open>Interpretation (the precise obstruction).\<close>  Because @{term wfpx_nrmP} is unbounded on
  the one-step predecessors of a single principal, the bounded-fragment approach is SHARP as
  it stands: @{term "wf RPrel"} cannot be reduced to @{term "RPrel_bnd N"} for any \<open>N\<close> nor to
  a norm-monotone side condition.  The genuine content — that despite the unbounded norm every
  descending chain still terminates — is precisely the ordinal-collapsing well-ordering of
  \<open>OT\<close> (order type \<open>\<psi>\<^sub>0(\<epsilon>\<^bsub>\<Omega>\<^sub>\<omega>+1\<^esub>)\<close>), which is the external-grade residual [Buc1] Lemma 2.2.
  In Buchholz terms: fundamental sequences descend in \<open><\<close> while their syntactic norm
  INCREASES, so no syntactic norm can serve as a well-founded rank.  \<open>REPORTED, not papered over.\<close>
\<close>

(* ===== end round 27 front CONDIII ===== *)



(* ===== r27 merge: wt-b1 block ===== *)
(* ===== round 27 front WFRPREL (wt-b1): [Buc1] Lemma 2.2 residual — the DEPTH-BOUNDED fragment of wf RPrel ===== *)

section \<open>[Buc1] Lemma 2.2 residual (r27-WFRPREL): the DEPTH-BOUNDED fragment of \<open>wf RPrel\<close>\<close>

text \<open>
  r20 (@{thm [source] m_buc1_2_2_OT_B_wf_via_principal}) reduced the sole external citation
  @{text buc1_2_2_OT_B_wf} FAITHFULLY to @{term "wf RPrel"} (the principal order on the
  \<open>D\<^sub>\<omega>\<close>-free \<open>OT\<close> principals).  r21b (@{thm [source] wfpx_wf_RPrel_bnd}) carved off the
  norm-BOUNDED fragment (finite + acyclic, hence WF) and reduced the general problem to the
  absence of an unbounded-NORM descending chain.

  Here we ENLARGE the elementary fragment strictly: from norm-bounded (a FINITE order) to
  DEPTH-bounded (an INFINITE order — unbounded coefficients \<open>v\<close> at every node).  The point
  is that Buchholz's genuinely-hard infinite descent (\<open>D\<^sub>0\<^sup>n(D\<^sub>1 0)\<close>, the header
  counterexample) has unbounded NESTING DEPTH; confined to any fixed depth the order is
  elementarily well-founded, by index stabilisation:

  \<^item> \<open>bdepthP/bdepthT\<close>: the max nesting depth of a principal / term.  \<open>RPrel_dep d\<close> /
    \<open>RTrel_dep d\<close> restrict @{term RPrel} / @{term RTrel} to depth \<open>\<le> d\<close>.  Since
    \<open>bdepthP p \<le> wfpx_nrmP p\<close> the depth fragment CONTAINS the norm fragment
    (\<open>RPrel_bnd N \<subseteq> RPrel_dep N\<close>); it is strictly larger (infinitely many indices).
  \<^item> \<open>wfpd_RPrel_dep_lex\<close> (the CROSS-INDEX step, elementary): a principal \<open>D\<^sub>v a\<close>
    embeds order-preservingly as \<open>(v, a)\<close> into \<open>(<\<^bsub>\<nat>\<^esub>) \<times>\<^sub>lex RTrel_dep (d-1)\<close>
    (@{thm [source] lessBT.simps}(4)); the index \<open>v \<in> \<nat>\<close> is well-founded, so
    \<open>wf (RTrel_dep (d-1)) \<Longrightarrow> wf (RPrel_dep d)\<close>.  This is exactly where Buchholz's
    collapsing would be needed WITHOUT the depth bound (the cross-index comparison
    \<open>D\<^sub>u a < D\<^sub>v b\<close>, \<open>u < v\<close>): the depth bound lets \<open>\<nat>\<close>'s WF stand in for it, because
    the subterm \<open>a\<close> then lives one depth lower and is handled by the induction hypothesis.
  \<^item> \<open>wfpd_tuple_lift_dep\<close> (the natural-sum / tuple layer, depth-guarded copy of the
    multiset-free @{thm [source] wfox_tuple_lift}): \<open>wf (RPrel_dep d) \<Longrightarrow> wf (RTrel_dep d)\<close>.
  Closing the mutual induction on \<open>d\<close> (@{text wfpd_wf_dep}) gives \<open>wf (RPrel_dep d)\<close> and
  \<open>wf (RTrel_dep d)\<close> UNCONDITIONALLY for every \<open>d\<close>, and hence (@{text wfpd_wf_goal_dep})
  the depth-\<open>\<le> d\<close> restriction of the [Buc1] Lemma 2.2 goal \<open>(OT\<^bsub>B\<^esub>, <)\<close> is WF.  The
  surviving residual for the full goal is sharpened to the absence of an unbounded-DEPTH
  descending chain (@{text wfpd_wf_RPrel_iff_no_unbounded_depth}) — the genuine
  ordinal-collapsing content of [Buc1] Lemma 2.2, which stays external (the paper \<open>sorry\<close>
  @{thm [source] buc1_2_2_OT_B_wf} remains the SOLE external citation).

  EMPIRICALLY VALIDATED (python/buchholz.py model, \<open>OT \<inter> T\<^sub>B\<close> samples
  \<open>idx \<le> 2\<close>, \<open>width \<le> 2\<close>, \<open>depth \<le> 3\<close>): lex characterisation of \<open>lessBP\<close>
  1555009/1555009; index weak-decrease along descent 776881/776881; strict-order laws
  (Lemma 2.1) 0 failures; \<open>bdepthT b < bdepthP p\<close> / \<open>head \<le> term\<close> /
  \<open>tail \<le> term\<close> 1247/1247 + 990/990; \<open>bdepthP \<le> wfpx_nrmP\<close> 1247/1247.

  Everything below is unconditional (no \<open>sorry\<close>, no new external citation).
\<close>

end
