theory M_8_7_Wfc_Component_Jumps
  imports M_8_7_Wfj_Level_Jump
begin

text \<open>Relocated proof material.  The declarations retain their original source order,
  and every relocated annotation is preserved below.  This theory is machine-checked
  outside the termination build tree.\<close>

(* ===== end r53-otx3 block ===== *)

(* ===== r53 merge: wt-y3 — collapse core: impredicativity established; residual = pbody-acc / staged jump ladder (wfc_) ===== *)

(* ===== r53: wt-y3 — buc1 collapse-core round (wfc_): G-antitonicity, secured
        propagation, same-head acc lift, head-recursion discharge; residual
        re-sharpened to principal-body RTrel-accessibility ===== *)

section \<open>r53 wfc — the collapse core: the head recursion is discharged\<close>

text \<open>Target: \<open>wfj_collapse_core\<close> (r52).  This round separates the two branches of
  the \<open>accI\<close> step for a principal \<open>D\<^sub>v b\<close> and discharges everything EXCEPT the
  genuine \<open>\<psi>\<close>-collapse content:

  \<^enum> SAME-HEAD branch (\<open>D\<^sub>v w < D\<^sub>v b\<close> via \<open>w < b\<close>): fully reduced to
    \<open>RTrel\<close>-accessibility of the body (\<open>wfc_principal_acc_of_body\<close>, an
    \<open>acc\<close>-induction along \<open>RTrel\<close>).
  \<^enum> STRICT-HEAD branch (\<open>D\<^sub>u w < D\<^sub>v b\<close> via \<open>u < v\<close>): the body \<open>w\<close> is completely
    unconstrained by the comparison, so this branch needs accessibility of ALL
    \<open>OT\<close>+\<open>dfree\<close> principals of head \<open>< v\<close> — but that hypothesis is FREE across
    the head index by strong induction on the (finite, \<open>dfree\<close>) head
    (\<open>wfc_wf_of_pbody_hyp\<close>), because \<open>wfj_hd\<close> is the true stratification
    (\<open>wfj_strat_hd\<close>, r52).

  Net effect: \<^bold>\<open>the head bookkeeping adds nothing\<close> — \<open>wf RPrel\<close> (hence the
  collapse core, hence [Buc1] 2.2) is EQUIVALENT to \<open>RTrel\<close>-accessibility of the
  bodies of \<open>OT\<close>+\<open>dfree\<close> principals (\<open>wfc_pbody_acc\<close>).  Together with the r52
  tuple layer (\<open>wfj_tuple_acc\<close> and its converse \<open>wfc_acc_component\<close> below), the
  two-sorted principal/tuple structure collapses to ONE question about bodies.\<close>

subsection \<open>(1) \<open>G\<close>-set antitonicity and secured-content propagation\<close>

lemma wfc_GBT_antitone: "\<forall>u u'. u \<le> u' \<longrightarrow> GBT u' t \<subseteq> GBT u t"
  and wfc_GBP_antitone: "\<forall>u u'. u \<le> u' \<longrightarrow> GBP u' q \<subseteq> GBP u q"
proof (induction t and q rule: wfs_lvT_wfs_lvP.induct)
  case (1 ps)
  show ?case
  proof (intro allI impI subsetI)
    fix u u' :: enat and x
    assume le: "u \<le> u'" and xin: "x \<in> GBT u' (Trm ps)"
    obtain r where rin: "r \<in> set ps" and xr: "x \<in> GBP u' r" using xin by auto
    have "x \<in> GBP u r" using "1.IH"[OF rin] le xr by blast
    then show "x \<in> GBT u (Trm ps)" using rin by auto
  qed
next
  case (2 v b)
  show ?case
  proof (intro allI impI subsetI)
    fix u u' :: enat and x
    assume le: "u \<le> u'" and xin: "x \<in> GBP u' (DB v b)"
    have u'v: "u' \<le> v" using xin by (auto split: if_splits)
    have uv: "u \<le> v" using le u'v by (rule order_trans)
    have xc: "x = b \<or> x \<in> GBT u' b" using xin u'v by (auto split: if_splits)
    have "x = b \<or> x \<in> GBT u b" using xc "2.IH" le by blast
    then show "x \<in> GBP u (DB v b)" using uv by auto
  qed
qed

text \<open>The collapse-core premise (secured \<open>G\<^sub>v\<close>-coefficients) propagates to every
  UNSHIELDED component of the body: if \<open>D\<^sub>w c\<close> is a top-level component of \<open>b\<close>
  with \<open>w \<ge> v\<close>, then \<open>c\<close> is itself secured and its own \<open>G\<^sub>w\<close>-content is secured
  — the recursion step of any future engine.  (Shielded components, \<open>w < v\<close>,
  are NOT covered: they are the genuine \<open>\<psi>\<close>-collapse content.)\<close>

lemma wfc_sec_component:
  assumes sec: "\<forall>x \<in> GBT v b. wfj_secT x"
    and comp: "DB w c \<in> set (untrm b)"
    and vw: "v \<le> w"
  shows "wfj_secT c" and "\<forall>x \<in> GBT w c. wfj_secT x"
proof -
  obtain ps where beq: "b = Trm ps" by (cases b) auto
  have cin: "DB w c \<in> set ps" using comp beq by simp
  have cG: "c \<in> GBT v b"
  proof -
    have m: "c \<in> GBP v (DB w c)" using vw by simp
    have "c \<in> (\<Union>p \<in> set ps. GBP v p)" using cin m by (rule UN_I)
    then show ?thesis using beq by simp
  qed
  show "wfj_secT c" using sec cG by blast
  have sub: "GBT w c \<subseteq> GBT v b"
  proof -
    have s1: "GBT w c \<subseteq> GBT v c" using wfc_GBT_antitone vw by blast
    have s2: "GBT v c \<subseteq> GBP v (DB w c)" using vw by auto
    have s3: "GBP v (DB w c) \<subseteq> GBT v b"
    proof
      fix y assume yin: "y \<in> GBP v (DB w c)"
      have "y \<in> (\<Union>p \<in> set ps. GBP v p)" using cin yin by (rule UN_I)
      then show "y \<in> GBT v b" using beq by simp
    qed
    show ?thesis using s1 s2 s3 by blast
  qed
  show "\<forall>x \<in> GBT w c. wfj_secT x" using sec sub by blast
qed

theorem wfc_wf_of_pbody:
  assumes "wfc_pbody_acc" shows "wf RPrel"
proof (rule wfc_wf_of_pbody_hyp)
  fix v c assume "isOT_BP (DB v c)" "dfree_BP (DB v c)"
  then show "c \<in> Wellfounded.acc RTrel"
    using assms[unfolded wfc_pbody_acc_def] by blast
qed

theorem wfc_pbody_of_wf:
  assumes "wf RPrel" shows "wfc_pbody_acc"
proof -
  have "wf RTrel" using wfox_tuple_lift[OF assms] .
  then have "\<forall>t. t \<in> Wellfounded.acc RTrel" by (rule wf_iff_acc[THEN iffD1])
  then show ?thesis unfolding wfc_pbody_acc_def by blast
qed

theorem wfc_pbody_iff_wf: "wfc_pbody_acc \<longleftrightarrow> wf RPrel"
  using wfc_wf_of_pbody wfc_pbody_of_wf by blast

theorem wfc_pbody_iff_collapse_core: "wfc_pbody_acc \<longleftrightarrow> wfj_collapse_core"
  using wfc_pbody_iff_wf wfj_collapse_core_iff_wf by blast

theorem wfc_pbody_iff_level_jump: "wfc_pbody_acc \<longleftrightarrow> wfs_level_jump"
  using wfc_pbody_iff_wf wfj_level_jump_of_wf wfs_wf_RPrel_of_level_jump by blast

subsection \<open>(4) Reflection: tuple accessibility gives component accessibility
  (the converse of \<open>wfj_tuple_acc\<close>)\<close>

lemma wfc_acc_singleton:
  assumes "Trm [p] \<in> Wellfounded.acc RTrel"
  shows "p \<in> Wellfounded.acc RPrel"
proof -
  have gen: "\<forall>p. t = Trm [p] \<longrightarrow> p \<in> Wellfounded.acc RPrel"
    if "t \<in> Wellfounded.acc RTrel" for t
    using that
  proof (induction rule: acc.induct)
    case (accI t)
    show ?case
    proof (intro allI impI)
      fix p assume te: "t = Trm [p]"
      show "p \<in> Wellfounded.acc RPrel"
      proof (rule acc.intros)
        fix q assume qp: "(q, p) \<in> RPrel"
        have "(Trm [q], Trm [p]) \<in> RTrel" using wfox_RPrel_into_RTrel[OF qp] .
        then have "(Trm [q], t) \<in> RTrel" using te by simp
        then show "q \<in> Wellfounded.acc RPrel" using accI.IH by blast
      qed
    qed
  qed
  show ?thesis using gen[OF assms] by blast
qed

lemma wfc_tail_lessBT: "descP (p # ps) \<Longrightarrow> lessBT (Trm ps) (Trm (p # ps))"
proof (induction ps arbitrary: p)
  case Nil
  show ?case by simp
next
  case (Cons q ps')
  have dq: "descP (q # ps')" using Cons.prems by simp
  have lq: "leBT (Trm [q]) (Trm [p])" using Cons.prems by simp
  have IH: "lessBT (Trm ps') (Trm (q # ps'))" using Cons.IH[OF dq] .
  show ?case
  proof (cases "q = p")
    case True
    then show ?thesis using IH by simp
  next
    case False
    have "lessBT (Trm [q]) (Trm [p])" using lq False by auto
    then have "lessBP q p" using b1x_lessBP_single by blast
    then show ?thesis by simp
  qed
qed

lemma wfc_member_leBT:
  "descP ps \<Longrightarrow> r \<in> set ps \<Longrightarrow> leBT (Trm [r]) (Trm ps)"
proof (induction ps)
  case Nil
  show ?case using Nil.prems(2) by simp
next
  case (Cons p ps')
  have dtail: "descP ps'" using Cons.prems(1) by (cases ps') simp_all
  show ?case
  proof (cases "ps' = []")
    case True
    then have "r = p" using Cons.prems(2) by simp
    then show ?thesis using True by simp
  next
    case False
    note psne = False
    have tl: "lessBT (Trm ps') (Trm (p # ps'))" using wfc_tail_lessBT[OF Cons.prems(1)] .
    show ?thesis
    proof (cases "r = p")
      case True
      have "lessBT (Trm []) (Trm ps')" using psne by simp
      then have "lessBT (Trm [r]) (Trm (p # ps'))" using True by simp
      then show ?thesis by blast
    next
      case False
      then have rin: "r \<in> set ps'" using Cons.prems(2) by simp
      have IH: "leBT (Trm [r]) (Trm ps')" using Cons.IH[OF dtail rin] .
      show ?thesis
      proof (cases "Trm [r] = Trm ps'")
        case True
        then show ?thesis using tl by simp
      next
        case False
        then have "lessBT (Trm [r]) (Trm ps')" using IH by blast
        then have "lessBT (Trm [r]) (Trm (p # ps'))" using tl by (rule lessBT_trans)
        then show ?thesis by blast
      qed
    qed
  qed
qed

lemma wfc_acc_component:
  assumes tacc: "t \<in> Wellfounded.acc RTrel"
    and tot: "isOT_BT t" and tdf: "dfree_BT t"
    and rin: "r \<in> set (untrm t)"
  shows "r \<in> Wellfounded.acc RPrel"
proof -
  obtain ps where te: "t = Trm ps" by (cases t) auto
  have rin': "r \<in> set ps" using rin te by simp
  have rot: "isOT_BP r" using tot te rin' by simp
  have rdf: "dfree_BP r" using tdf te rin' by simp
  have sot: "isOT_BT (Trm [r])" using rot by simp
  have sdf: "dfree_BT (Trm [r])" using rdf by simp
  have dps: "descP ps" using tot te by simp
  have le: "leBT (Trm [r]) (Trm ps)" using wfc_member_leBT[OF dps rin'] .
  have "Trm [r] \<in> Wellfounded.acc RTrel"
  proof (cases "Trm [r] = Trm ps")
    case True
    then show ?thesis using tacc te by simp
  next
    case False
    then have "lessBT (Trm [r]) (Trm ps)" using le by blast
    then have rrel: "(Trm [r], t) \<in> RTrel"
      using sot sdf tot tdf te by (simp add: RTrel_def)
    show ?thesis by (rule acc_downward[OF tacc rrel])
  qed
  then show ?thesis by (rule wfc_acc_singleton)
qed

theorem wfc_tuple_acc_iff:
  assumes "isOT_BT t" and "dfree_BT t"
  shows "t \<in> Wellfounded.acc RTrel \<longleftrightarrow> (\<forall>r \<in> set (untrm t). r \<in> Wellfounded.acc RPrel)"
proof
  assume "t \<in> Wellfounded.acc RTrel"
  then show "\<forall>r \<in> set (untrm t). r \<in> Wellfounded.acc RPrel"
    using wfc_acc_component assms by blast
next
  assume "\<forall>r \<in> set (untrm t). r \<in> Wellfounded.acc RPrel"
  then show "t \<in> Wellfounded.acc RTrel" using wfj_tuple_acc assms by blast
qed

(* ===== end r53 wfc block 1 (head-recursion discharge + tuple reflection) ===== *)

subsection \<open>(5) The \<open>lvP\<close>-staged bootstrap: a HEAD-bounded collapse core reaches a
  whole \<open>lvP\<close>-LEVEL, and the residual factors into per-level jump steps\<close>

text \<open>\<open>wfj_acc_of_collapse_core\<close> (r52) consumes the core at ALL heads.  Refinement:
  the core restricted to heads \<open>\<le> n\<close> (\<open>wfc_core_upto n\<close>) already yields
  accessibility of every principal of HEREDITARY level \<open>wfs_lvP \<le> n\<close>
  (\<open>wfc_acc_of_core_upto\<close>) — because \<open>G\<close>-elements do not raise the level
  (\<open>wfc_G_lvT\<close>).  Hence the whole goal factors into the classical-shape
  per-level steps \<open>wfc_jump_step n\<close>: FROM the wellfounded (hence, by
  \<open>wfs_accord\<close>/\<open>wfs_rk\<close>, well-ordered and ranked) accessible level-\<open>n\<close> part TO
  the core for heads \<open>\<le> n+1\<close> — exactly the transfinite-recursion step of
  [Buc1]'s own proof of Lemma 2.2.  This is the sharpest STAGED form of the
  residual: \<open>(\<forall>n. wfc_jump_step n) \<Longrightarrow> wf RPrel\<close> (\<open>wfc_wf_of_jump_steps\<close>).\<close>

lemma wfc_maxe_mem: "x \<in> set xs \<Longrightarrow> x \<le> wfs_maxe xs"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  show ?case
  proof (cases "x = y")
    case True
    then show ?thesis by (simp add: max.cobounded1)
  next
    case False
    then have "x \<in> set ys" using Cons.prems by simp
    then have "x \<le> wfs_maxe ys" using Cons.IH by blast
    then have "x \<le> max y (wfs_maxe ys)" by (rule max.coboundedI2)
    then show ?thesis by simp
  qed
qed

lemma wfc_G_lvT: "\<forall>u x. x \<in> GBT u t \<longrightarrow> wfs_lvT x \<le> wfs_lvT t"
  and wfc_G_lvP: "\<forall>u x. x \<in> GBP u q \<longrightarrow> wfs_lvT x \<le> wfs_lvP q"
proof (induction t and q rule: wfs_lvT_wfs_lvP.induct)
  case (1 ps)
  show ?case
  proof (intro allI impI)
    fix u x assume xin: "x \<in> GBT u (Trm ps)"
    obtain r where rin: "r \<in> set ps" and xr: "x \<in> GBP u r" using xin by auto
    have h1: "wfs_lvT x \<le> wfs_lvP r" using "1.IH"[OF rin] xr by blast
    have "wfs_lvP r \<in> set (map wfs_lvP ps)" using rin by simp
    then have h2: "wfs_lvP r \<le> wfs_maxe (map wfs_lvP ps)" by (rule wfc_maxe_mem)
    show "wfs_lvT x \<le> wfs_lvT (Trm ps)" using order_trans[OF h1 h2] by simp
  qed
next
  case (2 v b)
  show ?case
  proof (intro allI impI)
    fix u x assume xin: "x \<in> GBP u (DB v b)"
    have uv: "u \<le> v" using xin by (auto split: if_splits)
    have xc: "x = b \<or> x \<in> GBT u b" using xin uv by (auto split: if_splits)
    have bb: "wfs_lvT b \<le> wfs_lvP (DB v b)" by (simp add: max.cobounded2)
    show "wfs_lvT x \<le> wfs_lvP (DB v b)"
    proof (cases "x = b")
      case True
      then show ?thesis using bb by simp
    next
      case False
      then have "x \<in> GBT u b" using xc by blast
      then have "wfs_lvT x \<le> wfs_lvT b" using "2.IH" by blast
      then show ?thesis using bb by (rule order_trans)
    qed
  qed
qed

theorem wfc_acc_of_core_upto:
  assumes C: "wfc_core_upto n"
  shows "isOT_BP p \<Longrightarrow> dfree_BP p \<Longrightarrow> wfs_lvP p \<le> enat n \<Longrightarrow> p \<in> Wellfounded.acc RPrel"
proof (induction p rule: measure_induct_rule[where f = wfs_szP])
  case (less p)
  obtain v b where peq: "p = DB v b" by (cases p) auto
  have otp: "isOT_BP (DB v b)" using less.prems(1) peq by simp
  have dfp: "dfree_BP (DB v b)" using less.prems(2) peq by simp
  have otb: "isOT_BT b" using otp by simp
  have dfb: "dfree_BT b" using dfp by simp
  have vle: "v \<le> enat n"
  proof -
    have "v \<le> wfs_lvP p" using peq by (simp add: max.cobounded1)
    then show ?thesis using less.prems(3) by (rule order_trans)
  qed
  have lvb: "wfs_lvT b \<le> enat n"
  proof -
    have "wfs_lvT b \<le> wfs_lvP p" using peq by (simp add: max.cobounded2)
    then show ?thesis using less.prems(3) by (rule order_trans)
  qed
  have sec: "\<forall>x \<in> GBT v b. wfj_secT x"
  proof
    fix x assume xG: "x \<in> GBT v b"
    have otx: "isOT_BT x" using wfj_G_OT_T otb xG by blast
    have dfx: "dfree_BT x" using wfj_G_df_T dfb xG by blast
    have szx: "wfs_szT x < wfs_szT b" using wfj_G_szT xG by blast
    have lvx: "wfs_lvT x \<le> wfs_lvT b" using wfc_G_lvT xG by blast
    obtain rs where xeq: "x = Trm rs" by (cases x) auto
    have "\<forall>r \<in> set rs. r \<in> Wellfounded.acc RPrel"
    proof
      fix r assume rin: "r \<in> set rs"
      have otr: "isOT_BP r" using otx xeq rin by simp
      have dfr: "dfree_BP r" using dfx xeq rin by simp
      have szr: "wfs_szP r < wfs_szT x" using wfs_szP_mem_lt[OF rin] xeq by simp
      have szb: "wfs_szP p = Suc (wfs_szT b)" using peq by simp
      have szlt: "wfs_szP r < wfs_szP p" using szr szx szb by linarith
      have "wfs_lvP r \<in> set (map wfs_lvP rs)" using rin by simp
      then have "wfs_lvP r \<le> wfs_maxe (map wfs_lvP rs)" by (rule wfc_maxe_mem)
      then have "wfs_lvP r \<le> wfs_lvT x" using xeq by simp
      then have "wfs_lvP r \<le> wfs_lvT b" using lvx by (rule order_trans)
      then have lvr: "wfs_lvP r \<le> enat n" using lvb by (rule order_trans)
      show "r \<in> Wellfounded.acc RPrel" using less.IH[OF szlt otr dfr lvr] .
    qed
    then show "wfj_secT x" using xeq by simp
  qed
  have "DB v b \<in> Wellfounded.acc RPrel"
    using C[unfolded wfc_core_upto_def] vle otp dfp sec by blast
  then show ?case using peq by simp
qed

theorem wfc_acc_levels_of_jump_steps:
  assumes J: "\<And>n. wfc_jump_step n"
  shows "\<forall>p. isOT_BP p \<longrightarrow> dfree_BP p \<longrightarrow> wfs_lvP p \<le> enat n \<longrightarrow>
             p \<in> Wellfounded.acc RPrel"
proof (induction n)
  case 0
  show ?case
  proof (intro allI impI)
    fix p assume otp: "isOT_BP p" and dfp: "dfree_BP p" and lv: "wfs_lvP p \<le> enat 0"
    have "wfs_lvP p = 0"
      using lv by (cases "wfs_lvP p") (auto simp add: zero_enat_def)
    then show "p \<in> Wellfounded.acc RPrel"
      using wfs_level0_acc otp dfp by blast
  qed
next
  case (Suc n)
  have cu: "wfc_core_upto (Suc n)"
    using J[of n, unfolded wfc_jump_step_def] Suc.IH by blast
  show ?case
  proof (intro allI impI)
    fix p assume otp: "isOT_BP p" and dfp: "dfree_BP p"
      and lvp: "wfs_lvP p \<le> enat (Suc n)"
    show "p \<in> Wellfounded.acc RPrel"
      using wfc_acc_of_core_upto[OF cu otp dfp lvp] .
  qed
qed

theorem wfc_wf_of_jump_steps:
  assumes J: "\<And>n. wfc_jump_step n"
  shows "wf RPrel"
proof (rule acc_wfI)
  show "\<forall>x. x \<in> Wellfounded.acc RPrel"
  proof
    fix p :: BP
    show "p \<in> Wellfounded.acc RPrel"
    proof (cases "isOT_BP p \<and> dfree_BP p")
      case True
      have "wfs_lvP p \<noteq> \<infinity>" using wfs_lv_finP True by blast
      then obtain n where "wfs_lvP p = enat n" by (cases "wfs_lvP p") auto
      then have "wfs_lvP p \<le> enat n" by simp
      then show ?thesis using wfc_acc_levels_of_jump_steps[OF J] True by blast
    next
      case False
      show ?thesis
      proof (rule accI)
        fix q assume "(q, p) \<in> RPrel"
        then have "isOT_BP p \<and> dfree_BP p" by (auto simp add: RPrel_def)
        with False show "q \<in> Wellfounded.acc RPrel" by blast
      qed
    qed
  qed
qed

corollary wfc_level_jump_of_jump_steps:
  assumes "\<And>n. wfc_jump_step n"
  shows "wfs_level_jump"
  using wfj_level_jump_of_wf[OF wfc_wf_of_jump_steps[OF assms]] .

corollary wfc_collapse_core_of_jump_steps:
  assumes "\<And>n. wfc_jump_step n"
  shows "wfj_collapse_core"
  using wfj_collapse_core_of_wf[OF wfc_wf_of_jump_steps[OF assms]] .

lemma wfc_core_upto_of_wf:
  assumes "wf RPrel" shows "wfc_core_upto n"
proof -
  have "\<forall>p. p \<in> Wellfounded.acc RPrel" using assms wfs_wf_iff_all_acc by blast
  then show ?thesis unfolding wfc_core_upto_def by blast
qed

lemma wfc_jump_step_of_wf:
  assumes "wf RPrel" shows "wfc_jump_step n"
  using wfc_core_upto_of_wf[OF assms] unfolding wfc_jump_step_def by blast

theorem wfc_wf_iff_jump_steps: "wf RPrel \<longleftrightarrow> (\<forall>n. wfc_jump_step n)"
  using wfc_wf_of_jump_steps wfc_jump_step_of_wf by blast

lemma wfc_core_upto_of_collapse_core:
  assumes "wfj_collapse_core" shows "wfc_core_upto n"
  using assms unfolding wfj_collapse_core_def wfc_core_upto_def by blast

lemma wfc_collapse_core_of_upto:
  assumes A: "\<And>n. wfc_core_upto n"
  shows "wfj_collapse_core"
proof (unfold wfj_collapse_core_def, intro allI impI)
  fix v b assume otp: "isOT_BP (DB v b)" and dfp: "dfree_BP (DB v b)"
    and sec: "\<forall>x \<in> GBT v b. wfj_secT x"
  have "v \<noteq> \<infinity>" using dfp by simp
  then obtain k where vk: "v = enat k" by (cases v) auto
  have "v \<le> enat k" using vk by simp
  then show "DB v b \<in> Wellfounded.acc RPrel"
    using A[of k, unfolded wfc_core_upto_def] otp dfp sec by blast
qed


section \<open>Additional relocated campaign annotations\<close>

text \<open>\<^bold>\<open>Status after r53, and the honest obstruction analysis.\<close>

  \<^enum> CLOSED this round: \<open>G\<close>-antitonicity (\<open>wfc_GBT_antitone\<close>), secured-content
    propagation to unshielded components (\<open>wfc_sec_component\<close>), the same-head
    acc lift (\<open>wfc_principal_acc_of_body\<close>), the FULL head recursion
    (\<open>wfc_wf_of_pbody_hyp\<close>: body accessibility \<open>\<Longrightarrow>\<close> \<open>wf RPrel\<close>, by strong
    induction on the finite head via the r52 head stratification), tuple
    reflection (\<open>wfc_acc_component\<close> / \<open>wfc_tuple_acc_iff\<close>), the level-bounded
    bootstrap (\<open>wfc_G_lvT\<close> + \<open>wfc_acc_of_core_upto\<close>), and the staging
    \<open>(\<forall>n. wfc_jump_step n) \<Longrightarrow> wf RPrel\<close>.

  \<^enum> WHY an "induction on the secured tuple" CANNOT close the core by itself:
    in the \<open>accI\<close> step for \<open>D\<^sub>v a\<close> (secured), a predecessor \<open>q = D\<^sub>u w\<close> with
    \<open>u < v\<close> has a COMPLETELY unconstrained body \<open>w\<close> (\<open>lessBP\<close> compares heads
    first; no \<open>G\<close>-, size- or tuple-relation ties \<open>w\<close> to \<open>a\<close>).  Already at
    \<open>v = 1\<close> this branch demands accessibility of the entire \<open>\<psi>\<^sub>0\<close>-collapsed
    segment \<open>wfj_frag 0\<close>, which contains principals of EVERY \<open>lvP\<close>-level
    (\<open>wfj_frag0_lv_unbounded\<close>, r52).  So no wellfounded induction on
    \<open>(v, secured tuple of a)\<close> discharges it; the same-head branch, by
    contrast, is completely handled by the body order
    (\<open>wfc_principal_acc_of_body\<close>).

  \<^enum> The residual, in its two sharpest equivalent shapes:
    (i) GLOBAL: \<open>wfc_pbody_acc\<close> — \<open>RTrel\<close>-accessibility of the bodies of
        \<open>OT\<close>+\<open>dfree\<close> principals (head/tuple/secured bookkeeping all gone);
    (ii) STAGED: \<open>wfc_jump_step n\<close> — from the wellordered accessible
        level-\<open>n\<close> part (\<open>wfs_accord\<close>/\<open>wfs_rk\<close> give the wellorder and rank) to
        the collapse core for heads \<open>\<le> n + 1\<close>; the secured-coefficient
        premise and \<open>wfc_sec_component\<close> supply the inner \<open>G\<close>-recursion data.

  \<^enum> ROUTES to \<open>wfc_jump_step n\<close> (both genuinely impredicative — this is the
    \<open>\<psi>\<close>-collapse, in total proof-theoretically at \<open>\<Pi>\<^sup>1\<^sub>1-CA\<^sub>0\<close> grade):
    (a) DISTINGUISHED SETS (Buchholz--Schütte Fundierung, adapted): quantify
        over subsets \<open>M \<subseteq> BP\<close> that are wellfounded and \<open>C\<^sub>v\<close>-closed; HOL's
        impredicative comprehension carries the union-of-distinguished
        argument.  Est. 4--8 focused rounds (the linearity toolkit needed for
        comparability of distinguished sets is available).
    (b) SURROGATE-\<open>\<Omega>\<close> SEMANTICS: interpret into HOL wellorders (\<open><o\<close>), with
        \<open>\<Omega>\<^sub>v\<close> any strictly increasing ordinals of uncountable cofinality
        (\<open>\<omega>\<^sub>1\<cdot>(v+1)\<close>-grade suffices — the \<open>C\<close>-closures are countable); define
        \<open>C\<^sub>v(a)\<close>/\<open>\<psi>\<^sub>v\<close> by transfinite recursion and prove the interpretation
        strictly monotone on \<open>OT\<close> — [Buc1]'s own Lemma 2.2 proof, where the
        guard \<open>G\<^sub>v b < b\<close> (kept available in \<open>wfc_pbody_acc\<close> / supplied by
        \<open>wfc_sec_component\<close>) is exactly what makes \<open>\<psi>\<^sub>v\<close> order-faithful.
        Needs ordinal-recursion infrastructure beyond the current \<open>wfs_\<close>
        toolkit; est. 5--9 rounds.
    A purely syntactic per-\<open>v\<close> "relative rank" (r52 sketch) cannot avoid
    this: ranking \<open>D\<^sub>u\<close>-structure (\<open>u \<ge> v\<close>) over the level-\<open>n\<close> atoms
    re-creates the \<open>\<Omega>\<close>-tower (no ordinal fixed point \<open>B = \<omega>\<^bsup>B\<cdot>\<omega>\<^esup>\<close> exists),
    which is precisely why the collapse functions are load-bearing.\<close>

end
