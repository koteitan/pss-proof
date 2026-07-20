theory M_8_7_Wfj_Level_Jump
  imports M_8_7_Wfs_Semantic_Rank
begin

text \<open>Relocated proof material.  The declarations retain their original source order,
  and every relocated annotation is preserved below.  This theory is machine-checked
  outside the termination build tree.\<close>

lemma wfj_hd_le:
  assumes "(q, p) \<in> RPrel"
  shows "wfj_hd q \<le> wfj_hd p"
proof -
  obtain u w where qeq: "q = DB u w" by (cases q) auto
  obtain v c where peq: "p = DB v c" by (cases p) auto
  have "lessBP q p" using assms by (simp add: RPrel_def)
  then have "u < v \<or> (u = v \<and> lessBT w c)" using qeq peq by simp
  then show ?thesis using qeq peq by auto
qed

lemma wfj_strat_hd:
  assumes "(q, p) \<in> RPrel" and "wfj_hd p \<le> enat n"
  shows "wfj_hd q \<le> enat n"
  using wfj_hd_le[OF assms(1)] assms(2) order_trans by blast

lemma wfj_hd_le_lvP: "wfj_hd p \<le> wfs_lvP p"
  by (cases p) (simp add: max.cobounded1)

subsection \<open>(1b) STRAT-\<open>n\<close> for \<open>wfs_lvP\<close> is FALSE for every \<open>n \<ge> 1\<close>\<close>

lemma wfj_enat_max0: "max (x::enat) 0 = x"
  by (rule max_absorb1[OF zero_le])

lemma wfj_enat_0max: "max (0::enat) x = x"
  by (rule max_absorb2[OF zero_le])

lemma wfj_cexq_OT: "isOT_BP (wfj_cexq k)"
  by (simp add: wfj_cexq_def)

lemma wfj_cexq_dfree: "dfree_BP (wfj_cexq k)"
  by (simp add: wfj_cexq_def zero_enat_def)

lemma wfj_cexq_lv: "wfs_lvP (wfj_cexq k) = enat k"
  by (simp add: wfj_cexq_def wfj_enat_max0 wfj_enat_0max)

lemma wfj_cexq_hd: "wfj_hd (wfj_cexq k) = 0"
  by (simp add: wfj_cexq_def)

theorem wfj_stratn_lvP_refuted:
  assumes n1: "1 \<le> n"
  shows "\<exists>q p. (q, p) \<in> RPrel \<and> wfs_lvP p \<le> enat n \<and> \<not> wfs_lvP q \<le> enat n"
proof -
  have otp: "isOT_BP (DB (enat 1) (Trm []))" by simp
  have dfp: "dfree_BP (DB (enat 1) (Trm []))" by simp
  have lvp: "wfs_lvP (DB (enat 1) (Trm [])) = enat 1" by (simp add: wfj_enat_max0)
  have qp: "lessBP (wfj_cexq (Suc n)) (DB (enat 1) (Trm []))"
    by (simp add: wfj_cexq_def zero_enat_def)
  have inR: "(wfj_cexq (Suc n), DB (enat 1) (Trm [])) \<in> RPrel"
    using wfj_cexq_OT wfj_cexq_dfree otp dfp qp by (simp add: RPrel_def)
  have lep: "wfs_lvP (DB (enat 1) (Trm [])) \<le> enat n" using lvp n1 by simp
  have nleq: "\<not> wfs_lvP (wfj_cexq (Suc n)) \<le> enat n" by (simp add: wfj_cexq_lv)
  show ?thesis using inR lep nleq by blast
qed

corollary wfj_stratn_lvP_false:
  "\<not> (\<forall>n q p. 1 \<le> n \<longrightarrow> (q, p) \<in> RPrel \<longrightarrow> wfs_lvP p \<le> enat n \<longrightarrow> wfs_lvP q \<le> enat n)"
  using wfj_stratn_lvP_refuted by blast

lemma wfj_frag_downclosed:
  assumes sf: "s \<in> wfj_frag n" and qs: "(q, s) \<in> RPrel"
  shows "q \<in> wfj_frag n"
proof -
  have hq: "wfj_hd q \<le> wfj_hd s" by (rule wfj_hd_le[OF qs])
  have hs: "wfj_hd s \<le> enat n" using sf by (simp add: wfj_frag_def)
  have hn: "wfj_hd q \<le> enat n" using hq hs by (rule order_trans)
  have qg: "isOT_BP q" "dfree_BP q" using qs by (auto simp add: RPrel_def)
  show ?thesis using hn qg by (simp add: wfj_frag_def)
qed

lemma wfj_frag_mono:
  assumes "n \<le> m" shows "wfj_frag n \<subseteq> wfj_frag m"
proof
  fix p assume "p \<in> wfj_frag n"
  then have f1: "isOT_BP p" and f2: "dfree_BP p" and f3: "wfj_hd p \<le> enat n"
    by (auto simp add: wfj_frag_def)
  have "wfj_hd p \<le> enat m" by (rule order_trans[OF f3]) (simp add: assms)
  then show "p \<in> wfj_frag m" using f1 f2 by (simp add: wfj_frag_def)
qed

lemma wfj_lv_in_frag:
  assumes "isOT_BP p" and "dfree_BP p" and "wfs_lvP p \<le> enat n"
  shows "p \<in> wfj_frag n"
proof -
  have "wfj_hd p \<le> enat n" by (rule order_trans[OF wfj_hd_le_lvP assms(3)])
  then show ?thesis using assms(1,2) by (simp add: wfj_frag_def)
qed

text \<open>\<^bold>\<open>No easy base\<close>: the bottom fragment \<open>wfj_frag 0\<close> (the terms below \<open>\<Omega>\<^sub>1\<close>)
  already contains principals of EVERY \<open>wfs_lvP\<close>-level — it is the \<open>\<psi>\<^sub>0\<close>-collapsed
  image of the whole system, NOT an \<open>\<epsilon>\<^sub>0\<close>-sized base case.  So neither stratification
  gives a climbable ladder by itself: the \<open>lvP\<close>-fragments have easy bases but are not
  downward closed (refuted above); the head fragments are downward closed but their
  bottom already carries full collapsing strength.\<close>

lemma wfj_frag0_lv_unbounded: "\<exists>p \<in> wfj_frag 0. wfs_lvP p = enat k"
proof -
  have "wfj_cexq k \<in> wfj_frag 0"
    using wfj_cexq_OT wfj_cexq_dfree
    by (simp add: wfj_frag_def wfj_cexq_hd zero_enat_def)
  then show ?thesis using wfj_cexq_lv by blast
qed

theorem wfj_wf_RPrel_of_all_levels:
  assumes A: "\<forall>n. wfj_level_wf n"
  shows "wf RPrel"
proof (rule acc_wfI)
  show "\<forall>x. x \<in> Wellfounded.acc RPrel"
  proof
    fix p :: BP
    show "p \<in> Wellfounded.acc RPrel"
    proof (cases "isOT_BP p \<and> dfree_BP p")
      case True
      obtain v b where peq: "p = DB v b" by (cases p) auto
      have dfp: "dfree_BP (DB v b)" using True peq by simp
      then have "v \<noteq> \<infinity>" by simp
      then obtain k where vk: "v = enat k" by (cases v) auto
      have pfrag: "p \<in> wfj_frag k" using True peq vk by (simp add: wfj_frag_def)
      have dc: "\<forall>s q. s \<in> wfj_frag k \<longrightarrow> (q, s) \<in> RPrel \<longrightarrow> q \<in> wfj_frag k"
        using wfj_frag_downclosed by blast
      have wfk: "wf (Restr RPrel (wfj_frag k))"
        using A by (simp add: wfj_level_wf_def)
      have "wfj_frag k \<subseteq> Wellfounded.acc RPrel"
        by (rule wfs_closed_wf_acc[OF dc wfk])
      then show ?thesis using pfrag by blast
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

lemma wfj_all_levels_of_wf:
  assumes "wf RPrel" shows "wfj_level_wf n"
  using assms unfolding wfj_level_wf_def by (simp add: wf_Int1)

theorem wfj_wf_iff_all_levels: "wf RPrel \<longleftrightarrow> (\<forall>n. wfj_level_wf n)"
  using wfj_wf_RPrel_of_all_levels wfj_all_levels_of_wf by blast

lemma wfj_level_jump_of_wf:
  assumes "wf RPrel" shows "wfs_level_jump"
proof -
  have "\<forall>p. p \<in> Wellfounded.acc RPrel" using assms wfs_wf_iff_all_acc by blast
  then show ?thesis unfolding wfs_level_jump_def by blast
qed

theorem wfj_level_jump_of_all_levels:
  assumes "\<forall>n. wfj_level_wf n" shows "wfs_level_jump"
  using wfj_level_jump_of_wf wfj_wf_RPrel_of_all_levels[OF assms] by blast

subsection \<open>(3) The jump opening: \<open>G\<close>-set bricks and the SECURED-COEFFICIENT
  collapse core\<close>

text \<open>Since neither level ladder climbs (see above), the residual is re-sharpened from
  the per-level \<open>wfs_level_jump\<close> to the GLOBAL collapse engine.  The \<open>G\<^sub>v\<close>-elements of
  a body are proper subterms (\<open>wfj_G_szT\<close>), and they inherit \<open>OT\<close>/\<open>dfree\<close>
  (\<open>wfj_G_OT_T\<close>/\<open>wfj_G_df_T\<close>); call a term SECURED when all its principal components
  are already accessible (\<open>wfj_secT\<close>).  The engine statement \<open>wfj_collapse_core\<close> —
  an \<open>OT\<close>+\<open>dfree\<close> principal \<open>D\<^sub>v b\<close> whose \<open>G\<^sub>v\<close>-coefficients are all secured is
  itself accessible — then yields the WHOLE goal by a plain structural-size induction
  (\<open>wfj_acc_of_collapse_core\<close>): no level bookkeeping survives.\<close>

lemma wfj_G_szT: "\<forall>u x. x \<in> GBT u t \<longrightarrow> wfs_szT x < wfs_szT t"
  and wfj_G_szP: "\<forall>u x. x \<in> GBP u q \<longrightarrow> wfs_szT x < wfs_szP q"
proof (induction t and q rule: wfs_lvT_wfs_lvP.induct)
  case (1 ps)
  show ?case
  proof (intro allI impI)
    fix u x assume xin: "x \<in> GBT u (Trm ps)"
    obtain r where rin: "r \<in> set ps" and xr: "x \<in> GBP u r" using xin by auto
    have s1: "wfs_szT x < wfs_szP r" using "1.IH"[OF rin] xr by blast
    have s2: "wfs_szP r \<le> sum_list (map wfs_szP ps)" using wfs_szP_mem[OF rin] .
    have s3: "wfs_szT (Trm ps) = Suc (sum_list (map wfs_szP ps))" by simp
    show "wfs_szT x < wfs_szT (Trm ps)" using s1 s2 s3 by linarith
  qed
next
  case (2 v b)
  show ?case
  proof (intro allI impI)
    fix u x assume xin: "x \<in> GBP u (DB v b)"
    have sb: "wfs_szP (DB v b) = Suc (wfs_szT b)" by simp
    show "wfs_szT x < wfs_szP (DB v b)"
    proof (cases "u \<le> v")
      case True
      then have xc: "x = b \<or> x \<in> GBT u b" using xin by (auto split: if_splits)
      show ?thesis
      proof (cases "x = b")
        case True then show ?thesis using sb by simp
      next
        case False
        then have "x \<in> GBT u b" using xc by blast
        then have "wfs_szT x < wfs_szT b" using "2.IH" by blast
        then show ?thesis using sb by linarith
      qed
    next
      case False
      then show ?thesis using xin by simp
    qed
  qed
qed

lemma wfj_G_df_T: "\<forall>u x. dfree_BT t \<longrightarrow> x \<in> GBT u t \<longrightarrow> dfree_BT x"
  and wfj_G_df_P: "\<forall>u x. dfree_BP q \<longrightarrow> x \<in> GBP u q \<longrightarrow> dfree_BT x"
proof (induction t and q rule: wfs_lvT_wfs_lvP.induct)
  case (1 ps)
  show ?case
  proof (intro allI impI)
    fix u x assume df: "dfree_BT (Trm ps)" and xin: "x \<in> GBT u (Trm ps)"
    obtain r where rin: "r \<in> set ps" and xr: "x \<in> GBP u r" using xin by auto
    have dfr: "dfree_BP r" using df rin by simp
    show "dfree_BT x" using "1.IH"[OF rin] dfr xr by blast
  qed
next
  case (2 v b)
  show ?case
  proof (intro allI impI)
    fix u x assume df: "dfree_BP (DB v b)" and xin: "x \<in> GBP u (DB v b)"
    have dfb: "dfree_BT b" using df by simp
    show "dfree_BT x"
    proof (cases "u \<le> v")
      case True
      then have "x = b \<or> x \<in> GBT u b" using xin by (auto split: if_splits)
      then show ?thesis using "2.IH" dfb by blast
    next
      case False
      then show ?thesis using xin by simp
    qed
  qed
qed

text \<open>\<^bold>\<open>The bootstrap\<close>: the engine alone yields accessibility of EVERY \<open>OT\<close>+\<open>dfree\<close>
  principal, by structural-size induction — the \<open>G\<^sub>v\<close>-coefficients are proper
  subterms, so their components are accessible by the induction hypothesis.\<close>

theorem wfj_acc_of_collapse_core:
  assumes C: "wfj_collapse_core"
  shows "isOT_BP p \<Longrightarrow> dfree_BP p \<Longrightarrow> p \<in> Wellfounded.acc RPrel"
proof (induction p rule: measure_induct_rule[where f = wfs_szP])
  case (less p)
  obtain v b where peq: "p = DB v b" by (cases p) auto
  have otp: "isOT_BP (DB v b)" using less.prems(1) peq by simp
  have dfp: "dfree_BP (DB v b)" using less.prems(2) peq by simp
  have otb: "isOT_BT b" using otp by simp
  have dfb: "dfree_BT b" using dfp by simp
  have sec: "\<forall>x \<in> GBT v b. wfj_secT x"
  proof
    fix x assume xG: "x \<in> GBT v b"
    have otx: "isOT_BT x" using wfj_G_OT_T otb xG by blast
    have dfx: "dfree_BT x" using wfj_G_df_T dfb xG by blast
    have szx: "wfs_szT x < wfs_szT b" using wfj_G_szT xG by blast
    obtain rs where xeq: "x = Trm rs" by (cases x) auto
    have "\<forall>r \<in> set rs. r \<in> Wellfounded.acc RPrel"
    proof
      fix r assume rin: "r \<in> set rs"
      have otr: "isOT_BP r" using otx xeq rin by simp
      have dfr: "dfree_BP r" using dfx xeq rin by simp
      have szr: "wfs_szP r < wfs_szT x" using wfs_szP_mem_lt[OF rin] xeq by simp
      have szb: "wfs_szP p = Suc (wfs_szT b)" using peq by simp
      have "wfs_szP r < wfs_szP p" using szr szx szb by linarith
      then show "r \<in> Wellfounded.acc RPrel" using less.IH otr dfr by blast
    qed
    then show "wfj_secT x" using xeq by simp
  qed
  have "DB v b \<in> Wellfounded.acc RPrel"
    using C[unfolded wfj_collapse_core_def] otp dfp sec by blast
  then show ?case using peq by simp
qed

theorem wfj_wf_RPrel_of_collapse_core:
  assumes C: "wfj_collapse_core"
  shows "wf RPrel"
proof (rule acc_wfI)
  show "\<forall>x. x \<in> Wellfounded.acc RPrel"
  proof
    fix p :: BP
    show "p \<in> Wellfounded.acc RPrel"
    proof (cases "isOT_BP p \<and> dfree_BP p")
      case True
      then show ?thesis using wfj_acc_of_collapse_core[OF C] by blast
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

lemma wfj_collapse_core_of_wf:
  assumes "wf RPrel" shows "wfj_collapse_core"
proof -
  have "\<forall>p. p \<in> Wellfounded.acc RPrel" using assms wfs_wf_iff_all_acc by blast
  then show ?thesis unfolding wfj_collapse_core_def by blast
qed

theorem wfj_collapse_core_iff_wf: "wfj_collapse_core \<longleftrightarrow> wf RPrel"
  using wfj_wf_RPrel_of_collapse_core wfj_collapse_core_of_wf by blast

theorem wfj_collapse_core_iff_level_jump: "wfj_collapse_core \<longleftrightarrow> wfs_level_jump"
  using wfj_collapse_core_iff_wf wfj_level_jump_of_wf
        wfs_wf_RPrel_of_level_jump wfj_collapse_core_of_wf by blast

corollary wfj_all_levels_of_collapse_core:
  assumes "wfj_collapse_core" shows "wfj_level_wf n"
  using wfj_all_levels_of_wf[OF wfj_wf_RPrel_of_collapse_core[OF assms]] .

theorem wfj_OT_B_wf_of_collapse_core:
  assumes "wfj_collapse_core"
  shows "wf {(a, b). a \<in> OT_B \<and> b \<in> OT_B \<and> lessBT a b}"
  using m_buc1_2_2_OT_B_wf_via_principal[OF wfj_wf_RPrel_of_collapse_core[OF assms]] .

text \<open>Reflection back to principals, in the form the engine will consume: an \<open>OT\<close>+\<open>dfree\<close>
  principal is accessible iff its body's components are — the same-head layer of
  \<open>RPrel\<close> descends into \<open>RTrel\<close> on the body (\<open>wfox_RPrel_subterm\<close>).\<close>

lemma wfj_secT_tuple_acc:
  assumes "isOT_BT t" and "dfree_BT t" and "wfj_secT t"
  shows "t \<in> Wellfounded.acc RTrel"
proof -
  obtain rs where teq: "t = Trm rs" by (cases t) auto
  have "\<forall>r \<in> set (untrm t). r \<in> Wellfounded.acc RPrel"
    using assms(3) teq by simp
  then show ?thesis using wfj_tuple_acc assms(1,2) by blast
qed


section \<open>Additional relocated campaign annotations\<close>

text \<open>\<^bold>\<open>Status after r52 and route for the engine\<close>.

  \<^enum> REFUTED: the r51 plan's STRAT-\<open>n\<close> (\<open>lvP\<close>-fragments downward closed), for every
    \<open>n \<ge> 1\<close> (\<open>wfj_stratn_lvP_refuted\<close>).  The \<open>lvP\<close>-level ladder behind
    \<open>wfs_level_jump\<close> cannot be climbed stepwise: already the \<open>n = 0 \<Rightarrow> 1\<close> step
    pulls in the accessibility of \<open>D\<^sub>0 b\<close> for ARBITRARY \<open>OT\<close> bodies \<open>b\<close> (all of
    \<open>wfj_frag 0\<close>), i.e. the full collapsing strength.
  \<^enum> TRUE stratification: head index (\<open>wfj_frag\<close>, downward closed, no \<open>G\<close>-condition);
    all levels together \<open>\<longleftrightarrow>\<close> \<open>wf RPrel\<close>; but \<open>wfj_frag 0\<close> is the full
    \<open>\<psi>\<^sub>0\<close>-collapsed segment (\<open>wfj_frag0_lv_unbounded\<close>) — no easy base either.
  \<^enum> The goal is now concentrated in ONE genuinely global residual,
    \<open>wfj_collapse_core \<longleftrightarrow> wf RPrel \<longleftrightarrow> wfs_level_jump\<close>: accessibility of a
    principal with SECURED \<open>G\<^sub>v\<close>-coefficients.  Everything around it (bootstrap by
    size induction, per-level plumbing, [Buc1] 2.2 readback) is proven.
  \<^enum> Engine route (est. 2--4 focused rounds, classical distinguished-set /
    relative-rank argument): for fixed \<open>v\<close>, interpret bodies-with-secured-content by
    a RELATIVE RANK into wellorders over the already-accessible part — atoms =
    principals of head \<open>< v\<close> ranked by \<open>wfs_rk\<close> inside \<open>wfs_accord\<close> (r51 toolkit),
    tuples = descending words (dictionary order over a wellorder; NOTE
    \<open>HOL-Library.Multiset\<close> is NOT importable here — reuse the hand-rolled multiset
    layer of the \<open>wfox_\<close>/\<open>wfpd_\<close> blocks), \<open>D\<^sub>u\<close> for \<open>u \<ge> v\<close> = structural pairs
    \<open>(u, rank of argument)\<close>.  Load-bearing lemma: strict monotonicity of this rank
    along \<open>lessBT\<close> on secured \<open>OT\<close> bodies, where the \<open>G\<^sub>v < b\<close> condition is exactly
    what keeps the head case honest.  The engine recursion on the head index \<open>v\<close>
    must additionally secure the shielded (head \<open>< v\<close>) principals inside \<open>b\<close> —
    they are NOT covered by the secured-coefficient premise.\<close>

end
