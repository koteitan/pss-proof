theory M_8_7_Wcl_Collapse_Obstruction
  imports M_8_7_Wds_Distinguished_Sets
begin

text \<open>Relocated proof material.  The declarations retain their original source order,
  and every relocated annotation is preserved below.  This theory is machine-checked
  outside the termination build tree.\<close>

(* ===================================================================== *)
(* ===== r63 wcl: buc1-collapse --- engine-entry framing of THE       ===== *)
(* ===== residual wds_collapse (= wfj_collapse_core = wfc_pbody_acc    ===== *)
(* ===== = wf RPrel), the last external citation [Buc1] Lemma 2.2      ===== *)
(* ===== (Buchholz--Schuette Fundierung of (OT_B,<)).                  ===== *)
(* =====                                                               ===== *)
(* ===== This block delivers UNCONDITIONAL structural bricks that      ===== *)
(* ===== sharpen the attack surface for the collapse, WITHOUT citing   ===== *)
(* ===== any residual:                                                 ===== *)
(* =====  (A) wcl_min_bad_secured: the wfs_szP-minimal counterexample  ===== *)
(* =====      to accessibility is automatically G-trace-SECURED        ===== *)
(* =====      (wfj_secT) --- the standard [Buc1]/Buchholz--Schuette     ===== *)
(* =====      entry point: what the collapse engine must refute is a    ===== *)
(* =====      SECURED principal that fails to be accessible.            ===== *)
(* =====  (B) wcl_accfrag_*: the accessible fragment                   ===== *)
(* =====      wfj_frag v \<inter> acc RPrel satisfies the domain/downward/    ===== *)
(* =====      relative-acc clauses of wds_distinguished UNCONDITIONALLY;===== *)
(* =====      its 4th (G-progressiveness) clause is EXACTLY the         ===== *)
(* =====      collapse-core, so under the residual it is the CONCRETE   ===== *)
(* =====      maximal v-distinguished set (= wds_Mset v), discharging   ===== *)
(* =====      the r54 honesty note on D1 witness existence.             ===== *)
(* ===================================================================== *)

section \<open>r63-wcl --- [Buc1] 2.2 collapse: engine-entry framing (prefix \<open>wcl_\<close>)\<close>

subsection \<open>(A) The minimal counterexample to the collapse is \<open>G\<close>-trace-secured\<close>

text \<open>Contrapositive entry point of \<open>wfj_acc_of_collapse_core\<close>: if some
  \<open>OT\<close>+\<open>dfree\<close> principal is NOT \<open>RPrel\<close>-accessible, then a \<open>wfs_szP\<close>-minimal
  such principal \<open>D\<^sub>v b\<close> has its whole \<open>G\<^sub>v\<close>-trace already SECURED
  (\<open>wfj_secT\<close>): the trace components are proper subterms (\<open>wfj_G_szT\<close>), hence
  accessible by \<open>wfs_szP\<close>-minimality.  This is exactly the object the [Buc1]
  Lemma 2.2 collapse must refute --- a secured principal failing to be
  accessible.  Because \<open>wfj_collapse_core \<longleftrightarrow> wf RPrel\<close>
  (\<open>wfj_collapse_core_iff_wf\<close>) and \<open>wds_collapse \<longleftrightarrow> wf RPrel\<close>
  (\<open>wds_collapse_iff_wf\<close>), refuting this single witness closes the last
  external citation.  Unconditional (no residual cited).\<close>

lemma wcl_min_bad_secured:
  assumes bad: "\<not> (\<forall>p. isOT_BP p \<longrightarrow> dfree_BP p \<longrightarrow> p \<in> Wellfounded.acc RPrel)"
  shows "\<exists>v b. isOT_BP (DB v b) \<and> dfree_BP (DB v b)
               \<and> DB v b \<notin> Wellfounded.acc RPrel
               \<and> (\<forall>x \<in> GBT v b. wfj_secT x)"
proof -
  define Bad where
    "Bad = {p. isOT_BP p \<and> dfree_BP p \<and> p \<notin> Wellfounded.acc RPrel}"
  from bad obtain p0 where p0Bad: "p0 \<in> Bad" unfolding Bad_def by blast
  have wfm: "wf (measure wfs_szP)" by (rule wf_measure)
  have "\<exists>z\<in>Bad. \<forall>y. (y, z) \<in> measure wfs_szP \<longrightarrow> y \<notin> Bad"
    using wfm[unfolded wf_eq_minimal] p0Bad by blast
  then obtain z where zBad: "z \<in> Bad"
    and zmin: "\<forall>y. (y, z) \<in> measure wfs_szP \<longrightarrow> y \<notin> Bad" by blast
  have zot: "isOT_BP z" and zdf: "dfree_BP z"
    and znacc: "z \<notin> Wellfounded.acc RPrel"
    using zBad unfolding Bad_def by auto
  obtain v b where zeq: "z = DB v b" by (cases z) auto
  have otb: "isOT_BT b" using zot zeq by simp
  have dfb: "dfree_BT b" using zdf zeq by simp
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
      have szb: "wfs_szP z = Suc (wfs_szT b)" using zeq by simp
      have "wfs_szP r < wfs_szP z" using szr szx szb by linarith
      then have "(r, z) \<in> measure wfs_szP" by simp
      then have "r \<notin> Bad" using zmin by blast
      then show "r \<in> Wellfounded.acc RPrel"
        using otr dfr unfolding Bad_def by blast
    qed
    then show "wfj_secT x" using xeq by simp
  qed
  show ?thesis using zot zdf znacc sec zeq by blast
qed

text \<open>The immediate corollary in the exact \<open>wfj_collapse_core\<close> shape: refuting
  the secured witness IS the collapse core (hence \<open>wf RPrel\<close> and [Buc1] 2.2).
  This is the sharpest self-contained statement of what remains.\<close>

lemma wcl_core_iff_no_bad_secured:
  "wfj_collapse_core \<longleftrightarrow>
     \<not> (\<exists>v b. isOT_BP (DB v b) \<and> dfree_BP (DB v b)
             \<and> DB v b \<notin> Wellfounded.acc RPrel
             \<and> (\<forall>x \<in> GBT v b. wfj_secT x))"
proof
  assume C: "wfj_collapse_core"
  show "\<not> (\<exists>v b. isOT_BP (DB v b) \<and> dfree_BP (DB v b)
             \<and> DB v b \<notin> Wellfounded.acc RPrel
             \<and> (\<forall>x \<in> GBT v b. wfj_secT x))"
    using C[unfolded wfj_collapse_core_def] by blast
next
  assume R: "\<not> (\<exists>v b. isOT_BP (DB v b) \<and> dfree_BP (DB v b)
             \<and> DB v b \<notin> Wellfounded.acc RPrel
             \<and> (\<forall>x \<in> GBT v b. wfj_secT x))"
  show "wfj_collapse_core"
    unfolding wfj_collapse_core_def using R by blast
qed

subsection \<open>(B) The accessible fragment \<open>wfj_frag v \<inter> acc RPrel\<close> is the
  concrete maximal \<open>v\<close>-distinguished set\<close>

text \<open>Clauses 1--3 (domain, \<open>RPrel\<close>-downward closure, relative accessibility)
  of \<open>wds_distinguished\<close> hold for \<open>A\<^sub>v = wfj_frag v \<inter> acc RPrel\<close>
  UNCONDITIONALLY; clause 4 (\<open>G\<close>-progressiveness) is discharged by
  \<open>wfj_collapse_core\<close>.  So under the residual \<open>A\<^sub>v\<close> is the CONCRETE witness that
  the r54 D1 lemma (\<open>wds_Mset_distinguished\<close>) left abstract, and
  \<open>wds_Mset v = wfj_frag v \<inter> acc RPrel\<close>.\<close>

lemma wcl_accfrag_downclosed:
  assumes pA: "p \<in> wfj_frag v \<inter> Wellfounded.acc RPrel"
    and qp: "(q, p) \<in> RPrel"
  shows "q \<in> wfj_frag v \<inter> Wellfounded.acc RPrel"
proof -
  have qf: "q \<in> wfj_frag v" using wfj_frag_downclosed pA qp by blast
  have pacc: "p \<in> Wellfounded.acc RPrel" using pA by blast
  have "q \<in> Wellfounded.acc RPrel" using acc_downward[OF pacc qp] .
  then show ?thesis using qf by blast
qed

lemma wcl_accfrag_relacc:
  assumes pA: "p \<in> wfj_frag v \<inter> Wellfounded.acc RPrel"
  shows "p \<in> Wellfounded.acc (Restr RPrel (wfj_frag v \<inter> Wellfounded.acc RPrel))"
proof -
  have "p \<in> Wellfounded.acc RPrel" using pA by blast
  moreover have "Restr RPrel (wfj_frag v \<inter> Wellfounded.acc RPrel) \<subseteq> RPrel"
    by blast
  ultimately show ?thesis using acc_subset by blast
qed

lemma wcl_accfrag_prog_of_core:
  assumes C: "wfj_collapse_core"
    and uv: "u \<le> v" and ot: "isOT_BP (DB (enat u) c)"
    and df: "dfree_BP (DB (enat u) c)"
    and cnt: "\<forall>x \<in> GBT (enat u) c.
                x \<in> wds_hullT (wfj_frag v \<inter> Wellfounded.acc RPrel)"
  shows "DB (enat u) c \<in> wfj_frag v \<inter> Wellfounded.acc RPrel"
proof -
  have sec: "\<forall>x \<in> GBT (enat u) c. wfj_secT x"
  proof
    fix x assume xG: "x \<in> GBT (enat u) c"
    obtain rs where xeq: "x = Trm rs" by (cases x) auto
    have "\<forall>r \<in> set rs. r \<in> Wellfounded.acc RPrel"
    proof
      fix r assume rin: "r \<in> set rs"
      have "r \<in> set (untrm x)" using xeq rin by simp
      then have "r \<in> wfj_frag v \<inter> Wellfounded.acc RPrel"
        using cnt xG by (simp add: wds_hullT_iff)
      then show "r \<in> Wellfounded.acc RPrel" by blast
    qed
    then show "wfj_secT x" using xeq by simp
  qed
  have acc: "DB (enat u) c \<in> Wellfounded.acc RPrel"
    using C[unfolded wfj_collapse_core_def] ot df sec by blast
  have "wfj_hd (DB (enat u) c) \<le> enat v" using uv by simp
  then have "DB (enat u) c \<in> wfj_frag v" using ot df by (simp add: wfj_frag_def)
  then show ?thesis using acc by blast
qed

theorem wcl_accfrag_distinguished_of_core:
  assumes C: "wfj_collapse_core"
  shows "wds_distinguished v (wfj_frag v \<inter> Wellfounded.acc RPrel)"
proof (rule wds_distI)
  show "wfj_frag v \<inter> Wellfounded.acc RPrel \<subseteq> wfj_frag v" by blast
next
  fix p q assume "p \<in> wfj_frag v \<inter> Wellfounded.acc RPrel"
    and "(q, p) \<in> RPrel"
  then show "q \<in> wfj_frag v \<inter> Wellfounded.acc RPrel"
    by (rule wcl_accfrag_downclosed)
next
  fix p assume "p \<in> wfj_frag v \<inter> Wellfounded.acc RPrel"
  then show "p \<in> Wellfounded.acc (Restr RPrel (wfj_frag v \<inter> Wellfounded.acc RPrel))"
    by (rule wcl_accfrag_relacc)
next
  fix u c
  assume "u \<le> v" and "isOT_BP (DB (enat u) c)" and "dfree_BP (DB (enat u) c)"
    and "\<forall>x \<in> GBT (enat u) c.
           x \<in> wds_hullT (wfj_frag v \<inter> Wellfounded.acc RPrel)"
  then show "DB (enat u) c \<in> wfj_frag v \<inter> Wellfounded.acc RPrel"
    by (rule wcl_accfrag_prog_of_core[OF C])
qed

corollary wcl_Mset_distinguished_of_core:
  assumes C: "wfj_collapse_core"
  shows "wds_distinguished v (wds_Mset v)"
  by (rule wds_Mset_distinguished[OF wcl_accfrag_distinguished_of_core[OF C]])

corollary wcl_Mset_eq_accfrag_of_core:
  assumes C: "wfj_collapse_core"
  shows "wds_Mset v = wfj_frag v \<inter> Wellfounded.acc RPrel"
proof (rule subset_antisym)
  have "wds_Mset v \<subseteq> wfj_frag v" by (rule wds_Mset_frag)
  moreover have "wds_Mset v \<subseteq> Wellfounded.acc RPrel"
    by (rule wds_Mset_subset_acc)
  ultimately show "wds_Mset v \<subseteq> wfj_frag v \<inter> Wellfounded.acc RPrel" by blast
next
  show "wfj_frag v \<inter> Wellfounded.acc RPrel \<subseteq> wds_Mset v"
    by (rule wds_Mset_upper[OF wcl_accfrag_distinguished_of_core[OF C]])
qed

text \<open>Direct single-name bridge between the two named residuals (previously
  connected only transitively through \<open>wf RPrel\<close>): the collapse core yields
  \<open>wds_collapse\<close> via the concrete accessible-fragment witness.\<close>

corollary wcl_collapse_of_core:
  assumes "wfj_collapse_core" shows "wds_collapse"
  by (rule wds_collapse_of_wf[OF wfj_wf_RPrel_of_collapse_core[OF assms]])

subsection \<open>(C) The minimal counterexample has an \<open>RTrel\<close>-accessible BODY:
  the obstruction is purely the head-\<open>< v\<close> lower segment\<close>

text \<open>Sharper than (A): the \<open>wfs_szP\<close>-minimal non-accessible \<open>OT\<close>+\<open>dfree\<close>
  principal \<open>D\<^sub>v b\<close> has an \<open>RTrel\<close>-accessible BODY \<open>b\<close> (its DIRECT components
  are proper subterms, accessible by minimality; \<open>wfj_secT_tuple_acc\<close>).  Note
  this is complementary to (A): the \<open>G\<^sub>v\<close>-trace shields head-\<open>< v\<close> principals
  (r52 note: they are NOT covered by \<open>wfj_secT\<close>), whereas the direct body
  components ARE secured by size-minimality.\<close>

lemma wcl_min_bad_body_acc:
  assumes bad: "\<not> (\<forall>p. isOT_BP p \<longrightarrow> dfree_BP p \<longrightarrow> p \<in> Wellfounded.acc RPrel)"
  shows "\<exists>v b. isOT_BP (DB v b) \<and> dfree_BP (DB v b)
               \<and> DB v b \<notin> Wellfounded.acc RPrel
               \<and> b \<in> Wellfounded.acc RTrel"
proof -
  define Bad where
    "Bad = {p. isOT_BP p \<and> dfree_BP p \<and> p \<notin> Wellfounded.acc RPrel}"
  from bad obtain p0 where p0Bad: "p0 \<in> Bad" unfolding Bad_def by blast
  have wfm: "wf (measure wfs_szP)" by (rule wf_measure)
  have "\<exists>z\<in>Bad. \<forall>y. (y, z) \<in> measure wfs_szP \<longrightarrow> y \<notin> Bad"
    using wfm[unfolded wf_eq_minimal] p0Bad by blast
  then obtain z where zBad: "z \<in> Bad"
    and zmin: "\<forall>y. (y, z) \<in> measure wfs_szP \<longrightarrow> y \<notin> Bad" by blast
  have zot: "isOT_BP z" and zdf: "dfree_BP z"
    and znacc: "z \<notin> Wellfounded.acc RPrel"
    using zBad unfolding Bad_def by auto
  obtain v b where zeq: "z = DB v b" by (cases z) auto
  have otb: "isOT_BT b" using zot zeq by simp
  have dfb: "dfree_BT b" using zdf zeq by simp
  have secb: "wfj_secT b"
  proof -
    obtain bs where beq: "b = Trm bs" by (cases b) auto
    have "\<forall>r \<in> set bs. r \<in> Wellfounded.acc RPrel"
    proof
      fix r assume rin: "r \<in> set bs"
      have otr: "isOT_BP r" using otb beq rin by simp
      have dfr: "dfree_BP r" using dfb beq rin by simp
      have szr: "wfs_szP r < wfs_szT b" using wfs_szP_mem_lt[OF rin] beq by simp
      have szb: "wfs_szP z = Suc (wfs_szT b)" using zeq by simp
      have "wfs_szP r < wfs_szP z" using szr szb by linarith
      then have "(r, z) \<in> measure wfs_szP" by simp
      then have "r \<notin> Bad" using zmin by blast
      then show "r \<in> Wellfounded.acc RPrel"
        using otr dfr unfolding Bad_def by blast
    qed
    then show ?thesis using beq by simp
  qed
  have bacc: "b \<in> Wellfounded.acc RTrel"
    by (rule wfj_secT_tuple_acc[OF otb dfb secb])
  show ?thesis using zot zdf znacc bacc zeq by blast
qed

text \<open>Consequently the residual localizes to the head index: any minimal
  body-accessible counterexample sits STRICTLY ABOVE a lower-head
  counterexample.  With \<open>wfc_principal_acc_of_body\<close> (already proven: an
  \<open>OT\<close>+\<open>dfree\<close> principal with an \<open>RTrel\<close>-accessible body and ALL head-\<open>< v\<close>
  predecessors accessible is itself accessible), a witness whose head-\<open>< v\<close>
  segment were fully accessible would be accessible --- contradiction.  Hence
  the obstruction is NOT the body but the lower collapsing segment
  \<open>wfj_frag (v-1)\<close> (unbounded \<open>wfs_szP\<close> by \<open>wfj_frag0_lv_unbounded\<close>, so out of
  reach of size-minimality); this head-index descent is exactly the [Buc1]
  Lemma 2.2 transfinite recursion on \<open>v\<close>.\<close>

corollary wcl_lower_head_bad_exists:
  assumes bad: "\<not> (\<forall>p. isOT_BP p \<longrightarrow> dfree_BP p \<longrightarrow> p \<in> Wellfounded.acc RPrel)"
  shows "\<exists>v b. isOT_BP (DB v b) \<and> dfree_BP (DB v b)
               \<and> DB v b \<notin> Wellfounded.acc RPrel
               \<and> b \<in> Wellfounded.acc RTrel
               \<and> (\<exists>r. isOT_BP r \<and> dfree_BP r \<and> wfj_hd r < v
                      \<and> r \<notin> Wellfounded.acc RPrel)"
proof -
  obtain v b where otp: "isOT_BP (DB v b)" and dfp: "dfree_BP (DB v b)"
    and nacc: "DB v b \<notin> Wellfounded.acc RPrel"
    and bacc: "b \<in> Wellfounded.acc RTrel"
    using wcl_min_bad_body_acc[OF bad] by blast
  have "\<exists>r. isOT_BP r \<and> dfree_BP r \<and> wfj_hd r < v \<and> r \<notin> Wellfounded.acc RPrel"
  proof (rule ccontr)
    assume "\<not> (\<exists>r. isOT_BP r \<and> dfree_BP r \<and> wfj_hd r < v
                   \<and> r \<notin> Wellfounded.acc RPrel)"
    then have hlt: "\<And>r. isOT_BP r \<Longrightarrow> dfree_BP r \<Longrightarrow> wfj_hd r < v
                        \<Longrightarrow> r \<in> Wellfounded.acc RPrel" by blast
    have "DB v b \<in> Wellfounded.acc RPrel"
      by (rule wfc_principal_acc_of_body[OF hlt bacc otp dfp])
    then show False using nacc by blast
  qed
  then show ?thesis using otp dfp nacc bacc by blast
qed

(* ===================================================================== *)
(* ===== r64: wcl_ continuation --- the LEXICOGRAPHIC (head, size)     ===== *)
(* ===== minimal bad witness, and the sharp UPPER-COMPONENT residual.  ===== *)
(* =====                                                               ===== *)
(* ===== r63 exposed two INCOMPATIBLE minimality framings:             ===== *)
(* =====   * SIZE-minimal bad (wcl_min_bad_body_acc): body is acc, but  ===== *)
(* =====     head-<v predecessors may be LARGER (out of reach), so the ===== *)
(* =====     wfc_principal_acc_of_body hlt-premise is NOT discharged.   ===== *)
(* =====   * HEAD-minimal bad: hlt IS discharged, but the body need not ===== *)
(* =====     be acc.                                                    ===== *)
(* ===== The resolution is the LEXICOGRAPHIC minimum on (head, size)   ===== *)
(* ===== with HEAD dominating: it discharges BOTH the head-<n branch   ===== *)
(* ===== (i, by head-minimality) AND the head-=n smaller-body branch   ===== *)
(* ===== (ii, by size-minimality within the level).  The SOLE residual ===== *)
(* ===== is then the head->n ("upper", shielded/collapsed) components  ===== *)
(* ===== of the minimal-bad body --- exactly the psi-collapse content  ===== *)
(* ===== of [Buc1] Lemma 2.2.  This is a genuine sharpening: the entire ===== *)
(* ===== head-<= n segment of the minimal-bad body is now free.        ===== *)
(* ===================================================================== *)

subsection \<open>(D) The lexicographic \<open>(head, size)\<close>-minimal bad witness\<close>

text \<open>If some \<open>OT\<close>+\<open>dfree\<close> principal is not \<open>RPrel\<close>-accessible, then a
  \<open>(wfj_hd, wfs_szP)\<close>-lexicographically-minimal such principal \<open>D\<^bsub>n\<^esub> b\<close> has:
  (i) EVERY strictly-lower-head \<open>OT\<close>+\<open>dfree\<close> principal accessible (head
  minimality), and (ii) EVERY equal-head strictly-smaller principal accessible
  (size minimality at the level).  The lexicographic wellorder is the standard
  \<open>less_than <*lex*> less_than\<close> pulled back along \<open>g p = (hd\<^sub>nat p, wfs_szP p)\<close>.\<close>

lemma wcl_min_bad_lex:
  assumes bad: "\<not> (\<forall>p. isOT_BP p \<longrightarrow> dfree_BP p \<longrightarrow> p \<in> Wellfounded.acc RPrel)"
  shows "\<exists>n b. isOT_BP (DB (enat n) b) \<and> dfree_BP (DB (enat n) b)
             \<and> DB (enat n) b \<notin> Wellfounded.acc RPrel
             \<and> (\<forall>r. isOT_BP r \<longrightarrow> dfree_BP r \<longrightarrow> wfj_hd r < enat n
                    \<longrightarrow> r \<in> Wellfounded.acc RPrel)
             \<and> (\<forall>c. isOT_BP c \<longrightarrow> dfree_BP c \<longrightarrow> wfj_hd c = enat n
                    \<longrightarrow> wfs_szP c < wfs_szP (DB (enat n) b)
                    \<longrightarrow> c \<in> Wellfounded.acc RPrel)"
proof -
  define Bad where
    "Bad = {p. isOT_BP p \<and> dfree_BP p \<and> p \<notin> Wellfounded.acc RPrel}"
  define g :: "BP \<Rightarrow> nat \<times> nat" where
    "g = (\<lambda>p. (case wfj_hd p of enat k \<Rightarrow> k | \<infinity> \<Rightarrow> 0, wfs_szP p))"
  from bad obtain p0 where p0Bad: "p0 \<in> Bad" unfolding Bad_def by blast
  have wfR: "wf (inv_image (less_than <*lex*> less_than) g)"
    by (rule wf_inv_image[OF wf_lex_prod[OF wf_less_than wf_less_than]])
  have "\<exists>z\<in>Bad. \<forall>y. (y, z) \<in> inv_image (less_than <*lex*> less_than) g
                       \<longrightarrow> y \<notin> Bad"
    using wfR[unfolded wf_eq_minimal] p0Bad by blast
  then obtain z where zBad: "z \<in> Bad"
    and zmin: "\<forall>y. (y, z) \<in> inv_image (less_than <*lex*> less_than) g \<longrightarrow> y \<notin> Bad"
    by blast
  have zot: "isOT_BP z" and zdf: "dfree_BP z"
    and znacc: "z \<notin> Wellfounded.acc RPrel"
    using zBad unfolding Bad_def by auto
  obtain v b where zeq0: "z = DB v b" by (cases z) auto
  have "v \<noteq> \<infinity>" using zdf zeq0 by simp
  then obtain n where vn: "v = enat n" by (cases v) auto
  have zeq: "z = DB (enat n) b" using zeq0 vn by simp
  have gz: "g z = (n, wfs_szP z)" using zeq by (simp add: g_def)
  \<comment> \<open>(i) head minimality: every strictly-lower-head principal is accessible\<close>
  have i: "\<forall>r. isOT_BP r \<longrightarrow> dfree_BP r \<longrightarrow> wfj_hd r < enat n
                \<longrightarrow> r \<in> Wellfounded.acc RPrel"
  proof (intro allI impI)
    fix r assume otr: "isOT_BP r" and dfr: "dfree_BP r" and hlt: "wfj_hd r < enat n"
    show "r \<in> Wellfounded.acc RPrel"
    proof (rule ccontr)
      assume nacc: "r \<notin> Wellfounded.acc RPrel"
      then have rBad: "r \<in> Bad" using otr dfr unfolding Bad_def by blast
      obtain u w where req: "r = DB u w" by (cases r) auto
      have "u \<noteq> \<infinity>" using dfr req by simp
      then obtain m where um: "u = enat m" by (cases u) auto
      have hdr: "wfj_hd r = enat m" using req um by simp
      then have mn: "m < n" using hlt by simp
      have gr: "g r = (m, wfs_szP r)" using hdr by (simp add: g_def)
      have "(g r, g z) \<in> less_than <*lex*> less_than"
        using mn gr gz by (simp add: lex_prod_def)
      then have "(r, z) \<in> inv_image (less_than <*lex*> less_than) g"
        by (simp add: inv_image_def)
      then have "r \<notin> Bad" using zmin by blast
      then show False using rBad by blast
    qed
  qed
  \<comment> \<open>(ii) size minimality within the level \<open>n\<close>\<close>
  have ii: "\<forall>c. isOT_BP c \<longrightarrow> dfree_BP c \<longrightarrow> wfj_hd c = enat n
                 \<longrightarrow> wfs_szP c < wfs_szP (DB (enat n) b)
                 \<longrightarrow> c \<in> Wellfounded.acc RPrel"
  proof (intro allI impI)
    fix c assume otc: "isOT_BP c" and dfc: "dfree_BP c"
      and hdc: "wfj_hd c = enat n" and szc: "wfs_szP c < wfs_szP (DB (enat n) b)"
    show "c \<in> Wellfounded.acc RPrel"
    proof (rule ccontr)
      assume nacc: "c \<notin> Wellfounded.acc RPrel"
      then have cBad: "c \<in> Bad" using otc dfc unfolding Bad_def by blast
      have gc: "g c = (n, wfs_szP c)" using hdc by (simp add: g_def)
      have szc': "wfs_szP c < wfs_szP z" using szc zeq by simp
      have "(g c, g z) \<in> less_than <*lex*> less_than"
        using szc' gc gz by (simp add: lex_prod_def)
      then have "(c, z) \<in> inv_image (less_than <*lex*> less_than) g"
        by (simp add: inv_image_def)
      then have "c \<notin> Bad" using zmin by blast
      then show False using cBad by blast
    qed
  qed
  have zot': "isOT_BP (DB (enat n) b)" using zot zeq by simp
  have zdf': "dfree_BP (DB (enat n) b)" using zdf zeq by simp
  have znacc': "DB (enat n) b \<notin> Wellfounded.acc RPrel" using znacc zeq by simp
  show ?thesis using zot' zdf' znacc' i ii by blast
qed

theorem wcl_wf_of_upper:
  assumes U: "wcl_upper"
  shows "wf RPrel"
proof (rule ccontr)
  assume nwf: "\<not> wf RPrel"
  have bad: "\<not> (\<forall>p. isOT_BP p \<longrightarrow> dfree_BP p \<longrightarrow> p \<in> Wellfounded.acc RPrel)"
  proof
    assume A: "\<forall>p. isOT_BP p \<longrightarrow> dfree_BP p \<longrightarrow> p \<in> Wellfounded.acc RPrel"
    have "\<forall>p. p \<in> Wellfounded.acc RPrel"
    proof
      fix p :: BP
      show "p \<in> Wellfounded.acc RPrel"
      proof (cases "isOT_BP p \<and> dfree_BP p")
        case True thus ?thesis using A by blast
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
    then have "wf RPrel" using wfs_wf_iff_all_acc by blast
    with nwf show False by blast
  qed
  obtain n b where otp: "isOT_BP (DB (enat n) b)" and dfp: "dfree_BP (DB (enat n) b)"
    and nacc: "DB (enat n) b \<notin> Wellfounded.acc RPrel"
    and i: "\<forall>r. isOT_BP r \<longrightarrow> dfree_BP r \<longrightarrow> wfj_hd r < enat n
                 \<longrightarrow> r \<in> Wellfounded.acc RPrel"
    and ii: "\<forall>c. isOT_BP c \<longrightarrow> dfree_BP c \<longrightarrow> wfj_hd c = enat n
                  \<longrightarrow> wfs_szP c < wfs_szP (DB (enat n) b)
                  \<longrightarrow> c \<in> Wellfounded.acc RPrel"
    using wcl_min_bad_lex[OF bad] by blast
  have otb: "isOT_BT b" using otp by simp
  have dfb: "dfree_BT b" using dfp by simp
  obtain bs where beq: "b = Trm bs" by (cases b) auto
  \<comment> \<open>upper components (head \<open>> n\<close>) accessible by the residual\<close>
  have upper: "\<forall>w c. DB w c \<in> set (untrm b) \<longrightarrow> enat n < w
                     \<longrightarrow> DB w c \<in> Wellfounded.acc RPrel"
    using U[unfolded wcl_upper_def] otp dfp nacc i ii by blast
  \<comment> \<open>ALL body components accessible, by trichotomy on the component head\<close>
  have allcomp: "\<forall>r \<in> set (untrm b). r \<in> Wellfounded.acc RPrel"
  proof
    fix r assume rin: "r \<in> set (untrm b)"
    have rin': "r \<in> set bs" using rin beq by simp
    have otr: "isOT_BP r" using otb beq rin' by simp
    have dfr: "dfree_BP r" using dfb beq rin' by simp
    obtain w c where req: "r = DB w c" by (cases r) auto
    have rmem: "DB w c \<in> set (untrm b)" using rin req by simp
    show "r \<in> Wellfounded.acc RPrel"
    proof (cases w "enat n" rule: linorder_cases)
      case less
      have "wfj_hd r < enat n" using req less by simp
      then show ?thesis using i otr dfr by blast
    next
      case equal
      have hd_r: "wfj_hd r = enat n" using req equal by simp
      have "wfs_szP r < wfs_szT (Trm bs)" using wfs_szP_mem_lt[OF rin'] .
      then have "wfs_szP r < wfs_szT b" using beq by simp
      then have szr: "wfs_szP r < wfs_szP (DB (enat n) b)" by simp
      show ?thesis using ii otr dfr hd_r szr by blast
    next
      case greater
      show ?thesis using upper rmem greater req by blast
    qed
  qed
  have bacc: "b \<in> Wellfounded.acc RTrel"
    by (rule wfj_tuple_acc[OF otb dfb allcomp])
  have hlt: "\<And>r. isOT_BP r \<Longrightarrow> dfree_BP r \<Longrightarrow> wfj_hd r < enat n
                 \<Longrightarrow> r \<in> Wellfounded.acc RPrel"
    using i by blast
  have "DB (enat n) b \<in> Wellfounded.acc RPrel"
    by (rule wfc_principal_acc_of_body[OF hlt bacc otp dfp])
  then show False using nacc by blast
qed

text \<open>Converse sanity: \<open>wcl_upper\<close> is EXACTLY theorem-strength (no overshoot).
  Under \<open>wf RPrel\<close> every principal is accessible, so the residual holds
  vacuously (its \<open>D\<^bsub>n\<^esub> b \<notin> acc\<close> premise is never met).\<close>

lemma wcl_upper_of_wf:
  assumes "wf RPrel" shows "wcl_upper"
proof -
  have "\<forall>p. p \<in> Wellfounded.acc RPrel" using assms wfs_wf_iff_all_acc by blast
  then show ?thesis unfolding wcl_upper_def by blast
qed

theorem wcl_upper_iff_wf: "wcl_upper \<longleftrightarrow> wf RPrel"
  using wcl_wf_of_upper wcl_upper_of_wf by blast

corollary wcl_collapse_of_upper:
  assumes "wcl_upper" shows "wds_collapse"
  by (rule wds_collapse_of_wf[OF wcl_wf_of_upper[OF assms]])

corollary wcl_buc1_2_2_of_upper:
  \<comment> \<open>[Buc1] Lemma 2.2 in original shape, modulo the single \<open>wcl_upper\<close> residual.\<close>
  assumes "wcl_upper"
  shows "wf {(a, b). a \<in> OT_B \<and> b \<in> OT_B \<and> lessBT a b}"
  using wds_buc1_2_2_of_collapse[OF wcl_collapse_of_upper[OF assms]] .

(* ===================================================================== *)
(* ===== r65 (OPUS 4.8): the tower STEP and the intrinsic-globality   ===== *)
(* ===== obstruction of wcl_upper (prefixes wtw_ / wcl_).             ===== *)
(* =====                                                               ===== *)
(* ===== r64 pinned [Buc1] 2.2 to the single residual wcl_upper: for   ===== *)
(* ===== the lex-(head,size)-minimal bad principal D_n b, the head->n  ===== *)
(* ===== body components are RPrel-accessible.  This round makes the   ===== *)
(* ===== tower STEP explicit and unconditional (wtw_core_step: the     ===== *)
(* ===== level-u principal is accessible once head-<u principals AND   ===== *)
(* ===== the head->=u components are), and CERTIFIES why the residual  ===== *)
(* ===== cannot be discharged level-locally: for a bad witness, EVERY  ===== *)
(* ===== head->n component has the bad principal itself as a strict    ===== *)
(* ===== RPrel-predecessor (wcl_high_comp_bad_pred), so it is provably ===== *)
(* ===== NON-accessible (wcl_high_comp_not_acc) — the head->n content  ===== *)
(* ===== is exactly the shielded material with no elementary handle.   ===== *)
(* ===================================================================== *)

subsection \<open>(F) r65: the unconditional tower STEP and the globality of \<open>wcl_upper\<close>\<close>

text \<open>\<^bold>\<open>The tower step (positive, unconditional).\<close>  This is the clean level-\<open>u\<close>
  successor of the head recursion, isolating the low part (below the head,
  supplied by the induction hypothesis of any head-recursion) from the high
  part (the \<open>\<ge> u\<close> components, the residual).  It says: a level-\<open>u\<close> \<open>OT\<close>+\<open>dfree\<close>
  principal is \<open>RPrel\<close>-accessible as soon as (a) every strictly-lower-head
  \<open>OT\<close>+\<open>dfree\<close> principal is accessible (the tower below), and (b) every direct
  body component of head \<open>\<ge> u\<close> is accessible (the shielded upper part).  The
  low components (head \<open>< u\<close>) are handled by (a), so the body is
  \<open>RTrel\<close>-accessible (\<open>wfj_tuple_acc\<close>) and the principal lifts by
  \<open>wfc_principal_acc_of_body\<close>.  This packages exactly the split that
  \<open>wcl_wf_of_upper\<close> performs inline, as a reusable named brick for the tower.\<close>

lemma wtw_core_step:
  assumes hlt: "\<And>r. isOT_BP r \<Longrightarrow> dfree_BP r \<Longrightarrow> wfj_hd r < enat u
                    \<Longrightarrow> r \<in> Wellfounded.acc RPrel"
    and hge: "\<And>w c. DB w c \<in> set (untrm b) \<Longrightarrow> enat u \<le> w
                     \<Longrightarrow> DB w c \<in> Wellfounded.acc RPrel"
    and ot: "isOT_BP (DB (enat u) b)" and df: "dfree_BP (DB (enat u) b)"
  shows "DB (enat u) b \<in> Wellfounded.acc RPrel"
proof -
  have otb: "isOT_BT b" using ot by simp
  have dfb: "dfree_BT b" using df by simp
  obtain bs where beq: "b = Trm bs" by (cases b) auto
  have allc: "\<forall>r \<in> set (untrm b). r \<in> Wellfounded.acc RPrel"
  proof
    fix r assume rin: "r \<in> set (untrm b)"
    have rin': "r \<in> set bs" using rin beq by simp
    have otr: "isOT_BP r" using otb beq rin' by simp
    have dfr: "dfree_BP r" using dfb beq rin' by simp
    obtain w c where req: "r = DB w c" by (cases r) auto
    show "r \<in> Wellfounded.acc RPrel"
    proof (cases "w < enat u")
      case True
      have "wfj_hd r < enat u" using req True by simp
      then show ?thesis using hlt otr dfr by blast
    next
      case False
      have geu: "enat u \<le> w" using False by (simp add: not_less)
      have "DB w c \<in> set (untrm b)" using rin req by simp
      then have "DB w c \<in> Wellfounded.acc RPrel" using hge geu by blast
      then show ?thesis using req by simp
    qed
  qed
  have bacc: "b \<in> Wellfounded.acc RTrel" by (rule wfj_tuple_acc[OF otb dfb allc])
  show ?thesis by (rule wfc_principal_acc_of_body[OF hlt bacc ot df])
qed

text \<open>\<^bold>\<open>The intrinsic-globality obstruction.\<close>  The head-\<open>> n\<close> components of the
  lex-minimal bad principal \<open>D\<^bsub>n\<^esub> b\<close> are NOT merely "hard to reach": for a
  \<open>bad\<close> (non-accessible) witness they are provably NON-accessible.  The reason is
  structural: \<open>D\<^bsub>n\<^esub> b\<close> is itself a strict \<open>RPrel\<close>-predecessor of every body
  component of head \<open>w > n\<close> (head \<open>n < w\<close> forces \<open>lessBP (D\<^bsub>n\<^esub> b) (D\<^bsub>w\<^esub> c)\<close>
  irrespective of the bodies).  Since accessibility is downward closed
  (\<open>acc_downward\<close>), a component with a non-accessible predecessor is itself
  non-accessible.  Hence \<open>wcl_upper\<close>'s conclusion "the head-\<open>> n\<close> components are
  accessible" is FALSE on any genuine bad witness carrying such a component:
  \<open>wcl_upper\<close> can only hold vacuously, i.e. it is equivalent to \<open>wf RPrel\<close> with
  no proper sub-instance — there is no monotone "partial" progress to be made on
  the residual itself.  Establishing accessibility of those components therefore
  requires first ruling out the bad witness globally, which is the whole theorem
  (\<open>wcl_upper_iff_wf\<close>).  This is the exact certificate that the distinguished-set
  impredicative construction (\<open>wds_collapse\<close>, existence of a distinguished set =
  theorem strength) is unavoidable, and that no head-\<open>< n\<close> / size descent closes
  the head-\<open>> n\<close> level.\<close>

lemma wcl_high_comp_bad_pred:
  assumes ot: "isOT_BP (DB (enat n) b)" and df: "dfree_BP (DB (enat n) b)"
    and comp: "DB w c \<in> set (untrm b)" and hn: "enat n < w"
  shows "(DB (enat n) b, DB w c) \<in> RPrel"
proof -
  have otb: "isOT_BT b" using ot by simp
  have dfb: "dfree_BT b" using df by simp
  obtain bs where beq: "b = Trm bs" by (cases b) auto
  have cin: "DB w c \<in> set bs" using comp beq by simp
  have "\<forall>p \<in> set bs. isOT_BP p" using otb beq by simp
  then have otc: "isOT_BP (DB w c)" using cin by blast
  have "\<forall>p \<in> set bs. dfree_BP p" using dfb beq by simp
  then have dfc: "dfree_BP (DB w c)" using cin by blast
  have "lessBP (DB (enat n) b) (DB w c)" using hn by simp
  then show ?thesis using ot df otc dfc by (simp add: RPrel_def)
qed

corollary wcl_high_comp_not_acc:
  assumes ot: "isOT_BP (DB (enat n) b)" and df: "dfree_BP (DB (enat n) b)"
    and comp: "DB w c \<in> set (untrm b)" and hn: "enat n < w"
    and nacc: "DB (enat n) b \<notin> Wellfounded.acc RPrel"
  shows "DB w c \<notin> Wellfounded.acc RPrel"
proof
  assume acc: "DB w c \<in> Wellfounded.acc RPrel"
  have "DB (enat n) b \<in> Wellfounded.acc RPrel"
    by (rule acc_downward[OF acc wcl_high_comp_bad_pred[OF ot df comp hn]])
  then show False using nacc by blast
qed

text \<open>\<^bold>\<open>Consequently\<close>: on the lex-minimal bad witness \<open>D\<^bsub>n\<^esub> b\<close> (from
  \<open>wcl_min_bad_lex\<close>), the \<open>ONLY\<close> way \<open>wcl_upper\<close> can fail to be immediately
  self-contradictory is that \<open>b\<close> carries \<open>NO\<close> head-\<open>> n\<close> component at all --- in
  which case \<open>wcl_wf_of_upper\<close> already closes via clauses (i)/(ii) with no upper
  content.  If a head-\<open>> n\<close> component exists, \<open>wcl_high_comp_not_acc\<close> shows it is
  non-accessible, so \<open>wcl_upper\<close>'s demand is unmeetable without first refuting the
  witness.  This gives the sharpened obstruction and a strictly-shorter route
  through \<open>wcl_wf_of_upper\<close>: under the residual, either there is no upper content
  (finish by (i)/(ii)) or the residual is self-defeating on the witness.\<close>

lemma wcl_wf_of_upper_via_step:
  \<comment> \<open>Re-derivation of \<open>wf RPrel\<close> from \<open>wcl_upper\<close> through the named tower step
      \<open>wtw_core_step\<close>, making the low/upper split explicit.\<close>
  assumes U: "wcl_upper"
  shows "wf RPrel"
proof (rule ccontr)
  assume nwf: "\<not> wf RPrel"
  have bad: "\<not> (\<forall>p. isOT_BP p \<longrightarrow> dfree_BP p \<longrightarrow> p \<in> Wellfounded.acc RPrel)"
  proof
    assume A: "\<forall>p. isOT_BP p \<longrightarrow> dfree_BP p \<longrightarrow> p \<in> Wellfounded.acc RPrel"
    have "\<forall>p. p \<in> Wellfounded.acc RPrel"
    proof
      fix p :: BP
      show "p \<in> Wellfounded.acc RPrel"
      proof (cases "isOT_BP p \<and> dfree_BP p")
        case True thus ?thesis using A by blast
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
    then have "wf RPrel" using wfs_wf_iff_all_acc by blast
    with nwf show False by blast
  qed
  obtain n b where otp: "isOT_BP (DB (enat n) b)"
    and dfp: "dfree_BP (DB (enat n) b)"
    and nacc: "DB (enat n) b \<notin> Wellfounded.acc RPrel"
    and i: "\<forall>r. isOT_BP r \<longrightarrow> dfree_BP r \<longrightarrow> wfj_hd r < enat n
                 \<longrightarrow> r \<in> Wellfounded.acc RPrel"
    and ii: "\<forall>c. isOT_BP c \<longrightarrow> dfree_BP c \<longrightarrow> wfj_hd c = enat n
                  \<longrightarrow> wfs_szP c < wfs_szP (DB (enat n) b)
                  \<longrightarrow> c \<in> Wellfounded.acc RPrel"
    using wcl_min_bad_lex[OF bad] by blast
  have otb: "isOT_BT b" using otp by simp
  have dfb: "dfree_BT b" using dfp by simp
  obtain bs where beq: "b = Trm bs" by (cases b) auto
  \<comment> \<open>the residual supplies the head-\<open>> n\<close> (\<open>= \<ge> Suc n\<close>) components\<close>
  have upper: "\<forall>w c. DB w c \<in> set (untrm b) \<longrightarrow> enat n < w
                     \<longrightarrow> DB w c \<in> Wellfounded.acc RPrel"
    using U[unfolded wcl_upper_def] otp dfp nacc i ii by blast
  have hlt: "\<And>r. isOT_BP r \<Longrightarrow> dfree_BP r \<Longrightarrow> wfj_hd r < enat n
                 \<Longrightarrow> r \<in> Wellfounded.acc RPrel"
    using i by blast
  \<comment> \<open>the head-\<open>\<ge> n\<close> components: head \<open>= n\<close> by (ii) (proper subterms), head \<open>> n\<close> by the residual\<close>
  have hge: "\<And>w c. DB w c \<in> set (untrm b) \<Longrightarrow> enat n \<le> w
                    \<Longrightarrow> DB w c \<in> Wellfounded.acc RPrel"
  proof -
    fix w c assume rmem: "DB w c \<in> set (untrm b)" and geu: "enat n \<le> w"
    have rin': "DB w c \<in> set bs" using rmem beq by simp
    have "\<forall>p \<in> set bs. isOT_BP p" using otb beq by simp
    then have otr: "isOT_BP (DB w c)" using rin' by blast
    have "\<forall>p \<in> set bs. dfree_BP p" using dfb beq by simp
    then have dfr: "dfree_BP (DB w c)" using rin' by blast
    show "DB w c \<in> Wellfounded.acc RPrel"
    proof (cases "w = enat n")
      case True
      have hd_r: "wfj_hd (DB w c) = enat n" using True by simp
      have "wfs_szP (DB w c) < wfs_szT (Trm bs)"
        using wfs_szP_mem_lt[OF rin'] .
      then have "wfs_szP (DB w c) < wfs_szT b" using beq by simp
      then have szr: "wfs_szP (DB w c) < wfs_szP (DB (enat n) b)" by simp
      show ?thesis using ii otr dfr hd_r szr by blast
    next
      case False
      have "enat n < w" using geu False by simp
      then show ?thesis using upper rmem by blast
    qed
  qed
  have "DB (enat n) b \<in> Wellfounded.acc RPrel"
    by (rule wtw_core_step[OF hlt hge otp dfp])
  then show False using nacc by blast
qed


section \<open>Additional relocated campaign annotations\<close>

text \<open>\<^bold>\<open>Status after r64.\<close>  The last external citation [Buc1] Lemma 2.2 is now
  pinned to the SINGLE sharpest residual \<open>wcl_upper\<close> (\<open>wcl_upper_iff_wf\<close>: exactly
  theorem-strength).  Compared with r63's \<open>wds_collapse\<close>, the entire head-\<open>\<le> n\<close>
  segment of the minimal-bad body is discharged unconditionally by the
  lexicographic \<open>(head, size)\<close> minimality (\<open>wcl_min_bad_lex\<close>):

  \<^item> head-\<open>< n\<close> components: accessible by head-minimality (clause (i));
  \<^item> head-\<open>= n\<close> components: accessible by size-minimality within the level,
    since they are proper subterms of the body (clause (ii));
  \<^item> head-\<open>> n\<close> components (the \<open>\<psi>\<^bsub>n\<^esub>\<close>-shielded / collapsed coefficients): the
    SOLE remaining obligation \<open>wcl_upper\<close>.

  \<^bold>\<open>Exact obstruction.\<close>  \<open>wcl_upper\<close> asks that the head-\<open>> n\<close> body components of
  the minimal-bad principal be \<open>RPrel\<close>-accessible.  These are exactly Buchholz's
  collapsed coefficients \<open>\<psi>\<^bsub>w\<^esub>(\<dots>)\<close>, \<open>w > n\<close>, appearing under a \<open>\<psi>\<^bsub>n\<^esub>\<close>: their
  accessibility is NOT reachable by any subterm/size descent (they sit at a
  larger head) nor by head-minimality (their head is \<open>> n\<close>, not \<open>< n\<close>).  Closing
  them is the genuine transfinite content --- the [Buc1] distinguished-set /
  fundamental-sequence collapse (\<open>wds_distinguished\<close> + [Buc1] \<open>\<section>\<close>5, cf.
  \<open>wcl_accfrag_distinguished_of_core\<close>, which currently still assumes the collapse
  core).  Estimated 2--4 rounds if the distinguished-set tower induction on \<open>n\<close>
  can be made to feed \<open>wcl_upper\<close> level by level; genuinely external otherwise.\<close>


text \<open>\<^bold>\<open>Status after r65.\<close>  The residual for [Buc1] Lemma 2.2 is unchanged
  (\<open>wcl_upper\<close>, \<open>wcl_upper_iff_wf\<close>: exactly theorem-strength).  What r65 adds is
  the precise \<^emph>\<open>shape\<close> of the obstruction, as green bricks:

  \<^item> \<open>wtw_core_step\<close> — the unconditional level-\<open>u\<close> tower step (low part = the
    head-\<open>< u\<close> IH, upper part = the head-\<open>\<ge> u\<close> components), and
    \<open>wcl_wf_of_upper_via_step\<close> re-derives \<open>wf RPrel\<close> from \<open>wcl_upper\<close> through it,
    exposing the low/upper split as a reusable named brick for a future tower.
  \<^item> \<open>wcl_high_comp_bad_pred\<close> / \<open>wcl_high_comp_not_acc\<close> — the head-\<open>> n\<close>
    components of a bad witness are provably NON-accessible (the bad principal is
    their \<open>RPrel\<close>-predecessor).  So \<open>wcl_upper\<close> admits no monotone partial
    progress: its conclusion is false on any genuine witness with upper content;
    it can hold only vacuously.

  \<^bold>\<open>Exact obstruction / next idea.\<close>  The head-\<open>> n\<close> level cannot be discharged by
  any subterm/size descent (its members are lex-\<open>larger\<close>, and non-accessible
  while the witness is bad) nor by the head recursion (head-\<open>< n\<close> has no base:
  \<open>wfj_frag0_lv_unbounded\<close>).  The sole path is the impredicative
  distinguished-set collapse \<open>wds_collapse\<close> (equivalently \<open>wcl_upper\<close>): its
  exhibit-move must construct a \<open>v\<close>-distinguished set on top of \<open>wds_Mset v\<close>
  containing the target \<open>D\<^bsub>v\<^esub> c\<close>, whose only non-cheap clauses are (i) the
  \<open>RPrel\<close>-downward closure of the initial segment \<open>{q \<in> wfj_frag v. q \<le>\<^sub>P D\<^bsub>v\<^esub> c}\<close>
  (a transfinite induction along the wellfounded \<open>acc RPrel\<close>-restriction to
  \<open>wds_Mset v\<close>, using the premise that \<open>c\<close>'s \<open>G\<^sub>v\<close>-trace coefficients already sit in
  the tower), and (ii) its \<open>G\<close>-progressiveness.  The load-bearing missing fact is
  the \<^emph>\<open>existence of one \<open>v\<close>-distinguished set\<close> (the D1 witness for
  \<open>wds_Mset_distinguished\<close>) — itself of theorem strength (\<open>wfj_frag0_lv_unbounded\<close>
  forces it to contain a hereditarily-\<open>G\<close>-low unbounded-level family).  This is
  the genuine [Buc1] \<open>\<section>\<close>5 fundamental-sequence content and remains external-grade:
  a full formalization of the exhibit-move transfinite induction is estimated at
  \<open>\<ge> 5\<close> dedicated rounds (or importing an external well-foundedness of the
  Buchholz \<open>\<psi>\<close>-collapse).\<close>


end
