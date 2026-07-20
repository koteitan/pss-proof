theory M_8_7_Wds_Distinguished_Sets
  imports M_8_7_Wfc_Component_Jumps
begin

text \<open>Relocated proof material.  The declarations retain their original source order,
  and every relocated annotation is preserved below.  This theory is machine-checked
  outside the termination build tree.\<close>

lemma wds_hullT_iff: "t \<in> wds_hullT X \<longleftrightarrow> (\<forall>r \<in> set (untrm t). r \<in> X)"
  by (simp add: wds_hullT_def)

lemma wds_finite_GBT: "\<forall>u. finite (GBT u t)"
  and wds_finite_GBP: "\<forall>u. finite (GBP u q)"
proof (induction t and q rule: wfs_lvT_wfs_lvP.induct)
  case (1 ps)
  show ?case
  proof (intro allI)
    fix u :: enat
    have "finite (\<Union>p \<in> set ps. GBP u p)"
    proof (rule finite_UN_I)
      show "finite (set ps)" by simp
    next
      fix p assume pin: "p \<in> set ps"
      show "finite (GBP u p)" using "1.IH"[OF pin] by blast
    qed
    then show "finite (GBT u (Trm ps))" by simp
  qed
next
  case (2 v b)
  show ?case
  proof (intro allI)
    fix u :: enat
    have fb: "finite (GBT u b)" using "2.IH" by blast
    show "finite (GBP u (DB v b))" by (simp add: fb)
  qed
qed

lemma wds_distD_frag: "wds_distinguished v X \<Longrightarrow> X \<subseteq> wfj_frag v"
  unfolding wds_distinguished_def by blast

lemma wds_distD_down:
  "wds_distinguished v X \<Longrightarrow> p \<in> X \<Longrightarrow> (q, p) \<in> RPrel \<Longrightarrow> q \<in> X"
  unfolding wds_distinguished_def by blast

lemma wds_distD_acc:
  "wds_distinguished v X \<Longrightarrow> p \<in> X \<Longrightarrow> p \<in> Wellfounded.acc (Restr RPrel X)"
  unfolding wds_distinguished_def by blast

lemma wds_distD_prog:
  assumes "wds_distinguished v X" and "u \<le> v"
    and "isOT_BP (DB (enat u) c)" and "dfree_BP (DB (enat u) c)"
    and "\<forall>x \<in> GBT (enat u) c. x \<in> wds_hullT X"
  shows "DB (enat u) c \<in> X"
  using assms unfolding wds_distinguished_def by blast

lemma wds_distI:
  assumes "X \<subseteq> wfj_frag v"
    and "\<And>p q. p \<in> X \<Longrightarrow> (q, p) \<in> RPrel \<Longrightarrow> q \<in> X"
    and "\<And>p. p \<in> X \<Longrightarrow> p \<in> Wellfounded.acc (Restr RPrel X)"
    and "\<And>u c. u \<le> v \<Longrightarrow> isOT_BP (DB (enat u) c) \<Longrightarrow> dfree_BP (DB (enat u) c) \<Longrightarrow>
           (\<forall>x \<in> GBT (enat u) c. x \<in> wds_hullT X) \<Longrightarrow> DB (enat u) c \<in> X"
  shows "wds_distinguished v X"
  unfolding wds_distinguished_def using assms by blast

text \<open>The acc bridge: on a downward-closed set, relative accessibility is
  genuine accessibility.  (Small hand-rolled inductions; the hang catalog
  forbids \<open>blast\<close> saturation through \<open>acc\<close>.)\<close>

lemma wds_acc_lift_aux:
  assumes dc: "\<forall>r s. r \<in> X \<longrightarrow> (s, r) \<in> RPrel \<longrightarrow> s \<in> X"
    and ta: "t \<in> Wellfounded.acc (Restr RPrel X)"
  shows "t \<in> X \<longrightarrow> t \<in> Wellfounded.acc RPrel"
  using ta
proof (induction rule: acc.induct)
  case (accI x)
  show ?case
  proof (intro impI)
    assume xX: "x \<in> X"
    show "x \<in> Wellfounded.acc RPrel"
    proof (rule acc.intros)
      fix s assume sR: "(s, x) \<in> RPrel"
      have sX: "s \<in> X" using dc xX sR by blast
      have "(s, x) \<in> Restr RPrel X" using sR sX xX by blast
      then show "s \<in> Wellfounded.acc RPrel" using accI.IH sX by blast
    qed
  qed
qed

lemma wds_acc_lift:
  assumes d: "wds_distinguished v X" and pX: "p \<in> X"
  shows "p \<in> Wellfounded.acc RPrel"
proof -
  have dc: "\<forall>r s. r \<in> X \<longrightarrow> (s, r) \<in> RPrel \<longrightarrow> s \<in> X"
    using wds_distD_down[OF d] by blast
  have "p \<in> Wellfounded.acc (Restr RPrel X)" using wds_distD_acc[OF d pX] .
  then show ?thesis using wds_acc_lift_aux[OF dc] pX by blast
qed

subsection \<open>(3) Vergleichbarkeit: distinguished sets form a chain — from
  linearity (Lemma 2.1) and downward closure, even ACROSS levels\<close>

lemma wds_dist_comparable:
  assumes X: "wds_distinguished v X" and Y: "wds_distinguished w Y"
  shows "X \<subseteq> Y \<or> Y \<subseteq> X"
proof (rule ccontr)
  assume nc: "\<not> (X \<subseteq> Y \<or> Y \<subseteq> X)"
  then obtain p where pX: "p \<in> X" and pY: "p \<notin> Y" by blast
  obtain q where qY: "q \<in> Y" and qX: "q \<notin> X" using nc by blast
  have pf: "p \<in> wfj_frag v" using wds_distD_frag[OF X] pX by blast
  have qf: "q \<in> wfj_frag w" using wds_distD_frag[OF Y] qY by blast
  have pot: "isOT_BP p" using pf by (simp add: wfj_frag_def)
  have pdf: "dfree_BP p" using pf by (simp add: wfj_frag_def)
  have qot: "isOT_BP q" using qf by (simp add: wfj_frag_def)
  have qdf: "dfree_BP q" using qf by (simp add: wfj_frag_def)
  have "lessBP p q \<or> p = q \<or> lessBP q p" by (rule wfs_lessBP_total)
  then show False
  proof (elim disjE)
    assume "lessBP p q"
    then have "(p, q) \<in> RPrel" using pot pdf qot qdf by (simp add: RPrel_def)
    then have "p \<in> Y" using wds_distD_down[OF Y qY] by blast
    then show False using pY by blast
  next
    assume "p = q"
    then show False using pY qY by blast
  next
    assume "lessBP q p"
    then have "(q, p) \<in> RPrel" using pot pdf qot qdf by (simp add: RPrel_def)
    then have "q \<in> X" using wds_distD_down[OF X pX] by blast
    then show False using qX by blast
  qed
qed

lemma wds_Mset_upper: "wds_distinguished v X \<Longrightarrow> X \<subseteq> wds_Mset v"
  unfolding wds_Mset_def by blast

lemma wds_Mset_ex: "p \<in> wds_Mset v \<Longrightarrow> \<exists>X. wds_distinguished v X \<and> p \<in> X"
  unfolding wds_Mset_def by blast

lemma wds_Mset_frag: "wds_Mset v \<subseteq> wfj_frag v"
proof
  fix p assume "p \<in> wds_Mset v"
  then obtain X where "wds_distinguished v X" and "p \<in> X" using wds_Mset_ex by blast
  then show "p \<in> wfj_frag v" using wds_distD_frag by blast
qed

lemma wds_Mset_downclosed:
  assumes "p \<in> wds_Mset v" and "(q, p) \<in> RPrel"
  shows "q \<in> wds_Mset v"
proof -
  obtain X where dX: "wds_distinguished v X" and pX: "p \<in> X"
    using wds_Mset_ex[OF assms(1)] by blast
  have "q \<in> X" using wds_distD_down[OF dX pX assms(2)] .
  then show ?thesis using wds_Mset_upper[OF dX] by blast
qed

lemma wds_Mset_subset_acc: "wds_Mset v \<subseteq> Wellfounded.acc RPrel"
proof
  fix p assume "p \<in> wds_Mset v"
  then obtain X where "wds_distinguished v X" and "p \<in> X" using wds_Mset_ex by blast
  then show "p \<in> Wellfounded.acc RPrel" using wds_acc_lift by blast
qed

lemma wds_Mset_relacc:
  assumes "p \<in> wds_Mset v"
  shows "p \<in> Wellfounded.acc (Restr RPrel (wds_Mset v))"
proof -
  have "p \<in> Wellfounded.acc RPrel" using wds_Mset_subset_acc assms by blast
  moreover have "Restr RPrel (wds_Mset v) \<subseteq> RPrel" by blast
  ultimately show ?thesis using acc_subset by blast
qed

subsection \<open>(5) D1: the union lemma — \<open>M\<^sub>v\<close> is itself \<open>v\<close>-distinguished\<close>

text \<open>Finitely many \<open>M\<^sub>v\<close>-elements always sit inside a SINGLE distinguished
  set (the chain structure from comparability); this is the engine that lets
  the union absorb the \<open>G\<close>-progressiveness clause.\<close>

lemma wds_dist_finite_cover:
  assumes W: "wds_distinguished v X0"
    and fin: "finite S" and SM: "S \<subseteq> wds_Mset v"
  shows "\<exists>X. wds_distinguished v X \<and> S \<subseteq> X"
proof -
  have "S \<subseteq> wds_Mset v \<longrightarrow> (\<exists>X. wds_distinguished v X \<and> S \<subseteq> X)"
    using fin
  proof (induction rule: finite_induct)
    case empty
    show ?case using W by blast
  next
    case (insert r F)
    show ?case
    proof (intro impI)
      assume sub: "insert r F \<subseteq> wds_Mset v"
      have "F \<subseteq> wds_Mset v" using sub by blast
      then obtain X1 where d1: "wds_distinguished v X1" and F1: "F \<subseteq> X1"
        using insert.IH by blast
      have "r \<in> wds_Mset v" using sub by blast
      then obtain X2 where d2: "wds_distinguished v X2" and r2: "r \<in> X2"
        using wds_Mset_ex by blast
      show "\<exists>X. wds_distinguished v X \<and> insert r F \<subseteq> X"
        using wds_dist_comparable[OF d1 d2] d1 d2 F1 r2 by blast
    qed
  qed
  then show ?thesis using SM by blast
qed

theorem wds_Mset_distinguished:
  assumes W: "wds_distinguished v X0"
  shows "wds_distinguished v (wds_Mset v)"
proof (rule wds_distI)
  show "wds_Mset v \<subseteq> wfj_frag v" by (rule wds_Mset_frag)
next
  fix p q assume "p \<in> wds_Mset v" and "(q, p) \<in> RPrel"
  then show "q \<in> wds_Mset v" by (rule wds_Mset_downclosed)
next
  fix p assume "p \<in> wds_Mset v"
  then show "p \<in> Wellfounded.acc (Restr RPrel (wds_Mset v))"
    by (rule wds_Mset_relacc)
next
  fix u c
  assume uv: "u \<le> v" and otq: "isOT_BP (DB (enat u) c)"
    and dfq: "dfree_BP (DB (enat u) c)"
    and cnt: "\<forall>x \<in> GBT (enat u) c. x \<in> wds_hullT (wds_Mset v)"
  define S where "S = (\<Union>x \<in> GBT (enat u) c. set (untrm x))"
  have finS: "finite S"
    unfolding S_def
  proof (rule finite_UN_I)
    show "finite (GBT (enat u) c)" using wds_finite_GBT by blast
  next
    fix x assume "x \<in> GBT (enat u) c"
    show "finite (set (untrm x))" by simp
  qed
  have SM: "S \<subseteq> wds_Mset v"
  proof
    fix r assume "r \<in> S"
    then obtain x where xG: "x \<in> GBT (enat u) c" and rin: "r \<in> set (untrm x)"
      unfolding S_def by blast
    have "x \<in> wds_hullT (wds_Mset v)" using cnt xG by blast
    then show "r \<in> wds_Mset v" using rin by (simp add: wds_hullT_iff)
  qed
  obtain X where dX: "wds_distinguished v X" and SX: "S \<subseteq> X"
    using wds_dist_finite_cover[OF W finS SM] by blast
  have cntX: "\<forall>x \<in> GBT (enat u) c. x \<in> wds_hullT X"
  proof
    fix x assume xG: "x \<in> GBT (enat u) c"
    have "set (untrm x) \<subseteq> S" unfolding S_def using xG by blast
    then show "x \<in> wds_hullT X" using SX by (auto simp add: wds_hullT_iff)
  qed
  have "DB (enat u) c \<in> X" using wds_distD_prog[OF dX uv otq dfq cntX] .
  then show "DB (enat u) c \<in> wds_Mset v" using wds_Mset_upper[OF dX] by blast
qed

subsection \<open>(7) The Hauptlemma: collapse \<open>\<Longrightarrow>\<close> every \<open>OT\<close>+\<open>dfree\<close> principal
  lies in \<open>M\<^bsub>head\<^esub>\<close> (size induction — the \<open>G\<close>-trace is strictly smaller)\<close>

lemma wds_hauptlemma_aux:
  assumes C: "wds_collapse"
  shows "\<forall>v c. wfs_szP (DB (enat v) c) \<le> n \<longrightarrow> isOT_BP (DB (enat v) c) \<longrightarrow>
             dfree_BP (DB (enat v) c) \<longrightarrow> DB (enat v) c \<in> wds_Mset v"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (intro allI impI)
    fix v c
    assume sz: "wfs_szP (DB (enat v) c) \<le> n"
      and ot: "isOT_BP (DB (enat v) c)" and df: "dfree_BP (DB (enat v) c)"
    have otc: "isOT_BT c" using ot by simp
    have dfc: "dfree_BT c" using df by simp
    have prem: "\<forall>x \<in> GBT (enat v) c. \<forall>r \<in> set (untrm x).
                  \<exists>m e. r = DB (enat m) e \<and> r \<in> wds_Mset m"
    proof (intro ballI)
      fix x r assume xG: "x \<in> GBT (enat v) c" and rin: "r \<in> set (untrm x)"
      have otx: "isOT_BT x" using wfj_G_OT_T otc xG by blast
      have dfx: "dfree_BT x" using wfj_G_df_T dfc xG by blast
      obtain rs where xeq: "x = Trm rs" by (cases x) auto
      have rin': "r \<in> set rs" using rin xeq by simp
      have otr: "isOT_BP r" using otx xeq rin' by auto
      have dfr: "dfree_BP r" using dfx xeq rin' by auto
      obtain s e where req: "r = DB s e" by (cases r) auto
      have "s \<noteq> \<infinity>" using dfr req by simp
      then obtain m where sm: "s = enat m" by (cases s) auto
      have req': "r = DB (enat m) e" using req sm by simp
      have "wfs_szP r \<le> sum_list (map wfs_szP rs)" using rin' by (rule wfs_szP_mem)
      then have "wfs_szP r < wfs_szT (Trm rs)" by (simp add: less_Suc_eq_le)
      then have szr: "wfs_szP r < wfs_szT x" using xeq by simp
      have szx: "wfs_szT x < wfs_szT c" using wfj_G_szT xG by blast
      have szc: "wfs_szT c < wfs_szP (DB (enat v) c)" by simp
      have szrn: "wfs_szP r < n" using szr szx szc sz by linarith
      have sze: "wfs_szP (DB (enat m) e) \<le> wfs_szP r" using req' by simp
      have otr': "isOT_BP (DB (enat m) e)" using otr req' by simp
      have dfr': "dfree_BP (DB (enat m) e)" using dfr req' by simp
      have "DB (enat m) e \<in> wds_Mset m"
        using less.IH[OF szrn] sze otr' dfr' by blast
      then show "\<exists>m e. r = DB (enat m) e \<and> r \<in> wds_Mset m" using req' by blast
    qed
    have inst: "isOT_BP (DB (enat v) c) \<longrightarrow> dfree_BP (DB (enat v) c) \<longrightarrow>
        (\<forall>x \<in> GBT (enat v) c. \<forall>r \<in> set (untrm x).
            \<exists>m e. r = DB (enat m) e \<and> r \<in> wds_Mset m)
        \<longrightarrow> DB (enat v) c \<in> wds_Mset v"
      using C unfolding wds_collapse_def by blast
    show "DB (enat v) c \<in> wds_Mset v" using inst ot df prem by blast
  qed
qed

theorem wds_hauptlemma:
  assumes C: "wds_collapse"
    and ot: "isOT_BP (DB (enat v) c)" and df: "dfree_BP (DB (enat v) c)"
  shows "DB (enat v) c \<in> wds_Mset v"
proof -
  have "wfs_szP (DB (enat v) c) \<le> wfs_szP (DB (enat v) c)" by simp
  then show ?thesis using wds_hauptlemma_aux[OF C] ot df by blast
qed

subsection \<open>(8) The chain: collapse \<open>\<Longrightarrow>\<close> \<open>wfc_pbody_acc\<close> \<open>\<Longrightarrow>\<close> [Buc1] 2.2\<close>

theorem wds_pbody_of_collapse:
  assumes C: "wds_collapse"
  shows "wfc_pbody_acc"
  unfolding wfc_pbody_acc_def
proof (intro allI impI)
  fix v b assume ot: "isOT_BP (DB v b)" and df: "dfree_BP (DB v b)"
  have otb: "isOT_BT b" using ot by simp
  have dfb: "dfree_BT b" using df by simp
  have comp: "\<forall>r \<in> set (untrm b). r \<in> Wellfounded.acc RPrel"
  proof
    fix r assume rin: "r \<in> set (untrm b)"
    obtain bs where beq: "b = Trm bs" by (cases b) auto
    have rin': "r \<in> set bs" using rin beq by simp
    have otr: "isOT_BP r" using otb beq rin' by auto
    have dfr: "dfree_BP r" using dfb beq rin' by auto
    obtain s e where req: "r = DB s e" by (cases r) auto
    have "s \<noteq> \<infinity>" using dfr req by simp
    then obtain m where sm: "s = enat m" by (cases s) auto
    have req': "r = DB (enat m) e" using req sm by simp
    have otr': "isOT_BP (DB (enat m) e)" using otr req' by simp
    have dfr': "dfree_BP (DB (enat m) e)" using dfr req' by simp
    have "DB (enat m) e \<in> wds_Mset m" using wds_hauptlemma[OF C otr' dfr'] .
    then have "r \<in> wds_Mset m" using req' by simp
    then show "r \<in> Wellfounded.acc RPrel" using wds_Mset_subset_acc by blast
  qed
  show "b \<in> Wellfounded.acc RTrel" using wfj_tuple_acc[OF otb dfb comp] .
qed

theorem wds_wf_RPrel_of_collapse:
  assumes "wds_collapse" shows "wf RPrel"
  using wfc_wf_of_pbody[OF wds_pbody_of_collapse[OF assms]] .

theorem wds_wf_RTrel_of_collapse:
  assumes "wds_collapse" shows "wf RTrel"
  using wfox_tuple_lift[OF wds_wf_RPrel_of_collapse[OF assms]] .

corollary wds_buc1_2_2_of_collapse:
  \<comment> \<open>[Buc1] Lemma 2.2 in its original shape: \<open>(OT\<^bsub>B\<^esub>, <)\<close> is wellfounded.\<close>
  assumes "wds_collapse"
  shows "wf {(a, b). a \<in> OT_B \<and> b \<in> OT_B \<and> lessBT a b}"
  using wds_wf_RTrel_of_collapse[OF assms] by (simp add: wfox_goal_eq_RTrel)

corollary wds_collapse_core_of_collapse:
  assumes "wds_collapse" shows "wfj_collapse_core"
  using wfj_collapse_core_of_wf[OF wds_wf_RPrel_of_collapse[OF assms]] .

corollary wds_jump_steps_of_collapse:
  assumes "wds_collapse" shows "wfc_jump_step n"
  using wfc_jump_step_of_wf[OF wds_wf_RPrel_of_collapse[OF assms]] .

subsection \<open>(9) Converse sanity: the residual is EXACTLY theorem-strength\<close>

lemma wds_frag_distinguished_of_wf:
  assumes wfR: "wf RPrel"
  shows "wds_distinguished v (wfj_frag v)"
proof (rule wds_distI)
  show "wfj_frag v \<subseteq> wfj_frag v" by (rule subset_refl)
next
  fix p q assume "p \<in> wfj_frag v" and "(q, p) \<in> RPrel"
  then show "q \<in> wfj_frag v" using wfj_frag_downclosed by blast
next
  fix p assume "p \<in> wfj_frag v"
  have "wf (Restr RPrel (wfj_frag v))" using wfR by (simp add: wf_Int1)
  then have "\<forall>x. x \<in> Wellfounded.acc (Restr RPrel (wfj_frag v))"
    by (rule wf_iff_acc[THEN iffD1])
  then show "p \<in> Wellfounded.acc (Restr RPrel (wfj_frag v))" by blast
next
  fix u c
  assume uv: "u \<le> v" and ot: "isOT_BP (DB (enat u) c)"
    and df: "dfree_BP (DB (enat u) c)"
    and "\<forall>x \<in> GBT (enat u) c. x \<in> wds_hullT (wfj_frag v)"
  have "wfj_hd (DB (enat u) c) \<le> enat v" using uv by simp
  then show "DB (enat u) c \<in> wfj_frag v" using ot df by (simp add: wfj_frag_def)
qed

lemma wds_collapse_of_wf:
  assumes wfR: "wf RPrel"
  shows "wds_collapse"
  unfolding wds_collapse_def
proof (intro allI impI)
  fix v c
  assume ot: "isOT_BP (DB (enat v) c)" and df: "dfree_BP (DB (enat v) c)"
    and "\<forall>x \<in> GBT (enat v) c. \<forall>r \<in> set (untrm x).
           \<exists>m e. r = DB (enat m) e \<and> r \<in> wds_Mset m"
  have "wfj_hd (DB (enat v) c) \<le> enat v" by simp
  then have "DB (enat v) c \<in> wfj_frag v" using ot df by (simp add: wfj_frag_def)
  then show "DB (enat v) c \<in> wds_Mset v"
    using wds_Mset_upper[OF wds_frag_distinguished_of_wf[OF wfR]] by blast
qed

theorem wds_collapse_iff_wf: "wds_collapse \<longleftrightarrow> wf RPrel"
  using wds_wf_RPrel_of_collapse wds_collapse_of_wf by blast

corollary wds_collapse_iff_pbody: "wds_collapse \<longleftrightarrow> wfc_pbody_acc"
  using wds_collapse_iff_wf wfc_pbody_iff_wf by blast

corollary wds_Mset_eq_frag_of_collapse:
  assumes "wds_collapse" shows "wds_Mset v = wfj_frag v"
proof (rule subset_antisym)
  show "wds_Mset v \<subseteq> wfj_frag v" by (rule wds_Mset_frag)
next
  have "wf RPrel" using assms wds_collapse_iff_wf by blast
  then show "wfj_frag v \<subseteq> wds_Mset v"
    using wds_Mset_upper[OF wds_frag_distinguished_of_wf] by blast
qed


section \<open>Additional relocated campaign annotations\<close>

(* ===== end r54 oi4 base3 block ===== *)

(* ===== r54 merge: wt-y3 — distinguished sets blocks 1+2: definition, Mset, D1 union, acc bridge (wds_) ===== *)


(* ===== r54: wt-y3 — buc1 distinguished sets (wds_): Buchholz--Schuette
        Fundierung skeleton for wfc_pbody_acc: definition, comparability via
        linearity, Mset + union lemma (D1), basic closure lemmas ===== *)

section \<open>r54 wds — distinguished sets (ausgezeichnete Mengen) for the collapse\<close>

text \<open>Route (a) of the r53 obstruction analysis: the Buchholz--Schuette
  Fundierung, adapted to \<open>RPrel\<close>/\<open>lessBP\<close>.  HOL's impredicative comprehension
  carries the quantification over subsets \<open>X :: BP set\<close> for free.

  \<^bold>\<open>Design of \<open>wds_distinguished v X\<close>\<close> (the hard 20\<^latex>\<open>\%\<close> — rationale):

  \<^enum> DOMAIN: \<open>X \<subseteq> wfj_frag v\<close> — \<open>OT\<close>+\<open>dfree\<close> principals of head \<open>\<le> v\<close>, i.e. the
    principal terms denoting ordinals below \<open>\<Omega>\<^bsub>v+1\<^esub>\<close>.  This is the r52 TRUE
    stratification (\<open>wfj_strat_hd\<close>), not the refuted \<open>lvP\<close> one.

  \<^enum> DOWNWARD CLOSURE under \<open>RPrel\<close>.  Classically this is derived; we bake it
    in because together with linearity (\<open>wfs_lessBP_total\<close>, Lemma 2.1) it
    yields the Vergleichbarkeitssatz \<^bold>\<open>for free\<close>: downward-closed subsets of a
    linear order form a \<open>\<subseteq>\<close>-chain (\<open>wds_dist_comparable\<close>, below, even across
    levels).  Comparability is exactly what the union lemma (D1) needs to
    re-assemble the finitely many \<open>G\<close>-coefficients of a term inside a single
    member of the family.

  \<^enum> RELATIVE ACCESSIBILITY: every element of \<open>X\<close> is accessible w.r.t.
    \<open>Restr RPrel X\<close> (Buchholz--Schuette \<open>M \<subseteq> W(M)\<close>).  With downward closure
    this is equivalent to genuine \<open>RPrel\<close>-accessibility (\<open>wds_acc_lift\<close>) — the
    leverage of the machinery is INTENSIONAL (\<open>\<Sigma>\<^sup>1\<^sub>1\<close>-membership certificates),
    not extensional.

  \<^enum> \<open>G\<close>-PROGRESSIVENESS ("Abgeschlossenheit", the constructive-closure
    clause): for \<open>u \<le> v\<close>, any \<open>OT\<close>+\<open>dfree\<close> principal \<open>D\<^sub>u c\<close> whose \<open>G\<^sub>u\<close>-trace
    consists of tuples over \<open>X\<close> must already lie in \<open>X\<close>.  This is the
    \<open>K\<close>-coefficient-guarded closure of the classical \<open>C\<^sub>u\<close>-hull, with the
    "body previously constructed" premise DROPPED (K-guard-only form): the
    clause is what the r55+ exhibit-move will discharge against, and the
    \<open>OT\<close> premise keeps the [Buc1] guard \<open>G\<^sub>u c < c\<close> available inside it.
    If the exhibit-move turns out to need the body-constructibility premise
    (a \<open>wds_hullC\<close>-style inductive hull) or the [Buc1] \<open>\<section>\<close>5 fundamental-sequence
    conditions, weaken/extend HERE (definition v2) — all lemmas below are
    cheap to re-run; the load-bearing ones (comparability, D1, the chain) do
    not depend on the exact shape of this clause beyond monotonicity of its
    premise in \<open>X\<close>.

  \<^bold>\<open>Honesty note on existence.\<close>  The progressiveness clause forces every
  distinguished set to contain the hereditarily-\<open>G\<close>-low family (e.g.
  \<open>D\<^sub>0(D\<^sub>9 0)\<close>: its \<open>G\<^sub>0\<close>-trace is \<open>{0}\<close>), which has unbounded \<open>lvP\<close>
  (\<open>wfj_frag0_lv_unbounded\<close>).  Hence EXISTENCE of a \<open>v\<close>-distinguished set is
  itself of theorem strength — as it must be: this is where the
  impredicativity lives.  Accordingly the union lemma (D1) below takes an
  explicit family witness (classically the seed comes from the previous
  stage of the tower induction); under the eventual collapse residual the
  witness is free (\<open>wds_frag_distinguished_of_wf\<close>).\<close>

(* ===== end r54 wds block 1 (definition + comparability + Mset + D1) ===== *)

(* ===== r54 wds block 2: the collapse statement (D3) as the sharp residual,
        the Hauptlemma, and the full chain to wfc_pbody_acc / [Buc1] 2.2 ===== *)

subsection \<open>(6) D3: the collapse lemma — THE residual for r55+\<close>

text \<open>The classical Hauptlemma ("\<open>D\<^sub>v\<close> maps secured bodies into \<open>M\<^sub>v\<close>"), in the
  exact granularity that the size induction below consumes: if every principal
  component of every element of the \<open>G\<^sub>v\<close>-trace of the body \<open>c\<close> already lies in
  the distinguished union AT ITS OWN HEAD (the cross-level generalization of
  "over \<open>M\<^bsub>v+1\<^esub>\<close>-content" — trace components of a \<open>D\<^sub>v\<close>-body carry arbitrary
  heads), then \<open>D\<^sub>v c\<close> lies in \<open>M\<^sub>v\<close>.

  This is the ENTIRE remaining content of [Buc1] Lemma 2.2: everything below
  (\<open>wds_pbody_of_collapse\<close> \<dots>) is proven unconditionally from it, and the
  converse (\<open>wds_collapse_of_wf\<close>) shows the statement is exactly
  theorem-strength, no overshoot.

  \<^bold>\<open>Attack plan for r55+\<close> (the classical proof, adapted):
  \<^enum> EXHIBIT-MOVE: to place \<open>D\<^sub>v c \<in> M\<^sub>v\<close>, exhibit ONE distinguished set
    containing it — the candidate is \<open>M\<^sub>v \<union> {D\<^sub>v c}\<close>-closure.  Its relative-acc
    clause is CHEAP for the new point (its \<open>X\<close>-predecessors lie in \<open>M\<^sub>v\<close>, all
    accessible by D1+\<open>wds_acc_lift\<close>); the work is (i) the \<open>RPrel\<close>-downward
    closure of the candidate — i.e. showing the predecessors of \<open>D\<^sub>v c\<close> inside
    \<open>wfj_frag v\<close> are already in \<open>M\<^sub>v\<close> — and (ii) its \<open>G\<close>-progressiveness.
  \<^enum> For (i), the induction is along the wellfounded ABOVE-\<open>\<Omega>\<^sub>v\<close> structure of
    the body \<open>c\<close> over \<open>M\<close>-material (classically: transfinite induction up to
    \<open>\<epsilon>\<^bsub>\<Omega>\<^sub>n\<^sub>+\<^sub>1\<^esub>\<close> over the wellordered level-\<open>n\<close> part; here \<open>wfs_accord\<close> /
    \<open>wfs_rk\<close> supply the wellorder on \<open>M\<^sub>v \<subseteq> Wellfounded.acc RPrel\<close>).  The r53
    same-head engine \<open>wfc_principal_acc_of_body\<close> and the secured propagation
    \<open>wfc_sec_component\<close> are the prepared bricks for the body recursion; the
    [Buc1] \<open>\<section>\<close>5 fundamental sequences (\<open>b1x_operB_dom_all\<close>) are available if
    the limit-analysis needs them.
  \<^enum> The \<open>OT\<close> guard \<open>G\<^sub>v c < c\<close> (available inside the premise) is what makes
    the collapse order-faithful — [Buc1]'s own Lemma 2.2 proof idea.\<close>

text \<open>\<^bold>\<open>Status after r54.\<close>

  \<^enum> UNCONDITIONAL new content: the distinguished-set skeleton — definition
    (\<open>wds_distinguished\<close>/\<open>wds_hullT\<close>), the Vergleichbarkeitssatz
    (\<open>wds_dist_comparable\<close>, from Lemma 2.1 linearity + downward closure, even
    across levels), the union lemma D1 (\<open>wds_Mset_distinguished\<close>, modulo an
    explicit family witness — honest: family NONEMPTINESS is itself
    theorem-strength here, exactly as the impredicativity analysis of r53
    predicts; classically the witness is the previous stage of the tower
    induction), the basic closure package
    (\<open>wds_Mset_frag\<close>/\<open>_downclosed\<close>/\<open>_subset_acc\<close>/\<open>_relacc\<close>), the acc bridge
    (\<open>wds_acc_lift\<close>), and the size-induction Hauptlemma reducing
    \<open>wfc_pbody_acc\<close> — hence \<open>wf RPrel\<close>, \<open>wf RTrel\<close>, [Buc1] 2.2, the collapse
    core and all jump steps — to ONE named statement.

  \<^enum> THE RESIDUAL (r55+): \<open>wds_collapse\<close> — sharp (\<open>wds_collapse_iff_wf\<close>:
    exactly theorem-strength, no overshoot), classical in shape (the
    Buchholz--Schuette Hauptlemma), and structured for the exhibit-move
    against the four definition clauses (see the attack plan above
    \<open>wds_collapse_def\<close>).  Note D1 gives: once ANY \<open>v\<close>-distinguished set
    exists, \<open>M\<^sub>v\<close> is the maximal one — the exhibit-move should therefore
    construct its candidate ON TOP of \<open>M\<^sub>v\<close> and use comparability to absorb
    it back into the union.

  \<^enum> DESIGN FREEDOM kept open (documented at the definition): the
    progressiveness clause is the K-guard-only form; if the r55 exhibit-move
    needs body-constructibility (an inductive \<open>C\<^sub>v\<close>-hull) or [Buc1] \<open>\<section>\<close>5
    fseq-closure as additional premises, revise the clause there — the D1 and
    chain machinery only uses monotonicity-in-\<open>X\<close> of the clause premise and
    is cheap to re-run.\<close>

end
