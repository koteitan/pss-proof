theory M_8_7_Wfs_Semantic_Rank
  imports M_8_Wf_Bounded_Chain_Reductions
begin

text \<open>Relocated proof material.  The declarations retain their original source order,
  and every relocated annotation is preserved below.  This theory is machine-checked
  outside the termination build tree.\<close>

lemma wfs_max_eq0: "(max (x::enat) y = 0) = (x = 0 \<and> y = 0)"
  by (cases x; cases y) (auto simp add: max_def zero_enat_def)

lemma wfs_max_fin: "(max (x::enat) y \<noteq> \<infinity>) = (x \<noteq> \<infinity> \<and> y \<noteq> \<infinity>)"
  by (cases x; cases y) (auto simp add: max_def)

lemma wfs_maxe_eq0: "(wfs_maxe xs = 0) = (\<forall>x\<in>set xs. x = 0)"
  by (induction xs) (auto simp add: wfs_max_eq0)

lemma wfs_maxe_fin: "(\<forall>x\<in>set xs. x \<noteq> \<infinity>) \<Longrightarrow> wfs_maxe xs \<noteq> \<infinity>"
  by (induction xs) (auto simp add: wfs_max_fin zero_enat_def)

lemma wfs_lvT0_iff: "(wfs_lvT (Trm ps) = 0) = (\<forall>p\<in>set ps. wfs_lvP p = 0)"
  by (simp add: wfs_maxe_eq0)

lemma wfs_lvP0_iff: "(wfs_lvP (DB v b) = 0) = (v = 0 \<and> wfs_lvT b = 0)"
  by (simp add: wfs_max_eq0)

lemma wfs_lv_finT: "dfree_BT t \<Longrightarrow> wfs_lvT t \<noteq> \<infinity>"
  and wfs_lv_finP: "dfree_BP p \<Longrightarrow> wfs_lvP p \<noteq> \<infinity>"
proof (induction t and p rule: wfs_lvT_wfs_lvP.induct)
  case (1 ps)
  have "\<forall>x\<in>set (map wfs_lvP ps). x \<noteq> \<infinity>" using "1.IH" "1.prems" by auto
  then show ?case using wfs_maxe_fin by simp
next
  case (2 v b)
  then show ?case by (auto simp add: wfs_max_fin)
qed

lemma wfs_szP_mem: "z \<in> set ps \<Longrightarrow> wfs_szP z \<le> sum_list (map wfs_szP ps)"
  by (induction ps) auto

lemma wfs_szP_mem_lt: "z \<in> set ps \<Longrightarrow> wfs_szP z < wfs_szT (Trm ps)"
  using wfs_szP_mem[of z ps] by simp

lemma wfs_szT_arg_lt:
  assumes "DB v w \<in> set ps" shows "wfs_szT w < wfs_szT (Trm ps)"
proof -
  have "wfs_szP (DB v w) < wfs_szT (Trm ps)" using wfs_szP_mem_lt[OF assms] .
  then show ?thesis by simp
qed

lemma wfs_szT_tl_lt: "wfs_szT (Trm xs) < wfs_szT (Trm (x # xs))"
  by (cases x) simp

subsection \<open>\<open>descP\<close>: every component is \<open>\<le>\<close> the head\<close>

lemma wfs_descP_le: "descP (x # xs) \<Longrightarrow> z \<in> set xs \<Longrightarrow> lessBP z x \<or> z = x"
proof (induction xs arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons w ws)
  have wx: "lessBP w x \<or> w = x" using Cons.prems(1) by simp
  have dws: "descP (w # ws)" using Cons.prems(1) by simp
  show ?case
  proof (cases "z = w")
    case True
    then show ?thesis using wx by blast
  next
    case False
    then have zws: "z \<in> set ws" using Cons.prems(2) by simp
    have zw: "lessBP z w \<or> z = w" using Cons.IH[OF dws zws] .
    then show ?thesis using wx lessBP_trans by blast
  qed
qed

subsection \<open>(3) STRAT-0: level-0 OT terms are downward closed under \<open><\<close>\<close>

lemma wfs_enat_nlt0: "\<not> (u::enat) < 0"
  by (cases u) (auto simp add: zero_enat_def)

text \<open>The key syntactic stratification, term level: an OT term (componentwise OT
  principals + \<open>descP\<close>) that contains ANY \<open>D\<close>-index \<open>\<ge> 1\<close> is NEVER \<open><\<close> a level-0
  term.  Dictionary order + \<open>descP\<close> force every top-level head index to be \<open>0\<close> on
  both sides, and the offending index recurses into a structurally smaller argument.
  Note: no \<open>G\<close>-condition and no \<open>dfree\<close> is needed — \<open>isOT_BT a\<close> alone suffices.\<close>

lemma wfs_strat0_aux:
  "\<forall>a b. wfs_szT a \<le> n \<longrightarrow> lessBT a b \<longrightarrow> isOT_BT a \<longrightarrow>
         wfs_lvT b = 0 \<longrightarrow> wfs_lvT a = 0"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (intro allI impI)
    fix a b
    assume sza: "wfs_szT a \<le> n" and ab: "lessBT a b" and otA: "isOT_BT a"
      and lvb: "wfs_lvT b = 0"
    show "wfs_lvT a = 0"
    proof (rule ccontr)
      assume lvA: "wfs_lvT a \<noteq> 0"
      obtain as where aeq: "a = Trm as" by (cases a) auto
      obtain bs where beq: "b = Trm bs" by (cases b) auto
      have asne: "as \<noteq> []"
      proof
        assume "as = []"
        then have "wfs_lvT a = 0" by (simp add: aeq)
        with lvA show False by simp
      qed
      then obtain x xs where ase: "as = x # xs" by (cases as) auto
      have bsne: "bs \<noteq> []"
      proof
        assume "bs = []"
        then have "\<not> lessBT a b" by (simp add: aeq beq ase)
        with ab show False by simp
      qed
      then obtain y ys where bse: "bs = y # ys" by (cases bs) auto
      obtain vy d where yeq: "y = DB vy d" by (cases y) auto
      have lvy: "wfs_lvP y = 0"
        using lvb beq bse by (auto simp add: wfs_lvT0_iff wfs_maxe_eq0 wfs_max_eq0)
      have vy0: "vy = 0" and lvd: "wfs_lvT d = 0"
        using lvy yeq by (simp_all add: wfs_lvP0_iff wfs_max_eq0)
      have otComps: "\<forall>p\<in>set as. isOT_BP p" and dsc: "descP as"
        using otA aeq by simp_all
      have badEx: "\<not> (\<forall>p\<in>set as. wfs_lvP p = 0)"
        using lvA aeq by (simp add: wfs_lvT0_iff wfs_maxe_eq0 wfs_max_eq0)
      have cases2: "lessBP x y \<or> (x = y \<and> lessBT (Trm xs) (Trm ys))"
        using ab aeq beq ase bse by simp
      then show False
      proof
        assume xy: "lessBP x y"
        obtain u c where xeq: "x = DB u c" by (cases x) auto
        have "u < vy \<or> (u = vy \<and> lessBT c d)" using xy xeq yeq by simp
        then have ucd: "u = 0 \<and> lessBT c d"
          using vy0 wfs_enat_nlt0[of u] by auto
        have u0: "u = 0" and cd: "lessBT c d" using ucd by blast+
        have otx: "isOT_BP x" using otComps ase by simp
        have otc: "isOT_BT c" using otx xeq by simp
        show False
        proof (cases "wfs_lvT c = 0")
          case False
          have xin: "DB u c \<in> set as" using ase xeq by simp
          have szc: "wfs_szT c < wfs_szT a"
            using wfs_szT_arg_lt[OF xin] aeq by simp
          have cn: "wfs_szT c < n" using szc sza by linarith
          have "wfs_lvT c = 0" using less.IH[OF cn] cd otc lvd by blast
          with False show False by simp
        next
          case True
          have lvx: "wfs_lvP x = 0" using xeq u0 True by (simp add: wfs_lvP0_iff)
          obtain z where zin: "z \<in> set as" and zbad: "wfs_lvP z \<noteq> 0"
            using badEx by blast
          have zxs: "z \<in> set xs" using zin ase lvx zbad by auto
          have zle: "lessBP z x \<or> z = x"
            using wfs_descP_le[of x xs z] dsc ase zxs by simp
          have zx: "lessBP z x" using zle zbad lvx by auto
          obtain uz w where zeq: "z = DB uz w" by (cases z) auto
          have "uz < u \<or> (uz = u \<and> lessBT w c)" using zx zeq xeq by simp
          then have wcd: "uz = 0 \<and> lessBT w c"
            using u0 wfs_enat_nlt0[of uz] by auto
          have wc: "lessBT w c" using wcd by blast
          have wbad: "wfs_lvT w \<noteq> 0"
            using zbad zeq wcd by (simp add: wfs_lvP0_iff wfs_max_eq0)
          have otz: "isOT_BP z" using otComps zin by blast
          have otw: "isOT_BT w" using otz zeq by simp
          have zin': "DB uz w \<in> set as" using zin zeq by simp
          have szw: "wfs_szT w < wfs_szT a"
            using wfs_szT_arg_lt[OF zin'] aeq by simp
          have wn: "wfs_szT w < n" using szw sza by linarith
          have "wfs_lvT w = 0" using less.IH[OF wn] wc otw True by blast
          with wbad show False by simp
        qed
      next
        assume B: "x = y \<and> lessBT (Trm xs) (Trm ys)"
        have lvx: "wfs_lvP x = 0" using B lvy by simp
        obtain z where zin: "z \<in> set as" and zbad: "wfs_lvP z \<noteq> 0"
          using badEx by blast
        have zxs: "z \<in> set xs" using zin ase lvx zbad by auto
        have lvxs: "wfs_lvT (Trm xs) \<noteq> 0"
          using zxs zbad by (auto simp add: wfs_lvT0_iff wfs_maxe_eq0 wfs_max_eq0)
        have otxs: "isOT_BT (Trm xs)"
          using otComps ase descP_tl[of x xs] dsc by auto
        have lvys: "wfs_lvT (Trm ys) = 0"
          using lvb beq bse by (auto simp add: wfs_lvT0_iff wfs_maxe_eq0 wfs_max_eq0)
        have szxs: "wfs_szT (Trm xs) < wfs_szT a"
          using wfs_szT_tl_lt[of xs x] aeq ase by simp
        have xn: "wfs_szT (Trm xs) < n" using szxs sza by linarith
        have "wfs_lvT (Trm xs) = 0" using less.IH[OF xn] B otxs lvys by blast
        with lvxs show False by simp
      qed
    qed
  qed
qed

lemma wfs_strat0_T:
  assumes "lessBT a b" and "isOT_BT a" and "wfs_lvT b = 0"
  shows "wfs_lvT a = 0"
  using wfs_strat0_aux[of "wfs_szT a"] assms order_refl by blast

text \<open>Principal / \<open>RPrel\<close> form: the level-0 principals are downward closed.\<close>

lemma wfs_strat0_P:
  assumes qp: "(q, p) \<in> RPrel" and lvp: "wfs_lvP p = 0"
  shows "wfs_lvP q = 0"
proof -
  obtain uq w where qeq: "q = DB uq w" by (cases q) auto
  obtain up c where peq: "p = DB up c" by (cases p) auto
  have otq: "isOT_BP q" and lpq: "lessBP q p"
    using qp by (auto simp add: RPrel_def)
  have up0: "up = 0" and lvc: "wfs_lvT c = 0"
    using lvp peq by (simp_all add: wfs_lvP0_iff wfs_max_eq0)
  have "uq < up \<or> (uq = up \<and> lessBT w c)" using lpq qeq peq by simp
  then have wcd: "uq = 0 \<and> lessBT w c"
    using up0 wfs_enat_nlt0[of uq] by auto
  have otw: "isOT_BT w" using otq qeq by simp
  have "wfs_lvT w = 0" using wfs_strat0_T wcd otw lvc by blast
  then show ?thesis using qeq wcd by (simp add: wfs_lvP0_iff wfs_max_eq0)
qed

subsection \<open>(4) DEPTH-MONO-0: on level-0 OT terms the order bounds the depth\<close>

text \<open>At level 0 every head index is \<open>0\<close>, so the dictionary order always recurses
  into ARGUMENTS and never jumps levels: depth-\<open>d\<close> level-0 OT values fill exactly
  the interval \<open>[tower(d), tower(d+1))\<close>, making depth MONOTONE along \<open><\<close>.
  (At level \<open>\<ge> 1\<close> this is FALSE — the \<open>D\<^sub>0\<close>-towers of unbounded depth all sit below
  \<open>D\<^sub>0 (D\<^sub>1 0)\<close> — which is exactly why the level JUMP is the hard residual.)\<close>

lemma wfs_maxl_le: "(\<forall>x\<in>set xs. x \<le> K) \<Longrightarrow> maxl xs \<le> K"
  by (induction xs) auto

lemma wfs_bdepthT_le:
  assumes "\<And>z. z \<in> set ps \<Longrightarrow> bdepthP z \<le> K"
  shows "bdepthT (Trm ps) \<le> K"
proof -
  have "\<forall>x\<in>set (map bdepthP ps). x \<le> K" using assms by auto
  then show ?thesis by (simp add: wfs_maxl_le)
qed

lemma wfs_dmono_aux:
  "\<forall>a b. wfs_szT a + wfs_szT b \<le> n \<longrightarrow> lessBT a b \<longrightarrow> isOT_BT a \<longrightarrow>
         wfs_lvT a = 0 \<longrightarrow> wfs_lvT b = 0 \<longrightarrow> bdepthT a \<le> bdepthT b"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (intro allI impI)
    fix a b
    assume sz: "wfs_szT a + wfs_szT b \<le> n" and ab: "lessBT a b"
      and otA: "isOT_BT a" and lva: "wfs_lvT a = 0" and lvb: "wfs_lvT b = 0"
    obtain as where aeq: "a = Trm as" by (cases a) auto
    obtain bs where beq: "b = Trm bs" by (cases b) auto
    show "bdepthT a \<le> bdepthT b"
    proof (cases as)
      case Nil
      then show ?thesis using aeq by simp
    next
      case (Cons x xs)
      note ase = Cons
      have bsne: "bs \<noteq> []"
      proof
        assume "bs = []"
        then have "\<not> lessBT a b" by (simp add: aeq beq ase)
        with ab show False by simp
      qed
      then obtain y ys where bse: "bs = y # ys" by (cases bs) auto
      obtain vy d where yeq: "y = DB vy d" by (cases y) auto
      obtain u c where xeq: "x = DB u c" by (cases x) auto
      have otComps: "\<forall>p\<in>set as. isOT_BP p" and dsc: "descP as"
        using otA aeq by simp_all
      have lvcompsA: "\<forall>p\<in>set as. wfs_lvP p = 0"
        using lva aeq by (auto simp add: wfs_lvT0_iff wfs_maxe_eq0 wfs_max_eq0)
      have lvcompsB: "\<forall>p\<in>set bs. wfs_lvP p = 0"
        using lvb beq by (auto simp add: wfs_lvT0_iff wfs_maxe_eq0 wfs_max_eq0)
      have u0: "u = 0" and lvc: "wfs_lvT c = 0"
        using lvcompsA ase xeq by (auto simp add: wfs_lvP0_iff wfs_max_eq0)
      have vy0: "vy = 0" and lvd: "wfs_lvT d = 0"
        using lvcompsB bse yeq by (auto simp add: wfs_lvP0_iff wfs_max_eq0)
      have dPy: "bdepthP y \<le> bdepthT b"
        using bdepthP_head_le[of y bs] bse beq by simp
      have cases2: "lessBP x y \<or> (x = y \<and> lessBT (Trm xs) (Trm ys))"
        using ab aeq beq ase bse by simp
      have zbound: "\<And>z. z \<in> set as \<Longrightarrow> bdepthP z \<le> bdepthT b"
      proof -
        fix z assume zin: "z \<in> set as"
        have zle: "lessBP z x \<or> z = x"
          using wfs_descP_le[of x xs z] dsc ase zin by auto
        obtain uz w where zeq: "z = DB uz w" by (cases z) auto
        have uz0: "uz = 0" and lvw: "wfs_lvT w = 0"
          using lvcompsA zin zeq by (auto simp add: wfs_lvP0_iff wfs_max_eq0)
        have otz: "isOT_BP z" using otComps zin by blast
        have otw: "isOT_BT w" using otz zeq by simp
        have szw: "wfs_szT w < wfs_szT a"
          using wfs_szT_arg_lt[of uz w as] zin zeq aeq by simp
        show "bdepthP z \<le> bdepthT b"
        proof (cases "lessBP x y")
          case True
          have "u < vy \<or> (u = vy \<and> lessBT c d)" using True xeq yeq by simp
          then have cd: "lessBT c d" using u0 vy0 by auto
          have wd: "lessBT w d"
          proof (cases "z = x")
            case True
            then have "w = c" using zeq xeq by simp
            then show ?thesis using cd by simp
          next
            case False
            then have zx: "lessBP z x" using zle by blast
            have "uz < u \<or> (uz = u \<and> lessBT w c)" using zx zeq xeq by simp
            then have wc: "lessBT w c" using u0 uz0 by auto
            then show ?thesis using cd lessBT_trans by blast
          qed
          have szd: "wfs_szT d < wfs_szT b"
            using wfs_szT_arg_lt[of vy d bs] bse yeq beq by simp
          have dn: "wfs_szT w + wfs_szT d < n" using szw szd sz by linarith
          have "bdepthT w \<le> bdepthT d"
            using less.IH[OF dn] wd otw lvw lvd by blast
          then have "bdepthP z \<le> bdepthP y" using zeq yeq by simp
          then show ?thesis using dPy by linarith
        next
          case False
          then have Bx: "x = y" and xsys: "lessBT (Trm xs) (Trm ys)"
            using cases2 by blast+
          show ?thesis
          proof (cases "z = x")
            case True
            then have "bdepthP z = bdepthP y" using Bx by simp
            then show ?thesis using dPy by simp
          next
            case False
            then have zxs: "z \<in> set xs" using zin ase by auto
            have otxs: "isOT_BT (Trm xs)"
              using otComps ase descP_tl[of x xs] dsc by auto
            have lvxs: "wfs_lvT (Trm xs) = 0"
              using lvcompsA ase
              by (auto simp add: wfs_lvT0_iff wfs_maxe_eq0 wfs_max_eq0)
            have lvys: "wfs_lvT (Trm ys) = 0"
              using lvcompsB bse
              by (auto simp add: wfs_lvT0_iff wfs_maxe_eq0 wfs_max_eq0)
            have sza': "wfs_szT (Trm xs) < wfs_szT a"
              using aeq ase wfs_szT_tl_lt[of xs x] by simp
            have szb': "wfs_szT (Trm ys) < wfs_szT b"
              using beq bse wfs_szT_tl_lt[of ys y] by simp
            have tn: "wfs_szT (Trm xs) + wfs_szT (Trm ys) < n"
              using sza' szb' sz by linarith
            have IHt: "bdepthT (Trm xs) \<le> bdepthT (Trm ys)"
              using less.IH[OF tn] xsys otxs lvxs lvys by blast
            have z1: "bdepthP z \<le> bdepthT (Trm xs)"
              using bdepthP_head_le[of z xs] zxs by simp
            have y1: "bdepthT (Trm ys) \<le> bdepthT b"
              using bdepthT_tl_le[of "y # ys"] beq bse by simp
            show ?thesis using z1 IHt y1 by linarith
          qed
        qed
      qed
      have "bdepthT (Trm as) \<le> bdepthT b" by (rule wfs_bdepthT_le[OF zbound])
      then show ?thesis using aeq by simp
    qed
  qed
qed

lemma wfs_dmono_T:
  assumes "lessBT a b" and "isOT_BT a" and "wfs_lvT a = 0" and "wfs_lvT b = 0"
  shows "bdepthT a \<le> bdepthT b"
  using wfs_dmono_aux[of "wfs_szT a + wfs_szT b"] assms order_refl by blast

lemma wfs_dmono_P:
  assumes qp: "lessBP q p" and otq: "isOT_BP q"
      and lvq: "wfs_lvP q = 0" and lvp: "wfs_lvP p = 0"
  shows "bdepthP q \<le> bdepthP p"
proof -
  obtain uq w where qeq: "q = DB uq w" by (cases q) auto
  obtain up c where peq: "p = DB up c" by (cases p) auto
  have uq0: "uq = 0" and lvw: "wfs_lvT w = 0"
    using lvq qeq by (auto simp add: wfs_lvP0_iff wfs_max_eq0)
  have up0: "up = 0" and lvc: "wfs_lvT c = 0"
    using lvp peq by (auto simp add: wfs_lvP0_iff wfs_max_eq0)
  have "uq < up \<or> (uq = up \<and> lessBT w c)" using qp qeq peq by simp
  then have wc: "lessBT w c" using uq0 up0 by auto
  have otw: "isOT_BT w" using otq qeq by simp
  have "bdepthT w \<le> bdepthT c" using wfs_dmono_T[OF wc otw lvw lvc] .
  then show ?thesis using qeq peq by simp
qed

text \<open>\<^bold>\<open>Level-0 accessibility\<close> — the \<open>\<epsilon>\<^sub>0\<close>-grade base case, WITHOUT any new
  well-ordering argument: STRAT-0 keeps every \<open>RPrel\<close>-descent from a level-0
  principal at level 0, DEPTH-MONO-0 then pins it below depth \<open>bdepthP p\<close>, and the
  depth-bounded fragment is already known well-founded
  (@{thm [source] wfpd_wf_RPrel_dep}).\<close>

theorem wfs_level0_acc:
  assumes otp: "isOT_BP p" and dfp: "dfree_BP p" and lvp: "wfs_lvP p = 0"
  shows "p \<in> Wellfounded.acc RPrel"
proof -
  define S where "S = {q. isOT_BP q \<and> dfree_BP q \<and> wfs_lvP q = 0 \<and>
                          (lessBP q p \<or> q = p)}"
  have dc: "\<forall>s q. s \<in> S \<longrightarrow> (q, s) \<in> RPrel \<longrightarrow> q \<in> S"
  proof (intro allI impI)
    fix s q assume sS: "s \<in> S" and qs: "(q, s) \<in> RPrel"
    have sfacts: "isOT_BP s" "dfree_BP s" "wfs_lvP s = 0" "lessBP s p \<or> s = p"
      using sS by (auto simp add: S_def)
    have qfacts: "isOT_BP q" "dfree_BP q" "lessBP q s"
      using qs by (auto simp add: RPrel_def)
    have lvq: "wfs_lvP q = 0" using wfs_strat0_P[OF qs] sfacts(3) by blast
    have "lessBP q p" using qfacts(3) sfacts(4) lessBP_trans by blast
    then show "q \<in> S" using qfacts lvq by (auto simp add: S_def)
  qed
  have Sdep: "\<And>q. q \<in> S \<Longrightarrow> bdepthP q \<le> bdepthP p"
  proof -
    fix q assume qS: "q \<in> S"
    have qf: "isOT_BP q" "wfs_lvP q = 0" "lessBP q p \<or> q = p"
      using qS by (auto simp add: S_def)
    show "bdepthP q \<le> bdepthP p"
    proof (cases "q = p")
      case True then show ?thesis by simp
    next
      case False
      then have "lessBP q p" using qf(3) by blast
      then show ?thesis using wfs_dmono_P qf(1) qf(2) lvp by blast
    qed
  qed
  have sub: "Restr RPrel S \<subseteq> RPrel_dep (bdepthP p)"
  proof (rule subrelI)
    fix q1 q2 assume "(q1, q2) \<in> Restr RPrel S"
    then have inR: "(q1, q2) \<in> RPrel" and q1S: "q1 \<in> S" and q2S: "q2 \<in> S" by auto
    show "(q1, q2) \<in> RPrel_dep (bdepthP p)"
      using inR Sdep[OF q1S] Sdep[OF q2S] by (simp add: RPrel_dep_def)
  qed
  have wfS: "wf (Restr RPrel S)" by (rule wf_subset[OF wfpd_wf_RPrel_dep sub])
  have pS: "p \<in> S" using otp dfp lvp by (simp add: S_def)
  show ?thesis using wfs_closed_wf_acc[OF dc wfS] pS by blast
qed

lemma wfs_acc_levels_of_jump:
  assumes J: "wfs_level_jump"
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
  show ?case
  proof (intro allI impI)
    fix p assume otp: "isOT_BP p" and dfp: "dfree_BP p"
      and lvp: "wfs_lvP p \<le> enat (Suc n)"
    show "p \<in> Wellfounded.acc RPrel"
      using J[unfolded wfs_level_jump_def] otp dfp lvp Suc.IH by blast
  qed
qed

theorem wfs_wf_RPrel_of_level_jump:
  assumes J: "wfs_level_jump"
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
      then show ?thesis using wfs_acc_levels_of_jump[OF J] True by blast
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

text \<open>The GOAL ([Buc1] Lemma 2.2) modulo the single level-jump residual.\<close>

theorem wfs_OT_B_wf_of_level_jump:
  assumes "wfs_level_jump"
  shows "wf {(a, b). a \<in> OT_B \<and> b \<in> OT_B \<and> lessBT a b}"
  using m_buc1_2_2_OT_B_wf_via_principal[OF wfs_wf_RPrel_of_level_jump[OF assms]] .

lemma wfs_wf_iff_all_acc: "wf RPrel \<longleftrightarrow> (\<forall>p. p \<in> Wellfounded.acc RPrel)"
  by (rule wf_iff_acc)

subsection \<open>(6) \<open>wfs_acc_total\<close>: the accessible part is downward closed and
  carries a wellorder\<close>

lemma wfs_lessBP_total: "lessBP p q \<or> p = q \<or> lessBP q p"
  using lessBT_lessBP_total by blast

lemma wfs_acc_downclosed:
  assumes "(q, p) \<in> RPrel" and "p \<in> Wellfounded.acc RPrel"
  shows "q \<in> Wellfounded.acc RPrel"
  by (rule acc_downward[OF assms(2) assms(1)])

text \<open>The restriction of any relation to its accessible part is well-founded.\<close>

lemma wfs_Restr_acc_wf: "wf (Restr R (Wellfounded.acc R))"
proof (rule acc_wfI, intro allI)
  fix x
  show "x \<in> Wellfounded.acc (Restr R (Wellfounded.acc R))"
  proof (cases "x \<in> Wellfounded.acc R")
    case True
    then show ?thesis
    proof (induction rule: acc.induct)
      case (accI x)
      show ?case
      proof (rule Wellfounded.accI)
        fix y assume "(y, x) \<in> Restr R (Wellfounded.acc R)"
        then have "(y, x) \<in> R" by blast
        then show "y \<in> Wellfounded.acc (Restr R (Wellfounded.acc R))"
          using accI.IH by blast
      qed
    qed
  next
    case False
    show ?thesis
    proof (rule Wellfounded.accI)
      fix y assume "(y, x) \<in> Restr R (Wellfounded.acc R)"
      then have "x \<in> Wellfounded.acc R" by blast
      with False show "y \<in> Wellfounded.acc (Restr R (Wellfounded.acc R))" by blast
    qed
  qed
qed

lemma wfs_accord_strict_sub:
  "wfs_accord - Id \<subseteq> Restr RPrel (Wellfounded.acc RPrel)"
proof (rule subrelI)
  fix p q assume "(p, q) \<in> wfs_accord - Id"
  then have pq: "p \<in> wfs_ACC" "q \<in> wfs_ACC" "lessBP p q \<or> p = q" "p \<noteq> q"
    by (auto simp add: wfs_accord_def)
  have "lessBP p q" using pq(3) pq(4) by blast
  then have "(p, q) \<in> RPrel"
    using pq(1) pq(2) by (auto simp add: wfs_ACC_def RPrel_def)
  then show "(p, q) \<in> Restr RPrel (Wellfounded.acc RPrel)"
    using pq(1) pq(2) by (auto simp add: wfs_ACC_def)
qed

lemma wfs_accord_wf_strict: "wf (wfs_accord - Id)"
  by (rule wf_subset[OF wfs_Restr_acc_wf wfs_accord_strict_sub])

theorem wfs_accord_well_order: "well_order_on wfs_ACC wfs_accord"
proof -
  have r1: "wfs_accord \<subseteq> wfs_ACC \<times> wfs_ACC" by (auto simp add: wfs_accord_def)
  have r2: "refl_on wfs_ACC wfs_accord"
    by (auto simp add: refl_on_def wfs_accord_def)
  have r3: "trans wfs_accord"
  proof (rule transI)
    fix x y z assume a1: "(x, y) \<in> wfs_accord" and a2: "(y, z) \<in> wfs_accord"
    have f1: "x \<in> wfs_ACC" "z \<in> wfs_ACC" "lessBP x y \<or> x = y" "lessBP y z \<or> y = z"
      using a1 a2 by (auto simp add: wfs_accord_def)
    have "lessBP x z \<or> x = z" using f1(3) f1(4) lessBP_trans by blast
    then show "(x, z) \<in> wfs_accord"
      using f1(1) f1(2) by (auto simp add: wfs_accord_def)
  qed
  have r4: "antisym wfs_accord"
  proof (rule antisymI)
    fix x y assume "(x, y) \<in> wfs_accord" and "(y, x) \<in> wfs_accord"
    then have "(lessBP x y \<or> x = y) \<and> (lessBP y x \<or> y = x)"
      by (auto simp add: wfs_accord_def)
    then show "x = y" using lessBP_trans lessBP_irrefl by blast
  qed
  have r5: "total_on wfs_ACC wfs_accord"
  proof -
    have "\<And>x y. x \<in> wfs_ACC \<Longrightarrow> y \<in> wfs_ACC \<Longrightarrow> x \<noteq> y \<Longrightarrow>
            (x, y) \<in> wfs_accord \<or> (y, x) \<in> wfs_accord"
      using wfs_lessBP_total by (auto simp add: wfs_accord_def)
    then show ?thesis by (auto simp add: total_on_def)
  qed
  show ?thesis
    using r1 r2 r3 r4 r5 wfs_accord_wf_strict
    by (simp add: well_order_on_def linear_order_on_def partial_order_on_def
                  preorder_on_def)
qed

lemma wfs_accord_Field: "Field wfs_accord = wfs_ACC"
proof
  show "Field wfs_accord \<subseteq> wfs_ACC" by (auto simp add: Field_def wfs_accord_def)
  show "wfs_ACC \<subseteq> Field wfs_accord"
  proof
    fix p assume "p \<in> wfs_ACC"
    then have "(p, p) \<in> wfs_accord" by (simp add: wfs_accord_def)
    then show "p \<in> Field wfs_accord" by (auto simp add: Field_def)
  qed
qed

theorem wfs_accord_Well_order: "Well_order wfs_accord"
  using wfs_accord_well_order wfs_accord_Field by simp

lemma wfs_rk_Well_order: "Well_order (wfs_rk p)"
  unfolding wfs_rk_def by (rule Well_order_Restr[OF wfs_accord_Well_order])

lemma wfs_underS_accord:
  assumes pA: "p \<in> wfs_ACC"
  shows "underS wfs_accord p = {q. (q, p) \<in> RPrel}"
proof
  show "underS wfs_accord p \<subseteq> {q. (q, p) \<in> RPrel}"
  proof
    fix q assume "q \<in> underS wfs_accord p"
    then have "q \<noteq> p" and "(q, p) \<in> wfs_accord" by (auto simp add: underS_def)
    then have "q \<in> wfs_ACC" and "lessBP q p" by (auto simp add: wfs_accord_def)
    then show "q \<in> {q. (q, p) \<in> RPrel}"
      using pA by (auto simp add: wfs_ACC_def RPrel_def)
  qed
  show "{q. (q, p) \<in> RPrel} \<subseteq> underS wfs_accord p"
  proof
    fix q assume "q \<in> {q. (q, p) \<in> RPrel}"
    then have qp: "(q, p) \<in> RPrel" by blast
    have qacc: "q \<in> Wellfounded.acc RPrel"
      using wfs_acc_downclosed[OF qp] pA by (auto simp add: wfs_ACC_def)
    have qg: "isOT_BP q" "dfree_BP q" "lessBP q p"
      using qp by (auto simp add: RPrel_def)
    have qA: "q \<in> wfs_ACC" using qacc qg by (simp add: wfs_ACC_def)
    have "q \<noteq> p" using qg(3) lessBP_irrefl by blast
    then show "q \<in> underS wfs_accord p"
      using qA pA qg(3) by (auto simp add: underS_def wfs_accord_def)
  qed
qed

theorem wfs_rk_ordLess:
  \<comment> \<open>\<open>wfs_rk p <o wfs_rk q\<close>; the \<open><o\<close> notation is disabled in Main, so we use
      the constant @{const ordLess2} (\<open>= (\<lambda>r r'. (r, r') \<in> ordLess)\<close>) directly.\<close>
  assumes pq: "(p, q) \<in> RPrel" and qacc: "q \<in> Wellfounded.acc RPrel"
  shows "ordLess2 (wfs_rk p) (wfs_rk q)"
proof -
  have pacc: "p \<in> Wellfounded.acc RPrel" using wfs_acc_downclosed[OF pq qacc] .
  have pg: "isOT_BP p" "dfree_BP p" and qg: "isOT_BP q" "dfree_BP q"
    and lpq: "lessBP p q" using pq by (auto simp add: RPrel_def)
  have pA: "p \<in> wfs_ACC" and qA: "q \<in> wfs_ACC"
    using pacc qacc pg qg by (auto simp add: wfs_ACC_def)
  have pUq: "p \<in> underS wfs_accord q"
    using wfs_underS_accord[OF qA] pq by auto
  have Usub: "underS wfs_accord p \<subseteq> underS wfs_accord q"
  proof
    fix r assume "r \<in> underS wfs_accord p"
    then have rp: "(r, p) \<in> RPrel" using wfs_underS_accord[OF pA] by auto
    have rg: "isOT_BP r" "dfree_BP r" "lessBP r p"
      using rp by (auto simp add: RPrel_def)
    have "lessBP r q" using rg(3) lpq lessBP_trans by blast
    then have "(r, q) \<in> RPrel" using rg qg by (auto simp add: RPrel_def)
    then show "r \<in> underS wfs_accord q" using wfs_underS_accord[OF qA] by auto
  qed
  have UeqA: "underS (wfs_rk q) p = underS wfs_accord p"
  proof
    show "underS (wfs_rk q) p \<subseteq> underS wfs_accord p"
      by (auto simp add: wfs_rk_def underS_def)
    show "underS wfs_accord p \<subseteq> underS (wfs_rk q) p"
    proof
      fix r assume rU: "r \<in> underS wfs_accord p"
      have rUq: "r \<in> underS wfs_accord q" using Usub rU by blast
      have "(r, p) \<in> wfs_accord" and "r \<noteq> p" using rU by (auto simp add: underS_def)
      then show "r \<in> underS (wfs_rk q) p"
        using rUq pUq by (auto simp add: wfs_rk_def underS_def)
    qed
  qed
  have Uabs: "underS wfs_accord q \<inter> underS wfs_accord p = underS wfs_accord p"
    using Usub by blast
  have rkEq: "wfs_rk p = Restr (wfs_rk q) (underS (wfs_rk q) p)"
    using UeqA Usub by (auto simp add: wfs_rk_def)
  have FieldNE: "Field (wfs_rk q) \<noteq> {}"
  proof -
    have "(p, p) \<in> wfs_accord" using pA by (simp add: wfs_accord_def)
    then have "(p, p) \<in> wfs_rk q" using pUq by (simp add: wfs_rk_def)
    then have "p \<in> Field (wfs_rk q)" by (auto simp add: Field_def)
    then show ?thesis by blast
  qed
  show ?thesis
    using rkEq underS_Restr_ordLess[OF wfs_rk_Well_order FieldNE, of p] by simp
qed

theorem wfs_rank_semantic:
  "\<forall>p q. (p, q) \<in> RPrel \<and> q \<in> Wellfounded.acc RPrel \<longrightarrow>
         ordLess2 (wfs_rk p) (wfs_rk q)"
  using wfs_rk_ordLess by blast


section \<open>Additional relocated campaign annotations\<close>

(* ===== end r51-OIX block ===== *)

(* ===== r51 merge: wt-y3 — buc1: level-0 acc UNCONDITIONAL + goal == single residual wfs_level_jump; wellorder/rank toolkit (wfs_) ===== *)

(* ===== r51 buc1-semantic front (wfs_): [Buc1] Lemma 2.2 — semantic rank on the
        accessible part, level stratification, level-0 accessibility, LEVEL-JUMP
        residual ===== *)

section \<open>r51 wfs — \<open>wf RPrel\<close> via level stratification and the semantic rank\<close>

text \<open>Target: the LAST external citation, well-foundedness of Buchholz's \<open>(OT\<^bsub>B\<^esub>, <)\<close>
  ([Buc1] Lemma 2.2).  By @{thm [source] m_buc1_2_2_OT_B_wf_via_principal} it suffices
  to prove \<open>wf RPrel\<close> (the OT+dfree PRINCIPALS under \<open>lessBP\<close>).

  \<^bold>\<open>Plan of this front\<close> (all in this block, prefix \<open>wfs_\<close>):
  \<^enum> Infra probe: the wellorder-relation order \<open><o\<close> (\<open>ordLess\<close>) with
    @{thm [source] wf_ordLess}, and the accessible-part (\<open>Wellfounded.acc\<close>) machinery,
    are available from Main — no new imports.
  \<^enum> D-index LEVEL \<open>wfs_lvT/wfs_lvP\<close> (the maximum \<open>D\<close>-index occurring anywhere in a
    term, \<open>enat\<close>-valued so \<open>D\<^sub>\<omega>\<close> is \<open>\<infinity>\<close>).  Level \<open>\<le> n\<close> stratifies \<open>OT\<^bsub>B\<^esub>\<close>;
    semantically level 0 \<open>\<cong>\<close> the additively principal ordinals \<open>< \<epsilon>\<^sub>0\<close>, and
    level \<open>n \<Rightarrow> n+1\<close> is one \<open>\<psi>\<close>-collapse step.
  \<^enum> STRAT-0 (\<open>wfs_strat0_P\<close>): inside \<open>RPrel\<close>, the level-0 principals are DOWNWARD
    CLOSED — the OT (\<open>descP\<close> + componentwise \<open>G\<close>) constraint forbids an
    \<open>index \<ge> 1\<close> term below a level-0 term.  Purely syntactic induction.
  \<^enum> DEPTH-MONO-0 (\<open>wfs_dmono_P\<close>): on level-0 OT terms the ORDER BOUNDS THE DEPTH
    (\<open>q < p \<Longrightarrow> bdepthP q \<le> bdepthP p\<close>): at level 0 all head indices are equal, so
    the dictionary order never jumps levels and depth-\<open>d\<close> values fill exactly the
    interval \<open>[tower(d), tower(d+1))\<close>.  With STRAT-0 this pins every \<open>RPrel\<close>-descent
    from a level-0 principal inside the DEPTH-BOUNDED fragment, whose
    well-foundedness is already proven unconditionally
    (@{thm [source] wfpd_wf_RPrel_dep}) — giving \<open>wfs_level0_acc\<close>: every level-0
    OT+dfree principal is in \<open>Wellfounded.acc RPrel\<close>.
  \<^enum> The remaining content of [Buc1] Lemma 2.2 is isolated as ONE sharp named
    residual, the LEVEL JUMP (\<open>wfs_level_jump\<close>): accessibility at level \<open>n+1\<close>
    given accessibility at level \<open>n\<close>.  \<open>wfs_wf_RPrel_of_level_jump\<close> /
    \<open>wfs_OT_B_wf_of_level_jump\<close> discharge the goal modulo that single residual.
  \<^enum> The SEMANTIC RANK (honest pivot documented at the rank block): each accessible
    principal \<open>p\<close> is ranked by the restriction of the (reflexivized) order to its
    predecessors, a wellorder relation; \<open>rk\<close> is strictly monotone into \<open><o\<close>
    (@{thm [source] wf_ordLess}).  The rank exists exactly ON the accessible part,
    so it cannot by itself DISCHARGE accessibility — the level-jump residual is the
    genuine \<open>\<psi>\<close>-collapse core; the rank supplies the well-ordering of the accessible
    part needed by the classical collapse argument.\<close>

subsection \<open>(7) The semantic rank \<open>wfs_rk\<close> into \<open>(ordLess, wf_ordLess)\<close>\<close>

text \<open>\<^bold>\<open>Honest pivot\<close> (as anticipated): interpreting an OT principal by the order
  type of its own predecessors requires those predecessors to be WELL-ordered, which
  on the raw field is exactly the goal — so the rank is built ON THE ACCESSIBLE PART,
  where @{thm [source] wfs_Restr_acc_wf} + totality make \<open>wfs_accord\<close> a wellorder.
  The rank therefore cannot by itself discharge \<open>wf RPrel\<close>; its role is to supply,
  for FREE from Main (@{thm [source] wf_ordLess}), the well-ordered target that the
  classical collapse argument for the level jump recurses along.  \<open>wfs_rk p\<close> = the
  restriction of \<open>wfs_accord\<close> to the strict predecessors of \<open>p\<close>; \<open>p < q\<close> makes
  \<open>wfs_rk p\<close> a PROPER INITIAL SEGMENT (an \<open>underS\<close> ofilter) of \<open>wfs_rk q\<close>, hence
  \<open>wfs_rk p <o wfs_rk q\<close> by @{thm [source] underS_Restr_ordLess}.\<close>

text \<open>\<^bold>\<open>Status and feasibility verdict for the LEVEL JUMP\<close> (\<open>wfs_level_jump\<close>).

  \<^bold>\<open>Closed this round\<close>: infra probe (\<open><o\<close>/\<open>acc\<close> from Main), level function, STRAT-0,
  DEPTH-MONO-0, \<open>wfs_level0_acc\<close> (the \<open>\<epsilon>\<^sub>0\<close>-grade base case, fully unconditional),
  \<open>wfs_wf_RPrel_of_level_jump\<close> / \<open>wfs_OT_B_wf_of_level_jump\<close> (goal \<open>\<equiv>\<close> the single
  residual), accessible-part wellorder \<open>wfs_accord\<close>, semantic rank \<open>wfs_rk\<close>
  strictly monotone into \<open><o\<close>.

  \<^bold>\<open>Why the jump is genuinely harder than level 0\<close>: DEPTH-MONO fails at level
  \<open>\<ge> 1\<close> (all \<open>D\<^sub>0\<close>-towers sit below \<open>D\<^sub>0 (D\<^sub>1 0)\<close> with unbounded depth), so no
  depth-bounded fragment can absorb the descent; this is where the collapse
  \<open>\<psi>\<^sub>v\<close>-semantics is load-bearing.  The classical argument ([Buc1]'s own proof of
  Lemma 2.2) runs: transfinite recursion along the well-ordered accessible
  level-\<open>n\<close> part (NOW AVAILABLE: \<open>wfs_accord\<close>/\<open>wfs_rk\<close>), proving accessibility of
  each level-\<open>(n+1)\<close> principal \<open>D\<^sub>v b\<close> by an inner induction on the \<open>G\<^sub>v\<close>-content
  of \<open>b\<close>.  Formalizable pieces: (a) level-relativized STRAT-\<open>n\<close> (predecessors of
  level-\<open>\<le> n\<close> principals stay at level \<open>\<le> n\<close>; the STRAT-0 size induction should
  extend with an extra head-index-comparison case, since at level \<open>\<ge> 1\<close> head
  indices are merely \<open>\<le> n\<close>, not equal); (b) the inner \<open>G\<close>-recursion — the
  genuinely new content, needing the \<open>G\<^sub>v\<close>/\<open>lessBT\<close> interplay ([Buc1] §2 shape;
  cf. the proven \<open>m_buc1_3_2a_fseq_lt\<close> / \<open>m_buc1_3_2_OT_B_closed\<close> toolkit).
  \<^bold>\<open>Estimate\<close>: STRAT-\<open>n\<close> \<open>\<approx>\<close> 1 round; the collapse recursion (b) \<open>\<approx>\<close> 2--4 rounds
  of focused work with the wellorder/rank toolkit now in place; total 3--5 rounds.
  Main risk: the \<open>G\<^sub>v\<close> bookkeeping across levels (the \<open>u \<le> v\<close> branch structure of
  \<open>GBP\<close>) and the fact that level-\<open>n\<close> accessible parts must be compared as SETS of
  principals (no per-level normal-form theorem is available yet).\<close>

(* ===== end r51 buc1-semantic front (wfs_) ===== *)

(* ===== r52 merge: wt-y3 — buc1 jump r52: STRAT-n(lvP) refuted -> head-index STRAT; frag machinery; collapse-core residual + tuple-acc bricks (wfj_) ===== *)

(* ===== r52 merge: wt-y3 — buc1 level-jump front (wfj_): STRAT-n for wfs_lvP REFUTED
        (n >= 1); the TRUE downward-closed stratification is by HEAD index ===== *)

section \<open>r52 wfj — opening the level jump: STRAT-\<open>n\<close> refuted, head-index fragments\<close>

text \<open>Target: the single residual \<open>wfs_level_jump\<close> (r51).  The r51 feasibility plan
  proposed as step (a) the level-relativized STRAT-\<open>n\<close>:
  \<open>(q, p) \<in> RPrel \<Longrightarrow> wfs_lvP p \<le> n \<Longrightarrow> wfs_lvP q \<le> n\<close>.  \<^bold>\<open>This is FALSE for every
  \<open>n \<ge> 1\<close>\<close> (machine-checked below): in the strict head-comparison case \<open>u < v\<close> of
  \<open>lessBP\<close> the BODY of the smaller side is completely unconstrained by the comparison,
  and the \<open>G\<close>-condition does NOT bound its level — \<open>D\<^sub>0 (D\<^sub>k 0) \<in> OT\<close> for every \<open>k\<close>
  (its \<open>G\<^sub>0\<close>-set is \<open>{0\<^sub>B}\<close> and \<open>0\<^sub>B < D\<^sub>k 0\<close>) while \<open>D\<^sub>0 (D\<^sub>k 0) < D\<^sub>1 0\<close>.
  Semantically \<open>\<psi>\<^sub>0(\<Omega>\<^sub>k) < \<Omega>\<^sub>1\<close>: collapsed images of ALL levels sit below level 1.
  STRAT-0 (r51, \<open>wfs_strat0_P\<close>) survives because at level 0 the strict head case is
  impossible (\<open>u < 0\<close> has no solution in \<open>enat\<close>).

  The TRUE downward-closed stratification is by the HEAD index alone (the fragment
  "below \<open>\<Omega>\<^bsub>n+1\<^esub>\<close>"): \<open>lessBP\<close> compares heads first, so the head is weakly
  monotone along \<open>RPrel\<close> — no induction and no \<open>G\<close>-condition needed at all.\<close>

(* ===================================================================== *)
(* ===== r66 (OPUS 4.8) — buc1 MAJOR REFRAME: transcribe Buchholz's   ===== *)
(* ===== OWN proof of wf ([1] \<section>2, Lemmas 2.4--2.8), a FORWARD          ===== *)
(* ===== structural induction on TERM LENGTH (NOT the dead r65         ===== *)
(* ===== head-level / minimal-bad tower).  Prefix  bwo_  (Buchholz     ===== *)
(* ===== well-ordering).                                                ===== *)
(* ===================================================================== *)

section \<open>r66 bwo — Buchholz's own proof of \<open>wf RPrel\<close> ([1] \<section>2, Lemmas 2.4--2.8)\<close>

text \<open>
  \<^bold>\<open>The reframe.\<close>  r65 certified the head-level / minimal-bad-witness route
  DEAD (\<open>wcl_upper\<close> can hold only vacuously; the head-\<open>>n\<close> content is provably
  non-accessible under a bad witness).  Buchholz [1] avoids this entirely: he
  proves \<open>a \<in> W\<^sub>0\<close> by a FORWARD induction on the LENGTH of the term \<open>a\<close>
  (Lemma 2.7), with the impredicative content HIDDEN inside the definitions of
  the derived sets \<open>X\<^bsup>(a)\<^esup>\<close> / \<open>Xbar\<close> / \<open>W\<^sup>*\<close> and their closure lemmas 2.4/2.5/2.6.

  \<^bold>\<open>The correspondence to our machinery\<close> (established this round).  Our target is
  \<^term>\<open>wf RPrel\<close> (\<open>RPrel\<close> = \<open><\<close> on the \<open>D\<^sub>\<omega>\<close>-free \<open>OT\<close> principals); by
  \<open>wfs_wf_iff_all_acc\<close> and the tuple bridge \<open>wf RPrel \<longleftrightarrow> wf RTrel\<close> this is
  ``every \<open>OT\<^bsub>B\<^esub>\<close> term is \<open><\<close>-accessible'' = Buchholz 2.8 (\<open>a \<in> T\<^sub>0 \<Longrightarrow> a \<in> W\<^sub>0\<close>).
  The \<open>T\<close> / \<open><\<close> / \<open>a[z]\<close> / \<open>dom\<close> / \<open>a+b\<close> of [1] are our \<^typ>\<open>BT\<close> / \<open>lessBT\<close> /
  \<open>operB\<close> / \<open>domB\<close> / \<open>addBT\<close>; \<open>D\<^sub>v b\<close> is \<open>Dprin v b = Trm [DB v b]\<close>; \<open>W\<^sub>0\<close> is
  \<^term>\<open>Wellfounded.acc RTrel\<close>.  The five lemmas map as follows:

  \<^item> \<^bold>\<open>2.4(b)\<close>  \<open>a,b \<in> W\<^sub>v \<Longrightarrow> a+b \<in> W\<^sub>v\<close> (the addition / tuple-assembly layer):
    ALREADY PROVEN as \<open>wfj_tuple_acc\<close> (an \<open>OT\<^bsub>B\<^esub>\<close> term all of whose principal
    components are \<open>RPrel\<close>-accessible is \<open>RTrel\<close>-accessible).  Aliased below as
    \<open>bwo_2_4b_addition_closure\<close>.
  \<^item> \<^bold>\<open>2.7 case \<open>a = D\<^sub>v b\<close>\<close> (principal formation, the \<open>W\<^sub>v\<close>-membership step):
    ALREADY PROVEN as \<open>wfc_principal_acc_of_body\<close> (body \<open>RTrel\<close>-accessible +
    accessibility below the head \<open>\<Longrightarrow>\<close> the principal is \<open>RPrel\<close>-accessible).
    Aliased \<open>bwo_2_7_Dv_formation\<close>.
  \<^item> \<^bold>\<open>2.7/2.8 head recursion\<close> (\<open>A\<^sub>\<nu>(X)\<subseteq> X \<Longrightarrow> W\<^sub>\<nu>\<subseteq> X\<close> stratified by head):
    ALREADY PROVEN as \<open>wfc_wf_of_pbody_hyp\<close> — reduces \<^term>\<open>wf RPrel\<close> to
    ``every \<open>OT\<^bsub>B\<^esub>\<close> principal body is \<open>RTrel\<close>-accessible''.  Aliased
    \<open>bwo_2_8_head_recursion\<close>.
  \<^item> \<^bold>\<open>A1/A2\<close> (\<open>A\<^sub>\<nu>(W\<^sub>\<nu>)=W\<^sub>\<nu>\<close>, least-fixpoint induction): our \<^const>\<open>Wellfounded.acc\<close>
    IS the least fixpoint of ``all predecessors accessible \<open>\<Longrightarrow>\<close> accessible''
    (\<open>accI\<close> / \<open>acc.induct\<close>), so A1/A2 are free.
  \<^item> \<^bold>\<open>2.5\<close> (\<open>A\<^sub>\<nu>(X)\<subseteq> X \<Longrightarrow> A\<^sub>\<nu>(Xbar)\<subseteq> Xbar\<close>, the \<open>D\<^sub>\<nu>\<close>-closure crux) and
    \<^bold>\<open>2.6\<close> (\<open>A\<^sub>\<nu>(W\<^sup>*)\<subseteq> W\<^sup>*\<close>): the GENUINELY REMAINING content.  These build the
    below-head accessibility that r65 showed is unreachable head-locally; their
    proofs use the fundamental-sequence operator \<open>operB\<close>/\<open>domB\<close> essentially
    (2.6 case 4.2 sets \<open>z := D\<^sub>u b[1]\<close>).  Isolated here as the single residual
    \<open>bwo_Wstar_total\<close>.

  What this round contributes GREEN: the faithful transcription of the four
  derived-set definitions of [1] p.138 mapped to our term machinery, the three
  correspondence aliases above, and the main reduction \<open>bwo_2_2_wf\<close> that
  discharges \<^term>\<open>wf RPrel\<close> from \<open>bwo_Wstar_total\<close> — reusing the proven tuple
  layer and head recursion, so that the ONLY thing left is Buchholz's
  \<open>W\<^sup>*\<close>-totality (his 2.6 + the 2.7 length induction).\<close>

end
