theory Frontier_7_003
  imports P_7_1_paren_balance
begin

subsection \<open>§7.1 [Buc1] Lemma 2.1 — \<open>lessBT\<close> は狭義全順序\<close>

text \<open>The three properties of \<open>lessBT\<close> are proved by mutual structural induction
  on the \<open>BT\<close>/\<open>BP\<close> datatype.  For \<open>Trm ps\<close> we additionally induct on the list
  \<open>ps\<close>, using the fact (from \<open>BT_BP.induct\<close>) that \<open>lessBP\<close> has the property for
  all elements of \<open>ps\<close>.\<close>

\<comment> \<open>----  Irreflexivity  ----\<close>

\<comment> \<open>Helper: irrefl for lists — (\<forall>p \<in> set xs. \<not> lessBP p p) \<Longrightarrow> \<not> lessBT (Trm xs) (Trm xs)\<close>
lemma lessBT_list_irrefl:
  "(\<And>q. q \<in> set xs \<Longrightarrow> \<not> lessBP q q) \<Longrightarrow> \<not> lessBT (Trm xs) (Trm xs)"
proof (induction xs)
  case Nil thus ?case by simp
next
  case (Cons a rest)
  have na: "\<not> lessBP a a" using Cons.prems by simp
  have nr: "\<not> lessBT (Trm rest) (Trm rest)" using Cons.prems Cons.IH by simp
  thus ?case using na by simp
qed

lemma lessBT_lessBP_irrefl:
  "(\<not> lessBT t t) \<and> (\<not> lessBP p p)"
proof (induction rule: BT_BP.induct)
  case (Trm ps)
  \<comment> \<open>IH: \<forall>p \<in> set ps. \<not> lessBP p p\<close>
  have bp_irr: "\<And>q. q \<in> set ps \<Longrightarrow> \<not> lessBP q q"
    using Trm.IH by blast
  thus ?case using lessBT_list_irrefl[OF bp_irr] by blast
next
  case (DB u a)
  \<comment> \<open>IH: \<not> lessBT a a\<close>
  have "\<not> lessBP (DB u a) (DB u a)"
    using DB.IH by (simp add: order_less_irrefl)
  thus ?case by blast
qed

lemma lessBT_irrefl: "\<not> lessBT t t"
  using lessBT_lessBP_irrefl[where t = t and p = "DB 0 t"] by blast

\<comment> \<open>----  Transitivity  ----\<close>

text \<open>We prove transitivity by simultaneous induction on the function equation
  patterns, using \<open>lessBT_lessBP.induct\<close>.  In each case we reason about an
  arbitrary third argument \<open>c\<close> (resp. \<open>r\<close>).\<close>

lemma lessBT_trans:
  "lessBT a b \<Longrightarrow> lessBT b c \<Longrightarrow> lessBT a c"
and lessBP_trans:
  "lessBP p q \<Longrightarrow> lessBP q r \<Longrightarrow> lessBP p r"
proof (induction a b and p q arbitrary: c and r rule: lessBT_lessBP.induct)
  \<comment> \<open>Case 1: lessBT (Trm []) (Trm bs) — the empty list is smallest\<close>
  case (1 bs)
  \<comment> \<open>Goal: lessBT (Trm []) (Trm bs) \<Longrightarrow> lessBT (Trm bs) c \<Longrightarrow> lessBT (Trm []) c\<close>
  then show "\<And>c. lessBT (Trm []) (Trm bs) \<Longrightarrow> lessBT (Trm bs) c \<Longrightarrow>
               lessBT (Trm []) c"
  proof -
    fix c
    assume h2: "lessBT (Trm bs) c"
    \<comment> \<open>c must be non-empty; if c = Trm [], then lessBT (Trm bs) (Trm []) = False\<close>
    have "c \<noteq> Trm []"
    proof
      assume "c = Trm []"
      with h2 show False by (cases bs) auto
    qed
    thus "lessBT (Trm []) c" by (cases c) auto
  qed
next
  \<comment> \<open>Case 2: lessBT (Trm (a # as)) (Trm []) = False, premiss is vacuous\<close>
  case (2 a as)
  then show "\<And>c. lessBT (Trm (a # as)) (Trm []) \<Longrightarrow> lessBT (Trm []) c \<Longrightarrow>
               lessBT (Trm (a # as)) c"
    by simp
next
  \<comment> \<open>Case 3: lessBT (Trm (a # as)) (Trm (b # bs)): lex on head then tail\<close>
  case (3 a as b bs)
  then show "\<And>c. lessBT (Trm (a # as)) (Trm (b # bs)) \<Longrightarrow>
               lessBT (Trm (b # bs)) c \<Longrightarrow>
               lessBT (Trm (a # as)) c"
  proof -
    fix c
    assume h1: "lessBT (Trm (a # as)) (Trm (b # bs))"
    assume h2: "lessBT (Trm (b # bs)) c"
    obtain cs where ceq: "c = Trm cs" by (cases c)
    show "lessBT (Trm (a # as)) c"
    proof (cases cs)
      case Nil
      with h2 ceq show ?thesis by simp
    next
      case (Cons d ds)
      \<comment> \<open>h1: lessBP a b \<or> (a=b \<and> lessBT (Trm as) (Trm bs))
          h2: lessBP b d \<or> (b=d \<and> lessBT (Trm bs) (Trm ds))
          3.IH(1): IH for the BP recursive call (with arbitrary: r)
          3.IH(2): IH for the BT recursive call (with arbitrary: c)\<close>
      show ?thesis
      proof (cases "lessBP a b")
        case True
        \<comment> \<open>lessBP a b, need lessBP a d or (a=d and ...)\<close>
        show ?thesis
        proof (cases "lessBP b d")
          case True
          have "lessBP a d" using "3.IH"(1)[where r=d] \<open>lessBP a b\<close> True by blast
          with ceq Cons show ?thesis by auto
        next
          case False
          \<comment> \<open>\<not>lessBP b d, so b=d \<and> lessBT (Trm bs) (Trm ds) from h2\<close>
          with h2 ceq Cons have bd_eq: "b = d" and bt_bsds: "lessBT (Trm bs) (Trm ds)"
            by auto
          from True bd_eq have "lessBP a d" by simp
          with ceq Cons show ?thesis by auto
        qed
      next
        case False
        \<comment> \<open>\<not>lessBP a b, so a=b \<and> lessBT (Trm as) (Trm bs)\<close>
        with h1 have ab_eq: "a = b" and bt_asbs: "lessBT (Trm as) (Trm bs)" by auto
        show ?thesis
        proof (cases "lessBP b d")
          case True
          with ab_eq ceq Cons show ?thesis by auto
        next
          case False
          \<comment> \<open>\<not>lessBP b d, so b=d \<and> lessBT (Trm bs) (Trm ds)\<close>
          with h2 ceq Cons have bd_eq: "b = d" and bt_bsds: "lessBT (Trm bs) (Trm ds)"
            by auto
          have "lessBT (Trm as) (Trm ds)"
            using "3.IH"(2)[where c = "Trm ds"] bt_asbs bt_bsds by blast
          with ab_eq bd_eq ceq Cons show ?thesis by auto
        qed
      qed
    qed
  qed
next
  \<comment> \<open>Case 4: lessBP (DB u a) (DB v b): lex on (u, a)\<close>
  case (4 u a v b)
  then show "\<And>r. lessBP (DB u a) (DB v b) \<Longrightarrow> lessBP (DB v b) r \<Longrightarrow>
               lessBP (DB u a) r"
  proof -
    fix r
    assume h1: "lessBP (DB u a) (DB v b)"
    assume h2: "lessBP (DB v b) r"
    obtain w d where req: "r = DB w d" by (cases r)
    with h1 h2 "4.IH"[where c = d]
    show "lessBP (DB u a) r"
      unfolding req
      by (auto intro: order_less_trans)
  qed
qed

\<comment> \<open>----  Trichotomy  ----\<close>

\<comment> \<open>Helper: given BP-trichotomy for all elements of xs, BT-trichotomy for Trm xs.\<close>
lemma lessBT_list_total:
  "(\<And>p q. p \<in> set xs \<Longrightarrow> lessBP p q \<or> p = q \<or> lessBP q p) \<Longrightarrow>
   \<forall>ys. lessBT (Trm xs) (Trm ys) \<or> Trm xs = Trm ys \<or> lessBT (Trm ys) (Trm xs)"
proof (induction xs)
  case Nil
  thus ?case by (intro allI; cases) auto
next
  case (Cons a as')
  \<comment> \<open>Cons.prems: \<And>p q. p \<in> set (a # as') \<Longrightarrow> lessBP p q \<or> p = q \<or> lessBP q p
      Cons.IH: (\<And>p q. p \<in> set as' \<Longrightarrow> ...) \<Longrightarrow> \<forall>ys. lessBT (Trm as') ... \<or> ...\<close>
  have bp_a: "\<And>q. lessBP a q \<or> a = q \<or> lessBP q a"
    using Cons.prems by simp
  have bt_as': "\<And>ys. lessBT (Trm as') (Trm ys) \<or> Trm as' = Trm ys \<or> lessBT (Trm ys) (Trm as')"
    using Cons.IH Cons.prems by simp
  show ?case
  proof
    fix ys
    show "lessBT (Trm (a # as')) (Trm ys) \<or> Trm (a # as') = Trm ys \<or>
          lessBT (Trm ys) (Trm (a # as'))"
    proof (cases ys)
      case Nil thus ?thesis by simp
    next
      case (Cons d ds)
      show ?thesis unfolding Cons
        using bp_a[of d] bt_as'[of ds] by auto
    qed
  qed
qed

lemma lessBT_lessBP_total:
  "(\<forall>b. lessBT a b \<or> a = b \<or> lessBT b a) \<and>
   (\<forall>q. lessBP p q \<or> p = q \<or> lessBP q p)"
proof (induction rule: BT_BP.induct)
  case (Trm as)
  \<comment> \<open>IH: \<forall>p \<in> set as. (\<forall>b. ...) \<and> (\<forall>q. lessBP p q \<or> p = q \<or> lessBP q p)\<close>
  have bp_tri: "\<And>p q. p \<in> set as \<Longrightarrow> lessBP p q \<or> p = q \<or> lessBP q p"
    using Trm.IH by blast
  have bt_tri_list: "\<forall>bs. lessBT (Trm as) (Trm bs) \<or> Trm as = Trm bs \<or> lessBT (Trm bs) (Trm as)"
    using lessBT_list_total[where xs = as, OF bp_tri] by blast
  have bt_tri: "\<forall>b. lessBT (Trm as) b \<or> Trm as = b \<or> lessBT b (Trm as)"
    using bt_tri_list by (metis BT.exhaust)
  thus ?case by blast
next
  case (DB u a)
  \<comment> \<open>IH: (\<forall>b. lessBT a b \<or> a = b \<or> lessBT b a) \<and> ...\<close>
  have bt_tri: "\<forall>b. lessBT a b \<or> a = b \<or> lessBT b a"
    using DB.IH by blast
  have bp_tri: "\<forall>q. lessBP (DB u a) q \<or> DB u a = q \<or> lessBP q (DB u a)"
  proof
    fix q
    obtain v b where qeq: "q = DB v b" by (cases q)
    show "lessBP (DB u a) q \<or> DB u a = q \<or> lessBP q (DB u a)"
      unfolding qeq
      using bt_tri[rule_format, of b]
      by (metis lessBP.simps linorder_less_linear)
  qed
  thus ?case by blast
qed

lemma lessBT_total: "lessBT a b \<or> a = b \<or> lessBT b a"
  using lessBT_lessBP_total[where a = a and p = "DB 0 a"] by blast

end
