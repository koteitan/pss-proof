theory Frontier_7_054
  imports Support_7_049
begin

section \<open>§7.2 命題（scb分解と基本列の関係） conjunct (2): kind-1 / xseq-tower
  transport for the GENERAL marked principal \<open>c\<^sub>2 = D\<^sub>u(body)\<close> (non-empty
  \<open>s\<^sub>0\<close>/\<open>b\<^sub>0\<close>), article-faithful \<open>n+1\<close> form (A24 retracted)\<close>

text \<open>
  Generalises @{thm [source] m_7_2_scb_fseq_kind1_basic} (the \<open>s\<^sub>0 = b\<^sub>0 = ()\<close>
  case \<open>c\<^sub>2 = D\<^sub>u(D\<^sub>v 0)\<close>) to a marked principal \<open>c\<^sub>2 = D\<^sub>u(body)\<close> whose body has
  the marked leaf \<open>D\<^sub>v 0\<close> on its trailing right spine, prefixed by \<open>s\<^sub>0\<close> and
  suffixed by an all-\<open>RP\<close> tail \<open>b\<^sub>0\<close> at the flat level
  (\<open>flat(body) = s\<^sub>0 \<frown> flat(D\<^sub>v 0) \<frown> b\<^sub>0\<close>).  A24 is retracted: the
  earlier \<open>n\<close>-form came from misreading \<open>([].4)(ii)\<close>.  The article's
  \<open>(s\<^sub>0 D\<^bsub>v-1\<^esub>)\<^bsup>n+1\<^esup>\<close> form is empirically validated 48/48
  (\<open>s\<^sub>0 \<noteq> ()\<close>) and 12/12 (\<open>b\<^sub>0 \<noteq> ()\<close>) in
  @{path \<open>python/scb_fseq_kind1_check.py\<close>}.

  The OUTER spine \<open>s\<^sub>1\<close>/\<open>b\<^sub>1\<close> is transported exactly as in the basic case by
  @{thm [source] operB_scb_spine} (the marked principal \<open>c\<^sub>2 = D\<^sub>u(body)\<close> has
  \<open>domB c\<^sub>2 = NatSet\<close> for \<open>u < v\<close>).  The new work is the INNER evaluation of
  \<open>operB c\<^sub>2 (numBT n)\<close> via the \<open>xseq\<close> tower over the multi-component \<open>body\<close>:
  \<open>x\<^sub>0 = D\<^bsub>v-1\<^esub> 0\<close>, \<open>x\<^bsub>i+1\<^esub> = operB body (D\<^bsub>v-1\<^esub> x\<^sub>i)\<close>, and \<open>operB c\<^sub>2 (numBT n)
  = D\<^sub>u x\<^sub>n\<close>.  The tower step rests on a \<open>T\<^bsub>v-1\<^esub>\<close>-domain flat-transport for the
  body (\<open>operB_TBv_body_spine\<close> below), the \<open>T\<^bsub>u\<^esub>\<close>-analogue of
  @{thm [source] operB_scb_spine}: the marked principal is the leaf \<open>D\<^sub>v 0\<close>
  (\<open>domB(D\<^sub>v 0) = T\<^bsub>v-1\<^esub>\<close>) rather than a \<open>NatSet\<close>-domain principal.\<close>

text \<open>\<open>operB\<close>-domain for a single principal \<open>D\<^sub>w c\<close> over a \<open>T\<^bsub>m\<^esub>\<close>-domain body
  \<open>c\<close> with \<open>m < w\<close> and \<open>operB c z\<close> defined: the \<open>([].4)(iii)\<close> else-branch
  \<open>D\<^sub>w(operB c z)\<close>.  The \<open>xseq\<close>-guard obligations are vacuous (\<open>w \<le> u'\<close> with
  \<open>domB c = T\<^bsub>u'\<^esub>\<close> forces \<open>u' = m\<close>, \<open>w \<le> m\<close>, against \<open>m < w\<close>); the else-guard
  obligations contradict the supplied \<open>operB\<close>-domain hypothesis \<open>domc\<close>.
  The \<open>T\<^bsub>m\<^esub>\<close>-analogue of @{thm [source] operB_dom_NatSet_principal}.\<close>

lemma operB_dom_TBv_principal_aux:
  assumes dc: "domB c = TBv (enat m)" and cne: "c \<noteq> Trm []"
    and mw: "enat m < w"
    and domc: "domB_operB_xseq_dom (Inr (Inl (c, z)))"
  shows "domB_operB_xseq_dom (Inr (Inl (Trm [DB w c], z)))"
proof (rule domB_operB_xseq.domintros(2))
  \<comment> \<open>(0) \<open>domB c\<close> total\<close>
  show "domB_operB_xseq_dom (Inl x2)"
    if "Trm [DB w c] = Trm [DB x1 x2]" "x2 \<noteq> Trm []" for x1 x2
    by (rule domB_dom_all)
next
  \<comment> \<open>(1) \<open>db = {0}\<close> branch: vacuous (\<open>domB c = T\<^bsub>m\<^esub> \<noteq> {0}\<close>)\<close>
  show "domB_operB_xseq_dom (Inr (Inl (x2, Trm [])))"
    if "Trm [DB w c] = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "{Trm []} = domB x2" for x1 x2
  proof -
    have "x2 = c" using that(1) by simp
    hence "{Trm []} = TBv (enat m)" using that(3) dc by simp
    thus ?thesis using zero_set_neq_TBv by simp
  qed
next
  \<comment> \<open>(2) \<open>xseq\<close>-guard: \<open>w \<le> u'\<close>, \<open>domB c = T\<^bsub>u'\<^esub>\<close> forces \<open>w \<le> m\<close>, against \<open>m < w\<close>\<close>
  show "xb = Trm []"
    if "Trm [DB w c] = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "x1 \<le> enat u'"
       "domB x2 = TBv (enat u')"
       "\<not> domB_operB_xseq_dom (Inr (Inr (x2, enat (tbvIdx (TBv (enat u'))), numNat z)))"
       "xb \<in> TBv (enat u')" for x1 x2 u' xb
  proof -
    have x2c: "x2 = c" and x1w: "x1 = w" using that(1) by simp_all
    have "TBv (enat m) = TBv (enat u')" using dc that(4) x2c by simp
    hence "m = u'" by (auto dest: TBv_enat_inj)
    hence "w \<le> enat m" using that(3) x1w by simp
    thus ?thesis using mw by simp
  qed
next
  \<comment> \<open>(3) \<open>0 \<in> T\<^bsub>u'\<^esub>\<close>: trivially true\<close>
  show "Trm [] \<in> TBv (enat u')"
    if "Trm [DB w c] = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "x1 \<le> enat u'"
       "domB x2 = TBv (enat u')"
       "\<not> domB_operB_xseq_dom (Inr (Inr (x2, enat (tbvIdx (TBv (enat u'))), numNat z)))"
       for x1 x2 u'
    by (simp add: TBv_def)
next
  \<comment> \<open>(4) inner \<open>operB c (xseq \<dots>)\<close> guard: same vacuity as (2)\<close>
  show "xb = Trm []"
    if "Trm [DB w c] = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "x1 \<le> enat u'"
       "domB x2 = TBv (enat u')"
       "\<not> domB_operB_xseq_dom
            (Inr (Inl (x2, xseq x2 (enat (tbvIdx (TBv (enat u')))) (numNat z))))"
       "xb \<in> TBv (enat u')" for x1 x2 u' xb
  proof -
    have x2c: "x2 = c" and x1w: "x1 = w" using that(1) by simp_all
    have "TBv (enat m) = TBv (enat u')" using dc that(4) x2c by simp
    hence "m = u'" by (auto dest: TBv_enat_inj)
    hence "w \<le> enat m" using that(3) x1w by simp
    thus ?thesis using mw by simp
  qed
next
  \<comment> \<open>(5) \<open>0 \<in> T\<^bsub>u'\<^esub>\<close> for the inner call\<close>
  show "Trm [] \<in> TBv (enat u')"
    if "Trm [DB w c] = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "x1 \<le> enat u'"
       "domB x2 = TBv (enat u')"
       "\<not> domB_operB_xseq_dom
            (Inr (Inl (x2, xseq x2 (enat (tbvIdx (TBv (enat u')))) (numNat z))))"
       for x1 x2 u'
    by (simp add: TBv_def)
next
  \<comment> \<open>(6) \<open>else\<close>-guard: \<open>\<not> dom(operB c z)\<close> contradicts @{thm [source] domc}\<close>
  show "xb = Trm []"
    if "Trm [DB w c] = Trm [DB x1 x2]" "x2 \<noteq> Trm []"
       "\<forall>u. x1 \<le> enat u \<longrightarrow> domB x2 \<noteq> TBv (enat u)"
       "\<not> domB_operB_xseq_dom (Inr (Inl (x2, z)))"
       "xb \<in> domB x2" for x1 x2 xb
  proof -
    have "x2 = c" using that(1) by simp
    hence "\<not> domB_operB_xseq_dom (Inr (Inl (c, z)))" using that(4) by simp
    thus ?thesis using domc by simp
  qed
next
  \<comment> \<open>(7) \<open>0 \<in> domB c\<close> else-guard: same, vacuous via @{thm [source] domc}\<close>
  show "Trm [] \<in> domB x2"
    if "Trm [DB w c] = Trm [DB x1 x2]" "x2 \<noteq> Trm []"
       "\<forall>u. x1 \<le> enat u \<longrightarrow> domB x2 \<noteq> TBv (enat u)"
       "\<not> domB_operB_xseq_dom (Inr (Inl (x2, z)))" for x1 x2
  proof -
    have "x2 = c" using that(1) by simp
    hence "\<not> domB_operB_xseq_dom (Inr (Inl (c, z)))" using that(4) by simp
    thus ?thesis using domc by simp
  qed
next
  \<comment> \<open>(8) two-component multi: vacuous (single principal)\<close>
  show "domB_operB_xseq_dom (Inr (Inl (Trm [x21a], z)))"
    if "Trm [DB w c] = Trm [DB x1 x2, x21a]" for x1 x2 x21a
    using that by simp
next
  \<comment> \<open>(9) \<open>(\<ge>3)\<close>-component multi: vacuous (single principal)\<close>
  show "domB_operB_xseq_dom (Inr (Inl (Trm [last x22a], z)))"
    if "Trm [DB w c] = Trm (DB x1 x2 # x21a # x22a)" "x22a \<noteq> []" for x1 x2 x21a x22a
    using that(1) by simp
qed

text \<open>\<open>T\<^bsub>m\<^esub>\<close>-domain principal unfold (the \<open>([].4)(iii)\<close> branch): for a body
  \<open>c\<close> with \<open>domB c = T\<^bsub>m\<^esub>\<close>, \<open>c \<noteq> 0\<close>, and a head \<open>w\<close> with \<open>m < w\<close>, the guard
  \<open>(\<exists>u'. w \<le> u' \<and> domB c = T\<^bsub>u'\<^esub>)\<close> is false (it would force \<open>w \<le> m\<close>), so
  \<open>operB (D\<^sub>w c) z = D\<^sub>w (operB c z)\<close>.\<close>

lemma operB_TBv_principal_unfold:
  assumes dc: "domB c = TBv (enat m)" and cne: "c \<noteq> Trm []"
    and mw: "enat m < w"
    and domc: "domB_operB_xseq_dom (Inr (Inl (c, z)))"
  shows "operB (Trm [DB w c]) z = Dprin w (operB c z)"
proof -
  have dom: "domB_operB_xseq_dom (Inr (Inl (Trm [DB w c], z)))"
    by (rule operB_dom_TBv_principal_aux[OF dc cne mw domc])
  have nguard: "\<not> (\<exists>u'. w \<le> enat u' \<and> domB c = TBv (enat u'))"
  proof
    assume "\<exists>u'. w \<le> enat u' \<and> domB c = TBv (enat u')"
    then obtain u' where wu': "w \<le> enat u'" and du': "domB c = TBv (enat u')" by blast
    have "TBv (enat m) = TBv (enat u')" using dc du' by simp
    hence "m = u'" by (auto dest: TBv_enat_inj)
    hence "w \<le> enat m" using wu' by simp
    thus False using mw by simp
  qed
  have nz: "domB c \<noteq> {Trm []}" using dc zero_set_neq_TBv by auto
  have "operB (Trm [DB w c]) z
          = (let dbb = domB c in
             if dbb = {Trm []} then multBT (Dprin w (operB c (Trm []))) (numNat z + 1)
             else if (\<exists>u. w \<le> enat u \<and> dbb = TBv (enat u))
                  then Dprin w (operB c (xseq c (enat (tbvIdx dbb)) (numNat z)))
             else Dprin w (operB c z))"
    using operB.psimps[OF dom] cne by simp
  also have "\<dots> = (if domB c = {Trm []} then multBT (Dprin w (operB c (Trm []))) (numNat z + 1)
                   else if (\<exists>u. w \<le> enat u \<and> domB c = TBv (enat u))
                        then Dprin w (operB c (xseq c (enat (tbvIdx (domB c))) (numNat z)))
                   else Dprin w (operB c z))"
    by (simp add: Let_def)
  also have "\<dots> = (if (\<exists>u. w \<le> enat u \<and> domB c = TBv (enat u))
                   then Dprin w (operB c (xseq c (enat (tbvIdx (domB c))) (numNat z)))
                   else Dprin w (operB c z))"
    by (rule if_not_P[OF nz])
  also have "\<dots> = Dprin w (operB c z)"
    by (rule if_not_P[OF nguard])
  finally show ?thesis .
qed

text \<open>\<open>operB\<close>-domain spine heredity for a \<open>T\<^bsub>m\<^esub>\<close>-domain marked principal.  The
  \<open>T\<^bsub>m\<^esub>\<close>-analogue of @{thm [source] operB_dom_spine_aux}: heredity of \<open>domB body
  = T\<^bsub>m\<^esub>\<close> down the right spine is NOT automatic (\<open>T\<^bsub>m\<^esub>\<close> is not absorbing like
  \<open>NatSet\<close>), so we carry \<open>domB t = T\<^bsub>m\<^esub>\<close> as a premise and descend with
  @{thm [source] domB_single_TBv_struct} (which also yields \<open>m < w\<close> for each
  spine head \<open>w\<close>); the principal step is @{thm [source] operB_dom_TBv_principal_aux}.\<close>

lemma operB_dom_TBv_body_spine_aux:
  "\<And>s b. scb_decomp t s (flatBT (Trm [cp])) b
        \<Longrightarrow> domB (Trm [cp]) = TBv (enat m) \<Longrightarrow> dfree_BP cp
        \<Longrightarrow> domB t = TBv (enat m)
        \<Longrightarrow> domB_operB_xseq_dom (Inr (Inl (Trm [cp], z)))
        \<Longrightarrow> domB_operB_xseq_dom (Inr (Inl (t, z)))"
proof (induction t rule: measure_induct_rule[where f=size])
  case (less t s b)
  have tne: "t \<noteq> Trm []"
  proof
    assume z: "t = Trm []"
    have "flatBT t = s @ flatBP cp @ b" using less.prems(1) by (simp add: scb_decomp_def)
    moreover have "flatBT t = [Zsym]" using z by simp
    moreover obtain w cb where "cp = DB w cb" by (cases cp) auto
    ultimately show False by (cases s) auto
  qed
  obtain sc bc where comp: "flatBP (last (untrm t)) = sc @ flatBP cp @ bc"
      and rbc: "\<forall>x \<in> set bc. x = RP"
    using scb_to_last_component[OF less.prems(1) tne] by blast
  obtain w lb where lpw: "last (untrm t) = DB w lb"
    by (cases "last (untrm t)") auto
  obtain ts where tT: "t = Trm ts" by (cases t) auto
  have tsne: "ts \<noteq> []" using tne tT by auto
  have lastEq: "last ts = DB w lb" using lpw tT by simp
  have flateq: "Dsym w # flatBT lb = sc @ flatBP cp @ bc"
    using comp lpw by simp
  obtain w' cb' where cpw: "cp = DB w' cb'" by (cases cp) auto
  \<comment> \<open>\<open>domB(Trm[DB w lb]) = domB t = T\<^bsub>m\<^esub>\<close> (\<open>domB\<close> reads the last component)\<close>
  have domLastComp: "domB (Trm [DB w lb]) = TBv (enat m)"
  proof -
    have "domB t = domB (Trm [last ts])"
      unfolding tT by (rule domB_last_component[OF tsne])
    thus ?thesis using lastEq less.prems(4) by simp
  qed
  have domLast: "domB_operB_xseq_dom (Inr (Inl (Trm [DB w lb], z)))"
  proof (cases "sc = []")
    case True
    have e: "flatBP (DB w lb) @ [] = flatBP cp @ bc" using flateq True by simp
    have "flatBP (DB w lb) = flatBP cp \<and> [] = bc"
      using flatinj_flatBP_cancel[OF e] by blast
    hence cpEq: "DB w lb = cp" using m_7_flatBT_inj cpw by simp
    show ?thesis using cpEq less.prems(5) by simp
  next
    case False
    obtain sc1 where sc1: "sc = Dsym w # sc1"
      using flateq False by (cases sc) auto
    have aeq: "flatBT lb = sc1 @ flatBP cp @ bc" using flateq sc1 by simp
    have lbne: "lb \<noteq> Trm []"
    proof
      assume "lb = Trm []"
      hence "flatBT lb = [Zsym]" by simp
      thus False using aeq cpw by (cases sc1) auto
    qed
    have scbLb: "scb_decomp lb sc1 (flatBT (Trm [cp])) bc"
      unfolding scb_decomp_def using aeq rbc less.prems(3)
      by (auto simp: isPTB_str_def intro: exI[of _ cp])
    \<comment> \<open>\<open>domB lb = T\<^bsub>m\<^esub>\<close> and \<open>m < w\<close> from @{thm [source] domB_single_TBv_struct}\<close>
    have struct: "domB lb = TBv (enat m)
                    \<and> \<not> (\<exists>u'. w \<le> enat u' \<and> domB lb = TBv (enat u'))"
      by (rule domB_single_TBv_struct[OF domLastComp lbne])
    have domLbTBv: "domB lb = TBv (enat m)" using struct by (rule conjunct1)
    have nguard: "\<not> (\<exists>u'. w \<le> enat u' \<and> domB lb = TBv (enat u'))"
      using struct by (rule conjunct2)
    have mw: "enat m < w"
    proof (rule ccontr)
      assume "\<not> enat m < w"
      hence "w \<le> enat m" by simp
      hence "\<exists>u'. w \<le> enat u' \<and> domB lb = TBv (enat u')"
        using domLbTBv by blast
      thus False using nguard by simp
    qed
    have szlt: "size lb < size t"
      using rnsub_size_arg_lt'[of ts w lb] lastEq tsne tT by simp
    have domLb: "domB_operB_xseq_dom (Inr (Inl (lb, z)))"
      by (rule less.IH[OF szlt scbLb less.prems(2) less.prems(3) domLbTBv less.prems(5)])
    show ?thesis
      by (rule operB_dom_TBv_principal_aux[OF domLbTBv lbne mw domLb])
  qed
  show ?case
  proof (cases "tl ts")
    case Nil
    have ts1: "ts = [DB w lb]" using tsne lastEq Nil by (cases ts) auto
    show ?thesis using domLast tT ts1 by simp
  next
    case (Cons q qs)
    obtain p0 where tdecomp: "ts = p0 # q # qs" using Cons tsne by (cases ts) auto
    have lastp: "last (p0 # q # qs) = DB w lb" using lastEq tdecomp tT by simp
    have domLast': "domB_operB_xseq_dom (Inr (Inl (Trm [last (p0 # q # qs)], z)))"
      using domLast lastp by simp
    have "domB_operB_xseq_dom (Inr (Inl (Trm (p0 # q # qs), z)))"
      by (rule operB_dom_multi[OF domLast'])
    thus ?thesis using tT tdecomp by simp
  qed
qed

text \<open>\<open>T\<^bsub>m\<^esub>\<close>-domain flat spine transport (the inner \<open>xseq\<close>-step engine): the
  \<open>T\<^bsub>m\<^esub>\<close>-analogue of @{thm [source] operB_scb_spine}.  For a body \<open>t\<close> whose
  marked principal \<open>cp\<close> has \<open>domB(Trm[cp]) = T\<^bsub>m\<^esub>\<close> (in our use \<open>cp = D\<^sub>v 0\<close>,
  \<open>m = v-1\<close>), and whose \<open>operB\<close>-image is a single principal \<open>Trm[rp]\<close> (true
  when the second argument is the single principal \<open>D\<^bsub>v-1\<^esub> x\<^sub>i\<close> of the tower),
  \<open>flat(operB t z) = s \<frown> flat(operB(Trm[cp]) z) \<frown> b\<close>.  Same right-spine
  induction as @{thm [source] operB_scb_spine}; the spine-principal unfold is
  @{thm [source] operB_TBv_principal_unfold}, and \<open>domB lb = T\<^bsub>m\<^esub>\<close>/\<open>m < w\<close>
  come from @{thm [source] domB_single_TBv_struct}.\<close>

lemma operB_TBv_body_spine:
  "\<And>s b. scb_decomp t s (flatBT (Trm [cp])) b
        \<Longrightarrow> domB (Trm [cp]) = TBv (enat m) \<Longrightarrow> dfree_BP cp
        \<Longrightarrow> domB t = TBv (enat m)
        \<Longrightarrow> domB_operB_xseq_dom (Inr (Inl (Trm [cp], z)))
        \<Longrightarrow> operB (Trm [cp]) z = Trm [rp]
        \<Longrightarrow> flatBT (operB t z) = s @ flatBT (operB (Trm [cp]) z) @ b"
proof (induction t rule: measure_induct_rule[where f=size])
  case (less t s b)
  have tne: "t \<noteq> Trm []"
  proof
    assume z: "t = Trm []"
    have "flatBT t = s @ flatBP cp @ b" using less.prems(1) by (simp add: scb_decomp_def)
    moreover have "flatBT t = [Zsym]" using z by simp
    moreover obtain w cb where "cp = DB w cb" by (cases cp) auto
    ultimately show False by (cases s) auto
  qed
  obtain sc bc where comp: "flatBP (last (untrm t)) = sc @ flatBP cp @ bc"
      and rbc: "\<forall>x \<in> set bc. x = RP"
    using scb_to_last_component[OF less.prems(1) tne] by blast
  obtain w lb where lpw: "last (untrm t) = DB w lb"
    by (cases "last (untrm t)") auto
  obtain ts where tT: "t = Trm ts" by (cases t) auto
  have tsne: "ts \<noteq> []" using tne tT by auto
  have lastEq: "last ts = DB w lb" using lpw tT by simp
  have flateq: "Dsym w # flatBT lb = sc @ flatBP cp @ bc"
    using comp lpw by simp
  obtain w' cb' where cpw: "cp = DB w' cb'" by (cases cp) auto
  have flatt: "flatBT t = s @ flatBP cp @ b"
    using less.prems(1) by (simp add: scb_decomp_def)
  have iptcp: "isPTB_str (flatBT (Trm [cp]))"
    using less.prems(3) by (auto simp: isPTB_str_def)
  have rb: "\<forall>x \<in> set b. x = RP" using less.prems(1) by (simp add: scb_decomp_def)
  have ds_t: "domB_operB_xseq_dom (Inr (Inl (t, z)))"
    by (rule operB_dom_TBv_body_spine_aux[OF less.prems(1) less.prems(2) less.prems(3)
                                              less.prems(4) less.prems(5)])
  have operimg: "flatBT (operB (Trm [cp]) z) = flatBP rp"
    using less.prems(6) by simp
  \<comment> \<open>\<open>domB(Trm[DB w lb]) = domB t = T\<^bsub>m\<^esub>\<close>\<close>
  have domLastComp: "domB (Trm [DB w lb]) = TBv (enat m)"
  proof -
    have "domB t = domB (Trm [last ts])"
      unfolding tT by (rule domB_last_component[OF tsne])
    thus ?thesis using lastEq less.prems(4) by simp
  qed
  show ?case
  proof (cases "sc = []")
    case True
    have e: "flatBP (DB w lb) @ [] = flatBP cp @ bc" using flateq True by simp
    have cancel: "flatBP (DB w lb) = flatBP cp \<and> [] = bc"
      using flatinj_flatBP_cancel[OF e] by blast
    have cpEq: "DB w lb = cp" using cancel m_7_flatBT_inj cpw by simp
    show ?thesis
    proof (cases "tl ts")
      case Nil
      have ts1: "ts = [DB w lb]" using tsne lastEq Nil by (cases ts) auto
      have tcp: "t = Trm [cp]" using tT ts1 cpEq by simp
      have "flatBT t = flatBP cp" using tcp by simp
      hence ecollapse: "s @ flatBP cp @ b = flatBP cp" using flatt by simp
      have "length s + length b = 0"
      proof -
        have "length s + length (flatBP cp) + length b = length (flatBP cp)"
          using ecollapse by (metis length_append add.assoc)
        thus ?thesis by simp
      qed
      hence sb: "s = [] \<and> b = []" by simp
      show ?thesis using tcp sb by simp
    next
      case (Cons q qs)
      obtain p0 where tdecomp: "ts = p0 # q # qs" using Cons tsne by (cases ts) auto
      let ?rs = "butlast (p0 # q # qs)"
      have rsne: "?rs \<noteq> []" by simp
      have lastp: "last (p0 # q # qs) = DB w lb" using lastEq tdecomp tT by simp
      have lr: "p0 # q # qs = ?rs @ [DB w lb]"
        using lastp by (metis append_butlast_last_id list.distinct(1))
      have ds_t': "domB_operB_xseq_dom (Inr (Inl (Trm (p0 # q # qs), z)))"
        using ds_t tT tdecomp by simp
      have peelP: "operB (Trm (p0 # q # qs)) z
                    = addBT (Trm ?rs) (operB (Trm [last (p0 # q # qs)]) z)"
        by (rule operB_dom_multi_peel[OF ds_t'])
      have peel: "operB t z
                    = addBT (Trm ?rs) (operB (Trm [last (p0 # q # qs)]) z)"
        using peelP tT tdecomp by simp
      have opercp: "operB (Trm [last (p0 # q # qs)]) z = Trm [rp]"
        using lastp cpEq less.prems(6) by simp
      have operT: "operB t z = Trm (?rs @ [rp])"
        using peel opercp tdecomp by simp
      have flatt2: "flatBT t = Wpre ?rs @ flatBP (DB w lb) @ [RP]"
      proof -
        have "flatBT t = flatBT (Trm (?rs @ [DB w lb]))"
          using tT tdecomp arg_cong[where f="\<lambda>xs. flatBT (Trm xs)", OF lr] by simp
        also have "\<dots> = Wpre ?rs @ flatBP (DB w lb) @ [RP]"
          by (rule flatBT_multi_last[OF rsne])
        finally show ?thesis .
      qed
      have flatcp: "flatBT t = Wpre ?rs @ flatBP cp @ [RP]"
        using flatt2 cpEq by simp
      have scbWpre: "scb_decomp t (Wpre ?rs) (flatBT (Trm [cp])) [RP]"
        unfolding scb_decomp_def using flatcp iptcp by simp
      have sbeq: "s = Wpre ?rs \<and> b = [RP]"
        by (rule m_7_2_scb_unique_sb[OF less.prems(1) scbWpre tne])
      have "flatBT (operB t z) = Wpre ?rs @ flatBP rp @ [RP]"
        using operT flatBT_multi_last[OF rsne, of rp] by simp
      also have "\<dots> = Wpre ?rs @ flatBT (operB (Trm [cp]) z) @ [RP]"
        using operimg by simp
      also have "\<dots> = s @ flatBT (operB (Trm [cp]) z) @ b" using sbeq by simp
      finally show ?thesis .
    qed
  next
    case False
    obtain sc1 where sc1: "sc = Dsym w # sc1"
      using flateq False by (cases sc) auto
    have aeq: "flatBT lb = sc1 @ flatBP cp @ bc" using flateq sc1 by simp
    have lbne: "lb \<noteq> Trm []"
    proof
      assume "lb = Trm []"
      hence "flatBT lb = [Zsym]" by simp
      thus False using aeq cpw by (cases sc1) auto
    qed
    have scbLb: "scb_decomp lb sc1 (flatBT (Trm [cp])) bc"
      unfolding scb_decomp_def using aeq rbc less.prems(3)
      by (auto simp: isPTB_str_def intro: exI[of _ cp])
    have szlt: "size lb < size t"
      using rnsub_size_arg_lt'[of ts w lb] lastEq tsne tT by simp
    \<comment> \<open>\<open>domB lb = T\<^bsub>m\<^esub>\<close> and \<open>m < w\<close> from @{thm [source] domB_single_TBv_struct}\<close>
    have struct: "domB lb = TBv (enat m)
                    \<and> \<not> (\<exists>u'. w \<le> enat u' \<and> domB lb = TBv (enat u'))"
      by (rule domB_single_TBv_struct[OF domLastComp lbne])
    have domLbTBv: "domB lb = TBv (enat m)" using struct by (rule conjunct1)
    have nguard: "\<not> (\<exists>u'. w \<le> enat u' \<and> domB lb = TBv (enat u'))"
      using struct by (rule conjunct2)
    have mw: "enat m < w"
    proof (rule ccontr)
      assume "\<not> enat m < w"
      hence "w \<le> enat m" by simp
      hence "\<exists>u'. w \<le> enat u' \<and> domB lb = TBv (enat u')" using domLbTBv by blast
      thus False using nguard by simp
    qed
    have domLb: "domB_operB_xseq_dom (Inr (Inl (lb, z)))"
      by (rule operB_dom_TBv_body_spine_aux[OF scbLb less.prems(2) less.prems(3)
                                                domLbTBv less.prems(5)])
    have ih: "flatBT (operB lb z) = sc1 @ flatBT (operB (Trm [cp]) z) @ bc"
      by (rule less.IH[OF szlt scbLb less.prems(2) less.prems(3) domLbTBv
                          less.prems(5) less.prems(6)])
    have unfoldLast: "operB (Trm [DB w lb]) z = Dprin w (operB lb z)"
      by (rule operB_TBv_principal_unfold[OF domLbTBv lbne mw domLb])
    show ?thesis
    proof (cases "tl ts")
      case Nil
      have ts1: "ts = [DB w lb]" using tsne lastEq Nil by (cases ts) auto
      have tsingle: "t = Trm [DB w lb]" using tT ts1 by simp
      have flatOp: "flatBT (operB t z) = Dsym w # flatBT (operB lb z)"
        using unfoldLast tsingle by simp
      have flatOp2: "flatBT (operB t z) = (Dsym w # sc1) @ flatBT (operB (Trm [cp]) z) @ bc"
        using flatOp ih by simp
      have scbT: "scb_decomp t (Dsym w # sc1) (flatBT (Trm [cp])) bc"
        using scb_Dpt_lift[OF scbLb iptcp] tsingle by simp
      have sbeq: "s = Dsym w # sc1 \<and> b = bc"
        by (rule m_7_2_scb_unique_sb[OF less.prems(1) scbT tne])
      show ?thesis using flatOp2 sbeq by simp
    next
      case (Cons q qs)
      obtain p0 where tdecomp: "ts = p0 # q # qs" using Cons tsne by (cases ts) auto
      let ?rs = "butlast (p0 # q # qs)"
      have rsne: "?rs \<noteq> []" by simp
      have lastp: "last (p0 # q # qs) = DB w lb" using lastEq tdecomp tT by simp
      have lr: "p0 # q # qs = ?rs @ [DB w lb]"
        using lastp by (metis append_butlast_last_id list.distinct(1))
      have ds_t': "domB_operB_xseq_dom (Inr (Inl (Trm (p0 # q # qs), z)))"
        using ds_t tT tdecomp by simp
      have peelP: "operB (Trm (p0 # q # qs)) z
                    = addBT (Trm ?rs) (operB (Trm [last (p0 # q # qs)]) z)"
        by (rule operB_dom_multi_peel[OF ds_t'])
      have peel: "operB t z
                    = addBT (Trm ?rs) (operB (Trm [last (p0 # q # qs)]) z)"
        using peelP tT tdecomp by simp
      have innerOp: "operB (Trm [last (p0 # q # qs)]) z = Dprin w (operB lb z)"
        using lastp unfoldLast by simp
      have operT: "operB t z = Trm (?rs @ [DB w (operB lb z)])"
        using peel innerOp tdecomp by simp
      have flatt2: "flatBT t = Wpre ?rs @ (Dsym w # flatBT lb) @ [RP]"
      proof -
        have e1: "flatBT t = flatBT (Trm (?rs @ [DB w lb]))"
          using tT tdecomp arg_cong[where f="\<lambda>xs. flatBT (Trm xs)", OF lr] by simp
        also have "\<dots> = Wpre ?rs @ flatBP (DB w lb) @ [RP]"
          by (rule flatBT_multi_last[OF rsne])
        also have "\<dots> = Wpre ?rs @ (Dsym w # flatBT lb) @ [RP]" by simp
        finally show ?thesis .
      qed
      have flatcp: "flatBT t = (Wpre ?rs @ (Dsym w # sc1)) @ flatBP cp @ (bc @ [RP])"
        using flatt2 aeq by simp
      have scbWpre: "scb_decomp t (Wpre ?rs @ (Dsym w # sc1)) (flatBT (Trm [cp])) (bc @ [RP])"
        unfolding scb_decomp_def using flatcp iptcp rbc by auto
      have sbeq: "s = Wpre ?rs @ (Dsym w # sc1) \<and> b = bc @ [RP]"
        by (rule m_7_2_scb_unique_sb[OF less.prems(1) scbWpre tne])
      have "flatBT (operB t z) = Wpre ?rs @ (Dsym w # flatBT (operB lb z)) @ [RP]"
        using operT flatBT_multi_last[OF rsne, of "DB w (operB lb z)"] by simp
      also have "\<dots> = Wpre ?rs @ (Dsym w # sc1 @ flatBT (operB (Trm [cp]) z) @ bc) @ [RP]"
        using ih by simp
      also have "\<dots> = (Wpre ?rs @ (Dsym w # sc1)) @ flatBT (operB (Trm [cp]) z) @ (bc @ [RP])"
        by simp
      also have "\<dots> = s @ flatBT (operB (Trm [cp]) z) @ b" using sbeq by simp
      finally show ?thesis .
    qed
  qed
qed

text \<open>The inner \<open>xseq\<close>-tower flat read-back used by the article's
  \<open>n+1\<close> shape (A24 retracted).
  For a body with \<open>flat(body) = s\<^sub>0 \<frown> flat(D\<^sub>v 0) \<frown> b\<^sub>0\<close> (marked leaf \<open>D\<^sub>v 0\<close>,
  \<open>domB body = T\<^bsub>v-1\<^esub>\<close>), \<open>flat(xseq body (v-1) i) = (s\<^sub>0 D\<^bsub>v-1\<^esub>)\<^bsup>i\<^esup> D\<^bsub>v-1\<^esub> 0 b\<^sub>0\<^bsup>i\<^esup>\<close>.
  Induction on \<open>i\<close>: the base is @{thm [source] xseq_eval_0}; the step uses the
  recursion \<open>xseq body m (Suc j) = operB body (D\<^sub>m (xseq body m j))\<close>, the body
  flat transport @{thm [source] operB_TBv_body_spine} (marked principal \<open>D\<^sub>v 0\<close>,
  image \<open>operB(D\<^sub>v 0) (D\<^sub>m x\<^sub>j) = D\<^sub>m x\<^sub>j\<close> via @{thm [source] operB_Dv0_id}), and the
  IH.  Validated 48/48 + 12/12 in @{path \<open>python/scb_fseq_kind1_check.py\<close>}.\<close>

lemma xseq_body_tower_flat:
  fixes v :: nat
  assumes vpos: "0 < v"
    and db: "domB body = TBv (enat (v - 1))"
    and scb: "scb_decomp body s\<^sub>0 (flatBT (Dpt (enat v) 0\<^sub>B)) b\<^sub>0"
  shows "flatBT (xseq body (enat (v - 1)) i)
           = concat (replicate i ([Dsym (enat (v - 1))] @ s\<^sub>0))
             @ [Dsym (enat (v - 1))] @ [Zsym]
             @ concat (replicate i b\<^sub>0)"
proof (induction i)
  case 0
  have "xseq body (enat (v - 1)) 0 = Dprin (enat (v - 1)) (Trm [])"
    by (rule xseq_eval_0[OF db])
  thus ?case by simp
next
  case (Suc j)
  let ?m = "enat (v - 1)"
  let ?cp = "DB (enat v) 0\<^sub>B"
  let ?xj = "xseq body ?m j"
  \<comment> \<open>recursion step (corrected \<open>([].4)(ii)\<close>): \<open>x\<^bsub>j+1\<^esub> = D\<^bsub>v-1\<^esub> body[x\<^sub>j]\<close>\<close>
  have domStep: "domB_operB_xseq_dom (Inr (Inr (body, ?m, Suc j)))"
    by (rule xseq_dom_TBv_body[OF db])
  have step: "xseq body ?m (Suc j) = Dprin ?m (operB body ?xj)"
    using xseq.psimps[OF domStep] by simp
  \<comment> \<open>flat transport over the body, marked principal \<open>D\<^sub>v 0\<close>\<close>
  have dcp: "scb_decomp body s\<^sub>0 (flatBT (Trm [?cp])) b\<^sub>0" using scb by simp
  have domcp: "domB (Trm [?cp]) = TBv (enat (v - 1))" by (rule domB_Dw0[OF vpos])
  have dfreecp: "dfree_BP ?cp" by simp
  have domcpz: "domB_operB_xseq_dom (Inr (Inl (Trm [?cp], ?xj)))"
    by (rule operB_dom_Dv0)
  have imgcp: "operB (Trm [?cp]) ?xj = ?xj" by (rule operB_Dv0_id[OF vpos])
  obtain rp where xjps: "?xj = Trm [rp]"
    using xseq_single_TBv[OF db, of ?m j] by auto
  have oprp: "operB (Trm [?cp]) ?xj = Trm [rp]" using imgcp xjps by simp
  have transp: "flatBT (operB body ?xj)
                  = s\<^sub>0 @ flatBT (operB (Trm [?cp]) ?xj) @ b\<^sub>0"
    by (rule operB_TBv_body_spine[OF dcp domcp dfreecp db domcpz oprp])
  have flatstep: "flatBT (xseq body ?m (Suc j)) = Dsym ?m # (s\<^sub>0 @ flatBT ?xj @ b\<^sub>0)"
  proof -
    have "flatBT (xseq body ?m (Suc j)) = Dsym ?m # flatBT (operB body ?xj)"
      using step by simp
    also have "\<dots> = Dsym ?m # (s\<^sub>0 @ flatBT (operB (Trm [?cp]) ?xj) @ b\<^sub>0)"
      using transp by simp
    also have "\<dots> = Dsym ?m # (s\<^sub>0 @ flatBT ?xj @ b\<^sub>0)" using imgcp by simp
    finally show ?thesis .
  qed
  \<comment> \<open>fold in the IH\<close>
  have headfold: "([Dsym ?m] @ s\<^sub>0) @ concat (replicate j ([Dsym ?m] @ s\<^sub>0))
                    = concat (replicate (Suc j) ([Dsym ?m] @ s\<^sub>0))"
    by simp
  have tailfold: "concat (replicate j b\<^sub>0) @ b\<^sub>0 = concat (replicate (Suc j) b\<^sub>0)"
  proof -
    have "replicate (Suc j) b\<^sub>0 = replicate j b\<^sub>0 @ [b\<^sub>0]"
      by (simp add: replicate_append_same)
    thus ?thesis by simp
  qed
  have "flatBT (xseq body ?m (Suc j))
          = Dsym ?m # (s\<^sub>0 @
              (concat (replicate j ([Dsym ?m] @ s\<^sub>0)) @ [Dsym ?m] @ [Zsym]
               @ concat (replicate j b\<^sub>0)) @ b\<^sub>0)"
    using flatstep Suc.IH by simp
  also have "\<dots> = ([Dsym ?m] @ s\<^sub>0) @ concat (replicate j ([Dsym ?m] @ s\<^sub>0))
                  @ [Dsym ?m] @ [Zsym]
                  @ (concat (replicate j b\<^sub>0) @ b\<^sub>0)"
    by simp
  also have "\<dots> = concat (replicate (Suc j) ([Dsym ?m] @ s\<^sub>0))
                  @ [Dsym ?m] @ [Zsym]
                  @ concat (replicate (Suc j) b\<^sub>0)"
    using headfold tailfold by simp
  finally show ?case .
qed

text \<open>\<open>domB (D\<^sub>u body) = NatSet\<close> for \<open>u < v\<close> when \<open>domB body = T\<^bsub>v-1\<^esub>\<close>: the
  kind-1 \<open>([].4)(ii)\<close> guard \<open>(\<exists>u'. u \<le> u' \<and> domB body = T\<^bsub>u'\<^esub>)\<close> fires (\<open>u' = v-1\<close>),
  giving the \<open>NatSet\<close> branch.  General-\<open>body\<close> form of
  @{thm [source] domB_Du_Dv0_NatSet}.\<close>

lemma domB_Du_body_NatSet:
  assumes uv: "u < v" and db: "domB body = TBv (enat (v - 1))" and bne: "body \<noteq> Trm []"
  shows "domB (Trm [DB (enat u) body]) = NatSet"
proof -
  have nz: "domB body \<noteq> {Trm []}" using db zero_set_neq_TBv by auto
  have guard: "(\<exists>u'. enat u \<le> enat u' \<and> domB body = TBv (enat u'))"
  proof (intro exI[of _ "v - 1"] conjI)
    show "enat u \<le> enat (v - 1)" using uv by simp
    show "domB body = TBv (enat (v - 1))" by (rule db)
  qed
  have "domB (Trm [DB (enat u) body])
          = (let dbb = domB body in
             if dbb = {Trm []} then NatSet
             else if (\<exists>u'. enat u \<le> enat u' \<and> dbb = TBv (enat u')) then NatSet
             else dbb)"
    using bne by (subst domB_unfold) simp
  also have "\<dots> = NatSet" using nz guard by (simp add: Let_def)
  finally show ?thesis .
qed

text \<open>\<open>operB (D\<^sub>u body) (numBT n) = D\<^sub>u (xseq body (v-1) n)\<close> for \<open>u < v\<close>,
  \<open>domB body = T\<^bsub>v-1\<^esub>\<close>: the kind-1 unfold @{thm [source] operB_kind1_unfold}
  then \<open>numNat (numBT n) = n\<close>.  General-\<open>body\<close> form of
  @{thm [source] operB_Du_Dv0_kind1_eval}.\<close>

lemma operB_Du_body_kind1_eval:
  assumes uv: "u < v" and db: "domB body = TBv (enat (v - 1))" and bne: "body \<noteq> Trm []"
  shows "operB (Trm [DB (enat u) body]) (numBT n)
           = Dprin (enat u) (operB body (xseq body (enat (v - 1)) n))"
proof -
  have vu: "enat u \<le> enat (v - 1)" using uv by simp
  have "operB (Trm [DB (enat u) body]) (numBT n)
          = Dprin (enat u) (operB body (xseq body (enat (v - 1)) (numNat (numBT n))))"
    by (rule operB_kind1_unfold[OF db vu bne])
  also have "\<dots> = Dprin (enat u) (operB body (xseq body (enat (v - 1)) n))"
    by (simp add: numNat_numBT)
  finally show ?thesis .
qed

text \<open>List identity for the \<open>([].4)(ii)\<close> read-back: pulling a prefix \<open>xs\<close>
  through an \<open>n\<close>-fold \<open>(ys xs)\<close> repetition turns it into an \<open>n\<close>-fold
  \<open>(xs ys)\<close> repetition followed by \<open>xs\<close>.\<close>

lemma concat_replicate_shift:
  "xs @ concat (replicate n (ys @ xs)) = concat (replicate n (xs @ ys)) @ xs"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have "xs @ concat (replicate (Suc n) (ys @ xs))
          = (xs @ ys) @ (xs @ concat (replicate n (ys @ xs)))"
    by simp
  also have "\<dots> = (xs @ ys) @ (concat (replicate n (xs @ ys)) @ xs)"
    using Suc.IH by simp
  also have "\<dots> = concat (replicate (Suc n) (xs @ ys)) @ xs"
    by simp
  finally show ?case .
qed

end
