theory Frontier_7_052
  imports Support_7_047
begin

section \<open>§7.1 [Buc1] Lemma 3.2: termination of the \<open>xseq\<close> tower (\<open>operB\<close> kind-1)\<close>

text \<open>The genuine \<open>([].4)(ii)\<close> case of \<open>operB\<close>: the body \<open>b\<close> has
  \<open>domB b = T\<^bsub>u\<^esub>\<close> (\<open>= TBv (enat u)\<close>) and the head index \<open>v \<le> u\<close>, so the
  \<open>xseq\<close>-branch fires, building the fundamental-sequence tower
  \<open>x\<^sub>n\<close> (\<open>= xseq b u n\<close>) with \<open>x\<^sub>0 = D\<^sub>u 0\<close>, \<open>x\<^bsub>k+1\<^esub> = operB b (D\<^sub>u x\<^sub>k)\<close>.

  The termination ([Buc1] Lemma 3.2, induction on the length of the argument)
  rests on a single structural fact, validated 354/354 in
  \<open>python/_xseq_operB_TBv.py\<close>: for ANY \<open>b\<close> with \<open>domB b = T\<^bsub>u\<^esub>\<close>,
  evaluating \<open>operB b z\<close> recurses ONLY via the \<open>else\<close>/\<open>(iii)\<close> branch
  (\<open>D\<^sub>w(operB c z)\<close>, body strictly smaller, \<open>domB c = T\<^bsub>u\<^esub>\<close> again) and the
  \<open>[].2\<close> base case (\<open>c = 0\<close>, returns \<open>z\<close>) — NEVER the \<open>xseq\<close> branch, NEVER
  the \<open>mult\<close>/\<open>db = {0}\<close> branch.  Hence \<open>operB b z\<close> is defined for EVERY \<open>z\<close>
  by plain structural induction on \<open>size b\<close>, independently of \<open>z\<close>.\<close>

text \<open>Structural decomposition of a single principal whose \<open>domB\<close> is some
  \<open>T\<^bsub>u\<^esub>\<close> with non-zero body: \<open>domB (D\<^sub>w c) = T\<^bsub>u\<^esub>\<close>, \<open>c \<noteq> 0\<close> forces
  \<open>domB c = T\<^bsub>u\<^esub>\<close> and the strict inequality \<open>u < w\<close> (so the \<open>else\<close> guard of
  \<open>operB\<close>/\<open>domB\<close> is taken: no \<open>u'\<close> with \<open>w \<le> u'\<close> has \<open>T\<^bsub>u\<^esub> = T\<^bsub>u'\<^esub>\<close>).\<close>

lemma domB_single_TBv_struct:
  assumes db: "domB (Trm [DB w c]) = TBv (enat u)" and cne: "c \<noteq> Trm []"
  shows "domB c = TBv (enat u) \<and> \<not> (\<exists>u'. w \<le> enat u' \<and> domB c = TBv (enat u'))"
proof -
  have unf: "domB (Trm [DB w c]) =
               (let dbc = domB c in
                if dbc = {Trm []} then NatSet
                else if (\<exists>u'. w \<le> enat u' \<and> dbc = TBv (enat u')) then NatSet
                else dbc)"
    using cne by (subst domB_unfold) simp
  \<comment> \<open>the result \<open>T\<^bsub>u\<^esub>\<close> is neither \<open>{0}\<close> nor \<open>NatSet\<close>, so the final \<open>else dbc\<close>
     branch is taken: \<open>dbc = T\<^bsub>u\<^esub>\<close> and the guard is false\<close>
  have nz: "domB c \<noteq> {Trm []}"
  proof
    assume "domB c = {Trm []}"
    hence "domB (Trm [DB w c]) = NatSet" using unf by (simp add: Let_def)
    hence "NatSet = TBv (enat u)" using db by simp
    thus False using NatSet_neq_TBv by simp
  qed
  have nguard: "\<not> (\<exists>u'. w \<le> enat u' \<and> domB c = TBv (enat u'))"
  proof
    assume "\<exists>u'. w \<le> enat u' \<and> domB c = TBv (enat u')"
    hence "domB (Trm [DB w c]) = NatSet" using unf nz by (simp add: Let_def)
    hence "NatSet = TBv (enat u)" using db by simp
    thus False using NatSet_neq_TBv by simp
  qed
  have "domB (Trm [DB w c]) = domB c" using unf nz nguard by (simp add: Let_def)
  hence "domB c = TBv (enat u)" using db by simp
  thus ?thesis using nguard by simp
qed

text \<open>Lemma A (\<open>operB\<close>-totality on a \<open>T\<^bsub>u\<^esub>\<close>-body): if \<open>domB b = T\<^bsub>u\<^esub>\<close> then
  \<open>operB b z\<close> is defined for every \<open>z\<close>.  Strong induction on \<open>size b\<close>;
  the single recursive \<open>operB\<close>-call is the \<open>else\<close>-branch \<open>operB c z\<close> on a
  strictly smaller body \<open>c\<close> with \<open>domB c = T\<^bsub>u\<^esub>\<close>; the \<open>xseq\<close>- and \<open>mult\<close>-arm
  obligations are vacuous (their guards force \<open>{0} = T\<^bsub>u\<^esub>\<close> or \<open>w \<le> u\<close> against
  @{thm [source] domB_single_TBv_struct}); the \<open>else\<close>-guard obligations are
  vacuous because their \<open>\<not> dom (operB c z)\<close> hypothesis contradicts the IH.\<close>

lemma operB_dom_TBv_body:
  "domB b = TBv (enat u) \<Longrightarrow> domB_operB_xseq_dom (Inr (Inl (b, z)))"
proof (induction b arbitrary: u z rule: measure_induct_rule[where f=size])
  case (less b u z)
  obtain xs where bxs: "b = Trm xs" by (cases b)
  show ?case
  proof (cases xs)
    case Nil
    \<comment> \<open>\<open>b = 0\<close>: \<open>domB 0 = {} \<noteq> T\<^bsub>u\<^esub>\<close> (the latter contains \<open>0\<close>), contradiction\<close>
    have "domB b = {}" using bxs Nil by (subst domB_unfold) simp
    hence "TBv (enat u) = {}" using less.prems by simp
    moreover have "Trm [] \<in> TBv (enat u)" by (simp add: TBv_def)
    ultimately show ?thesis by simp
  next
    case (Cons p0 ps1)
    show ?thesis
    proof (cases ps1)
      case (Cons q ps2)
      \<comment> \<open>multi-component: peel to last via @{thm [source] operB_dom_multi};
         \<open>domB (Trm [last]) = T\<^bsub>u\<^esub>\<close> and \<open>size (Trm [last]) < size b\<close>\<close>
      have xseq_eq: "xs = p0 # q # ps2" using \<open>xs = p0 # ps1\<close> Cons by simp
      have ne: "xs \<noteq> []" using xseq_eq by simp
      have dlast: "domB (Trm [last (p0 # q # ps2)]) = TBv (enat u)"
        using less.prems bxs domB_last_component[OF ne] xseq_eq by simp
      \<comment> \<open>\<open>last\<close> is a single component among \<open>\<ge> 2\<close>, so strictly smaller\<close>
      have lastin: "last (p0 # q # ps2) \<in> set (q # ps2)"
        by (cases ps2) auto
      have szlast: "size (last (p0 # q # ps2)) \<le> size_list size (q # ps2)"
        by (rule size_list_estimation'[OF lastin order_refl])
      have szpos: "0 < size p0" by (cases p0) simp
      have core: "size (last (p0 # q # ps2)) < size p0 + size_list size (q # ps2)"
        using szlast szpos by linarith
      have eL: "size (Trm [last (p0 # q # ps2)] :: BT)
                  = Suc (Suc (size (last (p0 # q # ps2))))" by simp
      have eR: "size (Trm (p0 # q # ps2) :: BT)
                  = Suc (Suc (size p0 + size_list size (q # ps2)))" by simp
      have szlt: "size (Trm [last (p0 # q # ps2)] :: BT) < size b"
        using core eL eR bxs xseq_eq by simp
      have domLast': "domB_operB_xseq_dom (Inr (Inl (Trm [last (p0 # q # ps2)], z)))"
        by (rule less.IH[OF szlt dlast])
      have "domB_operB_xseq_dom (Inr (Inl (Trm (p0 # q # ps2), z)))"
        by (rule operB_dom_multi[OF domLast'])
      thus ?thesis using bxs xseq_eq by simp
    next
      case Nil
      \<comment> \<open>single principal \<open>b = Trm [DB w c]\<close>\<close>
      obtain w c where p0eq: "p0 = DB w c" by (cases p0)
      have beq: "b = Trm [DB w c]" using bxs \<open>xs = p0 # ps1\<close> Nil p0eq by simp
      have dbWc: "domB (Trm [DB w c]) = TBv (enat u)" using less.prems beq by simp
      show ?thesis
      proof (cases "c = Trm []")
        case True
        \<comment> \<open>\<open>c = 0\<close>: every \<open>domintros(2)\<close> obligation has premise \<open>x2 \<noteq> 0\<close> with
           \<open>x2 = c = 0\<close>, so all are vacuous except \<open>domB\<close>-totality\<close>
        show ?thesis
          unfolding beq True
        proof (rule domB_operB_xseq.domintros(2))
          show "domB_operB_xseq_dom (Inl x2)"
            if "Trm [DB w (Trm [])] = Trm [DB x1 x2]" "x2 \<noteq> Trm []" for x1 x2
            by (rule domB_dom_all)
        qed (use True in \<open>simp_all\<close>)
      next
        case False
        have struct: "domB c = TBv (enat u)
                        \<and> \<not> (\<exists>u'. w \<le> enat u' \<and> domB c = TBv (enat u'))"
          by (rule domB_single_TBv_struct[OF dbWc False])
        have dc: "domB c = TBv (enat u)" using struct by (rule conjunct1)
        have nguard: "\<not> (\<exists>u'. w \<le> enat u' \<and> domB c = TBv (enat u'))"
          using struct by (rule conjunct2)
        have szc: "size c < size b" using beq by simp
        have domc: "domB_operB_xseq_dom (Inr (Inl (c, z)))"
          by (rule less.IH[OF szc dc])
        show ?thesis
          unfolding beq
        proof (rule domB_operB_xseq.domintros(2))
          \<comment> \<open>(0) \<open>domB c\<close> total\<close>
          show "domB_operB_xseq_dom (Inl x2)"
            if "Trm [DB w c] = Trm [DB x1 x2]" "x2 \<noteq> Trm []" for x1 x2
            by (rule domB_dom_all)
        next
          \<comment> \<open>(1) \<open>db = {0}\<close> branch: \<open>domB c = T\<^bsub>u\<^esub> \<noteq> {0}\<close>\<close>
          show "domB_operB_xseq_dom (Inr (Inl (x2, Trm [])))"
            if "Trm [DB w c] = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "{Trm []} = domB x2"
            for x1 x2
          proof -
            have "x2 = c" using that(1) by simp
            hence "{Trm []} = TBv (enat u)" using that(3) dc by simp
            thus ?thesis using zero_set_neq_TBv by simp
          qed
        next
          \<comment> \<open>(2) \<open>xseq\<close>-guard: \<open>domB c = T\<^bsub>u'\<^esub>\<close>, \<open>w \<le> u'\<close> impossible by @{thm [source] nguard}\<close>
          show "xb = Trm []"
            if "Trm [DB w c] = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "x1 \<le> enat u'"
               "domB x2 = TBv (enat u')"
               "\<not> domB_operB_xseq_dom
                    (Inr (Inr (x2, enat (tbvIdx (TBv (enat u'))), numNat z)))"
               "xb \<in> TBv (enat u')" for x1 x2 u' xb
          proof -
            have "x2 = c" "x1 = w" using that(1) by simp_all
            hence "\<exists>u'. w \<le> enat u' \<and> domB c = TBv (enat u')"
              using that(3,4) by blast
            thus ?thesis using nguard by simp
          qed
        next
          \<comment> \<open>(3) \<open>0 \<in> T\<^bsub>u'\<^esub>\<close>: same vacuous guard\<close>
          show "Trm [] \<in> TBv (enat u')"
            if "Trm [DB w c] = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "x1 \<le> enat u'"
               "domB x2 = TBv (enat u')"
               "\<not> domB_operB_xseq_dom
                    (Inr (Inr (x2, enat (tbvIdx (TBv (enat u'))), numNat z)))"
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
            have "x2 = c" "x1 = w" using that(1) by simp_all
            hence "\<exists>u'. w \<le> enat u' \<and> domB c = TBv (enat u')"
              using that(3,4) by blast
            thus ?thesis using nguard by simp
          qed
        next
          \<comment> \<open>(5) \<open>0 \<in> T\<^bsub>u'\<^esub>\<close> for the inner call: same vacuous guard\<close>
          show "Trm [] \<in> TBv (enat u')"
            if "Trm [DB w c] = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "x1 \<le> enat u'"
               "domB x2 = TBv (enat u')"
               "\<not> domB_operB_xseq_dom
                    (Inr (Inl (x2, xseq x2 (enat (tbvIdx (TBv (enat u')))) (numNat z))))"
               for x1 x2 u'
            by (simp add: TBv_def)
        next
          \<comment> \<open>(6) \<open>else\<close>-guard: \<open>\<not> dom (operB c z)\<close> contradicts the IH @{thm [source] domc}\<close>
          show "xb = Trm []"
            if "Trm [DB w c] = Trm [DB x1 x2]" "x2 \<noteq> Trm []"
               "\<forall>u'. x1 \<le> enat u' \<longrightarrow> domB x2 \<noteq> TBv (enat u')"
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
               "\<forall>u'. x1 \<le> enat u' \<longrightarrow> domB x2 \<noteq> TBv (enat u')"
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
            if "Trm [DB w c] = Trm (DB x1 x2 # x21a # x22a)" "x22a \<noteq> []"
            for x1 x2 x21a x22a
            using that(1) by simp
        qed
      qed
    qed
  qed
qed

text \<open>\<open>tbvIdx (T\<^bsub>u\<^esub>) = u\<close>: the index is recovered uniquely by injectivity
  of \<open>TBv\<close> on finite levels (@{thm [source] TBv_enat_inj}).\<close>

lemma tbvIdx_TBv: "tbvIdx (TBv (enat u)) = u"
  unfolding tbvIdx_def
  by (rule the_equality) (auto dest: TBv_enat_inj)

text \<open>Lemma B ([Buc1] Lemma 3.2, the \<open>xseq\<close> tower): for a body \<open>b\<close> with
  \<open>domB b = T\<^bsub>u'\<^esub>\<close>, the tower \<open>xseq b u i\<close> is defined for every \<open>u\<close> and \<open>i\<close>.
  Induction on \<open>i\<close> (the length of the argument \<open>a\<close> in [Buc1]); the two
  \<open>domintros(3)\<close> obligations are the inner \<open>xseq b u nat\<close> (IH, smaller index)
  and \<open>operB b (D\<^sub>u (xseq b u nat))\<close> (defined for every second argument by
  @{thm [source] operB_dom_TBv_body}).\<close>

lemma xseq_dom_TBv_body:
  assumes db: "domB b = TBv (enat u')"
  shows "domB_operB_xseq_dom (Inr (Inr (b, u, i)))"
proof (induction i)
  case 0
  show ?case
    by (rule domB_operB_xseq.domintros(3)) simp_all
next
  case (Suc i)
  show ?case
  proof (rule domB_operB_xseq.domintros(3))
    \<comment> \<open>(1) inner \<open>xseq b u nat\<close>: \<open>nat = i\<close> by the case split, IH\<close>
    show "domB_operB_xseq_dom (Inr (Inr (b, u, nat)))"
      if "Suc i = Suc nat" for nat
      using Suc.IH that by simp
  next
    \<comment> \<open>(2) \<open>operB b (xseq b u nat)\<close>: defined for any second arg, Lemma A\<close>
    show "domB_operB_xseq_dom (Inr (Inl (b, xseq b u nat)))"
      if "Suc i = Suc nat" for nat
      by (rule operB_dom_TBv_body[OF db])
  qed
qed

text \<open>Lemma C (kind-1 \<open>operB\<close>-domain): the genuine \<open>([].4)(ii)\<close> principal
  \<open>D\<^sub>v b\<close> with \<open>domB b = T\<^bsub>u\<^esub>\<close> and \<open>v \<le> u\<close> is in \<open>operB\<close>'s domain.  The
  \<open>xseq\<close>-arm side conditions ((2)/(3)) are discharged by Lemma B
  (@{thm [source] xseq_dom_TBv_body}): their \<open>\<not> dom (xseq \<dots>)\<close> hypothesis is
  false, so they are vacuous; the \<open>db = {0}\<close> and \<open>else\<close> arms are vacuous
  because \<open>domB b = T\<^bsub>u\<^esub>\<close> with \<open>v \<le> u\<close>.\<close>

lemma operB_dom_kind1:
  assumes db: "domB b = TBv (enat u)" and vu: "v \<le> enat u" and bne: "b \<noteq> Trm []"
  shows "domB_operB_xseq_dom (Inr (Inl (Trm [DB v b], z)))"
proof (rule domB_operB_xseq.domintros(2))
  \<comment> \<open>(0) \<open>domB b\<close> total\<close>
  show "domB_operB_xseq_dom (Inl x2)"
    if "Trm [DB v b] = Trm [DB x1 x2]" "x2 \<noteq> Trm []" for x1 x2
    by (rule domB_dom_all)
next
  \<comment> \<open>(1) \<open>db = {0}\<close>: \<open>domB b = T\<^bsub>u\<^esub> \<noteq> {0}\<close>\<close>
  show "domB_operB_xseq_dom (Inr (Inl (x2, Trm [])))"
    if "Trm [DB v b] = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "{Trm []} = domB x2" for x1 x2
  proof -
    have "x2 = b" using that(1) by simp
    hence "{Trm []} = TBv (enat u)" using that(3) db by simp
    thus ?thesis using zero_set_neq_TBv by simp
  qed
next
  \<comment> \<open>(2) \<open>xseq\<close>-guard: \<open>\<not> dom (xseq b u' (numNat z))\<close> is FALSE (Lemma B)\<close>
  show "xb = Trm []"
    if "Trm [DB v b] = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "x1 \<le> enat u'"
       "domB x2 = TBv (enat u')"
       "\<not> domB_operB_xseq_dom
            (Inr (Inr (x2, enat (tbvIdx (TBv (enat u'))), numNat z)))"
       "xb \<in> TBv (enat u')" for x1 x2 u' xb
  proof -
    have "x2 = b" using that(1) by simp
    hence "domB b = TBv (enat u')" using that(4) by simp
    \<comment> \<open>the inner \<open>xseq\<close> tower IS defined (Lemma B), contradicting the hypothesis\<close>
    have "domB_operB_xseq_dom
            (Inr (Inr (b, enat (tbvIdx (TBv (enat u'))), numNat z)))"
      by (rule xseq_dom_TBv_body[OF \<open>domB b = TBv (enat u')\<close>])
    hence "domB_operB_xseq_dom
             (Inr (Inr (x2, enat (tbvIdx (TBv (enat u'))), numNat z)))"
      using \<open>x2 = b\<close> by simp
    thus ?thesis using that(5) by simp
  qed
next
  \<comment> \<open>(3) \<open>0 \<in> T\<^bsub>u'\<^esub>\<close>: trivially\<close>
  show "Trm [] \<in> TBv (enat u')"
    if "Trm [DB v b] = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "x1 \<le> enat u'"
       "domB x2 = TBv (enat u')"
       "\<not> domB_operB_xseq_dom
            (Inr (Inr (x2, enat (tbvIdx (TBv (enat u'))), numNat z)))"
       for x1 x2 u'
    by (simp add: TBv_def)
next
  \<comment> \<open>(4) inner \<open>operB b (xseq \<dots>)\<close> guard: \<open>\<not> dom\<close> is FALSE (Lemma A on any 2nd arg)\<close>
  show "xb = Trm []"
    if "Trm [DB v b] = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "x1 \<le> enat u'"
       "domB x2 = TBv (enat u')"
       "\<not> domB_operB_xseq_dom
            (Inr (Inl (x2, xseq x2 (enat (tbvIdx (TBv (enat u')))) (numNat z))))"
       "xb \<in> TBv (enat u')" for x1 x2 u' xb
  proof -
    have x2b: "x2 = b" using that(1) by simp
    hence dbu': "domB b = TBv (enat u')" using that(4) by simp
    have "domB_operB_xseq_dom
            (Inr (Inl (b, xseq b (enat (tbvIdx (TBv (enat u')))) (numNat z))))"
      by (rule operB_dom_TBv_body[OF dbu'])
    thus ?thesis using that(5) x2b by simp
  qed
next
  \<comment> \<open>(5) \<open>0 \<in> T\<^bsub>u'\<^esub>\<close> for the inner call\<close>
  show "Trm [] \<in> TBv (enat u')"
    if "Trm [DB v b] = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "x1 \<le> enat u'"
       "domB x2 = TBv (enat u')"
       "\<not> domB_operB_xseq_dom
            (Inr (Inl (x2, xseq x2 (enat (tbvIdx (TBv (enat u')))) (numNat z))))"
       for x1 x2 u'
    by (simp add: TBv_def)
next
  \<comment> \<open>(6) \<open>else\<close>-guard: \<open>\<forall>u'. v \<le> u' \<longrightarrow> domB b \<noteq> T\<^bsub>u'\<^esub>\<close> is FALSE
     (take \<open>u' = u\<close>: \<open>v \<le> u\<close> and \<open>domB b = T\<^bsub>u\<^esub>\<close>)\<close>
  show "xb = Trm []"
    if "Trm [DB v b] = Trm [DB x1 x2]" "x2 \<noteq> Trm []"
       "\<forall>u'. x1 \<le> enat u' \<longrightarrow> domB x2 \<noteq> TBv (enat u')"
       "\<not> domB_operB_xseq_dom (Inr (Inl (x2, z)))"
       "xb \<in> domB x2" for x1 x2 xb
  proof -
    have "x2 = b" "x1 = v" using that(1) by simp_all
    hence "v \<le> enat u \<longrightarrow> domB b \<noteq> TBv (enat u)" using that(3) by blast
    thus ?thesis using vu db by simp
  qed
next
  \<comment> \<open>(7) \<open>0 \<in> domB b\<close> else-guard: same FALSE premise\<close>
  show "Trm [] \<in> domB x2"
    if "Trm [DB v b] = Trm [DB x1 x2]" "x2 \<noteq> Trm []"
       "\<forall>u'. x1 \<le> enat u' \<longrightarrow> domB x2 \<noteq> TBv (enat u')"
       "\<not> domB_operB_xseq_dom (Inr (Inl (x2, z)))" for x1 x2
  proof -
    have "x2 = b" "x1 = v" using that(1) by simp_all
    hence "v \<le> enat u \<longrightarrow> domB b \<noteq> TBv (enat u)" using that(3) by blast
    thus ?thesis using vu db by simp
  qed
next
  \<comment> \<open>(8) two-component multi: vacuous (single principal)\<close>
  show "domB_operB_xseq_dom (Inr (Inl (Trm [x21a], z)))"
    if "Trm [DB v b] = Trm [DB x1 x2, x21a]" for x1 x2 x21a
    using that by simp
next
  \<comment> \<open>(9) \<open>(\<ge>3)\<close>-component multi: vacuous (single principal)\<close>
  show "domB_operB_xseq_dom (Inr (Inl (Trm [last x22a], z)))"
    if "Trm [DB v b] = Trm (DB x1 x2 # x21a # x22a)" "x22a \<noteq> []" for x1 x2 x21a x22a
    using that(1) by simp
qed

text \<open>The kind-1 \<open>operB\<close> unfold:
  \<open>operB (D\<^sub>v b) z = D\<^sub>v (operB b (xseq b (tbvIdx (domB b)) (numNat z)))\<close>
  when \<open>domB b = T\<^bsub>u\<^esub>\<close> and \<open>v \<le> u\<close> (the \<open>([].4)(ii)\<close> fundamental sequence
  \<open>a[n] = D\<^sub>v b[x\<^sub>n]\<close>).\<close>

lemma operB_kind1_unfold:
  assumes db: "domB b = TBv (enat u)" and vu: "v \<le> enat u" and bne: "b \<noteq> Trm []"
  shows "operB (Trm [DB v b]) z = Dprin v (operB b (xseq b (enat u) (numNat z)))"
proof -
  have dom: "domB_operB_xseq_dom (Inr (Inl (Trm [DB v b], z)))"
    by (rule operB_dom_kind1[OF db vu bne])
  have guard: "(\<exists>u'. v \<le> enat u' \<and> domB b = TBv (enat u'))" using db vu by blast
  have "operB (Trm [DB v b]) z
          = (let dbb = domB b in
             if dbb = {Trm []} then multBT (Dprin v (operB b (Trm []))) (numNat z + 1)
             else if (\<exists>u'. v \<le> enat u' \<and> dbb = TBv (enat u'))
                  then Dprin v (operB b (xseq b (enat (tbvIdx dbb)) (numNat z)))
             else Dprin v (operB b z))"
    using operB.psimps[OF dom] bne by simp
  also have "\<dots> = Dprin v (operB b (xseq b (enat (tbvIdx (domB b))) (numNat z)))"
  proof -
    have nz: "domB b \<noteq> {Trm []}" using db zero_set_neq_TBv by auto
    show ?thesis using nz guard by (simp add: Let_def)
  qed
  also have "\<dots> = Dprin v (operB b (xseq b (enat u) (numNat z)))"
    using db tbvIdx_TBv by simp
  finally show ?thesis .
qed


section \<open>§8.6/§8.7 \<open>[0]\<close>-零化 (annihilation): atomic single-step \<open>operB \<dash> (numBT 0)\<close> facts\<close>

text \<open>The \<open>[0]\<close> operation is \<open>\<lambda>a. operB a (numBT 0)\<close>.  Since \<open>numBT 0 = Trm [] = 0\<^sub>B\<close>
  and \<open>numNat (numBT 0) = 0\<close>, the atomic step facts below evaluate \<open>operB\<close> on the
  trailing \<open>D\<^sub>v 0\<close> principal that the §8.6/§8.7 零化可能性 lemmas peel.  These are
  the \<open>(D\<^sub>v 0)[0] = 0\<close> identity (article §8.7 proof) and the one-step trailing
  peel \<open>(t' + D\<^sub>v 0)[0] = t'\<close> (\<open>t' \<noteq> 0\<close>), the core computation of the article's
  零化可能性 induction.\<close>

text \<open>\<open>operB\<close>-domain on a single zero-body principal \<open>D\<^sub>v 0\<close>: every
  \<open>domintros(2)\<close> obligation carries the premise \<open>x2 \<noteq> 0\<close> with \<open>x2 = 0\<close>, so all
  recursion premises are vacuous except \<open>domB\<close>-totality (template: the \<open>c = 0\<close>
  branch of @{thm [source] operB_dom_TBv_body}).\<close>

lemma operB_dom_Dv0:
  "domB_operB_xseq_dom (Inr (Inl (Dpt v 0\<^sub>B, z)))"
proof (rule domB_operB_xseq.domintros(2))
  show "domB_operB_xseq_dom (Inl x2)"
    if "Trm [DB v (Trm [])] = Trm [DB x1 x2]" "x2 \<noteq> Trm []" for x1 x2
    by (rule domB_dom_all)
qed simp_all

subsection \<open>§8.7 \<open>[0]\<close>-零化 of a nested principal \<open>D\<^sub>u(D\<^sub>w 0)\<close>\<close>

text \<open>The genuine inductive content of the §8.7 末尾項の零化可能性 lemma in its
  \<open>t' = 0\<close> form: \<open>D\<^sub>u(D\<^sub>w 0)\<close> is annihilated to \<open>D\<^sub>u 0\<close> by iterating \<open>[0]\<close>
  \<open>k \<le> w+1\<close> times.  Two single-step laws drive it:
  the kind-1 (\<open>([].4)(ii)\<close>) descent \<open>D\<^sub>u(D\<^sub>w 0)[0] = D\<^sub>u(D\<^bsub>w-1\<^esub>0)\<close> when \<open>u < w\<close>,
  and the collapse \<open>D\<^sub>u(D\<^sub>w 0)[0] = D\<^sub>u 0\<close> when \<open>w \<le> u\<close>.\<close>

text \<open>\<open>domB(D\<^sub>w 0) = T\<^bsub>w-1\<^esub>\<close> for \<open>0 < w\<close> (\<open>([].2)\<close>).\<close>

lemma domB_Dw0:
  assumes "0 < w"
  shows "domB (Dpt (enat w) 0\<^sub>B) = TBv (enat (w - 1))"
proof -
  have "enat w \<noteq> 0" using assms by (simp add: zero_enat_def)
  moreover have "enat w \<noteq> \<infinity>" by simp
  ultimately show ?thesis by (subst domB_unfold) simp
qed

text \<open>\<open>xseq b u 0 = D\<^sub>u 0\<close> (the base of the \<open>x\<close>-tower; no recursion, fired from
  the \<open>xseq\<close>-domain @{thm [source] xseq_dom_TBv_body}).\<close>

lemma xseq_eval_0:
  assumes db: "domB b = TBv (enat u')"
  shows "xseq b u 0 = Dprin u (Trm [])"
proof -
  have dom: "domB_operB_xseq_dom (Inr (Inr (b, u, 0)))"
    by (rule xseq_dom_TBv_body[OF db])
  show ?thesis using xseq.psimps[OF dom] by simp
qed

text \<open>Every tower entry is a single \<open>D\<^sub>u\<dash>\<close>headed principal:
  \<open>x\<^sub>0 = D\<^sub>u 0\<close> and \<open>x\<^bsub>i+1\<^esub> = D\<^sub>u b[x\<^sub>i]\<close> (corrected \<open>([].4)(ii)\<close>).\<close>

lemma xseq_single_TBv:
  assumes db: "domB b = TBv (enat u')"
  shows "\<exists>t. xseq b u i = Trm [DB u t]"
proof (cases i)
  case 0
  thus ?thesis using xseq_eval_0[OF db, of u] by auto
next
  case (Suc j)
  have dom: "domB_operB_xseq_dom (Inr (Inr (b, u, Suc j)))"
    by (rule xseq_dom_TBv_body[OF db])
  have "xseq b u (Suc j) = Dprin u (operB b (xseq b u j))"
    using xseq.psimps[OF dom] by simp
  thus ?thesis using Suc by auto
qed

text \<open>\<open>operB (D\<^sub>v 0) z = z\<close> for finite \<open>0 < v < \<infinity>\<close> (the \<open>([].2)\<close> identity, for
  an arbitrary second argument \<open>z\<close>).\<close>

lemma operB_Dv0_id:
  assumes vpos: "0 < v"
  shows "operB (Dpt (enat v) 0\<^sub>B) z = z"
proof -
  have dom: "domB_operB_xseq_dom (Inr (Inl (Dpt (enat v) 0\<^sub>B, z)))"
    by (rule operB_dom_Dv0)
  have v0: "enat v \<noteq> 0" using vpos by (simp add: zero_enat_def)
  have vinf: "enat v \<noteq> \<infinity>" by simp
  have "operB (Trm [DB (enat v) (Trm [])]) z
          = (if enat v = 0 then Trm []
             else if enat v = \<infinity> then Dprin (enat (numNat z + 1)) (Trm [])
             else z)"
    using operB.psimps[OF dom] by simp
  also have "\<dots> = z" using v0 vinf by simp
  finally show ?thesis by simp
qed

section \<open>§7.2 命題（scb分解と基本列の関係）conjunct (2): kind-1 / xseq-tower transport
  for the basic marked principal \<open>c\<^sub>2 = D\<^sub>u(D\<^sub>v 0)\<close> (\<open>s\<^sub>0 = b\<^sub>0 = ()\<close>)\<close>

text \<open>
  The THIRD conjunct of @{text p_7_2_scb_fseq} (kind-1 marked principal,
  the \<open>([].4)(ii)\<close> \<open>xseq\<close>-tower regime).  The article statement quantifies over
  an arbitrary inner scb-decomposition \<open>(D\<^sub>u s\<^sub>0, D\<^sub>v 0, b\<^sub>0)\<close> of \<open>c\<^sub>2\<close>; but for a
  NON-empty \<open>s\<^sub>0\<close> (the marked \<open>D\<^sub>v 0\<close> is a leaf nested below intermediate spine
  nodes, e.g. \<open>c\<^sub>2 = D\<^sub>u(D\<^sub>w(D\<^sub>v 0))\<close> with \<open>u < v \<le> w\<close>) the literal RHS
  \<open>s\<^sub>1 D\<^sub>u (s\<^sub>0 D\<^bsub>v-1\<^esub>)\<^bsup>n+1\<^esup> 0 b\<^sub>0\<^bsup>n+1\<^esup> b\<^sub>1\<close> is FALSE: the \<open>xseq\<close> tower produces
  \<open>D\<^sub>u (s\<^sub>0 D\<^bsub>v-1\<^esub>)\<^bsup>n\<^esup> D\<^bsub>v-1\<^esub> 0\<close> (one fewer copy of \<open>s\<^sub>0\<close>) — empirically refuted in
  @{path \<open>python/_scb_fseq_kind1.py\<close>} (cases C/D).  Both sides coincide exactly
  when \<open>s\<^sub>0 = ()\<close> and \<open>b\<^sub>0 = ()\<close>, i.e. \<open>c\<^sub>2 = D\<^sub>u(D\<^sub>v 0)\<close> directly — which is the
  regime the downstream §8.6/§8.7 零化 lemmas consume.  We prove that basic
  case in full (with \<open>t\<close> embedding \<open>c\<^sub>2\<close> arbitrarily as its kind-1 marked
  principal), via the NatSet scb-spine transport @{thm [source] operB_scb_spine},
  after evaluating \<open>operB (D\<^sub>u(D\<^sub>v 0)) (numBT n)\<close> through the \<open>xseq\<close> tower.\<close>

text \<open>The \<open>xseq\<close> tower over \<open>b = D\<^sub>v 0\<close> with index \<open>v-1\<close>:
  \<open>xseq (D\<^sub>v 0) (v-1) i = (D\<^bsub>v-1\<^esub>)\<^bsup>i+1\<^esup> 0\<close>.  Base \<open>xseq_eval_0\<close>; step
  \<open>xseq b u (Suc j) = operB b (D\<^sub>u (xseq b u j))\<close> with the \<open>([].2)\<close> identity
  @{thm [source] operB_Dv0_id} collapsing \<open>operB (D\<^sub>v 0) (D\<^bsub>v-1\<^esub> x) = D\<^bsub>v-1\<^esub> x\<close>.\<close>

lemma xseq_Dv0_tower:
  assumes vpos: "0 < v"
  shows "xseq (Dpt (enat v) 0\<^sub>B) (enat (v - 1)) i
           = ((\<lambda>a. Dpt (enat (v - 1)) a) ^^ (i + 1)) 0\<^sub>B"
proof (induction i)
  case 0
  have db: "domB (Dpt (enat v) 0\<^sub>B) = TBv (enat (v - 1))" by (rule domB_Dw0[OF vpos])
  show ?case
    using xseq_eval_0[OF db, of "enat (v - 1)"] by simp
next
  case (Suc i)
  have db: "domB (Dpt (enat v) 0\<^sub>B) = TBv (enat (v - 1))" by (rule domB_Dw0[OF vpos])
  have dom: "domB_operB_xseq_dom (Inr (Inr (Dpt (enat v) 0\<^sub>B, enat (v - 1), Suc i)))"
    by (rule xseq_dom_TBv_body[OF db])
  let ?x = "((\<lambda>a. Dpt (enat (v - 1)) a) ^^ (i + 1)) 0\<^sub>B"
  have "xseq (Dpt (enat v) 0\<^sub>B) (enat (v - 1)) (Suc i)
          = Dprin (enat (v - 1)) (operB (Dpt (enat v) 0\<^sub>B) (xseq (Dpt (enat v) 0\<^sub>B) (enat (v - 1)) i))"
    using xseq.psimps[OF dom] by simp
  also have "\<dots> = Dprin (enat (v - 1)) (operB (Dpt (enat v) 0\<^sub>B) ?x)"
    using Suc.IH by simp
  also have "\<dots> = Dprin (enat (v - 1)) ?x"
    using operB_Dv0_id[OF vpos] by simp
  also have "\<dots> = ((\<lambda>a. Dpt (enat (v - 1)) a) ^^ (Suc i + 1)) 0\<^sub>B"
    by simp
  finally show ?case .
qed

end
