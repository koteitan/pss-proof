theory Frontier_7_046
  imports Support_7_039
begin

lemma numBT_Suc0_ne_zero: "numBT (Suc 0) \<noteq> Trm []"
  by (simp add: numBT_def)

lemma NatSet_neq_zero: "NatSet \<noteq> {Trm []}"
proof
  assume H: "NatSet = {Trm []}"
  have m: "numBT (Suc 0) \<in> NatSet" by (simp add: NatSet_def)
  with H have "numBT (Suc 0) \<in> {Trm []}" by simp
  hence "numBT (Suc 0) = Trm []" by simp
  with numBT_Suc0_ne_zero show False by simp
qed

lemma NatSet_neq_TBv: "NatSet \<noteq> TBv (enat u)"
proof
  assume H: "NatSet = TBv (enat u)"
  let ?w = "Trm [DB 0 (Trm [DB 0 (Trm [])])]"
  have inT: "?w \<in> TBv (enat u)" by (simp add: TBv_def)
  have "?w \<in> NatSet" using H inT by simp
  then obtain n where wn: "Trm [DB 0 (Trm [DB 0 (Trm [])])] = Trm (replicate n (DB 0 (Trm [])))"
    by (auto simp: NatSet_def numBT_def)
  hence leq: "[DB 0 (Trm [DB 0 (Trm [])])] = replicate n (DB 0 (Trm []))" by simp
  have "DB 0 (Trm [DB 0 (Trm [])]) \<in> set (replicate n (DB 0 (Trm [])))"
    using leq by (metis list.set_intros(1))
  hence "DB 0 (Trm [DB 0 (Trm [])]) = DB 0 (Trm [])"
    by (auto split: if_splits)
  thus False by simp
qed

text \<open>The propagation step: if \<open>domB b = NatSet\<close> and \<open>b \<noteq> 0\<close>, then any
  single principal \<open>D\<^sub>v b\<close> over it also has \<open>domB = NatSet\<close>.  By
  @{thm [source] domB_unfold} on the single-component branch: \<open>db = NatSet\<close>
  is neither \<open>{0}\<close> (@{thm [source] NatSet_neq_zero}) nor any \<open>T\<^sub>u\<close>
  (@{thm [source] NatSet_neq_TBv}), so it lands in the \<open>else db\<close> branch.\<close>

lemma domB_principal_NatSet:
  assumes db: "domB b = NatSet" and bne: "b \<noteq> Trm []"
  shows "domB (Trm [DB v b]) = NatSet"
proof -
  have "domB (Trm [DB v b]) =
          (let db = domB b in
           if db = {Trm []} then NatSet
           else if (\<exists>u. v \<le> enat u \<and> db = TBv (enat u)) then NatSet
           else db)"
    using bne by (subst domB_unfold) simp
  also have "\<dots> = NatSet"
    using db NatSet_neq_zero NatSet_neq_TBv by (auto simp: Let_def)
  finally show ?thesis .
qed

text \<open>\<open>domB\<close> reads only the last principal component (the multi-branch of
  @{thm [source] domB_unfold} collapses to the last component; the single and
  empty cases are trivial).\<close>

lemma domB_last_component:
  assumes ne: "xs \<noteq> []"
  shows "domB (Trm xs) = domB (Trm [last xs])"
proof (cases xs)
  case Nil thus ?thesis using ne by simp
next
  case (Cons p0 ps1)
  show ?thesis
  proof (cases ps1)
    case Nil thus ?thesis using Cons by simp
  next
    case (Cons q ps2)
    obtain v bb where p0eq: "p0 = DB v bb" by (cases p0)
    have unf: "domB (Trm (p0 # q # ps2)) = domB (Trm [last (p0 # q # ps2)])"
      unfolding p0eq by (subst domB_unfold) (simp only: BT.case list.case BP.case)
    thus ?thesis using \<open>xs = p0 # ps1\<close> Cons by simp
  qed
qed

text \<open>\<open>dom\<close>-heredity (\<open>m_8_7_OT_dom_hereditary\<close>, article 5962).  The all-\<open>RP\<close>
  tail pins the occurrence of \<open>flat t'\<close> onto the RIGHT spine of \<open>t\<close>
  (@{thm [source] scb_to_last_component}); \<open>domB\<close> only reads the right spine
  (@{thm [source] domB_last_component}), so \<open>NatSet\<close> propagates up via
  @{thm [source] domB_principal_NatSet}.  No \<open>operB\<close> totality is used —
  \<open>domB\<close> alone (now unconditional).\<close>

lemma domB_hereditary_aux:
  "\<And>s b. scb_decomp t s (flatBT (Trm [cp])) b \<Longrightarrow> domB (Trm [cp]) = NatSet
        \<Longrightarrow> dfree_BP cp \<Longrightarrow> domB t = NatSet"
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
  \<comment> \<open>pin the occurrence into the last component of \<open>t\<close>\<close>
  obtain sc bc where comp: "flatBP (last (untrm t)) = sc @ flatBP cp @ bc"
      and rbc: "\<forall>x \<in> set bc. x = RP"
    using scb_to_last_component[OF less.prems(1) tne] by blast
  obtain w lb where lpw: "last (untrm t) = DB w lb"
    by (cases "last (untrm t)") auto
  \<comment> \<open>\<open>domB t = domB (Trm [last component])\<close>\<close>
  obtain ts where tT: "t = Trm ts" by (cases t) auto
  have tsne: "ts \<noteq> []" using tne tT by auto
  have domLast: "domB t = domB (Trm [last ts])"
    unfolding tT by (rule domB_last_component[OF tsne])
  have lastEq: "last ts = DB w lb" using lpw tT by simp
  \<comment> \<open>the occurrence sits in \<open>flatBP (DB w lb) = Dsym w # flatBT lb\<close>\<close>
  have flateq: "Dsym w # flatBT lb = sc @ flatBP cp @ bc"
    using comp lpw by simp
  obtain w' cb' where cpw: "cp = DB w' cb'" by (cases cp) auto
  show ?case
  proof (cases "sc = []")
    case True
    \<comment> \<open>whole component: \<open>cp = DB w lb\<close>, so \<open>Trm [last ts] = Trm [cp]\<close>\<close>
    have e: "flatBP (DB w lb) @ [] = flatBP cp @ bc"
      using flateq True by simp
    have "flatBP (DB w lb) = flatBP cp \<and> [] = bc"
      using flatinj_flatBP_cancel[OF e] by blast
    hence "DB w lb = cp" using m_7_flatBT_inj cpw by simp
    hence "domB (Trm [last ts]) = domB (Trm [cp])" using lastEq by simp
    thus ?thesis using domLast less.prems(2) by simp
  next
    case False
    \<comment> \<open>occurrence inside the body \<open>lb\<close>: descend\<close>
    obtain sc1 where sc1: "sc = Dsym w # sc1"
      using flateq False by (cases sc) auto
    have aeq: "flatBT lb = sc1 @ flatBP cp @ bc"
      using flateq sc1 by simp
    have lbne: "lb \<noteq> Trm []"
    proof
      assume "lb = Trm []"
      hence "flatBT lb = [Zsym]" by simp
      thus False using aeq cpw by (cases sc1) auto
    qed
    have scbLb: "scb_decomp lb sc1 (flatBT (Trm [cp])) bc"
      unfolding scb_decomp_def using aeq rbc less.prems(3)
      by (auto simp: isPTB_str_def intro: exI[of _ cp])
    \<comment> \<open>\<open>size lb < size t\<close>\<close>
    have szlt: "size lb < size t"
      using rnsub_size_arg_lt'[of ts w lb] lastEq tsne tT by simp
    have domLb: "domB lb = NatSet"
      by (rule less.IH[OF szlt scbLb less.prems(2) less.prems(3)])
    have "domB (Trm [DB w lb]) = NatSet"
      by (rule domB_principal_NatSet[OF domLb lbne])
    hence "domB (Trm [last ts]) = NatSet" using lastEq by simp
    thus ?thesis using domLast by simp
  qed
qed

section \<open>§7.2 dom-可分解性 (p_7_2_scb_unique conjunct (2)) — domB side now unblocked\<close>

text \<open>
  Conjunct (2) of \<open>p_7_2_scb_unique\<close>: for \<open>t \<in> T\<^bsub>B\<^esub>\<close>,
    \<open>domB t = NatSet \<longleftrightarrow> (scb_kind0_able t \<or> scb_kind1_able t)\<close>.
  The earlier encoding made the RHS vacuous at \<open>t = Trm []\<close>; the retraction of
  A14 identifies that as an encoding artefact, not an article defect.  The current
  positive \<open>isPTB_str c\<close> conjunct excludes zero from both kind predicates.  The
  helper developed here retains \<open>t \<noteq> Trm []\<close> as its nonempty-branch premise;
  @{text p_7_2_scb_unique} assembles the article's unconditional statement by handling
  zero separately.

  Previously blocked on \<open>domB\<close> termination; now \<open>domB_dom_all\<close>/\<open>domB_unfold\<close>
  (proven this session) make \<open>domB\<close> total and unfoldable, so the \<open>domB\<close> side is
  reachable by right-spine induction.

  Empirically (\<open>check_dom2.py\<close>, BT model, indices \<open>{0,1,2}\<close>, depth 3, width 2,
  ~22M nonempty terms, 0 mismatches) the two-sided characterization is, with
  \<open>R = RightNodes t\<close>, \<open>j\<^sub>1 = Lng R - 1\<close>:
    \<open>domB t = NatSet \<longleftrightarrow> j\<^sub>1 \<ge> 1 \<and> (R!j\<^sub>1 = 0 \<or> (\<exists>k < j\<^sub>1. R!k < R!j\<^sub>1))\<close>
  and the same RHS-shape \<longleftrightarrow> \<open>scb_kind0_able t \<or> scb_kind1_able t\<close>.  The
  \<open>\<Rightarrow>\<close>-direction of the latter (kind-able \<Rightarrow> shape) is the GREEN
  @{thm [source] rnsub_kindable_imp_natshape} (now in \<open>Support_7_013\<close>).
\<close>

\<comment> \<open>The \<open>RightNodes\<close>-shape predicate that characterizes \<open>domB t = NatSet\<close>.\<close>
definition rnNatShape :: "nat list \<Rightarrow> bool" where
  "rnNatShape R \<longleftrightarrow> length R \<ge> 2
       \<and> (R ! (length R - 1) = 0 \<or> (\<exists>k < length R - 1. R ! k < R ! (length R - 1)))"

\<comment> \<open>\<open>TBv\<close> is injective on finite indices: distinct \<open>enat\<close> levels give distinct
   index sets (\<open>D\<^bsub>n'\<^esub> 0\<close> separates \<open>T\<^bsub>n\<^esub>\<close> from \<open>T\<^bsub>n'\<^esub>\<close> when \<open>n < n'\<close>).\<close>
lemma TBv_enat_inj:
  assumes "TBv (enat m) = TBv (enat n)"
  shows "m = n"
proof (rule ccontr)
  assume "m \<noteq> n"
  then consider "m < n" | "n < m" by linarith
  thus False
  proof cases
    case 1
    have "Trm [DB (enat n) (Trm [])] \<in> TBv (enat n)" by (simp add: TBv_def)
    hence "Trm [DB (enat n) (Trm [])] \<in> TBv (enat m)" using assms by simp
    hence "enat n \<le> enat m" by (simp add: TBv_def)
    thus False using 1 by simp
  next
    case 2
    have "Trm [DB (enat m) (Trm [])] \<in> TBv (enat m)" by (simp add: TBv_def)
    hence "Trm [DB (enat m) (Trm [])] \<in> TBv (enat n)" using assms by simp
    hence "enat m \<le> enat n" by (simp add: TBv_def)
    thus False using 2 by simp
  qed
qed

\<comment> \<open>\<open>{Trm []} \<noteq> TBv (enat u)\<close>: \<open>D\<^bsub>u+1\<^esub> 0 \<in> T\<^bsub>u+1\<^esub> \<subseteq> ... \<close> no — directly:
   \<open>Trm [] = {Trm []}\<close> is a singleton containing \<open>0\<close>, while \<open>TBv\<close> contains \<open>0\<close>
   too, so separate by a nonzero member.  \<open>D\<^bsub>u\<^esub> 0 \<in> TBv (enat u)\<close> but \<open>\<noteq> Trm []\<close>.\<close>
lemma zero_set_neq_TBv: "{Trm []} \<noteq> TBv (enat u)"
proof
  assume H: "{Trm []} = TBv (enat u)"
  have "Trm [DB (enat u) (Trm [])] \<in> TBv (enat u)" by (simp add: TBv_def)
  hence "Trm [DB (enat u) (Trm [])] \<in> {Trm []}" using H by simp
  thus False by simp
qed

text \<open>The master classification of \<open>domB t\<close> in terms of \<open>R = RightNodes t\<close>, by
  strong induction along the right spine (\<open>domB\<close> and \<open>RightNodes\<close> both read only
  the last principal component).  For \<open>t \<in> T\<^bsub>B\<^esub>\<close>, \<open>t \<noteq> 0\<close>, with \<open>m = last R\<close>:
  \<^item> if \<open>rnNatShape R\<close> then \<open>domB t = NatSet\<close>;
  \<^item> else if \<open>m = 0\<close> then \<open>domB t = {Trm []}\<close> (and \<open>R = [0]\<close>);
  \<^item> else \<open>domB t = TBv (enat (m - 1))\<close>.\<close>
lemma domB_classify_RN:
  "t \<in> T_B \<Longrightarrow> t \<noteq> Trm [] \<Longrightarrow>
       (rnNatShape (RightNodes t) \<longrightarrow> domB t = NatSet)
     \<and> (\<not> rnNatShape (RightNodes t) \<and> last (RightNodes t) = 0
          \<longrightarrow> domB t = {Trm []})
     \<and> (\<not> rnNatShape (RightNodes t) \<and> last (RightNodes t) \<noteq> 0
          \<longrightarrow> domB t = TBv (enat (last (RightNodes t) - 1)))"
proof (induction t rule: measure_induct_rule[where f=size])
  case (less t)
  obtain ys where ys: "t = Trm ys" by (cases t)
  have ysne: "ys \<noteq> []" using less.prems(2) ys by auto
  \<comment> \<open>reduce \<open>domB\<close> and \<open>RightNodes\<close> to the last principal component\<close>
  obtain u a where lastp: "last ys = DB u a"
    by (cases "last ys")
  have domLast: "domB t = domB (Trm [DB u a])"
    unfolding ys using domB_last_component[OF ysne] lastp by simp
  have RNlast: "RightNodes t = the_enat u # RightNodes a"
    unfolding ys using rnsub_RightNodes_last[OF ysne] lastp by simp
  \<comment> \<open>\<open>T\<^bsub>B\<^esub>\<close> facts about the last principal\<close>
  have ufin: "u \<noteq> \<infinity>" and aTB: "a \<in> T_B"
    using rnsub_TB_last[OF _ ysne lastp] less.prems(1) ys by auto
  obtain un where un: "u = enat un" using ufin by (cases u) auto
  have uthe: "the_enat u = un" using un by simp
  let ?Ra = "RightNodes a"
  let ?R = "RightNodes t"
  have Rcons: "?R = un # ?Ra" using RNlast uthe by simp
  show ?case
  proof (cases "a = Trm []")
    case True
    \<comment> \<open>bottom of the spine: single principal over \<open>0\<close>, \<open>R = [un]\<close>\<close>
    have Ra0: "?Ra = []" using True by simp
    have Req: "?R = [un]" using Rcons Ra0 by simp
    have notshape: "\<not> rnNatShape ?R" using Req by (simp add: rnNatShape_def)
    have lastR: "last ?R = un" using Req by simp
    have domeval: "domB (Trm [DB u a]) =
          (if un = 0 then {Trm []} else TBv (enat (un - 1)))"
    proof -
      have "domB (Trm [DB u a]) =
              (if a = Trm [] then
                 (if u = 0 then {Trm []}
                  else if u = \<infinity> then NatSet
                  else TBv (enat (the_enat u - 1)))
               else (let db = domB a in
                     if db = {Trm []} then NatSet
                     else if (\<exists>u'. u \<le> enat u' \<and> db = TBv (enat u')) then NatSet
                     else db))"
        by (subst domB_unfold) (simp only: BT.case list.case BP.case)
      also have "\<dots> = (if un = 0 then {Trm []} else TBv (enat (un - 1)))"
        using True ufin un uthe by (simp add: zero_enat_def)
      finally show ?thesis .
    qed
    show ?thesis
    proof (cases "un = 0")
      case True
      have "domB t = {Trm []}" using domLast domeval True by simp
      thus ?thesis using notshape lastR True by simp
    next
      case False
      have "domB t = TBv (enat (un - 1))" using domLast domeval False by simp
      thus ?thesis using notshape lastR False by simp
    qed
  next
    case False
    \<comment> \<open>recursive step: descend into \<open>a\<close>, apply IH\<close>
    have szlt: "size a < size t"
      using rnsub_size_arg_lt'[OF lastp ysne] ys by simp
    have ane: "a \<noteq> Trm []" using False .
    have IH: "(rnNatShape ?Ra \<longrightarrow> domB a = NatSet)
            \<and> (\<not> rnNatShape ?Ra \<and> last ?Ra = 0 \<longrightarrow> domB a = {Trm []})
            \<and> (\<not> rnNatShape ?Ra \<and> last ?Ra \<noteq> 0
                 \<longrightarrow> domB a = TBv (enat (last ?Ra - 1)))"
      using less.IH[OF szlt aTB ane] by simp
    have Rane: "?Ra \<noteq> []"
    proof -
      obtain w c where "last (untrm a) = DB w c"
        by (cases "last (untrm a)")
      moreover obtain zs where "a = Trm zs" by (cases a)
      ultimately show ?thesis using ane by (cases zs) auto
    qed
    have lenRa1: "length ?Ra \<ge> 1" using Rane by (cases ?Ra) auto
    \<comment> \<open>the \<open>domB\<close> evaluation at the principal level (nonzero body branch)\<close>
    have domeval: "domB (Trm [DB u a]) =
          (let db = domB a in
           if db = {Trm []} then NatSet
           else if (\<exists>u'. u \<le> enat u' \<and> db = TBv (enat u')) then NatSet
           else db)"
      using ane by (subst domB_unfold) (simp only: BT.case list.case BP.case if_False)
    \<comment> \<open>last of \<open>?R\<close> equals last of \<open>?Ra\<close>\<close>
    have lastReq: "last ?R = last ?Ra" using Rcons Rane by simp
    \<comment> \<open>case split on the IH classification of \<open>domB a\<close>\<close>
    show ?thesis
    proof (cases "rnNatShape ?Ra")
      case True
      \<comment> \<open>\<open>domB a = NatSet\<close>; then so is the principal (else-db branch)\<close>
      have da: "domB a = NatSet" using IH True by simp
      have dt: "domB t = NatSet"
        using domLast domeval da NatSet_neq_zero NatSet_neq_TBv
        by (auto simp: Let_def)
      \<comment> \<open>and the parent shape holds too (NAT propagates up the spine)\<close>
      have shapeP: "rnNatShape ?R"
      proof -
        have len2: "length ?Ra \<ge> 2"
          using True unfolding rnNatShape_def by simp
        have disj: "?Ra ! (length ?Ra - 1) = 0
                    \<or> (\<exists>k < length ?Ra - 1. ?Ra ! k < ?Ra ! (length ?Ra - 1))"
          using True unfolding rnNatShape_def by simp
        \<comment> \<open>shift indices by one for the cons \<open>?R = un # ?Ra\<close>\<close>
        have lenR: "length ?R = length ?Ra + 1" using Rcons by simp
        have RaNe: "?Ra \<noteq> []" using len2 by (cases ?Ra) auto
        have lastRR: "?R ! (length ?R - 1) = ?Ra ! (length ?Ra - 1)"
        proof -
          have "?R ! (length ?R - 1) = last ?R"
            using Rcons by (simp add: last_conv_nth)
          also have "\<dots> = last ?Ra" using Rcons RaNe by simp
          also have "\<dots> = ?Ra ! (length ?Ra - 1)"
            using RaNe by (simp add: last_conv_nth)
          finally show ?thesis .
        qed
        from disj show ?thesis
        proof
          assume z: "?Ra ! (length ?Ra - 1) = 0"
          have lenR2: "length ?R \<ge> 2" using lenR len2 by simp
          have "?R ! (length ?R - 1) = 0" using lastRR z by simp
          thus ?thesis using lenR2 unfolding rnNatShape_def by simp
        next
          assume "\<exists>k < length ?Ra - 1. ?Ra ! k < ?Ra ! (length ?Ra - 1)"
          then obtain k where klt: "k < length ?Ra - 1"
            and lt: "?Ra ! k < ?Ra ! (length ?Ra - 1)" by blast
          have lenR2: "length ?R \<ge> 2" using lenR len2 by simp
          have rsk: "?R ! (Suc k) = ?Ra ! k" using Rcons by simp
          have sklt: "Suc k < length ?R - 1" using klt lenR by simp
          have "?R ! (Suc k) < ?R ! (length ?R - 1)"
            using rsk lt lastRR by simp
          thus ?thesis using lenR2 sklt unfolding rnNatShape_def by blast
        qed
      qed
      show ?thesis using dt shapeP by simp
    next
      case False
      \<comment> \<open>\<open>domB a\<close> is \<open>{Trm []}\<close> or \<open>TBv (enat (last ?Ra - 1))\<close>\<close>
      let ?m = "last ?Ra"
      show ?thesis
      proof (cases "?m = 0")
        case True
        \<comment> \<open>\<open>domB a = {Trm []}\<close>; principal hits the \<open>db = {Trm []}\<close> branch \<Rightarrow> NatSet\<close>
        have da: "domB a = {Trm []}" using IH False True by simp
        have dt: "domB t = NatSet"
          using domLast domeval da by (simp add: Let_def)
        \<comment> \<open>parent shape: last of \<open>?R\<close> is \<open>0\<close>, length \<open>\<ge> 2\<close>\<close>
        have lenR: "length ?R \<ge> 2" using Rcons lenRa1 by simp
        have RNe: "?R \<noteq> []" using lenR by (cases ?R) auto
        have lastRa0: "last ?Ra = 0" using True by simp
        have "?R ! (length ?R - 1) = last ?R" using RNe by (simp add: last_conv_nth)
        also have "\<dots> = last ?Ra" using lastReq by simp
        also have "\<dots> = 0" using lastRa0 by simp
        finally have "?R ! (length ?R - 1) = 0" .
        hence shapeP: "rnNatShape ?R" using lenR unfolding rnNatShape_def by simp
        show ?thesis using dt shapeP by simp
      next
        case False
        note mne = False
        \<comment> \<open>\<open>domB a = TBv (enat (?m - 1))\<close>; the \<open>v \<le> u'\<close> test decides NAT vs TBv\<close>
        have da: "domB a = TBv (enat (?m - 1))"
          using IH \<open>\<not> rnNatShape ?Ra\<close> mne by simp
        \<comment> \<open>the existential test \<open>\<exists>u'. u \<le> enat u' \<and> domB a = TBv (enat u')\<close>
           reduces, by \<open>TBv\<close> injectivity, to \<open>un \<le> ?m - 1\<close>\<close>
        have testeq: "(\<exists>u'. u \<le> enat u' \<and> domB a = TBv (enat u'))
                        \<longleftrightarrow> un \<le> ?m - 1"
        proof
          assume "\<exists>u'. u \<le> enat u' \<and> domB a = TBv (enat u')"
          then obtain u' where ule: "u \<le> enat u'" and "domB a = TBv (enat u')" by blast
          hence "TBv (enat (?m - 1)) = TBv (enat u')" using da by simp
          hence "?m - 1 = u'" by (rule TBv_enat_inj)
          thus "un \<le> ?m - 1" using ule un by simp
        next
          assume "un \<le> ?m - 1"
          hence "u \<le> enat (?m - 1)" using un by simp
          thus "\<exists>u'. u \<le> enat u' \<and> domB a = TBv (enat u')" using da by blast
        qed
        have dazero: "domB a \<noteq> {Trm []}"
          using da zero_set_neq_TBv[of "?m - 1"] by auto
        \<comment> \<open>value of the let-expression in terms of the test result\<close>
        have letval: "domB (Trm [DB u a]) =
              (if (\<exists>u'. u \<le> enat u' \<and> domB a = TBv (enat u')) then NatSet
               else domB a)"
          using domeval dazero by (simp add: Let_def)
        show ?thesis
        proof (cases "un \<le> ?m - 1")
          case True
          note ule = True
          \<comment> \<open>test fires \<Rightarrow> \<open>domB t = NatSet\<close>; parent shape holds (\<open>un < ?m\<close>)\<close>
          have testT: "\<exists>u'. u \<le> enat u' \<and> domB a = TBv (enat u')"
            using testeq ule by simp
          have dt: "domB t = NatSet"
          proof -
            have "domB t = domB (Trm [DB u a])" by (rule domLast)
            also have "\<dots> = NatSet" using letval testT by simp
            finally show ?thesis .
          qed
          \<comment> \<open>\<open>un \<le> ?m - 1 < ?m\<close> (since \<open>?m \<noteq> 0\<close>), and \<open>?m = last ?R = ?R!(len-1)\<close>\<close>
          have unlt: "un < ?m" using ule mne by simp
          have lenR: "length ?R \<ge> 2" using Rcons lenRa1 by simp
          have RNe: "?R \<noteq> []" using lenR by (cases ?R) auto
          have lastposR: "?R ! (length ?R - 1) = ?m"
          proof -
            have "?R ! (length ?R - 1) = last ?R" using RNe by (simp add: last_conv_nth)
            also have "\<dots> = last ?Ra" using lastReq by simp
            finally show ?thesis by simp
          qed
          have "?R ! 0 = un" using Rcons by simp
          hence "?R ! 0 < ?R ! (length ?R - 1)" using unlt lastposR by simp
          moreover have "(0::nat) < length ?R - 1" using lenR by simp
          ultimately have shapeP: "rnNatShape ?R"
            using lenR unfolding rnNatShape_def by blast
          show ?thesis using dt shapeP by simp
        next
          case False
          note nule = False
          \<comment> \<open>test fails \<Rightarrow> \<open>domB t = domB a = TBv (enat (?m - 1))\<close>; NOT shape\<close>
          have testF: "\<not> (\<exists>u'. u \<le> enat u' \<and> domB a = TBv (enat u'))"
            using testeq nule by simp
          have dt: "domB t = TBv (enat (?m - 1))"
          proof -
            have "domB t = domB (Trm [DB u a])" by (rule domLast)
            also have "\<dots> = domB a" using letval testF by simp
            also have "\<dots> = TBv (enat (?m - 1))" by (rule da)
            finally show ?thesis .
          qed
          \<comment> \<open>parent is NOT shape: last \<open>= ?m \<noteq> 0\<close> and every earlier entry \<open>\<ge> ?m\<close>\<close>
          have notshapeRa: "\<not> rnNatShape ?Ra" using \<open>\<not> rnNatShape ?Ra\<close> .
          have lenR0: "length ?R \<ge> 2" using Rcons lenRa1 by simp
          have RNe0: "?R \<noteq> []" using lenR0 by (cases ?R) auto
          have lastposR: "?R ! (length ?R - 1) = ?m"
          proof -
            have "?R ! (length ?R - 1) = last ?R" using RNe0 by (simp add: last_conv_nth)
            also have "\<dots> = last ?Ra" using lastReq by simp
            finally show ?thesis by simp
          qed
          have notshapeP: "\<not> rnNatShape ?R"
          proof
            assume rns: "rnNatShape ?R"
            have len2: "length ?R \<ge> 2"
              using rns unfolding rnNatShape_def by simp
            have rdisj: "?R ! (length ?R - 1) = 0
                          \<or> (\<exists>k < length ?R - 1. ?R ! k < ?R ! (length ?R - 1))"
              using rns unfolding rnNatShape_def by simp
            \<comment> \<open>last \<open>= ?m \<noteq> 0\<close>, so the disjunct must be \<open>?R ! k < ?m\<close>\<close>
            have lnz: "?R ! (length ?R - 1) \<noteq> 0" using lastposR mne by simp
            obtain k where klt: "k < length ?R - 1"
              and ltk0: "?R ! k < ?R ! (length ?R - 1)"
              using rdisj lnz by blast
            have ltk: "?R ! k < ?m" using ltk0 lastposR by simp
            \<comment> \<open>derive a witness against \<open>\<not> rnNatShape ?Ra\<close> or against \<open>un \<ge> ?m\<close>\<close>
            show False
            proof (cases k)
              case 0
              have "?R ! 0 = un" using Rcons by simp
              hence "un < ?m" using ltk 0 by simp
              thus False using nule by simp
            next
              case (Suc k0)
              \<comment> \<open>\<open>?R ! (Suc k0) = ?Ra ! k0\<close>, with \<open>k0 < length ?Ra - 1\<close>\<close>
              have lenR: "length ?R = length ?Ra + 1" using Rcons by simp
              have RaK: "?R ! (Suc k0) = ?Ra ! k0" using Rcons by simp
              have k0lt: "k0 < length ?Ra - 1" using klt Suc lenR by simp
              have lastRaeq: "?Ra ! (length ?Ra - 1) = ?m"
                using Rane last_conv_nth[OF Rane] by simp
              \<comment> \<open>\<open>?Ra ! k0 = ?R ! (Suc k0) < ?m = ?Ra ! (length ?Ra - 1)\<close>:
                 this makes \<open>rnNatShape ?Ra\<close>, contradicting \<open>\<not> rnNatShape ?Ra\<close>\<close>
              have len2Ra: "length ?Ra \<ge> 2" using k0lt by linarith
              have "?Ra ! k0 < ?Ra ! (length ?Ra - 1)"
                using RaK Suc ltk lastRaeq by simp
              hence "rnNatShape ?Ra" using k0lt len2Ra
                unfolding rnNatShape_def by blast
              thus False using notshapeRa by simp
            qed
          qed
          have lastRm: "last ?R = ?m" using lastReq by simp
          show ?thesis using dt notshapeP lastRm mne
            by simp
        qed
      qed
    qed
  qed
qed

end
