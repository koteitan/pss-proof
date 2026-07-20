theory Frontier_7_050
  imports Support_7_043
begin

text \<open>\<open>operB\<close>-domain for a multi-component term reduces to the last component
  (the only operB recursive call in the multi-branch).\<close>

lemma operB_dom_multi:
  assumes "domB_operB_xseq_dom (Inr (Inl (Trm [last (p0 # q # qs)], z)))"
  shows "domB_operB_xseq_dom (Inr (Inl (Trm (p0 # q # qs), z)))"
proof (rule domB_operB_xseq.domintros(2))
  show "domB_operB_xseq_dom (Inl x2)"
    if "Trm (p0 # q # qs) = Trm [DB x1 x2]" "x2 \<noteq> Trm []" for x1 x2
    using that(1) by simp
next
  show "domB_operB_xseq_dom (Inr (Inl (x2, Trm [])))"
    if "Trm (p0 # q # qs) = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "{Trm []} = domB x2" for x1 x2
    using that(1) by simp
next
  show "xb = Trm []"
    if "Trm (p0 # q # qs) = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "x1 \<le> enat u"
       "domB x2 = TBv (enat u)"
       "\<not> domB_operB_xseq_dom (Inr (Inr (x2, enat (tbvIdx (TBv (enat u))), numNat z)))"
       "xb \<in> TBv (enat u)" for x1 x2 u xb
    using that(1) by simp
next
  show "Trm [] \<in> TBv (enat u)"
    if "Trm (p0 # q # qs) = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "x1 \<le> enat u"
       "domB x2 = TBv (enat u)"
       "\<not> domB_operB_xseq_dom (Inr (Inr (x2, enat (tbvIdx (TBv (enat u))), numNat z)))"
       for x1 x2 u
    using that(1) by simp
next
  show "xb = Trm []"
    if "Trm (p0 # q # qs) = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "x1 \<le> enat u"
       "domB x2 = TBv (enat u)"
       "\<not> domB_operB_xseq_dom (Inr (Inl (x2, xseq x2 (enat (tbvIdx (TBv (enat u)))) (numNat z))))"
       "xb \<in> TBv (enat u)" for x1 x2 u xb
    using that(1) by simp
next
  show "Trm [] \<in> TBv (enat u)"
    if "Trm (p0 # q # qs) = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "x1 \<le> enat u"
       "domB x2 = TBv (enat u)"
       "\<not> domB_operB_xseq_dom (Inr (Inl (x2, xseq x2 (enat (tbvIdx (TBv (enat u)))) (numNat z))))"
       for x1 x2 u
    using that(1) by simp
next
  show "xb = Trm []"
    if "Trm (p0 # q # qs) = Trm [DB x1 x2]" "x2 \<noteq> Trm []"
       "\<forall>u. x1 \<le> enat u \<longrightarrow> domB x2 \<noteq> TBv (enat u)"
       "\<not> domB_operB_xseq_dom (Inr (Inl (x2, z)))"
       "xb \<in> domB x2" for x1 x2 xb
    using that(1) by simp
next
  show "Trm [] \<in> domB x2"
    if "Trm (p0 # q # qs) = Trm [DB x1 x2]" "x2 \<noteq> Trm []"
       "\<forall>u. x1 \<le> enat u \<longrightarrow> domB x2 \<noteq> TBv (enat u)"
       "\<not> domB_operB_xseq_dom (Inr (Inl (x2, z)))" for x1 x2
    using that(1) by simp
next
  \<comment> \<open>(8) two-component multi \<open>Trm [p, q]\<close>: here \<open>qs = []\<close>, \<open>last = x21a\<close>\<close>
  show "domB_operB_xseq_dom (Inr (Inl (Trm [x21a], z)))"
    if "Trm (p0 # q # qs) = Trm [DB x1 x2, x21a]" for x1 x2 x21a
  proof -
    have qs0: "qs = []" and qeq: "q = x21a" using that by auto
    have "last (p0 # q # qs) = x21a" using qs0 qeq by simp
    thus ?thesis using assms by simp
  qed
next
  \<comment> \<open>(9) \<open>(\<ge>3)\<close>-component multi: \<open>last x22a = last (p0#q#qs)\<close>\<close>
  show "domB_operB_xseq_dom (Inr (Inl (Trm [last x22a], z)))"
    if "Trm (p0 # q # qs) = Trm (DB x1 x2 # x21a # x22a)" "x22a \<noteq> []" for x1 x2 x21a x22a
  proof -
    have "q = x21a" and "qs = x22a" using that(1) by auto
    hence "last x22a = last (p0 # q # qs)" using that(2) by simp
    thus ?thesis using assms by simp
  qed
qed

text \<open>\<open>operB\<close>-domain heredity UP the right spine.\<close>

lemma operB_dom_spine_aux:
  "\<And>s b. scb_decomp t s (flatBT (Trm [cp])) b
        \<Longrightarrow> domB (Trm [cp]) = NatSet \<Longrightarrow> dfree_BP cp
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
  have domLast: "domB_operB_xseq_dom (Inr (Inl (Trm [DB w lb], z)))"
  proof (cases "sc = []")
    case True
    have e: "flatBP (DB w lb) @ [] = flatBP cp @ bc" using flateq True by simp
    have "flatBP (DB w lb) = flatBP cp \<and> [] = bc"
      using flatinj_flatBP_cancel[OF e] by blast
    hence cpEq: "DB w lb = cp" using m_7_flatBT_inj cpw by simp
    show ?thesis using cpEq less.prems(4) by simp
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
    have domLb: "domB_operB_xseq_dom (Inr (Inl (lb, z)))"
      by (rule less.IH[OF szlt scbLb less.prems(2) less.prems(3) less.prems(4)])
    have domLbNat: "domB lb = NatSet"
      by (rule domB_hereditary_aux[OF scbLb less.prems(2) less.prems(3)])
    show ?thesis
      by (rule operB_dom_NatSet_principal[OF domLbNat lbne domLb])
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

text \<open>Flat of a multi-component term with last component peeled off:
  \<open>flat(Trm(rs@[p])) = Wpre rs @ flatBP p @ [RP]\<close>, \<open>rs \<noteq> []\<close>.  The wrapper
  \<open>Wpre rs\<close> depends only on \<open>rs\<close>, so it is identical for \<open>t\<close> and \<open>operB t z\<close>.\<close>

definition Wpre :: "BP list \<Rightarrow> Sym list" where
  "Wpre rs = LP # flatBP (hd rs) @ concat (map (\<lambda>r. CM # flatBP r) (tl rs)) @ [CM]"

lemma flatBT_multi_last:
  assumes "rs \<noteq> []"
  shows "flatBT (Trm (rs @ [p])) = Wpre rs @ flatBP p @ [RP]"
proof -
  obtain p0 ps where rs: "rs = p0 # ps" using assms by (cases rs) auto
  have "flatBT (Trm ((p0 # ps) @ [p]))
          = LP # (flatBP p0 @ concat (map (\<lambda>r. CM # flatBP r) (ps @ [p]))) @ [RP]"
    by (cases "ps @ [p]") simp_all
  also have "\<dots> = LP # flatBP p0 @ concat (map (\<lambda>r. CM # flatBP r) ps) @ (CM # flatBP p) @ [RP]"
    by simp
  also have "\<dots> = Wpre (p0 # ps) @ flatBP p @ [RP]"
    by (simp add: Wpre_def)
  finally show ?thesis using rs by simp
qed

text \<open>Spine-descent flat identity (the outer lift).  Extra hypothesis: the marked
  principal's \<open>operB\<close>-image is a single principal \<open>Trm [rp]\<close> (true for our \<open>cp\<close>,
  whose image is \<open>D\<^sub>u(\<dots>)\<close>); this keeps the multi-component flat clean.\<close>

lemma operB_scb_spine:
  "\<And>s b. scb_decomp t s (flatBT (Trm [cp])) b
        \<Longrightarrow> domB (Trm [cp]) = NatSet \<Longrightarrow> dfree_BP cp
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
    by (rule operB_dom_spine_aux[OF less.prems(1) less.prems(2) less.prems(3) less.prems(4)])
  have operimg: "flatBT (operB (Trm [cp]) z) = flatBP rp"
    using less.prems(5) by simp
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
        using lastp cpEq less.prems(5) by simp
      have operT: "operB t z = Trm (?rs @ [rp])"
        using peel opercp tdecomp by simp
      \<comment> \<open>flat of \<open>t\<close>: \<open>s = Wpre ?rs\<close>, \<open>b = [RP]\<close>\<close>
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
      \<comment> \<open>flat of \<open>operB t z\<close>\<close>
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
    have domLbNat: "domB lb = NatSet"
      by (rule domB_hereditary_aux[OF scbLb less.prems(2) less.prems(3)])
    have domLb: "domB_operB_xseq_dom (Inr (Inl (lb, z)))"
      by (rule operB_dom_spine_aux[OF scbLb less.prems(2) less.prems(3) less.prems(4)])
    have ih: "flatBT (operB lb z) = sc1 @ flatBT (operB (Trm [cp]) z) @ bc"
      by (rule less.IH[OF szlt scbLb less.prems(2) less.prems(3) less.prems(4) less.prems(5)])
    have unfoldLast: "operB (Trm [DB w lb]) z = Dprin w (operB lb z)"
      by (rule operB_NatSet_principal_unfold[OF domLbNat lbne domLb])
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

text \<open>\<open>dfree_BT\<close> distributes over \<open>+\<^sub>B\<close> (append of two \<open>Trm\<close>s) and is
  preserved by \<open>*\<^sub>B\<close> (iterated \<open>+\<^sub>B\<close>).\<close>

lemma dfree_BT_addBT:
  "dfree_BT (a +\<^sub>B b) \<longleftrightarrow> dfree_BT a \<and> dfree_BT b"
  by (cases a; cases b) auto

lemma dfree_BT_multBT:
  assumes "dfree_BT a"
  shows "dfree_BT (multBT a k)"
  by (induction k) (simp_all add: zero_enat_def dfree_BT_addBT assms)

end
