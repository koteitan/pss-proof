theory Frontier_7_043
  imports Support_7_037
begin

text \<open>The inner term of \<open>transC2 M\<close> (its \<open>bpHeadT\<close>) is never \<open>0\<^sub>B\<close>: every branch
  of the \<open>transC2\<close> definition produces \<open>Dpt v X\<close> with \<open>X\<close> a nonempty principal
  list (it always ends in \<open>Dpt (entry M 1 j\<^sub>1) 0\<^sub>B\<close>).\<close>

lemma bpHeadT_transC2_nonzero: "bpHeadT (transC2 M) \<noteq> 0\<^sub>B"
proof -
  let ?j1 = "transJ1 M"  let ?jp = "transJ0 M"  let ?v = "transV M"
  let ?t2 = "transT2 M"
  let ?J1 = "Lng (PB ?t2) - 1"  let ?pj = "PB ?t2 ! ?J1"
  let ?ldj = "(bpHeadV ?pj = enat (entry M 1 ?jp))"
  let ?t3 = "(if ?ldj then SigmaB (take ?J1 (PB ?t2)) else ?t2)"
  let ?t4 = "(if ?ldj then bpHeadT ?pj else ?t2)"
  have "transC2 M =
        (if transCondI M \<or> transCondIII M \<or> transCondV M
         then Dpt ?v (?t2 +\<^sub>B Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)
         else if transCondVI M
         then Dpt ?v (Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)
         else if ?t2 = 0\<^sub>B
         then Dpt ?v (Dpt (enat (entry M 1 ?jp)) (Dpt (enat (entry M 1 ?j1)) 0\<^sub>B))
         else Dpt ?v (?t3 +\<^sub>B Dpt (enat (entry M 1 ?jp))
                            (?t4 +\<^sub>B Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)))"
    by (simp add: transC2_def Let_def transV_def transT2_def transJ1_def transJ0_def)
  hence bhT: "bpHeadT (transC2 M) =
        (if transCondI M \<or> transCondIII M \<or> transCondV M
         then ?t2 +\<^sub>B Dpt (enat (entry M 1 ?j1)) 0\<^sub>B
         else if transCondVI M
         then Dpt (enat (entry M 1 ?j1)) 0\<^sub>B
         else if ?t2 = 0\<^sub>B
         then Dpt (enat (entry M 1 ?jp)) (Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)
         else ?t3 +\<^sub>B Dpt (enat (entry M 1 ?jp))
                     (?t4 +\<^sub>B Dpt (enat (entry M 1 ?j1)) 0\<^sub>B))"
    by simp
  have nz1: "?t2 +\<^sub>B Dpt (enat (entry M 1 ?j1)) 0\<^sub>B \<noteq> 0\<^sub>B"
    by (cases ?t2) simp
  have nz3: "?t3 +\<^sub>B Dpt (enat (entry M 1 ?jp))
                  (?t4 +\<^sub>B Dpt (enat (entry M 1 ?j1)) 0\<^sub>B) \<noteq> 0\<^sub>B"
    by (cases ?t3) simp
  show ?thesis
  proof (cases "transCondI M \<or> transCondIII M \<or> transCondV M")
    case True thus ?thesis using bhT nz1 by simp
  next
    case f1: False
    show ?thesis
    proof (cases "transCondVI M")
      case True thus ?thesis using bhT f1 by simp
    next
      case f2: False
      show ?thesis
      proof (cases "?t2 = 0\<^sub>B")
        case True thus ?thesis using bhT f1 f2 by simp
      next
        case f3: False thus ?thesis using bhT f1 f2 nz3 by simp
      qed
    qed
  qed
qed

text \<open>For a reduced monotone \<open>M\<close> of length \<open>> 1\<close>, \<open>Trans M\<close> is a single principal
  term with NONZERO inner: \<open>Trans M = Dpt (entry M 1 0) t'\<close> with \<open>t' \<noteq> 0\<^sub>B\<close>.
  Mirrors @{thm [source] Trans_PT_single}: the \<open>t\<^sub>1 = 0\<close> branch gives
  \<open>D\<^bsub>0\<^esub>(D\<^bsub>M\<^bsub>1,j\<^sub>1\<^esub>\<^esub> 0)\<close> (inner \<open>D\<^bsub>M\<^bsub>1,j\<^sub>1\<^esub>\<^esub> 0 \<noteq> 0\<close>); the surgery branch gives
  \<open>transC2 M\<close>, whose inner is @{thm [source] bpHeadT_transC2_nonzero}.\<close>

lemma trans_monoT_inner_nonzero:
  assumes MR: "M \<in> RT_PS" and mono: "monoT M" and L: "1 < Lng M"
  shows "bpHeadT (Trans M) \<noteq> 0\<^sub>B"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
  have domT: "Trans_Mark_dom (Inl M)" by (rule m_7_3_Trans_welldef[OF MR])
  let ?j1 = "Lng M - 1"
  show ?thesis
  proof (cases "Trans (Pred M) = 0\<^sub>B")
    case t1z: True
    have "Trans M = Dpt 0 (Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)"
      using Trans.psimps[OF domT] MR Lgt1 mono t1z by (simp add: Let_def)
    thus ?thesis by simp
  next
    case t1ne: False
    have hp: "hasParent M 0 ?j1" by (rule monoT_hasParent0_last[OF MT mono L])
    let ?t1 = "Trans (Pred M)"  let ?bv = "entry M 1 ?j1"
    define jp where "jp = parent M 0 (Lng M - 1)"
    define c1 where "c1 = Mark (Pred M) (Adm M jp)"
    define vv where "vv = bpHeadV c1"
    define tt2 where "tt2 = bpHeadT c1"
    define JJ1 where "JJ1 = Lng (PB tt2) - 1"
    define pj where "pj = PB tt2 ! JJ1"
    define ldj where "ldj = (bpHeadV pj = enat (entry M 1 jp))"
    define tt3 where "tt3 = (if ldj then SigmaB (take JJ1 (PB tt2)) else tt2)"
    define tt4 where "tt4 = (if ldj then bpHeadT pj else tt2)"
    define c2 where "c2 = (if transCondI M \<or> transCondIII M \<or> transCondV M
                           then Dpt vv (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)
                           else if transCondVI M
                           then Dpt vv (Dpt (enat ?bv) 0\<^sub>B)
                           else if tt2 = 0\<^sub>B
                           then Dpt vv (Dpt (enat (entry M 1 jp)) (Dpt (enat ?bv) 0\<^sub>B))
                           else Dpt vv (tt3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                              (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)))"
    define sb1 where "sb1 = (SOME sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb))"
    have trans_val: "Trans M = unflatBT (fst sb1 @ flatBT c2 @ snd sb1)"
      using Trans.psimps[OF domT] MR Lgt1 mono t1ne
      unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
                tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
                ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
                c2_def[symmetric] sb1_def[symmetric]
      by simp
    have c2eqT: "c2 = transC2 M"
      unfolding c2_def transC2_def Let_def
        vv_def tt2_def c1_def transV_def transT2_def transC1_def transJm1_def
        JJ1_def pj_def ldj_def tt3_def tt4_def transJ1_def transJ0_def jp_def
      by simp
    \<comment> \<open>\<open>c2\<close> is single-principal \<open>Dpt vv X\<close> with \<open>X = bpHeadT c2 \<noteq> 0\<^sub>B\<close>; its flat is
       \<open>Dsym vv # flatBT X\<close> with \<open>length (flatBT X) \<ge> 2\<close>, so \<open>length (flatBT c2) \<ge> 3\<close>.\<close>
    have c2pc1: "Lng (PB c2) = 1" using transC2_single_principal c2eqT by simp
    obtain pc2 where c2p: "c2 = Trm [pc2]"
      using c2pc1 by (cases c2) (auto simp: PB_def length_Suc_conv)
    have Xne: "bpHeadT c2 \<noteq> 0\<^sub>B" using bpHeadT_transC2_nonzero c2eqT by simp
    have c2head: "c2 = Dpt (bpHeadV c2) (bpHeadT c2)"
      using principal_reconstruct[OF c2pc1] .
    have flen2: "2 \<le> length (flatBT (bpHeadT c2))"
      by (rule flatBT_len_ge2[OF Xne])
    have c2flat: "flatBT c2 = Dsym (bpHeadV c2) # flatBT (bpHeadT c2)"
      by (subst c2head) simp
    have c2len: "3 \<le> length (flatBT c2)" using c2flat flen2 by simp
    \<comment> \<open>the surgery output's flat contains \<open>flatBT c2\<close> as a contiguous block\<close>
    have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
    have mkdA: "(Pred M, Adm M jp) \<in> Marked"
      using Marked_Pred_Adm[OF MT L hp] jp_def by simp
    have mb1: "(?t1, c1) \<in> MarkedB"
      using m_7_3_Trans_Mark_MarkedB[OF predRT mkdA] c1_def by simp
    have t1neT: "?t1 \<noteq> Trm []" using t1ne by simp
    have exsb: "\<exists>sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb)"
      using mb1 unfolding MarkedB_def by auto
    have dsome: "scb_decomp ?t1 (fst sb1) (flatBT c1) (snd sb1)"
      unfolding sb1_def by (rule someI_ex[OF exsb])
    have iptc1: "isPTB_str (flatBT c1)"
      using dsome t1neT by (simp add: scb_decomp_def)
    then obtain pc where pcl: "flatBT c1 = flatBP pc" by (auto simp: isPTB_str_def)
    have c1p: "c1 = Trm [pc]" by (metis pcl flatBT.simps(2) m_7_flatBT_inj)
    have c1TB: "c1 \<in> T_B" using m_7_3_Mark_in_T_B[OF predRT mkdA] c1_def by simp
    obtain wv tb where pcw: "pc = DB wv tb" by (cases pc) auto
    have iptc2': "isPTB_str (flatBT (Trm [pc2]))"
    proof -
      have vne: "transV M \<noteq> \<infinity>"
      proof -
        have "transV M = bpHeadV c1" by (simp add: transV_def transC1_def transJm1_def
              transJ0_def transJ1_def jp_def c1_def)
        also have "\<dots> = wv" using c1p pcw by simp
        finally show ?thesis using c1TB c1p pcw by (auto simp: T_B_def)
      qed
      have t2df: "dfree_BT (transT2 M)"
      proof -
        have "transT2 M = bpHeadT c1" by (simp add: transT2_def transC1_def transJm1_def
              transJ0_def transJ1_def jp_def c1_def)
        also have "\<dots> = tb" using c1p pcw by simp
        finally show ?thesis using c1TB c1p pcw by (auto simp: T_B_def)
      qed
      have c2df: "dfree_BT c2" using dfree_transC2[OF vne t2df] c2eqT by simp
      show ?thesis using c2df c2p by (auto simp: isPTB_str_def)
    qed
    have dsb': "scb_decomp ?t1 (fst sb1) (flatBT (Trm [pc])) (snd sb1)"
      using dsome c1p by simp
    obtain t' where t'f: "flatBT t' = fst sb1 @ flatBT (Trm [pc2]) @ snd sb1"
        and t'd: "scb_decomp t' (fst sb1) (flatBT (Trm [pc2])) (snd sb1)"
      using scb_replace_principal[OF dsb' iptc2'] by blast
    have transMp: "Trans M = t'"
      using trans_val t'f c2p unflatBT_flat[of t'] by simp
    have flatTM: "flatBT (Trans M) = fst sb1 @ flatBT c2 @ snd sb1"
      using transMp t'f c2p by simp
    \<comment> \<open>so \<open>flatBT (Trans M)\<close> has length \<ge> 3; if its inner were \<open>0\<^sub>B\<close> then
       \<open>Trans M = Dpt v 0\<^sub>B\<close> would flatten to length 2 — contradiction.\<close>
    have TMlen: "3 \<le> length (flatBT (Trans M))" using flatTM c2len by simp
    show ?thesis
    proof
      assume z: "bpHeadT (Trans M) = 0\<^sub>B"
      have tne: "Trans M \<noteq> 0\<^sub>B"
      proof
        assume "Trans M = 0\<^sub>B"
        hence "flatBT (Trans M) = [Zsym]" by simp
        thus False using TMlen by simp
      qed
      obtain q where TMq: "Trans M = Trm [q]"
        using Trans_PT_single MR mono tne by blast
      obtain a b where qab: "q = DB a b" by (cases q)
      have "b = 0\<^sub>B" using z TMq qab by simp
      hence "Trans M = Dpt a 0\<^sub>B" using TMq qab by simp
      hence "flatBT (Trans M) = [Dsym a, Zsym]" by simp
      thus False using TMlen by simp
    qed
  qed
qed

text \<open>Clause (3): under \<open>(1,0) <\<^bsub>M\<^esub>\<^sup>Next (1,1)\<close>, the leftmost principal component of
  \<open>Trans M\<close> is \<open>Dpt (entry M 1 0) (Dpt u t)\<close> for some \<open>u, t\<close> — i.e. its left two
  characters are \<open>D\<^bsub>M\<^bsub>1,0\<^esub>\<^esub> D\<^bsub>u\<^esub>\<close>.  The first \<open>P\<close>-component \<open>P M ! 0\<close> contains both
  columns \<open>0\<close> and \<open>1\<close> (they are \<open>Next\<close>-linked), so \<open>Lng (P M ! 0) > 1\<close> and
  \<open>P M ! 0 \<noteq> ((0,0))\<close>; clause (2) gives the leftmost PC \<open>= Trans (P M ! 0)\<close>, and
  @{thm [source] trans_monoT_inner_nonzero} on the (monotone, single-component)
  \<open>P M ! 0\<close> gives the nonzero inner.\<close>

lemma trans_leftmost_pc_two_chars:
  assumes MR: "M \<in> RT_PS" and nx: "nextR M 1 0 1"
  shows "\<exists>t. PB (Trans M) ! 0 = Dpt (enat (entry M 1 0)) t \<and> t \<noteq> 0\<^sub>B"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have L: "1 < Lng M"
    using nx by (auto simp: nextR_def nextrel1_def split: if_splits)
  \<comment> \<open>From \<open>(1,0) <\<^bsub>M\<^esub>\<^sup>Next (1,1)\<close>: \<open>le0 M 0 1\<close>, hence \<open>entry M 0 0 < entry M 0 1\<close>.
     But if \<open>Lng (P M ! 0) = 1\<close> then column 1 is a fresh component start, a row-0
     running minimum, giving \<open>entry M 0 0 \<ge> entry M 0 1\<close> — contradiction.  So
     columns 0 and 1 lie in the same first \<open>P\<close>-component: \<open>Lng (P M ! 0) > 1\<close>.\<close>
  have le01: "le0 M 0 1"
    using nx by (auto simp: nextR_def nextrel1_def split: if_splits)
  have e0lt: "entry M 0 0 < entry M 0 1"
    by (rule m_5_1_ancestor_basic_1[OF MT, of 0 1 1])
       (use L le01 in \<open>auto simp: leR_def\<close>)
  have ne_PM: "P M \<noteq> []" by (rule P_nonempty)
  have lenP1: "0 < Lng (P M)" using ne_PM by (cases "P M") auto
  have P0len_pos: "0 < Lng (P M ! 0)"
    by (rule idxsum_P_component_nonempty[OF MT lenP1])
  have P0big: "Lng (P M ! 0) > 1"
  proof (rule ccontr)
    assume "\<not> Lng (P M ! 0) > 1"
    hence P0one: "Lng (P M ! 0) = 1" using P0len_pos by linarith
    have lenP2: "Lng (P M) > 1"
    proof (rule ccontr)
      assume "\<not> Lng (P M) > 1"
      hence l1: "Lng (P M) = 1" using lenP1 by linarith
      then obtain Q where PMQ: "P M = [Q]" by (cases "P M") auto
      have "concat (P M) = M" by (rule poper_concat_P)
      hence "Q = M" using PMQ by simp
      hence "P M ! 0 = M" using PMQ by simp
      thus False using P0one L by simp
    qed
    have isum1: "IdxSum (P M) ! 1 = 1"
    proof -
      have "IdxSum (P M) ! 1 = sum_list (map length (take 1 (P M)))"
        using lenP2 by (intro idxsum_nth) simp
      also have "\<dots> = length (P M ! 0)" using ne_PM by (cases "P M") auto
      also have "\<dots> = 1" using P0one by simp
      finally show ?thesis .
    qed
    have "\<forall>j < IdxSum (P M) ! 1. entry M 0 j \<ge> entry M 0 (IdxSum (P M) ! 1)"
      using idxsum_leftend_lmin[OF MT, of 1] lenP2 by simp
    hence "entry M 0 0 \<ge> entry M 0 1" using isum1 by simp
    thus False using e0lt by simp
  qed
  have P0ne: "P M ! 0 \<noteq> [(0,0)]"
    using P0big by (cases "P M ! 0") auto
  \<comment> \<open>\<open>P M ! 0\<close> is reduced, a single-\<open>P\<close>-component (zero or mono); with \<open>Lng > 1\<close>
     it is monotone.\<close>
  have P0in: "P M ! 0 \<in> set (P M)" using ne_PM by (cases "P M") auto
  have P0RT: "P M ! 0 \<in> RT_PS"
    using m_6_6_P_reduced[OF MT] MR P0in
    by (metis in_set_conv_nth)
  have P0mono: "monoT (P M ! 0)"
    using m_6_2_P_components_1[OF MT] P0in P0big by (auto simp: zeroT_def)
  \<comment> \<open>the first \<open>P\<close>-component shares \<open>M\<close>'s left ends (it is \<open>seg M 0 (IdxSum!1 - 1)\<close>)\<close>
  have Jle: "(0::nat) \<le> Lng (P M) - 1" using ne_PM by (cases "P M") simp_all
  have P0seg: "P M ! 0 = seg M (IdxSum (P M) ! 0) (IdxSum (P M) ! 1 - 1)"
    using m_6_4_P_IdxSum[OF MT Jle] by simp
  have idx0: "IdxSum (P M) ! 0 = 0" by (simp add: idxsum_nth)
  have lp: "0 < Lng (seg M (IdxSum (P M) ! 0) (IdxSum (P M) ! 1 - 1))"
    using P0len_pos P0seg by simp
  have e10eq: "entry (P M ! 0) 1 0 = entry M 1 0"
  proof -
    have "entry (P M ! 0) 1 0
         = entry (seg M (IdxSum (P M) ! 0) (IdxSum (P M) ! 1 - 1)) 1 0"
      using P0seg by simp
    also have "\<dots> = entry M 1 (IdxSum (P M) ! 0 + 0)" by (rule entry_seg[OF lp])
    finally show ?thesis by (simp add: idx0)
  qed
  \<comment> \<open>leftmost PC \<open>= Trans (P M ! 0)\<close> (clause (2)); a single principal with nonzero
     inner (@{thm [source] trans_monoT_inner_nonzero}).\<close>
  have lpcEq: "PB (Trans M) ! 0 = Trans (P M ! 0)"
    using m_7_3_Trans_leftmost_pc MR P0ne by blast
  have core0: "bpHeadV (Trans (P M ! 0)) = enat (entry (P M ! 0) 1 0)"
    using m_7_3_Trans_leftend P0RT by blast
  have tne: "Trans (P M ! 0) \<noteq> 0\<^sub>B"
  proof
    assume z: "Trans (P M ! 0) = 0\<^sub>B"
    have "zeroT (P M ! 0)" using m_7_3_Trans_zeroT[OF P0RT] z by simp
    thus False using P0big by (simp add: zeroT_def)
  qed
  obtain p where tp: "Trans (P M ! 0) = Trm [p]"
    using Trans_PT_single P0RT P0mono tne by blast
  obtain v t where pvt: "p = DB v t" by (cases p)
  have headv: "v = enat (entry M 1 0)"
    using core0 e10eq tp pvt by simp
  have innerne: "t \<noteq> 0\<^sub>B"
    using trans_monoT_inner_nonzero[OF P0RT P0mono P0big] tp pvt by simp
  have "PB (Trans M) ! 0 = Dpt (enat (entry M 1 0)) t \<and> t \<noteq> 0\<^sub>B"
    using lpcEq tp pvt headv innerne by simp
  thus ?thesis by blast
qed

text \<open>The full §7.3 proposition (1)(2)(3).  Clause (1) reduces to the left-end
  core (@{thm [source] m_7_3_Trans_leftend}) plus \<open>entry M 1 0 = entry M 1 1\<close> in
  the \<open>P(M)\<^sub>0 = ((0,0)) \<and> Lng(P(M)) > 1\<close> case; clause (2) is
  @{thm [source] m_7_3_Trans_leftmost_pc} plus the core for the head; clause (3)
  is the core for the first character plus single-principality (the second
  character exists because the leftmost PC has nonzero tail when \<open>(1,0) <\<^bsub>M\<^esub>\<^sup>Next
  (1,1)\<close>).\<close>

text \<open>Sub-fact for clause (1): when \<open>M\<^sub>0 = (0,0)\<close> (i.e. \<open>P(M)\<^sub>0 = ((0,0))\<close>) and
  \<open>M\<close> is reduced of length \<open>> 1\<close>, the leftmost column-1 entry is shared:
  \<open>entry M 1 0 = entry M 1 1 = 0\<close>.  \<open>entry M 1 0 = 0\<close> follows from
  @{thm [source] reduced_e10_zero}; and \<open>entry M 1 1 = 0\<close> by the same applied to
  the reduced prefix sharing the left two columns, OR directly: when \<open>P(M)\<^sub>0 =
  ((0,0))\<close>, \<open>(0,0)\<close> is a full \<open>P\<close>-component, forcing \<open>M\<^sub>1\<close> to start a fresh
  component with \<open>M\<^bsub>1,1\<^esub> = 0\<close>.\<close>

lemma reduced_P0_zero_e11:
  assumes MR: "M \<in> RT_PS" and P0z: "P M ! 0 = [(0, 0)]" and L: "1 < Lng M"
    and lenP1: "Lng (P M) > 1"
  shows "entry M 1 0 = 0 \<and> entry M 1 1 = 0"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  \<comment> \<open>\<open>P M ! 0 = [(0,0)]\<close> means the first \<open>P\<close>-component is the single column \<open>(0,0)\<close>;
     \<open>concat (P M) = M\<close> so \<open>M\<^sub>0 = (0,0)\<close> and \<open>M\<^sub>1\<close> starts the next component.\<close>
  have concatP: "concat (P M) = M" by (rule poper_concat_P)
  have PMne: "P M \<noteq> []" by (rule P_nonempty)
  obtain rest where PMdec: "P M = [(0,0)] # rest"
    using P0z PMne by (cases "P M") auto
  have Mform: "M = (0,0) # concat rest"
    using concatP PMdec by simp
  have e00: "entry M 0 0 = 0" using Mform by (simp add: entry_def)
  have e10: "entry M 1 0 = 0"
    using reduced_e10_zero MR e00 by blast
  \<comment> \<open>The first \<open>P\<close>-component \<open>[(0,0)]\<close> has length 1, so the second IdxSum position is
     \<open>IdxSum (P M) ! 1 = 1\<close>.  Trunk left-minimality there gives
     \<open>entry M 0 0 \<ge> entry M 0 1\<close>, hence \<open>entry M 0 1 = 0\<close> and (no row-0 parent of 1) +
     RedCondB give \<open>entry M 1 1 = entry M 0 1 = 0\<close>.\<close>
  have isum1: "IdxSum (P M) ! 1 = 1"
  proof -
    have "IdxSum (P M) ! 1 = sum_list (map length (take 1 (P M)))"
      using lenP1 by (intro idxsum_nth) simp
    also have "\<dots> = length (P M ! 0)" using PMne by (cases "P M") auto
    also have "\<dots> = 1" using P0z by simp
    finally show ?thesis .
  qed
  have lmin: "\<forall>j < 1. entry M 0 j \<ge> entry M 0 1"
  proof -
    have "\<forall>j < IdxSum (P M) ! 1. entry M 0 j \<ge> entry M 0 (IdxSum (P M) ! 1)"
      using idxsum_leftend_lmin[OF MT, of 1] lenP1 by simp
    thus ?thesis using isum1 by simp
  qed
  have e01: "entry M 0 1 = 0"
    using lmin e00 by auto
  have nohp: "\<not> hasParent M 0 1"
  proof -
    have "1 < Lng M" using L .
    hence "(\<not> (\<exists>!j0. nextR M 0 j0 1)) \<longleftrightarrow> (\<forall>j<1. entry M 0 j \<ge> entry M 0 1)"
      using idxsum_no_parent0_iff[OF MT] by simp
    thus ?thesis using lmin by (simp add: hasParent_def)
  qed
  have condB: "RedCondB M"
    using m_6_6_reduced_iff_cond[OF MT] MR by auto
  have e11: "entry M 1 1 = 0"
  proof -
    have "1 \<le> Lng M - 1" using L by simp
    hence "entry M 0 1 = entry M 1 1"
      using condB[unfolded RedCondB_def, rule_format, of 1] nohp by simp
    thus ?thesis using e01 by simp
  qed
  show ?thesis using e10 e11 by simp
qed

end
