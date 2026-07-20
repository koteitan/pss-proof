theory Frontier_7_027
  imports P_7_4_RightNodes_Mark
begin

section \<open>§7.4 命題（\<open>RightNodes\<close> と \<open>RightAnces\<close> の一致） — m_7_4_RightAnces_RightNodes\<close>

text \<open>Step 1: domain totality of \<open>RightAnces\<close> on \<open>RT\<^bsub>PS\<^esub>\<close>, by strong \<open>Lng\<close>
  induction, mirroring @{thm [source] Trans_Mark_dom_RT_PS_aux}.  The recursive
  calls are: \<open>Red M\<close> (guarded \<open>M \<notin> RT_PS\<close>, vacuous here), \<open>seg M 0 jm1\<close>
  (\<open>jm1 = Adm M (parent M 0 (Lng M-1)) < Lng M - 1\<close>), and \<open>PJ = P M ! (Lng (P M)-1)
  = drop (Pcut M) M\<close> on the multi branch.\<close>

lemma RightAnces_dom_RT:
  "M \<in> RT_PS \<longrightarrow> RightAnces_dom M"
proof (induction M rule: measure_induct_rule[where f=Lng])
  case (less M)
  show ?case
  proof (rule impI)
    assume MR: "M \<in> RT_PS"
    have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
    have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
    \<comment> \<open>seg discharger: the \<open>seg M 0 jm1\<close> call has smaller \<open>Lng\<close> and stays reduced\<close>
    have segD: "\<not> Lng M - Suc 0 = 0 \<Longrightarrow> monoT M
        \<Longrightarrow> RightAnces_dom (seg M 0 (Adm M (parent M 0 (Lng M - Suc 0))))"
    proof -
      assume j1: "\<not> Lng M - Suc 0 = 0" and mono: "monoT M"
      have L: "1 < Lng M" using j1 by linarith
      let ?j1 = "Lng M - Suc 0"
      have j1eq: "Lng M - Suc 0 = Lng M - 1" by simp
      have hp: "hasParent M 0 (Lng M - 1)"
        by (rule monoT_hasParent0_last[OF MT mono L])
      have parR: "nextR M 0 (parent M 0 ?j1) ?j1"
        using hp unfolding j1eq hasParent_def parent_def by (rule theI')
      have jplt: "parent M 0 ?j1 < ?j1"
        using parR by (simp add: nextR_def nextrel0_def)
      have aLe: "Adm M (parent M 0 ?j1) \<le> parent M 0 ?j1" by (rule adm_Adm_le)
      have alt: "Adm M (parent M 0 ?j1) < ?j1" using aLe jplt by linarith
      have ale1: "Adm M (parent M 0 ?j1) \<le> Lng M - 1" using alt by simp
      have segRT: "seg M 0 (Adm M (parent M 0 ?j1)) \<in> RT_PS"
        by (rule seg_0_RT_PS[OF MR ale1])
      have segtake: "seg M 0 (Adm M (parent M 0 ?j1))
                     = take (Suc (Adm M (parent M 0 ?j1))) M"
        by (rule seg_0_eq_take) (use alt L in linarith)
      have "Suc (Adm M (parent M 0 ?j1)) < Lng M" using alt L by linarith
      hence "Lng (seg M 0 (Adm M (parent M 0 ?j1))) < Lng M"
        using segtake by (simp add: min_def)
      thus "RightAnces_dom (seg M 0 (Adm M (parent M 0 ?j1)))"
        using less.IH segRT by blast
    qed
    \<comment> \<open>multi discharger: the \<open>PJ\<close> call (= last \<open>P\<close>-component = \<open>drop (Pcut M) M\<close>)\<close>
    have multiD: "\<not> Lng M - Suc 0 = 0 \<Longrightarrow> \<not> monoT M
        \<Longrightarrow> RightAnces_dom (P M ! (Lng (P M) - 1))"
    proof -
      assume j1: "\<not> Lng M - Suc 0 = 0" and nm: "\<not> monoT M"
      have L: "1 < Lng M" using j1 by linarith
      have mu: "multiT M"
      proof -
        have "\<not> zeroT M" using L by (simp add: zeroT_def)
        thus ?thesis using nm by (simp add: multiT_def)
      qed
      have nth_last: "P M ! (Lng (P M) - 1) = drop (Pcut M) M"
        by (rule trans_multiT_last_component(1)[OF MT mu])
      have J1lt: "Lng (P M) - 1 < Lng (P M)"
        using P_nonempty[of M] by (cases "P M") auto
      have PJRT: "P M ! (Lng (P M) - 1) \<in> RT_PS"
        using m_6_6_P_reduced[OF MT] MR J1lt by blast
      have cut: "0 < Pcut M \<and> Pcut M \<le> Lng M - 1" using Pcut_le[OF L] by simp
      have lpj: "Lng (P M ! (Lng (P M) - 1)) = Lng M - Pcut M"
        using nth_last by simp
      have "Lng (P M ! (Lng (P M) - 1)) < Lng M"
        using lpj cut L by linarith
      thus "RightAnces_dom (P M ! (Lng (P M) - 1))"
        using less.IH PJRT by blast
    qed
    have segD2: "\<not> Lng M \<le> Suc 0 \<Longrightarrow> monoT M
        \<Longrightarrow> RightAnces_dom (seg M 0 (Adm M (parent M 0 (Lng M - Suc 0))))"
    proof -
      assume L: "\<not> Lng M \<le> Suc 0" and mono: "monoT M"
      have "Lng M - Suc 0 \<noteq> 0" using L by linarith
      thus "RightAnces_dom (seg M 0 (Adm M (parent M 0 (Lng M - Suc 0))))"
        using segD mono by blast
    qed
    have multiD2: "\<not> Lng M \<le> Suc 0 \<Longrightarrow> \<not> monoT M \<Longrightarrow> multiT M
        \<Longrightarrow> RightAnces_dom (drop (Pcut M) M)"
    proof -
      assume L: "\<not> Lng M \<le> Suc 0" and nm: "\<not> monoT M" and mu: "multiT M"
      have j1: "Lng M - Suc 0 \<noteq> 0" using L by linarith
      have pjeq: "P M ! (Lng (P M) - 1) = drop (Pcut M) M"
        by (rule trans_multiT_last_component(1)[OF MT mu])
      have "RightAnces_dom (P M ! (Lng (P M) - 1))" using multiD nm j1 by blast
      thus "RightAnces_dom (drop (Pcut M) M)" using pjeq by simp
    qed
    have vacD: "\<not> Lng M \<le> Suc 0 \<Longrightarrow> \<not> monoT M \<Longrightarrow> \<not> multiT M \<Longrightarrow> RightAnces_dom M"
    proof -
      assume L: "\<not> Lng M \<le> Suc 0" and nm: "\<not> monoT M" and nmu: "\<not> multiT M"
      have "zeroT M" using nm nmu by (simp add: multiT_def)
      hence "Lng M = 1" by (simp add: zeroT_def)
      thus "RightAnces_dom M" using L by simp
    qed
    show "RightAnces_dom M"
      apply (rule RightAnces.domintros)
      subgoal using MR by simp
      subgoal using segD2 by blast
      subgoal premises prems
      proof -
        have j1: "Lng M - Suc 0 \<noteq> 0" using prems(2) by linarith
        have D: "RightAnces_dom (P M ! (Lng (P M) - 1))"
          by (rule multiD[OF j1 prems(3)])
        show ?thesis using D by simp
      qed
      done
  qed
qed

text \<open>Helper: at the leftmost basepoint \<open>m = 0\<close>, \<open>Mark M 0\<close> coincides with
  \<open>Trans M\<close>.  Strong \<open>Lng\<close>-induction mirroring the \<open>Trans\<close>/\<open>Mark\<close> recursion:
  base \<open>Lng M = 1\<close> identical; \<open>monoT\<close>/\<open>t\<^sub>1 = 0\<close> identical (\<open>m = 0\<close> branch of
  \<open>Mark\<close>); \<open>monoT\<close>/\<open>t\<^sub>1 \<noteq> 0\<close> uses the IH \<open>Mark (Pred M) 0 = Trans (Pred M) = t\<^sub>1\<close>
  so the surgery's replaced component \<open>c\<^sub>0 = Mark (Pred M) 0\<close> equals \<open>t\<^sub>1\<close> and the
  surgery reproduces the \<open>Trans\<close> value at the SAME scb-position \<open>sb\<^sub>1\<close>; the multi
  case is excluded because \<open>(M, 0) \<in> Marked\<close> forces \<open>monoT M\<close> (column \<open>0\<close> would
  not be \<open>\<le>\<^bsub>R\<^esub>\<close> the last column of a multi term).\<close>

lemma ra_Mark0_eq_Trans:
  "(M, 0) \<in> Marked \<longrightarrow> M \<in> RT_PS \<longrightarrow> Mark M 0 = Trans M"
proof (induction M rule: measure_induct_rule[where f=Lng])
  case (less M)
  show ?case
  proof (intro impI)
    assume m0M: "(M, 0) \<in> Marked" and MR: "M \<in> RT_PS"
    have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
    have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
    have domT: "Trans_Mark_dom (Inl M)" by (rule m_7_3_Trans_welldef[OF MR])
    have domK: "\<And>m. Trans_Mark_dom (Inr (M, m))" by (rule m_7_3_Mark_welldef[OF MR])
    show "Mark M 0 = Trans M"
    proof (cases "Lng M = 1")
      case True
      have c1: "(M \<notin> RT_PS) = False" using MR by simp
      have c2: "(Lng M - 1 = 0) = True" using True by simp
      have mk: "Mark M 0 = (if (M::pairseq) ! 0 = (0,0) then 0\<^sub>B
                            else Dpt (enat (entry M 1 0)) 0\<^sub>B)"
        by (subst Mark.psimps[OF domK]) (simp only: c1 c2 if_False if_True Let_def)
      have tr: "Trans M = (if (M::pairseq) ! 0 = (0,0) then 0\<^sub>B
                           else Dpt (enat (entry M 1 0)) 0\<^sub>B)"
        by (subst Trans.psimps[OF domT]) (simp only: c1 c2 if_False if_True Let_def)
      show ?thesis using mk tr by simp
    next
      case notone: False
      have L: "1 < Lng M" using Mne notone by (cases M) auto
      have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
      \<comment> \<open>\<open>(M,0) \<in> Marked\<close> forces \<open>monoT M\<close>\<close>
      have mono: "monoT M"
      proof (rule ccontr)
        assume nm: "\<not> monoT M"
        have nz: "\<not> zeroT M" using L by (simp add: zeroT_def)
        have mu: "multiT M" using nm nz by (simp add: multiT_def)
        have "Pcut M \<le> 0" using multi_Marked_last_component(1)[OF MT mu m0M] .
        moreover have "0 < Pcut M" using Pcut_le[OF L] by simp
        ultimately show False by simp
      qed
      have hp: "hasParent M 0 (Lng M - 1)" by (rule monoT_hasParent0_last[OF MT mono L])
      have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
      have predb: "Pred M = butlast M" using L by (simp add: Pred_def)
      have LPlt: "Lng (Pred M) < Lng M" using predb L by simp
      \<comment> \<open>\<open>(Pred M, 0) \<in> Marked\<close> (column \<open>0\<close> survives \<open>Pred\<close>)\<close>
      have m0P: "(Pred M, 0) \<in> Marked"
        by (rule Marked_Pred[OF MT L m0M]) (use L in linarith)
      let ?j1 = "Lng M - 1"
      let ?bv = "entry M 1 (Lng M - 1)"
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
      show ?thesis
      proof (cases "Trans (Pred M) = 0\<^sub>B")
        case t1z: True
        have mk: "Mark M 0 = Dpt 0 (Dpt (enat ?bv) 0\<^sub>B)"
          using Mark.psimps[OF domK] MR Lgt1 mono t1z
          by (simp add: Let_def)
        have tr: "Trans M = Dpt 0 (Dpt (enat ?bv) 0\<^sub>B)"
          using Trans.psimps[OF domT] MR Lgt1 mono t1z
          by (simp add: Let_def)
        show ?thesis using mk tr by simp
      next
        case t1ne: False
        \<comment> \<open>\<open>Trans M\<close> at the scb-position \<open>sb\<^sub>1\<close> of \<open>c\<^sub>1\<close> in \<open>t\<^sub>1\<close>\<close>
        let ?t1 = "Trans (Pred M)"
        define sb1 where "sb1 = (SOME sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb))"
        have trans_val: "Trans M = unflatBT (fst sb1 @ flatBT c2 @ snd sb1)"
          using Trans.psimps[OF domT] MR Lgt1 mono t1ne
          unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
                    tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
                    ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
                    c2_def[symmetric] sb1_def[symmetric]
          by simp
        \<comment> \<open>IH: \<open>Mark (Pred M) 0 = Trans (Pred M) = t\<^sub>1\<close>\<close>
        have markPred0: "Mark (Pred M) 0 = ?t1"
          using less.IH[OF LPlt] m0P predRT by simp
        \<comment> \<open>\<open>(t\<^sub>1, c\<^sub>1) \<in> MarkedB\<close> so the SOME decomposition exists\<close>
        have mkdA: "(Pred M, Adm M jp) \<in> Marked"
          using Marked_Pred_Adm[OF MT L hp] jp_def by simp
        have mb1: "(?t1, c1) \<in> MarkedB"
          using Trans_Mark_invariant_aux[of "Pred M"] predRT mkdA
          unfolding c1_def by blast
        \<comment> \<open>evaluate \<open>Mark M 0\<close> (surgery branch, \<open>0 < j\<^sub>1\<close>)\<close>
        have mlt: "(0::nat) < Lng M - 1" using L by linarith
        have mark_val_raw: "Mark M 0 = (if (Mark (Pred M) 0, c1) \<in> MarkedB
              then unflatBT
                     (fst (SOME sb. scb_decomp (Mark (Pred M) 0) (fst sb)
                                      (flatBT c1) (snd sb))
                      @ flatBT c2
                      @ snd (SOME sb. scb_decomp (Mark (Pred M) 0) (fst sb)
                                        (flatBT c1) (snd sb)))
              else Dpt (enat ?bv) 0\<^sub>B)"
          using Mark.psimps[OF domK] MR Lgt1 mono t1ne mlt
          unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
                    tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
                    ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
                    c2_def[symmetric]
          by simp
        have mb0: "(Mark (Pred M) 0, c1) \<in> MarkedB" using markPred0 mb1 by simp
        have someEq: "(SOME sb. scb_decomp (Mark (Pred M) 0) (fst sb)
                                  (flatBT c1) (snd sb))
                    = (SOME sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb))"
          using markPred0 by simp
        have mark_val: "Mark M 0 = unflatBT (fst sb1 @ flatBT c2 @ snd sb1)"
          using mark_val_raw mb0 someEq by (simp add: sb1_def)
        show ?thesis using mark_val trans_val by simp
      qed
    qed
  qed
qed


text \<open>Helper: \<open>RightNodes\<close> ignores the left summand of \<open>+\<^sub>B\<close> when the right
  summand is a non-zero term (\<open>RightNodes\<close> depends only on the last principal
  component, and \<open>a +\<^sub>B b = Trm (untrm a @ untrm b)\<close> has the same last
  component as \<open>b\<close>).\<close>

lemma ra_RightNodes_addBT_right:
  assumes "b \<noteq> 0\<^sub>B"
  shows "RightNodes (a +\<^sub>B b) = RightNodes b"
proof -
  obtain as where a: "a = Trm as" by (cases a)
  obtain bs where b: "b = Trm bs" by (cases b)
  have bne: "bs \<noteq> []" using assms b by auto
  have add: "a +\<^sub>B b = Trm (as @ bs)" using a b by simp
  have nemp: "as @ bs \<noteq> []" using bne by simp
  have lasteq: "last (as @ bs) = last bs" using bne by simp
  have "RightNodes (Trm (as @ bs)) = RightNodes (Trm [last (as @ bs)])"
    by (rule rnsub_RightNodes_last[OF nemp])
  also have "\<dots> = RightNodes (Trm [last bs])" using lasteq by simp
  also have "\<dots> = RightNodes (Trm bs)"
    by (rule rnsub_RightNodes_last[OF bne, symmetric])
  finally show ?thesis using add b by simp
qed

text \<open>Helper: the tail of \<open>RightNodes (transC2 M)\<close> for a mono, \<open>t\<^sub>1 \<noteq> 0\<close>,
  \<open>j\<^sub>1 > 0\<close> sequence.  Mirrors the four \<open>c\<^sub>2\<close>-branches of @{thm [source]
  transC2_def}; in every branch the last principal component is
  \<open>D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>1\<^esub> 0\<close> (conds I/III/V/VI) or \<open>D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>0\<^esub>(\<dots> D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>1\<^esub> 0)\<close>
  (conds II/IV), so \<open>RightNodes\<close> reduces to the RightAnces tail.\<close>

lemma ra_RightNodes_transC2_tail:
  "RightNodes (transC2 M) = the_enat (transV M) #
     (if transCondI M \<or> transCondIII M \<or> transCondV M \<or> transCondVI M
      then [entry M 1 (transJ1 M)]
      else [entry M 1 (transJ0 M), entry M 1 (transJ1 M)])"
proof -
  let ?j1 = "transJ1 M"
  let ?jp = "transJ0 M"
  let ?v = "transV M"
  let ?t2 = "transT2 M"
  let ?Dj1 = "Dpt (enat (entry M 1 ?j1)) 0\<^sub>B"
  define J1 where "J1 = Lng (PB ?t2) - 1"
  define pj where "pj = PB ?t2 ! J1"
  define leftDj0 where "leftDj0 = (bpHeadV pj = enat (entry M 1 ?jp))"
  define t3 where "t3 = (if leftDj0 then SigmaB (take J1 (PB ?t2)) else ?t2)"
  define t4 where "t4 = (if leftDj0 then bpHeadT pj else ?t2)"
  have nzDj1: "?Dj1 \<noteq> 0\<^sub>B" by simp
  show ?thesis
  proof (cases "transCondI M \<or> transCondIII M \<or> transCondV M")
    case I135: True
    have c2: "transC2 M = Dpt ?v (?t2 +\<^sub>B ?Dj1)"
      using I135
      by (simp add: transC2_def Let_def transV_def transT2_def transJ1_def)
    have "RightNodes (?t2 +\<^sub>B ?Dj1) = RightNodes ?Dj1"
      by (rule ra_RightNodes_addBT_right[OF nzDj1])
    hence rn: "RightNodes (?t2 +\<^sub>B ?Dj1) = [entry M 1 ?j1]" by simp
    have cond4: "transCondI M \<or> transCondIII M \<or> transCondV M \<or> transCondVI M"
      using I135 by blast
    show ?thesis using c2 rn cond4 by simp
  next
    case notI135: False
    show ?thesis
    proof (cases "transCondVI M")
      case VI: True
      have c2: "transC2 M = Dpt ?v ?Dj1"
        using notI135 VI
        by (simp add: transC2_def Let_def transV_def transJ1_def)
      have cond4: "transCondI M \<or> transCondIII M \<or> transCondV M \<or> transCondVI M"
        using VI by blast
      show ?thesis using c2 cond4 by simp
    next
      case notVI: False
      show ?thesis
      proof (cases "?t2 = 0\<^sub>B")
        case t2z: True
        have c2: "transC2 M = Dpt ?v (Dpt (enat (entry M 1 ?jp)) ?Dj1)"
          using notI135 notVI t2z
          by (simp add: transC2_def Let_def transV_def transT2_def transJ1_def
                        transJ0_def)
        have notany: "\<not> (transCondI M \<or> transCondIII M \<or> transCondV M \<or> transCondVI M)"
          using notI135 notVI by simp
        show ?thesis using c2 notany by simp
      next
        case t2nz: False
        have c2: "transC2 M
                = Dpt ?v (t3 +\<^sub>B Dpt (enat (entry M 1 ?jp)) (t4 +\<^sub>B ?Dj1))"
          using notI135 notVI t2nz
          by (simp add: transC2_def Let_def transV_def transT2_def transJ1_def
                        transJ0_def J1_def pj_def leftDj0_def t3_def t4_def)
        have nzInner: "Dpt (enat (entry M 1 ?jp)) (t4 +\<^sub>B ?Dj1) \<noteq> 0\<^sub>B" by simp
        have rnInner: "RightNodes (Dpt (enat (entry M 1 ?jp)) (t4 +\<^sub>B ?Dj1))
                     = entry M 1 ?jp # RightNodes (t4 +\<^sub>B ?Dj1)" by simp
        have rnt4: "RightNodes (t4 +\<^sub>B ?Dj1) = [entry M 1 ?j1]"
          using ra_RightNodes_addBT_right[OF nzDj1] by simp
        have "RightNodes (t3 +\<^sub>B Dpt (enat (entry M 1 ?jp)) (t4 +\<^sub>B ?Dj1))
            = RightNodes (Dpt (enat (entry M 1 ?jp)) (t4 +\<^sub>B ?Dj1))"
          by (rule ra_RightNodes_addBT_right[OF nzInner])
        also have "\<dots> = [entry M 1 ?jp, entry M 1 ?j1]"
          using rnInner rnt4 by simp
        finally have rnRest: "RightNodes (t3 +\<^sub>B Dpt (enat (entry M 1 ?jp)) (t4 +\<^sub>B ?Dj1))
            = [entry M 1 ?jp, entry M 1 ?j1]" .
        have notany: "\<not> (transCondI M \<or> transCondIII M \<or> transCondV M \<or> transCondVI M)"
          using notI135 notVI by simp
        show ?thesis using c2 rnRest notany by simp
      qed
    qed
  qed
qed


text \<open>§7.4 命題（\<open>RightNodes\<close> と \<open>RightAnces\<close> の一致）/ \<open>p_7_4_RightAnces_RightNodes\<close>
  (content.md 2745).  First the \<open>RT\<^bsub>PS\<^esub>\<close>-restricted version by strong
  \<open>Lng\<close>-induction (mirroring the \<open>RightAnces\<close>/\<open>Trans\<close> recursion), then lift to
  \<open>T\<^bsub>PS\<^esub>\<close> via \<open>Red\<close> (both \<open>RightAnces\<close> and \<open>Trans\<close> factor through \<open>Red\<close>).\<close>

lemma ra_RightAnces_RightNodes_RT:
  "M \<in> RT_PS \<longrightarrow> RightAnces M = RightNodes (Trans M)"
proof (induction M rule: measure_induct_rule[where f=Lng])
  case (less M)
  show ?case
  proof (rule impI)
    assume MR: "M \<in> RT_PS"
    have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
    have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
    have domT: "Trans_Mark_dom (Inl M)" by (rule m_7_3_Trans_welldef[OF MR])
    have raM: "RightAnces M =
        (let j1 = Lng M - 1 in
          if j1 = 0 then (if (M::pairseq) ! 0 = (0,0) then [] else [entry M 1 0])
          else if monoT M then
            (if zeroT (Pred M) then [0, entry M 1 j1]
             else let jp = parent M 0 j1;  jm1 = Adm M jp;
                      a = (if zeroT (seg M 0 jm1) then [0] else RightAnces (seg M 0 jm1)) in
                  if transCondI M \<or> transCondIII M \<or> transCondV M \<or> transCondVI M
                  then a @ [entry M 1 j1]
                  else a @ [entry M 1 jp, entry M 1 j1])
          else
            (let J1 = Lng (P M) - 1;  PJ = P M ! J1 in
             if PJ = [(0,0)] then [0] else RightAnces PJ))"
      by (subst RightAnces.psimps[OF RightAnces_dom_RT[rule_format, OF MR]])
         (simp only: if_not_P[OF iffD2[OF not_not refl]] MR Let_def, simp add: MR)
    show "RightAnces M = RightNodes (Trans M)"
    proof (cases "Lng M = 1")
      case True
      \<comment> \<open>base: \<open>j\<^sub>1 = 0\<close>\<close>
      have j1z: "Lng M - 1 = 0" using True by simp
      have ra: "RightAnces M = (if (M::pairseq) ! 0 = (0,0) then [] else [entry M 1 0])"
        using raM j1z by (simp add: Let_def)
      have tr: "Trans M = (if (M::pairseq) ! 0 = (0,0) then 0\<^sub>B else Dpt (enat (entry M 1 0)) 0\<^sub>B)"
        using Trans.psimps[OF domT] MR j1z by (simp add: Let_def)
      show ?thesis
      proof (cases "(M::pairseq) ! 0 = (0,0)")
        case True
        have "RightNodes (Trans M) = RightNodes (0\<^sub>B::BT)" using tr True by simp
        thus ?thesis using ra True by simp
      next
        case False
        have "RightNodes (Trans M) = RightNodes (Dpt (enat (entry M 1 0)) 0\<^sub>B)"
          using tr False by simp
        also have "\<dots> = [entry M 1 0]" by simp
        finally show ?thesis using ra False by simp
      qed
    next
      case notone: False
      have L: "1 < Lng M" using Mne notone by (cases M) auto
      have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
      have j1ne: "Lng M - 1 \<noteq> 0" using L by simp
      let ?j1 = "Lng M - 1"
      show ?thesis
      proof (cases "monoT M")
        case mono: True
        have MP: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
        have hp: "hasParent M 0 ?j1" by (rule monoT_hasParent0_last[OF MT mono L])
        have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
        show ?thesis
        proof (cases "zeroT (Pred M)")
          case predz: True
          \<comment> \<open>\<open>t\<^sub>1 = Trans (Pred M) = 0\<close>; both sides \<open>[0, M\<^bsub>1,j\<^sub>1\<^esub>]\<close>\<close>
          have ra: "RightAnces M = [0, entry M 1 ?j1]"
            using raM j1ne mono predz by (simp add: Let_def)
          have t1z: "Trans (Pred M) = 0\<^sub>B"
            using m_7_3_Trans_zeroT[OF predRT] predz by simp
          have tr: "Trans M = Dpt 0 (Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)"
            using Trans.psimps[OF domT] MR Lgt1 mono t1z by (simp add: Let_def)
          have "RightNodes (Trans M) = the_enat (0::enat) # [entry M 1 ?j1]"
            using tr by simp
          also have "\<dots> = [0, entry M 1 ?j1]" by (simp add: zero_enat_def)
          finally show ?thesis using ra by simp
        next
          case prednz: False
          \<comment> \<open>the main mono branch: \<open>t\<^sub>1 \<noteq> 0\<close>\<close>
          have t1ne: "Trans (Pred M) \<noteq> 0\<^sub>B"
            using m_7_3_Trans_zeroT[OF predRT] prednz by blast
          define jp where "jp = parent M 0 ?j1"
          define jm1 where "jm1 = Adm M jp"
          have transJ1eq: "transJ1 M = ?j1" by (simp add: transJ1_def)
          have transJ0eq: "transJ0 M = jp" by (simp add: transJ0_def transJ1_def jp_def)
          have transJm1eq: "transJm1 M = jm1"
            by (simp add: transJm1_def transJ0eq jm1_def)
          have J1pos: "transJ1 M > 0" using L by (simp add: transJ1_def)
          have T1ne: "transT1 M \<noteq> 0\<^sub>B" using t1ne by (simp add: transT1_def)
          \<comment> \<open>\<open>Mark M jm1 = c\<^sub>2\<close>, \<open>RightNodes c\<^sub>2 = transV # tail\<close>\<close>
          have markc2: "Mark M jm1 = transC2 M"
            using m_7_3_Mark_rightmost2[OF MR MP J1pos T1ne] transJm1eq by simp
          define tail where
            "tail = (if transCondI M \<or> transCondIII M \<or> transCondV M \<or> transCondVI M
                     then [entry M 1 ?j1] else [entry M 1 jp, entry M 1 ?j1])"
          have rnc2: "RightNodes (transC2 M) = the_enat (transV M) # tail"
            using ra_RightNodes_transC2_tail[of M] transJ1eq transJ0eq tail_def by simp
          \<comment> \<open>the RightAnces value (mono, \<open>\<not> zeroT (Pred M)\<close> branch)\<close>
          have raMono: "RightAnces M =
              (if zeroT (seg M 0 jm1) then [0] else RightAnces (seg M 0 jm1)) @ tail"
            using raM j1ne mono prednz
            by (simp add: Let_def jp_def jm1_def tail_def)
          \<comment> \<open>positions: \<open>jm1 \<le> jp < j\<^sub>1\<close>\<close>
          have parR: "nextR M 0 jp ?j1"
            using hp unfolding hasParent_def parent_def jp_def by (rule theI')
          have jplt: "jp < ?j1" using parR by (simp add: nextR_def nextrel0_def)
          have jm1le: "jm1 \<le> jp" using adm_Adm_le jm1_def by simp
          have jm1lt: "jm1 < ?j1" using jm1le jplt by linarith
          have jm1lej1: "jm1 \<le> ?j1" using jm1lt by linarith
          have segRT: "seg M 0 jm1 \<in> RT_PS"
            by (rule seg_0_RT_PS[OF MR jm1lej1])
          have segtake: "seg M 0 jm1 = take (Suc jm1) M"
            by (rule seg_0_eq_take) (use jm1lt L in linarith)
          have segLng: "Lng (seg M 0 jm1) = Suc jm1" using jm1lt L by simp
          have segLnglt: "Lng (seg M 0 jm1) < Lng M" using segLng jm1lt L by linarith
          \<comment> \<open>\<open>entry (seg M 0 jm1) 1 jm1 = entry M 1 jm1\<close>\<close>
          have entseg: "entry (seg M 0 jm1) 1 jm1 = entry M 1 jm1"
            using entry_seg[of jm1 M 0 jm1 1] segLng by simp
          show ?thesis
          proof (cases "zeroT (seg M 0 jm1)")
            case segz: True
            \<comment> \<open>\<open>jm1 = 0\<close>, \<open>entry M 1 0 = 0\<close>, \<open>Trans M = Mark M 0 = c\<^sub>2\<close>\<close>
            have jm1z: "jm1 = 0"
            proof -
              have "Lng (seg M 0 jm1) = 1" using segz by (simp add: zeroT_def)
              thus ?thesis using segLng by simp
            qed
            have e10z: "entry M 1 0 = 0"
            proof -
              have a: "entry (seg M 0 0) 1 0 = 0" using segz jm1z by (simp add: zeroT_def)
              have b: "entry (seg M 0 0) 1 0 = entry M 1 0"
                using entseg jm1z by simp
              show ?thesis using a b by simp
            qed
            \<comment> \<open>\<open>(M, 0) \<in> Marked\<close>, hence \<open>Mark M 0 = Trans M\<close>\<close>
            have leM0: "leR M 0 0 ?j1" using mono by (simp add: monoT_def)
            have adm0: "adm M 0" by (simp add: adm_def nadm_def nextR_def nextrel1_def)
            have m0M: "(M, 0) \<in> Marked"
              using MT leM0 adm0 by (simp add: Marked_def)
            have markTrans: "Mark M 0 = Trans M"
              using ra_Mark0_eq_Trans m0M MR by blast
            have transM_c2: "Trans M = transC2 M"
              using markTrans markc2 jm1z by simp
            \<comment> \<open>\<open>the_enat (transV M) = 0\<close> (left index of \<open>Mark M 0\<close>)\<close>
            have vz: "the_enat (transV M) = 0"
            proof -
              have c1eq: "transC1 M = Mark (Pred M) 0"
                using transJm1eq jm1z by (simp add: transC1_def)
              have mkdA: "(Pred M, 0) \<in> Marked"
                using Marked_Pred_Adm[OF MT L hp] jp_def jm1_def jm1z by simp
              have e10Pz: "entry (Pred M) 1 0 = 0"
              proof -
                have pb: "Pred M = butlast M" using L by (simp add: Pred_def)
                have "0 < length (butlast M)" using L by simp
                thus ?thesis using pb e10z by (simp add: entry_def nth_butlast)
              qed
              have "Mark (Pred M) 0 = 0\<^sub>B
                    \<or> (\<exists>t. Mark (Pred M) 0 = Dpt (enat (entry (Pred M) 1 0)) t)"
                using Mark_leftend_form mkdA predRT by blast
              thus ?thesis
              proof
                assume "Mark (Pred M) 0 = 0\<^sub>B"
                hence "transV M = bpHeadV 0\<^sub>B" using c1eq by (simp add: transV_def)
                thus ?thesis by (simp add: zero_enat_def)
              next
                assume "\<exists>t. Mark (Pred M) 0 = Dpt (enat (entry (Pred M) 1 0)) t"
                then obtain t where
                  "Mark (Pred M) 0 = Dpt (enat (entry (Pred M) 1 0)) t" by blast
                hence "transV M = enat (entry (Pred M) 1 0)"
                  using c1eq by (simp add: transV_def)
                thus ?thesis using e10Pz by simp
              qed
            qed
            have ra: "RightAnces M = [0] @ tail" using raMono segz by simp
            have "RightNodes (Trans M) = RightNodes (transC2 M)" using transM_c2 by simp
            also have "\<dots> = the_enat (transV M) # tail" using rnc2 .
            also have "\<dots> = 0 # tail" using vz by simp
            finally show ?thesis using ra by simp
          next
            case segnz: False
            \<comment> \<open>\<open>jm1\<close>-basepoint mark splits \<open>RightNodes (Trans M)\<close>; IH on the slice\<close>
            have raN: "RightAnces M = RightAnces (seg M 0 jm1) @ tail"
              using raMono segnz by simp
            have IHN: "RightAnces (seg M 0 jm1) = RightNodes (Trans (seg M 0 jm1))"
              using less.IH[OF segLnglt] segRT by blast
            show ?thesis
            proof (cases "jm1 = 0")
              case jm1z: True
              \<comment> \<open>boundary: \<open>Trans M = c\<^sub>2\<close>, slice \<open>= [M\<^bsub>0\<^esub>]\<close> with \<open>RightNodes = [transV]\<close>\<close>
              have leM0: "leR M 0 0 ?j1" using mono by (simp add: monoT_def)
              have adm0: "adm M 0" by (simp add: adm_def nadm_def nextR_def nextrel1_def)
              have m0M: "(M, 0) \<in> Marked"
                using MT leM0 adm0 by (simp add: Marked_def)
              have markTrans: "Mark M 0 = Trans M"
                using ra_Mark0_eq_Trans m0M MR by blast
              have transM_c2: "Trans M = transC2 M"
                using markTrans markc2 jm1z by simp
              \<comment> \<open>slice \<open>N = seg M 0 0 = [M\<^bsub>0\<^esub>]\<close> reduced one-column, \<open>\<not> zeroT\<close>\<close>
              have NsegRT: "seg M 0 0 \<in> RT_PS" using segRT jm1z by simp
              have NsegT: "seg M 0 0 \<in> T_PS" using NsegRT by (simp add: RT_PS_def)
              have Nseglng: "Lng (seg M 0 0) = 1" by simp
              obtain w where Nw: "seg M 0 0 = [(w, w)]"
                using m_6_6_oneColumn[OF NsegT] NsegRT Nseglng by auto
              have nzN: "\<not> zeroT (seg M 0 0)" using segnz jm1z by simp
              have wne: "w \<noteq> 0"
              proof -
                have "entry (seg M 0 0) 1 0 \<noteq> 0" using nzN by (simp add: zeroT_def)
                thus ?thesis using Nw by (simp add: entry_def)
              qed
              have transN: "Trans (seg M 0 0) = Dpt (enat w) 0\<^sub>B"
                using Nw Trans_singleton wne by simp
              have rnN: "RightNodes (Trans (seg M 0 0)) = [w]"
                using transN by simp
              \<comment> \<open>\<open>w = the_enat (transV M)\<close> via \<open>entry M 1 0\<close>\<close>
              have e10w: "entry M 1 0 = w"
              proof -
                have "entry (seg M 0 0) 1 0 = entry M 1 0"
                  using entry_seg[of 0 M 0 0 1] by simp
                thus ?thesis using Nw by (simp add: entry_def)
              qed
              have veq: "the_enat (transV M) = w"
              proof -
                have c1eq: "transC1 M = Mark (Pred M) 0"
                  using transJm1eq jm1z by (simp add: transC1_def)
                have mkdA: "(Pred M, 0) \<in> Marked"
                  using Marked_Pred_Adm[OF MT L hp] jp_def jm1_def jm1z by simp
                have e10P: "entry (Pred M) 1 0 = w"
                proof -
                  have pb: "Pred M = butlast M" using L by (simp add: Pred_def)
                  have "0 < length (butlast M)" using L by simp
                  thus ?thesis using pb e10w by (simp add: entry_def nth_butlast)
                qed
                have markPnz: "Mark (Pred M) 0 \<noteq> 0\<^sub>B"
                proof -
                  have "transC1 M \<noteq> 0\<^sub>B"
                  proof -
                    have "Lng (PB (transC1 M)) = 1"
                      by (rule transC1_single_principal[OF MR MP J1pos T1ne])
                    thus ?thesis by (auto simp: PB_def)
                  qed
                  thus ?thesis using c1eq by simp
                qed
                obtain t where
                  mkform: "Mark (Pred M) 0 = Dpt (enat (entry (Pred M) 1 0)) t"
                  using Mark_leftend_form mkdA predRT markPnz by blast
                have "transV M = enat (entry (Pred M) 1 0)"
                  using c1eq mkform by (simp add: transV_def)
                thus ?thesis using e10P by simp
              qed
              have chain: "RightNodes (Trans M) = RightAnces (seg M 0 0) @ tail"
              proof -
                have "RightNodes (Trans M) = RightNodes (transC2 M)" using transM_c2 by simp
                also have "\<dots> = the_enat (transV M) # tail" using rnc2 .
                also have "\<dots> = w # tail" using veq by simp
                also have "\<dots> = [w] @ tail" by simp
                also have "\<dots> = RightNodes (Trans (seg M 0 0)) @ tail" using rnN by simp
                also have "\<dots> = RightAnces (seg M 0 0) @ tail" using IHN jm1z by simp
                finally show ?thesis .
              qed
              have raeq: "RightAnces M = RightAnces (seg M 0 0) @ tail"
                using raN jm1z by simp
              show ?thesis using raeq chain by simp
            next
              case jm1pos: False
              have jm1g0: "0 < jm1" using jm1pos by simp
              \<comment> \<open>\<open>(M, jm1) \<in> Marked\<close> with \<open>0 < jm1 < Lng M - 1\<close>\<close>
              have admA: "adm M jm1" using jm1_def by (simp add: adm_Adm_adm)
              have jpb: "jp \<le> Lng M - 1" using jplt by simp
              have le1a: "leR M 1 jm1 jp"
                using adm_row1_ancestry[OF MT jpb] jm1_def by simp
              have le0a: "leR M 0 jm1 jp" by (rule m_le1_imp_le0[OF le1a])
              have leMa: "leR M 0 jm1 ?j1"
              proof -
                have st: "nextrel0 M jp ?j1" using parR by (simp add: nextR_def)
                have "(nextrel0 M)\<^sup>*\<^sup>* jm1 jp" using le0a by (simp add: leR_def le0_def)
                hence "(nextrel0 M)\<^sup>*\<^sup>* jm1 ?j1" using st by (rule rtranclp.rtrancl_into_rtrancl)
                moreover have "jm1 < Lng M" using jm1lt L by linarith
                moreover have "?j1 < Lng M" using L by linarith
                ultimately show ?thesis by (simp add: leR_def le0_def)
              qed
              have mMjm1: "(M, jm1) \<in> Marked"
                using MT admA leMa by (simp add: Marked_def)
              \<comment> \<open>the \<open>RightNodes/Mark\<close> split at \<open>jm1\<close>\<close>
              obtain a0 a1 where
                splitT: "RightNodes (Trans M) = a0 @ [entry M 1 jm1] @ a1"
                and splitSeg: "RightNodes (Trans (seg M 0 jm1)) = a0 @ [entry M 1 jm1]"
                and splitMark: "RightNodes (Mark M jm1) = [entry M 1 jm1] @ a1"
                using m_7_4_RightNodes_Mark[OF mMjm1 MR jm1g0 jm1lt] by blast
              \<comment> \<open>\<open>RightNodes (Mark M jm1) = transV # tail = entry M 1 jm1 # tail\<close>\<close>
              have rnMarkc2: "RightNodes (Mark M jm1) = the_enat (transV M) # tail"
                using markc2 rnc2 by simp
              \<comment> \<open>so \<open>a1 = tail\<close>\<close>
              have a1tail: "a1 = tail"
                using splitMark rnMarkc2 by simp
              \<comment> \<open>combine: \<open>RightNodes (Trans M) = RightNodes (Trans (seg M 0 jm1)) @ tail\<close>\<close>
              have "RightNodes (Trans M) = (a0 @ [entry M 1 jm1]) @ a1"
                using splitT by simp
              also have "\<dots> = RightNodes (Trans (seg M 0 jm1)) @ tail"
                using splitSeg a1tail by simp
              also have "\<dots> = RightAnces (seg M 0 jm1) @ tail" using IHN by simp
              finally show ?thesis using raN by simp
            qed
          qed
        qed
      next
        case nmono: False
        \<comment> \<open>multi branch: \<open>RightNodes (Trans M)\<close> depends only on the last component\<close>
        have nz: "\<not> zeroT M" using L by (simp add: zeroT_def)
        have mu: "multiT M" using nmono nz by (simp add: multiT_def)
        let ?A = "take (Pcut M) M"
        let ?PJ = "drop (Pcut M) M"
        have PJeq: "P M ! (Lng (P M) - 1) = ?PJ"
          by (rule trans_multiT_last_component(1)[OF MT mu])
        have cut: "0 < Pcut M \<and> Pcut M \<le> Lng M - 1" using Pcut_le[OF L] by simp
        have Pne: "P M \<noteq> []" by (rule P_nonempty)
        have J1lt: "Lng (P M) - 1 < Lng (P M)" using Pne by (cases "P M") auto
        have PJRT: "?PJ \<in> RT_PS" using m_6_6_P_reduced[OF MT] MR J1lt PJeq by auto
        have PJT: "?PJ \<in> T_PS" using PJRT by (simp add: RT_PS_def)
        have LPJlt: "Lng ?PJ < Lng M"
        proof -
          have "Lng ?PJ = Lng M - Pcut M" by simp
          thus ?thesis using cut L by linarith
        qed
        \<comment> \<open>RightAnces value\<close>
        have raMulti: "RightAnces M = (if ?PJ = [(0,0)] then [0] else RightAnces ?PJ)"
          using raM j1ne nmono PJeq by (simp add: Let_def)
        \<comment> \<open>Trans value\<close>
        have c1: "(M \<notin> RT_PS) = False" using MR by simp
        have c2: "(Lng M - 1 = 0) = False" using L by simp
        have c3: "monoT M = False" using nmono by simp
        have Aeq2: "seg M 0 (Lng M - 1 - Lng (drop (Pcut M) M) + 1 - 1) = ?A"
        proof -
          have LdJ: "Lng (drop (Pcut M) M) = Lng M - Pcut M" by simp
          have "Lng M - 1 - Lng (drop (Pcut M) M) + 1 - 1 = Pcut M - 1"
            using LdJ cut by linarith
          moreover have "seg M 0 (Pcut M - 1) = take (Suc (Pcut M - 1)) M"
            by (rule seg_0_eq_take) (use cut L in linarith)
          moreover have "Suc (Pcut M - 1) = Pcut M" using cut by simp
          ultimately show ?thesis by simp
        qed
        have transM: "Trans M = (if ?PJ = [(0, 0)] then Trans ?A +\<^sub>B Dpt 0 0\<^sub>B
                                 else Trans ?A +\<^sub>B Trans ?PJ)"
        proof -
          have raw: "Trans M =
              (if P M ! (Lng (P M) - 1) = [(0, 0)]
               then Trans (seg M 0 (Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1 - 1))
                      +\<^sub>B Dpt 0 0\<^sub>B
               else Trans (seg M 0 (Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1 - 1))
                      +\<^sub>B Trans (P M ! (Lng (P M) - 1)))"
            by (subst Trans.psimps[OF domT]) (simp only: c1 c2 c3 if_False Let_def)
          show ?thesis unfolding raw PJeq Aeq2 ..
        qed
        show ?thesis
        proof (cases "?PJ = [(0, 0)]")
          case PJz: True
          have ra: "RightAnces M = [0]" using raMulti PJz by simp
          have tv: "Trans M = Trans ?A +\<^sub>B Dpt 0 0\<^sub>B" using transM PJz by simp
          have nzD0: "Dpt 0 0\<^sub>B \<noteq> 0\<^sub>B" by simp
          have "RightNodes (Trans M) = RightNodes (Dpt 0 0\<^sub>B)"
            using tv ra_RightNodes_addBT_right[OF nzD0] by simp
          also have "\<dots> = [0]" by (simp add: zero_enat_def)
          finally show ?thesis using ra by simp
        next
          case PJnz: False
          have ra: "RightAnces M = RightAnces ?PJ" using raMulti PJnz by simp
          have tv: "Trans M = Trans ?A +\<^sub>B Trans ?PJ" using transM PJnz by simp
          \<comment> \<open>\<open>?PJ\<close> not zero (reduced, \<open>\<noteq> [(0,0)]\<close>)\<close>
          have nzPJ: "\<not> zeroT ?PJ"
          proof
            assume z: "zeroT ?PJ"
            have L1: "Lng ?PJ = 1" using z by (simp add: zeroT_def)
            then obtain v where v: "?PJ = [(v, v)]"
              using m_6_6_oneColumn[OF PJT] PJRT by auto
            have "entry ?PJ 1 0 = 0" using z by (simp add: zeroT_def)
            hence "v = 0" using v by (simp add: entry_def)
            thus False using PJnz v by simp
          qed
          have tPJnz: "Trans ?PJ \<noteq> 0\<^sub>B"
            using m_7_3_Trans_zeroT[OF PJRT] nzPJ by blast
          have IHPJ: "RightAnces ?PJ = RightNodes (Trans ?PJ)"
            using less.IH[OF LPJlt] PJRT by blast
          have "RightNodes (Trans M) = RightNodes (Trans ?PJ)"
            using tv ra_RightNodes_addBT_right[OF tPJnz] by simp
          also have "\<dots> = RightAnces ?PJ" using IHPJ by simp
          finally show ?thesis using ra by simp
        qed
      qed
    qed
  qed
qed

end
