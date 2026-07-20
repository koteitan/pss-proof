theory Support_7_033
  imports Frontier_7_038
begin

text \<open>§7.4 keystone, \<open>monoT\<close>-interior \<open>markShift\<close> discharge (Step 2), BOUNDARY
  subcase \<open>transJm1 M = Lng M - 2\<close>.  Here the shifted index
  \<open>transJm1 M - m = Lng M - 2 - m\<close> is the LAST index of \<open>Pred N = Red (seg M m (Lng M - 2))\<close>,
  and \<open>transJm1 M = Lng M - 2\<close> is the LAST index of \<open>Pred M\<close>, so BOTH \<open>Mark\<close>s
  evaluate by @{thm [source] Mark_rightmost1_forward} to
  \<open>Dpt (enat (entry _ 1 (last))) 0\<close>, and the two row-1 entries coincide
  (both \<open>= entry M 1 (Lng M - 2)\<close>) by @{thm [source] repr_entry1_shift_gen}.
  Takes the two rightmost \<open>Marked\<close> anchorings; no IH needed.\<close>

lemma m_7_4_markShift_discharge_boundary:
  assumes MR: "M \<in> RT_PS" and mint: "m < Lng M - 2"
    and leM: "leR M 0 m (Lng M - 1)"
    and ancJm1: "m \<le> transJm1 M"
    and tjbnd: "transJm1 M = Lng M - 2"
    and mkdM: "(Pred M, Lng (Pred M) - 1) \<in> Marked"
    and mkdN: "(Pred (Red (seg M m (Lng M - 1))),
                Lng (Pred (Red (seg M m (Lng M - 1)))) - 1) \<in> Marked"
  shows "Mark (Pred (Red (seg M m (Lng M - 1)))) (transJm1 M - m)
       = Mark (Pred M) (transJm1 M)"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  let ?j1 = "Lng M - 1"  let ?N = "Red (seg M m ?j1)"
  let ?Sp = "seg M m (Lng M - 2)"  let ?RSp = "Red ?Sp"
  have L: "2 < Lng M" using mint by linarith
  have L1: "1 < Lng M" using L by linarith
  have mj1: "m < ?j1" using mint by linarith
  have mlt2: "m < Lng M - 2" using mint by linarith
  \<comment> \<open>\<open>Pred N = Red S'\<close> and its length\<close>
  have j1m1: "?j1 - 1 = Lng M - 2" by simp
  have predN: "Pred ?N = ?RSp"
    using m_7_4_Pred_Red_slice[OF mj1, of M] j1m1 by simp
  have Spne: "?Sp \<noteq> []" using mlt2 by (simp add: seg_def)
  have SpT: "?Sp \<in> T_PS" using Spne by (simp add: T_PS_def)
  have LRSp: "Lng ?RSp = Lng M - 1 - m" using m_6_5_Lng_Red[OF SpT] mlt2 by simp
  have lastN: "Lng (Pred ?N) - 1 = Lng M - 2 - m" using predN LRSp by simp
  \<comment> \<open>shifted index = last index of \<open>Pred N\<close>\<close>
  have idxeq: "transJm1 M - m = Lng (Pred ?N) - 1" using tjbnd lastN by simp
  \<comment> \<open>\<open>Pred N\<close> reduced, nonzero\<close>
  have RSpRT: "?RSp \<in> RT_PS"
  proof -
    have leM2: "leR M 0 m (Lng M - 2)"
      by (rule m_5_1_ancestor_tree_1[OF MT leM]) (use mint in linarith)+
    show ?thesis using slice_Red_in_RT_PS[OF MR mlt2 _ leM2] mint by simp
  qed
  have predNRT: "Pred ?N \<in> RT_PS" using predN RSpRT by simp
  have nzPredN: "\<not> zeroT (Pred ?N)"
  proof -
    have "1 < Lng (Pred ?N)" using predN LRSp mlt2 by simp
    thus ?thesis by (auto simp: zeroT_def)
  qed
  \<comment> \<open>\<open>Pred M\<close> reduced, nonzero; its last index = \<open>Lng M - 2 = transJm1 M\<close>\<close>
  have predMb: "Pred M = butlast M" using L1 by (simp add: Pred_def)
  have LPM: "Lng (Pred M) = Lng M - 1" using predMb by simp
  have lastM: "Lng (Pred M) - 1 = Lng M - 2" using LPM by simp
  have predMRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have nzPredM: "\<not> zeroT (Pred M)"
  proof - have "1 < Lng (Pred M)" using LPM L by linarith
    thus ?thesis by (auto simp: zeroT_def) qed
  \<comment> \<open>both \<open>Mark\<close>s are rightmost evaluations\<close>
  have markN: "Mark (Pred ?N) (Lng (Pred ?N) - 1)
             = Dpt (enat (entry (Pred ?N) 1 (Lng (Pred ?N) - 1))) 0\<^sub>B"
    by (rule Mark_rightmost1_forward[OF predNRT nzPredN mkdN])
  have markM: "Mark (Pred M) (Lng (Pred M) - 1)
             = Dpt (enat (entry (Pred M) 1 (Lng (Pred M) - 1))) 0\<^sub>B"
    by (rule Mark_rightmost1_forward[OF predMRT nzPredM mkdM])
  \<comment> \<open>the two row-1 entries coincide (both \<open>= entry M 1 (Lng M - 2)\<close>)\<close>
  have eM: "entry (Pred M) 1 (Lng (Pred M) - 1) = entry M 1 (Lng M - 2)"
  proof -
    have "entry (Pred M) 1 (Lng M - 2) = entry (butlast M) 1 (Lng M - 2)"
      using predMb by simp
    also have "\<dots> = entry M 1 (Lng M - 2)"
      using L by (simp add: entry_def nth_butlast)
    finally show ?thesis using lastM by simp
  qed
  have eN: "entry (Pred ?N) 1 (Lng (Pred ?N) - 1) = entry M 1 (Lng M - 2)"
  proof -
    have iN: "Lng M - 2 - m < Lng ?RSp" using LRSp mlt2 by linarith
    have leM2: "leR M 0 m (Lng M - 2)"
      by (rule m_5_1_ancestor_tree_1[OF MT leM]) (use mint in linarith)+
    have blt: "Lng M - 2 \<le> Lng M - 1" by simp
    have "entry ?RSp 1 (Lng M - 2 - m) = entry M 1 (m + (Lng M - 2 - m))"
      by (rule repr_entry1_shift_gen[OF MR mlt2 blt leM2 iN])
    also have "m + (Lng M - 2 - m) = Lng M - 2" using mlt2 by linarith
    finally show ?thesis using predN lastN by simp
  qed
  \<comment> \<open>assemble\<close>
  have "Mark (Pred ?N) (transJm1 M - m) = Mark (Pred ?N) (Lng (Pred ?N) - 1)"
    using idxeq by simp
  also have "\<dots> = Dpt (enat (entry M 1 (Lng M - 2))) 0\<^sub>B" using markN eN by simp
  also have "\<dots> = Mark (Pred M) (Lng (Pred M) - 1)" using markM eM by simp
  also have "\<dots> = Mark (Pred M) (transJm1 M)" using tjbnd lastM by simp
  finally show ?thesis .
qed


section \<open>§7.4 keystone: \<open>Mark M m = Trans (seg M m (Lng M - 1))\<close> (Step 4)\<close>

text \<open>The keystone, by strong \<open>Lng\<close>-induction.  Case split on the marked index
  \<open>m\<close> and the shape of \<open>M\<close>:
  \<^item> \<open>m = 0\<close>: @{thm [source] m_7_4_Mark_Trans_repr_m0};
  \<^item> \<open>m > 0\<close>, \<open>multiT M\<close>: reduce to the last \<open>P\<close>-component
    (@{thm [source] m_7_4_repr_multiT_step}) and apply the IH there;
  \<^item> \<open>m > 0\<close>, \<open>monoT M\<close>, \<open>m = Lng M - 2\<close> (boundary):
    @{thm [source] m_7_4_Mark_Trans_repr_monoT_boundary};
  \<^item> \<open>m > 0\<close>, \<open>monoT M\<close>, \<open>m < Lng M - 2\<close> (interior):
    @{thm [source] m_7_4_monoT_interior_core}, discharging \<open>ihPred\<close> from the IH
    at \<open>Pred M\<close> (index \<open>m\<close>) and \<open>markShift\<close> from
    @{thm [source] m_7_4_markShift_discharge_interior} /
    @{thm [source] m_7_4_markShift_discharge_boundary} (sub-split on
    \<open>transJm1 M < Lng M - 2\<close> vs \<open>= Lng M - 2\<close>), whose IH premises are at
    \<open>Pred M\<close> (index \<open>transJm1 M\<close>) and \<open>Pred N\<close> (index \<open>transJm1 M - m\<close>),
    both \<open>Lng\<close>-smaller.\<close>

lemma m_7_4_Mark_Trans_repr_aux:
  "M \<in> RT_PS \<longrightarrow> (\<forall>m. (M, m) \<in> Marked \<longrightarrow> m < Lng M - 1
                       \<longrightarrow> Mark M m = Trans (seg M m (Lng M - 1)))"
proof (induction M rule: measure_induct_rule[where f=Lng])
  case (less M)
  show ?case
  proof (intro impI allI)
    fix m assume MR: "M \<in> RT_PS" and mM: "(M, m) \<in> Marked" and mlt: "m < Lng M - 1"
    have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
    have L1: "1 < Lng M" using mlt by linarith
    let ?j1 = "Lng M - 1"
    show "Mark M m = Trans (seg M m ?j1)"
    proof (cases "m = 0")
      case True
      have "0 < Lng M - 1" using mlt True by linarith
      thus ?thesis using m_7_4_Mark_Trans_repr_m0[OF _ MR] mM True by simp
    next
      case mpos: False
      hence m0: "m > 0" by simp
      show ?thesis
      proof (cases "monoT M")
        case mono: True
        show ?thesis
        proof (cases "m = Lng M - 2")
          case bnd: True
          have L: "1 < Lng M - 1" using m0 bnd by linarith
          show ?thesis
            by (rule m_7_4_Mark_Trans_repr_monoT_boundary[OF mM MR mono bnd L])
        next
          case nbnd: False
          have mint: "m < Lng M - 2" using mlt nbnd m0 by linarith
          \<comment> \<open>=== anchoring facts (mirroring the interior core) ===\<close>
          have L: "2 < Lng M" using mint by linarith
          have mj1: "m < ?j1" using mint by linarith
          have j1le: "?j1 \<le> Lng M - 1" by simp
          have leM: "leR M 0 m ?j1" using mM by (simp add: Marked_def)
          have hp: "hasParent M 0 ?j1" by (rule monoT_hasParent0_last[OF MT mono L1])
          let ?j0 = "parent M 0 ?j1"
          have parj0: "nextR M 0 ?j0 ?j1"
            using hp unfolding hasParent_def parent_def by (rule theI')
          have j0lt: "?j0 < ?j1" using parj0 by (simp add: nextR_def nextrel0_def)
          have le0m: "le0 M m ?j1" using leM by (simp add: leR_def)
          have mnej1: "m \<noteq> ?j1" using mj1 by simp
          have anc0: "m \<le> ?j0"
            by (rule a1_le0_ancestor_le_parent[OF le0m mnej1 parj0])
          have admMm: "adm M m" using mM by (simp add: Marked_def)
          have ancJm1: "m \<le> transJm1 M"
          proof -
            have "m \<le> Adm M ?j0" by (rule adm_Adm_max[OF admMm anc0])
            thus ?thesis by (simp add: transJm1_def transJ0_def transJ1_def)
          qed
          \<comment> \<open>\<open>Pred M\<close> facts\<close>
          have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
          have predb: "Pred M = butlast M" using L1 by (simp add: Pred_def)
          have LP: "Lng (Pred M) = Lng M - 1" using predb by simp
          have LPlt: "Lng (Pred M) < Lng M" using LP L1 by linarith
          have mP: "(Pred M, m) \<in> Marked"
            by (rule Marked_Pred[OF MT L1 mM]) (use mj1 in linarith)
          \<comment> \<open>ihPred from the IH at \<open>Pred M\<close>, index \<open>m\<close>\<close>
          have mPlt: "m < Lng (Pred M) - 1" using LP mint by linarith
          have ihPred: "Mark (Pred M) m = Trans (seg (Pred M) m (Lng (Pred M) - 1))"
            using less.IH[OF LPlt] predRT mP mPlt by blast
          \<comment> \<open>=== N facts ===\<close>
          let ?S = "seg M m ?j1"  let ?N = "Red ?S"
          have anc: "Red ?N = ?N \<and> monoT ?N
                   \<and> ?S = (IncrFirst ^^ (entry M 0 m - entry M 1 m)) ?N"
            by (rule m_6_6_ancestor_slice_Red_IncrFirst[OF MR mj1 j1le leM])
          have monoN: "monoT ?N" using anc by simp
          have NR: "?N \<in> RT_PS" using slice_Red_in_RT_PS[OF MR mj1 j1le leM] by simp
          have NT: "?N \<in> T_PS" using NR by (simp add: RT_PS_def)
          have LN: "Lng ?N = Suc ?j1 - m"
          proof -
            have "Lng ?N = Lng ?S"
              using arg_cong[OF conjunct2[OF conjunct2[OF anc]], of Lng]
              by (simp add: Lng_funpow_IncrFirst)
            thus ?thesis by simp
          qed
          have LNgt2: "2 < Lng ?N" using LN mint by simp
          have LN1: "1 < Lng ?N" using LNgt2 by linarith
          have LNlt: "Lng ?N < Lng M" using LN m0 L1 by linarith
          have predNRT: "Pred ?N \<in> RT_PS" by (rule Pred_RT_PS[OF NR])
          have predNb: "Pred ?N = butlast ?N" using LN1 by (simp add: Pred_def)
          have LPN: "Lng (Pred ?N) = Lng ?N - 1" using predNb by simp
          have LPNlt: "Lng (Pred ?N) < Lng M" using LPN LN1 LNlt by linarith
          \<comment> \<open>\<open>transJm1 N = transJm1 M - m\<close> and \<open>(Pred N, transJm1 N) \<in> Marked\<close>\<close>
          have jm1N: "transJm1 ?N = transJm1 M - m"
            by (rule repr_transJm1_shift[OF mM MR mint leM hp anc0 j0lt])
          have hpN: "hasParent ?N 0 (Lng ?N - 1)"
            by (rule monoT_hasParent0_last[OF NT monoN LN1])
          have mkdAN: "(Pred ?N, Adm ?N (parent ?N 0 (Lng ?N - 1))) \<in> Marked"
            using Marked_Pred_Adm[OF NT LN1 hpN] by simp
          have mkdPN: "(Pred ?N, transJm1 M - m) \<in> Marked"
            using mkdAN jm1N by (simp add: transJm1_def transJ0_def transJ1_def)
          \<comment> \<open>leR anchoring of \<open>(Pred N, transJm1 M - m)\<close>\<close>
          have lePN: "leR (Red (seg M m (Lng M - 2))) 0 (transJm1 M - m)
                          (Lng (Red (seg M m (Lng M - 2))) - 1)"
          proof -
            have j1m1: "?j1 - 1 = Lng M - 2" by simp
            have predNeq: "Pred ?N = Red (seg M m (Lng M - 2))"
              using m_7_4_Pred_Red_slice[OF mj1, of M] j1m1 by simp
            have "leR (Pred ?N) 0 (transJm1 M - m) (Lng (Pred ?N) - 1)"
              using mkdPN by (simp add: Marked_def)
            thus ?thesis using predNeq by simp
          qed
          \<comment> \<open>\<open>(M, transJm1 M) \<in> Marked\<close> (holds in both interior/boundary subcases)\<close>
          have mMJm1: "(M, transJm1 M) \<in> Marked"
          proof -
            have admA: "adm M (Adm M ?j0)" by (rule adm_Adm_adm)
            have aLe: "Adm M ?j0 \<le> ?j0" by (rule adm_Adm_le)
            have altj1: "Adm M ?j0 < ?j1" using aLe j0lt by linarith
            have le1a: "leR M 1 (Adm M ?j0) ?j0"
              by (rule adm_row1_ancestry[OF MT]) (use j0lt in linarith)
            have le0a: "leR M 0 (Adm M ?j0) ?j0" by (rule m_le1_imp_le0[OF le1a])
            have "le0 M (Adm M ?j0) ?j1"
            proof -
              have st: "nextrel0 M ?j0 ?j1" using parj0 by (simp add: nextR_def)
              have "(nextrel0 M)\<^sup>*\<^sup>* (Adm M ?j0) ?j0"
                using le0a by (simp add: leR_def le0_def)
              hence "(nextrel0 M)\<^sup>*\<^sup>* (Adm M ?j0) ?j1"
                using st by (rule rtranclp.rtrancl_into_rtrancl)
              moreover have "Adm M ?j0 < Lng M" using altj1 L1 by linarith
              moreover have "?j1 < Lng M" using L1 by linarith
              ultimately show ?thesis by (simp add: le0_def)
            qed
            hence "leR M 0 (Adm M ?j0) ?j1" by (simp add: leR_def)
            thus ?thesis using admA MT
              by (simp add: Marked_def transJm1_def transJ0_def transJ1_def)
          qed
          \<comment> \<open>=== markShift via the interior/boundary discharge ===\<close>
          have markShift: "Mark (Pred ?N) (transJm1 M - m) = Mark (Pred M) (transJm1 M)"
          proof (cases "transJm1 M = Lng M - 2")
            case tbnd: True
            \<comment> \<open>boundary: both \<open>Mark\<close>s rightmost; rightmost anchorings from \<open>mkdPN\<close>/\<open>mP\<close>\<close>
            have mkdN': "(Pred ?N, Lng (Pred ?N) - 1) \<in> Marked"
            proof -
              have j1m1: "?j1 - 1 = Lng M - 2" by simp
              have predNeq: "Pred ?N = Red (seg M m (Lng M - 2))"
                using m_7_4_Pred_Red_slice[OF mj1, of M] j1m1 by simp
              have Spne: "seg M m (Lng M - 2) \<noteq> []" using mint by (simp add: seg_def)
              have SpT: "seg M m (Lng M - 2) \<in> T_PS" using Spne by (simp add: T_PS_def)
              have LRSp: "Lng (Red (seg M m (Lng M - 2))) = Lng M - 1 - m"
                using m_6_5_Lng_Red[OF SpT] mint by simp
              have "Lng (Pred ?N) - 1 = Lng M - 2 - m"
                using predNeq LRSp by simp
              hence "transJm1 M - m = Lng (Pred ?N) - 1" using tbnd by simp
              thus ?thesis using mkdPN by simp
            qed
            have mkdM': "(Pred M, Lng (Pred M) - 1) \<in> Marked"
            proof -
              have tjlt1: "transJm1 M < Lng M - 1" using tbnd L by linarith
              have mk: "(Pred M, transJm1 M) \<in> Marked"
                by (rule Marked_Pred[OF MT L1 mMJm1 tjlt1])
              have "Lng (Pred M) - 1 = transJm1 M" using LP tbnd by simp
              thus ?thesis using mk by simp
            qed
            show ?thesis
              by (rule m_7_4_markShift_discharge_boundary[OF MR mint leM ancJm1 tbnd mkdM' mkdN'])
          next
            case tint: False
            have tjint: "transJm1 M < Lng M - 2"
            proof -
              have "transJm1 M = Adm M ?j0" by (simp add: transJm1_def transJ0_def transJ1_def)
              moreover have "Adm M ?j0 \<le> ?j0" by (rule adm_Adm_le)
              ultimately have "transJm1 M \<le> ?j0" by simp
              hence "transJm1 M \<le> Lng M - 2" using j0lt by linarith
              thus ?thesis using tint by linarith
            qed
            \<comment> \<open>ihB from the IH at \<open>Pred N\<close>, index \<open>transJm1 M - m\<close>\<close>
            have idxNlt: "transJm1 M - m < Lng (Pred ?N) - 1"
            proof -
              have j1m1: "?j1 - 1 = Lng M - 2" by simp
              have predNeq: "Pred ?N = Red (seg M m (Lng M - 2))"
                using m_7_4_Pred_Red_slice[OF mj1, of M] j1m1 by simp
              have Spne: "seg M m (Lng M - 2) \<noteq> []" using mint by (simp add: seg_def)
              have SpT: "seg M m (Lng M - 2) \<in> T_PS" using Spne by (simp add: T_PS_def)
              have LRSp: "Lng (Red (seg M m (Lng M - 2))) = Lng M - 1 - m"
                using m_6_5_Lng_Red[OF SpT] mint by simp
              have "Lng (Pred ?N) - 1 = Lng M - 2 - m" using predNeq LRSp by simp
              thus ?thesis using tjint ancJm1 by linarith
            qed
            have ihB: "Mark (Pred ?N) (transJm1 M - m)
                     = Trans (seg (Pred ?N) (transJm1 M - m) (Lng (Pred ?N) - 1))"
              using less.IH[OF LPNlt] predNRT mkdPN idxNlt by blast
            \<comment> \<open>markM from the IH at \<open>Pred M\<close>, index \<open>transJm1 M\<close>\<close>
            have tjlt: "transJm1 M < Lng (Pred M) - 1" using tjint LP by linarith
            have tjlt1: "transJm1 M < Lng M - 1" using tjint by linarith
            have mkdJm1: "(Pred M, transJm1 M) \<in> Marked"
              by (rule Marked_Pred[OF MT L1 mMJm1 tjlt1])
            have ihMa: "Mark (Pred M) (transJm1 M)
                      = Trans (seg (Pred M) (transJm1 M) (Lng (Pred M) - 1))"
              using less.IH[OF LPlt] predRT mkdJm1 tjlt by blast
            have markM: "Mark (Pred M) (transJm1 M)
                       = Trans (seg M (transJm1 M) (Lng M - 2))"
            proof -
              have tjle: "transJm1 M \<le> Lng M - 2" using tjint by linarith
              have blt: "Lng M - 2 < Lng M - 1" using L by linarith
              have LPm1: "Lng (Pred M) - 1 = Lng M - 2" using LP by simp
              have "seg (Pred M) (transJm1 M) (Lng (Pred M) - 1)
                    = seg M (transJm1 M) (Lng M - 2)"
                using m_7_4_seg_Pred_eq[OF L1 tjle blt] LPm1 by simp
              thus ?thesis using ihMa by simp
            qed
            show ?thesis
              by (rule m_7_4_markShift_discharge_interior
                    [OF MR mint leM ancJm1 tjint lePN ihB markM])
          qed
          \<comment> \<open>=== apply the interior core ===\<close>
          show ?thesis
            by (rule m_7_4_monoT_interior_core[OF MR mono mM mint ihPred markShift])
        qed
      next
        case multi: False
        have nz: "\<not> zeroT M" using L1 by (simp add: zeroT_def)
        have mu: "multiT M" using multi nz by (simp add: multiT_def)
        \<comment> \<open>reduce to the last \<open>P\<close>-component, apply the IH there\<close>
        define PJ where "PJ = drop (Pcut M) M"
        have step: "Mark M m = Mark PJ (m - Pcut M)
                  \<and> seg M m ?j1 = seg PJ (m - Pcut M) (Lng PJ - 1)
                  \<and> PJ \<in> RT_PS \<and> (PJ, m - Pcut M) \<in> Marked
                  \<and> Lng PJ < Lng M \<and> m - Pcut M < Lng PJ - 1"
          using m_7_4_repr_multiT_step[OF MR mu mM mlt] PJ_def by simp
        have e1: "Mark M m = Mark PJ (m - Pcut M)" using step by simp
        have e2: "seg M m ?j1 = seg PJ (m - Pcut M) (Lng PJ - 1)" using step by simp
        have PJRT: "PJ \<in> RT_PS" using step by simp
        have PJm: "(PJ, m - Pcut M) \<in> Marked" using step by simp
        have PJlt: "Lng PJ < Lng M" using step by simp
        have PJmlt: "m - Pcut M < Lng PJ - 1" using step by simp
        have "Mark PJ (m - Pcut M) = Trans (seg PJ (m - Pcut M) (Lng PJ - 1))"
          using less.IH[OF PJlt] PJRT PJm PJmlt by blast
        thus ?thesis using e1 e2 by simp
      qed
    qed
  qed
qed

end
