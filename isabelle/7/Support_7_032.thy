theory Support_7_032
  imports Frontier_7_037
begin

text \<open>N-side \<open>Trans\<close>/slice transport at a shifted interior index: for
  \<open>N = Red (seg M m j\<^sub>1)\<close> (\<open>j\<^sub>1 = Lng M - 1\<close>), the backward-to-last slice of
  \<open>Pred N = Red (seg M m (j\<^sub>1 - 1))\<close> at a local interior index \<open>a\<close> has the same
  \<open>Trans\<close> as the corresponding slice of \<open>M\<close> ending at \<open>Lng M - 2\<close>.  This is the
  \<open>transJm1\<close>-index analogue of @{thm [source] m_7_4_Trans_PredN}.  Chain:
  \<open>Pred N = Red S'\<close> with \<open>S' = seg M m (Lng M - 2)\<close>
  (@{thm [source] m_7_4_Pred_Red_slice}); \<open>S' = (IncrFirst^^k') (Red S')\<close>
  (@{thm [source] m_6_6_ancestor_slice_Red_IncrFirst}); \<open>seg\<close> commutes with
  \<open>IncrFirst^^k'\<close> (@{thm [source] seg_funpow_IncrFirst}) and \<open>Trans\<close> ignores it
  (@{thm [source] Trans_funpow_IncrFirst}); \<open>seg_of_seg\<close> for the endpoint.
  Takes \<open>lePN\<close> (= the \<open>Marked\<close> anchoring of \<open>(Pred N, a)\<close>) for the slice's
  \<open>Red \<in> RT_PS\<close> facts.\<close>

lemma m_7_4_Trans_PredN_shift:
  assumes MR: "M \<in> RT_PS" and mint: "m < Lng M - 2"
    and leM: "leR M 0 m (Lng M - 1)"
    and alt: "a < Lng (Red (seg M m (Lng M - 2))) - 1"
    and lePN: "leR (Red (seg M m (Lng M - 2))) 0 a (Lng (Red (seg M m (Lng M - 2))) - 1)"
  shows "Trans (seg (Pred (Red (seg M m (Lng M - 1)))) a
                    (Lng (Pred (Red (seg M m (Lng M - 1)))) - 1))
       = Trans (seg M (m + a) (Lng M - 2))"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  let ?j1 = "Lng M - 1"
  let ?Sp = "seg M m (Lng M - 2)"          \<comment> \<open>\<open>S'\<close>\<close>
  let ?RSp = "Red ?Sp"                       \<comment> \<open>\<open>Pred N\<close>\<close>
  have L: "2 < Lng M" using mint by linarith
  have mj1: "m < ?j1" using mint by linarith
  \<comment> \<open>\<open>Pred N = Red S'\<close>\<close>
  have j1m1: "?j1 - 1 = Lng M - 2" by simp
  have predN: "Pred (Red (seg M m ?j1)) = ?RSp"
    using m_7_4_Pred_Red_slice[OF mj1, of M] j1m1 by simp
  \<comment> \<open>basic lengths\<close>
  have mlt2: "m < Lng M - 2" using mint by linarith
  have LSp: "Lng ?Sp = Lng M - 1 - m" using mlt2 by simp
  have Spne: "?Sp \<noteq> []" using mlt2 by (simp add: seg_def)
  have SpT: "?Sp \<in> T_PS" using Spne by (simp add: T_PS_def)
  have LRSp: "Lng ?RSp = Lng ?Sp" by (rule m_6_5_Lng_Red[OF SpT])
  have LRSp': "Lng ?RSp = Lng M - 1 - m" using LRSp LSp by simp
  have RSpRT: "?RSp \<in> RT_PS"
  proof -
    have mlt2': "m < Lng M - 2" using mint by linarith
    have leM2: "leR M 0 m (Lng M - 2)"
      by (rule m_5_1_ancestor_tree_1[OF MT leM]) (use mint in linarith)+
    show ?thesis using slice_Red_in_RT_PS[OF MR mlt2' _ leM2] mint by simp
  qed
  have RSpT: "?RSp \<in> T_PS" using RSpRT by (simp add: RT_PS_def)
  \<comment> \<open>last index of \<open>Pred N\<close>: \<open>Lng (Pred N) - 1 = Lng M - 2 - m\<close>\<close>
  have lasteq: "Lng (Pred (Red (seg M m ?j1))) - 1 = Lng M - 2 - m"
    using predN LRSp' by simp
  \<comment> \<open>\<open>S' = (IncrFirst^^k') (Red S')\<close>\<close>
  have leM2: "leR M 0 m (Lng M - 2)"
    by (rule m_5_1_ancestor_tree_1[OF MT leM]) (use mint in linarith)+
  define k' where "k' = entry M 0 m - entry M 1 m"
  have SpIF: "?Sp = (IncrFirst ^^ k') ?RSp"
    using m_6_6_ancestor_slice_Red_IncrFirst[OF MR mlt2 _ leM2] mint k'_def by simp
  \<comment> \<open>local last index \<open>w = Lng (Red S') - 1 = Lng M - 2 - m\<close>; \<open>m + w = Lng M - 2\<close>\<close>
  let ?w = "Lng ?RSp - 1"
  have wval: "?w = Lng M - 2 - m" using LRSp' by simp
  have mw: "m + ?w = Lng M - 2" using wval mint by linarith
  \<comment> \<open>(i) RHS = \<open>Trans (seg (Red S') a w)\<close> via \<open>seg_of_seg\<close> + \<open>IncrFirst\<close>\<close>
  have wleSp: "?w \<le> Lng M - 2 - m" using wval by simp
  have segofseg: "seg ?Sp a ?w = seg M (m + a) (m + ?w)"
  proof -
    have ab: "m \<le> Lng M - 2" using mint by linarith
    have db: "?w \<le> (Lng M - 2) - m" using wval by simp
    show ?thesis using seg_of_seg[OF ab db, where M=M and c=a] by simp
  qed
  have segM_eq: "seg M (m + a) (Lng M - 2) = seg ?Sp a ?w"
    using segofseg mw by simp
  \<comment> \<open>(ii) \<open>seg S' a w = (IncrFirst^^k') (seg (Red S') a w)\<close>\<close>
  have wlt: "?w < Lng ?RSp" using alt by simp
  have segcomm: "seg ?Sp a ?w = (IncrFirst ^^ k') (seg ?RSp a ?w)"
  proof -
    have "seg ((IncrFirst ^^ k') ?RSp) a ?w = (IncrFirst ^^ k') (seg ?RSp a ?w)"
      by (rule seg_funpow_IncrFirst[OF wlt])
    thus ?thesis using SpIF by simp
  qed
  \<comment> \<open>(iii) \<open>Trans\<close> ignores \<open>IncrFirst^^k'\<close> on the inner slice\<close>
  have innerT: "seg ?RSp a ?w \<in> T_PS"
  proof -
    have "a \<le> ?w" using alt by simp
    hence "seg ?RSp a ?w \<noteq> []" by (simp add: seg_def)
    thus ?thesis by (simp add: T_PS_def)
  qed
  have innerRedRT: "Red (seg ?RSp a ?w) \<in> RT_PS"
    using slice_Red_in_RT_PS[OF RSpRT alt _ lePN] by simp
  have transIF: "Trans ((IncrFirst ^^ k') (seg ?RSp a ?w)) = Trans (seg ?RSp a ?w)"
    by (rule Trans_funpow_IncrFirst[OF innerT innerRedRT])
  \<comment> \<open>assemble\<close>
  have "Trans (seg M (m + a) (Lng M - 2)) = Trans (seg ?Sp a ?w)"
    using segM_eq by simp
  also have "\<dots> = Trans ((IncrFirst ^^ k') (seg ?RSp a ?w))" using segcomm by simp
  also have "\<dots> = Trans (seg ?RSp a ?w)" by (rule transIF)
  finally have RHS: "Trans (seg M (m + a) (Lng M - 2)) = Trans (seg ?RSp a ?w)" .
  \<comment> \<open>LHS = \<open>Trans (seg (Red S') a w)\<close>\<close>
  have LHS: "Trans (seg (Pred (Red (seg M m ?j1))) a
                       (Lng (Pred (Red (seg M m ?j1))) - 1))
           = Trans (seg ?RSp a ?w)"
    using predN lasteq wval by simp
  show ?thesis using LHS RHS by simp
qed

text \<open>§7.4 keystone, \<open>monoT\<close>-interior \<open>markShift\<close> discharge (Step 2), INTERIOR
  subcase \<open>transJm1 M < Lng M - 2\<close>.  Goal
  \<open>Mark (Pred N) (transJm1 M - m) = Mark (Pred M) (transJm1 M)\<close>
  (\<open>N = Red (seg M m (Lng M - 1))\<close>).  Takes
  \<^item> \<open>ihB\<close>: keystone IH at \<open>Pred N\<close>, index \<open>transJm1 M - m\<close>
    (\<open>Mark (Pred N) (transJm1 M - m) = Trans (seg (Pred N) (transJm1 M - m) (Lng (Pred N) - 1))\<close>);
  \<^item> \<open>markM\<close>: the \<open>M\<close>-side value
    (\<open>Mark (Pred M) (transJm1 M) = Trans (seg M (transJm1 M) (Lng M - 2))\<close>),
    discharged in the assembly from the IH at \<open>Pred M\<close> (interior) — see id1's
    @{thm [source] m_7_4_interior_id1} pattern;
  \<^item> the \<open>Marked\<close> anchoring \<open>lePN\<close> of \<open>(Pred N, transJm1 M - m)\<close>.
  Reduces \<open>ihB\<close>'s slice to \<open>Trans (seg M (transJm1 M) (Lng M - 2))\<close> via
  @{thm [source] m_7_4_Trans_PredN_shift} (with \<open>m + (transJm1 M - m) = transJm1 M\<close>
  since \<open>m \<le> transJm1 M\<close>), matching \<open>markM\<close>.  Empirically exact
  (repr7: 0 viol, maxlen\<le>5).\<close>

lemma m_7_4_markShift_discharge_interior:
  assumes MR: "M \<in> RT_PS" and mint: "m < Lng M - 2"
    and leM: "leR M 0 m (Lng M - 1)"
    and ancJm1: "m \<le> transJm1 M"
    and tjint: "transJm1 M < Lng M - 2"
    and lePN: "leR (Red (seg M m (Lng M - 2))) 0 (transJm1 M - m)
                   (Lng (Red (seg M m (Lng M - 2))) - 1)"
    and ihB: "Mark (Pred (Red (seg M m (Lng M - 1)))) (transJm1 M - m)
            = Trans (seg (Pred (Red (seg M m (Lng M - 1)))) (transJm1 M - m)
                         (Lng (Pred (Red (seg M m (Lng M - 1)))) - 1))"
    and markM: "Mark (Pred M) (transJm1 M)
              = Trans (seg M (transJm1 M) (Lng M - 2))"
  shows "Mark (Pred (Red (seg M m (Lng M - 1)))) (transJm1 M - m)
       = Mark (Pred M) (transJm1 M)"
proof -
  let ?j1 = "Lng M - 1"  let ?N = "Red (seg M m ?j1)"
  let ?RSp = "Red (seg M m (Lng M - 2))"
  let ?a = "transJm1 M - m"
  \<comment> \<open>\<open>Lng (Red S') = Lng M - 1 - m\<close>, so the interior index bound \<open>alt\<close> holds\<close>
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have mlt2: "m < Lng M - 2" using mint by linarith
  have Spne: "seg M m (Lng M - 2) \<noteq> []" using mlt2 by (simp add: seg_def)
  have SpT: "seg M m (Lng M - 2) \<in> T_PS" using Spne by (simp add: T_PS_def)
  have LRSp: "Lng ?RSp = Lng M - 1 - m"
    using m_6_5_Lng_Red[OF SpT] mlt2 by simp
  have alt: "?a < Lng ?RSp - 1"
    using LRSp ancJm1 tjint by linarith
  \<comment> \<open>N-side: reduce \<open>ihB\<close>'s slice to \<open>Trans (seg M (transJm1 M) (Lng M - 2))\<close>\<close>
  have shift: "Trans (seg (Pred ?N) ?a (Lng (Pred ?N) - 1))
             = Trans (seg M (m + ?a) (Lng M - 2))"
    by (rule m_7_4_Trans_PredN_shift[OF MR mint leM alt lePN])
  have mpa: "m + ?a = transJm1 M" using ancJm1 by simp
  have "Mark (Pred ?N) ?a = Trans (seg (Pred ?N) ?a (Lng (Pred ?N) - 1))"
    by (rule ihB)
  also have "\<dots> = Trans (seg M (m + ?a) (Lng M - 2))" by (rule shift)
  also have "\<dots> = Trans (seg M (transJm1 M) (Lng M - 2))" using mpa by simp
  also have "\<dots> = Mark (Pred M) (transJm1 M)" using markM by (rule sym)
  finally show ?thesis .
qed

end
