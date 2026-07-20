theory Frontier_6_017
  imports P_6_4_FirstNodes_Joints_mono
begin

text \<open>The defining property of the trunk: every step below \<open>TrMax M\<close> is a row-1
  \<open><\<^sup>Next\<close>-edge.\<close>

lemma TrMax_trunk_step:
  assumes "M \<in> T_PS" "j' < TrMax M"
  shows "nextR M 1 j' (j' + 1)"
proof -
  let ?S = "{j. \<forall>j'<j. nextR M 1 j' (j' + 1)}"
  have LM: "Lng M > 0" using assms(1) by (cases M) (auto simp: T_PS_def)
  have sub: "?S \<subseteq> {..Lng M - 1}"
  proof
    fix j assume "j \<in> ?S"
    hence H: "\<forall>j'<j. nextR M 1 j' (j' + 1)" by simp
    show "j \<in> {..Lng M - 1}"
    proof (rule ccontr)
      assume "j \<notin> {..Lng M - 1}"
      hence "Lng M - 1 < j" by simp
      hence "nextR M 1 (Lng M - 1) ((Lng M - 1) + 1)" using H by blast
      hence "(Lng M - 1) + 1 < Lng M" by (simp add: nextR_def nextrel1_def)
      thus False using LM by simp
    qed
  qed
  hence fin: "finite ?S" by (rule finite_subset) simp
  have ne: "?S \<noteq> {}" by blast
  have "Max ?S \<in> ?S" using fin ne by (rule Max_in)
  hence "\<forall>j'<Max ?S. nextR M 1 j' (j' + 1)" by simp
  moreover have "TrMax M = Max ?S" by (simp add: TrMax_def)
  ultimately show ?thesis using assms(2) by simp
qed

text \<open>Trunk ancestry in row 1: any \<open>a \<le> b \<le> TrMax M\<close> are row-1 related.\<close>

lemma trunk_le1:
  assumes "M \<in> T_PS" "a \<le> b" "b \<le> TrMax M"
  shows "leR M 1 a b"
proof -
  have LM: "Lng M > 0" using assms(1) by (cases M) (auto simp: T_PS_def)
  have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF assms(1)])
  have "(nextrel1 M)\<^sup>*\<^sup>* a b" using assms(2,3)
  proof (induction b)
    case 0 thus ?case by simp
  next
    case (Suc b)
    show ?case
    proof (cases "a = Suc b")
      case True thus ?thesis by simp
    next
      case False
      with Suc.prems(1) have ab: "a \<le> b" by simp
      have bT: "b < TrMax M" using Suc.prems(2) by simp
      have "(nextrel1 M)\<^sup>*\<^sup>* a b" using Suc.IH[OF ab] bT by simp
      moreover have "nextrel1 M b (Suc b)"
        using TrMax_trunk_step[OF assms(1) bT] by (simp add: nextR_def)
      ultimately show ?thesis by simp
    qed
  qed
  moreover have "a < Lng M" using assms(2,3) tb LM by linarith
  moreover have "b < Lng M" using assms(3) tb LM by linarith
  ultimately show ?thesis by (simp add: leR_def le1_def)
qed

text \<open>Trunk ancestry in row 0 (a consequence of \<open>trunk_le1\<close>).\<close>

lemma trunk_le0:
  assumes "M \<in> T_PS" "a \<le> b" "b \<le> TrMax M"
  shows "leR M 0 a b"
  using m_le1_imp_le0[OF trunk_le1[OF assms]] .

text \<open>For \<open>k < IdxSum Q ! (length Q)\<close> there is a unique block index \<open>J\<close> with
  \<open>IdxSum Q ! J \<le> k < IdxSum Q ! (J + 1)\<close>.\<close>

lemma idxsum_locate:
  assumes "k < IdxSum Q ! (length Q)"
  shows "\<exists>J < length Q. IdxSum Q ! J \<le> k \<and> k < IdxSum Q ! (J + 1)"
proof -
  let ?S = "{J. J \<le> length Q \<and> IdxSum Q ! J \<le> k}"
  have z: "IdxSum Q ! 0 = 0" by (simp add: idxsum_nth)
  hence z0: "0 \<in> ?S" by simp
  have fin: "finite ?S" by (auto intro: finite_subset[of ?S "{..length Q}"])
  have ne: "?S \<noteq> {}" using z0 by blast
  let ?J = "Max ?S"
  have inS: "?J \<in> ?S" using fin ne by (rule Max_in)
  hence Jle: "?J \<le> length Q" and JIdx: "IdxSum Q ! ?J \<le> k" by auto
  have Jlt: "?J < length Q"
  proof (cases "?J = length Q")
    case True
    hence "IdxSum Q ! (length Q) \<le> k" using JIdx by simp
    thus ?thesis using assms by simp
  next
    case False thus ?thesis using Jle by simp
  qed
  have "k < IdxSum Q ! (?J + 1)"
  proof (rule ccontr)
    assume "\<not> k < IdxSum Q ! (?J + 1)"
    hence "IdxSum Q ! (?J + 1) \<le> k" by simp
    hence "?J + 1 \<in> ?S" using Jlt by simp
    hence "?J + 1 \<le> ?J" by (rule Max_ge[OF fin])
    thus False by simp
  qed
  thus ?thesis using Jlt JIdx by blast
qed

text \<open>Within a branch component, the left end is a row-0 ancestor of every later
  index of that component (translated back to \<open>M\<close>).  For \<open>TrMax M < k \<le> Lng M - 1\<close>
  this yields a branch index \<open>J\<close> with \<open>leR M 0 (FirstNodes M ! J) k\<close>.\<close>

lemma branch_component_le0:
  assumes M: "M \<in> PT_PS" and ktr: "TrMax M < k" and kL: "k \<le> Lng M - 1"
  shows "\<exists>J < length (Br M). leR M 0 (FirstNodes M ! J) k"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
  have trlt: "TrMax M < Lng M - 1" using ktr kL by linarith
  let ?N = "seg M (TrMax M + 1) (Lng M - 1)"
  have brQ: "Br M = P ?N" using trlt by (simp add: Br_def)
  have NL: "Lng ?N = Lng M - 1 - TrMax M" using trlt by simp
  have NLpos: "Lng ?N > 0" using trlt by simp
  have Nne: "?N \<noteq> []" using NLpos length_greater_0_conv by blast
  have NT: "?N \<in> T_PS" using Nne by (simp add: T_PS_def)
  have LMlt: "Lng M - 1 < Lng M" using trlt by linarith
  let ?Q = "P ?N"
  let ?kp = "k - (TrMax M + 1)"
  have kpN: "?kp < Lng ?N" using ktr kL NL by linarith
  \<comment> \<open>\<open>IdxSum ?Q ! (length ?Q) = Lng ?N\<close>\<close>
  have total: "IdxSum ?Q ! (length ?Q) = Lng ?N"
  proof -
    have "IdxSum ?Q ! (length ?Q) = sum_list (map length (take (length ?Q) ?Q))"
      by (simp add: idxsum_nth)
    also have "\<dots> = sum_list (map length ?Q)" by simp
    also have "\<dots> = length (concat ?Q)" by (simp add: length_concat)
    also have "concat ?Q = ?N" by (rule idxsum_concat_P)
    finally show ?thesis by simp
  qed
  have kplt: "?kp < IdxSum ?Q ! (length ?Q)" using kpN total by simp
  obtain J where J: "J < length ?Q" "IdxSum ?Q ! J \<le> ?kp"
    "?kp < IdxSum ?Q ! (J + 1)"
    using idxsum_locate[OF kplt] by blast
  let ?a = "IdxSum ?Q ! J"
  let ?b = "IdxSum ?Q ! (J + 1) - 1"
  have Jle: "J \<le> Lng ?Q - 1" using J(1) by simp
  have comp: "?Q ! J = seg ?N ?a ?b" by (rule m_6_4_P_IdxSum[OF NT Jle])
  have lenpos: "0 < Lng (?Q ! J)" by (rule idxsum_P_component_nonempty[OF NT J(1)])
  have diff: "IdxSum ?Q ! (J + 1) = ?a + length (?Q ! J)" by (rule idxsum_diff[OF J(1)])
  have bge: "?kp \<le> ?b" using J(3) diff lenpos by linarith
  \<comment> \<open>row-0 ancestry from the component's left end to \<open>?kp\<close>, inside \<open>?N\<close>\<close>
  have leNa: "leR ?N 0 ?a ?kp"
  proof (cases "?a = ?kp")
    case True
    have aN: "?a < Lng ?N" using J(2) kpN by simp
    thus ?thesis using True by (simp add: leR_def le0_def)
  next
    case False
    with J(2) have altkp: "?a < ?kp" by simp
    let ?C = "?Q ! J"
    have CinP: "?C \<in> set ?Q" using J(1) by (rule nth_mem)
    have Czm: "zeroT ?C \<or> monoT ?C" using m_6_2_P_components_1[OF NT] CinP by blast
    have aN: "?a < Lng ?N" using J(2) kpN by simp
    have bN: "?b < Lng ?N"
    proof -
      have "IdxSum ?Q ! (J + 1) \<le> IdxSum ?Q ! (length ?Q)"
        by (rule idxsum_mono[OF _ order.refl]) (use J(1) in simp)
      hence "IdxSum ?Q ! (J + 1) \<le> Lng ?N" using total by simp
      thus ?thesis using NLpos by linarith
    qed
    \<comment> \<open>local position \<open>p = ?kp - ?a\<close> inside the component \<open>?C = seg ?N ?a ?b\<close>\<close>
    let ?p = "?kp - ?a"
    have ppos: "0 < ?p" using altkp by simp
    have CL: "Lng ?C = Suc ?b - ?a" using comp by simp
    have pb: "?p \<le> Lng ?C - 1" using bge CL altkp J(2) by linarith
    have Cgt1: "Lng ?C > 1" using ppos pb by linarith
    \<comment> \<open>so \<open>?C\<close> is monoT (not zeroT, since \<open>Lng > 1\<close>)\<close>
    have Cmono: "monoT ?C" using Czm Cgt1 by (auto simp: zeroT_def)
    have leC: "leR ?C 0 0 (Lng ?C - 1)" using Cmono by (simp add: monoT_def)
    have CTPS: "?C \<in> T_PS" using Cgt1 by (cases ?C) (auto simp: T_PS_def)
    have le0I: "(0::nat) \<le> ?p" by simp
    have leCp: "leR ?C 0 0 ?p"
      by (rule m_5_1_ancestor_tree_1[OF CTPS leC le0I pb])
    \<comment> \<open>translate component-le0 to \<open>?N\<close>-le0\<close>
    have le0C: "le0 ?C 0 ?p" using leCp by (simp add: leR_def)
    have aux: "le0 (seg ?N ?a ?b) 0 ?p = le0 ?N (?a + 0) (?a + ?p)"
    proof (rule adm_le0_seg)
      show "?b < Lng ?N" using bN .
      show "0 \<le> ?b - ?a" by simp
      show "?p \<le> ?b - ?a" using pb CL by simp
      show "?a \<le> ?b" using altkp bge by linarith
    qed
    have "le0 ?N ?a (?a + ?p)" using le0C comp aux by simp
    moreover have "?a + ?p = ?kp" using altkp J(2) by simp
    ultimately show ?thesis by (simp add: leR_def)
  qed
  \<comment> \<open>translate \<open>?N\<close>-le0 to \<open>M\<close>-le0\<close>
  have leMa: "leR M 0 (TrMax M + 1 + ?a) (TrMax M + 1 + ?kp)"
  proof -
    have le0N: "le0 ?N ?a ?kp" using leNa by (simp add: leR_def)
    have aN: "?a \<le> Lng ?N - 1" using J(2) kpN by linarith
    have eq: "le0 ?N ?a ?kp = le0 M (TrMax M + 1 + ?a) (TrMax M + 1 + ?kp)"
    proof (rule adm_le0_seg)
      show "Lng M - 1 < Lng M" using LMlt .
      show "?a \<le> Lng M - 1 - (TrMax M + 1)" using aN NL by simp
      show "?kp \<le> Lng M - 1 - (TrMax M + 1)" using kpN NL by simp
      show "TrMax M + 1 \<le> Lng M - 1" using trlt by simp
    qed
    have "le0 M (TrMax M + 1 + ?a) (TrMax M + 1 + ?kp)" using le0N eq by simp
    thus ?thesis by (simp add: leR_def)
  qed
  have JBr: "J < length (Br M)" using J(1) brQ by simp
  have fn: "FirstNodes M ! J = TrMax M + 1 + ?a" using FirstNodes_nth[OF JBr] brQ by simp
  have kk: "TrMax M + 1 + ?kp = k" using ktr by simp
  have "leR M 0 (FirstNodes M ! J) k" using leMa fn kk by simp
  thus ?thesis using JBr by blast
qed

text \<open>§6.5 branch-3b BC0, PIECE 2 (into-block row-0 edge).  Each branch block of
  \<open>Red M\<close> is, as a sub-list, a contiguous segment \<open>seg (Red M) bs be\<close> that is
  \<open>monoT\<close> (or \<open>zeroT\<close>); the block left-end is therefore a row-0 ancestor of every
  later index of the SAME block, lifted back to \<open>Red M\<close>.  Stated generally for a
  \<open>monoT\<close> segment of any \<open>T_PS\<close> sequence \<open>R\<close>: this is the part of branch-3b BC0
  that lives inside a single block (no inter-block reasoning).  The block-equals-
  segment fact and monotonicity are supplied at the use-site from the \<open>Red\<close>
  recursion (per-block IH: \<open>monoT (Red N_J)\<close>, \<open>IncrFirst\<close> preserves \<open>monoT\<close> and
  \<open>le0\<close>).  Empirically TRUE 70037/70037 (rank\<le>5), validated at rank\<ge>12.\<close>

lemma le0_monoT_seg_into_list:
  assumes R: "R \<in> T_PS"
    and seg_mono: "monoT (seg R bs be)"
    and order: "bs \<le> p" "p \<le> be" and beL: "be < Lng R"
  shows "le0 R bs p"
proof -
  let ?S = "seg R bs be"
  have bsbe: "bs \<le> be" using order by linarith
  have SL: "Lng ?S = Suc be - bs" by (simp only: Lng_seg)
  have SLpos: "Lng ?S > 0" using SL bsbe by linarith
  have Sne: "?S \<noteq> []" using SLpos by force
  have ST: "?S \<in> T_PS" using Sne by (simp add: T_PS_def)
  \<comment> \<open>mono gives the left-end as row-0 ancestor of the segment's last index\<close>
  have leLast: "leR ?S 0 0 (Lng ?S - 1)" using seg_mono by (simp add: monoT_def)
  have pbs: "p - bs \<le> Lng ?S - 1" using order SL by linarith
  have z: "(0::nat) \<le> p - bs" by simp
  have leP: "leR ?S 0 0 (p - bs)"
    by (rule m_5_1_ancestor_tree_1[OF ST leLast z pbs])
  have le0S: "le0 ?S 0 (p - bs)" using leP by (simp add: leR_def)
  \<comment> \<open>lift segment-le0 to \<open>R\<close>-le0 via @{thm [source] adm_le0_seg}\<close>
  have transfer: "le0 ?S 0 (p - bs) = le0 R (bs + 0) (bs + (p - bs))"
  proof (rule adm_le0_seg)
    show "be < Lng R" using beL .
    show "(0::nat) \<le> be - bs" by simp
    show "p - bs \<le> be - bs" using order by simp
    show "bs \<le> be" using bsbe .
  qed
  have "le0 R bs p" using le0S transfer order by simp
  thus ?thesis .
qed

text \<open>Core of \<open>m_6_4_mono_slice\<close>: for \<open>j0'\<close> a (weak) ancestor of the last joint,
  every index \<open>k\<close> with \<open>j0' < k \<le> Lng M - 1\<close> is a row-0 descendant of \<open>j0'\<close>.\<close>

lemma slice_le0_to_index:
  assumes M: "M \<in> PT_PS" and brne: "Br M \<noteq> []"
    and j0le: "j0' \<le> Joints M ! (Lng (Br M) - 1)"
    and lt: "j0' < k" and kL: "k \<le> Lng M - 1"
  shows "leR M 0 j0' k"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  let ?last = "Lng (Br M) - 1"
  have lastL: "?last < Lng (Br M)" using brne by (cases "Br M") auto
  \<comment> \<open>the last joint is in the trunk\<close>
  have lastTr: "Joints M ! ?last \<le> TrMax M"
    using m_6_4_FirstNodes_TrMax_Joints[OF M lastL] by simp
  have j0Tr: "j0' \<le> TrMax M" using j0le lastTr by simp
  show ?thesis
  proof (cases "k \<le> TrMax M")
    case True
    \<comment> \<open>Case A: \<open>k\<close> is in the trunk.\<close>
    show ?thesis by (rule trunk_le0[OF MT less_imp_le_nat[OF lt] True])
  next
    case False
    \<comment> \<open>Case B: \<open>k\<close> is in a branch component.\<close>
    hence ktr: "TrMax M < k" by simp
    obtain J where JBr: "J < length (Br M)"
      and leFNk: "leR M 0 (FirstNodes M ! J) k"
      using branch_component_le0[OF M ktr kL] by blast
    \<comment> \<open>\<open>nextR M 0 (Joints M ! J) (FirstNodes M ! J)\<close>\<close>
    have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
    have trne: "TrMax M \<noteq> Lng M - 1"
    proof
      assume "TrMax M = Lng M - 1"
      hence "Br M = []" by (simp add: Br_def)
      with brne show False by simp
    qed
    with tb have trlt: "TrMax M < Lng M - 1" by linarith
    let ?N = "seg M (TrMax M + 1) (Lng M - 1)"
    have brQ: "Br M = P ?N" using trne by (simp add: Br_def)
    have JQ: "J \<le> Lng (P ?N) - 1" using JBr brQ by (cases "P ?N") auto
    have hp: "hasParent M 0 (TrMax M + 1 + IdxSum (P ?N) ! J)"
      using m_6_4_mono_slice_next[OF M _ _ JQ] trlt by auto
    have fnJ: "TrMax M + 1 + IdxSum (P ?N) ! J = FirstNodes M ! J"
      using FirstNodes_nth[OF JBr] brQ by simp
    have hpf: "hasParent M 0 (FirstNodes M ! J)" using hp fnJ by simp
    have aJ_eq: "Joints M ! J = parent M 0 (FirstNodes M ! J)" by (rule Joints_nth[OF JBr])
    have nxJ: "nextR M 0 (Joints M ! J) (FirstNodes M ! J)"
    proof -
      have "\<exists>!j0. nextR M 0 j0 (FirstNodes M ! J)" using hpf by (simp add: hasParent_def)
      hence "nextR M 0 (THE j0. nextR M 0 j0 (FirstNodes M ! J)) (FirstNodes M ! J)"
        by (rule theI')
      thus ?thesis using aJ_eq by (simp add: parent_def)
    qed
    \<comment> \<open>\<open>Joints M ! J \<le> TrMax M\<close> and \<open>Joints M ! ?last \<le> Joints M ! J\<close>\<close>
    have aJTr: "Joints M ! J \<le> TrMax M"
      using m_6_4_FirstNodes_TrMax_Joints[OF M JBr] by simp
    have JleLast: "J \<le> ?last" using JBr by simp
    have lastLeaJ: "Joints M ! ?last \<le> Joints M ! J"
    proof (cases "J = ?last")
      case True thus ?thesis by simp
    next
      case False
      with JleLast have "J < ?last" by simp
      thus ?thesis
        using m_6_4_FirstNodes_Joints_mono_aux[OF M _ lastL] by simp
    qed
    have j0leaJ: "j0' \<le> Joints M ! J" using j0le lastLeaJ by simp
    \<comment> \<open>chain \<open>j0' \<le> Joints!J <\<^sup>Next FirstNodes!J \<le> k\<close>\<close>
    have le1: "leR M 0 j0' (Joints M ! J)"
      by (rule trunk_le0[OF MT j0leaJ aJTr])
    have leFN: "leR M 0 (Joints M ! J) (FirstNodes M ! J)"
      using nxJ by (auto simp: nextR_def leR_def le0_def nextrel0_def)
    have "le0 M j0' (FirstNodes M ! J)"
      using le0_trans[of M j0' "Joints M ! J" "FirstNodes M ! J"]
            le1 leFN by (simp add: leR_def)
    hence "le0 M j0' k"
      using le0_trans[of M j0' "FirstNodes M ! J" k] leFNk by (simp add: leR_def)
    thus ?thesis by (simp add: leR_def)
  qed
qed

end
