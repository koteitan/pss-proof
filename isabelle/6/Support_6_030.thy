theory Support_6_030
  imports Frontier_6_048
begin

text \<open>m (§6.6, L4): \<open>P\<close>-stability of reducedness — if \<open>M\<close> is reduced
  (\<open>Red M = M\<close>) then every \<open>P\<close>-block is itself reduced.  Discharges the
  forward foundation \<open>p_6_6_Red_P_stable\<close>.

  Route: when \<open>M\<close> is multi, the \<open>Red\<close> multiT branch gives
  \<open>Red M = concat (map Red (P M))\<close>; together with
  \<open>M = Red M = concat (P M)\<close> (@{thm [source] idxsum_concat_P}), the two
  concatenations agree.  Each block lies in \<open>T_PS\<close> (nonempty), so
  @{thm [source] m_6_5_Lng_Red} gives \<open>Lng (Red B) = Lng B\<close>, matching the
  block-length profiles; @{thm [source] concat_eq_of_map_length_eq} then forces
  \<open>map Red (P M) = P M\<close> blockwise.  When \<open>M\<close> is not multi, \<open>P M = [M]\<close> and the
  only block is \<open>M\<close> itself, which is reduced by hypothesis.\<close>

lemma m_6_6_Red_P_stable:
  assumes M: "M \<in> T_PS" and red: "Red M = M" and J: "J < Lng (P M)"
  shows "Red (P M ! J) = P M ! J"
proof (cases "multiT M")
  case False
  \<comment> \<open>Non-multi: \<open>P M = [M]\<close>, so the only block is \<open>M\<close> itself.\<close>
  have pm: "P M = [M]" using False by (subst P.simps) simp
  have J0: "J = 0" using J pm by simp
  show ?thesis using pm J0 red by simp
next
  case True
  have Mne: "M \<noteq> []" using M by (simp add: T_PS_def)
  have nz: "\<not> zeroT M" using True by (simp add: multiT_def)
  have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF M])
  \<comment> \<open>multiT branch of \<open>Red\<close>.\<close>
  have rM: "Red M = concat (map Red (P M))"
    using Red.psimps[OF domM] nz True by simp
  \<comment> \<open>\<open>M = concat (P M)\<close> by §6.4.\<close>
  have concP: "concat (P M) = M" by (rule idxsum_concat_P)
  \<comment> \<open>The two concatenations agree (both \<open>= M\<close>).\<close>
  have ceq: "concat (map Red (P M)) = concat (P M)"
    using rM red concP by simp
  \<comment> \<open>Each block is in \<open>T_PS\<close> (nonempty), so its \<open>Red\<close> preserves length.\<close>
  have step: "map (length \<circ> Red) (P M) = map length (P M)"
  proof (rule map_cong[OF refl])
    fix B0 assume B0: "B0 \<in> set (P M)"
    have B0T: "B0 \<in> T_PS" using P_blocks_nonempty[OF Mne] B0
      by (auto simp: T_PS_def)
    have "length (Red B0) = length B0" using m_6_5_Lng_Red[OF B0T] by simp
    thus "(length \<circ> Red) B0 = length B0" by simp
  qed
  have leneq: "map length (map Red (P M)) = map length (P M)"
    by (simp only: map_map step)
  have blockeq: "map Red (P M) = P M"
    by (rule concat_eq_of_map_length_eq[OF ceq leneq])
  have "Red (P M ! J) = (map Red (P M)) ! J"
    using J by simp
  also have "\<dots> = P M ! J" by (simp only: blockeq)
  finally show ?thesis .
qed


(* ===== keystone foundation block from workflow kf-diag ===== *)
text \<open>L5 (§6.6 RedCondA core-trunk diagonal pinning).  On the core-trunk branch
  — \<open>monoT M\<close>, core endpoints \<open>M\<^bsub>0,0\<^esub>=M\<^bsub>1,0\<^esub>=0\<close>, and the trunk reaching the last
  column (\<open>TrMax M = Lng M - 1\<close>) — \<open>RedCondA M\<close> forces \<open>M\<close> to be the full diagonal
  \<open>((0,0),(1,1),\<dots>,(L-1,L-1))\<close>.

  Route: \<open>m_6_6_condAB_coeff\<close> gives \<open>M\<^bsub>0,j\<^esub> \<le> j\<close>.  \<open>TrMax M = Lng M - 1\<close> means each
  consecutive trunk step \<open>(1,j') <\<^bsub>M\<^esub>\<^sup>Next (1,j'+1)\<close> holds (\<open>TrMax_trunk_step\<close>); its
  embedded \<open>\<le>\<^sub>M\<close>-row-0 datum collapses (consecutive indices) to \<open>nextrel0 M j' (j'+1)\<close>,
  whence both rows strictly increase along the trunk.  With the core endpoints this
  pins \<open>M\<^bsub>0,j\<^esub> = j\<close> and \<open>M\<^bsub>1,j\<^esub> \<ge> j\<close>.  Once row 0 is the index, \<open>\<le>\<^sub>M\<close>(row 0) is the
  index order, so the row-1 parent of \<open>j\<close> is unique (\<open>= j-1\<close>); RedCondA(row 1) then
  forces \<open>M\<^bsub>1,j\<^esub> = M\<^bsub>1,j-1\<^esub>+1\<close>, pinning \<open>M\<^bsub>1,j\<^esub> = j\<close>.  Extensionality (\<open>nth_equalityI\<close>)
  concludes \<open>M = diagSeq 0 (Lng M - 1)\<close>.\<close>

lemma m_6_6_RedCondA_core_diag:
  assumes MT: "M \<in> T_PS" and mono: "monoT M"
    and e00: "entry M 0 0 = 0" and e10: "entry M 1 0 = 0"
    and trmax: "TrMax M = Lng M - 1"
    and condA: "RedCondA M"
  shows "M = diagSeq 0 (Lng M - 1)"
proof -
  have LMpos: "0 < Lng M" using MT by (cases M) (auto simp: T_PS_def)
  \<comment> \<open>Trunk step holds for every \<open>j' < Lng M - 1\<close>.\<close>
  have trunk_step: "\<And>j'. j' < Lng M - 1 \<Longrightarrow> nextR M 1 j' (j' + 1)"
  proof -
    fix j' assume "j' < Lng M - 1"
    hence "j' < TrMax M" using trmax by simp
    thus "nextR M 1 j' (j' + 1)" by (rule TrMax_trunk_step[OF MT])
  qed
  \<comment> \<open>Embedded \<open>\<le>\<^sub>M\<close>(row 0) of a trunk step collapses to a single \<open>nextrel0\<close> step.\<close>
  have nr0_step: "\<And>j'. j' < Lng M - 1 \<Longrightarrow> nextrel0 M j' (j' + 1)"
  proof -
    fix j' assume hj: "j' < Lng M - 1"
    have "nextrel1 M j' (j' + 1)" using trunk_step[OF hj] by (simp add: nextR_def)
    hence le0: "le0 M j' (j' + 1)" by (simp add: nextrel1_def)
    hence rt: "(nextrel0 M)\<^sup>*\<^sup>* j' (j' + 1)" by (simp add: le0_def)
    from rt show "nextrel0 M j' (j' + 1)"
    proof (cases rule: rtranclp.cases)
      case rtrancl_refl thus ?thesis by simp
    next
      case (rtrancl_into_rtrancl b)
      have rtb: "(nextrel0 M)\<^sup>*\<^sup>* j' b" using rtrancl_into_rtrancl by simp
      have laststep: "nextrel0 M b (j' + 1)" using rtrancl_into_rtrancl by simp
      have "j' \<le> b" using rtb by (rule nextrel0_rtrancl_mono)
      moreover have "b < j' + 1" using laststep by (simp add: nextrel0_def)
      ultimately have "b = j'" by linarith
      thus ?thesis using laststep by simp
    qed
  qed
  \<comment> \<open>Both rows strictly increase along the trunk.\<close>
  have inc0: "\<And>j'. j' < Lng M - 1 \<Longrightarrow> entry M 0 j' < entry M 0 (j' + 1)"
    using nr0_step by (simp add: nextrel0_def)
  have inc1: "\<And>j'. j' < Lng M - 1 \<Longrightarrow> entry M 1 j' < entry M 1 (j' + 1)"
  proof -
    fix j' assume hj: "j' < Lng M - 1"
    have "nextrel1 M j' (j' + 1)" using trunk_step[OF hj] by (simp add: nextR_def)
    thus "entry M 1 j' < entry M 1 (j' + 1)" by (simp add: nextrel1_def)
  qed
  \<comment> \<open>Lower bound: a from-zero strictly increasing nat sequence is \<open>\<ge> j\<close>.\<close>
  have ge_idx: "\<And>i j. i \<le> 1 \<Longrightarrow> j < Lng M \<Longrightarrow> entry M i 0 = 0 \<Longrightarrow>
      (\<And>j'. j' < Lng M - 1 \<Longrightarrow> entry M i j' < entry M i (j' + 1)) \<Longrightarrow> j \<le> entry M i j"
  proof -
    fix i j assume hi: "i \<le> 1" and hj: "j < Lng M" and base: "entry M i 0 = 0"
      and step: "\<And>j'. j' < Lng M - 1 \<Longrightarrow> entry M i j' < entry M i (j' + 1)"
    from hj show "j \<le> entry M i j"
    proof (induction j)
      case 0 thus ?case by simp
    next
      case (Suc n)
      have nlt: "n < Lng M - 1" using Suc.prems by linarith
      have "n \<le> entry M i n" using Suc.IH nlt by linarith
      moreover have "entry M i n < entry M i (Suc n)" using step[OF nlt] by simp
      ultimately show ?case by simp
    qed
  qed
  \<comment> \<open>Row 0 upper bound from \<open>m_6_6_condAB_coeff\<close>.\<close>
  have le0_idx: "\<And>j. j \<le> Lng M - 1 \<Longrightarrow> entry M 0 j \<le> j"
    using m_6_6_condAB_coeff[OF MT e00 e10 condA] by blast
  \<comment> \<open>Row 0 is the index.\<close>
  have row0: "\<And>j. j < Lng M \<Longrightarrow> entry M 0 j = j"
  proof -
    fix j assume hj: "j < Lng M"
    have "j \<le> entry M 0 j" using ge_idx[OF _ hj e00] inc0 by simp
    moreover have "entry M 0 j \<le> j" using le0_idx hj by simp
    ultimately show "entry M 0 j = j" by simp
  qed
  \<comment> \<open>With row 0 = index, \<open>nextrel0\<close> is exactly the consecutive step.\<close>
  have nr0_iff: "\<And>a b. b < Lng M \<Longrightarrow> nextrel0 M a b \<longleftrightarrow> b = a + 1"
  proof
    fix a b assume bL: "b < Lng M"
    assume "nextrel0 M a b"
    hence ab: "a < b" and amin: "\<forall>k. a < k \<and> k < b \<longrightarrow> entry M 0 k \<ge> entry M 0 b"
      by (auto simp: nextrel0_def)
    show "b = a + 1"
    proof (rule ccontr)
      assume "b \<noteq> a + 1"
      hence "a + 1 < b" using ab by linarith
      hence "entry M 0 (a + 1) \<ge> entry M 0 b" using amin by simp
      moreover have "entry M 0 (a + 1) = a + 1" using row0 \<open>a + 1 < b\<close> bL by simp
      moreover have "entry M 0 b = b" using row0 bL by simp
      ultimately show False using \<open>a + 1 < b\<close> by simp
    qed
  next
    fix a b assume bL: "b < Lng M" assume "b = a + 1"
    hence aL: "a < Lng M" and aL1: "a < b" using bL by simp_all
    have "a < Lng M - 1" using \<open>b = a + 1\<close> bL by linarith
    have e0: "entry M 0 a < entry M 0 b"
      using row0[OF aL] row0[OF bL] \<open>b = a + 1\<close> by simp
    have amin: "\<forall>k. a < k \<and> k < b \<longrightarrow> entry M 0 k \<ge> entry M 0 b"
      using \<open>b = a + 1\<close> by auto
    show "nextrel0 M a b"
      unfolding nextrel0_def using aL bL aL1 e0 amin by blast
  qed
  \<comment> \<open>Hence row-0 reachability \<open>le0\<close> is the index order.\<close>
  have le0_order: "\<And>a b. b < Lng M \<Longrightarrow> le0 M a b \<Longrightarrow> a \<le> b"
  proof -
    fix a b assume "b < Lng M" "le0 M a b"
    hence "(nextrel0 M)\<^sup>*\<^sup>* a b" by (simp add: le0_def)
    thus "a \<le> b" by (rule nextrel0_rtrancl_mono)
  qed
  \<comment> \<open>Row-1 parent of \<open>j\<close> is unique once \<open>le0\<close> is the index order.\<close>
  have par1_unique: "\<And>a c k. k < Lng M \<Longrightarrow> nextrel1 M a k \<Longrightarrow> nextrel1 M c k \<Longrightarrow> a = c"
  proof -
    fix a c k assume kL: "k < Lng M" and na: "nextrel1 M a k" and nc: "nextrel1 M c k"
    have key: "\<And>x y. nextrel1 M x k \<Longrightarrow> nextrel1 M y k \<Longrightarrow> x < y \<Longrightarrow> False"
    proof -
      fix x y assume nx: "nextrel1 M x k" and ny: "nextrel1 M y k" and xy: "x < y"
      have yk: "y < k" using ny by (simp add: nextrel1_def)
      have ymin: "\<forall>j. x < j \<and> le0 M j k \<longrightarrow> entry M 1 j \<ge> entry M 1 k"
        using nx by (simp add: nextrel1_def)
      have leyk: "le0 M y k" using ny by (simp add: nextrel1_def)
      have "entry M 1 y \<ge> entry M 1 k" using ymin xy leyk by simp
      moreover have "entry M 1 y < entry M 1 k" using ny by (simp add: nextrel1_def)
      ultimately show False by simp
    qed
    show "a = c"
    proof (rule ccontr)
      assume "a \<noteq> c"
      then consider "a < c" | "c < a" by linarith
      thus False using key[OF na nc] key[OF nc na] by cases simp_all
    qed
  qed
  \<comment> \<open>Each trunk column \<open>j\<close> (\<open>0 < j \<le> Lng M - 1\<close>) has a row-1 parent \<open>= j - 1\<close>.\<close>
  have haspar1: "\<And>j. 0 < j \<Longrightarrow> j \<le> Lng M - 1 \<Longrightarrow> hasParent M 1 j"
  proof -
    fix j assume jpos: "0 < j" and jle: "j \<le> Lng M - 1"
    have jm1: "j - 1 < Lng M - 1" using jpos jle by linarith
    have step: "nextR M 1 (j - 1) j" using trunk_step[OF jm1] jpos by simp
    show "hasParent M 1 j"
      unfolding hasParent_def
    proof (rule ex1I[of _ "j - 1"])
      show "nextR M 1 (j - 1) j" by (rule step)
    next
      fix c assume "nextR M 1 c j"
      hence "nextrel1 M c j" by (simp add: nextR_def)
      moreover have "nextrel1 M (j - 1) j" using step by (simp add: nextR_def)
      moreover have "j < Lng M" using jle LMpos by linarith
      ultimately show "c = j - 1" using par1_unique by blast
    qed
  qed
  have par1_val: "\<And>j. 0 < j \<Longrightarrow> j \<le> Lng M - 1 \<Longrightarrow> parent M 1 j = j - 1"
  proof -
    fix j assume jpos: "0 < j" and jle: "j \<le> Lng M - 1"
    have jm1: "j - 1 < Lng M - 1" using jpos jle by linarith
    have step: "nextR M 1 (j - 1) j" using trunk_step[OF jm1] jpos by simp
    have ex1: "\<exists>!j0. nextR M 1 j0 j" using haspar1[OF jpos jle] by (simp add: hasParent_def)
    show "parent M 1 j = j - 1"
      unfolding parent_def using ex1 step by (rule the1_equality)
  qed
  \<comment> \<open>RedCondA(row 1) then pins row 1 to the index.\<close>
  have condA1: "\<And>j. j \<le> Lng M - 1 \<Longrightarrow> hasParent M 1 j \<Longrightarrow>
      entry M 1 (parent M 1 j) + 1 = entry M 1 j"
    using condA unfolding RedCondA_def by simp
  have row1: "\<And>j. j < Lng M \<Longrightarrow> entry M 1 j = j"
  proof -
    fix j assume hj: "j < Lng M"
    from hj show "entry M 1 j = j"
    proof (induction j)
      case 0 thus ?case using e10 by simp
    next
      case (Suc n)
      have nle: "Suc n \<le> Lng M - 1" using Suc.prems by linarith
      have npos: "0 < Suc n" by simp
      have hp: "hasParent M 1 (Suc n)" by (rule haspar1[OF npos nle])
      have pv: "parent M 1 (Suc n) = n" using par1_val[OF npos nle] by simp
      have "entry M 1 n + 1 = entry M 1 (Suc n)"
        using condA1[OF nle hp] pv by simp
      moreover have "entry M 1 n = n" using Suc.IH Suc.prems by simp
      ultimately show ?case by simp
    qed
  qed
  \<comment> \<open>Assemble: each pair is \<open>(j,j)\<close>, matching \<open>diagSeq 0 (Lng M - 1)\<close>.\<close>
  have pairs: "\<And>j. j < Lng M \<Longrightarrow> M ! j = (j, j)"
  proof -
    fix j assume hj: "j < Lng M"
    have "fst (M ! j) = j" using row0[OF hj] by (simp add: entry_def)
    moreover have "snd (M ! j) = j" using row1[OF hj] by (simp add: entry_def)
    ultimately show "M ! j = (j, j)" by (simp add: prod_eq_iff)
  qed
  have Ldiag: "Lng (diagSeq 0 (Lng M - 1)) = Lng M" using LMpos by simp
  show ?thesis
  proof (rule nth_equalityI)
    show "Lng M = Lng (diagSeq 0 (Lng M - 1))" using Ldiag by simp
  next
    fix j assume "j < Lng M"
    have dj: "j < Suc (Lng M - 1) - 0" using \<open>j < Lng M\<close> LMpos by simp
    have "M ! j = (j, j)" using pairs[OF \<open>j < Lng M\<close>] .
    also have "\<dots> = diagSeq 0 (Lng M - 1) ! j" using diagSeq_nth[OF dj] by simp
    finally show "M ! j = diagSeq 0 (Lng M - 1) ! j" .
  qed
qed

end
