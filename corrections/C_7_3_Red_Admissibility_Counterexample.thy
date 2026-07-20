theory C_7_3_Red_Admissibility_Counterexample
  imports "PSS_A.pss_mechanized"
begin

text \<open>Relocated proof material.  The declarations retain their original source order,
  and every relocated annotation is preserved below.  This theory is machine-checked
  outside the termination build tree.\<close>

lemma cexM_Lng [simp]: "Lng cexM = 5" by (simp add: cexM_def)

lemma cexM_TPS [simp]: "cexM \<in> T_PS" by (simp add: cexM_def T_PS_def)

lemma cexM_row0: "j < 5 \<Longrightarrow> entry cexM 0 j = j"
proof -
  assume "j < 5"
  then consider "j = 0" | "j = 1" | "j = 2" | "j = 3" | "j = 4" by linarith
  thus ?thesis by cases (simp_all add: cexM_def entry_def)
qed

lemma cexM_row1:
  "entry cexM 1 0 = 0" "entry cexM 1 1 = 6" "entry cexM 1 2 = 5"
  "entry cexM 1 3 = 3" "entry cexM 1 4 = 4"
  by (simp_all add: cexM_def entry_def)

text \<open>Row 0 of \<open>cexM\<close> is the identity, so \<open>le\<^sub>0\<close> is just the index order.\<close>

lemma cexM_le0I: "a \<le> b \<Longrightarrow> b < 5 \<Longrightarrow> le0 cexM a b"
proof -
  assume ab: "a \<le> b" and b: "b < 5"
  have "\<forall>j. a < j \<longrightarrow> j \<le> b \<longrightarrow> entry cexM 0 a < entry cexM 0 j"
  proof (intro allI impI)
    fix j assume j1: "a < j" and j2: "j \<le> b"
    have "a < 5" using ab b by simp
    moreover have "j < 5" using j2 b by simp
    ultimately show "entry cexM 0 a < entry cexM 0 j"
      using cexM_row0 j1 by simp
  qed
  thus ?thesis using y3w_le0_iff[of a b cexM] ab b by simp
qed

lemma cexM_le0D: "le0 cexM a b \<Longrightarrow> a \<le> b \<and> b < 5"
  using y3w_le0_bounds[of cexM a b] by simp

lemma cexM_nx1: "Suc j < 5 \<Longrightarrow> nextrel1 cexM j (Suc j)
                   \<longleftrightarrow> entry cexM 1 j < entry cexM 1 (Suc j)"
proof -
  assume s: "Suc j < 5"
  have "entry cexM 0 j < entry cexM 0 (Suc j)" using cexM_row0 s by simp
  thus ?thesis using y3w_nextrel1_adj[of j cexM] s by simp
qed

lemma cexM_monoT: "monoT cexM"
proof -
  have "le0 cexM 0 4" by (rule cexM_le0I) simp_all
  thus ?thesis by (simp add: monoT_def zeroT_def leR_def)
qed

lemma cexM_nmulti: "\<not> multiT cexM" using cexM_monoT by (simp add: multiT_def)
lemma cexM_nzero: "\<not> zeroT cexM" by (simp add: zeroT_def)
lemma cexM_PT: "cexM \<in> PT_PS" using cexM_monoT by (simp add: PT_PS_def)

subsection \<open>\<open>TrMax cexM = 1\<close>, and the branch data\<close>

lemma cexM_TrMax: "TrMax cexM = 1"
proof (rule TrMax_eqI_endpoint[OF cexM_TPS])
  fix j' :: nat assume "j' < 1"
  hence z: "j' = 0" by simp
  have "nextrel1 cexM 0 (Suc 0)" using cexM_nx1[of 0] cexM_row1 by simp
  thus "nextR cexM 1 j' (j' + 1)" using z by (simp add: nextR_def)
next
  have "\<not> nextrel1 cexM 1 (Suc 1)"
    using cexM_nx1[of 1] by (simp add: cexM_def entry_def)
  thus "1 = Lng cexM - 1 \<or> \<not> nextR cexM 1 1 (1 + 1)" by (simp add: nextR_def)
qed

lemma cexM_tail_monoT: "monoT [(2::nat,5::nat), (3,3), (4,4)]"
proof -
  let ?N = "[(2::nat,5::nat), (3,3), (4,4)]"
  have L: "Lng ?N = 3" by simp
  have r0: "\<And>j. j < 3 \<Longrightarrow> entry ?N 0 j = 2 + j"
  proof -
    fix j :: nat assume "j < 3"
    then consider "j = 0" | "j = 1" | "j = 2" by linarith
    thus "entry ?N 0 j = 2 + j" by cases (simp_all add: entry_def)
  qed
  have H: "\<forall>j. 0 < j \<longrightarrow> j \<le> 2 \<longrightarrow> entry ?N 0 0 < entry ?N 0 j"
    using r0 by auto
  have iff: "le0 ?N 0 2 \<longleftrightarrow> (\<forall>j. 0 < j \<longrightarrow> j \<le> 2 \<longrightarrow> entry ?N 0 0 < entry ?N 0 j)"
    by (rule y3w_le0_iff) (simp_all add: L)
  have le02: "le0 ?N 0 2" using iff H by blast
  have Lm: "Lng ?N - 1 = 2" using L by simp
  have leN: "le0 ?N 0 (Lng ?N - 1)" unfolding Lm by (rule le02)
  have nzN: "\<not> zeroT ?N" using L by (simp add: zeroT_def)
  show ?thesis using nzN leN by (simp add: monoT_def leR_def)
qed

lemma cexM_Br: "Br cexM = [[(2,5), (3,3), (4,4)]]"
proof -
  let ?N = "[(2::nat,5::nat), (3,3), (4,4)]"
  have tne: "TrMax cexM \<noteq> Lng cexM - 1" using cexM_TrMax by simp
  have NT: "?N \<in> T_PS" by (simp add: T_PS_def)
  have nm: "\<not> multiT ?N" using cexM_tail_monoT by (simp add: multiT_def)
  have b: "Br cexM = P (seg cexM (TrMax cexM + 1) (Lng cexM - 1))"
    using tne by (simp add: Br_def)
  have s: "seg cexM (TrMax cexM + 1) (Lng cexM - 1) = ?N"
    using cexM_TrMax by (simp add: cexM_def seg_def)
  have "Br cexM = P ?N" using b s by simp
  also have "\<dots> = [?N]" by (rule y3r_P_nonmulti[OF NT nm])
  finally show ?thesis .
qed

lemma cexM_LngBr [simp]: "Lng (Br cexM) = 1" using cexM_Br by simp

lemma cexM_FirstNodes: "FirstNodes cexM ! 0 = 2"
proof -
  have "FirstNodes cexM ! 0 = TrMax cexM + 1 + IdxSum (Br cexM) ! 0"
    by (rule FirstNodes_nth) (simp add: cexM_Br)
  also have "\<dots> = 2" using cexM_TrMax by (simp add: cexM_Br IdxSum_def)
  finally show ?thesis .
qed

lemma cexM_nx0_2: "nextrel0 cexM j 2 \<longleftrightarrow> j = 1"
proof
  assume H: "nextrel0 cexM j 2"
  hence jl: "j < 2" by (simp add: nextrel0_def)
  show "j = 1"
  proof (rule ccontr)
    assume "j \<noteq> 1"
    hence j0: "j = 0" using jl by simp
    have "entry cexM 0 1 \<ge> entry cexM 0 2" using H j0 by (simp add: nextrel0_def)
    thus False using cexM_row0[of 1] cexM_row0[of 2] by simp
  qed
next
  assume "j = 1"
  thus "nextrel0 cexM j 2"
    using cexM_row0[of 1] cexM_row0[of 2] by (simp add: nextrel0_def)
qed

lemma cexM_Joints: "Joints cexM ! 0 = 1"
proof -
  have "Joints cexM ! 0 = (THE j. nextR cexM 0 j (FirstNodes cexM ! 0))"
    by (simp add: Joints_def cexM_Br)
  also have "\<dots> = (THE j. nextrel0 cexM j 2)"
    using cexM_FirstNodes by (simp add: nextR_def)
  also have "\<dots> = 1" using cexM_nx0_2 by auto
  finally show ?thesis .
qed

lemma cexM_nx1_2: "nextrel1 cexM j 2 \<longleftrightarrow> j = 0"
proof
  assume H: "nextrel1 cexM j 2"
  hence jl: "j < 2" and lt: "entry cexM 1 j < entry cexM 1 2"
    by (simp_all add: nextrel1_def)
  show "j = 0"
  proof (rule ccontr)
    assume "j \<noteq> 0"
    hence "j = 1" using jl by simp
    thus False using lt cexM_row1 by simp
  qed
next
  assume j: "j = 0"
  have le02: "le0 cexM 0 2" by (rule cexM_le0I) simp_all
  have bet: "\<forall>k. 0 < k \<and> le0 cexM k 2 \<longrightarrow> entry cexM 1 k \<ge> entry cexM 1 2"
  proof (intro allI impI)
    fix k assume hk: "0 < k \<and> le0 cexM k 2"
    hence "k \<le> 2" using cexM_le0D by blast
    hence "k = 1 \<or> k = 2" using hk by linarith
    thus "entry cexM 1 k \<ge> entry cexM 1 2" using cexM_row1 by auto
  qed
  show "nextrel1 cexM j 2"
    unfolding nextrel1_def using j le02 bet cexM_row1 by simp
qed

lemma cexM_npJ: "npJ cexM 0 = 1"
proof -
  have b: "entry (Br cexM ! 0) 1 0 = 5" using cexM_Br by (simp add: entry_def)
  have "npJ cexM 0 = Suc (THE j. nextR cexM 1 j (FirstNodes cexM ! 0))"
    using b by (simp add: npJ_def)
  also have "\<dots> = Suc (THE j. nextrel1 cexM j 2)"
    using cexM_FirstNodes by (simp add: nextR_def)
  also have "\<dots> = 1" using cexM_nx1_2 by auto
  finally show ?thesis .
qed

lemma cexM_NJ: "NJ cexM 0 = [(2,1), (3,3), (4,4)]"
  using cexM_Joints cexM_npJ cexM_Br
  by (simp add: NJ_def cexM_def entry_def)

subsection \<open>Evaluating \<open>Red\<close>\<close>

text \<open>\<open>Red [(0,0),(3,1),(4,3),(5,4)] = diagSeq 0 3\<close>: a full trunk.\<close>

lemma cexM_redA: "Red [(0,0), (3,1), (4,3), (5,4)] = [(0,0), (1,1), (2,2), (3,3)]"
proof -
  let ?A = "[(0::nat,0::nat), (3,1), (4,3), (5,4)]"
  have AT: "?A \<in> T_PS" by (simp add: T_PS_def)
  have LA: "Lng ?A = 4" by simp
  have r0: "\<And>j. j < 4 \<Longrightarrow> entry ?A 0 j = (if j = 0 then 0 else 2 + j)"
  proof -
    fix j :: nat assume "j < 4"
    then consider "j = 0" | "j = 1" | "j = 2" | "j = 3" by linarith
    thus "entry ?A 0 j = (if j = 0 then 0 else 2 + j)"
      by cases (simp_all add: entry_def)
  qed
  have r1: "entry ?A 1 0 = 0" "entry ?A 1 1 = 1" "entry ?A 1 2 = 3" "entry ?A 1 3 = 4"
    by (simp_all add: entry_def)
  have le03: "le0 ?A 0 3"
  proof -
    have H: "\<forall>j. 0 < j \<longrightarrow> j \<le> 3 \<longrightarrow> entry ?A 0 0 < entry ?A 0 j" using r0 by auto
    have iff: "le0 ?A 0 3 \<longleftrightarrow> (\<forall>j. 0 < j \<longrightarrow> j \<le> 3 \<longrightarrow> entry ?A 0 0 < entry ?A 0 j)"
      by (rule y3w_le0_iff) (simp_all add: LA)
    show ?thesis using iff H by blast
  qed
  have LmA: "Lng ?A - 1 = 3" using LA by simp
  have leA: "le0 ?A 0 (Lng ?A - 1)" unfolding LmA by (rule le03)
  have nz: "\<not> zeroT ?A" by (simp add: zeroT_def)
  have mono: "monoT ?A" using nz leA by (simp add: monoT_def leR_def)
  have nmu: "\<not> multiT ?A" using mono by (simp add: multiT_def)
  have adj: "\<And>j. Suc j < 4 \<Longrightarrow> nextrel1 ?A j (Suc j)"
  proof -
    fix j :: nat assume s: "Suc j < 4"
    have e0: "entry ?A 0 j < entry ?A 0 (Suc j)" using r0 s by auto
    have e1: "entry ?A 1 j < entry ?A 1 (Suc j)"
    proof -
      from s consider "j = 0" | "j = 1" | "j = 2" by linarith
      thus ?thesis by cases (simp_all add: entry_def)
    qed
    show "nextrel1 ?A j (Suc j)" using y3w_nextrel1_adj[of j ?A] s e0 e1 by simp
  qed
  have TA: "TrMax ?A = 3"
  proof (rule TrMax_eqI_endpoint[OF AT])
    fix j' :: nat assume "j' < 3"
    thus "nextR ?A 1 j' (j' + 1)" using adj[of j'] by (simp add: nextR_def)
  next
    show "3 = Lng ?A - 1 \<or> \<not> nextR ?A 1 3 (3 + 1)" using LA by simp
  qed
  have dom: "Red_dom ?A" by (rule m_6_5_Red_welldef[OF AT])
  have c0: "entry ?A 0 0 = 0" by (simp add: entry_def)
  have c1: "entry ?A 1 0 = 0" by (simp add: entry_def)
  have "Red ?A = diagSeq 0 (0 + (Lng ?A - 1))"
    using Red.psimps[OF dom] nz nmu c0 c1 TA LA by (simp add: Let_def)
  also have "\<dots> = [(0,0), (1,1), (2,2), (3,3)]"
    by (simp add: diagSeq_def eval_nat_numeral)
  finally show ?thesis .
qed

text \<open>\<open>Red [(2,1),(3,3),(4,4)] = [(1,1),(2,2),(3,3)]\<close>: the \<open>m\<^sub>1\<^sub>0 > 0\<close> rebase.\<close>

lemma cexM_redNJ: "Red [(2,1), (3,3), (4,4)] = [(1,1), (2,2), (3,3)]"
proof -
  let ?B = "[(2::nat,1::nat), (3,3), (4,4)]"
  let ?A = "[(0::nat,0::nat), (3,1), (4,3), (5,4)]"
  let ?N = "[(0::nat,0::nat), (1,1), (2,2), (3,3)]"
  have BT: "?B \<in> T_PS" by (simp add: T_PS_def)
  have LB: "Lng ?B = 3" by simp
  have r0: "\<And>j. j < 3 \<Longrightarrow> entry ?B 0 j = 2 + j"
  proof -
    fix j :: nat assume "j < 3"
    then consider "j = 0" | "j = 1" | "j = 2" by linarith
    thus "entry ?B 0 j = 2 + j" by cases (simp_all add: entry_def)
  qed
  have le02: "le0 ?B 0 2"
  proof -
    have H: "\<forall>j. 0 < j \<longrightarrow> j \<le> 2 \<longrightarrow> entry ?B 0 0 < entry ?B 0 j" using r0 by auto
    have iff: "le0 ?B 0 2 \<longleftrightarrow> (\<forall>j. 0 < j \<longrightarrow> j \<le> 2 \<longrightarrow> entry ?B 0 0 < entry ?B 0 j)"
      by (rule y3w_le0_iff) (simp_all add: LB)
    show ?thesis using iff H by blast
  qed
  have LmB: "Lng ?B - 1 = 2" using LB by simp
  have leB: "le0 ?B 0 (Lng ?B - 1)" unfolding LmB by (rule le02)
  have nz: "\<not> zeroT ?B" by (simp add: zeroT_def)
  have mono: "monoT ?B" using nz leB by (simp add: monoT_def leR_def)
  have nmu: "\<not> multiT ?B" using mono by (simp add: multiT_def)
  have m00: "entry ?B 0 0 = 2" by (simp add: entry_def)
  have m10: "entry ?B 1 0 = 1" by (simp add: entry_def)
  have nc: "\<not> (entry ?B 0 0 = 0 \<and> entry ?B 1 0 = 0)" using m00 by simp
  have c1p: "0 < entry ?B 1 0" using m10 by simp
  have dom: "Red_dom ?B" by (rule m_6_5_Red_welldef[OF BT])
  \<comment> \<open>the argument of the recursive call\<close>
  have argeq: "diagSeq 0 (entry ?B 1 0 - 1) @ (IncrFirst ^^ entry ?B 1 0) ?B = ?A"
    using m10 by (simp add: diagSeq_def IncrFirst_def)
  have Neq: "Red (diagSeq 0 (entry ?B 1 0 - 1) @ (IncrFirst ^^ entry ?B 1 0) ?B) = ?N"
    unfolding argeq by (rule cexM_redA)
  have LN: "Lng ?N = 4" by simp
  have segN: "seg ?N 1 3 = [(1,1), (2,2), (3,3)]"
    by (simp add: seg_def eval_nat_numeral)
  have segPT: "seg ?N (entry ?B 1 0) (Lng ?N - 1) \<in> PT_PS"
  proof -
    let ?S = "[(1::nat,1::nat), (2,2), (3,3)]"
    have ST: "?S \<in> T_PS" by (simp add: T_PS_def)
    have s0: "\<And>j. j < 3 \<Longrightarrow> entry ?S 0 j = 1 + j"
    proof -
      fix j :: nat assume "j < 3"
      then consider "j = 0" | "j = 1" | "j = 2" by linarith
      thus "entry ?S 0 j = 1 + j" by cases (simp_all add: entry_def)
    qed
    have H: "\<forall>j. 0 < j \<longrightarrow> j \<le> 2 \<longrightarrow> entry ?S 0 0 < entry ?S 0 j" using s0 by auto
    have iff: "le0 ?S 0 2 \<longleftrightarrow> (\<forall>j. 0 < j \<longrightarrow> j \<le> 2 \<longrightarrow> entry ?S 0 0 < entry ?S 0 j)"
      by (rule y3w_le0_iff) simp_all
    have le2: "le0 ?S 0 2" using iff H by blast
    have LmS: "Lng ?S - 1 = 2" by simp
    have leS: "le0 ?S 0 (Lng ?S - 1)" unfolding LmS by (rule le2)
    have nzS: "\<not> zeroT ?S" by (simp add: zeroT_def)
    have monoS: "monoT ?S" using nzS leS by (simp add: monoT_def leR_def)
    have LNm: "Lng ?N - 1 = 3" using LN by simp
    have seq: "seg ?N (entry ?B 1 0) (Lng ?N - 1) = ?S"
      unfolding m10 LNm by (rule segN)
    show ?thesis unfolding seq using ST monoS by (simp add: PT_PS_def)
  qed
  have cond: "entry ?B 1 0 \<le> Lng ?N - 1 \<and> seg ?N (entry ?B 1 0) (Lng ?N - 1) \<in> PT_PS"
    using m10 LN segPT by simp
  have "Red ?B = map (\<lambda>j. (entry ?N 0 j - entry ?N 0 (entry ?B 1 0)
                              + entry ?N 1 (entry ?B 1 0), entry ?N 1 j))
                     [entry ?B 1 0..<Suc (Lng ?N - 1)]"
    using Red.psimps[OF dom] nz nmu nc c1p Neq cond by (simp add: Let_def)
  also have "\<dots> = [(1,1), (2,2), (3,3)]"
    using m10 LN by (simp add: entry_def eval_nat_numeral)
  finally show ?thesis .
qed

lemma cexM_Red: "Red cexM = [(0,0), (1,1), (2,1), (3,2), (4,3)]"
proof -
  have tne: "TrMax cexM \<noteq> Lng cexM - 1" using cexM_TrMax by simp
  have c0: "entry cexM 0 0 = 0" by (simp add: cexM_def entry_def)
  have c1: "entry cexM 1 0 = 0" by (simp add: cexM_def entry_def)
  have "Red cexM = diagSeq 0 (TrMax cexM)
          @ concat (map (\<lambda>J. (IncrFirst ^^ (Joints cexM ! J + 1 - npJ cexM J))
                                 (Red (NJ cexM J)))
                    [0..<Lng (Br cexM)])"
    by (rule d_Red_core_nontrunk_unfold[OF cexM_TPS cexM_nzero cexM_nmulti c0 c1 tne])
  also have "\<dots> = diagSeq 0 1 @ (IncrFirst ^^ 1) (Red (NJ cexM 0))"
    using cexM_TrMax cexM_Joints cexM_npJ by simp
  also have "\<dots> = diagSeq 0 1 @ (IncrFirst ^^ 1) [(1,1), (2,2), (3,3)]"
    using cexM_NJ cexM_redNJ by simp
  also have "\<dots> = [(0,0), (1,1), (2,1), (3,2), (4,3)]"
    by (simp add: diagSeq_def IncrFirst_def)
  finally show ?thesis .
qed

text \<open>\<open>Red cexM\<close> is already reduced (its only \<open>P\<close>-component, \<open>cexM\<close> itself, has a
  diagonal left end), so \<open>Red (Red cexM) = Red cexM\<close>.\<close>

lemma cexM_Red2: "Red (Red cexM) = Red cexM"
proof -
  have PM: "P cexM = [cexM]" by (rule y3r_P_nonmulti[OF cexM_TPS cexM_nmulti])
  have diag: "\<forall>I < length (P cexM). entry (P cexM ! I) 0 0 = entry (P cexM ! I) 1 0"
    using PM by (simp add: cexM_def entry_def)
  have "Red cexM \<in> RT_PS" by (rule y3r_Red_reduced_of_diag[OF cexM_TPS diag])
  thus ?thesis by (simp add: RT_PS_def)
qed

subsection \<open>The refutation\<close>

lemma cexM_adm3: "adm cexM 3"
proof -
  have "\<not> nadm cexM 3"
    using y3w_nadm_local[of 3 cexM] by (simp add: cexM_def entry_def)
  thus ?thesis by (simp add: adm_def)
qed

lemma cexM_marked3: "(cexM, 3) \<in> Marked"
proof -
  have "le0 cexM 3 4" by (rule cexM_le0I) simp_all
  thus ?thesis using cexM_adm3 by (simp add: Marked_def leR_def)
qed

lemma cexM_anc3: "\<exists>i<3. le0 cexM i 3"
proof (intro exI[of _ 0] conjI)
  show "(0::nat) < 3" by simp
  show "le0 cexM 0 3" by (rule cexM_le0I) simp_all
qed

lemma cexM_Red2_nadm3: "\<not> adm (Red (Red cexM)) 3"
proof -
  let ?R = "[(0::nat,0::nat), (1,1), (2,1), (3,2), (4,3)]"
  have R: "Red (Red cexM) = ?R" using cexM_Red2 cexM_Red by simp
  have LR: "Lng ?R = 5" by simp
  have "nadm ?R 3" using y3w_nadm_local[of 3 ?R] LR by (simp add: entry_def)
  thus ?thesis using R by (simp add: adm_def)
qed

text \<open>\<^bold>\<open>(C4) is FALSE.\<close>\<close>

theorem y3z_C4_false:
  "\<not> (\<forall>M m. M \<in> T_PS \<longrightarrow> (M, m) \<in> Marked \<longrightarrow> (\<exists>i<m. le0 M i m)
             \<longrightarrow> adm (Red (Red M)) m)"
  using cexM_TPS cexM_marked3 cexM_anc3 cexM_Red2_nadm3 by blast

text \<open>\<^bold>\<open>Brick A is FALSE\<close>: the failing column \<open>3\<close> is exactly the \<open>j\<^sub>0\<close> of the §7.4
  proposition on \<open>cexM\<close> --- the unique \<open><\<^sup>NextAdm\<close>-predecessor of the right end.\<close>

lemma cexM_adm: "j < 5 \<Longrightarrow> adm cexM j"
proof -
  assume j: "j < 5"
  consider "j = 0" | "j = 1" | "j = 2" | "j = 3" | "j = 4" using j by linarith
  thus "adm cexM j"
  proof cases
    case 1 thus ?thesis by (simp add: y3w_adm_0)
  next
    case 2
    have "\<not> nadm cexM 1"
      using y3w_nadm_local[of 1 cexM] by (simp add: cexM_def entry_def)
    thus ?thesis using 2 by (simp add: adm_def)
  next
    case 3
    have "\<not> nadm cexM 2"
      using y3w_nadm_local[of 2 cexM] by (simp add: cexM_def entry_def)
    thus ?thesis using 3 by (simp add: adm_def)
  next
    case 4 thus ?thesis using cexM_adm3 by simp
  next
    case 5 thus ?thesis using y3x_adm_last[of 4 cexM] by simp
  qed
qed

lemma cexM_nextAdm3: "nextAdm cexM 0 3 (Lng cexM - 1)"
proof -
  have le34: "le0 cexM 3 4" by (rule cexM_le0I) simp_all
  have Lm: "Lng cexM - 1 = 4" by simp
  have l: "leR cexM 0 3 (Lng cexM - 1)"
    unfolding Lm leR_def using le34 by simp
  have vac: "\<forall>j. 3 < j \<and> j < Lng cexM - 1 \<longrightarrow> \<not> leR cexM 0 j (Lng cexM - 1)
                  \<or> \<not> adm cexM j"
  proof (intro allI impI)
    fix j assume A: "3 < j \<and> j < Lng cexM - 1"
    have a1: "3 < j" using A by simp
    have a2: "j < 4" using A Lm by simp
    have False using a1 a2 by linarith
    thus "\<not> leR cexM 0 j (Lng cexM - 1) \<or> \<not> adm cexM j" by simp
  qed
  have lt: "(3::nat) < Lng cexM - 1" using Lm by simp
  show ?thesis unfolding nextAdm_def using l lt cexM_adm3 vac by simp
qed

lemma cexM_nextAdm_only3:
  assumes H: "nextAdm cexM 0 j0 (Lng cexM - 1)" shows "j0 = 3"
proof (rule ccontr)
  assume ne: "j0 \<noteq> 3"
  have Lm: "Lng cexM - 1 = 4" by simp
  have lt: "j0 < 4" using H Lm by (simp add: nextAdm_def)
  have j0lt: "j0 < 3" using lt ne by simp
  have gap: "\<not> leR cexM 0 3 (Lng cexM - 1) \<or> \<not> adm cexM 3"
    using H j0lt Lm unfolding nextAdm_def by simp
  have le34: "le0 cexM 3 4" by (rule cexM_le0I) simp_all
  have l: "leR cexM 0 3 (Lng cexM - 1)"
    unfolding Lm leR_def using le34 by simp
  show False using gap l cexM_adm3 by simp
qed

lemma cexM_nextAdm_ex1: "\<exists>!j0. nextAdm cexM 0 j0 (Lng cexM - 1)"
  using cexM_nextAdm3 cexM_nextAdm_only3 by blast

lemma cexM_nextAdm_unique: "(THE j0. nextAdm cexM 0 j0 (Lng cexM - 1)) = 3"
  using cexM_nextAdm3 cexM_nextAdm_only3 by (rule the_equality)

theorem y3z_brickA_false:
  "\<not> (\<forall>M. M \<in> T_PS \<longrightarrow> (\<exists>!j0. nextAdm M 0 j0 (Lng M - 1))
           \<longrightarrow> adm (Red (Red M)) (THE j0. nextAdm M 0 j0 (Lng M - 1)))"
proof
  assume A: "\<forall>M. M \<in> T_PS \<longrightarrow> (\<exists>!j0. nextAdm M 0 j0 (Lng M - 1))
                 \<longrightarrow> adm (Red (Red M)) (THE j0. nextAdm M 0 j0 (Lng M - 1))"
  note A' = A[rule_format, of cexM]
  have h: "adm (Red (Red cexM)) (THE j0. nextAdm cexM 0 j0 (Lng cexM - 1))"
    by (rule A'[OF cexM_TPS cexM_nextAdm_ex1])
  have "adm (Red (Red cexM)) 3" using h cexM_nextAdm_unique by simp
  thus False using cexM_Red2_nadm3 by simp
qed


section \<open>Additional relocated campaign annotations\<close>

text \<open>\<^bold>\<open>STATUS (r79, honest)\<close>.  The r77/r78 reduction
  @{thm [source] y3w_7_4_Mark_nextAdm_TPS_of_adm} is a valid implication but a
  \<^bold>\<open>dead route\<close>: its hypothesis \<open>adm (Red (Red M)) j\<^sub>0\<close> (Brick A) is FALSE in
  general (@{thm [source] y3z_brickA_false}), and so is the \<section>6 statement (C4)
  that r77 proposed to derive it from (@{thm [source] y3z_C4_false}).  The
  supporting censuses (4523/0, 50288/0, 45716/0) were bounded by entries \<open>< 3\<close>
  resp. \<open>< 4\<close>; \<open>cexM\<close> needs a row-1 entry of 6.  This is the 13th empirical false
  positive in this project and the fourth caused by a too-small entry bound.

  What survives, and what the next route must look like:

    \<^item> (F) (@{thm [source] y3w_Red_le0}) is unaffected --- \<open>Red\<close> really does only ADD
      row-0 ancestor edges.  So \<open>le\<^sub>M\<close> transports; only \<open>adm\<close> does not, and now
      provably \<^bold>\<open>cannot\<close> be made to.
    \<^item> The \<open>RT\<^bsub>PS\<^esub>\<close> engine @{thm [source] Mark_nest_common_marked} DOES relax in the
      \<^emph>\<open>inner\<close> column: on reduced \<open>M\<close>, \<open>(M,j\<^sub>0) \<in> T\<^bsub>PS\<^esub>\<^sup>Marked\<close> and \<open>j \<le> j\<^sub>0 < Lng M - 1\<close>
      alone pin the unique common scb position (1271/0 at entries \<open>< 4\<close>, \<open>Lng \<le> 4\<close>;
      2845/0 at entries \<open>< 3\<close>, \<open>Lng \<le> 5\<close>).  But it does \<^bold>\<open>not\<close> relax in the OUTER
      column: dropping \<open>adm M j\<^sub>0\<close> and keeping only the \<open>le\<^sub>0\<close>-to-right-end facts
      breaks it (7/883 resp. 21/1495 failures).  Since \<open>adm (Red (Red M)) j\<^sub>0\<close> is
      exactly what \<open>cexM\<close> refutes, \<^bold>\<open>no\<close> relaxation of this engine can carry the
      \<open>T\<^bsub>PS\<^esub>\<close> statement: the reduct simply is not marked at \<open>j\<^sub>0\<close>.
    \<^item> The \<^bold>\<open>proposition itself is not refuted\<close>: on \<open>cexM\<close> all four of its exercises
      still pass in the vetted model.  So it must be proved by a route that does
      \<^emph>\<open>not\<close> go through \<open>T\<^bsub>PS\<^esub>\<^sup>Marked\<close>-ness of the reduct --- e.g. directly on the
      \<open>Mark\<close>/\<open>Trans\<close> recursion (note \<open>Mark M i = Mark (Red (Red M)) i\<close> always holds,
      @{thm [source] y3s_Mark_funpow_Red}: it is only the \<^emph>\<open>hypotheses\<close> of the \<section>7
      engine, not its subject matter, that fail to transport).  Empirically
      \<open>Mark N k\<close> is principal-or-zero for \<^bold>\<open>every\<close> column \<open>k\<close> of a reduced \<open>N\<close>
      (1065/0), which is the reflexive (\<open>j = j\<^sub>0\<close>) half of the conclusion and needs
      no admissibility at all --- that is the natural next brick.
    \<^item> Sweeps: \<open>python/red_model.py\<close>, \<open>python/trans_model.py\<close> (both vetted).\<close>

(* ===================================================================== *)
(* r80-Y3Y: the DIRECT route on the Mark/Trans recursion.                 *)
(* Brick (P): for a REDUCED N, Mark N m is dfree and principal-or-zero    *)
(* for EVERY column m --- no adm, no Marked, no ancestry hypothesis.      *)
(* This is the ingredient the old (dead) route tried to obtain by         *)
(* transporting Marked-ness through Red (refuted by y3z_C4_false).        *)
(* ===================================================================== *)

section \<open>r80-Y3Y --- unconditional principality of \<open>Mark\<close> on \<open>RT\<^bsub>PS\<^esub>\<close>\<close>

text \<open>\<^bold>\<open>Brick (P)\<close>.  Every value of \<open>Mark N m\<close> at a reduced \<open>N\<close> is a \<open>D\<^sub>\<omega>\<close>-free
  Buchholz term which is either \<open>0\<^sub>B\<close> or a \<^emph>\<open>single principal\<close> term
  (\<open>isPTB_str\<close> of its flattening) --- for \<^bold>\<open>every\<close> column \<open>m\<close>, admissible or not,
  marked or not, in range or not.  The frozen @{thm [source] Mark_marked_isPTB}
  derives this from \<open>(N,m) \<in> Marked\<close> via the \<open>MarkedB\<close> invariant; that route is
  unavailable here (the reduct of a marked \<open>T\<^bsub>PS\<^esub>\<close>-column need not be marked ---
  @{thm [source] y3z_brickA_false}).  Instead we run the \<open>Mark\<close> recursion itself:
  in the surgery branch the principality of the substituted value
  \<open>c\<^sub>0 = Mark (Pred N) m\<close> comes from the \<^emph>\<open>induction hypothesis\<close> rather than from
  \<open>Marked\<close>-ness, and the principality of the implanted block \<open>c\<^sub>2 = transC2 N\<close> is
  already hypothesis-free (@{thm [source] m_8_5_isPTB_str_transC2_std},
  @{thm [source] dfree_transC2}); the fallback / leaf branches are \<open>D\<^bsub>v\<^esub> 0\<close> outright.
  Census (this round, python/_y3_74_princ_wide.py): 0 failures, all exercises
  non-vacuous (the statement has no hypothesis beyond \<open>N \<in> RT\<^bsub>PS\<^esub>\<close>).\<close>

section \<open>r81-Y4 --- the RELAXED nesting engine: \<open>Mark\<close> nests with NO hypothesis on the inner column\<close>

text \<open>\<^bold>\<open>Target\<close> (the last open item of the project).  The \<open>T\<^bsub>PS\<^esub>\<close> form of the §7.4
  系 (\<open>Mark\<close> vs. \<open>NextAdm\<close>) must be proven through the reduct \<open>R = Red (Red M)\<close>,
  because \<open>Trans\<close>/\<open>Mark\<close> are only defined on \<open>RT\<^bsub>PS\<^esub>\<close>.  The \<^emph>\<open>subject matter\<close>
  transports perfectly (@{thm [source] y3s_Mark_funpow_Red}: \<open>Mark M i = Mark (Red (Red M)) i\<close>)
  and so does ancestry (@{thm [source] y3w_Red_le0}), but \<^bold>\<open>admissibility does not\<close>:
  @{thm [source] y3z_C4_false} exhibits a \<open>T\<^bsub>PS\<^esub>\<close> sequence with a marked, strictly
  \<open>\<le>\<^sub>0\<close>-ancestral column whose reduct is NOT admissible.  Every hypothesis of the
  frozen \<open>RT\<^bsub>PS\<^esub>\<close> engine (@{thm [source] Mark_nest_common_marked},
  @{thm [source] Mark_MarkedB_nest}, @{thm [source] m_7_3_Trans_Mark_MarkedB}) is
  \<open>Marked\<close>-ness, i.e. admissibility — so the engine cannot be \<^emph>\<open>fed\<close>; it must be
  \<^bold>\<open>replaced\<close>.

  This section replaces it.  The punchline is that the nesting needs \<^bold>\<open>no hypothesis
  at all\<close>: for a reduced \<open>N\<close> and ANY two columns \<open>j \<le> j\<^sub>0\<close> (admissible or not, marked
  or not, ancestral or not, in range or not) the later marked block nests in the
  earlier one.  The frozen engine's \<open>Marked\<close> hypotheses were never load-bearing for
  the \<^emph>\<open>conclusion\<close>; they were load-bearing only for its \<^emph>\<open>ingredients\<close>
  (\<open>(Trans N, Mark N k) \<in> MarkedB\<close> was the only source of principality of \<open>Mark N k\<close>).
  @{thm [source] y3y_Mark_princ} removed exactly that dependency last round, and the
  induction below now runs on the \<open>Mark\<close> recursion itself.

  Census (\<open>python/_y4_free_census.py\<close>, \<open>python/_y4_relax_census.py\<close>) — all exercises
  NON-VACUOUS, bounds stated:
    \<^item> free nesting (@{text y4b}/@{text y4c}), entries \<le> 4, \<open>Lng\<close> \<le> 4, columns probed
      up to \<open>Lng N + 2\<close> (so out-of-range columns too): 47518 exercises, 0 failures;
    \<^item> joint \<open>Pred\<close>-companion (@{text y4d}), entries \<le> 4, \<open>Lng\<close> \<le> 4: 1932 exercises,
      0 failures; random entries \<le> 20, \<open>Lng\<close> \<le> 10: 594 exercises, 0 failures.
  The wide runs (entries \<le> 8, \<open>Lng\<close> \<le> 6) are reported in the round log.\<close>


text \<open>\<^bold>\<open>The relaxed engine, \<open>\<exists>!\<close> joint form.\<close>  This is the §7.4 系's nesting fact
  with the INNER column's \<open>Marked\<close>-ness (and its \<open>\<le>\<^sub>0\<close>-ancestry) DELETED.

  \<^bold>\<open>\<open>\<Longrightarrow>\<close> NOT a route to the \<open>T\<^bsub>PS\<^esub>\<close> form of the §7.4 系. READ THIS BEFORE REUSING IT.\<close>
  The hypothesis \<open>(N,j\<^sub>0) \<in> Marked\<close> that survives here is admissibility at the OUTER
  column \<^emph>\<open>of the reduct\<close>.  In the \<open>T\<^bsub>PS\<^esub>\<close> transport the reduct is \<open>N = Red (Red M)\<close>,
  and admissibility is NOT \<open>Red\<close>-invariant (correction A4; \<open>\<le>\<^sub>M\<close> is not preserved by
  \<open>Red\<close>): @{thm [source] y3z_C4_false} and @{thm [source] y3z_brickA_false} exhibit a
  \<open>T\<^bsub>PS\<^esub>\<close> sequence \<open>M\<close> with \<open>(M,j\<^sub>0) \<in> Marked\<close> and \<open>\<not> adm (Red (Red M)) j\<^sub>0\<close>.  So
  \<open>y4d_Mark_nest_Pred_joint\<close> and \<open>y4e_Mark_nest_relaxed_Pred\<close>
  below are TRUE implications whose hypothesis we \<^bold>\<open>cannot supply\<close> from the \<open>T\<^bsub>PS\<^esub>\<close>
  side.  They are kept because they are the correct \<open>RT\<^bsub>PS\<^esub>\<close> statements (and because
  the \<open>multiT\<close> branch of @{thm [source] y4d_Mark_nest_Pred_aux} genuinely needs
  \<open>Marked\<close> to transport into the last \<open>P\<close>-component), NOT because they are a live
  route.  The \<open>T\<^bsub>PS\<^esub>\<close> form of the 系 is FALSE anyway --- see the closing note of this
  section.  The hypothesis-free part of this round that IS reusable everywhere is
  @{thm [source] y4b_Mark_nest_free} / @{thm [source] y4c_Mark_nest_free_ex1}; the
  honest \<open>RT\<^bsub>PS\<^esub>\<close> engine is subsection (f).\<close>

end
