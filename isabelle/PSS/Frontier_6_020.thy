theory Frontier_6_020
  imports Support_6_003
begin

section \<open>§6.5 Red termination: foundational helpers\<close>

text \<open>
  Helpers for the well-definedness (= termination) of @{const Red}.  The
  article proves \<open>p_6_5_Red_welldef\<close> in two layers: on the core
  \<open>{M \<in> PT\<^sub>PS | M\<^sub>0 = (0,0)}\<close> by induction on \<open>Lng M - TrMax M\<close>, and on the rest
  of \<open>T\<^sub>PS\<close> immediately.  The facts below establish the arithmetic the measure
  needs: lengths/entries of \<open>diagSeq\<close>, that a diagonal prefix extends the trunk,
  and that branches are strictly shorter than the branch segment.
\<close>

subsection \<open>Diagonal segments \<open>diagSeq a b = ((j,j))\<^bsub>j=a\<^esub>\<^bsup>b\<^esup>\<close>\<close>

lemma Lng_diagSeq[simp]: "Lng (diagSeq a b) = Suc b - a"
  by (simp add: diagSeq_def del: upt_Suc)

lemma diagSeq_nth:
  assumes "j < Suc b - a"
  shows "diagSeq a b ! j = (a + j, a + j)"
proof -
  have lt: "j < length [a..<Suc b]" using assms by (simp del: upt_Suc)
  have aj: "a + j < Suc b" using assms by linarith
  show ?thesis by (simp add: diagSeq_def nth_map[OF lt] nth_upt aj del: upt_Suc)
qed

lemma entry_diagSeq:
  assumes "j < Suc b - a"
  shows "entry (diagSeq a b) i j = a + j"
  using diagSeq_nth[OF assms] by (simp add: entry_def)

subsection \<open>Branch length bound\<close>

text \<open>A single block of a \<open>concat\<close> is no longer than the whole \<open>concat\<close>.\<close>

lemma length_nth_le_concat:
  assumes "J < length xss"
  shows "length (xss ! J) \<le> length (concat xss)"
proof -
  have mem: "(map length xss) ! J \<in> set (map length xss)"
    using assms by (simp add: nth_mem)
  have "length (xss ! J) = (map length xss) ! J" using assms by simp
  also have "\<dots> \<le> sum_list (map length xss)" by (rule member_le_sum_list[OF mem]) simp
  also have "\<dots> = length (concat xss)" by (simp add: length_concat)
  finally show ?thesis .
qed

text \<open>m: each branch component is strictly shorter than the branch segment,
  i.e. \<open>Lng (Br M ! J) \<le> Lng M - TrMax M - 1\<close>.  This bounds the recursion
  argument \<open>N\<^sub>J\<close> in the core case of @{const Red} (case 2).\<close>

lemma Lng_Br_le:
  assumes J: "J < Lng (Br M)"
  shows "Lng (Br M ! J) \<le> Lng M - TrMax M - 1"
proof -
  have ne: "Br M \<noteq> []" using J by auto
  have tr: "TrMax M \<noteq> Lng M - 1"
  proof
    assume "TrMax M = Lng M - 1"
    hence "Br M = []" by (simp add: Br_def)
    thus False using ne by simp
  qed
  hence brP: "Br M = P (seg M (TrMax M + 1) (Lng M - 1))" by (simp add: Br_def)
  let ?Q = "seg M (TrMax M + 1) (Lng M - 1)"
  have "Lng (Br M ! J) \<le> Lng (concat (P ?Q))"
    using J by (simp only: brP length_nth_le_concat)
  also have "\<dots> = Lng ?Q" by (simp add: poper_concat_P)
  also have "\<dots> = Suc (Lng M - 1) - (TrMax M + 1)" by (simp only: Lng_seg)
  also have "\<dots> \<le> Lng M - TrMax M - 1" by simp
  finally show ?thesis .
qed

subsection \<open>Trunk of a diagonal segment\<close>

text \<open>The row-1 chain steps along a diagonal: \<open>(1,j) <\<^bsub>diagSeq u v\<^esub>\<^sup>Next (1,j+1)\<close>
  for every interior \<open>j\<close>.  (The single ancestor of \<open>j+1\<close> reachable from above
  is \<open>j+1\<close> itself, so the row-1 minimality condition is vacuous.)\<close>

lemma nextR1_diagSeq:
  assumes "Suc j < Suc v - u"
  shows "nextR (diagSeq u v) 1 j (Suc j)"
proof -
  let ?M = "diagSeq u v"
  have L: "Lng ?M = Suc v - u" by simp
  have e0j:  "entry ?M 0 j = u + j"          using assms by (intro entry_diagSeq) simp
  have e0sj: "entry ?M 0 (Suc j) = u + Suc j" using assms by (intro entry_diagSeq) simp
  have e1j:  "entry ?M 1 j = u + j"          using assms by (intro entry_diagSeq) simp
  have e1sj: "entry ?M 1 (Suc j) = u + Suc j" using assms by (intro entry_diagSeq) simp
  have n0: "nextrel0 ?M j (Suc j)"
    unfolding nextrel0_def using assms e0j e0sj L by auto
  have rt: "(nextrel0 ?M)\<^sup>*\<^sup>* j (Suc j)" using n0 by (rule r_into_rtranclp)
  have le0: "le0 ?M j (Suc j)" unfolding le0_def using assms L rt by auto
  have univ: "\<forall>j''. j < j'' \<and> le0 ?M j'' (Suc j)
                  \<longrightarrow> entry ?M 1 (Suc j) \<le> entry ?M 1 j''"
  proof (intro allI impI)
    fix j'' assume a: "j < j'' \<and> le0 ?M j'' (Suc j)"
    hence "(nextrel0 ?M)\<^sup>*\<^sup>* j'' (Suc j)" by (simp add: le0_def)
    hence "j'' \<le> Suc j" by (rule nextrel0_rtrancl_mono)
    with a have "j'' = Suc j" by linarith
    thus "entry ?M 1 (Suc j) \<le> entry ?M 1 j''" by simp
  qed
  have "nextrel1 ?M j (Suc j)"
    unfolding nextrel1_def using assms e1j e1sj L le0 univ by auto
  thus ?thesis by (simp add: nextR_def)
qed

text \<open>m: a diagonal segment is entirely trunk: \<open>TrMax (diagSeq u v) = v - u\<close>
  \<open>(= Lng - 1)\<close>.  Foundational for the core base case of @{const Red}
  (\<open>j\<^sub>1' = j\<^sub>1\<close>) and for the trunk-extension estimate of \<open>coreReduce\<close>.\<close>

lemma TrMax_diagSeq:
  assumes uv: "u \<le> v"
  shows "TrMax (diagSeq u v) = v - u"
proof -
  let ?M = "diagSeq u v"
  have L: "Lng ?M = Suc v - u" by simp
  have pos: "\<And>j'. j' < v - u \<Longrightarrow> nextR ?M 1 j' (Suc j')"
  proof -
    fix j' assume "j' < v - u"
    hence "Suc j' < Suc v - u" using uv by (simp add: Suc_diff_le)
    thus "nextR ?M 1 j' (Suc j')" by (rule nextR1_diagSeq)
  qed
  have neg: "\<not> nextR ?M 1 (v - u) (Suc (v - u))"
  proof
    assume "nextR ?M 1 (v - u) (Suc (v - u))"
    hence "nextrel1 ?M (v - u) (Suc (v - u))" by (simp add: nextR_def)
    hence "Suc (v - u) < Lng ?M" by (simp add: nextrel1_def)
    thus False using L uv by simp
  qed
  have Seq: "{j. \<forall>j'<j. nextR ?M 1 j' (j' + 1)} = {.. v - u}"
  proof (rule set_eqI, rule iffI)
    fix j assume "j \<in> {j. \<forall>j'<j. nextR ?M 1 j' (j' + 1)}"
    hence h: "\<forall>j'<j. nextR ?M 1 j' (Suc j')" by simp
    show "j \<in> {.. v - u}"
    proof (rule ccontr)
      assume "j \<notin> {.. v - u}"
      hence "v - u < j" by simp
      with h have "nextR ?M 1 (v - u) (Suc (v - u))" by simp
      thus False using neg by simp
    qed
  next
    fix j assume "j \<in> {.. v - u}"
    hence jle: "j \<le> v - u" by simp
    have "\<forall>j'<j. nextR ?M 1 j' (Suc j')"
    proof (intro allI impI)
      fix j' assume "j' < j"
      hence "j' < v - u" using jle by linarith
      thus "nextR ?M 1 j' (Suc j')" by (rule pos)
    qed
    thus "j \<in> {j. \<forall>j'<j. nextR ?M 1 j' (j' + 1)}" by simp
  qed
  have "TrMax ?M = Max {j. \<forall>j'<j. nextR ?M 1 j' (j' + 1)}" by (simp add: TrMax_def)
  also have "\<dots> = Max {.. v - u}" by (simp only: Seq)
  also have "\<dots> = v - u" by (rule Max_eqI) auto
  finally show ?thesis .
qed

subsection \<open>\<open>\<le>\<^sub>M\<close> on a diagonal segment is the index order (both rows)\<close>

text \<open>H1 (feeds the core-trunk base case \<open>Red (diagSeq ..)\<close>): on a diagonal
  segment \<open>diagSeq a b\<close> the row-0 \<open><\<^sup>Next\<close>-step is the consecutive index step.\<close>

lemma nextrel0_diagSeq_step:
  assumes "Suc j < Suc b - a"
  shows "nextrel0 (diagSeq a b) j (Suc j)"
proof -
  let ?M = "diagSeq a b"
  have L: "Lng ?M = Suc b - a" by simp
  have ej:  "entry ?M 0 j = a + j"           using assms by (intro entry_diagSeq) simp
  have esj: "entry ?M 0 (Suc j) = a + Suc j"  using assms by (intro entry_diagSeq) simp
  show ?thesis unfolding nextrel0_def using assms ej esj L by auto
qed

text \<open>Row-0 reachability along a diagonal: every \<open>j0 \<le> j1 < Lng\<close> is connected
  by the reflexive-transitive closure of consecutive steps.\<close>

lemma nextrel0_diagSeq_rtrancl:
  assumes "j1 < Suc b - a" and "j0 \<le> j1"
  shows "(nextrel0 (diagSeq a b))\<^sup>*\<^sup>* j0 j1"
proof -
  let ?M = "diagSeq a b"
  from assms obtain d where d: "j1 = j0 + d" using le_Suc_ex by blast
  have "j0 + d < Suc b - a \<Longrightarrow> (nextrel0 ?M)\<^sup>*\<^sup>* j0 (j0 + d)"
  proof (induction d)
    case 0 show ?case by simp
  next
    case (Suc d)
    have lt: "Suc (j0 + d) < Suc b - a" using Suc.prems by simp
    have rt: "(nextrel0 ?M)\<^sup>*\<^sup>* j0 (j0 + d)" using Suc.IH lt by simp
    have step: "nextrel0 ?M (j0 + d) (Suc (j0 + d))"
      using lt by (rule nextrel0_diagSeq_step)
    show ?case using rt step by (simp add: rtranclp.rtrancl_into_rtrancl)
  qed
  thus ?thesis using assms(1) d by simp
qed

text \<open>m (H1): row-0 \<open>\<le>\<^sub>M\<close> on a diagonal segment is the index order.\<close>

lemma le0_diagSeq:
  assumes "j0 < Suc b - a" and "j1 < Suc b - a"
  shows "le0 (diagSeq a b) j0 j1 \<longleftrightarrow> j0 \<le> j1"
proof
  assume "le0 (diagSeq a b) j0 j1"
  hence "(nextrel0 (diagSeq a b))\<^sup>*\<^sup>* j0 j1" by (simp add: le0_def)
  thus "j0 \<le> j1" by (rule nextrel0_rtrancl_mono)
next
  assume "j0 \<le> j1"
  hence "(nextrel0 (diagSeq a b))\<^sup>*\<^sup>* j0 j1"
    using assms(2) by (rule nextrel0_diagSeq_rtrancl[rotated])
  thus "le0 (diagSeq a b) j0 j1" using assms by (simp add: le0_def)
qed

subsection \<open>\<open>IncrFirst\<close>-invariance of \<open>TrMax\<close> (and its iterate)\<close>

text \<open>\<open>TrMax\<close> depends only on the row-1 \<open><\<^sup>Next\<close> chain, which is \<open>IncrFirst\<close>-
  invariant (\<open>nextrel1_IncrFirst_eq\<close>); hence so is \<open>TrMax\<close>, and \<open>Lng - TrMax\<close>
  (the core measure) is preserved by the \<open>IncrFirst\<^bsup>m\<^sub>1\<^sub>0\<^esup>\<close> in case 4 of @{const Red}.\<close>

lemma TrMax_IncrFirst[simp]: "TrMax (IncrFirst M) = TrMax M"
  by (simp add: TrMax_def nextR_def nextrel1_IncrFirst_eq)

lemma Lng_funpow_IncrFirst[simp]: "Lng ((IncrFirst ^^ k) M) = Lng M"
  by (induction k) simp_all

lemma TrMax_funpow_IncrFirst[simp]: "TrMax ((IncrFirst ^^ k) M) = TrMax M"
  by (induction k) simp_all

subsection \<open>Trunk extension by a diagonal prefix\<close>

text \<open>A consecutive row-1 increase \<open>(1,j) <\<^bsub>M\<^esub>\<^sup>Next (1,j+1)\<close> follows from the
  raw monotonicity at \<open>j\<close>: the row-0 step gives \<open>\<le>\<^sub>M\<close>, and the only \<open>\<le>\<^sub>M\<close>-ancestor
  of \<open>j+1\<close> above \<open>j\<close> is \<open>j+1\<close> itself, so the row-1 minimality is automatic.
  Generic helper subsuming @{thm [source] nextR1_diagSeq}.\<close>

lemma nextR1_consecutive:
  assumes L: "Suc j < Lng M"
    and e0: "entry M 0 j < entry M 0 (Suc j)"
    and e1: "entry M 1 j < entry M 1 (Suc j)"
  shows "nextR M 1 j (Suc j)"
proof -
  have n0: "nextrel0 M j (Suc j)" unfolding nextrel0_def using L e0 by auto
  have rt: "(nextrel0 M)\<^sup>*\<^sup>* j (Suc j)" using n0 by (rule r_into_rtranclp)
  have le0: "le0 M j (Suc j)" unfolding le0_def using L rt by auto
  have univ: "\<forall>i. j < i \<and> le0 M i (Suc j) \<longrightarrow> entry M 1 (Suc j) \<le> entry M 1 i"
  proof (intro allI impI)
    fix i assume a: "j < i \<and> le0 M i (Suc j)"
    hence "(nextrel0 M)\<^sup>*\<^sup>* i (Suc j)" by (simp add: le0_def)
    hence "i \<le> Suc j" by (rule nextrel0_rtrancl_mono)
    with a have "i = Suc j" by linarith
    thus "entry M 1 (Suc j) \<le> entry M 1 i" by simp
  qed
  have "nextrel1 M j (Suc j)"
    unfolding nextrel1_def using L e1 le0 univ by auto
  thus ?thesis by (simp add: nextR_def)
qed

text \<open>Entries of \<open>diagSeq 0 k @ rest\<close>: diagonal on the prefix \<open>i \<le> k\<close>, and
  \<open>rest\<close>'s head at the junction index \<open>Suc k\<close>.\<close>

lemma entry_diagSeq_append_lo:
  assumes "i \<le> k"
  shows "entry (diagSeq 0 k @ rest) p i = i"
proof -
  have lt: "i < length (diagSeq 0 k)" using assms by simp
  have ai: "i < Suc k - 0" using assms by simp
  have "(diagSeq 0 k @ rest) ! i = diagSeq 0 k ! i" using lt by (simp add: nth_append)
  also have "\<dots> = (i, i)" using diagSeq_nth[OF ai] by simp
  finally show ?thesis by (simp add: entry_def)
qed

lemma entry_diagSeq_append_junction:
  "entry (diagSeq 0 k @ rest) p (Suc k) = entry rest p 0"
  by (simp add: entry_def nth_append)

text \<open>§6.5 branch-3b BC0, PIECE 1 (trunk-spine row-0 edge).  In the core-nontrunk
  reduction \<open>Red M = diagSeq 0 (TrMax M) @ concat (..branch blocks..)\<close>, the
  diagonal prefix \<open>diagSeq 0 t\<close> carries a faithful row-0 spine: on every prefix
  index \<open>j \<le> t\<close> the row-0 \<open><\<^sup>Next\<close>-step is the consecutive step, so \<open>le0\<close> on the
  prefix is the index order.  This is the easy half of branch-3b BC0 (the part
  that lives entirely inside the trunk diagonal); the genuinely-hard residual is
  PIECE 3 (the spine-to-block junction).  Empirically TRUE 60750/60750 (rank\<le>5),
  validated again at rank\<ge>12.\<close>

lemma nextrel0_diagSeq_append_step:
  assumes "j < k"
  shows "nextrel0 (diagSeq 0 k @ rest) j (Suc j)"
proof -
  let ?M = "diagSeq 0 k @ rest"
  have L: "Lng ?M = Suc k + Lng rest" by simp
  have lt: "Suc j < Lng ?M" using assms L by linarith
  have ej:  "entry ?M 0 j = j"       using assms by (intro entry_diagSeq_append_lo) simp
  have esj: "entry ?M 0 (Suc j) = Suc j" using assms by (intro entry_diagSeq_append_lo) simp
  have noint: "\<forall>j'. j < j' \<and> j' < Suc j \<longrightarrow> entry ?M 0 j' \<ge> entry ?M 0 (Suc j)" by auto
  show ?thesis unfolding nextrel0_def using assms lt ej esj noint by simp
qed

lemma nextrel0_diagSeq_append_rtrancl:
  assumes "j1 \<le> k" and "j0 \<le> j1"
  shows "(nextrel0 (diagSeq 0 k @ rest))\<^sup>*\<^sup>* j0 j1"
proof -
  let ?M = "diagSeq 0 k @ rest"
  from assms(2) obtain d where d: "j1 = j0 + d" using le_Suc_ex by blast
  have "j0 + d \<le> k \<Longrightarrow> (nextrel0 ?M)\<^sup>*\<^sup>* j0 (j0 + d)"
  proof (induction d)
    case 0 show ?case by simp
  next
    case (Suc d)
    have le: "j0 + d \<le> k" using Suc.prems by simp
    have rt: "(nextrel0 ?M)\<^sup>*\<^sup>* j0 (j0 + d)" using Suc.IH le by simp
    have lt: "j0 + d < k" using Suc.prems by simp
    have step: "nextrel0 ?M (j0 + d) (Suc (j0 + d))"
      using lt by (rule nextrel0_diagSeq_append_step)
    show ?case using rt step by (simp add: rtranclp.rtrancl_into_rtrancl)
  qed
  thus ?thesis using assms(1) d by simp
qed

lemma le0_diagSeq_append_prefix:
  assumes "j0 \<le> j1" and "j1 \<le> k"
  shows "le0 (diagSeq 0 k @ rest) j0 j1"
proof -
  let ?M = "diagSeq 0 k @ rest"
  have rt: "(nextrel0 ?M)\<^sup>*\<^sup>* j0 j1"
    by (rule nextrel0_diagSeq_append_rtrancl[OF assms(2,1)])
  have L: "Lng ?M = Suc k + Lng rest" by simp
  have b1: "j1 < Lng ?M" using assms(2) L by linarith
  have b0: "j0 < Lng ?M" using assms b1 by linarith
  show ?thesis using rt b0 b1 by (simp add: le0_def)
qed

text \<open>If a non-empty \<open>rest\<close> starts strictly above the diagonal (both rows
  \<open>> k\<close>), the trunk runs through the whole diagonal prefix and the junction, so
  \<open>TrMax (diagSeq 0 k @ rest) \<ge> Suc k\<close>.  This is the trunk-extension fact behind
  \<open>coreReduce\<close> (case 4 of @{const Red}): a diagonal prefix of length \<open>m\<^sub>1\<^sub>0\<close> raises
  \<open>TrMax\<close> by \<open>m\<^sub>1\<^sub>0\<close>, keeping \<open>Lng - TrMax\<close> from growing.\<close>

lemma nextR1_diagSeq_append:
  assumes ne: "rest \<noteq> []" and r0: "k < entry rest 0 0" and r1: "k < entry rest 1 0"
    and jk: "j' \<le> k"
  shows "nextR (diagSeq 0 k @ rest) 1 j' (Suc j')"
proof -
  let ?M = "diagSeq 0 k @ rest"
  have lenr: "Lng rest > 0" using ne by (cases rest) auto
  have lenM: "Lng ?M = Suc k + Lng rest" by simp
  have L: "Suc j' < Lng ?M" using jk lenr lenM by linarith
  have ej': "entry ?M 0 j' = j'" "entry ?M 1 j' = j'" using jk by (auto simp: entry_diagSeq_append_lo)
  have key: "entry ?M 0 j' < entry ?M 0 (Suc j') \<and> entry ?M 1 j' < entry ?M 1 (Suc j')"
  proof (cases "j' < k")
    case True
    hence sk: "Suc j' \<le> k" by simp
    have "entry ?M 0 (Suc j') = Suc j'" "entry ?M 1 (Suc j') = Suc j'"
      using sk by (auto simp: entry_diagSeq_append_lo)
    thus ?thesis using ej' by simp
  next
    case False
    hence jk': "j' = k" using jk by simp
    have "entry ?M 0 (Suc j') = entry rest 0 0" "entry ?M 1 (Suc j') = entry rest 1 0"
      using jk' by (auto simp: entry_diagSeq_append_junction)
    thus ?thesis using ej' jk' r0 r1 by simp
  qed
  show ?thesis by (rule nextR1_consecutive[OF L conjunct1[OF key] conjunct2[OF key]])
qed

lemma le_TrMax_intro:
  assumes T: "M \<in> T_PS" and H: "\<forall>j'<n. nextR M 1 j' (j' + 1)"
  shows "n \<le> TrMax M"
proof -
  let ?S = "{j. \<forall>j'<j. nextR M 1 j' (j' + 1)}"
  have LM: "Lng M > 0" using T by (cases M) (auto simp: T_PS_def)
  have sub: "?S \<subseteq> {..Lng M - 1}"
  proof
    fix j assume "j \<in> ?S"
    hence Hj: "\<forall>j'<j. nextR M 1 j' (j' + 1)" by simp
    show "j \<in> {..Lng M - 1}"
    proof (rule ccontr)
      assume "j \<notin> {..Lng M - 1}"
      hence "Lng M - 1 < j" by simp
      hence "nextR M 1 (Lng M - 1) ((Lng M - 1) + 1)" using Hj by blast
      hence "(Lng M - 1) + 1 < Lng M" by (simp add: nextR_def nextrel1_def)
      thus False using LM by simp
    qed
  qed
  hence fin: "finite ?S" by (rule finite_subset) simp
  have nS: "n \<in> ?S" using H by simp
  have "n \<le> Max ?S" using fin nS by (rule Max_ge)
  thus ?thesis by (simp add: TrMax_def)
qed

lemma TrMax_diagSeq_append_ge:
  assumes ne: "rest \<noteq> []" and r0: "k < entry rest 0 0" and r1: "k < entry rest 1 0"
  shows "Suc k \<le> TrMax (diagSeq 0 k @ rest)"
proof -
  let ?M = "diagSeq 0 k @ rest"
  have T: "?M \<in> T_PS" using ne by (simp add: T_PS_def)
  have "\<forall>j'<Suc k. nextR ?M 1 j' (j' + 1)"
  proof (intro allI impI)
    fix j' assume "j' < Suc k"
    hence "j' \<le> k" by simp
    from nextR1_diagSeq_append[OF ne r0 r1 this] show "nextR ?M 1 j' (j' + 1)" by simp
  qed
  from le_TrMax_intro[OF T this] show ?thesis .
qed

subsection \<open>The core measure \<open>\<beta>\<close> and the one-step \<open>coreReduce\<close>\<close>

text \<open>\<open>entry\<close> under the \<open>IncrFirst\<close> iterate: row 0 is raised by \<open>k\<close>, row 1 fixed.\<close>

lemma entry_funpow_IncrFirst0:
  "j < Lng M \<Longrightarrow> entry ((IncrFirst ^^ k) M) 0 j = entry M 0 j + k"
proof (induction k)
  case 0 thus ?case by simp
next
  case (Suc k)
  have jl: "j < Lng ((IncrFirst ^^ k) M)" using Suc.prems by simp
  have "entry ((IncrFirst ^^ Suc k) M) 0 j = entry (IncrFirst ((IncrFirst ^^ k) M)) 0 j"
    by simp
  also have "\<dots> = Suc (entry ((IncrFirst ^^ k) M) 0 j)" using jl by (simp add: entry_IncrFirst)
  also have "\<dots> = Suc (entry M 0 j + k)" using Suc by simp
  finally show ?case by simp
qed

lemma entry_funpow_IncrFirst1:
  "j < Lng M \<Longrightarrow> entry ((IncrFirst ^^ k) M) 1 j = entry M 1 j"
proof (induction k)
  case 0 thus ?case by simp
next
  case (Suc k)
  have jl: "j < Lng ((IncrFirst ^^ k) M)" using Suc.prems by simp
  have "entry ((IncrFirst ^^ Suc k) M) 1 j = entry (IncrFirst ((IncrFirst ^^ k) M)) 1 j"
    by simp
  also have "\<dots> = entry ((IncrFirst ^^ k) M) 1 j" using jl by (simp add: entry_IncrFirst)
  also have "\<dots> = entry M 1 j" using Suc by simp
  finally show ?case .
qed


text \<open>\<open>\<beta> M = Lng M - TrMax M\<close> is the core measure (branch positions right of the
  trunk).  \<open>coreReduce M\<close> is the core element (starting at \<open>(0,0)\<close>) that a
  non-core mono \<open>M\<close> reduces to in one @{const Red} step: shift row 0 down when
  \<open>M\<^bsub>1,0\<^esub> = 0\<close> (case 3), else prepend a diagonal of length \<open>M\<^bsub>1,0\<^esub>\<close> (case 4).\<close>

definition betaM :: "pairseq \<Rightarrow> nat" where
  "betaM M = Lng M - TrMax M"

definition coreReduce :: "pairseq \<Rightarrow> pairseq" where
  "coreReduce M =
     (if entry M 1 0 = 0
      then map (\<lambda>j. (entry M 0 j - entry M 0 0, entry M 1 j)) [0..<Lng M]
      else diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ (entry M 1 0)) M)"

text \<open>\<open>coreReduce M\<close> starts at \<open>(0,0)\<close> (it lands in the core), for any non-empty
  non-core \<open>M\<close>.\<close>

lemma coreReduce_core:
  assumes T: "M \<in> T_PS"
  shows "entry (coreReduce M) 0 0 = 0 \<and> entry (coreReduce M) 1 0 = 0"
proof (cases "entry M 1 0 = 0")
  case True
  have L: "Lng M > 0" using T by (cases M) (auto simp: T_PS_def)
  have "coreReduce M = map (\<lambda>j. (entry M 0 j - entry M 0 0, entry M 1 j)) [0..<Lng M]"
    using True by (simp add: coreReduce_def)
  thus ?thesis using True L by (simp add: entry_def)
next
  case False
  let ?k = "entry M 1 0 - 1"
  have "coreReduce M = diagSeq 0 ?k @ (IncrFirst ^^ (entry M 1 0)) M"
    using False by (simp add: coreReduce_def)
  thus ?thesis using False
    by (simp add: entry_diagSeq_append_lo[where i=0])
qed

text \<open>m: the core measure does not grow under \<open>coreReduce\<close>:
  \<open>\<beta> (coreReduce M) \<le> Lng M\<close>.  Case 3 (\<open>m\<^sub>1\<^sub>0=0\<close>) is immediate (\<open>Lng\<close> fixed,
  \<open>\<beta> \<le> Lng\<close>); case 4 (\<open>m\<^sub>1\<^sub>0>0\<close>) uses @{thm [source] TrMax_diagSeq_append_ge}: the
  prepended diagonal of length \<open>m\<^sub>1\<^sub>0\<close> raises \<open>TrMax\<close> by \<open>m\<^sub>1\<^sub>0\<close>.\<close>

lemma betaM_coreReduce_le:
  assumes T: "M \<in> T_PS"
  shows "betaM (coreReduce M) \<le> Lng M"
proof (cases "entry M 1 0 = 0")
  case True
  have "coreReduce M = map (\<lambda>j. (entry M 0 j - entry M 0 0, entry M 1 j)) [0..<Lng M]"
    using True by (simp add: coreReduce_def)
  hence "Lng (coreReduce M) = Lng M" by simp
  thus ?thesis by (simp add: betaM_def)
next
  case False
  let ?m = "entry M 1 0"
  let ?k = "?m - 1"
  let ?rest = "(IncrFirst ^^ ?m) M"
  have m1: "?m \<ge> 1" using False by simp
  have L0: "0 < Lng M" using T by (cases M) (auto simp: T_PS_def)
  have cr: "coreReduce M = diagSeq 0 ?k @ ?rest" using False by (simp add: coreReduce_def)
  have lenr: "Lng ?rest = Lng M" by simp
  have ne: "?rest \<noteq> []" using L0 lenr by (metis length_greater_0_conv)
  have er0: "entry ?rest 0 0 = entry M 0 0 + ?m" by (rule entry_funpow_IncrFirst0[OF L0])
  have er1: "entry ?rest 1 0 = entry M 1 0" by (rule entry_funpow_IncrFirst1[OF L0])
  have r0: "?k < entry ?rest 0 0" using m1 er0 by simp
  have r1: "?k < entry ?rest 1 0" using m1 er1 by simp
  have trge: "Suc ?k \<le> TrMax (coreReduce M)"
    using cr TrMax_diagSeq_append_ge[OF ne r0 r1] by simp
  have lenc: "Lng (coreReduce M) = Suc ?k + Lng M" using cr by simp
  have "betaM (coreReduce M) = (Suc ?k + Lng M) - TrMax (coreReduce M)"
    by (simp add: betaM_def lenc)
  also have "\<dots> \<le> (Suc ?k + Lng M) - Suc ?k" using trge by (rule diff_le_mono2)
  also have "\<dots> = Lng M" by simp
  finally show ?thesis .
qed

text \<open>Every \<open>P\<close>-block of a non-empty sequence is non-empty (the cut
  \<open>0 < Pcut M \<le> Lng M - 1\<close> keeps both \<open>take\<close> and \<open>drop\<close> halves non-empty).
  Needed e.g. for \<open>Lng (Br M ! J) = Lng (N\<^sub>J)\<close>.\<close>

lemma P_blocks_nonempty:
  assumes "M \<noteq> []"
  shows "\<forall>B \<in> set (P M). B \<noteq> []"
proof -
  have "M \<noteq> [] \<longrightarrow> (\<forall>B \<in> set (P M). B \<noteq> [])"
  proof (induction M rule: P.induct)
    case (1 M)
    show ?case
    proof (rule impI)
      assume ne: "M \<noteq> []"
      show "\<forall>B \<in> set (P M). B \<noteq> []"
      proof (cases "multiT M \<and> 1 < Lng M")
        case True
        let ?c = "Pcut M"
        have L: "1 < Lng M" using True by simp
        have step: "P M = P (take ?c M) @ [drop ?c M]" using True by (subst P.simps) simp
        have cge: "0 < ?c" and cle: "?c \<le> Lng M - 1" using Pcut_le[OF L] by auto
        have tne: "take ?c M \<noteq> []" using cge ne by (simp add: take_eq_Nil)
        have IH: "\<forall>B \<in> set (P (take ?c M)). B \<noteq> []" using "1.IH"[OF True] tne by blast
        have dne: "drop ?c M \<noteq> []" using cle L by (simp add: drop_eq_Nil)
        show ?thesis using step IH dne by auto
      next
        case False
        note nc = this
        have "P M = [M]" by (subst P.simps) (rule if_not_P[OF nc])
        thus ?thesis using ne by simp
      qed
    qed
  qed
  thus ?thesis using assms by blast
qed

text \<open>Row-0 minimality of a mono sequence: \<open>M\<^bsub>0,0\<^esub> < M\<^bsub>0,j\<^esub>\<close> for every
  \<open>0 < j < Lng M\<close> (the left end is the strict row-0 minimum).  This is the fact
  that makes the \<open>m\<^sub>1\<^sub>0 = 0\<close> row-0 shift in \<open>coreReduce\<close> order-preserving (no
  \<open>nat\<close> truncation), via @{thm [source] m_5_1_ancestor_basic_1} and \<open>monoT\<close>.\<close>

lemma monoT_row0_min:
  assumes M: "M \<in> T_PS" and mono: "monoT M" and j: "0 < j" "j < Lng M"
  shows "entry M 0 0 < entry M 0 j"
proof -
  have le: "leR M 0 0 (Lng M - 1)" using mono by (simp add: monoT_def)
  have jle: "j \<le> Lng M - 1" using j by simp
  show ?thesis by (rule m_5_1_ancestor_basic_1[OF M j(1) jle le])
qed

text \<open>The row-0 shift used by \<open>coreReduce\<close> in the \<open>m\<^sub>1\<^sub>0 = 0\<close> case: subtract
  \<open>M\<^bsub>0,0\<^esub>\<close> from row 0, keep row 1.  For a mono \<open>M\<close> the left end is the row-0
  minimum (@{thm [source] monoT_row0_min}), so the subtraction is
  order-preserving and \<open>shiftRow0\<close> stays mono.\<close>

definition shiftRow0 :: "pairseq \<Rightarrow> pairseq" where
  "shiftRow0 M = map (\<lambda>j. (entry M 0 j - entry M 0 0, entry M 1 j)) [0..<Lng M]"

lemma Lng_shiftRow0[simp]: "Lng (shiftRow0 M) = Lng M"
  by (simp add: shiftRow0_def)

lemma entry_shiftRow0_0:
  "j < Lng M \<Longrightarrow> entry (shiftRow0 M) 0 j = entry M 0 j - entry M 0 0"
  by (simp add: shiftRow0_def entry_def)

lemma entry_shiftRow0_1:
  "j < Lng M \<Longrightarrow> entry (shiftRow0 M) 1 j = entry M 1 j"
  by (simp add: shiftRow0_def entry_def)

lemma entry0_ge_min:
  assumes M: "M \<in> T_PS" and mono: "monoT M" and j: "j < Lng M"
  shows "entry M 0 0 \<le> entry M 0 j"
proof (cases "j = 0")
  case True thus ?thesis by simp
next
  case False
  hence "0 < j" by simp
  from monoT_row0_min[OF M mono this j] show ?thesis by simp
qed

lemma nextrel0_shiftRow0_eq:
  assumes M: "M \<in> T_PS" and mono: "monoT M"
  shows "nextrel0 (shiftRow0 M) j0 j1 = nextrel0 M j0 j1"
proof (cases "j0 < Lng M \<and> j1 < Lng M")
  case True
  hence j0L: "j0 < Lng M" and j1L: "j1 < Lng M" by simp_all
  let ?c = "entry M 0 0"
  have e0: "entry (shiftRow0 M) 0 j0 = entry M 0 j0 - ?c" using j0L by (rule entry_shiftRow0_0)
  have e1: "entry (shiftRow0 M) 0 j1 = entry M 0 j1 - ?c" using j1L by (rule entry_shiftRow0_0)
  have gj0: "?c \<le> entry M 0 j0" using entry0_ge_min[OF M mono j0L] .
  have gj1: "?c \<le> entry M 0 j1" using entry0_ge_min[OF M mono j1L] .
  have lt_iff: "(entry M 0 j0 - ?c < entry M 0 j1 - ?c) = (entry M 0 j0 < entry M 0 j1)"
    using gj0 gj1 by linarith
  have ge_iff: "\<forall>j. j0 < j \<and> j < j1 \<longrightarrow>
                  (entry (shiftRow0 M) 0 j \<ge> entry (shiftRow0 M) 0 j1)
                  = (entry M 0 j \<ge> entry M 0 j1)"
  proof (intro allI impI)
    fix j assume jb: "j0 < j \<and> j < j1"
    hence jL: "j < Lng M" using j1L by simp
    have ej: "entry (shiftRow0 M) 0 j = entry M 0 j - ?c" using jL by (rule entry_shiftRow0_0)
    have gj: "?c \<le> entry M 0 j" using entry0_ge_min[OF M mono jL] .
    show "(entry (shiftRow0 M) 0 j \<ge> entry (shiftRow0 M) 0 j1)
            = (entry M 0 j \<ge> entry M 0 j1)"
      using ej e1 gj gj1 by linarith
  qed
  show ?thesis
    unfolding nextrel0_def
    using e0 e1 lt_iff ge_iff by (simp add: Lng_shiftRow0 cong: conj_cong)
next
  case False
  thus ?thesis by (auto simp: nextrel0_def Lng_shiftRow0)
qed

lemma le0_shiftRow0_eq:
  assumes M: "M \<in> T_PS" and mono: "monoT M"
  shows "le0 (shiftRow0 M) j0 j1 = le0 M j0 j1"
proof -
  have "nextrel0 (shiftRow0 M) = nextrel0 M"
    by (intro ext) (rule nextrel0_shiftRow0_eq[OF M mono])
  thus ?thesis by (simp add: le0_def Lng_shiftRow0)
qed

text \<open>m: row-1 is untouched by \<open>shiftRow0\<close> and \<open>le0\<close> is preserved (above), so
  \<open>nextrel1\<close> is preserved.  Function-level so it rewrites under \<open>\<^sup>*\<^sup>*\<close> in \<open>le1\<close>.\<close>

lemma nextrel1_shiftRow0_eq:
  assumes M: "M \<in> T_PS" and mono: "monoT M"
  shows "nextrel1 (shiftRow0 M) = nextrel1 M"
proof (intro ext)
  fix j0 j1
  have le0eq: "le0 (shiftRow0 M) = le0 M"
    by (intro ext) (rule le0_shiftRow0_eq[OF M mono])
  have "nextrel1 (shiftRow0 M) j0 j1 \<longleftrightarrow>
        (j0 < Lng M \<and> j1 < Lng M \<and> j0 < j1 \<and>
         entry (shiftRow0 M) 1 j0 < entry (shiftRow0 M) 1 j1 \<and>
         le0 M j0 j1 \<and>
         (\<forall>j. j0 < j \<and> le0 M j j1 \<longrightarrow>
              entry (shiftRow0 M) 1 j \<ge> entry (shiftRow0 M) 1 j1))"
    unfolding nextrel1_def by (simp add: le0eq Lng_shiftRow0)
  also have "\<dots> \<longleftrightarrow> nextrel1 M j0 j1"
  proof (cases "j0 < Lng M \<and> j1 < Lng M")
    case False thus ?thesis by (auto simp: nextrel1_def le0_def)
  next
    case True
    then have jb: "j0 < Lng M" "j1 < Lng M" by auto
    have e1j0: "entry (shiftRow0 M) 1 j0 = entry M 1 j0"
      using jb(1) by (rule entry_shiftRow0_1)
    have e1j1: "entry (shiftRow0 M) 1 j1 = entry M 1 j1"
      using jb(2) by (rule entry_shiftRow0_1)
    have q: "(\<forall>j. j0 < j \<and> le0 M j j1 \<longrightarrow>
                entry (shiftRow0 M) 1 j \<ge> entry (shiftRow0 M) 1 j1)
           = (\<forall>j. j0 < j \<and> le0 M j j1 \<longrightarrow> entry M 1 j \<ge> entry M 1 j1)"
    proof (intro iffI allI impI)
      fix j assume H: "\<forall>j. j0 < j \<and> le0 M j j1 \<longrightarrow>
                          entry (shiftRow0 M) 1 j \<ge> entry (shiftRow0 M) 1 j1"
        and jr: "j0 < j \<and> le0 M j j1"
      from jr have jL: "j < Lng M" by (simp add: le0_def)
      have ej: "entry (shiftRow0 M) 1 j = entry M 1 j" using jL by (rule entry_shiftRow0_1)
      from H jr have "entry (shiftRow0 M) 1 j1 \<le> entry (shiftRow0 M) 1 j" by blast
      thus "entry M 1 j1 \<le> entry M 1 j" using e1j1 ej by simp
    next
      fix j assume H: "\<forall>j. j0 < j \<and> le0 M j j1 \<longrightarrow> entry M 1 j1 \<le> entry M 1 j"
        and jr: "j0 < j \<and> le0 M j j1"
      from jr have jL: "j < Lng M" by (simp add: le0_def)
      have ej: "entry (shiftRow0 M) 1 j = entry M 1 j" using jL by (rule entry_shiftRow0_1)
      from H jr have "entry M 1 j1 \<le> entry M 1 j" by blast
      thus "entry (shiftRow0 M) 1 j1 \<le> entry (shiftRow0 M) 1 j" using e1j1 ej by simp
    qed
    have lt: "(entry (shiftRow0 M) 1 j0 < entry (shiftRow0 M) 1 j1)
            = (entry M 1 j0 < entry M 1 j1)" using e1j0 e1j1 by simp
    show ?thesis
      unfolding nextrel1_def using jb lt q
      by (simp add: Lng_shiftRow0 le0eq)
  qed
  finally show "nextrel1 (shiftRow0 M) j0 j1 = nextrel1 M j0 j1" .
qed

lemma monoT_shiftRow0:
  assumes M: "M \<in> T_PS" and mono: "monoT M"
  shows "monoT (shiftRow0 M)"
proof -
  have nz: "\<not> zeroT (shiftRow0 M)"
  proof -
    have "zeroT (shiftRow0 M) = zeroT M"
    proof (cases "Lng M = 1")
      case True
      hence "0 < Lng M" by simp
      hence "entry (shiftRow0 M) 1 0 = entry M 1 0" by (rule entry_shiftRow0_1)
      thus ?thesis using True by (simp add: zeroT_def Lng_shiftRow0)
    next
      case False
      thus ?thesis by (simp add: zeroT_def Lng_shiftRow0)
    qed
    thus ?thesis using mono by (simp add: monoT_def)
  qed
  have "leR M 0 0 (Lng M - 1)" using mono by (simp add: monoT_def)
  hence "leR (shiftRow0 M) 0 0 (Lng (shiftRow0 M) - 1)"
    by (simp add: leR_def Lng_shiftRow0 le0_shiftRow0_eq[OF M mono])
  thus ?thesis using nz by (simp add: monoT_def)
qed

text \<open>\<open>coreReduce M\<close> is mono (hence non-multi) in the \<open>m\<^sub>1\<^sub>0 = 0\<close> case:
  there it equals @{const shiftRow0}, which preserves \<open>monoT\<close>.\<close>

lemma coreReduce_monoT_m10_0:
  assumes M: "M \<in> T_PS" and mono: "monoT M" and z: "entry M 1 0 = 0"
  shows "monoT (coreReduce M)"
proof -
  have "coreReduce M = shiftRow0 M" using z by (simp add: coreReduce_def shiftRow0_def)
  thus ?thesis using monoT_shiftRow0[OF M mono] by simp
qed

text \<open>Entry of \<open>diagSeq 0 k @ rest\<close> on the \<open>rest\<close> part (index \<open>Suc k + a\<close>).\<close>

lemma entry_diagSeq_append_hi:
  assumes "a < Lng rest"
  shows "entry (diagSeq 0 k @ rest) p (Suc k + a) = entry rest p a"
proof -
  have "(diagSeq 0 k @ rest) ! (Suc k + a) = rest ! a" by (simp add: nth_append)
  thus ?thesis by (simp add: entry_def)
qed

lemma monoT_funpow_IncrFirst[simp]: "monoT ((IncrFirst ^^ k) M) = monoT M"
  by (induction k) (simp_all add: IncrFirst_monoT_eq)

text \<open>If a mono \<open>rest\<close> starts strictly above the diagonal in row 0, prepending the
  diagonal \<open>diagSeq 0 k\<close> keeps it mono: row 0 is \<open>> 0\<close> at every index after \<open>0\<close>,
  so @{thm [source] le0_build} gives \<open>(0,0) \<le>\<^bsub>M\<^esub> (0, Lng-1)\<close>.  This is the
  row-0 analogue of @{thm [source] TrMax_diagSeq_append_ge}; it discharges the
  \<open>m\<^sub>1\<^sub>0 > 0\<close> case of "coreReduce is mono".\<close>

lemma monoT_diagSeq_append:
  assumes ne: "rest \<noteq> []" and rmono: "monoT rest" and rTPS: "rest \<in> T_PS"
    and r0: "k < entry rest 0 0"
  shows "monoT (diagSeq 0 k @ rest)"
proof -
  let ?M = "diagSeq 0 k @ rest"
  have lenr: "0 < Lng rest" using ne by (cases rest) auto
  have lenM: "Lng ?M = Suc k + Lng rest" by simp
  have MTPS: "?M \<in> T_PS" using ne by (simp add: T_PS_def)
  have e00: "entry ?M 0 0 = 0" using entry_diagSeq_append_lo[where i=0 and k=k and rest=rest] by simp
  have key: "\<And>j. 0 < j \<Longrightarrow> j \<le> Lng ?M - 1 \<Longrightarrow> 0 < entry ?M 0 j"
  proof -
    fix j assume j0: "0 < j" and jle: "j \<le> Lng ?M - 1"
    show "0 < entry ?M 0 j"
    proof (cases "j \<le> k")
      case True
      hence "entry ?M 0 j = j" by (rule entry_diagSeq_append_lo)
      thus ?thesis using j0 by simp
    next
      case False
      hence kj: "k < j" by simp
      let ?a = "j - Suc k"
      have ja: "j = Suc k + ?a" using kj by simp
      have aL: "?a < Lng rest" using jle lenM kj by linarith
      have "entry ?M 0 j = entry rest 0 ?a"
        using ja entry_diagSeq_append_hi[OF aL, where k=k and p=0] by simp
      moreover have "entry rest 0 0 \<le> entry rest 0 ?a"
        using entry0_ge_min[OF rTPS rmono aL] .
      ultimately show ?thesis using r0 by simp
    qed
  qed
  have j1lt: "Lng ?M - 1 < Lng ?M" using lenM lenr by simp
  have j0lt: "(0::nat) < Lng ?M - 1" using lenM lenr by simp
  have "(nextrel0 ?M)\<^sup>*\<^sup>* 0 (Lng ?M - 1)"
  proof (rule le0_build[OF MTPS j1lt j0lt])
    show "\<forall>j. 0 < j \<and> j \<le> Lng ?M - 1 \<longrightarrow> entry ?M 0 0 < entry ?M 0 j"
      using key e00 by simp
  qed
  hence "le0 ?M 0 (Lng ?M - 1)" using j1lt by (simp add: le0_def)
  hence "leR ?M 0 0 (Lng ?M - 1)" by (simp add: leR_def)
  moreover have "\<not> zeroT ?M" using lenM lenr by (simp add: zeroT_def)
  ultimately show ?thesis by (simp add: monoT_def)
qed

lemma coreReduce_monoT_m10_pos:
  assumes M: "M \<in> T_PS" and mono: "monoT M" and pos: "0 < entry M 1 0"
  shows "monoT (coreReduce M)"
proof -
  let ?m = "entry M 1 0"
  let ?rest = "(IncrFirst ^^ ?m) M"
  have L0: "0 < Lng M" using M by (cases M) (auto simp: T_PS_def)
  have cr: "coreReduce M = diagSeq 0 (?m - 1) @ ?rest" using pos by (simp add: coreReduce_def)
  have lenr: "Lng ?rest = Lng M" by simp
  have ne: "?rest \<noteq> []" using L0 lenr by (metis length_greater_0_conv)
  have rTPS: "?rest \<in> T_PS" using ne by (simp add: T_PS_def)
  have rmono: "monoT ?rest" using mono by simp
  have "entry ?rest 0 0 = entry M 0 0 + ?m" by (rule entry_funpow_IncrFirst0[OF L0])
  hence r0: "?m - 1 < entry ?rest 0 0" using pos by simp
  show ?thesis using cr monoT_diagSeq_append[OF ne rmono rTPS r0] by simp
qed

text \<open>m: \<open>coreReduce M\<close> is non-multi (mono) for any non-core mono \<open>M\<close> — the
  case-3/4 obligation that makes the global measure \<open>\<nu>\<close> well-behaved.\<close>

lemma coreReduce_nonmulti:
  assumes M: "M \<in> T_PS" and mono: "monoT M"
  shows "\<not> multiT (coreReduce M)"
proof (cases "entry M 1 0 = 0")
  case True
  from coreReduce_monoT_m10_0[OF M mono True] show ?thesis by (simp add: multiT_def)
next
  case False
  hence "0 < entry M 1 0" by simp
  from coreReduce_monoT_m10_pos[OF M mono this] show ?thesis by (simp add: multiT_def)
qed

text \<open>The trunk holds up to \<open>TrMax M\<close>: the row-1 chain \<open>(1,j) <\<^sup>Next (1,j+1)\<close>
  is unbroken for every \<open>j < TrMax M\<close>.  (\<open>TrMax M = Max ?S\<close> lies in the
  downward-closed finite set \<open>?S\<close>.)\<close>

lemma TrMax_in_S:
  assumes T: "M \<in> T_PS"
  shows "\<forall>j'<TrMax M. nextR M 1 j' (j' + 1)"
proof -
  let ?S = "{j. \<forall>j'<j. nextR M 1 j' (j' + 1)}"
  have LM: "Lng M > 0" using T by (cases M) (auto simp: T_PS_def)
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
  have "0 \<in> ?S" by simp
  hence ne: "?S \<noteq> {}" by blast
  have "Max ?S \<in> ?S" by (rule Max_in[OF fin ne])
  thus ?thesis by (simp add: TrMax_def)
qed

text \<open>m: row-0 grows by at least 1 per step along the trunk:
  \<open>M\<^bsub>0,0\<^esub> + j \<le> M\<^bsub>0,j\<^esub>\<close> for \<open>j \<le> TrMax M\<close>.  (Each trunk step gives a row-0
  \<open>\<le>\<^sub>M\<close>-edge, hence a strict row-0 increase.)\<close>

lemma trunk_row0_inc:
  assumes T: "M \<in> T_PS" and jt: "j \<le> TrMax M" and jL: "j < Lng M"
  shows "entry M 0 0 + j \<le> entry M 0 j"
  using jt jL
proof (induction j)
  case 0 thus ?case by simp
next
  case (Suc j')
  have jt': "j' < TrMax M" using Suc.prems(1) by simp
  have nx: "nextR M 1 j' (Suc j')" using TrMax_in_S[OF T] jt' by simp
  have le: "leR M 0 j' (Suc j')" using nx by (auto simp: leR_def nextR_def nextrel1_def)
  have inc: "entry M 0 j' < entry M 0 (Suc j')"
    by (rule m_5_1_ancestor_basic_1[OF T _ _ le]) auto
  have IH: "entry M 0 0 + j' \<le> entry M 0 j'" using Suc by simp
  show ?case using inc IH by simp
qed

end
