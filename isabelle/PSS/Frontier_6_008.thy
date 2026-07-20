theory Frontier_6_008
  imports P_6_2_P_components_1
begin

subsection \<open>§6.3 許容性\<close>

text \<open>
  THE KEY HELPER for the §6.3 slice lemmas.  For a slice \<open>N = seg M j0' j1'\<close>
  (with \<open>j1' < Lng M\<close>) the row-0 \<open><\<^sup>Next\<close> relation on \<open>N\<close> corresponds
  exactly to that on \<open>M\<close>, shifted by \<open>j0'\<close>, on the index range of \<open>N\<close>.
  Both \<open>nextrel0 N a b\<close> and \<open>nextrel0 M (j0'+a) (j0'+b)\<close> have the same shape;
  the middle-condition quantifiers correspond under \<open>j' = j0'+j\<close>, and the
  length bounds agree because \<open>b < Lng N \<longleftrightarrow> j0'+b \<le> j1' < Lng M\<close>.
\<close>

lemma adm_nextrel0_seg:
  assumes "j1' < Lng M" "a < Lng (seg M j0' j1')" "b < Lng (seg M j0' j1')"
  shows "nextrel0 (seg M j0' j1') a b \<longleftrightarrow> nextrel0 M (j0' + a) (j0' + b)"
proof -
  let ?N = "seg M j0' j1'"
  have aN: "a < Suc j1' - j0'" and bN: "b < Suc j1' - j0'" using assms(2,3) by simp_all
  have aLM: "j0' + a < Lng M" using aN assms(1) by simp
  have bLM: "j0' + b < Lng M" using bN assms(1) by simp
  have eA: "entry ?N 0 a = entry M 0 (j0' + a)" using assms(2) by (simp add: entry_seg)
  have eB: "entry ?N 0 b = entry M 0 (j0' + b)" using assms(3) by (simp add: entry_seg)
  have mid: "(\<forall>j. a < j \<and> j < b \<longrightarrow> entry ?N 0 j \<ge> entry ?N 0 b)
           = (\<forall>j'. j0' + a < j' \<and> j' < j0' + b \<longrightarrow> entry M 0 j' \<ge> entry M 0 (j0' + b))"
  proof
    assume H: "\<forall>j. a < j \<and> j < b \<longrightarrow> entry ?N 0 j \<ge> entry ?N 0 b"
    show "\<forall>j'. j0' + a < j' \<and> j' < j0' + b \<longrightarrow> entry M 0 j' \<ge> entry M 0 (j0' + b)"
    proof (intro allI impI)
      fix j' assume a': "j0' + a < j' \<and> j' < j0' + b"
      have j0j': "j0' \<le> j'" using a' by simp
      let ?j = "j' - j0'"
      have jN: "?j < Lng ?N" using a' bN j0j' by (simp only: Lng_seg) linarith
      have "a < ?j \<and> ?j < b" using a' j0j' by linarith
      hence "entry ?N 0 ?j \<ge> entry ?N 0 b" using H by blast
      moreover have "entry ?N 0 ?j = entry M 0 j'" using jN a' by (simp add: entry_seg)
      ultimately show "entry M 0 j' \<ge> entry M 0 (j0' + b)" using eB by simp
    qed
  next
    assume H: "\<forall>j'. j0' + a < j' \<and> j' < j0' + b \<longrightarrow> entry M 0 j' \<ge> entry M 0 (j0' + b)"
    show "\<forall>j. a < j \<and> j < b \<longrightarrow> entry ?N 0 j \<ge> entry ?N 0 b"
    proof (intro allI impI)
      fix j assume aj: "a < j \<and> j < b"
      hence jN: "j < Lng ?N" using bN by simp
      have ej: "entry ?N 0 j = entry M 0 (j0' + j)" using jN by (simp add: entry_seg)
      have "j0' + a < j0' + j \<and> j0' + j < j0' + b" using aj by simp
      hence "entry M 0 (j0' + j) \<ge> entry M 0 (j0' + b)" using H by blast
      thus "entry ?N 0 j \<ge> entry ?N 0 b" using ej eB by simp
    qed
  qed
  have "nextrel0 ?N a b \<longleftrightarrow>
        (a < Lng ?N \<and> b < Lng ?N \<and> a < b \<and> entry ?N 0 a < entry ?N 0 b \<and>
         (\<forall>j. a < j \<and> j < b \<longrightarrow> entry ?N 0 j \<ge> entry ?N 0 b))"
    by (simp add: nextrel0_def)
  also have "\<dots> \<longleftrightarrow>
        (j0' + a < Lng M \<and> j0' + b < Lng M \<and> j0' + a < j0' + b \<and>
         entry M 0 (j0' + a) < entry M 0 (j0' + b) \<and>
         (\<forall>j'. j0' + a < j' \<and> j' < j0' + b \<longrightarrow> entry M 0 j' \<ge> entry M 0 (j0' + b)))"
    using assms(2,3) aLM bLM eA eB mid by auto
  also have "\<dots> \<longleftrightarrow> nextrel0 M (j0' + a) (j0' + b)"
    by (simp add: nextrel0_def)
  finally show ?thesis .
qed

text \<open>An \<open>M\<close>-chain inside \<open>[j0'..j1']\<close> transfers to an \<open>N\<close>-chain (shifted).\<close>

lemma adm_le0_seg_M_to_N:
  assumes "j1' < Lng M" "(nextrel0 M)\<^sup>*\<^sup>* (j0' + a) c" "c \<le> j1'"
  shows "(nextrel0 (seg M j0' j1'))\<^sup>*\<^sup>* a (c - j0')"
  using assms(2,3)
proof (induction rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step y z)
  have ge0: "j0' + a \<le> y" using step.hyps(1) by (rule nextrel0_rtrancl_mono)
  have yz: "y < z" using step.hyps(2) by (simp add: nextrel0_def)
  have yj1: "y \<le> j1'" using yz step.prems by simp
  have IHy: "(nextrel0 (seg M j0' j1'))\<^sup>*\<^sup>* a (y - j0')" using step.IH yj1 by simp
  have yN: "y - j0' < Lng (seg M j0' j1')" using yj1 ge0 by simp
  have zN: "z - j0' < Lng (seg M j0' j1')" using step.prems ge0 yz by simp
  have "j0' + (y - j0') = y" using ge0 by simp
  moreover have "j0' + (z - j0') = z" using ge0 yz by simp
  ultimately have "nextrel0 (seg M j0' j1') (y - j0') (z - j0')"
    using adm_nextrel0_seg[OF assms(1) yN zN] step.hyps(2) by simp
  with IHy show ?case by (rule rtranclp.rtrancl_into_rtrancl)
qed

text \<open>Conversely an \<open>N\<close>-chain transfers to an \<open>M\<close>-chain (shifted up).\<close>

lemma adm_le0_seg_N_to_M:
  assumes "j1' < Lng M" "(nextrel0 (seg M j0' j1'))\<^sup>*\<^sup>* a b"
  shows "(nextrel0 M)\<^sup>*\<^sup>* (j0' + a) (j0' + b)"
  using assms(2)
proof (induction rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step y z)
  have yz: "y < z" using step.hyps(2) by (simp add: nextrel0_def)
  have zN: "z < Lng (seg M j0' j1')" using step.hyps(2) by (simp add: nextrel0_def)
  have yN: "y < Lng (seg M j0' j1')" using yz zN by simp
  have "nextrel0 M (j0' + y) (j0' + z)"
    using adm_nextrel0_seg[OF assms(1) yN zN] step.hyps(2) by simp
  with step.IH show ?case by (rule rtranclp.rtrancl_into_rtrancl)
qed

text \<open>
  Hence \<open>le0\<close> on the slice corresponds to \<open>le0\<close> on \<open>M\<close> shifted by \<open>j0'\<close>, for
  indices in range.
\<close>

lemma adm_le0_seg:
  assumes "j1' < Lng M" "a \<le> j1' - j0'" "b \<le> j1' - j0'" "j0' \<le> j1'"
  shows "le0 (seg M j0' j1') a b \<longleftrightarrow> le0 M (j0' + a) (j0' + b)"
proof
  assume "le0 (seg M j0' j1') a b"
  hence ch: "(nextrel0 (seg M j0' j1'))\<^sup>*\<^sup>* a b"
    and aN: "a < Lng (seg M j0' j1')" and bN: "b < Lng (seg M j0' j1')"
    by (simp_all add: le0_def)
  have "(nextrel0 M)\<^sup>*\<^sup>* (j0' + a) (j0' + b)"
    by (rule adm_le0_seg_N_to_M[OF assms(1) ch])
  moreover have "j0' + a < Lng M" using aN assms(1) by simp
  moreover have "j0' + b < Lng M" using bN assms(1) by simp
  ultimately show "le0 M (j0' + a) (j0' + b)" by (simp add: le0_def)
next
  assume "le0 M (j0' + a) (j0' + b)"
  hence ch: "(nextrel0 M)\<^sup>*\<^sup>* (j0' + a) (j0' + b)" by (simp add: le0_def)
  have cj1: "j0' + b \<le> j1'" using assms(3,4) by simp
  have "(nextrel0 (seg M j0' j1'))\<^sup>*\<^sup>* a (j0' + b - j0')"
    by (rule adm_le0_seg_M_to_N[OF assms(1) ch cj1])
  hence "(nextrel0 (seg M j0' j1'))\<^sup>*\<^sup>* a b" by simp
  moreover have "a < Lng (seg M j0' j1')" using assms(2,4) by simp
  moreover have "b < Lng (seg M j0' j1')" using assms(3,4) by simp
  ultimately show "le0 (seg M j0' j1') a b" by (simp add: le0_def)
qed

text \<open>
  The row-1 \<open><\<^sup>Next\<close> relation also corresponds on the slice interior.  Here
  \<open>nextrel1\<close> additionally constrains the row-1 entries and quantifies over
  \<open>le0 _ j j1\<close>-ancestors; the \<open>le0\<close> correspondence above turns the universal
  condition on \<open>N\<close> into the one on \<open>M\<close>.
\<close>

lemma adm_nextrel1_seg:
  assumes "j1' < Lng M" "a < Lng (seg M j0' j1')" "b < Lng (seg M j0' j1')"
  shows "nextrel1 (seg M j0' j1') a b \<longleftrightarrow> nextrel1 M (j0' + a) (j0' + b)"
proof -
  let ?N = "seg M j0' j1'"
  have aN: "a < Suc j1' - j0'" and bN: "b < Suc j1' - j0'" using assms(2,3) by simp_all
  have j0j1: "j0' \<le> j1'" using bN by simp
  have aLM: "j0' + a < Lng M" using aN assms(1) by simp
  have bLM: "j0' + b < Lng M" using bN assms(1) by simp
  have eA: "entry ?N 1 a = entry M 1 (j0' + a)" using assms(2) by (simp add: entry_seg)
  have eB: "entry ?N 1 b = entry M 1 (j0' + b)" using assms(3) by (simp add: entry_seg)
  have le0AB: "le0 ?N a b \<longleftrightarrow> le0 M (j0' + a) (j0' + b)"
    using adm_le0_seg[OF assms(1) _ _ j0j1] aN bN by simp
  have univ: "(\<forall>j. a < j \<and> le0 ?N j b \<longrightarrow> entry ?N 1 j \<ge> entry ?N 1 b)
            = (\<forall>j'. j0' + a < j' \<and> le0 M j' (j0' + b) \<longrightarrow> entry M 1 j' \<ge> entry M 1 (j0' + b))"
  proof
    assume H: "\<forall>j. a < j \<and> le0 ?N j b \<longrightarrow> entry ?N 1 j \<ge> entry ?N 1 b"
    show "\<forall>j'. j0' + a < j' \<and> le0 M j' (j0' + b) \<longrightarrow> entry M 1 j' \<ge> entry M 1 (j0' + b)"
    proof (intro allI impI)
      fix j' assume a': "j0' + a < j' \<and> le0 M j' (j0' + b)"
      hence le0': "le0 M j' (j0' + b)" by simp
      have j'le: "j' \<le> j0' + b"
      proof -
        have "(nextrel0 M)\<^sup>*\<^sup>* j' (j0' + b)" using le0' by (simp add: le0_def)
        thus ?thesis by (rule nextrel0_rtrancl_mono)
      qed
      have j'ge: "j0' \<le> j'" using a' by simp
      let ?j = "j' - j0'"
      have jb: "?j \<le> j1' - j0'" using j'le bN j0j1 j'ge by linarith
      have aj: "a < ?j" using a' j'ge by linarith
      have le0Nj: "le0 ?N ?j b"
        using adm_le0_seg[OF assms(1) _ _ j0j1] jb bN le0' j'ge by simp
      have ejN: "entry ?N 1 ?j = entry M 1 j'"
        using j'le j'ge bN by (simp add: entry_seg)
      have "entry ?N 1 ?j \<ge> entry ?N 1 b" using H aj le0Nj by blast
      thus "entry M 1 j' \<ge> entry M 1 (j0' + b)" using ejN eB by simp
    qed
  next
    assume H: "\<forall>j'. j0' + a < j' \<and> le0 M j' (j0' + b) \<longrightarrow> entry M 1 j' \<ge> entry M 1 (j0' + b)"
    show "\<forall>j. a < j \<and> le0 ?N j b \<longrightarrow> entry ?N 1 j \<ge> entry ?N 1 b"
    proof (intro allI impI)
      fix j assume aj: "a < j \<and> le0 ?N j b"
      hence le0Nj: "le0 ?N j b" by simp
      have jN: "j < Lng ?N" using le0Nj by (simp add: le0_def)
      have jb: "j \<le> j1' - j0'" using jN by simp
      have le0M: "le0 M (j0' + j) (j0' + b)"
        using adm_le0_seg[OF assms(1) jb _ j0j1] bN le0Nj by simp
      have "j0' + a < j0' + j" using aj by simp
      hence "entry M 1 (j0' + j) \<ge> entry M 1 (j0' + b)" using H le0M by blast
      moreover have "entry ?N 1 j = entry M 1 (j0' + j)" using jN by (simp add: entry_seg)
      ultimately show "entry ?N 1 j \<ge> entry ?N 1 b" using eB by simp
    qed
  qed
  have "nextrel1 ?N a b \<longleftrightarrow>
        (a < Lng ?N \<and> b < Lng ?N \<and> a < b \<and> entry ?N 1 a < entry ?N 1 b \<and>
         le0 ?N a b \<and>
         (\<forall>j. a < j \<and> le0 ?N j b \<longrightarrow> entry ?N 1 j \<ge> entry ?N 1 b))"
    by (simp add: nextrel1_def)
  also have "\<dots> \<longleftrightarrow>
        (j0' + a < Lng M \<and> j0' + b < Lng M \<and> j0' + a < j0' + b \<and>
         entry M 1 (j0' + a) < entry M 1 (j0' + b) \<and>
         le0 M (j0' + a) (j0' + b) \<and>
         (\<forall>j'. j0' + a < j' \<and> le0 M j' (j0' + b) \<longrightarrow> entry M 1 j' \<ge> entry M 1 (j0' + b)))"
    using assms(2,3) aLM bLM eA eB le0AB univ by auto
  also have "\<dots> \<longleftrightarrow> nextrel1 M (j0' + a) (j0' + b)"
    by (simp add: nextrel1_def)
  finally show ?thesis .
qed

text \<open>
  Row-1 \<open>nextR\<close> on the slice interior corresponds to that on \<open>M\<close> shifted by
  \<open>j0'\<close>.  This is the statement the article uses at line 611.
\<close>

lemma adm_nextR1_seg:
  assumes "j1' < Lng M" "a < Lng (seg M j0' j1')" "b < Lng (seg M j0' j1')"
  shows "nextR (seg M j0' j1') 1 a b \<longleftrightarrow> nextR M 1 (j0' + a) (j0' + b)"
  using adm_nextrel1_seg[OF assms] by (simp add: nextR_def)

end
