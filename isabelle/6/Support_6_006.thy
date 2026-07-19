theory Support_6_006
  imports Frontier_6_022
begin

lemma le1_funpow_IncrFirst_eq: "le1 ((IncrFirst ^^ k) M) = le1 M"
  by (induction k) (simp_all add: le1_IncrFirst_eq)

text \<open>m: \<open>le1\<close> seg-shift (full RTC version of @{thm [source] adm_nextrel1_seg}),
  mirroring @{thm [source] adm_le0_seg}.  Both directions transfer a row-1 chain
  across the slice via @{thm [source] adm_nextrel1_seg}.\<close>

lemma adm_le1_seg_M_to_N:
  assumes "j1' < Lng M" "(nextrel1 M)\<^sup>*\<^sup>* (j0' + a) c" "c \<le> j1'"
  shows "(nextrel1 (seg M j0' j1'))\<^sup>*\<^sup>* a (c - j0')"
  using assms(2,3)
proof (induction rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step y z)
  have ge0: "j0' + a \<le> y" using step.hyps(1) by (rule nextrel1_rtrancl_mono)
  have yz: "y < z" using step.hyps(2) by (simp add: nextrel1_def)
  have yj1: "y \<le> j1'" using yz step.prems by simp
  have IHy: "(nextrel1 (seg M j0' j1'))\<^sup>*\<^sup>* a (y - j0')" using step.IH yj1 by simp
  have yN: "y - j0' < Lng (seg M j0' j1')" using yj1 ge0 by simp
  have zN: "z - j0' < Lng (seg M j0' j1')" using step.prems ge0 yz by simp
  have "j0' + (y - j0') = y" using ge0 by simp
  moreover have "j0' + (z - j0') = z" using ge0 yz by simp
  ultimately have "nextrel1 (seg M j0' j1') (y - j0') (z - j0')"
    using adm_nextrel1_seg[OF assms(1) yN zN] step.hyps(2) by simp
  with IHy show ?case by (rule rtranclp.rtrancl_into_rtrancl)
qed

lemma adm_le1_seg_N_to_M:
  assumes "j1' < Lng M" "(nextrel1 (seg M j0' j1'))\<^sup>*\<^sup>* a b"
  shows "(nextrel1 M)\<^sup>*\<^sup>* (j0' + a) (j0' + b)"
  using assms(2)
proof (induction rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step y z)
  have yz: "y < z" using step.hyps(2) by (simp add: nextrel1_def)
  have zN: "z < Lng (seg M j0' j1')" using step.hyps(2) by (simp add: nextrel1_def)
  have yN: "y < Lng (seg M j0' j1')" using yz zN by simp
  have "nextrel1 M (j0' + y) (j0' + z)"
    using adm_nextrel1_seg[OF assms(1) yN zN] step.hyps(2) by simp
  with step.IH show ?case by (rule rtranclp.rtrancl_into_rtrancl)
qed

lemma adm_le1_seg:
  assumes "j1' < Lng M" "a \<le> j1' - j0'" "b \<le> j1' - j0'" "j0' \<le> j1'"
  shows "le1 (seg M j0' j1') a b \<longleftrightarrow> le1 M (j0' + a) (j0' + b)"
proof
  assume "le1 (seg M j0' j1') a b"
  hence ch: "(nextrel1 (seg M j0' j1'))\<^sup>*\<^sup>* a b"
    and aN: "a < Lng (seg M j0' j1')" and bN: "b < Lng (seg M j0' j1')"
    by (simp_all add: le1_def)
  have "(nextrel1 M)\<^sup>*\<^sup>* (j0' + a) (j0' + b)"
    by (rule adm_le1_seg_N_to_M[OF assms(1) ch])
  moreover have "j0' + a < Lng M" using aN assms(1) by simp
  moreover have "j0' + b < Lng M" using bN assms(1) by simp
  ultimately show "le1 M (j0' + a) (j0' + b)" by (simp add: le1_def)
next
  assume "le1 M (j0' + a) (j0' + b)"
  hence ch: "(nextrel1 M)\<^sup>*\<^sup>* (j0' + a) (j0' + b)" by (simp add: le1_def)
  have cj1: "j0' + b \<le> j1'" using assms(3,4) by simp
  have "(nextrel1 (seg M j0' j1'))\<^sup>*\<^sup>* a (j0' + b - j0')"
    by (rule adm_le1_seg_M_to_N[OF assms(1) ch cj1])
  hence "(nextrel1 (seg M j0' j1'))\<^sup>*\<^sup>* a b" by simp
  moreover have "a < Lng (seg M j0' j1')" using assms(2,4) by simp
  moreover have "b < Lng (seg M j0' j1')" using assms(3,4) by simp
  ultimately show "le1 (seg M j0' j1') a b" by (simp add: le1_def)
qed

text \<open>m: fact2a (PRE-Red ancestor index-shift).  With
  \<open>arg = ((j,j))\<^bsub>j=0\<^esub>\<^bsup>m\<^sub>1\<^sub>0-1\<^esup> \<oplus> IncrFirst\<^bsup>m\<^sub>1\<^sub>0\<^esup>(M)\<close> (\<open>m\<^sub>1\<^sub>0 = M\<^bsub>1,0\<^esub> > 0\<close>), the
  diagonal prefix has length \<open>m\<^sub>1\<^sub>0\<close>, so the tail of \<open>arg\<close> at index \<open>m\<^sub>1\<^sub>0\<close> is
  \<open>seg arg m\<^sub>1\<^sub>0 (Lng arg - 1) = IncrFirst\<^bsup>m\<^sub>1\<^sub>0\<^esup>(M)\<close>.  Hence the slice-shift facts
  @{thm [source] adm_le0_seg}/@{thm [source] adm_le1_seg} together with the
  \<open>IncrFirst\<close>-invariance of \<open>le0\<close>/\<open>le1\<close> give
  \<open>leR M i j j' \<longleftrightarrow> leR arg i (j+m\<^sub>1\<^sub>0) (j'+m\<^sub>1\<^sub>0)\<close>.  This is the index-shift
  the article cites in §6.5 命題（単項性と Red の関係） (content.md 952-956),
  stated PRE-Red (no \<open>Red\<close> is applied yet).\<close>

lemma m_6_5_monoT_Red_fact2a_leR_shift:
  assumes MT: "M \<in> T_PS" and m10pos: "0 < entry M 1 0"
    and i: "i = 0 \<or> i = 1" and jL: "j < Lng M" and jpL: "j' < Lng M"
  shows "leR M i j j'
           = leR (diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ (entry M 1 0)) M)
                 i (j + entry M 1 0) (j' + entry M 1 0)"
proof -
  let ?m10 = "entry M 1 0"
  let ?rest = "(IncrFirst ^^ ?m10) M"
  let ?arg = "diagSeq 0 (?m10 - 1) @ ?rest"
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have LM: "0 < Lng M" using Mne by (cases M) auto
  \<comment> \<open>geometry of arg\<close>
  have Ldiag: "Lng (diagSeq 0 (?m10 - 1)) = ?m10" using m10pos by (simp del: upt_Suc)
  have Lrest: "Lng ?rest = Lng M" by simp
  have Larg: "Lng ?arg = Lng M + ?m10" using Ldiag Lrest by simp
  have argpos: "0 < Lng ?arg" using Larg LM by simp
  have m10lt: "?m10 < Lng ?arg" using Larg LM by simp
  \<comment> \<open>tail of arg at index m10 is exactly rest\<close>
  have tail: "seg ?arg ?m10 (Lng ?arg - 1) = ?rest"
  proof -
    have "seg ?arg ?m10 (Lng ?arg - 1) = drop ?m10 ?arg"
      by (rule drop_eq_seg[OF m10lt, symmetric])
    also have "\<dots> = ?rest" using Ldiag by simp
    finally show ?thesis .
  qed
  have Largm1: "Lng ?arg - 1 < Lng ?arg" using argpos by simp
  \<comment> \<open>seg-slice shift facts specialised to (M:=arg, j0':=m10, j1':=Lng arg - 1)\<close>
  have inrange_j:  "j  \<le> (Lng ?arg - 1) - ?m10" using jL Larg by simp
  have inrange_jp: "j' \<le> (Lng ?arg - 1) - ?m10" using jpL Larg by simp
  have le_m10:     "?m10 \<le> Lng ?arg - 1" using m10lt by simp
  show ?thesis
  proof (cases "i = 0")
    case True
    have "leR ?arg 0 (j + ?m10) (j' + ?m10) = le0 ?arg (?m10 + j) (?m10 + j')"
      by (simp add: leR_def add.commute)
    also have "\<dots> = le0 (seg ?arg ?m10 (Lng ?arg - 1)) j j'"
      using adm_le0_seg[OF Largm1 inrange_j inrange_jp le_m10] by simp
    also have "\<dots> = le0 ?rest j j'" using tail by simp
    also have "\<dots> = le0 M j j'" by (simp add: le0_funpow_IncrFirst_eq)
    also have "\<dots> = leR M 0 j j'" by (simp add: leR_def)
    finally show ?thesis using True by simp
  next
    case False
    hence i1: "i = 1" using i by simp
    have "leR ?arg 1 (j + ?m10) (j' + ?m10) = le1 ?arg (?m10 + j) (?m10 + j')"
      by (simp add: leR_def add.commute)
    also have "\<dots> = le1 (seg ?arg ?m10 (Lng ?arg - 1)) j j'"
      using adm_le1_seg[OF Largm1 inrange_j inrange_jp le_m10] by simp
    also have "\<dots> = le1 ?rest j j'" using tail by simp
    also have "\<dots> = le1 M j j'" by (simp add: le1_funpow_IncrFirst_eq)
    also have "\<dots> = leR M 1 j j'" by (simp add: leR_def)
    finally show ?thesis using i1 by simp
  qed
qed

end
