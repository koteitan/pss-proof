theory pss_paper
  imports pss_defs "HOL-Library.Extended_Nat"
begin

text \<open>
  Faithful transcription of the *statements* (命題 / 補題 / 系 / 定理) of
  P進大好きbot's article "ペア数列の停止性", in the order they appear.

  Every statement here is left as @{command sorry}: this file records WHAT
  the article claims, not the proofs.  Statements whose proof the article
  itself omits, and statements we have simply not yet proved, are all
  @{command sorry} here.  The mechanized proofs live in
  @{file "pss_mechanized.thy"}.

  Naming / traceability: each fact is named \<open>p_<sec>_<slug>\<close> and carries a
  comment with the article section (§) and the original Japanese name, so it
  can be located in @{file "tmp/content.md"}.
\<close>

section \<open>§5 定式化\<close>

subsection \<open>§5.1 親子関係\<close>

text \<open>命題（親の存在の判定条件） — criterion for existence of a parent.\<close>

lemma p_5_1_parent_exists_1:
  assumes "M \<in> T_PS" "j0 < j1" "j1 < Lng M"
  assumes "entry M 0 j0 < entry M 0 j1"
  shows "\<exists>j. j0 \<le> j \<and> j < j1 \<and> nextR M 0 j j1"
  sorry

lemma p_5_1_parent_exists_2:
  assumes "M \<in> T_PS" "j0 < j1" "j1 < Lng M"
  assumes "entry M 1 j0 < entry M 1 j1" "leR M 0 j0 j1"
  shows "\<exists>j. j0 \<le> j \<and> j < j1 \<and> nextR M 1 j j1"
  sorry

lemma p_5_1_parent_exists_3:
  assumes "M \<in> T_PS" "j0 < j1" "j1 < Lng M"
  assumes "\<And>j. j0 < j \<Longrightarrow> j \<le> j1 \<Longrightarrow> entry M 0 j0 < entry M 0 j"
  shows "leR M 0 j0 j1"
  sorry

lemma p_5_1_parent_exists_4:
  assumes "M \<in> T_PS" "j0 < j1" "j1 < Lng M"
  assumes "\<And>j. j0 < j \<Longrightarrow> leR M 0 j j1 \<Longrightarrow> entry M 1 j0 < entry M 1 j"
  assumes "leR M 0 j0 j1"
  shows "leR M 1 j0 j1"
  sorry

text \<open>命題（親の基本性質） — basic property of the parent.\<close>

lemma p_5_1_parent_basic_1:
  assumes "M \<in> T_PS" "j0 < j" "j \<le> j1"
  assumes "nextR M 0 j0 j1"
  shows "entry M 0 j \<ge> entry M 0 j1"
  sorry

lemma p_5_1_parent_basic_2:
  assumes "M \<in> T_PS" "j0 < j" "j \<le> j1"
  assumes "nextR M 1 j0 j1" "leR M 0 j j1"
  shows "entry M 1 j \<ge> entry M 1 j1"
  sorry

text \<open>系（直系先祖の基本性質） — basic property of (lineal) ancestors.\<close>

lemma p_5_1_ancestor_basic_1:
  assumes "M \<in> T_PS" "j0 < j" "j \<le> j1"
  assumes "leR M 0 j0 j1"
  shows "entry M 0 j0 < entry M 0 j"
  sorry

lemma p_5_1_ancestor_basic_2:
  assumes "M \<in> T_PS" "j0 < j" "j \<le> j1"
  assumes "leR M 1 j0 j1" "leR M 0 j j1"
  shows "entry M 1 j0 < entry M 1 j"
  sorry

text \<open>系（直系先祖の木構造） — tree structure of ancestors.\<close>

lemma p_5_1_ancestor_tree_1:
  assumes "M \<in> T_PS" "leR M 0 j0 j1" "j0 \<le> j" "j \<le> j1"
  shows "leR M 0 j0 j"
  sorry

lemma p_5_1_ancestor_tree_2:
  assumes "M \<in> T_PS" "leR M 1 j0 j1" "j0 \<le> j" "leR M 0 j j1"
  shows "leR M 1 j0 j"
  sorry


subsection \<open>§5.3 基本列\<close>

text \<open>命題（\<open>Pred\<close>が\<open>[1]\<close>で表されること） — \<open>Pred\<close> equals the \<open>n=1\<close> step.\<close>

lemma p_5_3_pred_is_oper1:
  assumes "M \<in> T_PS" "Lng M > 1"
  shows "Pred M = M[1]"
  sorry


subsection \<open>§5.4 ペア数列システム\<close>

text \<open>
  命題（\<open>F\<^sub>M\<close>と基本列の関係） — relation between \<open>F\<^sub>M\<close> and the fundamental
  sequence.  The article states the equivalence of: (1) \<open>(M,n) \<in> Dom F\<close>;
  (2) \<open>(M[n],n) \<in> Dom F\<close>; (3) both, together with \<open>F\<^sub>M(n) = F\<^bsub>M[n]\<^esub>(n)\<close>.

  CORRECTED form (see @{file "amendments.md"} entry A1): the article's second
  argument \<open>n\<close> is an apparent typo for \<open>f n\<close>, and the substantive content is
  the case \<open>Lng M > 1\<close> (for \<open>Lng M = 1\<close> the relation is trivial since
  \<open>M[n] = M\<close>).
\<close>

lemma p_5_4_F_oper_dom:
  assumes "M \<in> T_PS" "n \<ge> 1" "Lng M > 1"
  shows "Fdom f M n \<longleftrightarrow> Fdom f (M[n]) (f n)"
  sorry

lemma p_5_4_F_oper_val:
  assumes "M \<in> T_PS" "n \<ge> 1" "Lng M > 1" "Fdom f M n"
  shows "Fval f M n = Fval f (M[n]) (f n)"
  sorry


section \<open>§6 ペア数列の基本性質\<close>

subsection \<open>§6.1 最上行のインクリメント\<close>

text \<open>命題（\<open>\<le>\<^sub>M\<close>の\<open>IncrFirst\<close>不変性） — \<open>\<le>\<^sub>M\<close> and \<open>\<le>\<^bsub>IncrFirst M\<^esub>\<close> coincide.\<close>

lemma p_6_1_le_IncrFirst_inv:
  shows "leR (IncrFirst M) i j0 j1 \<longleftrightarrow> leR M i j0 j1"
  sorry


subsection \<open>§6.2 単項性\<close>

text \<open>命題（複項性の判定条件） — equivalence of: (1) not multi; (2) strict
  increase from the left; (3) \<open>(0,0) \<le>\<^sub>M (0, Lng M - 1)\<close>.\<close>

lemma p_6_2_multi_crit_12:
  assumes "M \<in> T_PS"
  shows "(\<not> multiT M) = (\<forall>j. 0 < j \<and> j < Lng M \<longrightarrow> entry M 0 0 < entry M 0 j)"
  sorry

lemma p_6_2_multi_crit_23:
  assumes "M \<in> T_PS"
  shows "(\<forall>j. 0 < j \<and> j < Lng M \<longrightarrow> entry M 0 0 < entry M 0 j)
         = leR M 0 0 (Lng M - 1)"
  sorry

text \<open>系（単項性の始切片への遺伝性） — a proper initial slice of a mono is mono.\<close>

lemma p_6_2_mono_prefix:
  assumes "M \<in> PT_PS" "0 < j0" "j0 < Lng M"
  shows "monoT (seg M 0 j0)"
  sorry

text \<open>命題（単項性の直系先祖による切片への遺伝性） — an ancestor slice is mono.\<close>

lemma p_6_2_mono_ancestor_slice:
  assumes "M \<in> T_PS" "j0' < j1'" "leR M 0 j0' j1'"
  shows "monoT (seg M j0' j1')"
  sorry

text \<open>命題（\<open>P\<close>の\<open>IncrFirst\<close>同変性） — \<open>P\<close> commutes with \<open>IncrFirst\<close>.\<close>

lemma p_6_2_P_IncrFirst:
  shows "P (IncrFirst M) = map IncrFirst (P M)"
  sorry

text \<open>命題（\<open>P\<close>の各成分の非複項性） — each component of \<open>P M\<close> is non-multi, and
  \<open>M\<close> is multi iff \<open>Lng (P M) > 1\<close>.\<close>

lemma p_6_2_P_components_1:
  assumes "M \<in> T_PS"
  shows "\<forall>M' \<in> set (P M). zeroT M' \<or> monoT M'"
  sorry

lemma p_6_2_P_components_2:
  assumes "M \<in> T_PS"
  shows "multiT M \<longleftrightarrow> length (P M) > 1"
  sorry

text \<open>命題（\<open>P\<close>の加法性） — additivity of \<open>P\<close> at a left-minimal cut \<open>j\<^sub>0\<close>.\<close>

lemma p_6_2_P_additive:
  assumes "M \<in> T_PS" "0 < j0" "j0 \<le> Lng M - 1"
    and "\<And>j. j < j0 \<Longrightarrow> entry M 0 j \<ge> entry M 0 j0"
  shows "P M = P (seg M 0 (j0 - 1)) @ P (seg M j0 (Lng M - 1))"
  sorry

text \<open>命題（\<open>P\<close>と基本列の関係） — relation between \<open>P\<close> and the fundamental
  sequence (here \<open>P(M)\<^bsub>J\<^sub>1\<^esub> = last (P M)\<close>, \<open>(P(M)\<^sub>J)\<^bsub>J=0\<^esub>\<^bsup>J\<^sub>1-1\<^esup> = butlast (P M)\<close>).\<close>

lemma p_6_2_P_oper_1:
  assumes "M \<in> T_PS" "n \<ge> 1" "Lng (last (P M)) = 1"
  shows "M[n] = Pred M
       \<and> (if length (P M) = 1 then P (M[n]) = [(M[n])] else P (M[n]) = butlast (P M))"
  sorry

lemma p_6_2_P_oper_2:
  assumes "M \<in> T_PS" "n \<ge> 1" "Lng (last (P M)) > 1"
  shows "M[n] = concat (butlast (P M)) @ (last (P M))[n]
       \<and> P (M[n]) = butlast (P M) @ P ((last (P M))[n])"
  sorry

text \<open>命題（非複項性と基本列の関係） — for a non-multi \<open>M\<close>, \<open>P(M[n])\<close> is either
  \<open>n\<close> copies of \<open>Pred M\<close> or the singleton \<open>[M[n]]\<close>.\<close>

lemma p_6_2_nonmulti_oper_1:
  assumes "M \<in> T_PS" "n \<ge> 1" "\<not> multiT M"
    "nextR M 0 0 (Lng M - 1)" "entry M 1 (Lng M - 1) = 0"
  shows "P (M[n]) = replicate n (Pred M)"
  sorry

lemma p_6_2_nonmulti_oper_2:
  assumes "M \<in> T_PS" "n \<ge> 1" "\<not> multiT M"
    "\<not> nextR M 0 0 (Lng M - 1) \<or> entry M 1 (Lng M - 1) > 0"
  shows "P ((M::pairseq)[n]) = [(M[n])]"
  sorry


subsection \<open>§6.3 許容性\<close>

text \<open>命題（許容性の切片への遺伝性） — admissibility transfers to slices.\<close>

lemma p_6_3_adm_slice:
  assumes "M \<in> T_PS" "j0' \<le> j0" "j0 \<le> j1'" "j1' \<le> Lng M - 1"
  shows "(adm M j0 \<or> j0' = j0 \<or> j0 = j1') = adm (seg M j0' j1') (j0 - j0')"
  sorry

text \<open>命題（許容化の切片への遺伝性） — admissibilization transfers to slices.\<close>

lemma p_6_3_admof_slice:
  assumes "M \<in> T_PS" "j0' \<le> Adm M j0" "j0 < j1'" "j1' \<le> Lng M - 1"
  shows "Adm (seg M j0' j1') (j0 - j0') = Adm M j0 - j0'"
  sorry

text \<open>命題（基点の切片への遺伝性） — a marked pair sequence restricts to a marked slice.\<close>

lemma p_6_3_marked_slice:
  assumes "(M, m) \<in> Marked" "j0' \<le> m" "m \<le> j1'" "j1' \<le> Lng M - 1"
  shows "(seg M j0' j1', m - j0') \<in> Marked"
  sorry


subsection \<open>§6.4 幹と枝\<close>

text \<open>命題（\<open>P\<close>と\<open>IdxSum\<close>の関係） — each component of \<open>P M\<close> is the \<open>M\<close>-slice
  between consecutive \<open>IdxSum\<close> values.\<close>

lemma p_6_4_P_IdxSum:
  assumes "M \<in> T_PS" "J \<le> Lng (P M) - 1"
  shows "(P M) ! J = seg M (IdxSum (P M) ! J) (IdxSum (P M) ! (J + 1) - 1)"
  sorry

text \<open>系（\<open>P\<close>と\<open>IdxSum\<close>の合成の特徴付け）.\<close>

lemma p_6_4_P_IdxSum_char_1:
  assumes "M \<in> T_PS" "J \<le> Lng (P M) - 1"
  shows "\<not> (\<exists>!j0. nextR M 0 j0 (IdxSum (P M) ! J))"
  sorry

lemma p_6_4_P_IdxSum_char_2:
  assumes "M \<in> T_PS" "j \<le> Lng M - 1" "\<not> (\<exists>!j0. nextR M 0 j0 j)"
  shows "\<exists>J. J \<le> Lng (P M) - 1 \<and> j = IdxSum (P M) ! J"
  sorry

text \<open>命題（\<open>P\<close>の各成分の左端の単調性）.\<close>

lemma p_6_4_P_leftend_mono:
  assumes "M \<in> T_PS" "J0' \<le> J1'" "J1' \<le> Lng (P M) - 1"
  shows "entry ((P M) ! J0') 0 0 \<ge> entry ((P M) ! J1') 0 0"
  sorry

text \<open>命題（切片の単項成分と\<open><\<^bsub>M\<^esub>\<^sup>Next\<close>の関係）.\<close>

lemma p_6_4_mono_slice_next:
  assumes "M \<in> PT_PS" "0 < j0" "j0 \<le> Lng M - 1"
    "J \<le> Lng (P (seg M j0 (Lng M - 1))) - 1"
  shows "hasParent M 0 (j0 + IdxSum (P (seg M j0 (Lng M - 1))) ! J)
       \<and> parent M 0 (j0 + IdxSum (P (seg M j0 (Lng M - 1))) ! J) < j0"
  sorry

text \<open>命題（\<open>FirstNodes\<close>と\<open>TrMax\<close>と\<open>Joints\<close>の関係）.\<close>

lemma p_6_4_FirstNodes_TrMax_Joints:
  assumes "M \<in> PT_PS" "J \<le> Lng (Br M) - 1"
  shows "Joints M ! J \<le> TrMax M \<and> TrMax M < FirstNodes M ! J"
  sorry

text \<open>系（\<open>FirstNodes\<close>と\<open>Joints\<close>の単調性）.\<close>

lemma p_6_4_FirstNodes_Joints_mono:
  assumes "M \<in> PT_PS" "J0' < J1'" "J1' \<le> Lng (Br M) - 1"
  shows "FirstNodes M ! J0' \<le> FirstNodes M ! J1'
       \<and> Joints M ! J0' \<ge> Joints M ! J1'
       \<and> entry M 0 (FirstNodes M ! J0') \<ge> entry M 0 (FirstNodes M ! J1')
       \<and> (\<forall>i\<in>{0,1}. entry M i (Joints M ! J0') > entry M i (Joints M ! J1'))"
  sorry

text \<open>系（単項性の切片への遺伝性） — §6.4 version (via Joints).\<close>

lemma p_6_4_mono_slice:
  assumes "M \<in> PT_PS" "j0' < j1'" "j1' \<le> Lng M - 1"
    "j0' \<le> Joints M ! (Lng (Br M) - 1)"
  shows "monoT (seg M j0' j1')"
  sorry


subsection \<open>§6.5 簡約化\<close>

text \<open>命題（\<open>Red\<close>のwell-defined性） — the recursion defining \<open>Red\<close> terminates on
  every \<open>M \<in> T\<^sub>PS\<close> (the article: 上の条件を全て満たす写像 \<open>Red\<close> が一意に存在する).
  Encoded as totality of the \<open>function\<close>-domain predicate \<open>Red_dom\<close>.\<close>

lemma p_6_5_Red_welldef:
  assumes "M \<in> T_PS"
  shows "Red_dom M"
  sorry

text \<open>命題（\<open>Red\<close>の\<open>IncrFirst\<close>不変性）.\<close>

lemma p_6_5_Red_IncrFirst:
  assumes "M \<in> T_PS"
  shows "Red (IncrFirst M) = Red M"
  sorry

text \<open>命題（\<open>Lng\<close>の\<open>Red\<close>不変性）.\<close>

lemma p_6_5_Lng_Red:
  assumes "M \<in> T_PS"
  shows "Lng (Red M) = Lng M"
  sorry

text \<open>系（\<open>Red\<close>が零項性を保つこと）.\<close>

lemma p_6_5_Red_zeroT:
  assumes "M \<in> T_PS"
  shows "zeroT M \<longleftrightarrow> zeroT (Red M)"
  sorry

text \<open>系（直系先祖の\<open>Red\<close>不変性） — \<open>\<le>\<^bsub>M\<^esub>\<close> and \<open>\<le>\<^bsub>Red M\<^esub>\<close> coincide.\<close>

lemma p_6_5_Red_le:
  assumes "M \<in> T_PS"
  shows "leR M i j0 j1 = leR (Red M) i j0 j1"
  sorry

text \<open>系（\<open>Red\<close>が単項性を保つこと）.\<close>

lemma p_6_5_Red_monoT:
  assumes "M \<in> T_PS"
  shows "monoT M \<longleftrightarrow> monoT (Red M)"
  sorry

text \<open>系（\<open>P\<close>の\<open>Red\<close>同変性） — \<open>P(Red M) = (Red (P M\<^sub>J))\<^bsub>J\<^esub>\<close>.\<close>

lemma p_6_5_P_Red:
  assumes "M \<in> T_PS"
  shows "P (Red M) = map Red (P M)"
  sorry

text \<open>命題（単項性と\<open>Red\<close>の関係） — the suffix \<open>(N\<^sub>j)\<^bsub>j=M\<^bsub>1,0\<^esub>\<^esub>\<^bsup>Lng N-1\<^esup>\<close> of
  \<open>N = Red (((j,j))\<^bsub>j=0\<^esub>\<^bsup>M\<^bsub>1,0\<^esub>-1\<^esup> \<oplus> IncrFirst\<^bsup>M\<^bsub>1,0\<^esub>\<^esup>(M))\<close> is mono;
  this is exactly the branch condition that makes the \<open>Red M := M\<close> fall-throughs
  \<^bold>\<open>[19]\<close>/\<^bold>\<open>[20]\<close> in the §6.5 definition dead.\<close>

lemma p_6_5_monoT_Red:
  assumes "M \<in> PT_PS"
  defines "N \<equiv> Red (diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ (entry M 1 0)) M)"
  shows "seg N (entry M 1 0) (Lng N - 1) \<in> PT_PS"
  sorry

text \<open>命題（\<open>Red\<close>の冪等性）.\<close>

lemma p_6_5_Red_idem:
  assumes "M \<in> T_PS"
  shows "Red (Red M) = Red M"
  sorry

text \<open>命題（\<open>Red\<close>と\<open>Pred\<close>の可換性）.\<close>

lemma p_6_5_Red_Pred:
  assumes "M \<in> T_PS"
  shows "Red (Pred M) = Pred (Red M)"
  sorry

text \<open>命題（\<open>Red\<close>と基本列の可換性）.\<close>

lemma p_6_5_Red_oper:
  assumes "M \<in> T_PS" "n \<ge> 1"
  shows "(Red M)[n] = Red (M[n])"
  sorry

text \<open>命題（\<open>Red\<close>が許容性を保つこと） — \<open>\<nat>\<^sub>M = \<nat>\<^bsub>Red M\<^esub>\<close>.\<close>

lemma p_6_5_Red_adm:
  assumes "M \<in> T_PS"
  shows "AdmSet M = AdmSet (Red M)"
  sorry

text \<open>系（許容化の\<open>Red\<close>不変性）.\<close>

lemma p_6_5_admof_Red:
  assumes "M \<in> T_PS"
  shows "Adm M j = Adm (Red M) j"
  sorry

text \<open>系（\<open>Red\<close>が基点を保つこと） — a marked pair sequence stays marked under
  \<open>Red\<close>; in the article the codomain is \<open>RT\<^bsub>PS\<^esub>\<^sup>Marked\<close> (marked AND reduced),
  the reducedness being @{thm [source] p_6_5_Red_idem}.  \<open>RT\<^sub>PS\<close> itself is §6.6.\<close>

lemma p_6_5_Red_marked:
  assumes "(M, m) \<in> Marked"
  shows "(Red M, m) \<in> Marked"
  sorry


subsection \<open>§6.6 簡約性\<close>

text \<open>命題（簡約性の切片への遺伝性） — a reduced sequence restricts to a reduced
  slice across the trunk end.\<close>

lemma p_6_6_reduced_slice:
  assumes "M \<in> RT_PS" "j0' \<le> TrMax M" "TrMax M \<le> j1'" "j1' \<le> Lng M - 1"
  shows "seg M j0' j1' \<in> RT_PS"
  sorry

text \<open>命題（\<open>P\<close>が簡約性を保つこと）.\<close>

lemma p_6_6_P_reduced:
  assumes "M \<in> T_PS"
  shows "M \<in> RT_PS \<longleftrightarrow> (\<forall>J < Lng (P M). P M ! J \<in> RT_PS)"
  sorry

text \<open>命題（簡約性が基本列で保たれること）.\<close>

lemma p_6_6_reduced_oper:
  assumes "M \<in> RT_PS" "n \<ge> 1"
  shows "((M::pairseq)[n]) \<in> RT_PS"
  sorry

text \<open>命題（簡約性と係数の関係） — reducedness \<open>\<longleftrightarrow>\<close> conditions (A) and (B).\<close>

lemma p_6_6_reduced_iff_cond:
  assumes "M \<in> T_PS"
  shows "M \<in> RT_PS \<longleftrightarrow> RedCondA M \<and> RedCondB M"
  sorry

text \<open>補題（\<open>Red\<close>と左端の関係） (1): \<open>Red\<close> fixes the row-1 left end.\<close>

lemma p_6_6_Red_leftend_1:
  assumes "M \<in> T_PS"
  shows "entry (Red M) 1 0 = entry M 1 0"
  sorry

text \<open>補題（\<open>Red\<close>と左端の関係） (2): a leading diagonal prefix is preserved by \<open>Red\<close>.\<close>

lemma p_6_6_Red_leftend_2:
  assumes "M \<in> T_PS" "monoT M" "j0 \<le> Lng M - 1"
    "seg M 0 j0 = diagSeq u (j0 + u)"
  shows "(Red M) ! j0 = (j0 + u, j0 + u)"
  sorry

text \<open>補題（簡約性と係数の基本性質） — in a reduced sequence row 0 dominates row 1.\<close>

lemma p_6_6_reduced_coeff:
  assumes "M \<in> RT_PS" "j < Lng M"
  shows "entry M 0 j \<ge> entry M 1 j"
  sorry

text \<open>補題（簡約性と左端の関係） — prepending a diagonal to a reduced mono sequence
  keeps it reduced and mono.\<close>

lemma p_6_6_reduced_leftend:
  assumes "M \<in> RT_PS" "M \<in> PT_PS" "u \<le> entry M 1 0"
  defines "N \<equiv> diagSeq u (entry M 1 0 - 1) @ M"
  shows "Red N = N \<and> monoT N"
  sorry

text \<open>補題（条件(A)と(B)と係数の基本性質）.\<close>

lemma p_6_6_condAB_coeff:
  assumes "M \<in> T_PS" "entry M 0 0 = 0" "entry M 1 0 = 0" "RedCondA M"
  shows
    "(\<forall>j \<le> Lng M - 1. entry M 0 j \<le> j)
   \<and> (RedCondB M \<longrightarrow> (\<forall>j \<le> Lng M - 1. entry M 0 j \<ge> entry M 1 j))
   \<and> (\<forall>i \<le> 1. (i = 0 \<or> (i = 1 \<and> RedCondB M)) \<longrightarrow>
        (\<forall>j \<le> Lng M - 1.
           (\<exists>j0' j1'. \<not> leR M i j0' j1' \<and> j0' < j1' \<and> j1' \<le> j) \<longrightarrow> entry M i j < j))"
  sorry

text \<open>系（直系先祖による切片と\<open>Red\<close>と\<open>IncrFirst\<close>の関係）.  原文の指数の添字 \<open>m\<close> は
  \<open>j\<^sub>0'\<close> の誤記（amendments.md A2）。\<close>

lemma p_6_6_ancestor_slice_Red_IncrFirst:
  assumes "M \<in> RT_PS" "j0' < j1'" "j1' \<le> Lng M - 1" "leR M 0 j0' j1'"
  defines "N \<equiv> Red (seg M j0' j1')"
  shows "Red N = N \<and> monoT N
       \<and> seg M j0' j1' = (IncrFirst ^^ (entry M 0 j0' - entry M 1 j0')) N"
  sorry

text \<open>系（\<open>1\<close>列ペア数列の基本性質） — the reduced length-1 sequences are exactly
  the diagonals \<open>((v,v))\<close>.\<close>

lemma p_6_6_oneColumn:
  assumes "M \<in> T_PS"
  shows "(Lng M = 1 \<and> M \<in> RT_PS) \<longleftrightarrow> (\<exists>v. M = [(v, v)])"
  sorry


subsection \<open>§6.7 標準形\<close>

text \<open>命題（標準形の簡約性） — \<open>ST\<^sub>PS \<subseteq> RT\<^sub>PS\<close>.\<close>

lemma p_6_7_standard_reduced:
  shows "ST_PS \<subseteq> RT_PS"
  sorry

text \<open>\<open>ST\<^sub>PS = \<Union>\<^sub>k S\<^sub>kT\<^sub>PS\<close> (\<open>ST\<^sub>PS\<close> の定義に基づく最小性より).\<close>

lemma p_6_7_ST_eq_Union_SkT:
  shows "ST_PS = (\<Union>k. SkT_PS k)"
  sorry

text \<open>命題（標準形の単項成分が標準形であること） — \<open>P(M) \<in> S\<^sub>kT\<^sub>PS\<^bsup><\<omega>\<^esup>\<close>.\<close>

lemma p_6_7_standard_P_components:
  assumes "M \<in> SkT_PS k"
  shows "\<forall>J < Lng (P M). P M ! J \<in> SkT_PS k"
  sorry

text \<open>命題（標準形の始切片への遺伝性）.\<close>

lemma p_6_7_standard_prefix:
  assumes "M \<in> ST_PS" "j1' \<le> Lng M - 1"
  shows "seg M 0 j1' \<in> ST_PS"
  sorry


subsection \<open>§6.8 降順性\<close>

text \<open>命題（標準形の切片と\<open>Br\<close>の降順性の関係）.\<close>

lemma p_6_8_standard_slice_Br_descending:
  assumes "M \<in> ST_PS" "j0' < j1'" "j1' \<le> Lng M - 1" "leR M 0 j0' j1'"
  shows "monoT (seg M j0' j1') \<and> descending (Br (seg M j0' j1'))"
  sorry

text \<open>命題（標準形の単項成分が降順であること）.\<close>

lemma p_6_8_standard_P_descending:
  assumes "M \<in> ST_PS" "J0' \<le> J1'" "J1' \<le> Lng (P M) - 1"
    "entry (P M ! J0') 0 0 = entry (P M ! J1') 0 0"
  shows "entry (P M ! J0') 1 0 \<ge> entry (P M ! J1') 1 0"
  sorry


section \<open>§7 Buchholz の表記系への翻訳\<close>

text \<open>
  The Buchholz notation system, transcribed from the cited reference
  \<^bold>\<open>[Buc1]\<close> = W. Buchholz, "A new system of proof-theoretic ordinal
  functions", Annals of Pure and Applied Logic 32 (1986), pp. 195–207.
  These are the formulas of the external reference on which §7 of the article
  relies; we transcribe them here (in the paper file) rather than as our own
  modelling definitions.

  Indices \<open>v \<le> \<omega>\<close> of the symbols \<open>D\<^sub>v\<close> are modelled by \<^typ>\<open>enat\<close>
  (a finite \<open>v < \<omega>\<close> is \<open>enat n\<close>; \<open>\<omega>\<close> is \<open>\<infinity>\<close>).
\<close>

subsection \<open>§7.1 Buchholz の表記系 — 項と順序 ([Buc1] §2)\<close>

text \<open>
  [Buc1] (T1)–(T3): a term is \<open>0\<close> (\<open>= Trm []\<close>), a principal term \<open>D\<^sub>v a\<close>
  (\<open>= Trm [DB v a]\<close>), or a tuple \<open>(a\<^sub>0,\<dots>,a\<^sub>k)\<close> (\<open>k \<ge> 1\<close>) of principal
  terms (\<open>= Trm\<close> of a length \<open>\<ge> 2\<close> list).  Single principal: \<open>(a) := a\<close>.
\<close>

datatype BT = Trm "BP list"
     and BP = DB enat BT

abbreviation BZero :: BT  ("0\<^sub>B") where "0\<^sub>B \<equiv> Trm []"

text \<open>[Buc1] (<1)–(<3): the ordering \<open><\<close> on \<open>T\<close>.  As a dictionary order on the
  principal-term lists (a proper prefix is smaller), with principals compared
  by \<open>D\<^sub>u a < D\<^sub>v b \<longleftrightarrow> u < v \<or> (u = v \<and> a < b)\<close>.\<close>

fun lessBT :: "BT \<Rightarrow> BT \<Rightarrow> bool" and lessBP :: "BP \<Rightarrow> BP \<Rightarrow> bool" where
  "lessBT (Trm []) (Trm bs) = (bs \<noteq> [])"
| "lessBT (Trm (a # as)) (Trm []) = False"
| "lessBT (Trm (a # as)) (Trm (b # bs)) =
     (lessBP a b \<or> (a = b \<and> lessBT (Trm as) (Trm bs)))"
| "lessBP (DB u a) (DB v b) = (u < v \<or> (u = v \<and> lessBT a b))"

abbreviation leBT :: "BT \<Rightarrow> BT \<Rightarrow> bool" where
  "leBT a b \<equiv> lessBT a b \<or> a = b"

text \<open>[Buc1] (G1)–(G3): \<open>G\<^sub>u a \<subseteq> T\<close>.\<close>

fun GBT :: "enat \<Rightarrow> BT \<Rightarrow> BT set" and GBP :: "enat \<Rightarrow> BP \<Rightarrow> BT set" where
  "GBT u (Trm ps) = (\<Union>p \<in> set ps. GBP u p)"
| "GBP u (DB v b) = (if u \<le> v then insert b (GBT u b) else {})"

text \<open>[Buc1] §3: addition \<open>a + b\<close> and \<open>a \<cdot> n\<close>.\<close>

fun addBT :: "BT \<Rightarrow> BT \<Rightarrow> BT"  (infixl "+\<^sub>B" 65) where
  "addBT (Trm as) (Trm bs) = Trm (as @ bs)"

fun multBT :: "BT \<Rightarrow> nat \<Rightarrow> BT"  (infixl "*\<^sub>B" 70) where
  "multBT a 0 = 0\<^sub>B"
| "multBT a (Suc n) = (multBT a n) +\<^sub>B a"

text \<open>[Buc1] §3: \<open>T\<^sub>v\<close> for \<open>v \<le> \<omega>\<close> — terms whose top-level principal indices
  are all \<open>\<le> v\<close>.\<close>

definition TBv :: "enat \<Rightarrow> BT set" where
  "TBv v = {t. \<forall>p \<in> set (case t of Trm ps \<Rightarrow> ps). (case p of DB u a \<Rightarrow> u \<le> v)}"

text \<open>\<open>T\<^bsub>B\<^esub>\<close>: the \<open>D\<^sub>\<omega>\<close>-free terms (no index equals \<open>\<omega> = \<infinity>\<close> anywhere).\<close>

fun dfree_BT :: "BT \<Rightarrow> bool" and dfree_BP :: "BP \<Rightarrow> bool" where
  "dfree_BT (Trm ps) = (\<forall>p \<in> set ps. dfree_BP p)"
| "dfree_BP (DB v b) = (v \<noteq> \<infinity> \<and> dfree_BT b)"

definition T_B :: "BT set" where
  "T_B = {t. dfree_BT t}"

end
