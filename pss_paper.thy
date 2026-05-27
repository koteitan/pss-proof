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

  CORRECTED form (see @{file "corrections.md"} entry A1): the article's second
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

text \<open>命題（\<open>FirstNodes\<close>と\<open>TrMax\<close>と\<open>Joints\<close>の関係）.  \<open>J\<close> indexes a branch
  component: the article's \<open>J \<le> Lng (Br M) - 1\<close> is rendered \<open>J < Lng (Br M)\<close>
  to avoid the \<^bold>\<open>nat\<close> truncation artifact when \<open>Br M = []\<close> (where \<open>Lng - 1 = 0\<close>
  would spuriously admit \<open>J = 0\<close> and dereference the empty \<open>Joints M\<close>).\<close>

lemma p_6_4_FirstNodes_TrMax_Joints:
  assumes "M \<in> PT_PS" "J < Lng (Br M)"
  shows "Joints M ! J \<le> TrMax M \<and> TrMax M < FirstNodes M ! J"
  sorry

text \<open>系（\<open>FirstNodes\<close>と\<open>Joints\<close>の単調性）.  (\<open>J\<^sub>1' < Lng (Br M)\<close>: see above.)\<close>

text \<open>NOTE (correction A3): the article's statement (4),
  \<open>\<forall>i\<in>{0,1}. M\<^bsub>i,Joints J0'\<^esub> > M\<^bsub>i,Joints J1'\<^esub>\<close> (strict), is \<^bold>\<open>false\<close>: distinct
  branches may share a trunk joint, e.g. for the standard mono pair sequence
  \<open>(0,0)(1,1)(2,1)(3,1)(2,0)\<close> both branches join at index 1, so
  \<open>Joints = [1,1]\<close> and (4) reads \<open>1 > 1\<close>.  We transcribe the corrected statement
  with parts (1)(2)(3) only (the article's "(4) follows immediately from (3)"
  overlooks that (3) is non-strict).  See @{file "corrections.md"} A3.\<close>

lemma p_6_4_FirstNodes_Joints_mono:
  assumes "M \<in> PT_PS" "J0' < J1'" "J1' < Lng (Br M)"
  shows "FirstNodes M ! J0' \<le> FirstNodes M ! J1'
       \<and> Joints M ! J0' \<ge> Joints M ! J1'
       \<and> entry M 0 (FirstNodes M ! J0') \<ge> entry M 0 (FirstNodes M ! J1')"
  sorry

text \<open>系（単項性の切片への遺伝性） — §6.4 version (via Joints).\<close>

lemma p_6_4_mono_slice:
  assumes "M \<in> PT_PS" "j0' < j1'" "j1' \<le> Lng M - 1"
    "j0' \<le> Joints M ! (Lng (Br M) - 1)"
  shows "monoT (seg M j0' j1')"
  sorry


subsection \<open>§6.5 簡約化\<close>

text \<open>
  CAUTION (correction A4 — see corrections.md and docs/red-le-domain.md).
  The eight §6.5 corollaries p_6_5_Red_le, p_6_5_Red_monoT, p_6_5_P_Red,
  p_6_5_Red_idem, p_6_5_Red_oper, p_6_5_Red_adm, p_6_5_admof_Red and
  p_6_5_Red_marked are FALSE as the article states them for all M : T_PS —
  counterexample Red ((0,0)(0,1)) = (0,0)(1,1), which changes the ancestor tree
  (checked empirically with python/ + yaBMS).  They DO hold on the restricted
  domain of ANCESTOR-ANCHORED SLICES of standard / reduced+mono sequences, i.e.
  the actual §7 use-sites.  Their premise is therefore corrected here from
  \<open>M \<in> T_PS\<close> to \<open>M \<in> anchored_slice\<close> (pss_defs.thy), so the sorry below is
  no longer a false axiom — the statements are now true but UNPROVEN, and the
  domain \<open>anchored_slice\<close> is PROVISIONAL (a simpler intrinsic characterization
  and the proof are pending).  The remaining §6.5 facts (Lng_Red, Red_zeroT,
  Red_Pred, Red_IncrFirst) hold on all of T_PS and keep that premise.
\<close>

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
  assumes "M \<in> anchored_slice"  \<comment> \<open>correction A4: false on \<open>T\<^sub>PS\<close>; provisional domain\<close>
  shows "leR M i j0 j1 = leR (Red M) i j0 j1"
  sorry

text \<open>系（\<open>Red\<close>が単項性を保つこと）.\<close>

lemma p_6_5_Red_monoT:
  assumes "M \<in> anchored_slice"  \<comment> \<open>correction A4\<close>
  shows "monoT M \<longleftrightarrow> monoT (Red M)"
  sorry

text \<open>系（\<open>P\<close>の\<open>Red\<close>同変性） — \<open>P(Red M) = (Red (P M\<^sub>J))\<^bsub>J\<^esub>\<close>.\<close>

lemma p_6_5_P_Red:
  assumes "M \<in> anchored_slice"  \<comment> \<open>correction A4\<close>
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
  assumes "M \<in> anchored_slice"  \<comment> \<open>correction A4\<close>
  shows "Red (Red M) = Red M"
  sorry

text \<open>命題（\<open>Red\<close>と\<open>Pred\<close>の可換性）.\<close>

lemma p_6_5_Red_Pred:
  assumes "M \<in> T_PS"
  shows "Red (Pred M) = Pred (Red M)"
  sorry

text \<open>命題（\<open>Red\<close>と基本列の可換性）.\<close>

lemma p_6_5_Red_oper:
  assumes "M \<in> anchored_slice" "n \<ge> 1"  \<comment> \<open>correction A4\<close>
  shows "(Red M)[n] = Red (M[n])"
  sorry

text \<open>命題（\<open>Red\<close>が許容性を保つこと） — \<open>\<nat>\<^sub>M = \<nat>\<^bsub>Red M\<^esub>\<close>.\<close>

lemma p_6_5_Red_adm:
  assumes "M \<in> anchored_slice"  \<comment> \<open>correction A4\<close>
  shows "AdmSet M = AdmSet (Red M)"
  sorry

text \<open>系（許容化の\<open>Red\<close>不変性）.\<close>

lemma p_6_5_admof_Red:
  assumes "M \<in> anchored_slice"  \<comment> \<open>correction A4\<close>
  shows "Adm M j = Adm (Red M) j"
  sorry

text \<open>系（\<open>Red\<close>が基点を保つこと） — a marked pair sequence stays marked under
  \<open>Red\<close>; in the article the codomain is \<open>RT\<^bsub>PS\<^esub>\<^sup>Marked\<close> (marked AND reduced),
  the reducedness being @{thm [source] p_6_5_Red_idem}.  \<open>RT\<^sub>PS\<close> itself is §6.6.\<close>

lemma p_6_5_Red_marked:
  assumes "(M, m) \<in> Marked" "M \<in> anchored_slice"  \<comment> \<open>correction A4\<close>
  shows "(Red M, m) \<in> Marked"
  sorry


subsection \<open>§6.6 簡約性\<close>

text \<open>命題（簡約性の切片への遺伝性） — a reduced sequence restricts to a reduced
  initial slice (from the trunk root) across the trunk end.
  CORRECTION A5: the article's premise \<open>j0' \<le> TrMax M\<close> is too weak (false for
  e.g. the standard reduced M = (0,0)(1,1)(1,0), slice seg M 1 2); corrected to
  \<open>j0' = 0\<close> (empirically sound, python/red_66_audit.py).  Final premise pending.\<close>

lemma p_6_6_reduced_slice:
  assumes "M \<in> RT_PS" "j0' = 0" "TrMax M \<le> j1'" "j1' \<le> Lng M - 1"  \<comment> \<open>A5: was \<open>j0' \<le> TrMax M\<close>\<close>
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
  \<open>j\<^sub>0'\<close> の誤記（corrections.md A2）。\<close>

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

text \<open>[Buc1] Lemma 2.1: \<open><\<close> is a strict linear order on \<open>T\<close> — irreflexive,
  transitive, and trichotomous (the latter gives totality and asymmetry).\<close>

lemma p_7_1_lessBT_linord:
  shows "\<not> lessBT t t"
    and "lessBT a b \<Longrightarrow> lessBT b c \<Longrightarrow> lessBT a c"
    and "lessBT a b \<or> a = b \<or> lessBT b a"
  sorry

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

text \<open>[Buc1] (OT1)–(OT3): the ordinal terms \<open>OT \<subseteq> T\<close>.  Characterized
  structurally: \<open>0 \<in> OT\<close>; a principal \<open>D\<^sub>v b \<in> OT\<close> iff \<open>b \<in> OT\<close> and
  \<open>G\<^sub>v b < b\<close>; a tuple \<open>(a\<^sub>0,\<dots>,a\<^sub>k) \<in> OT\<close> iff every component is an
  \<open>OT\<close>-principal and the components are non-increasing \<open>a\<^sub>k \<le> \<dots> \<le> a\<^sub>0\<close>.\<close>

fun descP :: "BP list \<Rightarrow> bool" where
  "descP [] = True"
| "descP [p] = True"
| "descP (p # q # ps) = (leBT (Trm [q]) (Trm [p]) \<and> descP (q # ps))"

fun isOT_BT :: "BT \<Rightarrow> bool" and isOT_BP :: "BP \<Rightarrow> bool" where
  "isOT_BT (Trm ps) = ((\<forall>p \<in> set ps. isOT_BP p) \<and> descP ps)"
| "isOT_BP (DB v b) = (isOT_BT b \<and> (\<forall>x \<in> GBT v b. lessBT x b))"

definition OT :: "BT set" where
  "OT = {t. isOT_BT t}"

text \<open>\<open>OT\<^bsub>B\<^esub> := OT \<inter> T\<^bsub>B\<^esub>\<close> (content.md 5951): the \<open>D\<^sub>\<omega>\<close>-free ordinal terms.
  \<open>(OT\<^bsub>B\<^esub>, <)\<close> is well-founded ([Buc1] Lemma 2.2) — the eventual source of
  termination.\<close>

definition OT_B :: "BT set" where
  "OT_B = OT \<inter> T_B"


subsection \<open>§7.1 Buchholz の表記系 — 基本列と \<open>dom\<close> ([Buc1] §3)\<close>

text \<open>\<open>D\<^sub>v a = Trm [DB v a]\<close> (a principal term as a \<^typ>\<open>BT\<close>).\<close>

abbreviation Dprin :: "enat \<Rightarrow> BT \<Rightarrow> BT" where "Dprin v a \<equiv> Trm [DB v a]"

text \<open>The numeral terms \<open>\<nat> \<cong> {0,1,1+1,\<dots>}\<close> ([Buc1] §3): \<open>n\<close> is \<open>n\<close> copies of
  \<open>1 = D\<^sub>0 0\<close>.  \<open>numNat\<close> recovers \<open>n\<close> from a numeral term.\<close>

definition numBT :: "nat \<Rightarrow> BT" where
  "numBT n = Trm (replicate n (DB 0 (Trm [])))"

definition numNat :: "BT \<Rightarrow> nat" where
  "numNat t = (case t of Trm ps \<Rightarrow> length ps)"

definition NatSet :: "BT set" where
  "NatSet = range numBT"

text \<open>\<open>tbvIdx D\<close>: the unique \<open>u\<close> with \<open>D = T\<^sub>u\<close> (used when \<open>dom(b) = T\<^sub>u\<close>).\<close>

definition tbvIdx :: "BT set \<Rightarrow> nat" where
  "tbvIdx D = (THE u. D = TBv (enat u))"

text \<open>
  [Buc1] §3 \<open>dom(a)\<close> and \<open>a[z]\<close>, ([].0)–([].5), with the \<^bold>\<open>[Buc2]\<close>-modified
  case ([].4)(ii) (article footnote, content.md 6427): \<open>x\<^sub>0 = D\<^sub>u 0\<close>,
  \<open>x\<^sub>i = b[D\<^sub>u x\<^bsub>i-1\<^esub>]\<close>, \<open>a[n] = D\<^sub>v b[x\<^sub>n]\<close>; \<open>xseq b u\<close> computes \<open>x\<close>.

  \<open>dom\<close> returns the actual index set (\<open>\<emptyset>\<close>, \<open>{0}\<close>, \<open>\<nat>\<close> = \<open>NatSet\<close>, or
  \<open>T\<^sub>u\<close> = \<open>TBv (enat u)\<close>).  Mutual recursion (with \<open>xseq\<close>); all calls are on
  \<open>dom\<close>/\<open>[]\<close>-free arguments, so the definition is accepted by \<open>function\<close>;
  termination ([Buc1] Lemma 3.2, induction on the length of \<open>a\<close>) is deferred.
\<close>

function
  domB :: "BT \<Rightarrow> BT set" and
  operB :: "BT \<Rightarrow> BT \<Rightarrow> BT" and
  xseq :: "BT \<Rightarrow> enat \<Rightarrow> nat \<Rightarrow> BT"
where
  "domB a =
     (case a of Trm xs \<Rightarrow> (case xs of
        [] \<Rightarrow> {}
      | [DB v b] \<Rightarrow>
          (if b = Trm [] then
             (if v = 0 then {Trm []}
              else if v = \<infinity> then NatSet
              else TBv (enat (the_enat v - 1)))
           else
             (let db = domB b in
              if db = {Trm []} then NatSet
              else if (\<exists>u. v \<le> enat u \<and> db = TBv (enat u)) then NatSet
              else db))
      | (p # q # rest) \<Rightarrow> domB (Trm [last (p # q # rest)])))"
| "operB a z =
     (case a of Trm xs \<Rightarrow> (case xs of
        [] \<Rightarrow> Trm []
      | [DB v b] \<Rightarrow>
          (if b = Trm [] then
             (if v = 0 then Trm []
              else if v = \<infinity> then Dprin (enat (numNat z + 1)) (Trm [])
              else z)
           else
             (let db = domB b in
              if db = {Trm []} then multBT (Dprin v (operB b (Trm []))) (numNat z + 1)
              else if (\<exists>u. v \<le> enat u \<and> db = TBv (enat u))
                   then Dprin v (operB b (xseq b (enat (tbvIdx db)) (numNat z)))
              else Dprin v (operB b z)))
      | (p # q # rest) \<Rightarrow>
          addBT (Trm (butlast (p # q # rest))) (operB (Trm [last (p # q # rest)]) z)))"
| "xseq b u i =
     (case i of
        0 \<Rightarrow> Dprin u (Trm [])
      | Suc j \<Rightarrow> operB b (Dprin u (xseq b u j)))"
  by pat_completeness auto

text \<open>
  \<open>P\<^bsub>B\<^esub> : T\<^bsub>B\<^esub> \<to> PT\<^bsub>B\<^esub>\<^bsup><\<omega>\<^esup>\<close> and its inverse \<open>\<Sigma>\<^bsub>B\<^esub>\<close> (§7.1).  In the
  datatype model the principal components of \<open>Trm ps\<close> are simply \<open>(Trm [p])\<^bsub>p\<in>ps\<^esub>\<close>;
  \<open>\<Sigma>\<^bsub>B\<^esub>\<close> concatenates their (length-1) component lists.  Hence \<open>P\<^bsub>B\<^esub>\<close>
  and \<open>\<Sigma>\<^bsub>B\<^esub>\<close> are mutually inverse (命題（順序数項の単項成分の基本性質）(2)).
\<close>

fun untrm :: "BT \<Rightarrow> BP list" where
  "untrm (Trm ps) = ps"

definition PB :: "BT \<Rightarrow> BT list" where
  "PB t = map (\<lambda>p. Trm [p]) (untrm t)"

definition SigmaB :: "BT list \<Rightarrow> BT" where
  "SigmaB ts = Trm (concat (map untrm ts))"

text \<open>命題（順序数項の単項成分の基本性質） (§7.1): with \<open>J\<^sub>1 := Lng(P(t)) - 1\<close>,
  (1) \<open>J\<^sub>1 = -1\<close> (i.e. \<open>Lng(P t) = 0\<close>) iff \<open>t = 0\<close>, and (2) \<open>t = \<Sigma>\<^bsub>B\<^esub>(P t)\<close>.\<close>

lemma p_7_1_term_components:
  assumes "t \<in> T_B"
  shows "(Lng (PB t) = 0 \<longleftrightarrow> t = Trm []) \<and> SigmaB (PB t) = t"
  sorry


subsection \<open>§7.2 scb分解 ([Buc1] のアルファベット \<open>\<Sigma>\<close> 上)\<close>

text \<open>The alphabet \<open>\<Sigma>\<close>: the letters \<open>\<^bold>(\<close>, \<open>\<^bold>,\<close>, \<open>\<^bold>)\<close>, \<open>0\<close>, and \<open>D\<^sub>u\<close>
  (\<open>u \<le> \<omega>\<close>).\<close>

datatype Sym = LP | CM | RP | Zsym | Dsym enat

text \<open>\<open>flat t\<close>: the \<open>\<Sigma>\<close>-string of a term.  \<open>0 = "0"\<close>; a principal
  \<open>D\<^sub>u a = "D\<^sub>u" \<frown> flat a\<close>; a tuple \<open>(a\<^sub>0,\<dots>,a\<^sub>k) = "(" a\<^sub>0 "," \<dots> "," a\<^sub>k ")"\<close>
  (single principal uncontracted: \<open>(a) = a\<close>).\<close>

fun flatBT :: "BT \<Rightarrow> Sym list" and flatBP :: "BP \<Rightarrow> Sym list" where
  "flatBT (Trm []) = [Zsym]"
| "flatBT (Trm [p]) = flatBP p"
| "flatBT (Trm (p # q # ps)) =
     LP # (flatBP p @ concat (map (\<lambda>r. CM # flatBP r) (q # ps))) @ [RP]"
| "flatBP (DB u a) = Dsym u # flatBT a"

text \<open>命題（順序数項のカッコの個数が左右で等しいこと） (§7.1): in the \<open>\<Sigma>\<close>-string
  of any \<open>t \<in> T\<^bsub>B\<^esub>\<close> the letter \<open>\<^bold>(\<close> occurs as often as \<open>\<^bold>)\<close>.\<close>

lemma p_7_1_paren_balance:
  assumes "t \<in> T_B"
  shows "length (filter (\<lambda>x. x = LP) (flatBT t))
       = length (filter (\<lambda>x. x = RP) (flatBT t))"
  sorry

text \<open>\<open>RightNodes : T\<^bsub>B\<^esub> \<to> \<nat>\<^bsup><\<omega>\<^esup>\<close> (§7.2): \<open>0 \<mapsto> ()\<close>; \<open>D\<^sub>u t' \<mapsto> (u) \<frown>
  RightNodes t'\<close>; a multi term \<open>\<mapsto> RightNodes\<close> of its last principal component.\<close>

function RightNodes :: "BT \<Rightarrow> nat list" where
  "RightNodes (Trm xs) =
     (case xs of [] \<Rightarrow> []
      | _ \<Rightarrow> (case last xs of DB u a \<Rightarrow> the_enat u # RightNodes a))"
  by pat_completeness auto
\<comment> \<open>termination (induction on the rightmost spine) is deferred, like \<open>Red\<close>/\<open>domB\<close>.\<close>

text \<open>
  scb-decomposition (§7.2): \<open>(s,c,b) \<in> (\<Sigma>\<^bsup><\<omega>\<^esup>)\<^sup>3\<close> is an scb-decomposition
  of \<open>t\<close> when \<open>flat t = s \<frown> c \<frown> b\<close>, \<open>c\<close> is (the string of) a principal term
  \<open>\<in> PT\<^bsub>B\<^esub>\<close> when \<open>t \<noteq> 0\<close>, and \<open>b\<close> consists only of \<open>\<^bold>)\<close>.
\<close>

definition isPTB_str :: "Sym list \<Rightarrow> bool" where
  "isPTB_str c = (\<exists>p. dfree_BP p \<and> c = flatBP p)"

definition scb_decomp :: "BT \<Rightarrow> Sym list \<Rightarrow> Sym list \<Rightarrow> Sym list \<Rightarrow> bool" where
  "scb_decomp t s c b \<longleftrightarrow>
     flatBT t = s @ c @ b
   \<and> (t \<noteq> Trm [] \<longrightarrow> isPTB_str c)
   \<and> (\<forall>x \<in> set b. x = RP)"

text \<open>第\<open>0\<close>種 / 第\<open>1\<close>種 scb-decomposition (§7.2).  Their \<open>RightNodes\<close>
  conditions refer to the principal term whose string is \<open>c\<close>.\<close>

definition scb_kind0 :: "BT \<Rightarrow> Sym list \<Rightarrow> Sym list \<Rightarrow> Sym list \<Rightarrow> bool" where
  "scb_kind0 t s c b \<longleftrightarrow>
     scb_decomp t s c b
   \<and> (\<forall>p. c = flatBP p \<longrightarrow>
        (Lng (RightNodes (Trm [p])) = 2 \<and> RightNodes (Trm [p]) ! 1 = 0))"

definition scb_kind1 :: "BT \<Rightarrow> Sym list \<Rightarrow> Sym list \<Rightarrow> Sym list \<Rightarrow> bool" where
  "scb_kind1 t s c b \<longleftrightarrow>
     scb_decomp t s c b
   \<and> (\<forall>p. c = flatBP p \<longrightarrow>
        (let r = RightNodes (Trm [p]); j1 = Lng r - 1 in
         j1 \<ge> 1 \<and> r ! 0 < r ! j1 \<and> (\<forall>j. 0 < j \<and> j < j1 \<longrightarrow> r ! j \<ge> r ! j1)))"

text \<open>\<open>T\<^bsub>B\<^esub>\<^sup>Marked \<subseteq> T\<^bsub>B\<^esub>\<^sup>2\<close>: pairs \<open>(t,c)\<close> for which some scb-decomposition
  \<open>(s,c,b)\<close> of \<open>t\<close> exists (with \<open>c = flat\<close> of the marked principal).\<close>

definition MarkedB :: "(BT \<times> BT) set" where
  "MarkedB = {(t, c). \<exists>s b. scb_decomp t s (flatBT c) b}"


text \<open>
  Modelling note for the §7.2 propositions below.  The article ranges over
  \<open>\<Sigma>\<^bsup><\<omega>\<^esup>\<close> (strings) and \<open>\<nat>\<^bsup><\<omega>\<^esup>\<close>; we model the former as \<^typ>\<open>Sym list\<close>
  and the latter as \<^typ>\<open>nat list\<close>, with the string connective \<open>s c b\<close> = list
  append \<open>@\<close> and \<open>\<oplus>\<^sub>\<nat>\<close> = \<open>@\<close>.  "\<open>x \<in> T\<^bsub>B\<^esub>\<close> as a string" (i.e. the string is the
  \<open>flat\<close> of a \<open>D\<^sub>\<omega>\<close>-free term) is written \<open>\<exists>t. t \<in> T\<^bsub>B\<^esub> \<and> flatBT t = \<dots>\<close>; the
  unique witnessing term is recovered by \<open>unflatBT\<close> (defined in §7.3).  "\<open>c\<close> 単項" (\<open>c \<in> PT\<^bsub>B\<^esub>\<close>)
  for a \<^typ>\<open>BT\<close> is \<open>\<exists>p. c = Trm [p]\<close> (a single principal component), with
  \<open>D\<^sub>\<omega>\<close>-freeness added as \<open>c \<in> T\<^bsub>B\<^esub>\<close> where the article writes \<open>PT\<^bsub>B\<^esub>\<close>.  The
  string-level \<open>D\<^sub>v\<close>-prefix \<open>D\<^sub>v s\<close> is \<open>Dsym (enat v) # s\<close> (cf. \<^const>\<open>flatBP\<close>).
\<close>

text \<open>命題（scb分解の置換可能性） (§7.2): for strings \<open>s,b\<close> and terms \<open>c\<^sub>0,c\<^sub>1\<close>,
  if (\<open>c\<^sub>0\<close> is not principal \<open>\<or>\<close> \<open>c\<^sub>1\<close> is principal), the string \<open>s\<frown>flat c\<^sub>0\<frown>b\<close> is
  (the \<open>flat\<close> of) a term \<open>\<in> T\<^bsub>B\<^esub>\<close>, and \<open>(s, flat c\<^sub>0, b)\<close> is an scb-decomposition
  of it, then \<open>s\<frown>flat c\<^sub>1\<frown>b\<close> is also (the \<open>flat\<close> of) a term \<open>\<in> T\<^bsub>B\<^esub>\<close> and
  \<open>(s, flat c\<^sub>1, b)\<close> is an scb-decomposition of it.\<close>

lemma p_7_2_scb_replaceable:
  assumes "c\<^sub>0 \<in> T_B" "c\<^sub>1 \<in> T_B"
    and "(\<not>(\<exists>p. c\<^sub>0 = Trm [p])) \<or> (\<exists>p. c\<^sub>1 = Trm [p])"
    and "t\<^sub>0 \<in> T_B" "flatBT t\<^sub>0 = s @ flatBT c\<^sub>0 @ b"
    and "scb_decomp t\<^sub>0 s (flatBT c\<^sub>0) b"
  shows "\<exists>t\<^sub>1. t\<^sub>1 \<in> T_B \<and> flatBT t\<^sub>1 = s @ flatBT c\<^sub>1 @ b
            \<and> scb_decomp t\<^sub>1 s (flatBT c\<^sub>1) b"
  sorry

text \<open>命題（scb分解の合成則） (§7.2):
  (1) if \<open>(s\<^sub>0,flat c\<^sub>0,b\<^sub>0)\<close> is an scb-decomposition of \<open>t\<close> (\<open>c\<^sub>0 \<in> PT\<^bsub>B\<^esub>\<close>) and
      \<open>(s\<^sub>1,c\<^sub>1,b\<^sub>1)\<close> is an scb-decomposition of \<open>c\<^sub>0\<close>, then \<open>(s\<^sub>0\<frown>s\<^sub>1, c\<^sub>1, b\<^sub>1\<frown>b\<^sub>0)\<close>
      is an scb-decomposition of \<open>t\<close>;
  (2) if \<open>(s,c,b)\<close> is an scb-decomposition of \<open>t\<close> then \<open>(D\<^sub>v s, c, b)\<close> is one of
      \<open>D\<^sub>v t\<close>.\<close>

lemma p_7_2_scb_compose:
  assumes "t \<in> T_B"
  shows "\<And>c\<^sub>0 s\<^sub>0 s\<^sub>1 c\<^sub>1 b\<^sub>1 b\<^sub>0.
            c\<^sub>0 \<in> T_B \<Longrightarrow> (\<exists>p. c\<^sub>0 = Trm [p]) \<Longrightarrow>
            scb_decomp t s\<^sub>0 (flatBT c\<^sub>0) b\<^sub>0 \<Longrightarrow>
            scb_decomp c\<^sub>0 s\<^sub>1 c\<^sub>1 b\<^sub>1 \<Longrightarrow>
            scb_decomp t (s\<^sub>0 @ s\<^sub>1) c\<^sub>1 (b\<^sub>1 @ b\<^sub>0)"
    and "\<And>v s c b. scb_decomp t s c b \<Longrightarrow>
            scb_decomp (Dpt (enat v) t) (Dsym (enat v) # s) c b"
  sorry

text \<open>命題（scb分解の自明性の判定条件） (§7.2): for \<open>(t,c) \<in> T\<^bsub>B\<^esub>\<^sup>Marked\<close> the
  following are equivalent: (1) \<open>t = c\<close>; (2) every scb-decomposition \<open>(s,flat c,b)\<close>
  of \<open>t\<close> has \<open>s = ()\<close> and \<open>b = ()\<close>; (3) some scb-decomposition \<open>((),flat c,b)\<close> of
  \<open>t\<close> exists.\<close>

lemma p_7_2_scb_triviality:
  assumes "(t, c) \<in> MarkedB"
  shows "(t = c)
       \<longleftrightarrow> (\<forall>s b. scb_decomp t s (flatBT c) b \<longrightarrow> s = [] \<and> b = [])"
    and "(t = c)
       \<longleftrightarrow> (\<exists>b. scb_decomp t [] (flatBT c) b)"
  sorry

text \<open>\<open>t\<close> が第\<open>0\<close>種 / 第\<open>1\<close>種 scb分解可能 (§7.2): some \<open>scb_kind0\<close> / \<open>scb_kind1\<close>
  decomposition of \<open>t\<close> exists.\<close>

abbreviation scb_kind0_able :: "BT \<Rightarrow> bool" where
  "scb_kind0_able t \<equiv> \<exists>s c b. scb_kind0 t s c b"

abbreviation scb_kind1_able :: "BT \<Rightarrow> bool" where
  "scb_kind1_able t \<equiv> \<exists>s c b. scb_kind1 t s c b"

text \<open>命題（scb分解の一意性） (§7.2):
  (1) the \<open>(s,b)\<close>-part of an scb-decomposition with a fixed \<open>c\<close> is unique;
  (2) \<open>dom(t) = \<nat>\<close> iff \<open>t\<close> is 第\<open>0\<close>種- or 第\<open>1\<close>種-scb-decomposable;
  (3) \<open>t\<close> is not both 第\<open>0\<close>種- and 第\<open>1\<close>種-scb-decomposable;
  (4) the 第\<open>0\<close>種 scb-decomposition of \<open>t\<close> is unique;
  (5) the 第\<open>1\<close>種 scb-decomposition of \<open>t\<close> is unique.\<close>

lemma p_7_2_scb_unique:
  assumes "t \<in> T_B"
  shows "\<And>s\<^sub>0 s\<^sub>1 c b\<^sub>0 b\<^sub>1.
            scb_decomp t s\<^sub>0 c b\<^sub>0 \<Longrightarrow> scb_decomp t s\<^sub>1 c b\<^sub>1 \<Longrightarrow>
            s\<^sub>0 = s\<^sub>1 \<and> b\<^sub>0 = b\<^sub>1"
    and "(domB t = NatSet) \<longleftrightarrow> (scb_kind0_able t \<or> scb_kind1_able t)"
    and "\<not> scb_kind0_able t \<or> \<not> scb_kind1_able t"
    and "\<And>s\<^sub>0 c\<^sub>0 b\<^sub>0 s\<^sub>1 c\<^sub>1 b\<^sub>1.
            scb_kind0 t s\<^sub>0 c\<^sub>0 b\<^sub>0 \<Longrightarrow> scb_kind0 t s\<^sub>1 c\<^sub>1 b\<^sub>1 \<Longrightarrow>
            (s\<^sub>0, c\<^sub>0, b\<^sub>0) = (s\<^sub>1, c\<^sub>1, b\<^sub>1)"
    and "\<And>s\<^sub>0 c\<^sub>0 b\<^sub>0 s\<^sub>1 c\<^sub>1 b\<^sub>1.
            scb_kind1 t s\<^sub>0 c\<^sub>0 b\<^sub>0 \<Longrightarrow> scb_kind1 t s\<^sub>1 c\<^sub>1 b\<^sub>1 \<Longrightarrow>
            (s\<^sub>0, c\<^sub>0, b\<^sub>0) = (s\<^sub>1, c\<^sub>1, b\<^sub>1)"
  sorry

text \<open>系（加法とscb分解の関係） (§7.2): for \<open>t \<in> T\<^bsub>B\<^esub>\<close>, \<open>c \<in> PT\<^bsub>B\<^esub>\<close>:
  (1) \<open>(t+c, c) \<in> T\<^bsub>B\<^esub>\<^sup>Marked\<close>;
  (2) if \<open>(s,flat c,b)\<close> is an scb-decomposition of \<open>t+c\<close>, then \<open>(s,flat c',b)\<close>
      is one of \<open>t+c'\<close>;
  (3) if \<open>s\<^sub>1\<frown>D\<^sub>v(t+c)\<frown>b\<^sub>1 \<in> T\<^bsub>B\<^esub>\<close> and \<open>(s\<^sub>0,flat c,b\<^sub>0)\<close> is an scb-decomposition of
      \<open>s\<^sub>1 D\<^sub>v(t+c) b\<^sub>1\<close>, then \<open>s\<^sub>1 D\<^sub>v(t+c') b\<^sub>1 \<in> T\<^bsub>B\<^esub>\<close> and \<open>(s\<^sub>0,flat c',b\<^sub>0)\<close> is
      an scb-decomposition of it.\<close>

lemma p_7_2_add_scb:
  assumes "t \<in> T_B" "c \<in> T_B" "\<exists>p. c = Trm [p]"
  shows "(t +\<^sub>B c, c) \<in> MarkedB"
    and "\<And>s b c'. c' \<in> T_B \<Longrightarrow> (\<exists>p. c' = Trm [p]) \<Longrightarrow>
            scb_decomp (t +\<^sub>B c) s (flatBT c) b \<Longrightarrow>
            scb_decomp (t +\<^sub>B c') s (flatBT c') b"
    and "\<And>v s\<^sub>0 s\<^sub>1 b\<^sub>0 b\<^sub>1 c' u\<^sub>1.
            c' \<in> T_B \<Longrightarrow> (\<exists>p. c' = Trm [p]) \<Longrightarrow>
            u\<^sub>1 \<in> T_B \<Longrightarrow> flatBT u\<^sub>1 = s\<^sub>1 @ (Dsym (enat v) # flatBT (t +\<^sub>B c)) @ b\<^sub>1 \<Longrightarrow>
            scb_decomp u\<^sub>1 s\<^sub>0 (flatBT c) b\<^sub>0 \<Longrightarrow>
            (\<exists>u\<^sub>1'. u\<^sub>1' \<in> T_B
                 \<and> flatBT u\<^sub>1' = s\<^sub>1 @ (Dsym (enat v) # flatBT (t +\<^sub>B c')) @ b\<^sub>1
                 \<and> scb_decomp u\<^sub>1' s\<^sub>0 (flatBT c') b\<^sub>0)"
  sorry

text \<open>命題（scb分解と基本列の関係） (§7.2):
  (1-1) \<open>t'\<^sub>0 + D\<^sub>v(t'\<^sub>1 + D\<^sub>0 0)[n] = t'\<^sub>0 + (D\<^sub>v t'\<^sub>1)\<cdot>(n+1)\<close>;
  (1-2) if \<open>(s, D\<^sub>u(t'\<^sub>0 + D\<^sub>v(t'\<^sub>1+D\<^sub>0 0)), b)\<close> is an scb-decomposition of \<open>t\<close>,
        then \<open>(s, D\<^sub>u(t'\<^sub>0 + (D\<^sub>v t'\<^sub>1)\<cdot>(n+1)), b)\<close> is one of \<open>t[n]\<close>;
  (2) if \<open>(s\<^sub>1,c\<^sub>2,b\<^sub>1)\<close> is a 第\<open>1\<close>種 scb-decomposition of \<open>t\<close> and
        \<open>(D\<^sub>u s\<^sub>0, D\<^sub>v 0, b\<^sub>0)\<close> is an scb-decomposition of \<open>c\<^sub>2\<close>, then \<open>v > u\<close> and
        the \<open>\<Sigma>\<close>-string of \<open>t[n]\<close> is
        \<open>s\<^sub>1 D\<^sub>u (s\<^sub>0 D\<^bsub>v-1\<^esub>)\<^bsup>n+1\<^esup> 0 b\<^sub>0\<^bsup>n+1\<^esup> b\<^sub>1\<close>.
  Modelling: BT fundamental sequence \<open>t[n] = operB t (numB<\<close>\<open>n)\<close> (numeral term);
  string powers \<open>x\<^bsup>k\<^esup> = concat (replicate k x)\<close>.\<close>

lemma p_7_2_scb_fseq:
  fixes v n :: nat
  shows "\<And>t'\<^sub>0 t'\<^sub>1. t'\<^sub>0 \<in> T_B \<Longrightarrow> t'\<^sub>1 \<in> T_B \<Longrightarrow>
            operB (t'\<^sub>0 +\<^sub>B Dpt (enat v) (t'\<^sub>1 +\<^sub>B Dpt 0 0\<^sub>B)) (numBT n)
              = t'\<^sub>0 +\<^sub>B multBT (Dpt (enat v) t'\<^sub>1) (n + 1)"
    and "\<And>t'\<^sub>0 t'\<^sub>1 t u s b.
            t'\<^sub>0 \<in> T_B \<Longrightarrow> t'\<^sub>1 \<in> T_B \<Longrightarrow> t \<in> T_B \<Longrightarrow>
            scb_decomp t s
              (flatBT (Dpt (enat u) (t'\<^sub>0 +\<^sub>B Dpt (enat v) (t'\<^sub>1 +\<^sub>B Dpt 0 0\<^sub>B)))) b \<Longrightarrow>
            scb_decomp (operB t (numBT n)) s
              (flatBT (Dpt (enat u) (t'\<^sub>0 +\<^sub>B multBT (Dpt (enat v) t'\<^sub>1) (n + 1)))) b"
    and "\<And>t u s\<^sub>0 s\<^sub>1 c\<^sub>2 b\<^sub>0 b\<^sub>1.
            t \<in> T_B \<Longrightarrow>
            scb_kind1 t s\<^sub>1 (flatBT c\<^sub>2) b\<^sub>1 \<Longrightarrow>
            scb_decomp c\<^sub>2 (Dsym (enat u) # s\<^sub>0) (flatBT (Dpt (enat v) 0\<^sub>B)) b\<^sub>0 \<Longrightarrow>
            v > u \<and>
            flatBT (operB t (numBT n)) =
              s\<^sub>1 @ (Dsym (enat u)
                # concat (replicate (n + 1) (s\<^sub>0 @ [Dsym (enat (v - 1))]))
                @ [Zsym]
                @ concat (replicate (n + 1) b\<^sub>0))
              @ b\<^sub>1"
  sorry

text \<open>命題（\<open>RightNodes\<close>と部分表現の関係） (§7.2): for strings \<open>s,b\<close>, \<open>v \<in> \<nat>\<close> and
  \<open>t \<in> PT\<^bsub>B\<^esub>\<close>, if \<open>b\<close> consists only of \<open>\<^bold>)\<close> and \<open>s\<frown>flat(D\<^sub>v 0)\<frown>b \<in> T\<^bsub>B\<^esub>\<close>, then
  \<open>s\<frown>flat(D\<^sub>v t)\<frown>b \<in> T\<^bsub>B\<^esub>\<close>, \<open>Lng(P(s D\<^sub>v t b)) = Lng(P(s D\<^sub>v 0 b))\<close>, and there are
  unique \<open>a\<^sub>0,a\<^sub>1 \<in> \<nat>\<^bsup><\<omega>\<^esup>\<close> with
  (1) \<open>RightNodes(s D\<^sub>v t b) = a\<^sub>0 \<frown> [v] \<frown> a\<^sub>1\<close>;
  (2) \<open>RightNodes(s D\<^sub>v 0 b) = a\<^sub>0 \<frown> [v]\<close>;
  (3) \<open>RightNodes(D\<^sub>v t) = [v] \<frown> a\<^sub>1\<close>.
  Modelling: \<open>P(\<dots>)\<close> on a string = \<open>P\<^bsub>B\<^esub>\<close> of the witnessing term \<open>unflatBT\<close>.\<close>

lemma p_7_2_RightNodes_subexpr:
  fixes v :: nat
  assumes "t \<in> T_B" "\<exists>p. t = Trm [p]"
    and "\<forall>x \<in> set b. x = RP"
    and "t\<^sub>0 \<in> T_B" "flatBT t\<^sub>0 = s @ flatBT (Dpt (enat v) 0\<^sub>B) @ b"
  shows "\<exists>t\<^sub>1. t\<^sub>1 \<in> T_B \<and> flatBT t\<^sub>1 = s @ flatBT (Dpt (enat v) t) @ b
            \<and> Lng (PB t\<^sub>1) = Lng (PB t\<^sub>0)
            \<and> (\<exists>!aa. RightNodes t\<^sub>1 = fst aa @ [v] @ snd aa
                  \<and> RightNodes t\<^sub>0 = fst aa @ [v]
                  \<and> RightNodes (Dpt (enat v) t) = [v] @ snd aa)"
  sorry


subsection \<open>§7.3 翻訳写像 (Trans / Mark)\<close>

text \<open>The principal-term constructor \<open>D\<^sub>v t = Trm [DB v t]\<close> (\<open>v :: enat\<close>); on the
  pair-sequence side the row-1 coefficients are \<open>nat\<close>, embedded via \<open>enat\<close>.\<close>

abbreviation Dpt :: "enat \<Rightarrow> BT \<Rightarrow> BT" where
  "Dpt v t \<equiv> Trm [DB v t]"

text \<open>The mutually exclusive conditions (I)–(VI) of the \<open>Trans\<close> recursion
  (article 2096–2106), for a reduced mono \<open>M\<close> with \<open>j\<^sub>1 = Lng M - 1 > 0\<close>.
  Here \<open>j\<^sub>0\<close> is the row-0 nearest ancestor of \<open>j\<^sub>1\<close>, modelled as \<open>parent M 0 j\<^sub>1\<close>
  (FAITHFULNESS: article \<open>j\<^sub>0 = max{j<j\<^sub>1 | (0,j) \<le>\<^sub>M (0,j\<^sub>1)}\<close>; coincidence with
  \<open>parent M 0 j\<^sub>1\<close> to be verified — see \<open>docs/trans-mark.md\<close>).\<close>

definition transCondI :: "pairseq \<Rightarrow> bool" where
  "transCondI M \<longleftrightarrow> entry M 1 (Lng M - 1) = 0 \<and> adm M (parent M 0 (Lng M - 1))"

definition transCondII :: "pairseq \<Rightarrow> bool" where
  "transCondII M \<longleftrightarrow> entry M 1 (Lng M - 1) = 0 \<and> \<not> adm M (parent M 0 (Lng M - 1))"

definition transCondIII :: "pairseq \<Rightarrow> bool" where
  "transCondIII M \<longleftrightarrow> entry M 1 (Lng M - 1) > 0
     \<and> entry M 1 (parent M 0 (Lng M - 1)) \<ge> entry M 1 (Lng M - 1)
     \<and> adm M (parent M 0 (Lng M - 1))"

definition transCondIV :: "pairseq \<Rightarrow> bool" where
  "transCondIV M \<longleftrightarrow> entry M 1 (Lng M - 1) > 0
     \<and> entry M 1 (parent M 0 (Lng M - 1)) \<ge> entry M 1 (Lng M - 1)
     \<and> \<not> adm M (parent M 0 (Lng M - 1))"

definition transCondV :: "pairseq \<Rightarrow> bool" where
  "transCondV M \<longleftrightarrow> entry M 1 (Lng M - 1) > 0
     \<and> entry M 1 (parent M 0 (Lng M - 1)) + 1 = entry M 1 (Lng M - 1)
     \<and> parent M 0 (Lng M - 1) + 1 < Lng M - 1"

definition transCondVI :: "pairseq \<Rightarrow> bool" where
  "transCondVI M \<longleftrightarrow> entry M 1 (Lng M - 1) > 0
     \<and> entry M 1 (parent M 0 (Lng M - 1)) + 1 = entry M 1 (Lng M - 1)
     \<and> parent M 0 (Lng M - 1) + 1 = Lng M - 1"

text \<open>The string-level connective \<open>s c b\<close> of the article (a \<open>\<Sigma>\<close>-string that is a
  valid term string) is realised at the \<open>BT\<close> level by \<open>unflatBT\<close>: the unique
  term whose \<open>flat\<close> is the given string (\<open>flatBT\<close> is injective on \<open>T\<^bsub>B\<^esub>\<close>).\<close>

definition unflatBT :: "Sym list \<Rightarrow> BT" where
  "unflatBT xs = (THE t. flatBT t = xs)"

text \<open>Accessors for a principal term \<open>D\<^sub>v t\<close> (its head index \<open>v\<close> and body \<open>t\<close>);
  total, with junk defaults off the principal shape.  Used to read \<open>c\<^sub>1 = D\<^sub>v t\<^sub>2\<close>
  and the left end \<open>D\<^bsub>M\<^sub>1\<^sub>,\<^sub>j\<^sub>0\<^esub>\<close> of \<open>P\<^bsub>B\<^esub>(t\<^sub>2)\<^bsub>J\<^sub>1\<^esub>\<close>.\<close>

fun bpHeadV :: "BT \<Rightarrow> enat" where
  "bpHeadV (Trm (DB v t # ps)) = v"
| "bpHeadV (Trm []) = 0"

fun bpHeadT :: "BT \<Rightarrow> BT" where
  "bpHeadT (Trm (DB v t # ps)) = t"
| "bpHeadT (Trm []) = 0\<^sub>B"

text \<open>翻訳写像 \<open>Trans\<close> / \<open>Mark\<close> (§7.3, article 2044–2180), a mutual recursion on
  \<open>Lng M\<close>.  Termination is deferred (like \<open>Red\<close> / \<open>RightNodes\<close> / \<open>domB\<close>): we use a
  catch-all \<open>function\<close> and \<open>pat_completeness\<close>, leaving the conditional \<open>psimps\<close>.
  The article's \<open>\<Sigma>\<close>-string connective \<open>s c b\<close> is realised by \<open>unflatBT\<close>.\<close>

function Trans :: "pairseq \<Rightarrow> BT" and Mark :: "pairseq \<Rightarrow> nat \<Rightarrow> BT" where
  "Trans M =
     (if M \<notin> RT_PS then Trans (Red M)
      else let j1 = Lng M - 1 in
        if j1 = 0 then
          (if (M::pairseq) ! 0 = (0,0) then 0\<^sub>B else Dpt (enat (entry M 1 0)) 0\<^sub>B)
        else if monoT M then
          (let t1 = Trans (Pred M) in
           if t1 = 0\<^sub>B then Dpt 0 (Dpt (enat (entry M 1 j1)) 0\<^sub>B)
           else
             let jp = parent M 0 j1;
                 c1 = Mark (Pred M) (Adm M jp);
                 v = bpHeadV c1;  t2 = bpHeadT c1;  J1 = Lng (PB t2) - 1;
                 pj = PB t2 ! J1;  leftDj0 = (bpHeadV pj = enat (entry M 1 jp));
                 t3 = (if leftDj0 then SigmaB (take J1 (PB t2)) else t2);
                 t4 = (if leftDj0 then bpHeadT pj else t2);
                 c2 = (if transCondI M \<or> transCondIII M \<or> transCondV M
                       then Dpt v (t2 +\<^sub>B Dpt (enat (entry M 1 j1)) 0\<^sub>B)
                       else if transCondVI M
                       then Dpt v (Dpt (enat (entry M 1 j1)) 0\<^sub>B)
                       else if t2 = 0\<^sub>B
                       then Dpt v (Dpt (enat (entry M 1 jp)) (Dpt (enat (entry M 1 j1)) 0\<^sub>B))
                       else Dpt v (t3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                          (t4 +\<^sub>B Dpt (enat (entry M 1 j1)) 0\<^sub>B)));
                 sb1 = (SOME sb. scb_decomp t1 (fst sb) (flatBT c1) (snd sb))
             in unflatBT (fst sb1 @ flatBT c2 @ snd sb1))
        else
          (let J1 = Lng (P M) - 1;  PJ = P M ! J1;  j0 = j1 - Lng PJ + 1 in
           if PJ = [(0,0)] then Trans (seg M 0 (j0 - 1)) +\<^sub>B Dpt 0 0\<^sub>B
           else Trans (seg M 0 (j0 - 1)) +\<^sub>B Trans PJ))"
| "Mark M m =
     (if M \<notin> RT_PS then Mark (Red M) m
      else let j1 = Lng M - 1 in
        if j1 = 0 then
          (if (M::pairseq) ! 0 = (0,0) then 0\<^sub>B else Dpt (enat (entry M 1 0)) 0\<^sub>B)
        else if monoT M then
          (let t1 = Trans (Pred M) in
           if t1 = 0\<^sub>B then
             (if m = 0 then Dpt 0 (Dpt (enat (entry M 1 j1)) 0\<^sub>B)
              else Dpt (enat (entry M 1 j1)) 0\<^sub>B)
           else
             let jp = parent M 0 j1;
                 c1 = Mark (Pred M) (Adm M jp);
                 v = bpHeadV c1;  t2 = bpHeadT c1;  J1 = Lng (PB t2) - 1;
                 pj = PB t2 ! J1;  leftDj0 = (bpHeadV pj = enat (entry M 1 jp));
                 t3 = (if leftDj0 then SigmaB (take J1 (PB t2)) else t2);
                 t4 = (if leftDj0 then bpHeadT pj else t2);
                 c2 = (if transCondI M \<or> transCondIII M \<or> transCondV M
                       then Dpt v (t2 +\<^sub>B Dpt (enat (entry M 1 j1)) 0\<^sub>B)
                       else if transCondVI M
                       then Dpt v (Dpt (enat (entry M 1 j1)) 0\<^sub>B)
                       else if t2 = 0\<^sub>B
                       then Dpt v (Dpt (enat (entry M 1 jp)) (Dpt (enat (entry M 1 j1)) 0\<^sub>B))
                       else Dpt v (t3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                          (t4 +\<^sub>B Dpt (enat (entry M 1 j1)) 0\<^sub>B)))
             in if m < j1 then
                  (let c0 = Mark (Pred M) m in
                   if (c0, c1) \<in> MarkedB
                   then let sm1 = (SOME sb. scb_decomp c0 (fst sb) (flatBT c1) (snd sb))
                        in unflatBT (fst sm1 @ flatBT c2 @ snd sm1)
                   else Dpt (enat (entry M 1 j1)) 0\<^sub>B)
                else Dpt (enat (entry M 1 j1)) 0\<^sub>B)
        else
          (let J1 = Lng (P M) - 1;  PJ = P M ! J1;  j0 = j1 - Lng PJ + 1 in
           if PJ = [(0,0)] then Dpt 0 0\<^sub>B
           else Mark PJ (m - j0)))"
  by pat_completeness auto

text \<open>命題（\<open>Trans\<close>の well-defined 性）(§7.3, 2184): the recursion determines a
  unique total \<open>Trans\<close>/\<open>Mark\<close>.  In Isabelle this is the totality of the
  \<open>function\<close>-domain (termination); deferred — not transcribed as a separate
  \<open>sorry\<close> lemma here.\<close>

text \<open>命題（\<open>2\<close>列ペア数列の基本性質） (§7.3, 2190).\<close>

lemma p_7_3_twoColumn:
  assumes "M \<in> RT_PS" "monoT M" "Lng M = 2"
  shows "Trans M = Dpt (enat (entry M 1 0)) (Dpt (enat (entry M 1 1)) 0\<^sub>B)"
    and "(M, 0) \<in> Marked" and "(M, 1) \<in> Marked"
    and "Mark M 0 = Dpt (enat (entry M 1 0)) (Dpt (enat (entry M 1 1)) 0\<^sub>B)"
    and "Mark M 1 = Dpt (enat (entry M 1 1)) 0\<^sub>B"
  sorry

text \<open>命題（\<open>Trans\<close>の\<open>(IncrFirst,Red)\<close>不変\<open>P\<close>同変性） (1) (§7.3, 2234).\<close>

lemma p_7_3_Trans_IncrFirst_Red:
  assumes "M \<in> T_PS"
  shows "Trans M = Trans (Red M)" and "Trans M = Trans (IncrFirst M)"
  sorry

text \<open>命題（\<open>Mark\<close>の\<open>(IncrFirst,Red,P)\<close>不変性） (1) (§7.3, 2246).\<close>

lemma p_7_3_Mark_IncrFirst_Red:
  assumes "(M, m) \<in> Marked"
  shows "Mark M m = Mark (Red M) m" and "Mark M m = Mark (IncrFirst M) m"
  sorry

text \<open>命題（\<open>Trans\<close>が零項性を保つこと） (§7.3, 2254).\<close>

lemma p_7_3_Trans_zeroT:
  assumes "M \<in> T_PS"
  shows "zeroT M \<longleftrightarrow> Trans M = 0\<^sub>B"
  sorry

text \<open>命題（\<open>c\<^sub>1\<close>と\<open>c\<^sub>2\<close>の大小関係） (§7.3, 2270): in the \<open>j\<^sub>1 > 0\<close>, \<open>t\<^sub>1 \<noteq> 0\<close> branch,
  \<open>c\<^sub>1\<close> and \<open>c\<^sub>2\<close> are principal and \<open>c\<^sub>1 < c\<^sub>2\<close>.  Uses the def-internal symbols
  \<open>c\<^sub>1\<close>/\<open>c\<^sub>2\<close>; to be stated once they are exposed as separate functions — deferred.\<close>

text \<open>命題（\<open>Pred\<close>の\<open>Trans\<close>に関する降下性） (§7.3, 2278).\<close>

lemma p_7_3_Pred_Trans_descend:
  assumes "M \<in> T_PS" "Lng M > 1"
  shows "lessBT (Trans (Pred M)) (Trans M)"
  sorry

text \<open>命題（右端第\<open>1\<close>基点の\<open>Mark\<close>の基本性質） (§7.3, 2296).\<close>

lemma p_7_3_Mark_rightmost1:
  assumes "(M, m) \<in> Marked" "M \<in> RT_PS"
  shows "(m = Lng M - 1) \<longleftrightarrow> (Mark M m = Dpt (enat (entry M 1 m)) 0\<^sub>B)"
  sorry

text \<open>命題（\<open>Trans\<close>が単項性を保つこと） (§7.3, 2358).  A \<open>BT\<close> term is principal
  (\<open>\<in> PT\<^bsub>B\<^esub>\<close>) iff it has a single principal component, i.e. \<open>Lng (P\<^bsub>B\<^esub> t) = 1\<close>.\<close>

lemma p_7_3_Trans_monoT:
  assumes "M \<in> T_PS"
  shows "monoT M \<longleftrightarrow>
           (Lng (PB (Trans M)) = 1 \<or> (zeroT (P M ! 0) \<and> Lng (P M) = 2))"
  sorry


subsection \<open>§7.4 許容的親子関係\<close>

text \<open>命題（\<open>Adm\<^sub>M\<close>と\<open><\<^bsub>M\<^esub>\<^sup>NextAdm\<close>の関係） — when \<open>j\<^sub>1 = Lng M - 1\<close> has a
  unique row-\<open>i\<close> parent \<open>j\<^sub>0\<close>, its admissibilization \<open>Adm\<^sub>M(j\<^sub>0)\<close> is the
  admissible parent of \<open>j\<^sub>1\<close>.  (This §7.4 proposition is \<open>Trans\<close>-free; the
  remaining §7.3 / §7.4 statements await the \<open>Trans\<close> / \<open>Mark\<close> definition.)\<close>

lemma p_7_4_Adm_nextAdm:
  assumes "M \<in> T_PS" "hasParent M i (Lng M - 1)"
  shows "nextAdm M i (Adm M (parent M i (Lng M - 1))) (Lng M - 1)"
  sorry


text \<open>命題（\<open>Trans\<close>と\<open><\<^bsub>M\<^esub>\<^sup>NextAdm\<close>の関係） (§7.4): for \<open>M \<in> T\<^bsub>PS\<^esub>\<close> with
  \<open>j\<^sub>1 = Lng M - 1\<close>, if there is a unique \<open>j\<^sub>0\<close> with
  \<open>(0,j\<^sub>0) <\<^bsub>M\<^esub>\<^sup>NextAdm (0,j\<^sub>1)\<close>, then there exist unique
  \<open>(s\<^sub>0,b\<^sub>0) \<in> (\<Sigma>\<^bsup><\<omega>\<^esup>)\<^sup>2\<close> such that
  \<open>(s\<^sub>0, Mark(Pred M, j\<^sub>0), b\<^sub>0)\<close> is an scb-decomposition of \<open>Trans(Pred M)\<close> and
  \<open>(s\<^sub>0, Mark(M, j\<^sub>0), b\<^sub>0)\<close> is an scb-decomposition of \<open>Trans M\<close>.\<close>

lemma p_7_4_Trans_nextAdm:
  assumes "M \<in> T_PS"
    and "\<exists>!j0. nextAdm M 0 j0 (Lng M - 1)"
  shows "\<exists>!sb. scb_decomp (Trans (Pred M))
                  (fst sb) (flatBT (Mark (Pred M) (THE j0. nextAdm M 0 j0 (Lng M - 1)))) (snd sb)
            \<and> scb_decomp (Trans M)
                  (fst sb) (flatBT (Mark M (THE j0. nextAdm M 0 j0 (Lng M - 1)))) (snd sb)"
  sorry

text \<open>系（\<open>Mark\<close>と\<open><\<^bsub>M\<^esub>\<^sup>NextAdm\<close>の関係） (§7.4): under the same hypotheses, with
  \<open>j\<^sub>0\<close> the unique NextAdm-parent of \<open>j\<^sub>1 = Lng M - 1\<close>, for any \<open>j\<close> with
  \<open>(0,j) \<le>\<^sub>M (0,j\<^sub>0)\<close> there exist unique \<open>(s\<^sub>0,b\<^sub>0)\<close> such that
  \<open>(s\<^sub>0, Mark(Pred M, j\<^sub>0), b\<^sub>0)\<close> is an scb-decomposition of \<open>Mark(Pred M, j)\<close> and
  \<open>(s\<^sub>0, Mark(M, j\<^sub>0), b\<^sub>0)\<close> is an scb-decomposition of \<open>Mark(M, j)\<close>.\<close>

lemma p_7_4_Mark_nextAdm:
  assumes "M \<in> T_PS"
    and "\<exists>!j0. nextAdm M 0 j0 (Lng M - 1)"
    and "leR M 0 j (THE j0. nextAdm M 0 j0 (Lng M - 1))"
  shows "\<exists>!sb. scb_decomp (Mark (Pred M) j)
                  (fst sb) (flatBT (Mark (Pred M) (THE j0. nextAdm M 0 j0 (Lng M - 1)))) (snd sb)
            \<and> scb_decomp (Mark M j)
                  (fst sb) (flatBT (Mark M (THE j0. nextAdm M 0 j0 (Lng M - 1)))) (snd sb)"
  sorry

text \<open>系（\<open>Trans\<close>の\<open>Mark\<close>と\<open>Pred\<close>による表示） (§7.4): for any
  \<open>(M,m) \<in> T\<^bsub>PS\<^esub>\<^sup>Marked\<close> (modelled by \<open>(M,m) \<in> Marked\<close>), if \<open>m < Lng M - 1\<close>
  then there exist unique \<open>(s\<^sub>0,b\<^sub>0)\<close> such that \<open>(s\<^sub>0, Mark(Pred M, m), b\<^sub>0)\<close> is an
  scb-decomposition of \<open>Trans(Pred M)\<close> and \<open>(s\<^sub>0, Mark(M, m), b\<^sub>0)\<close> is an
  scb-decomposition of \<open>Trans M\<close>.\<close>

lemma p_7_4_Trans_Mark_Pred:
  assumes "(M, m) \<in> Marked"
    and "m < Lng M - 1"
  shows "\<exists>!sb. scb_decomp (Trans (Pred M)) (fst sb) (flatBT (Mark (Pred M) m)) (snd sb)
            \<and> scb_decomp (Trans M) (fst sb) (flatBT (Mark M m)) (snd sb)"
  sorry

text \<open>系（\<open>Trans\<close>の\<open>Mark\<close>と切片による表示） (§7.4): for any
  \<open>(M,m) \<in> RT\<^bsub>PS\<^esub>\<^sup>Marked\<close> (modelled by \<open>(M,m) \<in> Marked \<and> M \<in> RT\<^bsub>PS\<^esub>\<close>), if
  \<open>0 < m < Lng M - 1\<close> then there exist unique \<open>(s\<^sub>0,b\<^sub>0)\<close> such that
  \<open>(s\<^sub>0, D\<^bsub>M\<^sub>1\<^sub>,\<^sub>m\<^esub> 0, b\<^sub>0)\<close> is an scb-decomposition of \<open>Trans((M\<^sub>j)\<^bsub>j=0\<^esub>\<^bsup>m\<^esup>)\<close> and
  \<open>(s\<^sub>0, Mark(M, m), b\<^sub>0)\<close> is an scb-decomposition of \<open>Trans M\<close>.  Here
  \<open>(M\<^sub>j)\<^bsub>j=0\<^esub>\<^bsup>m\<^esup> = seg M 0 m\<close> and \<open>D\<^bsub>M\<^sub>1\<^sub>,\<^sub>m\<^esub> 0 = Dpt (enat (entry M 1 m)) 0\<^sub>B\<close>.\<close>

lemma p_7_4_Trans_Mark_seg:
  assumes "(M, m) \<in> Marked" "M \<in> RT_PS"
    and "0 < m" "m < Lng M - 1"
  shows "\<exists>!sb. scb_decomp (Trans (seg M 0 m))
                  (fst sb) (flatBT (Dpt (enat (entry M 1 m)) 0\<^sub>B)) (snd sb)
            \<and> scb_decomp (Trans M) (fst sb) (flatBT (Mark M m)) (snd sb)"
  sorry

text \<open>系（\<open>RightNodes\<close>と\<open>Mark\<close>の関係） (§7.4): for any
  \<open>(M,m) \<in> RT\<^bsub>PS\<^esub>\<^sup>Marked\<close> (modelled by \<open>(M,m) \<in> Marked \<and> M \<in> RT\<^bsub>PS\<^esub>\<close>), if
  \<open>0 < m < Lng M - 1\<close> then there exist \<open>a\<^sub>0, a\<^sub>1 \<in> \<nat>\<^bsup><\<omega>\<^esup>\<close> such that
  \<open>RightNodes(Trans M) = a\<^sub>0 \<frown> (M\<^sub>1\<^sub>,\<^sub>m) \<frown> a\<^sub>1\<close>,
  \<open>RightNodes(Trans((M\<^sub>j)\<^bsub>j=0\<^esub>\<^bsup>m\<^esup>)) = a\<^sub>0 \<frown> (M\<^sub>1\<^sub>,\<^sub>m)\<close>, and
  \<open>RightNodes(Mark(M, m)) = (M\<^sub>1\<^sub>,\<^sub>m) \<frown> a\<^sub>1\<close>.  Here the article's \<open>\<oplus>\<^sub>\<nat>\<close> on
  \<open>\<nat>\<^bsup><\<omega>\<^esup>\<close> is list append \<open>@\<close>, and \<open>(M\<^sub>1\<^sub>,\<^sub>m) = [entry M 1 m]\<close>.\<close>

lemma p_7_4_RightNodes_Mark:
  assumes "(M, m) \<in> Marked" "M \<in> RT_PS"
    and "0 < m" "m < Lng M - 1"
  shows "\<exists>a0 a1. RightNodes (Trans M) = a0 @ [entry M 1 m] @ a1
              \<and> RightNodes (Trans (seg M 0 m)) = a0 @ [entry M 1 m]
              \<and> RightNodes (Mark M m) = [entry M 1 m] @ a1"
  sorry

text \<open>\<open>RightAnces : T\<^bsub>PS\<^esub> \<to> \<nat>\<^bsup><\<omega>\<^esup>\<close> (§7.4, article 2704–2741): a recursion on
  \<open>Lng M\<close> mirroring \<open>Trans\<close> (reduced/mono/multi/non-reduced; conditions (I)–(VI);
  \<open>j\<^sub>0 = parent M 0 j\<^sub>1\<close>, \<open>j\<^sub>-\<^sub>1 = Adm M j\<^sub>0\<close>).  Independent of \<open>Trans\<close>/\<open>Mark\<close>;
  termination deferred (like \<open>Trans\<close>/\<open>RightNodes\<close>).\<close>

function RightAnces :: "pairseq \<Rightarrow> nat list" where
  "RightAnces M =
     (if M \<notin> RT_PS then RightAnces (Red M)
      else let j1 = Lng M - 1 in
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
  by pat_completeness auto

text \<open>命題（\<open>RightNodes\<close>と\<open>RightAnces\<close>の関係） (§7.4, 2745).\<close>

lemma p_7_4_RightAnces_RightNodes:
  assumes "M \<in> T_PS"
  shows "RightAnces M = RightNodes (Trans M)"
  sorry

text \<open>系（非零項の\<open>RightAnces\<close>が非空であること） (§7.4, 2809).\<close>

lemma p_7_4_RightAnces_zeroT:
  assumes "M \<in> T_PS"
  shows "zeroT M \<longleftrightarrow> RightAnces M = []"
  sorry

end
