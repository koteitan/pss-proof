theory M_8_7_Bwo_Well_Ordering_Residue
  imports M_8_7_Wcl_Collapse_Obstruction
begin

text \<open>Relocated proof material.  The declarations retain their original source order,
  and every relocated annotation is preserved below.  This theory is machine-checked
  outside the termination build tree.\<close>

text \<open>The converse: the residual is EXACTLY \<^term>\<open>wf RPrel\<close>-strength (no
  overshoot).  If \<^term>\<open>wf RPrel\<close> then every principal is accessible, so every
  term is in \<open>W\<^sup>*\<close>.\<close>

lemma bwo_Wstar_total_of_wf:
  assumes "wf RPrel"
  shows "bwo_Wstar_total"
proof (unfold bwo_Wstar_total_def, intro allI impI)
  fix t assume "isOT_BT t" and "dfree_BT t"
  have all: "\<forall>p. p \<in> Wellfounded.acc RPrel" using assms wfs_wf_iff_all_acc by blast
  show "t \<in> bwo_Wstar" unfolding bwo_Wstar_def using all by blast
qed

theorem bwo_2_2_wf_iff: "bwo_Wstar_total \<longleftrightarrow> wf RPrel"
  using bwo_2_2_wf bwo_Wstar_total_of_wf by blast

text \<open>\<open>A\<^sub>\<nu>(X,a)\<close> is monotone in the level bound \<open>\<nu>\<close> (only the \<open>T\<^sub>u\<close> clause
  depends on \<open>\<nu>\<close>, through \<open>u < \<nu>\<close>).  Buchholz's \<open>A\<^sub>u(X) \<subseteq> A\<^sub>\<nu>(X)\<close> for \<open>u \<le> \<nu>\<close>.\<close>

lemma bwo_Aop_mono_nv:
  assumes le: "nv \<le> nv'" and a: "bwo_Aop nv X a"
  shows "bwo_Aop nv' X a"
proof -
  consider "a = Trm []"
    | "(domB a = {Trm []} \<or> domB a = NatSet) \<and> (\<forall>n. operB a (numBT n) \<in> X)"
    | u where "enat u < nv" "domB a = TBv (enat u)" "\<forall>z \<in> bwo_Wlev u. operB a z \<in> X"
    using a[unfolded bwo_Aop_def] by blast
  thus ?thesis
  proof cases
    case 1 thus ?thesis unfolding bwo_Aop_def by blast
  next
    case 2 thus ?thesis unfolding bwo_Aop_def by blast
  next
    case (3 u)
    have "enat u < nv'" using 3(1) le by (rule less_le_trans)
    thus ?thesis using 3(2) 3(3) unfolding bwo_Aop_def by blast
  qed
qed

subsection \<open>(5) [Buc1] Lemma 2.4(a): shift closure \<open>A\<^sub>\<nu>(X\<^bsup>(a)\<^esup>) \<subseteq> X\<^bsup>(a)\<^esup>\<close>\<close>

text \<open>Faithful transcription of [Buc1] p.138 Lemma 2.4(a).  Assume \<open>X\<close> is
  \<open>A\<^sub>\<nu>\<close>-closed and \<open>a \<in> X\<close>; then every \<open>b\<close> with \<open>A\<^sub>\<nu>(X\<^bsup>(a)\<^esup>, b)\<close> lies in
  \<open>X\<^bsup>(a)\<^esup>\<close>, i.e. \<open>a + b \<in> X\<close>.  The three cases (\<open>b = 0\<close>; \<open>dom(b) \<in> {{0},\<nat>}\<close>;
  \<open>dom(b) = T\<^sub>u\<close>) use the glue \<open>dom(a+b)=dom(b)\<close> and \<open>(a+b)[z]=a+b[z]\<close> to
  transport the \<open>A\<^sub>\<nu>\<close>-witness for \<open>b\<close> into one for \<open>a+b\<close>.\<close>

lemma bwo_2_4a_shift_closure:
  assumes Acl: "\<And>c. bwo_Aop nv X c \<Longrightarrow> c \<in> X"
    and aX: "a \<in> X"
    and body: "bwo_Aop nv (bwo_shift a X) b"
  shows "b \<in> bwo_shift a X"
proof -
  have goal: "a +\<^sub>B b \<in> X"
  proof -
    consider (zero) "b = Trm []"
      | (num) "(domB b = {Trm []} \<or> domB b = NatSet)
               \<and> (\<forall>n. operB b (numBT n) \<in> bwo_shift a X)"
      | (tu) u where "enat u < nv" "domB b = TBv (enat u)"
               "\<forall>z \<in> bwo_Wlev u. operB b z \<in> bwo_shift a X"
      using body[unfolded bwo_Aop_def] by blast
    thus ?thesis
    proof cases
      case zero
      thus ?thesis using aX bwo_addBT_Nil_right by simp
    next
      case num
      have bne: "b \<noteq> Trm []"
      proof
        assume z: "b = Trm []"
        have dz: "domB b = {}" using z bwo_domB_Nil by simp
        have "numBT 0 \<in> NatSet" by (simp add: NatSet_def)
        moreover have "Trm [] \<in> {Trm []}" by simp
        ultimately show False using conjunct1[OF num] dz by auto
      qed
      have d: "domB (a +\<^sub>B b) = {Trm []} \<or> domB (a +\<^sub>B b) = NatSet"
        using conjunct1[OF num] bwo_addBT_domB[OF bne] by simp
      have op: "\<forall>n. operB (a +\<^sub>B b) (numBT n) \<in> X"
      proof (intro allI)
        fix n
        have "operB b (numBT n) \<in> bwo_shift a X" using conjunct2[OF num] by blast
        hence "a +\<^sub>B operB b (numBT n) \<in> X" by (simp add: bwo_shift_def)
        thus "operB (a +\<^sub>B b) (numBT n) \<in> X"
          using bwo_addBT_operB[OF bne] by simp
      qed
      have "bwo_Aop nv X (a +\<^sub>B b)"
        using d op unfolding bwo_Aop_def by blast
      thus ?thesis by (rule Acl)
    next
      case (tu u)
      have bne: "b \<noteq> Trm []"
      proof
        assume z: "b = Trm []"
        have "TBv (enat u) = {}" using z tu(2) bwo_domB_Nil by simp
        moreover have "Trm [] \<in> TBv (enat u)" by (simp add: TBv_def)
        ultimately show False by simp
      qed
      have d: "domB (a +\<^sub>B b) = TBv (enat u)"
        using tu(2) bwo_addBT_domB[OF bne] by simp
      have op: "\<forall>z \<in> bwo_Wlev u. operB (a +\<^sub>B b) z \<in> X"
      proof
        fix z assume zW: "z \<in> bwo_Wlev u"
        have "operB b z \<in> bwo_shift a X" using tu(3) zW by blast
        hence "a +\<^sub>B operB b z \<in> X" by (simp add: bwo_shift_def)
        thus "operB (a +\<^sub>B b) z \<in> X"
          using bwo_addBT_operB[OF bne] by simp
      qed
      have "bwo_Aop nv X (a +\<^sub>B b)"
        using tu(1) d op unfolding bwo_Aop_def by blast
      thus ?thesis by (rule Acl)
    qed
  qed
  show ?thesis using goal by (simp add: bwo_shift_def)
qed

text \<open>[Buc1] Lemma 2.5, sub-result (1): \<open>\<forall>u<\<nu>. a + D\<^bsub>u+1\<^esub>0 \<in> X\<close> (p.138).  This is
  the ONLY step of Lemma 2.5 that invokes Buchholz's leastness
  (A2) \<open>A\<^sub>u(Y) \<subseteq> Y \<Longrightarrow> W\<^sub>u \<subseteq> Y\<close>.  For the \<^emph>\<open>acc\<close>-based \<open>bwo_Wlev\<close> of this
  development (A2) is the \<^bold>\<open>hard\<close> direction — it says
  \<open>{z. D\<^sub>u z \<in> acc} \<subseteq>\<close> every \<open>A\<^sub>u\<close>-closed set, i.e. the fundamental sequences are
  cofinal in the \<open><\<close>-predecessors of \<open>D\<^sub>u z\<close> (Buchholz's genuine \<section>2/\<section>3 content,
  NOT free here because \<open>bwo_Wlev\<close> is defined via \<open>acc\<close>, not as the least fixpoint
  of \<open>A\<^sub>u\<close>).  It is carried as the explicit hypothesis \<open>A2\<close>, isolating it as THE
  residual; everything else — 2.4(a), the level monotonicity \<open>A\<^sub>u \<subseteq> A\<^sub>\<nu>\<close>, and the
  \<open>+\<^sub>B\<close>/\<open>domB\<close>/\<open>operB\<close> glue — is discharged.\<close>

lemma bwo_2_5_sub1:
  assumes Acl: "\<And>c. bwo_Aop nv X c \<Longrightarrow> c \<in> X"
    and aX: "a \<in> X"
    and A2: "\<And>Y. (\<And>c. bwo_Aop (enat u) Y c \<Longrightarrow> c \<in> Y) \<Longrightarrow> bwo_Wlev u \<subseteq> Y"
    and ult: "enat u < nv"
  shows "a +\<^sub>B Trm [DB (enat (Suc u)) (Trm [])] \<in> X"
proof -
  let ?D = "Trm [DB (enat (Suc u)) (Trm [])] :: BT"
  have Dne: "?D \<noteq> Trm []" by simp
  have domAD: "domB (a +\<^sub>B ?D) = TBv (enat u)"
    using bwo_addBT_domB[OF Dne] bwo_domB_Dsucc0 by simp
  have opAD: "\<And>z. operB (a +\<^sub>B ?D) z = a +\<^sub>B z"
  proof -
    fix z
    have "operB (a +\<^sub>B ?D) z = a +\<^sub>B operB ?D z" by (rule bwo_addBT_operB[OF Dne])
    also have "\<dots> = a +\<^sub>B z" using bwo_operB_Dsucc0 by simp
    finally show "operB (a +\<^sub>B ?D) z = a +\<^sub>B z" .
  qed
  \<comment> \<open>2.4(a): \<open>X\<^bsup>(a)\<^esup>\<close> is \<open>A\<^sub>\<nu>\<close>-closed, hence \<open>A\<^sub>u\<close>-closed since \<open>A\<^sub>u \<subseteq> A\<^sub>\<nu>\<close>\<close>
  have shiftAu: "\<And>c. bwo_Aop (enat u) (bwo_shift a X) c \<Longrightarrow> c \<in> bwo_shift a X"
  proof -
    fix c assume "bwo_Aop (enat u) (bwo_shift a X) c"
    hence bnv: "bwo_Aop nv (bwo_shift a X) c"
      by (rule bwo_Aop_mono_nv[OF less_imp_le[OF ult]])
    show "c \<in> bwo_shift a X" by (rule bwo_2_4a_shift_closure[OF Acl aX bnv])
  qed
  \<comment> \<open>(A2): \<open>W\<^sub>u \<subseteq> X\<^bsup>(a)\<^esup>\<close>\<close>
  have WsubShift: "bwo_Wlev u \<subseteq> bwo_shift a X" by (rule A2[OF shiftAu])
  have azX: "\<And>z. z \<in> bwo_Wlev u \<Longrightarrow> a +\<^sub>B z \<in> X"
  proof -
    fix z assume "z \<in> bwo_Wlev u"
    hence "z \<in> bwo_shift a X" using WsubShift by blast
    thus "a +\<^sub>B z \<in> X" by (simp add: bwo_shift_def)
  qed
  have opX: "\<forall>z \<in> bwo_Wlev u. operB (a +\<^sub>B ?D) z \<in> X"
  proof
    fix z assume "z \<in> bwo_Wlev u"
    hence "a +\<^sub>B z \<in> X" by (rule azX)
    thus "operB (a +\<^sub>B ?D) z \<in> X" using opAD by simp
  qed
  have "bwo_Aop nv X (a +\<^sub>B ?D)"
    using ult domAD opX unfolding bwo_Aop_def by blast
  thus ?thesis by (rule Acl)
qed


section \<open>Additional relocated campaign annotations\<close>

subsection \<open>(7) STATUS — the EXACT residual after r68: the surgery TRANSPORT\<close>

text \<open>
  \<^bold>\<open>What is now proven (unconditionally).\<close>  @{thm [source] ox8_body_rspine_lessBT}:
  for the census host \<open>M\<close> (\<open>ST_PS\<close>, \<open>PT_PS\<close>, \<open>hasParent\<close>, \<open>1 < Lng M - 1\<close>,
  \<open>condIII \<or> condIV\<close>, \<open>Trans M \<in> OT\<^bsub>B\<^esub>\<close>, \<open>ltJ\<close>) EVERY right-spine sub-body of
  \<open>body = bpHeadT (Trans (s84x_N M))\<close> is \<^emph>\<open>strictly below \<open>body\<close>\<close>.  This is the
  \<^bold>\<open>self-maximality\<close> of the census spine — the fact the SETLE1 descent needs, and
  (per STEP-0) the only true one: the spine head word is NOT monotone (3379
  strict drops among 11306 levels), and the stepwise chain
  \<open>Y\<^sub>k < Y\<^bsub>k-1\<^esub>\<close> is FALSE (2274/11306), so nothing weaker than the direct
  \<open>G\<close>-condition bound can produce it.

  \<^bold>\<open>The one remaining gap: the surgery TRANSPORT.\<close>  The census \<open>spineH\<close>
  (@{thm [source] ox6_SETLE1_reduce_restr}) compares the peel bodies of the
  \<^emph>\<open>surgered\<close> trees: with \<open>X\<^sub>0 = D\<^bsub>ub\<^esub>0\<close>, \<open>X\<^sub>1 = d4vx_ins s\<^sub>0 ub b\<^sub>0 X\<^sub>0\<close>,
  \<open>A\<^sub>1 = d4vx_ins s\<^sub>0 ub b\<^sub>0 A\<^sub>0\<close>, it needs
  \[ \<open>leBT (ox8_rsub A\<^sub>1 k) X\<^sub>1\<close> \qquad (k \<ge> 1), \]
  whereas the \<open>G\<close>-descent gives the \<^emph>\<open>leaf\<close>-version
  \<open>lessBT (ox8_rsub body k) body\<close>.  \<open>X\<^sub>1\<close> / \<open>A\<^sub>1\<close> are \<open>body\<close> with its deepest-right
  LEAF principal \<open>D\<^bsub>v\<^sub>1\<^esub>0\<close> replaced by \<open>D\<^bsub>ub\<^esub>X\<^sub>0\<close> / \<open>D\<^bsub>ub\<^esub>A\<^sub>0\<close> (\<open>ub = v\<^sub>1 - 1 < v\<^sub>1\<close>),
  and the peel keeps the two sides aligned: at every align3 level the three
  trees share \<open>(qs, w, sc, bc)\<close> (@{thm [source] ox7_align3_track}), so the peel
  bodies are \<open>lbB = ox8_rsub body k\<close>, \<open>lbX = ox8_rsub X\<^sub>1 k\<close>, \<open>lbA = ox8_rsub A\<^sub>1 k\<close>
  with the SAME context.  The needed lemma is therefore exactly

  \<^bold>\<open>TRANSPORT\<close>: \<open>flatBT WB = s \<frown> flat (D\<^bsub>v\<^sub>1\<^esub>0) \<frown> b\<close>, \<open>flatBT WX = s \<frown> flat (D\<^bsub>ub\<^esub>X\<^sub>0) \<frown> b\<close>,
  \<open>flatBT tB = sc \<frown> flat (D\<^bsub>v\<^sub>1\<^esub>0) \<frown> bc\<close>, \<open>flatBT tA = sc \<frown> flat (D\<^bsub>ub\<^esub>A\<^sub>0) \<frown> bc\<close>,
  \<open>b, bc\<close> all-\<open>RP\<close>, \<open>s = pre \<frown> sc\<close> with \<open>pre \<noteq> []\<close>, \<open>ub < v\<^sub>1\<close>, and
  \<open>lessBT tB WB\<close>  \<Longrightarrow>  \<open>lessBT tA WX\<close>.

  STEP-0 validates TRANSPORT as verdict-INVARIANCE (11306/11306: the verdict of
  \<open>lessBT (level-k body with hole content \<open>Q\<close>) X\<^sub>1\<close> is the same for
  \<open>Q \<in> {0, X\<^sub>0, A\<^sub>0, BIG}\<close>), i.e. the first difference lies strictly ABOVE the hole
  body.  Its proof is a lock-step first-difference induction: the surgery only
  ever touches the LAST principal of each right-spine level
  (@{thm [source] scb_to_last_component}), while the \<open>lessBT\<close> recursion walks the
  principal lists from the LEFT, so at every position either (i) the compared
  principals are hole-free — hence literally identical in the leaf- and the
  surgered version, and the verdict transports verbatim; or (ii) the compared
  principal is the hole-carrying last one, where the surgery is a strict
  DECREASE (\<open>D\<^bsub>ub\<^esub>Q < D\<^bsub>v\<^sub>1\<^esub>0\<close> by \<open>ub < v\<^sub>1\<close>, @{thm [source] scbext_lessBT}), so a
  verdict \<open>'<'\<close> on the left is preserved and an EQUALITY on the left becomes a
  strict \<open>'<'\<close> — the same verdict as the leaf version's prefix rule.

  \<^bold>\<open>The one case that needs a census input\<close> (and hence the exact Isar
  obstruction).  The dangerous branch of (ii) is when the comparison reaches the
  hole-carrying last principal of the RIGHT operand (\<open>WX\<close>) while the left operand
  (\<open>tA\<close>) still offers a hole-FREE principal at that index — there the surgery
  \<^emph>\<open>lowers the right side\<close> and a leaf-version \<open>'<'\<close> could flip.  This requires
  \<open>|principal list of tA| > |principal list of WX|\<close> at a common peel depth.  STEP-0
  shows it never happens on real census hosts, because EVERY right-spine level of
  \<open>X\<^sub>1\<close> above the hole is a \<^bold>\<open>pure chain\<close> (a single principal; 11306/11306), so the
  right operand's list has length 1 and the comparison at index 0 is exactly the
  hole-carrying principal on both sides.  The missing brick is therefore either
  (a) the chain-ness of the census spine — \<open>ox8_lastT\<close>-levels of \<open>body\<close> above the
  hole have a single principal (a \<open>Trans\<close>-image geometry fact), or (b) a
  head-hypothesis strong enough to rule the flip out
  (\<open>bpHeadV\<close> of the left operand's index-\<open>|QS|\<close> principal \<open>< W\<close>, which for the
  hole level follows from \<open>descP\<close> + \<open>ub < v\<^sub>1 \<le> W\<close> only when that principal is the
  hole itself).  Everything else in TRANSPORT is elementary
  (@{thm [source] scbext_lessBT}, @{thm [source] ox7_align3_track},
  @{thm [source] ox7_headlt_lessBT}).

  \<^bold>\<open>Assembly once TRANSPORT lands\<close>: TRANSPORT + @{thm [source] ox8_body_rspine_lessBT}
  give \<open>spineH\<close> of @{thm [source] ox6_SETLE1_reduce_restr} (the \<open>tx' \<in> G\<^sub>u X\<^sub>1\<close>
  witness is not even needed — the align3-track suffix relation \<open>s\<^sub>0 = pre \<frown> sc\<close>,
  \<open>pre \<noteq> []\<close>, is what the engine really supplies), hence the census
  \<open>SETLE1_ltJ\<close> slot of @{thm [source] oi8_census_final_ivadmeq}, leaving
  \<open>{FINRC}\<close> only.
\<close>

(* ===== end r68 ox8 block (part 1: the G-descent source; residual = TRANSPORT) ===== *)


(* =====================================================================
   r68 bwl block.  Prefix  bwl_  ([Buc1] \<section>2 with the CORRECT semantics for
   \<open>W\<^sub>v\<close>: the LEAST FIXPOINT of the accessibility operator \<open>A\<^sub>v\<close>).
   ===================================================================== *)

text \<open>\<^bold>\<open>Why this block exists.\<close>  Round 66 transcribed [Buc1] \<section>2 but defined the
  level sets by \<^emph>\<open>accessibility\<close>, \<open>bwo_Wlev u = {z. D\<^sub>u z \<in> acc RPrel}\<close>.  With that
  reading Buchholz's leastness principle

    (A2)  \<open>A\<^sub>u(Y) \<subseteq> Y \<Longrightarrow> W\<^sub>u \<subseteq> Y\<close>

  is NOT free — it becomes a cofinality statement about fundamental sequences —
  and round 67 had to carry it as an explicit hypothesis of
  @{thm [source] bwo_2_5_sub1}.  But in [1] p.137 \<open>W\<^sub>v\<close> is by DEFINITION the
  \<^bold>\<open>iterated inductive definition\<close> generated by

    (W1) \<open>0 \<in> W\<^sub>v\<close>;
    (W2) \<open>dom(a) \<in> {{0}, \<nat>}\<close>, \<open>\<forall>n. a[n] \<in> W\<^sub>v\<close> \<Longrightarrow> \<open>a \<in> W\<^sub>v\<close>;
    (W3) \<open>dom(a) = T\<^sub>u\<close> with \<open>u < v\<close>, \<open>\<forall>z \<in> W\<^sub>u. a[z] \<in> W\<^sub>v\<close> \<Longrightarrow> \<open>a \<in> W\<^sub>v\<close>

  i.e. \<open>W\<^sub>v = lfp (A\<^sub>v)\<close> where the LOWER levels \<open>W\<^sub>u\<close> \<open>(u < v)\<close> occur as
  \<^emph>\<open>parameters\<close> (this is exactly why it is an ITERATED inductive definition: the
  occurrence of \<open>W\<^sub>u\<close> in (W3) is not monotone in the set being generated, so the
  whole family cannot be produced by a single \<open>lfp\<close>).  With that definition
  (A1) and (A2) are the fixpoint equation and the induction rule of the
  \<open>lfp\<close> — FREE.  We rebuild the \<section>2 machinery on that basis.\<close>

(* ===== end r68 bwl part 1 (lfp semantics: A1/A2/W1/W2/W3/level-mono FREE) ===== *)

subsection \<open>(3) [Buc1] Lemma 2.4 on the \<open>lfp\<close> semantics\<close>

text \<open>2.4(a) \<open>A\<^sub>\<nu>(X) \<subseteq> X\<close>, \<open>a \<in> X\<close> \<Longrightarrow> \<open>A\<^sub>\<nu>(X\<^bsup>(a)\<^esup>) \<subseteq> X\<^bsup>(a)\<^esup>\<close> — same proof as
  @{thm [source] bwo_2_4a_shift_closure}, but for the family-parametric \<open>bwl_Aop\<close>
  (the lower levels enter only as an opaque set, so the argument is unchanged).\<close>

end
