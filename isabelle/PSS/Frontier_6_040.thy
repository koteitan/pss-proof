theory Frontier_6_040
  imports Support_6_022
begin

lemma descending_Br_of_branch_le0:
  assumes M'T: "seg M j0' j1' \<in> T_PS"
    and brle: "TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1
               \<or> le0 (seg M j0' j1') (TrMax (seg M j0' j1') + 1) (Lng (seg M j0' j1') - 1)"
  shows "descending (Br (seg M j0' j1'))"
proof -
  let ?M' = "seg M j0' j1'"
  let ?Yp = "seg ?M' (TrMax ?M' + 1) (Lng ?M' - 1)"
  show ?thesis
  proof (cases "TrMax ?M' = Lng ?M' - 1")
    case True
    have "Br ?M' = []" using True by (simp add: Br_def)
    thus ?thesis by (simp add: descending_def)
  next
    case Trne: False
    have tb: "TrMax ?M' \<le> Lng ?M' - 1" by (rule TrMax_bound[OF M'T])
    with Trne have trlt: "TrMax ?M' < Lng ?M' - 1" by linarith
    have BrM': "Br ?M' = P ?Yp" using Trne by (simp add: Br_def)
    \<comment> \<open>the residual le0 holds (the \<open>TrMax = end\<close> disjunct is excluded by \<open>Trne\<close>)\<close>
    have le0Yp: "le0 ?M' (TrMax ?M' + 1) (Lng ?M' - 1)" using brle Trne by blast
    \<comment> \<open>\<open>Y\<^sub>p\<close> is non-multi: when \<open>1 < Lng Y\<^sub>p\<close> it is \<open>monoT\<close> via @{thm [source] monoT_seg_of_le0}\<close>
    have YpNonMulti: "\<not> (multiT ?Yp \<and> 1 < Lng ?Yp)"
    proof (cases "1 < Lng ?Yp")
      case False thus ?thesis by simp
    next
      case LYp: True
      have LYp': "Lng ?Yp = Suc (Lng ?M' - 1) - (TrMax ?M' + 1)" by (simp only: Lng_seg)
      have ab: "TrMax ?M' + 1 < Lng ?M' - 1" using LYp LYp' by linarith
      have blt: "Lng ?M' - 1 < Lng ?M'" using trlt by linarith
      have "monoT ?Yp" by (rule monoT_seg_of_le0[OF blt ab le0Yp])
      thus ?thesis by (simp add: multiT_def)
    qed
    have PYp: "P ?Yp = [?Yp]" by (rule poper_P_nonmulti[OF YpNonMulti])
    show ?thesis using BrM' PYp by (simp add: descending_def)
  qed
qed

text \<open>(The over-general \<open>slice_P_tiebreak\<close> stub was REMOVED: the d0pos branch's
  \<open>brle\<close>-true case is now fully proven by @{thm [source] descending_Br_of_branch_le0}
  (single component), and only the \<open>\<not>brle\<close> multi-component case remains as an inline
  residual sorry inside the d0pos closure — docs continued 33.)\<close>

text \<open>§6.8 d1pos \<open>\<not>brle\<close> REGIME A assembly (the GREEN regime-A instance of the main
  identification stub \<open>oper_d1pos_notbrle_LOW_take_eq\<close>, below).  In regime A the
  \<open>M\<close>-side branch region start \<open>A = j'\<^sub>0 + TrMax M' + 1\<close> sits STRICTLY below the period
  base \<open>j\<^sub>m\<^sub>2 = parent N 1 (Lng N-1)\<close> (\<open>Areg\<close>), so the LOW prefix is read \<open>N\<close>-verbatim
  (\<open>shamt = 0\<close>) and the witnesses are \<open>j\<^sub>0\<^sup>red = j'\<^sub>0\<close>, \<open>j\<^sub>1\<^sup>red = Lng N-1\<close>.  PURE WIRING of
  the GREEN regime-A geometry:
  (1) @{thm [source] oper_d1pos_notbrle_Br_align_regA} gives \<open>TrMax M' = TrMax N\<^sub>p\<close> (TrEq)
      and both \<open>Br = P(seg ..)\<close> reshapes with both branches non-empty;
  (2) @{thm [source] oper_d1pos_anchor_coincide_regA2} gives \<open>c = cN\<close> / \<open>F8end\<close> / \<open>F9end\<close>
      (no \<open>clt\<close>/\<open>cNlt\<close> needed — derived internally);
  (3) @{thm [source] oper_d1pos_branch_collapse_concrete} (with \<open>shamt = 0\<close>,
      \<open>lowshift\<close> via @{thm [source] oper_d1pos_branch_lowshift_regA},
      \<open>butl\<close> via @{thm [source] oper_d1pos_branch_butl}) folds \<open>P S\<close> to
      \<open>butlast (P Snside) @ [last (P S)]\<close>, so \<open>LOW = butlast (Br N\<^sub>p)\<close> VERBATIM;
  (4) @{thm [source] oper_d1pos_tail_junction} lifts \<open>F8end\<close>/\<open>F9end\<close> to the tail node.
  DEEP-VERIFIED rank 10 (KMAX=10, /tmp/regA_c_chk.py: 537/537 regime-A cases,
  \<open>c=cN\<close>/\<open>F8end\<close>/\<open>F9end\<close> with \<open>c = IdxSum (P S)!(len-1)\<close>, 0 failures; full wiring
  \<open>butlast verbatim\<close>/\<open>lenLOW\<close>/\<open>F8\<close>/\<open>F9\<close> 99/99 at KMAX=7).\<close>

text \<open>§6.8 d0pos \<open>\<not>brle\<close> CONTEXT SIDE-FACTS (sub-agent ctxhyp).  The regime-A
  assembly lemma (\<open>oper_d1pos_notbrle_LOW_take_eq_regA\<close>, below) and the regime-B
  anchor coincidence (@{thm [source] oper_d1pos_anchor_coincide_regB2}) carry
  several facts as EXTRA hypotheses that the final assembly must discharge from
  the main-stub context
  (\<open>N\<close> std monoT d1pos: \<open>i\<^sub>1=1\<close>, \<open>hasParent\<close>, \<open>jm2 = parent N 1 (Lng N-1) < Lng N-1\<close>).
  Here we prove the purely \<open>N\<close>-side ones (\<open>dpos\<close>, \<open>r1le\<close>) directly from the d1pos
  parent relation \<open>nextrel1 N jm2 (Lng N-1)\<close>.

  \<open>dpos\<close>: \<open>entry N 0 jm2 < entry N 0 (Lng N-1)\<close>.  The parent gives the row-0
  ancestry chain \<open>(nextrel0 N)\<^sup>*\<^sup>* jm2 (Lng N-1)\<close>; since \<open>jm2 < Lng N-1\<close> (\<open>j0lt\<close>),
  @{thm [source] le0_ances_aux} turns the chain into the STRICT increase.
  \<open>r1le\<close>: \<open>entry N 1 jm2 \<le> entry N 1 (Lng N-1)\<close>, in fact STRICT, read straight off
  the \<open>nextrel1\<close> definition.\<close>

lemma oper_d1pos_ctx_dpos:
  assumes hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
  shows "entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1)"
proof -
  let ?jm2 = "parent N 1 (Lng N - 1)"  let ?j1 = "Lng N - 1"
  have hp1: "hasParent N 1 ?j1" using hp i1z by simp
  have parR: "nextR N 1 ?jm2 ?j1"
    using hp1 unfolding hasParent_def parent_def by (rule theI')
  have "leR N 0 ?jm2 ?j1" using poper_nextR_imp_le0[OF parR] by simp
  hence rc: "(nextrel0 N)\<^sup>*\<^sup>* ?jm2 ?j1" by (simp add: leR_def le0_def)
  show ?thesis using le0_ances_aux[OF rc] j0lt by blast
qed

lemma oper_d1pos_ctx_r1le:
  assumes hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
  shows "entry N 1 (parent N 1 (Lng N - 1)) \<le> entry N 1 (Lng N - 1)"
proof -
  let ?jm2 = "parent N 1 (Lng N - 1)"  let ?j1 = "Lng N - 1"
  have hp1: "hasParent N 1 ?j1" using hp i1z by simp
  have parR: "nextR N 1 ?jm2 ?j1"
    using hp1 unfolding hasParent_def parent_def by (rule theI')
  hence "nextrel1 N ?jm2 ?j1" by (simp add: nextR_def)
  thus ?thesis by (simp add: nextrel1_def)
qed

text \<open>§6.8 d0pos \<open>\<not>brle\<close> STRUCTURAL side-facts (sub-agent struc).  The two regime
  assembly lemmas (\<open>oper_d1pos_notbrle_LOW_take_eq_regA\<close> /
  \<open>_regB\<close>, below) carry several STRUCTURAL facts as extra hypotheses.  Here we prove the
  two that are THEOREMS of the main-stub context (\<open>j0lt\<close>, \<open>multiM\<close>); the remaining
  three (\<open>AltN\<close>, \<open>multiNp\<close>, \<open>j0pge\<close>) are NOT derivable from the stub hyps — they
  are genuine REGIME-SPLIT conditions (see the blocker note at the assembly site).

  \<open>j0lt\<close>: \<open>parent N 1 (Lng N-1) < Lng N-1\<close>.  The d1pos parent relation
  \<open>nextR N 1 jm2 (Lng N-1)\<close> (from \<open>hasParent\<close>/\<open>idx1=1\<close>, via @{thm [source] theI'})
  unfolds to \<open>nextrel1 N jm2 (Lng N-1)\<close>, whose definition has \<open>jm2 < Lng N-1\<close>
  as a conjunct.  (rank 10: /tmp/struc_verify.py 3602/3602.)\<close>

lemma oper_d1pos_ctx_j0lt:
  assumes hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
  shows "parent N 1 (Lng N - 1) < Lng N - 1"
proof -
  let ?jm2 = "parent N 1 (Lng N - 1)"  let ?j1 = "Lng N - 1"
  have hp1: "hasParent N 1 ?j1" using hp i1z by simp
  have parR: "nextR N 1 ?jm2 ?j1"
    using hp1 unfolding hasParent_def parent_def by (rule theI')
  hence "nextrel1 N ?jm2 ?j1" by (simp add: nextR_def)
  thus ?thesis by (simp add: nextrel1_def)
qed

text \<open>\<open>multiM\<close>: \<open>1 < length (P (seg M A j1'))\<close> with \<open>A = j0' + TrMax M' + 1\<close>,
  \<open>M' = seg M j0' j1'\<close>.  The branch region \<open>S = seg M A j1'\<close> is a slice-of-slice:
  by @{thm [source] seg_of_seg}, \<open>S = seg M' (TrMax M'+1) (Lng M'-1)\<close>.  We reduce
  \<open>1 < length (P S)\<close> to \<open>multiT S\<close> (@{thm [source] m_6_2_P_components_2}); then
  \<open>multiT S = \<not>zeroT S \<and> \<not>monoT S\<close>, and \<open>monoT S\<close> would need \<open>le0 S 0 (Lng S-1)\<close>,
  which by @{thm [source] adm_le0_seg} on \<open>M'\<close> equals \<open>le0 M' (TrMax M'+1) (Lng M'-1)\<close>
  — the second \<open>notbrle\<close> disjunct, FALSE.  The same \<open>\<not>le0\<close> forces \<open>Lng S > 1\<close>
  (else \<open>le0 S 0 0\<close> reflexive), hence \<open>\<not>zeroT S\<close>.  (rank 10: /tmp/struc_verify.py
  3602/3602.)\<close>

lemma oper_d1pos_ctx_multiM:
  fixes M :: pairseq
  assumes M'T: "seg M j0' j1' \<in> T_PS"
    and lt: "j0' < j1'"
    and notbrle: "\<not> (TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1
                     \<or> le0 (seg M j0' j1') (TrMax (seg M j0' j1') + 1) (Lng (seg M j0' j1') - 1))"
  shows "1 < length (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1'))"
proof -
  let ?M' = "seg M j0' j1'"
  let ?t  = "TrMax ?M'"
  let ?A  = "j0' + ?t + 1"
  let ?S  = "seg M ?A j1'"
  \<comment> \<open>the two \<open>notbrle\<close> conjuncts\<close>
  have trne: "?t \<noteq> Lng ?M' - 1" using notbrle by blast
  have notle0: "\<not> le0 ?M' (?t + 1) (Lng ?M' - 1)" using notbrle by blast
  \<comment> \<open>geometry of \<open>M'\<close>: \<open>Lng M' = Suc j1' - j0'\<close>, \<open>TrMax M' < Lng M' - 1\<close>\<close>
  have lenM': "Lng ?M' = Suc j1' - j0'" by (rule Lng_seg)
  have tb: "?t \<le> Lng ?M' - 1" by (rule TrMax_bound[OF M'T])
  have tlt: "?t < Lng ?M' - 1" using tb trne by linarith
  have j0le: "j0' \<le> j1'" using lt by simp
  \<comment> \<open>\<open>S = seg M' (TrMax M'+1) (Lng M'-1)\<close> by @{thm [source] seg_of_seg}\<close>
  have dle: "Lng ?M' - 1 \<le> j1' - j0'" using lenM' by linarith
  have segS: "seg ?M' (?t + 1) (Lng ?M' - 1) = seg M (j0' + (?t + 1)) (j0' + (Lng ?M' - 1))"
    by (rule seg_of_seg[OF j0le dle])
  have e1: "j0' + (?t + 1) = ?A" by simp
  have e2: "j0' + (Lng ?M' - 1) = j1'" using lenM' j0le by simp
  have Seq: "?S = seg ?M' (?t + 1) (Lng ?M' - 1)" using segS e1 e2 by simp
  \<comment> \<open>\<open>le0 S 0 (Lng S - 1) \<longleftrightarrow> le0 M' (TrMax M'+1) (Lng M'-1)\<close> via @{thm [source] adm_le0_seg}\<close>
  have LngS: "Lng ?S = Suc j1' - ?A" by (rule Lng_seg)
  have LngSeq: "Lng ?S = Lng ?M' - 1 - ?t" using LngS lenM' tlt by linarith
  \<comment> \<open>side-conditions for @{thm [source] adm_le0_seg} on \<open>M'\<close>, window \<open>[t+1, Lng M'-1]\<close>\<close>
  have c1: "Lng ?M' - 1 < Lng ?M'" using lenM' lt by linarith
  have c2: "(0::nat) \<le> (Lng ?M' - 1) - (?t + 1)" by simp
  have c3: "Lng ?S - 1 \<le> (Lng ?M' - 1) - (?t + 1)" using LngSeq by simp
  have c4: "?t + 1 \<le> Lng ?M' - 1" using tlt by simp
  have admeq: "le0 (seg ?M' (?t + 1) (Lng ?M' - 1)) 0 (Lng ?S - 1)
             \<longleftrightarrow> le0 ?M' ((?t + 1) + 0) ((?t + 1) + (Lng ?S - 1))"
    by (rule adm_le0_seg[OF c1 c2 c3 c4])
  \<comment> \<open>rewrite the two endpoints of the RHS \<open>le0\<close> to \<open>(t+1)\<close> / \<open>Lng M'-1\<close> explicitly\<close>
  have lhseq: "(?t + 1) + 0 = ?t + 1" by simp
  have endeq: "(?t + 1) + (Lng ?S - 1) = Lng ?M' - 1" using LngSeq tlt by simp
  have rhsR: "le0 ?M' ((?t + 1) + 0) ((?t + 1) + (Lng ?S - 1))
            = le0 ?M' (?t + 1) (Lng ?M' - 1)"
    by (rule arg_cong2[where f = "le0 ?M'", OF lhseq endeq])
  have admR: "le0 (seg ?M' (?t + 1) (Lng ?M' - 1)) 0 (Lng ?S - 1)
            = le0 ?M' (?t + 1) (Lng ?M' - 1)"
    using admeq rhsR by simp
  have le0Siff: "le0 ?S 0 (Lng ?S - 1) = le0 ?M' (?t + 1) (Lng ?M' - 1)"
    by (subst Seq) (rule admR)
  have notle0S: "\<not> le0 ?S 0 (Lng ?S - 1)" using le0Siff notle0 by simp
  \<comment> \<open>\<open>Lng S > 1\<close>: else \<open>le0 S 0 0\<close> reflexive, contradicting \<open>\<not>le0 S 0 (Lng S-1)\<close>\<close>
  have Spos: "0 < Lng ?S" using LngSeq tlt by linarith
  have LngS1: "1 < Lng ?S"
  proof (rule ccontr)
    assume "\<not> 1 < Lng ?S"
    hence "Lng ?S = 1" using Spos by linarith
    hence "Lng ?S - 1 = 0" by simp
    moreover have "le0 ?S 0 0" using Spos by (rule le0_refl)
    ultimately show False using notle0S by simp
  qed
  \<comment> \<open>\<open>S \<in> T_PS\<close> and \<open>\<not>zeroT S\<close>; then \<open>\<not>monoT S\<close> from \<open>\<not>le0 S 0 (Lng S-1)\<close>\<close>
  have Sne: "?S \<noteq> []"
  proof
    assume "?S = []"
    hence "Lng ?S = 0" by simp
    thus False using Spos by simp
  qed
  have ST: "?S \<in> T_PS" using Sne by (simp add: T_PS_def)
  have nzS: "\<not> zeroT ?S" using LngS1 by (simp add: zeroT_def)
  have nmS: "\<not> monoT ?S"
  proof
    assume "monoT ?S"
    hence "leR ?S 0 0 (Lng ?S - 1)" by (simp add: monoT_def)
    hence "le0 ?S 0 (Lng ?S - 1)" by (simp add: leR_def)
    thus False using notle0S by simp
  qed
  have multiS: "multiT ?S" using nzS nmS by (simp add: multiT_def)
  show ?thesis using m_6_2_P_components_2[OF ST] multiS by simp
qed

text \<open>§6.8 d1pos GEOMETRY-HYP dischargers (agent geomhyp).
  §6.8 d1pos ROW-0 verbatim agreement of the oper.  At every index
  \<open>x \<le> Lng N-1\<close> the row-0 value of \<open>N[n]\<close> equals \<open>N\<close>'s row-0 value
  (NB: row-1 does NOT agree at the block boundary \<open>x = Lng N-1\<close>, where it folds
  to \<open>entry N 1 j\<^sub>m\<^sub>2\<close>, so only the row-0 statement holds).  Three regions:
  the prefix \<open>x < j\<^sub>m\<^sub>2\<close> reads off \<open>N\<close> verbatim (@{thm [source] oper_d1pos_nth_prefix});
  block 0 (\<open>j\<^sub>m\<^sub>2 \<le> x < Lng N-1\<close>, \<open>q = 0\<close>, shift \<open>0\<cdot>\<delta> = 0\<close>) is @{thm [source] oper_d1pos_entry0}
  at \<open>q=0\<close>; the boundary \<open>x = Lng N-1 = j\<^sub>m\<^sub>2 + 1\<cdot>w + 0\<close> is block 1 (\<open>q=1<n\<close>, \<open>s=0\<close>)
  whose shift \<open>1\<cdot>\<delta> = entry N 0 (Lng N-1) - entry N 0 j\<^sub>m\<^sub>2\<close> exactly refills the gap, so
  \<open>entry N 0 j\<^sub>m\<^sub>2 + 1\<cdot>\<delta> = entry N 0 (Lng N-1)\<close>.  \<open>1 < n\<close> is forced by \<open>Lng N-1 < Lng (N[n])\<close>
  (@{thm [source] oper_d1pos_LngM}: \<open>Lng (N[n]) = j\<^sub>m\<^sub>2 + n\<cdot>w\<close>, so \<open>j\<^sub>m\<^sub>2+w < j\<^sub>m\<^sub>2+n\<cdot>w\<close> needs
  \<open>1 < n\<close>).  DEEP-VERIFIED (/tmp/le0Np_route.py: row-0 coincidence 0/4308 bad on
  \<open>[0,Lng N-1]\<close>; /tmp/row1_endpoint.py: row-1 differs 340/340 at the boundary).\<close>

lemma oper_d1pos_row0_agree:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and bnd: "Lng N - 1 < Lng ((N::pairseq)[n])"
    and x: "x \<le> Lng N - 1"
  shows "entry ((N::pairseq)[n]) 0 x = entry N 0 x"
proof -
  let ?j0 = "parent N 1 (Lng N - 1)"  let ?w = "Lng N - 1 - ?j0"
  let ?delta = "entry N 0 (Lng N - 1) - entry N 0 ?j0"
  have w0: "0 < ?w" using j0lt by linarith
  have LngNn: "Lng ((N::pairseq)[n]) = ?j0 + n * ?w"
    by (rule oper_d1pos_LngM[OF L notzero hp i1z j0lt])
  have n1: "1 < n"
  proof -
    have "?j0 + ?w < ?j0 + n * ?w" using bnd LngNn j0lt by linarith
    hence "?w < n * ?w" by linarith
    thus ?thesis using w0 by (cases n) auto
  qed
  show ?thesis
  proof (cases "x < ?j0")
    case True
    have "((N::pairseq)[n]) ! x = N ! x"
      by (rule oper_d1pos_nth_prefix[OF L notzero hp i1z True])
    thus ?thesis by (simp add: entry_def)
  next
    case False
    hence ge: "?j0 \<le> x" by simp
    show ?thesis
    proof (cases "x = Lng N - 1")
      case False
      hence xlt: "x < Lng N - 1" using x by simp
      have s: "x - ?j0 < ?w" using xlt ge by linarith
      have q0n: "(0::nat) < n" using n1 by simp
      have split: "x = ?j0 + 0 * ?w + (x - ?j0)" using ge by simp
      have "entry ((N::pairseq)[n]) 0 (?j0 + 0 * ?w + (x - ?j0))
            = entry N 0 (?j0 + (x - ?j0)) + 0 * ?delta"
        by (rule oper_d1pos_entry0[OF L notzero hp i1z j0lt q0n s])
      hence "entry ((N::pairseq)[n]) 0 x = entry N 0 (?j0 + (x - ?j0))"
        using split by simp
      thus ?thesis using ge by simp
    next
      case True
      have s0: "(0::nat) < ?w" using w0 .
      have q1n: "(1::nat) < n" using n1 .
      have split: "Lng N - 1 = ?j0 + 1 * ?w + (0::nat)" using j0lt by simp
      have "entry ((N::pairseq)[n]) 0 (?j0 + 1 * ?w + (0::nat))
            = entry N 0 (?j0 + (0::nat)) + 1 * ?delta"
        by (rule oper_d1pos_entry0[OF L notzero hp i1z j0lt q1n s0])
      hence "entry ((N::pairseq)[n]) 0 (Lng N - 1)
            = entry N 0 ?j0 + ?delta" using split by simp
      also have "\<dots> = entry N 0 (Lng N - 1)"
      proof -
        have "entry N 0 ?j0 \<le> entry N 0 (Lng N - 1)"
          using oper_d1pos_ctx_dpos[OF hp i1z j0lt] by simp
        thus ?thesis by simp
      qed
      finally show ?thesis using True by simp
    qed
  qed
qed

text \<open>§6.8 d1pos ROW-0-only \<open>nextrel0\<close> transfer across a shared row-0 prefix.
  Mirror of @{thm [source] nextrel0_prefix_imp} but the hypothesis is the
  row-0 agreement only (\<open>nextrel0\<close> reads no row-1 data).\<close>

lemma nextrel0_prefix_row0:
  assumes agree: "\<And>j. j \<le> c \<Longrightarrow> entry M 0 j = entry N 0 j"
    and cN: "c < Lng N"
    and xy: "x \<le> c" "y \<le> c"
    and h: "nextrel0 M x y"
  shows "nextrel0 N x y"
proof -
  from h have hx: "x < y" and hv: "entry M 0 x < entry M 0 y"
    and hmid: "\<And>j. x < j \<Longrightarrow> j < y \<Longrightarrow> entry M 0 y \<le> entry M 0 j"
    by (auto simp: nextrel0_def)
  show ?thesis
    unfolding nextrel0_def
  proof (intro conjI allI impI)
    show "x < Lng N" using xy(1) cN by linarith
    show "y < Lng N" using xy(2) cN by linarith
    show "x < y" by (rule hx)
    show "entry N 0 x < entry N 0 y" using hv agree[OF xy(1)] agree[OF xy(2)] by simp
    fix j assume "x < j \<and> j < y"
    hence j1: "x < j" and j2: "j < y" by auto
    have jc: "j \<le> c" using j2 xy(2) by linarith
    show "entry N 0 y \<le> entry N 0 j" using hmid[OF j1 j2] agree[OF xy(2)] agree[OF jc] by simp
  qed
qed

text \<open>§6.8 d1pos ROW-0-only \<open>le0\<close> transfer across a shared row-0 prefix.  Mirror of
  @{thm [source] le0_prefix_agree} with the row-0-only hypothesis.\<close>

lemma le0_prefix_row0:
  assumes agree: "\<And>j. j \<le> c \<Longrightarrow> entry M 0 j = entry N 0 j"
    and cM: "c < Lng M" and cN: "c < Lng N"
    and ac: "a \<le> c" and bc: "b \<le> c"
    and le: "le0 M a b"
  shows "le0 N a b"
proof -
  have rM: "(nextrel0 M)\<^sup>*\<^sup>* a b" using le by (simp add: le0_def)
  have "b \<le> c \<longrightarrow> (nextrel0 N)\<^sup>*\<^sup>* a b"
    using rM
  proof (induction rule: rtranclp_induct)
    case base show ?case by simp
  next
    case (step y z)
    show ?case
    proof
      assume zc: "z \<le> c"
      have yz: "nextrel0 M y z" using step.hyps(2) .
      have ylt: "y < z" using yz by (simp add: nextrel0_def)
      have yc: "y \<le> c" using ylt zc by linarith
      have "(nextrel0 N)\<^sup>*\<^sup>* a y" using step.IH yc by simp
      moreover have "nextrel0 N y z"
        by (rule nextrel0_prefix_row0[OF agree cN yc zc yz])
      ultimately show "(nextrel0 N)\<^sup>*\<^sup>* a z" by simp
    qed
  qed
  hence "(nextrel0 N)\<^sup>*\<^sup>* a b" using bc by simp
  thus ?thesis using ac bc cN by (simp add: le0_def)
qed

text \<open>§6.8 d1pos \<open>le0Np\<close> context discharger: \<open>le0 N j'\<^sub>0 (Lng N-1)\<close>.  The CRITICAL
  extra hypothesis of both regime assembly lemmas.  Two bricks:
  (a) ENDPOINT RESTRICTION of \<open>le0M : le0 M j'\<^sub>0 j'\<^sub>1\<close> down to \<open>le0 M j'\<^sub>0 (Lng N-1)\<close>
      via @{thm [source] m_5_1_ancestor_tree_1} (\<open>M\<in>T_PS\<close>, \<open>j'\<^sub>0 \<le> Lng N-1 \<le> j'\<^sub>1\<close>);
      the boundary index \<open>Lng N-1\<close> lies on the row-0 ancestry chain because
      \<open>j'\<^sub>1 \<ge> Lng N-1\<close> (\<open>bge\<close>) — DEEP-VERIFIED (/tmp/le0M_split.py: \<open>le0 M j'\<^sub>0 (Lng N-1)\<close>
      0/2253 FALSE);
  (b) ROW-0 TRANSFER \<open>M \<to> N\<close> on \<open>[0, Lng N-1]\<close> via @{thm [source] le0_prefix_row0}
      (@{thm [source] oper_d1pos_row0_agree}); row-0 of \<open>N[n]\<close> = \<open>N\<close> verbatim there.
  DEEP-VERIFIED (/tmp/regB_assembly_deep.py 1344/1344 regime B; /tmp/le0Np_route.py
  0/3370 FALSE under the exact main-stub hyps).\<close>

lemma oper_d1pos_ctx_le0Np:
  fixes N :: pairseq and M :: pairseq
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and Neq: "M = (N::pairseq)[n]"
    and le0M: "le0 M j0' j1'"
    and j0plt: "j0' < Lng N - 1"
    and jM: "j1' < Lng M"
    and bge: "Lng N - 1 \<le> j1'"
  shows "le0 N j0' (Lng N - 1)"
proof -
  let ?c = "Lng N - 1"
  have MT: "M \<in> T_PS" using jM unfolding T_PS_def by (cases M) auto
  \<comment> \<open>(a) endpoint restriction of \<open>le0M\<close> down to the boundary \<open>Lng N-1\<close>\<close>
  have leRM: "leR M 0 j0' j1'" using le0M by (simp add: leR_def)
  have j0'le: "j0' \<le> ?c" using j0plt by simp
  have leRMc: "leR M 0 j0' ?c"
    by (rule m_5_1_ancestor_tree_1[OF MT leRM j0'le bge])
  have le0Mc: "le0 M j0' ?c" using leRMc by (simp add: leR_def)
  \<comment> \<open>(b) row-0 transfer \<open>M \<to> N\<close> on \<open>[0, Lng N-1]\<close>\<close>
  have cltM: "?c < Lng M"
  proof -
    have "Lng N - 1 < Lng ((N::pairseq)[n])" using bge jM Neq by simp
    thus ?thesis using Neq by simp
  qed
  have cltN: "?c < Lng N" using L by simp
  have bnd: "Lng N - 1 < Lng ((N::pairseq)[n])" using cltM Neq by simp
  have agree: "\<And>j. j \<le> ?c \<Longrightarrow> entry M 0 j = entry N 0 j"
  proof -
    fix j assume jc: "j \<le> ?c"
    have "entry ((N::pairseq)[n]) 0 j = entry N 0 j"
      by (rule oper_d1pos_row0_agree[OF L notzero hp i1z j0lt bnd jc])
    thus "entry M 0 j = entry N 0 j" using Neq by simp
  qed
  show ?thesis
    by (rule le0_prefix_row0[OF agree cltM cltN j0'le order.refl le0Mc])
qed

text \<open>§6.8 d1pos \<open>\<not>brle\<close> CELL-4 (PERIODIC-TAIL) UNIFIED anchor coincidence
  (perfix-A).  Replaces the FALSE-hyp BOUNDARY dispatch (\<open>mLmin_SnB\<close>/\<open>cleB\<close>) of
  the periodic-tail cell \<open>oper_d1pos_notbrle_LOW_take_eq_periodic\<close>.  Both anchors satisfy
  \<open>c, c\<^sub>N \<le> m = Lng Snside - 1\<close> and the ALL-BUT-LAST prefix is a clean
  \<open>(IncrFirst^^shamt)\<close>-shift (\<open>shiftEq\<close>, deep-verified 8019/8019 at rank 12);
  the single boundary node at \<open>m\<close> shifts by \<open>shamt\<close> in row 0 (\<open>boundEq0\<close>) and is
  \<open>\<le>\<close> in row 1 (\<open>boundEq1\<close>, both 8019/8019).  This covers the regime where the
  \<open>M\<close>-side branch \<open>S\<close> may CROSS the period boundary (\<open>Lng S > Lng Snside\<close>) with the
  anchor STRICTLY below the boundary (\<open>c = c\<^sub>N < m\<close>, the 458/3369 boundary cases
  where the OLD \<open>mLmin_SnB\<close>/\<open>cleB\<close> are FALSE) AS WELL AS the anchor-at-boundary
  case (\<open>c = c\<^sub>N = m\<close>).  Derivation: \<open>P (seg S 0 (m-1)) = map (shift) (P (seg Snside
  0 (m-1)))\<close> from \<open>shiftEq\<close> (@{thm [source] P_funpow_IncrFirst}); relate both
  butlasts to it by cases on \<open>c < m\<close> — STRICT uses the regime-agnostic
  @{thm [source] P_butlast_take_at_anchor} on BOTH operands; the BOUNDARY \<open>c = m\<close>
  identifies the prefix directly with @{thm [source] oper_d1pos_branch_butl}.  The
  length count (\<open>shift\<close> preserves component lengths, @{thm [source] Lng_funpow_IncrFirst})
  gives \<open>c = c\<^sub>N\<close>; junction entries from the prefix shift (\<open>c < m\<close>) or
  \<open>boundEq0\<close>/\<open>boundEq1\<close> (\<open>c = m\<close>).  NO \<open>mLmin\<close>, NO \<open>cle\<close>, NO IH.\<close>

lemma oper_d1pos_anchor_coincide_period_unified:
  fixes S :: pairseq and Snside :: pairseq and shamt :: nat
  defines "c \<equiv> IdxSum (P S) ! (length (P S) - 1)"
      and "cN \<equiv> IdxSum (P Snside) ! (length (P Snside) - 1)"
  assumes ST: "S \<in> T_PS" and multi: "1 < length (P S)"
    and SnT: "Snside \<in> T_PS" and multiN: "1 < length (P Snside)"
    and mleS: "Lng Snside - 1 \<le> Lng S - 1"
    and cleM: "IdxSum (P S) ! (length (P S) - 1) \<le> Lng Snside - 1"
    and lenPSeq: "length (P S) = length (P Snside)"
    and shiftEq: "seg S 0 (Lng Snside - 1 - 1)
                = (IncrFirst ^^ shamt) (seg Snside 0 (Lng Snside - 1 - 1))"
    and boundEq0: "entry S 0 (Lng Snside - 1) = entry Snside 0 (Lng Snside - 1) + shamt"
    and boundEq1: "entry S 1 (Lng Snside - 1) \<le> entry Snside 1 (Lng Snside - 1)"
  shows "c = cN"
    and "entry S 0 c = entry Snside 0 cN + shamt"
    and "entry S 1 c \<le> entry Snside 1 cN"
proof -
  let ?m = "Lng Snside - 1"
  \<comment> \<open>anchor structural data on both operands\<close>
  have c0: "0 < c" unfolding c_def by (rule oper_d1pos_branch_anchor(1)[OF ST multi])
  have cleS: "c \<le> Lng S - 1" unfolding c_def by (rule oper_d1pos_branch_anchor(2)[OF ST multi])
  have cleM': "c \<le> ?m" unfolding c_def using cleM by simp
  have cN0: "0 < cN" unfolding cN_def by (rule oper_d1pos_branch_anchor(1)[OF SnT multiN])
  have cNlem: "cN \<le> ?m" unfolding cN_def by (rule oper_d1pos_branch_anchor(2)[OF SnT multiN])
  have mpos: "0 < ?m" using cN0 cNlem by linarith
  have Snpos: "0 < Lng Snside" using mpos by linarith
  have Spos: "0 < Lng S" using cleS c0 by linarith
  have mleS': "?m \<le> Lng S" using mleS Spos by linarith
  have mleSn': "?m \<le> Lng Snside" by simp
  \<comment> \<open>butlast identities at the respective anchors (regime-agnostic)\<close>
  have butS_anchor: "butlast (P S) = P (seg S 0 (c - 1))"
    using oper_d1pos_branch_butl[OF ST multi] unfolding c_def by simp
  have butSn_anchor: "butlast (P Snside) = P (seg Snside 0 (cN - 1))"
    using oper_d1pos_branch_butl[OF SnT multiN] unfolding cN_def by simp
  \<comment> \<open>the prefix shift at \<open>m-1\<close>, lifted to \<open>P\<close>\<close>
  have PpreEq: "P (seg S 0 (?m - 1)) = map (IncrFirst ^^ shamt) (P (seg Snside 0 (?m - 1)))"
    using shiftEq by (simp add: P_funpow_IncrFirst)
  have butlPpreEq: "butlast (P (seg S 0 (?m - 1)))
                  = map (IncrFirst ^^ shamt) (butlast (P (seg Snside 0 (?m - 1))))"
    using PpreEq by (simp add: map_butlast)
  \<comment> \<open>uniform anchor offsets: \<open>c\<close>/\<open>cN\<close> are the all-but-last \<open>P\<close>-length totals\<close>
  have cbutl: "c = sum_list (map length (butlast (P S)))"
    unfolding c_def by (simp add: idxsum_nth butlast_conv_take)
  have cNbutl: "cN = sum_list (map length (butlast (P Snside)))"
    unfolding cN_def by (simp add: idxsum_nth butlast_conv_take)
  \<comment> \<open>common shifted prefix length \<open>Lpre = length (P (seg \<cdot> 0 (m-1)))\<close> (shift preserves count)\<close>
  have Lpre_eq: "length (P (seg S 0 (?m - 1))) = length (P (seg Snside 0 (?m - 1)))"
    using PpreEq by simp
  \<comment> \<open>boundary-status bridge: for an anchor \<open>a \<le> m \<le> Lng X\<close>, the component count of
     \<open>X\<close> is the prefix count when \<open>a < m\<close>, one MORE when \<open>a = m\<close>.  We extract:
     \<open>length (P X) = length (P (seg X 0 (m-1))) + (if anchor=m then 1 else 0)\<close>.\<close>
  have lenStat_S:
    "length (P S) = length (P (seg S 0 (?m - 1))) + (if c = ?m then 1 else 0)"
  proof (cases "c < ?m")
    case True
    have eqb: "butlast (P (seg S 0 (?m - 1))) = butlast (P S)"
      using P_butlast_take_at_anchor[OF ST multi True[unfolded c_def] mleS'] c_def by simp
    have "length (P (seg S 0 (?m - 1))) - 1 = length (P S) - 1"
      using eqb by (metis length_butlast)
    moreover have "0 < length (P (seg S 0 (?m-1)))" "0 < length (P S)"
      using P_nonempty[of "seg S 0 (?m-1)"] P_nonempty[of S] by auto
    ultimately have "length (P (seg S 0 (?m - 1))) = length (P S)" by linarith
    thus ?thesis using True by simp
  next
    case False
    hence cm: "c = ?m" using cleM' by linarith
    have eqp: "butlast (P S) = P (seg S 0 (?m - 1))" using butS_anchor cm by simp
    have d1: "length (P S) - 1 = length (P (seg S 0 (?m - 1)))"
      using eqp by (metis length_butlast)
    have p1: "0 < length (P S)" using P_nonempty[of S] by (cases "P S") auto
    have "length (P S) = length (P (seg S 0 (?m - 1))) + 1" using d1 p1 by linarith
    thus ?thesis using cm by simp
  qed
  have lenStat_Sn:
    "length (P Snside) = length (P (seg Snside 0 (?m - 1))) + (if cN = ?m then 1 else 0)"
  proof (cases "cN < ?m")
    case True
    have eqb: "butlast (P (seg Snside 0 (?m - 1))) = butlast (P Snside)"
      using P_butlast_take_at_anchor[OF SnT multiN True[unfolded cN_def] mleSn'] cN_def by simp
    have "length (P (seg Snside 0 (?m - 1))) - 1 = length (P Snside) - 1"
      using eqb by (metis length_butlast)
    moreover have "0 < length (P (seg Snside 0 (?m-1)))" "0 < length (P Snside)"
      using P_nonempty[of "seg Snside 0 (?m-1)"] P_nonempty[of Snside] by auto
    ultimately have "length (P (seg Snside 0 (?m - 1))) = length (P Snside)" by linarith
    thus ?thesis using True by simp
  next
    case False
    hence cNm: "cN = ?m" using cNlem by linarith
    have eqp: "butlast (P Snside) = P (seg Snside 0 (?m - 1))" using butSn_anchor cNm by simp
    have d1: "length (P Snside) - 1 = length (P (seg Snside 0 (?m - 1)))"
      using eqp by (metis length_butlast)
    have p1: "0 < length (P Snside)" using P_nonempty[of Snside] by (cases "P Snside") auto
    have "length (P Snside) = length (P (seg Snside 0 (?m - 1))) + 1" using d1 p1 by linarith
    thus ?thesis using cNm by simp
  qed
  \<comment> \<open>from \<open>length (P S) = length (P Snside)\<close> and \<open>Lpre_eq\<close>: the boundary statuses match\<close>
  have statEq: "(c = ?m) = (cN = ?m)"
  proof -
    obtain ls lsn lp where ls: "ls = length (P S)" and lsn: "lsn = length (P Snside)"
      and lp: "lp = length (P (seg S 0 (?m - 1)))" by blast
    have lp': "length (P (seg Snside 0 (?m - 1))) = lp" using Lpre_eq lp by simp
    have eS: "ls = lp + (if c = ?m then 1 else 0)" using lenStat_S ls lp by simp
    have eSn: "lsn = lp + (if cN = ?m then 1 else 0)" using lenStat_Sn lsn lp' by simp
    have "ls = lsn" using lenPSeq ls lsn by simp
    hence ifeq: "(if c = ?m then (1::nat) else 0) = (if cN = ?m then 1 else 0)"
      using eS eSn by simp
    show ?thesis
    proof (cases "c = ?m")
      case True
      have "(if cN = ?m then (1::nat) else 0) = 1" using ifeq True by simp
      hence "cN = ?m" by (cases "cN = ?m") simp_all
      thus ?thesis using True by simp
    next
      case Fa: False
      have "(if cN = ?m then (1::nat) else 0) = 0" using ifeq Fa by simp
      hence "cN \<noteq> ?m" by (cases "cN = ?m") simp_all
      thus ?thesis using Fa by simp
    qed
  qed
  \<comment> \<open>uniform \<open>butShift\<close> from the matched status\<close>
  have butShift: "butlast (P S) = map (IncrFirst ^^ shamt) (butlast (P Snside))"
  proof (cases "c = ?m")
    case True
    \<comment> \<open>BOTH anchors at boundary: \<open>butlast (P X) = P (seg X 0 (m-1))\<close> (full prefix)\<close>
    have cNm: "cN = ?m" using True statEq by simp
    have lhs: "butlast (P S) = P (seg S 0 (?m - 1))" using butS_anchor True by simp
    have rhsN: "butlast (P Snside) = P (seg Snside 0 (?m - 1))" using butSn_anchor cNm by simp
    show ?thesis using lhs rhsN PpreEq by simp
  next
    case False
    \<comment> \<open>BOTH anchors strictly below boundary: \<open>butlast (P X) = butlast (P (seg X 0 (m-1)))\<close>\<close>
    have clt: "c < ?m" using False cleM' by linarith
    have cNm: "cN \<noteq> ?m" using False statEq by simp
    have cNlt: "cN < ?m" using cNm cNlem by linarith
    have e1: "butlast (P (seg S 0 (?m - 1))) = butlast (P S)"
      using P_butlast_take_at_anchor[OF ST multi clt[unfolded c_def] mleS'] c_def by simp
    have e2: "butlast (P (seg Snside 0 (?m - 1))) = butlast (P Snside)"
      using P_butlast_take_at_anchor[OF SnT multiN cNlt[unfolded cN_def] mleSn'] cN_def by simp
    show ?thesis using e1[symmetric] butlPpreEq e2 by simp
  qed
  show ceq: "c = cN"
    using cbutl cNbutl butShift by (simp add: o_def Lng_funpow_IncrFirst)
  \<comment> \<open>junction entries at the anchor \<open>c = cN \<le> m\<close>\<close>
  have cle_m: "c \<le> ?m" using ceq cNlem by simp
  show "entry S 0 c = entry Snside 0 cN + shamt"
  proof (cases "c < ?m")
    case strict: True
    \<comment> \<open>anchor in the shifted all-but-last prefix\<close>
    have ce: "c \<le> ?m - 1" using strict by linarith
    have segpre: "seg S 0 (?m - 1) = (IncrFirst ^^ shamt) (seg Snside 0 (?m - 1))"
      using shiftEq by simp
    have cltSeg: "c < Lng (seg Snside 0 (?m - 1))"
      using ce Lng_seg[of Snside 0 "?m-1"] mpos by simp
    have eqsh: "entry (seg S 0 (?m - 1)) 0 c = entry (seg Snside 0 (?m - 1)) 0 c + shamt"
      using segpre entry_funpow_IncrFirst0[OF cltSeg] by simp
    have cltS: "c < Lng (seg S 0 (?m - 1))"
      using ce Lng_seg[of S 0 "?m-1"] mpos mleS' by simp
    have l: "entry (seg S 0 (?m - 1)) 0 c = entry S 0 c" using entry_seg[OF cltS] by simp
    have r: "entry (seg Snside 0 (?m - 1)) 0 c = entry Snside 0 c" using entry_seg[OF cltSeg] by simp
    show ?thesis using eqsh l r ceq by simp
  next
    case False
    hence cm: "c = ?m" using cle_m by linarith
    have "entry S 0 ?m = entry Snside 0 ?m + shamt" using boundEq0 .
    thus ?thesis using cm ceq by simp
  qed
  show "entry S 1 c \<le> entry Snside 1 cN"
  proof (cases "c < ?m")
    case strict: True
    have ce: "c \<le> ?m - 1" using strict by linarith
    have segpre: "seg S 0 (?m - 1) = (IncrFirst ^^ shamt) (seg Snside 0 (?m - 1))"
      using shiftEq by simp
    have cltSeg: "c < Lng (seg Snside 0 (?m - 1))"
      using ce Lng_seg[of Snside 0 "?m-1"] mpos by simp
    have eqsh: "entry (seg S 0 (?m - 1)) 1 c = entry (seg Snside 0 (?m - 1)) 1 c"
      using segpre entry_funpow_IncrFirst1[OF cltSeg] by simp
    have cltS: "c < Lng (seg S 0 (?m - 1))"
      using ce Lng_seg[of S 0 "?m-1"] mpos mleS' by simp
    have l: "entry (seg S 0 (?m - 1)) 1 c = entry S 1 c" using entry_seg[OF cltS] by simp
    have r: "entry (seg Snside 0 (?m - 1)) 1 c = entry Snside 1 c" using entry_seg[OF cltSeg] by simp
    show ?thesis using eqsh l r ceq by simp
  next
    case False
    hence cm: "c = ?m" using cle_m by linarith
    have "entry S 1 ?m \<le> entry Snside 1 ?m" using boundEq1 .
    thus ?thesis using cm ceq by simp
  qed
qed

text \<open>§6.8 d1pos regime-B \<open>mLmin\<close> brick.  The boundary index \<open>m\<close> of a multi branch
  region \<open>X\<close> is a row-0 LEFT-MINIMUM of \<open>X\<close> whenever the last \<open>P\<close>-cut sits exactly
  at \<open>m\<close> (\<open>IdxSum (P X) ! (length (P X) - 1) = m\<close>): the last cut is a row-0 left-min
  by @{thm [source] idxsum_leftend_lmin}, and \<open>= m\<close> identifies it with the boundary.
  In regime B the slice start \<open>A\<close> sits in block 0 with \<open>A < Lng N-1\<close>, so the common
  branch anchor \<open>c = c\<^sub>N = m = Lng (seg N A (Lng N-1)) - 1\<close> (the last branch
  component is the singleton at the boundary); this brick lifts the left-minimality.
  DEEP-VERIFIED (/tmp/mlmin_route.py: \<open>c==m\<close>/\<open>cN==m\<close> 1344/1344, both left-min routes
  1344/1344 over the regime-B slices).\<close>

lemma idxsum_lastcut_lmin_at:
  fixes X :: pairseq
  assumes XT: "X \<in> T_PS" and multi: "1 < length (P X)"
    and meq: "IdxSum (P X) ! (length (P X) - 1) = m"
  shows "\<forall>j < m. entry X 0 m \<le> entry X 0 j"
proof -
  let ?J = "length (P X) - 1"
  have JL: "?J < length (P X)" using multi by simp
  have lmin: "\<forall>j < IdxSum (P X) ! ?J. entry X 0 j \<ge> entry X 0 (IdxSum (P X) ! ?J)"
    using idxsum_leftend_lmin[OF XT JL] by blast
  show ?thesis
  proof (intro allI impI)
    fix j assume jm: "j < m"
    have "j < IdxSum (P X) ! ?J" using jm meq by simp
    hence "entry X 0 j \<ge> entry X 0 (IdxSum (P X) ! ?J)" using lmin by blast
    thus "entry X 0 m \<le> entry X 0 j" using meq by simp
  qed
qed

text \<open>§6.8 d1pos \<open>\<not>brle\<close> UNIFIED \<open>lenPSeqB\<close> DISCHARGER (cap7-a).  The component-count
  match \<open>length (P S) = length (P Snside)\<close> — the one unified-route hypothesis that the
  unified anchor lemma @{thm [source] oper_d1pos_anchor_coincide_period_unified} CONSUMES
  rather than derives.  Derived from the SAME prefix-shift data MINUS \<open>lenPSeq\<close>:
  \<open>shiftEq\<close> (\<open>seg S 0 (m-1) = (IncrFirst^^shamt)(seg Snside 0 (m-1))\<close>),
  \<open>boundEq0\<close> (the row-0 boundary value), and the spans \<open>mleS\<close> (\<open>m \<le> Lng S-1\<close>) / \<open>cleM\<close>
  (\<open>c \<le> m\<close>).  ROUTE (the crux): \<open>length (P X) = Lpre + (if anchor X = m then 1 else 0)\<close>
  for both \<open>X = S, Snside\<close> (the \<open>lenStat\<close> count: a boundary component is present iff the
  anchor sits at \<open>m\<close>), with the common \<open>Lpre = length (P (seg X 0 (m-1)))\<close> equal across
  the shift (@{thm [source] P_funpow_IncrFirst}); the boundary STATUS coincides because
  \<open>anchor X = m \<longleftrightarrow> m\<close> is a row-0 weak left-minimum of \<open>X\<close>
  (@{thm [source] idxsum_lastcut_lmin_at} \<open>\<Rightarrow>\<close>, @{thm [source] anchor_ge_of_leftmin} \<open>\<Leftarrow>\<close>),
  and that left-min status transfers verbatim from \<open>Snside\<close> to \<open>S\<close> through the +\<open>shamt\<close>
  row-0 agreement (\<open>shiftEq\<close> on \<open>[0,m-1]\<close> via @{thm [source] entry_funpow_IncrFirst0},
  \<open>boundEq0\<close> at \<open>m\<close>): adding the constant \<open>shamt\<close> to every row-0 entry preserves the
  \<open>\<le>\<close> comparisons.  DEEP-VERIFIED rank 13 (val 5, KMAX=7, tmp/cap7_lenpseq_check.py:
  2478 regB/boundary/periodic cases, lenPSeqB 0 fails, status-mismatch 0;
  tmp/cap7_probe3.py: \<open>(anchor=m) = lmin0\<close> 0 fails both \<open>S\<close>/\<open>Snside\<close>).\<close>

lemma oper_d1pos_lenPSeq_unified:
  fixes S :: pairseq and Snside :: pairseq and shamt :: nat
  defines "c \<equiv> IdxSum (P S) ! (length (P S) - 1)"
      and "cN \<equiv> IdxSum (P Snside) ! (length (P Snside) - 1)"
  assumes ST: "S \<in> T_PS" and multi: "1 < length (P S)"
    and SnT: "Snside \<in> T_PS" and multiN: "1 < length (P Snside)"
    and mleS: "Lng Snside - 1 \<le> Lng S - 1"
    and cleM: "IdxSum (P S) ! (length (P S) - 1) \<le> Lng Snside - 1"
    and shiftEq: "seg S 0 (Lng Snside - 1 - 1)
                = (IncrFirst ^^ shamt) (seg Snside 0 (Lng Snside - 1 - 1))"
    and boundEq0: "entry S 0 (Lng Snside - 1) = entry Snside 0 (Lng Snside - 1) + shamt"
  shows "length (P S) = length (P Snside)"
proof -
  let ?m = "Lng Snside - 1"
  \<comment> \<open>anchor structural data on both operands (\<open>0 < c, cN\<close>; \<open>c, cN \<le> m\<close>)\<close>
  have c0: "0 < c" unfolding c_def by (rule oper_d1pos_branch_anchor(1)[OF ST multi])
  have cleS: "c \<le> Lng S - 1" unfolding c_def by (rule oper_d1pos_branch_anchor(2)[OF ST multi])
  have cleM': "c \<le> ?m" unfolding c_def using cleM by simp
  have cN0: "0 < cN" unfolding cN_def by (rule oper_d1pos_branch_anchor(1)[OF SnT multiN])
  have cNlem: "cN \<le> ?m" unfolding cN_def by (rule oper_d1pos_branch_anchor(2)[OF SnT multiN])
  have mpos: "0 < ?m" using cN0 cNlem by linarith
  have Snpos: "0 < Lng Snside" using mpos by linarith
  have Spos: "0 < Lng S" using c0 cleS by linarith
  have mleS': "?m \<le> Lng S" using mleS Spos by linarith
  have mleSn': "?m \<le> Lng Snside" by simp
  \<comment> \<open>butlast identities at the respective anchors (regime-agnostic)\<close>
  have butS_anchor: "butlast (P S) = P (seg S 0 (c - 1))"
    using oper_d1pos_branch_butl[OF ST multi] unfolding c_def by simp
  have butSn_anchor: "butlast (P Snside) = P (seg Snside 0 (cN - 1))"
    using oper_d1pos_branch_butl[OF SnT multiN] unfolding cN_def by simp
  \<comment> \<open>the prefix shift at \<open>m-1\<close>, lifted to \<open>P\<close>: equal component COUNTS\<close>
  have PpreEq: "P (seg S 0 (?m - 1)) = map (IncrFirst ^^ shamt) (P (seg Snside 0 (?m - 1)))"
    using shiftEq by (simp add: P_funpow_IncrFirst)
  have Lpre_eq: "length (P (seg S 0 (?m - 1))) = length (P (seg Snside 0 (?m - 1)))"
    using PpreEq by simp
  \<comment> \<open>\<open>lenStat\<close>: a boundary component is present iff the anchor sits at \<open>m\<close>\<close>
  have lenStat_S:
    "length (P S) = length (P (seg S 0 (?m - 1))) + (if c = ?m then 1 else 0)"
  proof (cases "c < ?m")
    case True
    have eqb: "butlast (P (seg S 0 (?m - 1))) = butlast (P S)"
      using P_butlast_take_at_anchor[OF ST multi True[unfolded c_def] mleS'] c_def by simp
    have "length (P (seg S 0 (?m - 1))) - 1 = length (P S) - 1"
      using eqb by (metis length_butlast)
    moreover have "0 < length (P (seg S 0 (?m - 1)))" "0 < length (P S)"
      using P_nonempty[of "seg S 0 (?m-1)"] P_nonempty[of S] by auto
    ultimately have "length (P (seg S 0 (?m - 1))) = length (P S)" by linarith
    thus ?thesis using True by simp
  next
    case False
    hence cm: "c = ?m" using cleM' by linarith
    have eqp: "butlast (P S) = P (seg S 0 (?m - 1))" using butS_anchor cm by simp
    have d1: "length (P S) - 1 = length (P (seg S 0 (?m - 1)))"
      using eqp by (metis length_butlast)
    have p1: "0 < length (P S)" using P_nonempty[of S] by (cases "P S") auto
    have "length (P S) = length (P (seg S 0 (?m - 1))) + 1" using d1 p1 by linarith
    thus ?thesis using cm by simp
  qed
  have lenStat_Sn:
    "length (P Snside) = length (P (seg Snside 0 (?m - 1))) + (if cN = ?m then 1 else 0)"
  proof (cases "cN < ?m")
    case True
    have eqb: "butlast (P (seg Snside 0 (?m - 1))) = butlast (P Snside)"
      using P_butlast_take_at_anchor[OF SnT multiN True[unfolded cN_def] mleSn'] cN_def by simp
    have "length (P (seg Snside 0 (?m - 1))) - 1 = length (P Snside) - 1"
      using eqb by (metis length_butlast)
    moreover have "0 < length (P (seg Snside 0 (?m-1)))" "0 < length (P Snside)"
      using P_nonempty[of "seg Snside 0 (?m-1)"] P_nonempty[of Snside] by auto
    ultimately have "length (P (seg Snside 0 (?m - 1))) = length (P Snside)" by linarith
    thus ?thesis using True by simp
  next
    case False
    hence cNm: "cN = ?m" using cNlem by linarith
    have eqp: "butlast (P Snside) = P (seg Snside 0 (?m - 1))" using butSn_anchor cNm by simp
    have d1: "length (P Snside) - 1 = length (P (seg Snside 0 (?m - 1)))"
      using eqp by (metis length_butlast)
    have p1: "0 < length (P Snside)" using P_nonempty[of Snside] by (cases "P Snside") auto
    have "length (P Snside) = length (P (seg Snside 0 (?m - 1))) + 1" using d1 p1 by linarith
    thus ?thesis using cNm by simp
  qed
  \<comment> \<open>(crux) the boundary status coincides: \<open>(c = m) = (cN = m)\<close>, via the row-0
     left-min characterization (transferred across the +\<open>shamt\<close> shift)\<close>
  have row0_shift: "\<And>j. j < ?m \<Longrightarrow> entry S 0 j = entry Snside 0 j + shamt"
  proof -
    fix j assume jm: "j < ?m"
    have jle: "j \<le> ?m - 1" using jm by linarith
    have jltSn: "j < Lng (seg Snside 0 (?m - 1))"
      using jle Lng_seg[of Snside 0 "?m-1"] mpos by simp
    have jltS: "j < Lng (seg S 0 (?m - 1))"
      using jle Lng_seg[of S 0 "?m-1"] mpos mleS' by simp
    have eS: "entry (seg S 0 (?m - 1)) 0 j = entry S 0 j" using entry_seg[OF jltS] by simp
    have eSn: "entry (seg Snside 0 (?m - 1)) 0 j = entry Snside 0 j" using entry_seg[OF jltSn] by simp
    have "entry (seg S 0 (?m - 1)) 0 j = entry (seg Snside 0 (?m - 1)) 0 j + shamt"
      using shiftEq entry_funpow_IncrFirst0[OF jltSn] by simp
    thus "entry S 0 j = entry Snside 0 j + shamt" using eS eSn by simp
  qed
  have lmin_transfer: "(\<forall>j < ?m. entry S 0 ?m \<le> entry S 0 j)
                     = (\<forall>j < ?m. entry Snside 0 ?m \<le> entry Snside 0 j)"
  proof -
    have "\<And>j. j < ?m \<Longrightarrow> (entry S 0 ?m \<le> entry S 0 j) = (entry Snside 0 ?m \<le> entry Snside 0 j)"
    proof -
      fix j assume jm: "j < ?m"
      have eSj: "entry S 0 j = entry Snside 0 j + shamt" using row0_shift[OF jm] .
      have eSm: "entry S 0 ?m = entry Snside 0 ?m + shamt" using boundEq0 .
      show "(entry S 0 ?m \<le> entry S 0 j) = (entry Snside 0 ?m \<le> entry Snside 0 j)"
        using eSj eSm by simp
    qed
    thus ?thesis by blast
  qed
  have statEq: "(c = ?m) = (cN = ?m)"
  proof
    assume cm: "c = ?m"
    \<comment> \<open>\<open>c = m \<Longrightarrow> m\<close> is a row-0 left-min of \<open>S\<close> (anchor cut), transfers to \<open>Snside\<close>,
       then @{thm [source] anchor_ge_of_leftmin} forces \<open>cN \<ge> m\<close>, with \<open>cN \<le> m\<close>: \<open>cN = m\<close>\<close>
    have lminS: "\<forall>j < ?m. entry S 0 ?m \<le> entry S 0 j"
      using idxsum_lastcut_lmin_at[OF ST multi cm[unfolded c_def]] by blast
    have lminSn: "\<forall>j < ?m. entry Snside 0 ?m \<le> entry Snside 0 j"
      using lminS lmin_transfer by simp
    have mleSnm1: "?m \<le> Lng Snside - 1" by simp
    have "?m \<le> cN" unfolding cN_def
      by (rule anchor_ge_of_leftmin[OF SnT mleSnm1 lminSn])
    thus "cN = ?m" using cNlem by linarith
  next
    assume cNm: "cN = ?m"
    have lminSn: "\<forall>j < ?m. entry Snside 0 ?m \<le> entry Snside 0 j"
      using idxsum_lastcut_lmin_at[OF SnT multiN cNm[unfolded cN_def]] by blast
    have lminS: "\<forall>j < ?m. entry S 0 ?m \<le> entry S 0 j"
      using lminSn lmin_transfer by simp
    have mleSm1: "?m \<le> Lng S - 1" using mleS by simp
    have "?m \<le> c" unfolding c_def
      by (rule anchor_ge_of_leftmin[OF ST mleSm1 lminS])
    thus "c = ?m" using cleM' by linarith
  qed
  show ?thesis using lenStat_S lenStat_Sn Lpre_eq statEq by simp
qed

lemma oper_d1pos_notbrle_LOW_take_eq_regA:
  fixes N :: pairseq and M :: pairseq
  assumes NT: "N \<in> T_PS" and monoN: "monoT N" and LNgt: "1 < Lng N"
    and notzeroN: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hasparN: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1zN: "idx1 N (Lng N - 1) = 1"
    and Neq: "M = N[n]" and n1: "1 \<le> n"
    and M'T: "seg M j0' j1' \<in> T_PS"
    and le0M: "le0 M j0' j1'"
    and lt: "j0' < j1'" and jM: "j1' < Lng M"
    and bge: "Lng N - 1 \<le> j1'"
    and notbrle: "\<not> (TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1
                     \<or> le0 (seg M j0' j1') (TrMax (seg M j0' j1') + 1) (Lng (seg M j0' j1') - 1))"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and dpos: "entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1)"
    and Areg: "j0' + TrMax (seg M j0' j1') + 1 < parent N 1 (Lng N - 1)"
    and multiM: "1 < length (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1'))"
    and multiNp: "1 < length (P (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)))"
    and le0Np: "le0 N j0' (Lng N - 1)"
    and tnc: "TrMax (seg N j0' (Lng N - 1)) \<le> Lng N - 1 - 1 - j0'"
    and stop: "\<not> nextR (seg ((N::pairseq)[n]) j0' j1') 1
                  (TrMax (seg N j0' (Lng N - 1)))
                  (TrMax (seg N j0' (Lng N - 1)) + 1)"
  shows "\<exists>j0red j1red shamt LOW tail.
            j0red < j1red \<and> j1red \<le> Lng N - 1
          \<and> le0 N j0red j1red
          \<and> Br (seg M j0' j1') = LOW @ [tail]
          \<and> Br (seg N j0red j1red) \<noteq> []
          \<and> length LOW = Lng (Br (seg N j0red j1red)) - 1
          \<and> (\<forall>J. J < length LOW
                 \<longrightarrow> entry (LOW ! J) 0 0 = entry (Br (seg N j0red j1red) ! J) 0 0 + shamt
                   \<and> entry (LOW ! J) 1 0 = entry (Br (seg N j0red j1red) ! J) 1 0)
          \<and> entry tail 0 0
              = entry (Br (seg N j0red j1red) ! (Lng (Br (seg N j0red j1red)) - 1)) 0 0
                + shamt
          \<and> entry tail 1 0
              \<le> entry (Br (seg N j0red j1red) ! (Lng (Br (seg N j0red j1red)) - 1)) 1 0"
proof -
  let ?M = "(N::pairseq)[n]"
  let ?M' = "seg M j0' j1'"
  let ?T = "TrMax ?M'"
  let ?A = "j0' + ?T + 1"
  let ?j1red = "Lng N - 1"
  let ?Np = "seg N j0' ?j1red"
  let ?jm2 = "parent N 1 (Lng N - 1)"
  \<comment> \<open>basic geometry: \<open>M = N[n]\<close>, \<open>j'\<^sub>0 < Lng N-1\<close> (regime A), span/cap data\<close>
  have MNn: "M = ?M" using Neq .
  have j1lt: "j1' < Lng ?M" using jM Neq by simp
  have j0lt2: "j0' < ?j1red" using Areg j0lt by linarith
  have j0j1red: "j0' < ?j1red" using j0lt2 .
  have j1redspan: "?j1red \<le> j0' + (j1' - j0')" using bge lt by linarith
  have j1redle: "?j1red \<le> Lng N - 1" by simp
  \<comment> \<open>\<open>M = N[n]\<close>: identify the consumer-side slice with the \<open>N[n]\<close>-slice\<close>
  have Mp_eq: "?M' = seg ?M j0' j1'" using Neq by simp
  \<comment> \<open>(1) TrEq + both \<open>Br = P(seg ..)\<close> reshapes + non-emptiness (regime A)\<close>
  have notbrle': "\<not> (TrMax (seg ?M j0' j1') = Lng (seg ?M j0' j1') - 1
                     \<or> le0 (seg ?M j0' j1') (TrMax (seg ?M j0' j1') + 1) (Lng (seg ?M j0' j1') - 1))"
    using notbrle Mp_eq by simp
  have stop': "\<not> nextR (seg ?M j0' j1') 1
                  (TrMax (seg N j0' (Lng N - 1)))
                  (TrMax (seg N j0' (Lng N - 1)) + 1)"
    using stop .
  have align: "TrMax (seg ?M j0' j1') = TrMax (seg N j0' ?j1red)
       \<and> Br (seg ?M j0' j1') = P (seg ?M (j0' + TrMax (seg ?M j0' j1') + 1) j1')
       \<and> Br (seg N j0' ?j1red) = P (seg N (j0' + TrMax (seg N j0' ?j1red) + 1) ?j1red)
       \<and> Br (seg ?M j0' j1') \<noteq> [] \<and> Br (seg N j0' ?j1red) \<noteq> []"
    by (rule oper_d1pos_notbrle_Br_align_regA[OF LNgt notzeroN hasparN i1zN j0lt n1
            j1redle j0j1red j1redspan refl lt j1lt tnc stop' notbrle'])
  \<comment> \<open>extract the five conjuncts as separate facts (avoid feeding TrEq to simp)\<close>
  have alTrEq: "TrMax (seg ?M j0' j1') = TrMax (seg N j0' ?j1red)" using align by blast
  have alBrM:  "Br (seg ?M j0' j1') = P (seg ?M (j0' + TrMax (seg ?M j0' j1') + 1) j1')"
    using align by blast
  have alBrN:  "Br (seg N j0' ?j1red) = P (seg N (j0' + TrMax (seg N j0' ?j1red) + 1) ?j1red)"
    using align by blast
  have alneM:  "Br (seg ?M j0' j1') \<noteq> []" using align by blast
  have alneN:  "Br (seg N j0' ?j1red) \<noteq> []" using align by blast
  have TrMeq: "?T = TrMax (seg ?M j0' j1')" using Mp_eq by (rule arg_cong)
  have TrEq: "?T = TrMax ?Np" using TrMeq alTrEq by simp
  have BrM'P: "Br ?M' = P (seg ?M ?A j1')"
  proof -
    have aeq: "j0' + TrMax (seg ?M j0' j1') + 1 = ?A" using TrMeq by simp
    have "Br ?M' = Br (seg ?M j0' j1')" using Mp_eq by (rule arg_cong)
    also have "\<dots> = P (seg ?M (j0' + TrMax (seg ?M j0' j1') + 1) j1')" by (rule alBrM)
    also have "\<dots> = P (seg ?M ?A j1')" using aeq by (rule arg_cong[where f = "\<lambda>z. P (seg ?M z j1')"])
    finally show ?thesis .
  qed
  have BrNpP0: "Br ?Np = P (seg N (j0' + TrMax ?Np + 1) ?j1red)" using alBrN .
  have BrM'ne: "Br ?M' \<noteq> []" using alneM Mp_eq by simp
  have BrNpne: "Br ?Np \<noteq> []" using alneN .
  \<comment> \<open>rewrite the \<open>N\<close>-side branch region with TrEq: \<open>Snside = seg N A (Lng N-1)\<close>\<close>
  let ?S = "seg ?M ?A j1'"
  let ?Snside = "seg N ?A ?j1red"
  have BrNpP: "Br ?Np = P ?Snside" using BrNpP0 TrEq by simp
  have BrM'PS: "Br ?M' = P ?S" using BrM'P .
  \<comment> \<open>multiplicity of both branch regions (consumer side-conditions)\<close>
  have multiS: "1 < length (P ?S)"
  proof -
    have "?S = seg M ?A j1'" using Neq by simp
    thus ?thesis using multiM by simp
  qed
  have multiSn: "1 < length (P ?Snside)" using multiNp by simp
  \<comment> \<open>regime-A placement of \<open>A\<close> below \<open>jm2\<close>\<close>
  have AltJm2: "?A < ?jm2" using Areg .
  have Ele: "Lng N - 1 \<le> j1'" using bge .
  have Eub: "j1' < Lng ?M" using j1lt .
  \<comment> \<open>(2) anchor coincidence: \<open>c = cN\<close> / \<open>F8end\<close> / \<open>F9end\<close> at the anchor cuts\<close>
  let ?c = "IdxSum (P ?S) ! (length (P ?S) - 1)"
  let ?cN = "IdxSum (P ?Snside) ! (length (P ?Snside) - 1)"
  have ceq: "?c = ?cN"
    by (rule oper_d1pos_anchor_coincide_regA2(1)[OF LNgt notzeroN hasparN i1zN j0lt
          n1 AltJm2 Ele Eub dpos multiS multiSn])
  have F8end: "entry ?S 0 ?c = entry ?Snside 0 ?cN"
    by (rule oper_d1pos_anchor_coincide_regA2(2)[OF LNgt notzeroN hasparN i1zN j0lt
          n1 AltJm2 Ele Eub dpos multiS multiSn])
  have F9end: "entry ?S 1 ?c \<le> entry ?Snside 1 ?cN"
    by (rule oper_d1pos_anchor_coincide_regA2(3)[OF LNgt notzeroN hasparN i1zN j0lt
          n1 AltJm2 Ele Eub dpos multiS multiSn])
  \<comment> \<open>\<open>S \<in> T_PS\<close>, \<open>Snside \<in> T_PS\<close> (non-empty from multiplicity)\<close>
  have Sne: "?S \<noteq> []"
  proof
    assume "?S = []"
    hence "P ?S = [[]]" by (subst P.simps) (simp add: multiT_def zeroT_def monoT_def)
    thus False using multiS by simp
  qed
  have ST: "?S \<in> T_PS" using Sne by (auto simp: T_PS_def seg_def)
  have Snne: "?Snside \<noteq> []"
  proof
    assume "?Snside = []"
    hence "P ?Snside = [[]]" by (subst P.simps) (simp add: multiT_def zeroT_def monoT_def)
    thus False using multiSn by simp
  qed
  have SnT: "?Snside \<in> T_PS" using Snne by (auto simp: T_PS_def seg_def)
  \<comment> \<open>(3) the \<open>butl\<close> hypothesis: \<open>butlast (P Snside) = P (seg Snside 0 (cN-1))\<close>\<close>
  have butl: "butlast (P ?Snside) = P (seg ?Snside 0 (?cN - 1))"
    by (rule oper_d1pos_branch_butl[OF SnT multiSn])
  \<comment> \<open>(3) the \<open>lowshift\<close> hypothesis (\<open>shamt = 0\<close>): \<open>seg S 0 (c-1) = (IncrFirst^^0)(base)\<close>\<close>
  have clt: "?c < Lng ?Snside - 1"
    by (rule oper_d1pos_clt_regA[OF LNgt notzeroN hasparN i1zN j0lt n1 AltJm2 Ele Eub
          dpos multiS])
  have AltN: "?A < Lng N - 1" using AltJm2 j0lt by linarith
  have Ajm2: "?A \<le> ?jm2" using AltJm2 by linarith
  have cNlt: "?cN < Lng ?Snside - 1"
    by (rule oper_d1pos_cNlt_of_Ajm2[OF LNgt AltN multiSn Ajm2 j0lt dpos])
  \<comment> \<open>geometry of the verbatim window: \<open>A + (c-1) < Lng N-1\<close>, span caps.  Freeze
     \<open>c\<close>/\<open>cN\<close>/\<open>A\<close>/\<open>j1\<close> as abstract vars (avoid the documented double-nat-sub linarith loop)\<close>
  have LngSn: "Lng ?Snside = Suc (Lng N - 1) - ?A" by simp
  have mEq: "Lng ?Snside - 1 = Lng N - 1 - ?A" using LngSn AltN by simp
  obtain cc where ccdef: "cc = ?c" by blast
  obtain ccN where ccNdef: "ccN = ?cN" by blast
  obtain AA where AAdef: "AA = ?A" by blast
  obtain b1 where b1def: "b1 = (j1'::nat)" by blast
  obtain LN1 where LN1def: "LN1 = Lng N - 1" by blast
  have cclt: "cc < LN1 - AA" using clt mEq ccdef AAdef LN1def by simp
  have cNlt': "ccN < LN1 - AA" using cNlt mEq ccNdef AAdef LN1def by simp
  have AltN': "AA < LN1" using AltN AAdef LN1def by simp
  have AleE': "AA \<le> b1" using Ele AltN AAdef b1def LN1def by simp
  have LN1leE: "LN1 \<le> b1" using Ele b1def LN1def by simp
  have Abnd: "?A + (?c - 1) < Lng N - 1"
    using cclt AltN' ccdef AAdef LN1def by linarith
  have AleE: "?A \<le> j1'" using AleE' AAdef b1def by simp
  have ccleE: "?c - 1 \<le> j1' - ?A"
    using cclt AltN' LN1leE ccdef AAdef b1def LN1def by linarith
  have ANleE: "?A \<le> ?j1red" using AltN by linarith
  have cNleEN: "?cN - 1 \<le> ?j1red - ?A"
    using cNlt' AltN' ccNdef AAdef LN1def by linarith
  have lowshift: "seg ?S 0 (?c - 1) = (IncrFirst ^^ (0::nat)) (seg ?Snside 0 (?cN - 1))"
    by (rule oper_d1pos_branch_lowshift_regA[OF LNgt notzeroN hasparN i1zN j0lt n1
          refl ceq Abnd AleE ccleE ANleE cNleEN])
  \<comment> \<open>(3) the concrete collapse with \<open>shamt = 0\<close>, \<open>BN = Br N\<^sub>p\<close>, \<open>base = seg Snside 0 (cN-1)\<close>\<close>
  have lowshift': "seg ?S 0 (IdxSum (P ?S) ! (length (P ?S) - 1) - 1)
                 = (IncrFirst ^^ (0::nat)) (seg ?Snside 0 (?cN - 1))"
    using lowshift by simp
  have butlBN: "butlast (Br ?Np) = P (seg ?Snside 0 (?cN - 1))"
    using butl BrNpP by simp
  have collapse: "P ?S = map (IncrFirst ^^ (0::nat)) (butlast (Br ?Np)) @ [last (P ?S)]"
    by (rule oper_d1pos_branch_collapse_concrete[OF ST multiS lowshift' butlBN])
  \<comment> \<open>\<open>(IncrFirst^^0) = id\<close>, so the LOW prefix is \<open>butlast (Br N\<^sub>p)\<close> VERBATIM\<close>
  have collapse0: "Br ?M' = butlast (Br ?Np) @ [last (P ?S)]"
    using collapse BrM'PS by simp
  \<comment> \<open>identify \<open>LOW = butlast (Br M')\<close>, \<open>tail = last (Br M')\<close>\<close>
  have BrM'split: "Br ?M' = butlast (Br ?M') @ [last (Br ?M')]"
    using BrM'ne by (simp add: append_butlast_last_id)
  have LOWeq: "butlast (Br ?M') = butlast (Br ?Np)"
    using collapse0 BrM'split by simp
  have tailEq: "last (Br ?M') = last (P ?S)"
    using collapse0 BrM'split by simp
  \<comment> \<open>(4) tail junction \<open>F8\<close>/\<open>F9\<close> (\<open>shamt = 0\<close>)\<close>
  have F8end0: "entry ?S 0 ?c = entry ?Snside 0 ?cN + (0::nat)" using F8end by simp
  have F8: "entry (last (P ?S)) 0 0 = entry (last (P ?Snside)) 0 0 + (0::nat)"
    by (rule oper_d1pos_tail_junction(1)[OF ST multiS SnT multiSn F8end0 F9end])
  have F9: "entry (last (P ?S)) 1 0 \<le> entry (last (P ?Snside)) 1 0"
    by (rule oper_d1pos_tail_junction(2)[OF ST multiS SnT multiSn F8end0 F9end])
  \<comment> \<open>\<open>last (P Snside) = Br N\<^sub>p ! (Lng (Br N\<^sub>p) - 1)\<close>\<close>
  have lastNp: "last (P ?Snside) = Br ?Np ! (Lng (Br ?Np) - 1)"
    using BrNpP BrNpne by (simp add: last_conv_nth)
  \<comment> \<open>length of the LOW prefix\<close>
  have lenLOW: "length (butlast (Br ?M')) = Lng (Br ?Np) - 1"
    using LOWeq BrNpne by simp
  \<comment> \<open>per-component verbatim entry facts on the LOW prefix\<close>
  have prefix: "\<forall>J. J < length (butlast (Br ?M'))
                 \<longrightarrow> entry (butlast (Br ?M') ! J) 0 0
                       = entry (Br ?Np ! J) 0 0 + (0::nat)
                   \<and> entry (butlast (Br ?M') ! J) 1 0
                       = entry (Br ?Np ! J) 1 0"
  proof (intro allI impI)
    fix J assume JL: "J < length (butlast (Br ?M'))"
    have JLN: "J < length (butlast (Br ?Np))" using JL LOWeq by simp
    have nthEq: "butlast (Br ?M') ! J = butlast (Br ?Np) ! J" using LOWeq by simp
    have nthBN: "butlast (Br ?Np) ! J = Br ?Np ! J" using JLN by (simp add: nth_butlast)
    have "butlast (Br ?M') ! J = Br ?Np ! J" using nthEq nthBN by simp
    thus "entry (butlast (Br ?M') ! J) 0 0 = entry (Br ?Np ! J) 0 0 + (0::nat)
        \<and> entry (butlast (Br ?M') ! J) 1 0 = entry (Br ?Np ! J) 1 0" by simp
  qed
  \<comment> \<open>tail facts against \<open>Br N\<^sub>p ! (Lng (Br N\<^sub>p) - 1)\<close>\<close>
  have tail0: "entry (last (Br ?M')) 0 0
             = entry (Br ?Np ! (Lng (Br ?Np) - 1)) 0 0 + (0::nat)"
    using tailEq F8 lastNp by simp
  have tail1: "entry (last (Br ?M')) 1 0
             \<le> entry (Br ?Np ! (Lng (Br ?Np) - 1)) 1 0"
    using tailEq F9 lastNp by simp
  \<comment> \<open>\<open>le0 N j'\<^sub>0 (Lng N-1)\<close> is supplied (deep-verified true; from \<open>le0M\<close> at the assembly site)\<close>
  have le0N: "le0 N j0' ?j1red" using le0Np .
  \<comment> \<open>collect the body with the regime-A witnesses, then EXISTS-introduce\<close>
  have body:
    "j0' < ?j1red \<and> ?j1red \<le> Lng N - 1
       \<and> le0 N j0' ?j1red
       \<and> Br ?M' = butlast (Br ?M') @ [last (Br ?M')]
       \<and> Br (seg N j0' ?j1red) \<noteq> []
       \<and> length (butlast (Br ?M')) = Lng (Br (seg N j0' ?j1red)) - 1
       \<and> (\<forall>J. J < length (butlast (Br ?M'))
              \<longrightarrow> entry (butlast (Br ?M') ! J) 0 0
                    = entry (Br (seg N j0' ?j1red) ! J) 0 0 + (0::nat)
                \<and> entry (butlast (Br ?M') ! J) 1 0
                    = entry (Br (seg N j0' ?j1red) ! J) 1 0)
       \<and> entry (last (Br ?M')) 0 0
           = entry (Br (seg N j0' ?j1red) ! (Lng (Br (seg N j0' ?j1red)) - 1)) 0 0 + (0::nat)
       \<and> entry (last (Br ?M')) 1 0
           \<le> entry (Br (seg N j0' ?j1red) ! (Lng (Br (seg N j0' ?j1red)) - 1)) 1 0"
    using j0j1red j1redle le0N BrM'split BrNpne lenLOW prefix tail0 tail1 by blast
  show ?thesis
    by (intro exI[of _ j0'] exI[of _ "Lng N - 1"] exI[of _ "0::nat"]
              exI[of _ "butlast (Br ?M')"] exI[of _ "last (Br ?M')"]) (rule body)
qed

text \<open>§6.8 d1pos \<open>\<not>brle\<close> REGIME B assembly (the GREEN regime-B instance of the main
  identification stub \<open>oper_d1pos_notbrle_LOW_take_eq\<close>, below).  The MIRROR of
  @{thm [source] oper_d1pos_notbrle_LOW_take_eq_regA}: same existential WITNESSES
  (DEEP-VERIFIED: in regime B \<open>j'\<^sub>0 \<ge> j\<^sub>m\<^sub>2\<close> with \<open>j'\<^sub>0\<close> in block 0, so the formula-G
  reduction \<open>q = (j'\<^sub>0-j\<^sub>m\<^sub>2) div w = 0\<close>, \<open>j\<^sub>0\<^sup>red = j\<^sub>m\<^sub>2 + (j'\<^sub>0-j\<^sub>m\<^sub>2) mod w = j'\<^sub>0\<close>,
  \<open>j\<^sub>1\<^sup>red = min (j'\<^sub>0+(j'\<^sub>1-j'\<^sub>0)) (Lng N-1) = Lng N-1\<close> by \<open>bge\<close>, \<open>shamt = q\<cdot>\<delta> = 0\<close> —
  /tmp/regB_assembly_deep.py 1344/1344 rank 10, /tmp/regB_j0red.py \<open>j\<^sub>0\<^sup>red=j'\<^sub>0\<close>
  1344/1344 \<open>j'\<^sub>0\<ge>j\<^sub>m\<^sub>2\<close>).  ONLY the GEOMETRY route differs from regime A: the slice
  start \<open>A = j'\<^sub>0 + TrMax M' + 1\<close> sits AT/ABOVE the period base \<open>j\<^sub>m\<^sub>2\<close> (\<open>Areg : j\<^sub>m\<^sub>2 \<le> A\<close>)
  yet still in block 0 (\<open>A < Lng N-1 = j\<^sub>m\<^sub>2 + w\<close>), so the common branch anchor sits AT
  the boundary \<open>c = c\<^sub>N = m = Lng (seg N A (Lng N-1)) - 1\<close>, pinned by
  @{thm [source] oper_d1pos_anchor_coincide_regB2} (boundary version, given the
  residual block-fold left-mins \<open>mLmin_S\<close>/\<open>mLmin_Sn\<close> and the row-1 period bound
  \<open>r1le\<close>).  WIRING:
  (1) @{thm [source] oper_d1pos_notbrle_Br_align} (regime-B Br-align, \<open>q = 0\<close>,
      \<open>s\<^sub>0 = j'\<^sub>0 - j\<^sub>m\<^sub>2\<close>, \<open>shamt = 0\<close>) gives \<open>TrMax M' = TrMax N\<^sub>p\<close> and both reshapes;
  (2) @{thm [source] oper_d1pos_anchor_coincide_regB2} gives \<open>c = c\<^sub>N\<close> / \<open>F8end\<close> / \<open>F9end\<close>;
  (3) the LOW window \<open>[A, A+c-1]\<close> ends at \<open>Lng N-2 < Lng N-1\<close>, hence is read \<open>N\<close>-verbatim:
      @{thm [source] oper_d1pos_branch_lowshift_regA} (\<open>shamt = 0\<close>, both windows start at
      \<open>A\<close>, \<open>c = c\<^sub>N\<close>) supplies \<open>lowshift\<close>, then @{thm [source] oper_d1pos_branch_collapse_concrete}
      (\<open>butl\<close> via @{thm [source] oper_d1pos_branch_butl}) folds \<open>P S\<close> to
      \<open>butlast (Br N\<^sub>p) @ [last (P S)]\<close>, so \<open>LOW = butlast (Br N\<^sub>p)\<close> VERBATIM;
  (4) @{thm [source] oper_d1pos_tail_junction} lifts \<open>F8end\<close>/\<open>F9end\<close> to the tail node.
  DEEP-VERIFIED rank 10 (KMAX=10, /tmp/regB_assembly_deep.py: 1344/1344 regime-B cases
  \<open>jm2\<le>A<Lng N-1\<close>, all of \<open>c=c\<^sub>N=m\<close>/\<open>shamt=0\<close>/\<open>F8end\<close>/\<open>F9end\<close>/full F1..F9 wiring, with
  \<open>c = IdxSum (P S)!(len-1)\<close>, 0 failures).\<close>

lemma oper_d1pos_notbrle_LOW_take_eq_regB:
  fixes N :: pairseq and M :: pairseq
  assumes NT: "N \<in> T_PS" and monoN: "monoT N" and LNgt: "1 < Lng N"
    and notzeroN: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hasparN: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1zN: "idx1 N (Lng N - 1) = 1"
    and Neq: "M = N[n]" and n1: "1 \<le> n"
    and M'T: "seg M j0' j1' \<in> T_PS"
    and le0M: "le0 M j0' j1'"
    and lt: "j0' < j1'" and jM: "j1' < Lng M"
    and bge: "Lng N - 1 \<le> j1'"
    and notbrle: "\<not> (TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1
                     \<or> le0 (seg M j0' j1') (TrMax (seg M j0' j1') + 1) (Lng (seg M j0' j1') - 1))"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and dpos: "entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1)"
    and Areg: "parent N 1 (Lng N - 1) \<le> j0' + TrMax (seg M j0' j1') + 1
                 \<and> j0' + TrMax (seg M j0' j1') + 1 < Lng N - 1"
    and j0pge: "parent N 1 (Lng N - 1) \<le> j0'"
    and multiM: "1 < length (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1'))"
    and multiNp: "1 < length (P (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)))"
    and le0Np: "le0 N j0' (Lng N - 1)"
    and tnc: "TrMax (seg N j0' (Lng N - 1)) \<le> Lng N - 1 - 1 - j0'"
    and stop: "\<not> nextR (seg ((N::pairseq)[n]) j0' j1') 1
                  (TrMax (seg N j0' (Lng N - 1)))
                  (TrMax (seg N j0' (Lng N - 1)) + 1)"
    \<comment> \<open>UNIFIED anchor inputs (perfix-A, \<open>shamt = 0\<close>): replace the FALSE \<open>mLmin_S\<close>/
       \<open>mLmin_Sn\<close>/\<open>r1le\<close> (which are false on 1026/4584 regB cases,
       python/d1pos_regB_mlmin_verify.py) with the regime-agnostic period-unified
       anchor facts — all deep-verified rank-12 4584/4584 regB + 252/252 boundary
       (python/d1pos_regB_unified_verify.py).\<close>
    and shiftEqB: "seg (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 0
              (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1 - 1)
        = (IncrFirst ^^ (0::nat))
            (seg (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) 0
                 (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1 - 1))"
    and boundEq0B: "entry (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 0
                (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1)
        = entry (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) 0
                (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1) + (0::nat)"
    and boundEq1B: "entry (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 1
                (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1)
        \<le> entry (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) 1
                (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1)"
    and lenPSeqB: "length (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1'))
                 = length (P (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)))"
    and cleMB: "IdxSum (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')) !
            (length (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')) - 1)
          \<le> Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1"
    and mleSB: "Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1
              \<le> Lng (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') - 1"
  shows "\<exists>j0red j1red shamt LOW tail.
            j0red < j1red \<and> j1red \<le> Lng N - 1
          \<and> le0 N j0red j1red
          \<and> Br (seg M j0' j1') = LOW @ [tail]
          \<and> Br (seg N j0red j1red) \<noteq> []
          \<and> length LOW = Lng (Br (seg N j0red j1red)) - 1
          \<and> (\<forall>J. J < length LOW
                 \<longrightarrow> entry (LOW ! J) 0 0 = entry (Br (seg N j0red j1red) ! J) 0 0 + shamt
                   \<and> entry (LOW ! J) 1 0 = entry (Br (seg N j0red j1red) ! J) 1 0)
          \<and> entry tail 0 0
              = entry (Br (seg N j0red j1red) ! (Lng (Br (seg N j0red j1red)) - 1)) 0 0
                + shamt
          \<and> entry tail 1 0
              \<le> entry (Br (seg N j0red j1red) ! (Lng (Br (seg N j0red j1red)) - 1)) 1 0"
proof -
  let ?M = "(N::pairseq)[n]"
  let ?M' = "seg M j0' j1'"
  let ?T = "TrMax ?M'"
  let ?A = "j0' + ?T + 1"
  let ?j1red = "Lng N - 1"
  let ?Np = "seg N j0' ?j1red"
  let ?jm2 = "parent N 1 (Lng N - 1)"
  let ?w = "?j1red - ?jm2"
  let ?delta = "entry N 0 ?j1red - entry N 0 ?jm2"
  \<comment> \<open>regime-B placement: \<open>jm2 \<le> A < Lng N-1\<close>, and \<open>jm2 \<le> j'\<^sub>0\<close> (block 0)\<close>
  have Ajm2: "?jm2 \<le> ?A" using Areg by blast
  have AltN: "?A < ?j1red" using Areg by blast
  \<comment> \<open>basic geometry: \<open>M = N[n]\<close>, span/cap data\<close>
  have MNn: "M = ?M" using Neq .
  have j1lt: "j1' < Lng ?M" using jM Neq by simp
  have j0lt2: "j0' < ?j1red" using AltN lt by linarith
  have j0j1red: "j0' < ?j1red" using j0lt2 .
  have j1redspan: "?j1red \<le> j0' + (j1' - j0')" using bge lt by linarith
  have j1redle: "?j1red \<le> Lng N - 1" by simp
  \<comment> \<open>\<open>j'\<^sub>0 < Lng N-1\<close> (block 0) and the period split \<open>j'\<^sub>0 = jm2 + 0\<cdot>w + s0\<close>\<close>
  have j0plt: "j0' < ?j1red" using j0j1red .
  have w0: "0 < ?w" using j0lt by linarith
  have s0lt: "j0' - ?jm2 < ?w" using j0plt j0pge by linarith
  \<comment> \<open>\<open>M = N[n]\<close>: identify the consumer-side slice with the \<open>N[n]\<close>-slice\<close>
  have Mp_eq: "?M' = seg ?M j0' j1'" using Neq by simp
  \<comment> \<open>(1) TrEq + both \<open>Br = P(seg ..)\<close> reshapes + non-emptiness (regime B, \<open>q = 0\<close>)\<close>
  have notbrle': "\<not> (TrMax (seg ?M j0' j1') = Lng (seg ?M j0' j1') - 1
                     \<or> le0 (seg ?M j0' j1') (TrMax (seg ?M j0' j1') + 1) (Lng (seg ?M j0' j1') - 1))"
    using notbrle Mp_eq by simp
  have stop': "\<not> nextR (seg ?M j0' j1') 1
                  (TrMax (seg N j0' (Lng N - 1)))
                  (TrMax (seg N j0' (Lng N - 1)) + 1)"
    using stop .
  \<comment> \<open>regime-B Br alignment: \<open>q = 0\<close>, \<open>s\<^sub>0 = j'\<^sub>0 - j\<^sub>m\<^sub>2\<close>, so \<open>j\<^sub>0\<^sup>red = j'\<^sub>0\<close>, \<open>shamt = 0\<close>\<close>
  have qz: "(0::nat) < n" using n1 by simp
  have s0eqJ: "j0' = ?jm2 + (j0' - ?jm2)" using j0pge by simp
  have j0'eq: "j0' = ?jm2 + 0 * ?w + (j0' - ?jm2)" using s0eqJ by simp
  have shamt0eq: "(0::nat) = 0 * ?delta" by simp
  have align: "TrMax (seg ?M j0' j1') = TrMax (seg N j0' ?j1red)
       \<and> Br (seg ?M j0' j1') = P (seg ?M (j0' + TrMax (seg ?M j0' j1') + 1) j1')
       \<and> Br (seg N j0' ?j1red) = P (seg N (j0' + TrMax (seg N j0' ?j1red) + 1) ?j1red)
       \<and> Br (seg ?M j0' j1') \<noteq> [] \<and> Br (seg N j0' ?j1red) \<noteq> []"
    by (rule oper_d1pos_notbrle_Br_align[OF NT LNgt notzeroN hasparN i1zN j0lt n1 qz
            j0plt s0eqJ s0lt j0'eq shamt0eq j1redle j0j1red j1redspan lt j1lt tnc stop' notbrle'])
  \<comment> \<open>extract the five conjuncts as separate facts (avoid feeding TrEq to simp)\<close>
  have alTrEq: "TrMax (seg ?M j0' j1') = TrMax (seg N j0' ?j1red)" using align by blast
  have alBrM:  "Br (seg ?M j0' j1') = P (seg ?M (j0' + TrMax (seg ?M j0' j1') + 1) j1')"
    using align by blast
  have alBrN:  "Br (seg N j0' ?j1red) = P (seg N (j0' + TrMax (seg N j0' ?j1red) + 1) ?j1red)"
    using align by blast
  have alneM:  "Br (seg ?M j0' j1') \<noteq> []" using align by blast
  have alneN:  "Br (seg N j0' ?j1red) \<noteq> []" using align by blast
  have TrMeq: "?T = TrMax (seg ?M j0' j1')" using Mp_eq by (rule arg_cong)
  have TrEq: "?T = TrMax ?Np" using TrMeq alTrEq by simp
  have BrM'P: "Br ?M' = P (seg ?M ?A j1')"
  proof -
    have aeq: "j0' + TrMax (seg ?M j0' j1') + 1 = ?A" using TrMeq by simp
    have "Br ?M' = Br (seg ?M j0' j1')" using Mp_eq by (rule arg_cong)
    also have "\<dots> = P (seg ?M (j0' + TrMax (seg ?M j0' j1') + 1) j1')" by (rule alBrM)
    also have "\<dots> = P (seg ?M ?A j1')" using aeq by (rule arg_cong[where f = "\<lambda>z. P (seg ?M z j1')"])
    finally show ?thesis .
  qed
  have BrNpP0: "Br ?Np = P (seg N (j0' + TrMax ?Np + 1) ?j1red)" using alBrN .
  have BrM'ne: "Br ?M' \<noteq> []" using alneM Mp_eq by simp
  have BrNpne: "Br ?Np \<noteq> []" using alneN .
  \<comment> \<open>rewrite the \<open>N\<close>-side branch region with TrEq: \<open>Snside = seg N A (Lng N-1)\<close>\<close>
  let ?S = "seg ?M ?A j1'"
  let ?Snside = "seg N ?A ?j1red"
  have BrNpP: "Br ?Np = P ?Snside" using BrNpP0 TrEq by simp
  have BrM'PS: "Br ?M' = P ?S" using BrM'P .
  \<comment> \<open>multiplicity of both branch regions (consumer side-conditions)\<close>
  have multiS: "1 < length (P ?S)"
  proof -
    have "?S = seg M ?A j1'" using Neq by simp
    thus ?thesis using multiM by simp
  qed
  have multiSn: "1 < length (P ?Snside)" using multiNp by simp
  have Ele: "Lng N - 1 \<le> j1'" using bge .
  have Eub: "j1' < Lng ?M" using j1lt .
  \<comment> \<open>bridge: the carried UNIFIED facts are stated in raw \<open>seg M/N\<close> form; rephrase
     against \<open>?S = seg ?M ?A j1'\<close>/\<open>?Snside = seg N ?A (Lng N-1)\<close> (the \<open>?A\<close> abbrev
     and \<open>?M = N[n]\<close> identification)\<close>
  have SeqM: "seg M ?A j1' = ?S" using Neq by simp
  \<comment> \<open>\<open>S \<in> T_PS\<close>, \<open>Snside \<in> T_PS\<close> (non-empty from multiplicity) — needed by the
     unified anchor call below, so derived FIRST\<close>
  have Sne: "?S \<noteq> []"
  proof
    assume "?S = []"
    hence "P ?S = [[]]" by (subst P.simps) (simp add: multiT_def zeroT_def monoT_def)
    thus False using multiS by simp
  qed
  have ST: "?S \<in> T_PS" using Sne by (auto simp: T_PS_def seg_def)
  have Snne: "?Snside \<noteq> []"
  proof
    assume "?Snside = []"
    hence "P ?Snside = [[]]" by (subst P.simps) (simp add: multiT_def zeroT_def monoT_def)
    thus False using multiSn by simp
  qed
  have SnT: "?Snside \<in> T_PS" using Snne by (auto simp: T_PS_def seg_def)
  \<comment> \<open>(2) anchor coincidence via the period-UNIFIED route (\<open>shamt = 0\<close>) — NO \<open>mLmin\<close>
     (false on regB), NO \<open>r1le\<close>; the regime-agnostic
     @{thm [source] oper_d1pos_anchor_coincide_period_unified}\<close>
  let ?c = "IdxSum (P ?S) ! (length (P ?S) - 1)"
  let ?cN = "IdxSum (P ?Snside) ! (length (P ?Snside) - 1)"
  have shB: "seg ?S 0 (Lng ?Snside - 1 - 1)
           = (IncrFirst ^^ (0::nat)) (seg ?Snside 0 (Lng ?Snside - 1 - 1))"
    using shiftEqB SeqM by simp
  have bnd0: "entry ?S 0 (Lng ?Snside - 1) = entry ?Snside 0 (Lng ?Snside - 1) + (0::nat)"
    using boundEq0B SeqM by simp
  have bnd1: "entry ?S 1 (Lng ?Snside - 1) \<le> entry ?Snside 1 (Lng ?Snside - 1)"
    using boundEq1B SeqM by simp
  have lenPS_loc: "length (P ?S) = length (P ?Snside)" using lenPSeqB SeqM by simp
  have cleM_loc: "?c \<le> Lng ?Snside - 1" using cleMB SeqM by simp
  have mleS_loc: "Lng ?Snside - 1 \<le> Lng ?S - 1" using mleSB SeqM by simp
  have ceq: "?c = ?cN"
    by (rule oper_d1pos_anchor_coincide_period_unified(1)[OF ST multiS SnT multiSn
          mleS_loc cleM_loc lenPS_loc shB bnd0 bnd1])
  have F8end: "entry ?S 0 ?c = entry ?Snside 0 ?cN + (0::nat)"
    by (rule oper_d1pos_anchor_coincide_period_unified(2)[OF ST multiS SnT multiSn
          mleS_loc cleM_loc lenPS_loc shB bnd0 bnd1])
  have F9end: "entry ?S 1 ?c \<le> entry ?Snside 1 ?cN"
    by (rule oper_d1pos_anchor_coincide_period_unified(3)[OF ST multiS SnT multiSn
          mleS_loc cleM_loc lenPS_loc shB bnd0 bnd1])
  \<comment> \<open>(3) the \<open>butl\<close> hypothesis: \<open>butlast (P Snside) = P (seg Snside 0 (cN-1))\<close>\<close>
  have butl: "butlast (P ?Snside) = P (seg ?Snside 0 (?cN - 1))"
    by (rule oper_d1pos_branch_butl[OF SnT multiSn])
  \<comment> \<open>(3) the \<open>lowshift\<close> hypothesis (\<open>shamt = 0\<close>): the LOW window \<open>[A, A+c-1]\<close> ends at
     \<open>Lng N-2 < Lng N-1\<close>, so it is read \<open>N\<close>-verbatim; both windows start at \<open>A\<close>, \<open>c = cN\<close>\<close>
  have cle: "?c \<le> Lng (seg N ?A (Lng N - 1)) - 1"
    by (rule oper_d1pos_clt_regB[OF LNgt notzeroN hasparN i1zN j0lt n1 Ajm2 AltN Ele Eub
          dpos multiS])
  have LngSn: "Lng ?Snside = Suc (Lng N - 1) - ?A" by simp
  have mEq: "Lng ?Snside - 1 = Lng N - 1 - ?A" using LngSn AltN by simp
  have cleM: "?c \<le> Lng N - 1 - ?A" using cle mEq by simp
  \<comment> \<open>freeze \<open>c\<close>/\<open>A\<close>/\<open>j1\<close> as abstract vars (avoid the documented double-nat-sub linarith loop)\<close>
  obtain cc where ccdef: "cc = ?c" by blast
  obtain AA where AAdef: "AA = ?A" by blast
  obtain b1 where b1def: "b1 = (j1'::nat)" by blast
  obtain LN1 where LN1def: "LN1 = Lng N - 1" by blast
  have cclt: "cc \<le> LN1 - AA" using cleM ccdef AAdef LN1def by simp
  have AltN': "AA < LN1" using AltN AAdef LN1def by simp
  have AleE': "AA \<le> b1" using Ele AltN AAdef b1def LN1def by simp
  have LN1leE: "LN1 \<le> b1" using Ele b1def LN1def by simp
  \<comment> \<open>\<open>A + (c-1) < Lng N-1\<close>: \<open>c \<le> Lng N-1 - A\<close> and \<open>0 < A\<close>-window so \<open>A+(c-1) \<le> Lng N-2\<close>\<close>
  have Abnd: "?A + (?c - 1) < Lng N - 1"
    using cclt AltN' ccdef AAdef LN1def by linarith
  have AleE: "?A \<le> j1'" using AleE' AAdef b1def by simp
  have ccleE: "?c - 1 \<le> j1' - ?A"
    using cclt AltN' LN1leE ccdef AAdef b1def LN1def by linarith
  have ANleE: "?A \<le> ?j1red" using AltN by linarith
  have cNleEN: "?cN - 1 \<le> ?j1red - ?A" using ceq ccdef AAdef LN1def cclt by linarith
  have lowshift: "seg ?S 0 (?c - 1) = (IncrFirst ^^ (0::nat)) (seg ?Snside 0 (?cN - 1))"
    by (rule oper_d1pos_branch_lowshift_regA[OF LNgt notzeroN hasparN i1zN j0lt n1
          refl ceq Abnd AleE ccleE ANleE cNleEN])
  \<comment> \<open>(3) the concrete collapse with \<open>shamt = 0\<close>, \<open>BN = Br N\<^sub>p\<close>, \<open>base = seg Snside 0 (cN-1)\<close>\<close>
  have lowshift': "seg ?S 0 (IdxSum (P ?S) ! (length (P ?S) - 1) - 1)
                 = (IncrFirst ^^ (0::nat)) (seg ?Snside 0 (?cN - 1))"
    using lowshift by simp
  have butlBN: "butlast (Br ?Np) = P (seg ?Snside 0 (?cN - 1))"
    using butl BrNpP by simp
  have collapse: "P ?S = map (IncrFirst ^^ (0::nat)) (butlast (Br ?Np)) @ [last (P ?S)]"
    by (rule oper_d1pos_branch_collapse_concrete[OF ST multiS lowshift' butlBN])
  \<comment> \<open>\<open>(IncrFirst^^0) = id\<close>, so the LOW prefix is \<open>butlast (Br N\<^sub>p)\<close> VERBATIM\<close>
  have collapse0: "Br ?M' = butlast (Br ?Np) @ [last (P ?S)]"
    using collapse BrM'PS by simp
  \<comment> \<open>identify \<open>LOW = butlast (Br M')\<close>, \<open>tail = last (Br M')\<close>\<close>
  have BrM'split: "Br ?M' = butlast (Br ?M') @ [last (Br ?M')]"
    using BrM'ne by (simp add: append_butlast_last_id)
  have LOWeq: "butlast (Br ?M') = butlast (Br ?Np)"
    using collapse0 BrM'split by simp
  have tailEq: "last (Br ?M') = last (P ?S)"
    using collapse0 BrM'split by simp
  \<comment> \<open>(4) tail junction \<open>F8\<close>/\<open>F9\<close> (\<open>shamt = 0\<close>)\<close>
  have F8end0: "entry ?S 0 ?c = entry ?Snside 0 ?cN + (0::nat)" using F8end by simp
  have F8: "entry (last (P ?S)) 0 0 = entry (last (P ?Snside)) 0 0 + (0::nat)"
    by (rule oper_d1pos_tail_junction(1)[OF ST multiS SnT multiSn F8end0 F9end])
  have F9: "entry (last (P ?S)) 1 0 \<le> entry (last (P ?Snside)) 1 0"
    by (rule oper_d1pos_tail_junction(2)[OF ST multiS SnT multiSn F8end0 F9end])
  \<comment> \<open>\<open>last (P Snside) = Br N\<^sub>p ! (Lng (Br N\<^sub>p) - 1)\<close>\<close>
  have lastNp: "last (P ?Snside) = Br ?Np ! (Lng (Br ?Np) - 1)"
    using BrNpP BrNpne by (simp add: last_conv_nth)
  \<comment> \<open>length of the LOW prefix\<close>
  have lenLOW: "length (butlast (Br ?M')) = Lng (Br ?Np) - 1"
    using LOWeq BrNpne by simp
  \<comment> \<open>per-component verbatim entry facts on the LOW prefix\<close>
  have prefix: "\<forall>J. J < length (butlast (Br ?M'))
                 \<longrightarrow> entry (butlast (Br ?M') ! J) 0 0
                       = entry (Br ?Np ! J) 0 0 + (0::nat)
                   \<and> entry (butlast (Br ?M') ! J) 1 0
                       = entry (Br ?Np ! J) 1 0"
  proof (intro allI impI)
    fix J assume JL: "J < length (butlast (Br ?M'))"
    have JLN: "J < length (butlast (Br ?Np))" using JL LOWeq by simp
    have nthEq: "butlast (Br ?M') ! J = butlast (Br ?Np) ! J" using LOWeq by simp
    have nthBN: "butlast (Br ?Np) ! J = Br ?Np ! J" using JLN by (simp add: nth_butlast)
    have "butlast (Br ?M') ! J = Br ?Np ! J" using nthEq nthBN by simp
    thus "entry (butlast (Br ?M') ! J) 0 0 = entry (Br ?Np ! J) 0 0 + (0::nat)
        \<and> entry (butlast (Br ?M') ! J) 1 0 = entry (Br ?Np ! J) 1 0" by simp
  qed
  \<comment> \<open>tail facts against \<open>Br N\<^sub>p ! (Lng (Br N\<^sub>p) - 1)\<close>\<close>
  have tail0: "entry (last (Br ?M')) 0 0
             = entry (Br ?Np ! (Lng (Br ?Np) - 1)) 0 0 + (0::nat)"
    using tailEq F8 lastNp by simp
  have tail1: "entry (last (Br ?M')) 1 0
             \<le> entry (Br ?Np ! (Lng (Br ?Np) - 1)) 1 0"
    using tailEq F9 lastNp by simp
  \<comment> \<open>\<open>le0 N j'\<^sub>0 (Lng N-1)\<close> is supplied (deep-verified true; from \<open>le0M\<close> at the assembly site)\<close>
  have le0N: "le0 N j0' ?j1red" using le0Np .
  \<comment> \<open>collect the body with the regime-B witnesses (\<open>j\<^sub>0\<^sup>red = j'\<^sub>0\<close>, \<open>j\<^sub>1\<^sup>red = Lng N-1\<close>,
     \<open>shamt = 0\<close>), then EXISTS-introduce\<close>
  have body:
    "j0' < ?j1red \<and> ?j1red \<le> Lng N - 1
       \<and> le0 N j0' ?j1red
       \<and> Br ?M' = butlast (Br ?M') @ [last (Br ?M')]
       \<and> Br (seg N j0' ?j1red) \<noteq> []
       \<and> length (butlast (Br ?M')) = Lng (Br (seg N j0' ?j1red)) - 1
       \<and> (\<forall>J. J < length (butlast (Br ?M'))
              \<longrightarrow> entry (butlast (Br ?M') ! J) 0 0
                    = entry (Br (seg N j0' ?j1red) ! J) 0 0 + (0::nat)
                \<and> entry (butlast (Br ?M') ! J) 1 0
                    = entry (Br (seg N j0' ?j1red) ! J) 1 0)
       \<and> entry (last (Br ?M')) 0 0
           = entry (Br (seg N j0' ?j1red) ! (Lng (Br (seg N j0' ?j1red)) - 1)) 0 0 + (0::nat)
       \<and> entry (last (Br ?M')) 1 0
           \<le> entry (Br (seg N j0' ?j1red) ! (Lng (Br (seg N j0' ?j1red)) - 1)) 1 0"
    using j0j1red j1redle le0N BrM'split BrNpne lenLOW prefix tail0 tail1 by blast
  show ?thesis
    by (intro exI[of _ j0'] exI[of _ "Lng N - 1"] exI[of _ "0::nat"]
              exI[of _ "butlast (Br ?M')"] exI[of _ "last (Br ?M')"]) (rule body)
qed

text \<open>§6.8 d1pos \<open>\<not>brle\<close> BOUNDARY-CROSS assembly (the GREEN boundary-cross instance
  of the main identification stub \<open>oper_d1pos_notbrle_LOW_take_eq\<close>, below).  The
  MISSING tile between regime A and regime B: the slice START sits in the BASE
  (\<open>j'\<^sub>0 < j\<^sub>m\<^sub>2\<close>, so it is read \<open>N\<close>-verbatim, \<open>j\<^sub>0\<^sup>red = j'\<^sub>0\<close>, \<open>shamt = 0\<close>) yet the
  branch SOURCE \<open>A = j'\<^sub>0 + TrMax M' + 1\<close> crosses the period boundary into block 0's
  tail (\<open>j\<^sub>m\<^sub>2 \<le> A < Lng N-1\<close>), so the common branch anchor sits AT the boundary
  \<open>c = c\<^sub>N = m\<close> just like regime B.  HENCE the WITNESS is regime-A-like
  (\<open>j\<^sub>0\<^sup>red = j'\<^sub>0\<close>, \<open>j\<^sub>1\<^sup>red = Lng N-1\<close>, \<open>shamt = 0\<close>) while the GEOMETRY route is
  regime-B-like (boundary anchor).  DEEP-VERIFIED rank 9 (KMAX=9, python/d1pos_uncovered_deep.py:
  99/99 boundary-cross cases \<open>j'\<^sub>0<j\<^sub>m\<^sub>2 \<and> j\<^sub>m\<^sub>2\<le>A<Lng N-1\<close>, all of \<open>shamt=0\<close>/\<open>j\<^sub>0\<^sup>red=j'\<^sub>0\<close>/full
  F1..F9 wiring, 0 failures; python/d1pos_tiling_map.py 9/9 at rank 7).  WIRING:
  (1) @{thm [source] oper_d1pos_notbrle_Br_align_regA} (\<open>j\<^sub>0\<^sup>red = j'\<^sub>0\<close>, verbatim,
      \<open>shamt = 0\<close>) gives \<open>TrMax M' = TrMax N\<^sub>p\<close> and both reshapes — the ONLY step that
      differs from regime B (where \<open>j'\<^sub>0 \<ge> j\<^sub>m\<^sub>2\<close> needs the period-split Br-align);
  (2)–(4) IDENTICAL to regime B: @{thm [source] oper_d1pos_anchor_coincide_regB2}
      pins \<open>c = c\<^sub>N = m\<close> at the boundary, @{thm [source] oper_d1pos_branch_lowshift_regA}
      reads the LOW window \<open>N\<close>-verbatim, @{thm [source] oper_d1pos_branch_collapse_concrete}
      folds, @{thm [source] oper_d1pos_tail_junction} lifts the tail.\<close>

lemma oper_d1pos_notbrle_LOW_take_eq_boundary:
  fixes N :: pairseq and M :: pairseq
  assumes NT: "N \<in> T_PS" and monoN: "monoT N" and LNgt: "1 < Lng N"
    and notzeroN: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hasparN: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1zN: "idx1 N (Lng N - 1) = 1"
    and Neq: "M = N[n]" and n1: "1 \<le> n"
    and M'T: "seg M j0' j1' \<in> T_PS"
    and le0M: "le0 M j0' j1'"
    and lt: "j0' < j1'" and jM: "j1' < Lng M"
    and bge: "Lng N - 1 \<le> j1'"
    and notbrle: "\<not> (TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1
                     \<or> le0 (seg M j0' j1') (TrMax (seg M j0' j1') + 1) (Lng (seg M j0' j1') - 1))"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and dpos: "entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1)"
    and Areg: "parent N 1 (Lng N - 1) \<le> j0' + TrMax (seg M j0' j1') + 1
                 \<and> j0' + TrMax (seg M j0' j1') + 1 < Lng N - 1"
    and j0ltjm2: "j0' < parent N 1 (Lng N - 1)"
    and multiM: "1 < length (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1'))"
    and multiNp: "1 < length (P (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)))"
    and le0Np: "le0 N j0' (Lng N - 1)"
    and tnc: "TrMax (seg N j0' (Lng N - 1)) \<le> Lng N - 1 - 1 - j0'"
    and stop: "\<not> nextR (seg ((N::pairseq)[n]) j0' j1') 1
                  (TrMax (seg N j0' (Lng N - 1)))
                  (TrMax (seg N j0' (Lng N - 1)) + 1)"
    \<comment> \<open>UNIFIED anchor inputs (perfix-A, \<open>shamt = 0\<close>): replace the FALSE \<open>mLmin_S\<close>/
       \<open>mLmin_Sn\<close>/\<open>r1le\<close> (which are false on 1026/4584 regB cases,
       python/d1pos_regB_mlmin_verify.py) with the regime-agnostic period-unified
       anchor facts — all deep-verified rank-12 4584/4584 regB + 252/252 boundary
       (python/d1pos_regB_unified_verify.py).\<close>
    and shiftEqB: "seg (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 0
              (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1 - 1)
        = (IncrFirst ^^ (0::nat))
            (seg (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) 0
                 (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1 - 1))"
    and boundEq0B: "entry (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 0
                (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1)
        = entry (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) 0
                (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1) + (0::nat)"
    and boundEq1B: "entry (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 1
                (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1)
        \<le> entry (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) 1
                (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1)"
    and lenPSeqB: "length (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1'))
                 = length (P (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)))"
    and cleMB: "IdxSum (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')) !
            (length (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')) - 1)
          \<le> Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1"
    and mleSB: "Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1
              \<le> Lng (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') - 1"
  shows "\<exists>j0red j1red shamt LOW tail.
            j0red < j1red \<and> j1red \<le> Lng N - 1
          \<and> le0 N j0red j1red
          \<and> Br (seg M j0' j1') = LOW @ [tail]
          \<and> Br (seg N j0red j1red) \<noteq> []
          \<and> length LOW = Lng (Br (seg N j0red j1red)) - 1
          \<and> (\<forall>J. J < length LOW
                 \<longrightarrow> entry (LOW ! J) 0 0 = entry (Br (seg N j0red j1red) ! J) 0 0 + shamt
                   \<and> entry (LOW ! J) 1 0 = entry (Br (seg N j0red j1red) ! J) 1 0)
          \<and> entry tail 0 0
              = entry (Br (seg N j0red j1red) ! (Lng (Br (seg N j0red j1red)) - 1)) 0 0
                + shamt
          \<and> entry tail 1 0
              \<le> entry (Br (seg N j0red j1red) ! (Lng (Br (seg N j0red j1red)) - 1)) 1 0"
proof -
  let ?M = "(N::pairseq)[n]"
  let ?M' = "seg M j0' j1'"
  let ?T = "TrMax ?M'"
  let ?A = "j0' + ?T + 1"
  let ?j1red = "Lng N - 1"
  let ?Np = "seg N j0' ?j1red"
  let ?jm2 = "parent N 1 (Lng N - 1)"
  let ?w = "?j1red - ?jm2"
  let ?delta = "entry N 0 ?j1red - entry N 0 ?jm2"
  \<comment> \<open>boundary-cross placement: \<open>jm2 \<le> A < Lng N-1\<close>, but \<open>j'\<^sub>0 < jm2\<close> (slice starts in base)\<close>
  have Ajm2: "?jm2 \<le> ?A" using Areg by blast
  have AltN: "?A < ?j1red" using Areg by blast
  \<comment> \<open>basic geometry: \<open>M = N[n]\<close>, span/cap data\<close>
  have MNn: "M = ?M" using Neq .
  have j1lt: "j1' < Lng ?M" using jM Neq by simp
  have j0lt2: "j0' < ?j1red" using AltN lt by linarith
  have j0j1red: "j0' < ?j1red" using j0lt2 .
  have j1redspan: "?j1red \<le> j0' + (j1' - j0')" using bge lt by linarith
  have j1redle: "?j1red \<le> Lng N - 1" by simp
  \<comment> \<open>\<open>M = N[n]\<close>: identify the consumer-side slice with the \<open>N[n]\<close>-slice\<close>
  have Mp_eq: "?M' = seg ?M j0' j1'" using Neq by simp
  \<comment> \<open>(1) TrEq + both \<open>Br = P(seg ..)\<close> reshapes + non-emptiness (boundary, \<open>j\<^sub>0\<^sup>red = j'\<^sub>0\<close>)\<close>
  have notbrle': "\<not> (TrMax (seg ?M j0' j1') = Lng (seg ?M j0' j1') - 1
                     \<or> le0 (seg ?M j0' j1') (TrMax (seg ?M j0' j1') + 1) (Lng (seg ?M j0' j1') - 1))"
    using notbrle Mp_eq by simp
  have stop': "\<not> nextR (seg ?M j0' j1') 1
                  (TrMax (seg N j0' (Lng N - 1)))
                  (TrMax (seg N j0' (Lng N - 1)) + 1)"
    using stop .
  \<comment> \<open>regime-A (verbatim) Br alignment: \<open>j\<^sub>0\<^sup>red = j'\<^sub>0\<close>, \<open>shamt = 0\<close> — the slice start
     \<open>j'\<^sub>0 < jm2\<close> is read \<open>N\<close>-verbatim, exactly as in regime A\<close>
  have align: "TrMax (seg ?M j0' j1') = TrMax (seg N j0' ?j1red)
       \<and> Br (seg ?M j0' j1') = P (seg ?M (j0' + TrMax (seg ?M j0' j1') + 1) j1')
       \<and> Br (seg N j0' ?j1red) = P (seg N (j0' + TrMax (seg N j0' ?j1red) + 1) ?j1red)
       \<and> Br (seg ?M j0' j1') \<noteq> [] \<and> Br (seg N j0' ?j1red) \<noteq> []"
    by (rule oper_d1pos_notbrle_Br_align_regA[OF LNgt notzeroN hasparN i1zN j0lt n1
            j1redle j0j1red j1redspan refl lt j1lt tnc stop' notbrle'])
  \<comment> \<open>extract the five conjuncts as separate facts (avoid feeding TrEq to simp)\<close>
  have alTrEq: "TrMax (seg ?M j0' j1') = TrMax (seg N j0' ?j1red)" using align by blast
  have alBrM:  "Br (seg ?M j0' j1') = P (seg ?M (j0' + TrMax (seg ?M j0' j1') + 1) j1')"
    using align by blast
  have alBrN:  "Br (seg N j0' ?j1red) = P (seg N (j0' + TrMax (seg N j0' ?j1red) + 1) ?j1red)"
    using align by blast
  have alneM:  "Br (seg ?M j0' j1') \<noteq> []" using align by blast
  have alneN:  "Br (seg N j0' ?j1red) \<noteq> []" using align by blast
  have TrMeq: "?T = TrMax (seg ?M j0' j1')" using Mp_eq by (rule arg_cong)
  have TrEq: "?T = TrMax ?Np" using TrMeq alTrEq by simp
  have BrM'P: "Br ?M' = P (seg ?M ?A j1')"
  proof -
    have aeq: "j0' + TrMax (seg ?M j0' j1') + 1 = ?A" using TrMeq by simp
    have "Br ?M' = Br (seg ?M j0' j1')" using Mp_eq by (rule arg_cong)
    also have "\<dots> = P (seg ?M (j0' + TrMax (seg ?M j0' j1') + 1) j1')" by (rule alBrM)
    also have "\<dots> = P (seg ?M ?A j1')" using aeq by (rule arg_cong[where f = "\<lambda>z. P (seg ?M z j1')"])
    finally show ?thesis .
  qed
  have BrNpP0: "Br ?Np = P (seg N (j0' + TrMax ?Np + 1) ?j1red)" using alBrN .
  have BrM'ne: "Br ?M' \<noteq> []" using alneM Mp_eq by simp
  have BrNpne: "Br ?Np \<noteq> []" using alneN .
  \<comment> \<open>rewrite the \<open>N\<close>-side branch region with TrEq: \<open>Snside = seg N A (Lng N-1)\<close>\<close>
  let ?S = "seg ?M ?A j1'"
  let ?Snside = "seg N ?A ?j1red"
  have BrNpP: "Br ?Np = P ?Snside" using BrNpP0 TrEq by simp
  have BrM'PS: "Br ?M' = P ?S" using BrM'P .
  \<comment> \<open>multiplicity of both branch regions (consumer side-conditions)\<close>
  have multiS: "1 < length (P ?S)"
  proof -
    have "?S = seg M ?A j1'" using Neq by simp
    thus ?thesis using multiM by simp
  qed
  have multiSn: "1 < length (P ?Snside)" using multiNp by simp
  have Ele: "Lng N - 1 \<le> j1'" using bge .
  have Eub: "j1' < Lng ?M" using j1lt .
  \<comment> \<open>bridge: the carried UNIFIED facts are stated in raw \<open>seg M/N\<close> form; rephrase
     against \<open>?S = seg ?M ?A j1'\<close>/\<open>?Snside = seg N ?A (Lng N-1)\<close> (the \<open>?A\<close> abbrev
     and \<open>?M = N[n]\<close> identification)\<close>
  have SeqM: "seg M ?A j1' = ?S" using Neq by simp
  \<comment> \<open>\<open>S \<in> T_PS\<close>, \<open>Snside \<in> T_PS\<close> (non-empty from multiplicity) — needed by the
     unified anchor call below, so derived FIRST\<close>
  have Sne: "?S \<noteq> []"
  proof
    assume "?S = []"
    hence "P ?S = [[]]" by (subst P.simps) (simp add: multiT_def zeroT_def monoT_def)
    thus False using multiS by simp
  qed
  have ST: "?S \<in> T_PS" using Sne by (auto simp: T_PS_def seg_def)
  have Snne: "?Snside \<noteq> []"
  proof
    assume "?Snside = []"
    hence "P ?Snside = [[]]" by (subst P.simps) (simp add: multiT_def zeroT_def monoT_def)
    thus False using multiSn by simp
  qed
  have SnT: "?Snside \<in> T_PS" using Snne by (auto simp: T_PS_def seg_def)
  \<comment> \<open>(2) anchor coincidence via the period-UNIFIED route (\<open>shamt = 0\<close>) — NO \<open>mLmin\<close>
     (false on regB), NO \<open>r1le\<close>; the regime-agnostic
     @{thm [source] oper_d1pos_anchor_coincide_period_unified}\<close>
  let ?c = "IdxSum (P ?S) ! (length (P ?S) - 1)"
  let ?cN = "IdxSum (P ?Snside) ! (length (P ?Snside) - 1)"
  have shB: "seg ?S 0 (Lng ?Snside - 1 - 1)
           = (IncrFirst ^^ (0::nat)) (seg ?Snside 0 (Lng ?Snside - 1 - 1))"
    using shiftEqB SeqM by simp
  have bnd0: "entry ?S 0 (Lng ?Snside - 1) = entry ?Snside 0 (Lng ?Snside - 1) + (0::nat)"
    using boundEq0B SeqM by simp
  have bnd1: "entry ?S 1 (Lng ?Snside - 1) \<le> entry ?Snside 1 (Lng ?Snside - 1)"
    using boundEq1B SeqM by simp
  have lenPS_loc: "length (P ?S) = length (P ?Snside)" using lenPSeqB SeqM by simp
  have cleM_loc: "?c \<le> Lng ?Snside - 1" using cleMB SeqM by simp
  have mleS_loc: "Lng ?Snside - 1 \<le> Lng ?S - 1" using mleSB SeqM by simp
  have ceq: "?c = ?cN"
    by (rule oper_d1pos_anchor_coincide_period_unified(1)[OF ST multiS SnT multiSn
          mleS_loc cleM_loc lenPS_loc shB bnd0 bnd1])
  have F8end: "entry ?S 0 ?c = entry ?Snside 0 ?cN + (0::nat)"
    by (rule oper_d1pos_anchor_coincide_period_unified(2)[OF ST multiS SnT multiSn
          mleS_loc cleM_loc lenPS_loc shB bnd0 bnd1])
  have F9end: "entry ?S 1 ?c \<le> entry ?Snside 1 ?cN"
    by (rule oper_d1pos_anchor_coincide_period_unified(3)[OF ST multiS SnT multiSn
          mleS_loc cleM_loc lenPS_loc shB bnd0 bnd1])
  \<comment> \<open>(3) the \<open>butl\<close> hypothesis: \<open>butlast (P Snside) = P (seg Snside 0 (cN-1))\<close>\<close>
  have butl: "butlast (P ?Snside) = P (seg ?Snside 0 (?cN - 1))"
    by (rule oper_d1pos_branch_butl[OF SnT multiSn])
  \<comment> \<open>(3) the \<open>lowshift\<close> hypothesis (\<open>shamt = 0\<close>): the LOW window \<open>[A, A+c-1]\<close> ends at
     \<open>Lng N-2 < Lng N-1\<close>, so it is read \<open>N\<close>-verbatim; both windows start at \<open>A\<close>, \<open>c = cN\<close>\<close>
  have cle: "?c \<le> Lng (seg N ?A (Lng N - 1)) - 1"
    by (rule oper_d1pos_clt_regB[OF LNgt notzeroN hasparN i1zN j0lt n1 Ajm2 AltN Ele Eub
          dpos multiS])
  have LngSn: "Lng ?Snside = Suc (Lng N - 1) - ?A" by simp
  have mEq: "Lng ?Snside - 1 = Lng N - 1 - ?A" using LngSn AltN by simp
  have cleM: "?c \<le> Lng N - 1 - ?A" using cle mEq by simp
  \<comment> \<open>freeze \<open>c\<close>/\<open>A\<close>/\<open>j1\<close> as abstract vars (avoid the documented double-nat-sub linarith loop)\<close>
  obtain cc where ccdef: "cc = ?c" by blast
  obtain AA where AAdef: "AA = ?A" by blast
  obtain b1 where b1def: "b1 = (j1'::nat)" by blast
  obtain LN1 where LN1def: "LN1 = Lng N - 1" by blast
  have cclt: "cc \<le> LN1 - AA" using cleM ccdef AAdef LN1def by simp
  have AltN': "AA < LN1" using AltN AAdef LN1def by simp
  have AleE': "AA \<le> b1" using Ele AltN AAdef b1def LN1def by simp
  have LN1leE: "LN1 \<le> b1" using Ele b1def LN1def by simp
  \<comment> \<open>\<open>A + (c-1) < Lng N-1\<close>: \<open>c \<le> Lng N-1 - A\<close> and \<open>0 < A\<close>-window so \<open>A+(c-1) \<le> Lng N-2\<close>\<close>
  have Abnd: "?A + (?c - 1) < Lng N - 1"
    using cclt AltN' ccdef AAdef LN1def by linarith
  have AleE: "?A \<le> j1'" using AleE' AAdef b1def by simp
  have ccleE: "?c - 1 \<le> j1' - ?A"
    using cclt AltN' LN1leE ccdef AAdef b1def LN1def by linarith
  have ANleE: "?A \<le> ?j1red" using AltN by linarith
  have cNleEN: "?cN - 1 \<le> ?j1red - ?A" using ceq ccdef AAdef LN1def cclt by linarith
  have lowshift: "seg ?S 0 (?c - 1) = (IncrFirst ^^ (0::nat)) (seg ?Snside 0 (?cN - 1))"
    by (rule oper_d1pos_branch_lowshift_regA[OF LNgt notzeroN hasparN i1zN j0lt n1
          refl ceq Abnd AleE ccleE ANleE cNleEN])
  \<comment> \<open>(3) the concrete collapse with \<open>shamt = 0\<close>, \<open>BN = Br N\<^sub>p\<close>, \<open>base = seg Snside 0 (cN-1)\<close>\<close>
  have lowshift': "seg ?S 0 (IdxSum (P ?S) ! (length (P ?S) - 1) - 1)
                 = (IncrFirst ^^ (0::nat)) (seg ?Snside 0 (?cN - 1))"
    using lowshift by simp
  have butlBN: "butlast (Br ?Np) = P (seg ?Snside 0 (?cN - 1))"
    using butl BrNpP by simp
  have collapse: "P ?S = map (IncrFirst ^^ (0::nat)) (butlast (Br ?Np)) @ [last (P ?S)]"
    by (rule oper_d1pos_branch_collapse_concrete[OF ST multiS lowshift' butlBN])
  \<comment> \<open>\<open>(IncrFirst^^0) = id\<close>, so the LOW prefix is \<open>butlast (Br N\<^sub>p)\<close> VERBATIM\<close>
  have collapse0: "Br ?M' = butlast (Br ?Np) @ [last (P ?S)]"
    using collapse BrM'PS by simp
  \<comment> \<open>identify \<open>LOW = butlast (Br M')\<close>, \<open>tail = last (Br M')\<close>\<close>
  have BrM'split: "Br ?M' = butlast (Br ?M') @ [last (Br ?M')]"
    using BrM'ne by (simp add: append_butlast_last_id)
  have LOWeq: "butlast (Br ?M') = butlast (Br ?Np)"
    using collapse0 BrM'split by simp
  have tailEq: "last (Br ?M') = last (P ?S)"
    using collapse0 BrM'split by simp
  \<comment> \<open>(4) tail junction \<open>F8\<close>/\<open>F9\<close> (\<open>shamt = 0\<close>)\<close>
  have F8end0: "entry ?S 0 ?c = entry ?Snside 0 ?cN + (0::nat)" using F8end by simp
  have F8: "entry (last (P ?S)) 0 0 = entry (last (P ?Snside)) 0 0 + (0::nat)"
    by (rule oper_d1pos_tail_junction(1)[OF ST multiS SnT multiSn F8end0 F9end])
  have F9: "entry (last (P ?S)) 1 0 \<le> entry (last (P ?Snside)) 1 0"
    by (rule oper_d1pos_tail_junction(2)[OF ST multiS SnT multiSn F8end0 F9end])
  \<comment> \<open>\<open>last (P Snside) = Br N\<^sub>p ! (Lng (Br N\<^sub>p) - 1)\<close>\<close>
  have lastNp: "last (P ?Snside) = Br ?Np ! (Lng (Br ?Np) - 1)"
    using BrNpP BrNpne by (simp add: last_conv_nth)
  \<comment> \<open>length of the LOW prefix\<close>
  have lenLOW: "length (butlast (Br ?M')) = Lng (Br ?Np) - 1"
    using LOWeq BrNpne by simp
  \<comment> \<open>per-component verbatim entry facts on the LOW prefix\<close>
  have prefix: "\<forall>J. J < length (butlast (Br ?M'))
                 \<longrightarrow> entry (butlast (Br ?M') ! J) 0 0
                       = entry (Br ?Np ! J) 0 0 + (0::nat)
                   \<and> entry (butlast (Br ?M') ! J) 1 0
                       = entry (Br ?Np ! J) 1 0"
  proof (intro allI impI)
    fix J assume JL: "J < length (butlast (Br ?M'))"
    have JLN: "J < length (butlast (Br ?Np))" using JL LOWeq by simp
    have nthEq: "butlast (Br ?M') ! J = butlast (Br ?Np) ! J" using LOWeq by simp
    have nthBN: "butlast (Br ?Np) ! J = Br ?Np ! J" using JLN by (simp add: nth_butlast)
    have "butlast (Br ?M') ! J = Br ?Np ! J" using nthEq nthBN by simp
    thus "entry (butlast (Br ?M') ! J) 0 0 = entry (Br ?Np ! J) 0 0 + (0::nat)
        \<and> entry (butlast (Br ?M') ! J) 1 0 = entry (Br ?Np ! J) 1 0" by simp
  qed
  \<comment> \<open>tail facts against \<open>Br N\<^sub>p ! (Lng (Br N\<^sub>p) - 1)\<close>\<close>
  have tail0: "entry (last (Br ?M')) 0 0
             = entry (Br ?Np ! (Lng (Br ?Np) - 1)) 0 0 + (0::nat)"
    using tailEq F8 lastNp by simp
  have tail1: "entry (last (Br ?M')) 1 0
             \<le> entry (Br ?Np ! (Lng (Br ?Np) - 1)) 1 0"
    using tailEq F9 lastNp by simp
  \<comment> \<open>\<open>le0 N j'\<^sub>0 (Lng N-1)\<close> is supplied (deep-verified true; from \<open>le0M\<close> at the assembly site)\<close>
  have le0N: "le0 N j0' ?j1red" using le0Np .
  \<comment> \<open>collect the body with the regime-B witnesses (\<open>j\<^sub>0\<^sup>red = j'\<^sub>0\<close>, \<open>j\<^sub>1\<^sup>red = Lng N-1\<close>,
     \<open>shamt = 0\<close>), then EXISTS-introduce\<close>
  have body:
    "j0' < ?j1red \<and> ?j1red \<le> Lng N - 1
       \<and> le0 N j0' ?j1red
       \<and> Br ?M' = butlast (Br ?M') @ [last (Br ?M')]
       \<and> Br (seg N j0' ?j1red) \<noteq> []
       \<and> length (butlast (Br ?M')) = Lng (Br (seg N j0' ?j1red)) - 1
       \<and> (\<forall>J. J < length (butlast (Br ?M'))
              \<longrightarrow> entry (butlast (Br ?M') ! J) 0 0
                    = entry (Br (seg N j0' ?j1red) ! J) 0 0 + (0::nat)
                \<and> entry (butlast (Br ?M') ! J) 1 0
                    = entry (Br (seg N j0' ?j1red) ! J) 1 0)
       \<and> entry (last (Br ?M')) 0 0
           = entry (Br (seg N j0' ?j1red) ! (Lng (Br (seg N j0' ?j1red)) - 1)) 0 0 + (0::nat)
       \<and> entry (last (Br ?M')) 1 0
           \<le> entry (Br (seg N j0' ?j1red) ! (Lng (Br (seg N j0' ?j1red)) - 1)) 1 0"
    using j0j1red j1redle le0N BrM'split BrNpne lenLOW prefix tail0 tail1 by blast
  show ?thesis
    by (intro exI[of _ j0'] exI[of _ "Lng N - 1"] exI[of _ "0::nat"]
              exI[of _ "butlast (Br ?M')"] exI[of _ "last (Br ?M')"]) (rule body)
qed


text \<open>§6.8 helper — \<open>IncrFirst\<close> commutes with \<open>seg\<close>: a slice of the row-0-shifted
  sequence is the shift of the slice (\<open>IncrFirst = map\<close>, which commutes with the
  take/drop that build \<open>seg\<close>).  The \<open>funpow\<close> version follows by induction.  Used in
  the CELL-4 periodic assembly to push the full per-block shift through the LOW
  prefix window.\<close>

lemma seg_IncrFirst0:
  assumes "b < Lng M"
  shows "seg (IncrFirst M) a b = IncrFirst (seg M a b)"
proof (rule nth_equalityI)
  show "length (seg (IncrFirst M) a b) = length (IncrFirst (seg M a b))"
    by (simp add: IncrFirst_def)
next
  fix i assume "i < length (seg (IncrFirst M) a b)"
  hence ic: "i < Suc b - a" by (simp add: IncrFirst_def)
  have segL: "seg (IncrFirst M) a b ! i = (IncrFirst M) ! (a + i)"
    using ic by (rule seg_nth_eq)
  have segR: "seg M a b ! i = M ! (a + i)" using ic by (rule seg_nth_eq)
  have ailt: "a + i < Lng M" using ic assms by linarith
  have "(IncrFirst M) ! (a + i) = (Suc (fst (M ! (a + i))), snd (M ! (a + i)))"
    using ailt by (simp add: IncrFirst_def)
  moreover have "IncrFirst (seg M a b) ! i
               = (Suc (fst (seg M a b ! i)), snd (seg M a b ! i))"
  proof -
    have "i < length (seg M a b)" using ic by simp
    thus ?thesis by (simp add: IncrFirst_def)
  qed
  ultimately show "seg (IncrFirst M) a b ! i = IncrFirst (seg M a b) ! i"
    using segL segR by simp
qed

lemma seg_funpow_IncrFirst0:
  assumes "b < Lng M"
  shows "seg ((IncrFirst ^^ k) M) a b = (IncrFirst ^^ k) (seg M a b)"
  using assms
proof (induction k)
  case 0 thus ?case by simp
next
  case (Suc k)
  have bk: "b < Lng ((IncrFirst ^^ k) M)" using Suc.prems by simp
  have "seg ((IncrFirst ^^ Suc k) M) a b = seg (IncrFirst ((IncrFirst ^^ k) M)) a b"
    by simp
  also have "\<dots> = IncrFirst (seg ((IncrFirst ^^ k) M) a b)" by (rule seg_IncrFirst0[OF bk])
  also have "\<dots> = IncrFirst ((IncrFirst ^^ k) (seg M a b))" using Suc by simp
  also have "\<dots> = (IncrFirst ^^ Suc k) (seg M a b)" by simp
  finally show ?case .
qed

end
