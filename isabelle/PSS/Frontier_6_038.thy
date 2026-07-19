theory Frontier_6_038
  imports Support_6_020
begin

text \<open>§6.8 d1pos ¬brle — the ANCHOR TAIL entry reduction.  The last \<open>P\<close>-component
  of a multi-\<open>P\<close> \<open>S \<in> T_PS\<close> is, by @{thm [source] oper_d1pos_branch_anchor}(5),
  the single segment \<open>seg S c (Lng S - 1)\<close> with \<open>c = IdxSum (P S) ! (length (P S) - 1)\<close>,
  whose head row-\<open>i\<close> value (\<open>entry (last (P S)) i 0\<close>) is just the \<open>S\<close>-entry at the
  anchor cut \<open>c\<close> (the left endpoint, @{thm [source] entry_seg} at offset \<open>0\<close>; the
  cut satisfies \<open>c \<le> Lng S - 1\<close> so the segment is non-empty).  PURELY STRUCTURAL —
  no block-fold.\<close>

lemma oper_d1pos_anchor_tail_entry:
  fixes S :: pairseq
  defines "c \<equiv> IdxSum (P S) ! (length (P S) - 1)"
  assumes ST: "S \<in> T_PS" and multi: "1 < length (P S)"
  shows "entry (last (P S)) i 0 = entry S i c"
proof -
  have cle: "c \<le> Lng S - 1" unfolding c_def
    by (rule oper_d1pos_branch_anchor(2)[OF ST multi])
  have tailseg: "seg S c (Lng S - 1) = last (P S)" unfolding c_def
    by (rule oper_d1pos_branch_anchor(5)[OF ST multi])
  \<comment> \<open>the tail segment is non-empty: \<open>0 < Suc (Lng S - 1) - c\<close> since \<open>c \<le> Lng S - 1\<close>\<close>
  have ne: "(0::nat) < Lng (seg S c (Lng S - 1))" using cle by simp
  have "entry (seg S c (Lng S - 1)) i 0 = entry S i (c + 0)"
    by (rule entry_seg[OF ne])
  hence "entry (seg S c (Lng S - 1)) i 0 = entry S i c" by simp
  thus ?thesis using tailseg by simp
qed

text \<open>§6.8 d1pos ¬brle — the TAIL JUNCTION (F8/F9).  Given the two N-/M-side multi-\<open>P\<close>
  branch regions \<open>S\<close> (= \<open>Br M'\<close>) and \<open>Snside\<close> (= \<open>Br N\<^sub>p\<close>), each with its anchor cut
  \<open>c\<close>/\<open>cN\<close>, the article's row-0 \<open>+shamt\<close> tie and row-1 drop at the anchor LEFT
  ENDPOINTS (the deep block-fold geometry, supplied as \<open>F8end\<close>/\<open>F9end\<close>):
    \<open>F8end : entry S 0 c    = entry Snside 0 cN + shamt\<close>   (row-0 +shamt tie)
    \<open>F9end : entry S 1 c    \<le> entry Snside 1 cN\<close>           (row-1 drop)
  lift, via the anchor-tail entry reduction @{thm [source] oper_d1pos_anchor_tail_entry},
  to the TAIL-NODE junction the §6.8 assembly stub consumes:
    \<open>F8 : entry (last (P S)) 0 0    = entry (last (P Snside)) 0 0 + shamt\<close>
    \<open>F9 : entry (last (P S)) 1 0    \<le> entry (last (P Snside)) 1 0\<close>.
  Here \<open>last (P S) = Br M' ! (Lng (Br M') - 1)\<close> and \<open>last (P Snside) = Br N\<^sub>p !
  (Lng (Br N\<^sub>p) - 1)\<close> are the tail nodes \<open>tail\<close> and \<open>Br N\<^sub>p ! (Lng (Br N\<^sub>p) - 1)\<close> of the
  consumer obligation.  DEEP-VERIFIED rank 8 (python/d1pos_tail_junction.py): both the
  endpoint identities \<open>F8end\<close>/\<open>F9end\<close> and the lifted tail facts \<open>F8\<close>/\<open>F9\<close> hold
  1395/1395 (len\<le>12 val\<le>4) and 3276/3276 (len\<le>11 val\<le>5), 0 failures.  PURELY
  STRUCTURAL given the endpoint identities — no block-fold inside this lemma.\<close>

lemma oper_d1pos_tail_junction:
  fixes S :: pairseq and Snside :: pairseq
  defines "c \<equiv> IdxSum (P S) ! (length (P S) - 1)"
      and "cN \<equiv> IdxSum (P Snside) ! (length (P Snside) - 1)"
  assumes ST: "S \<in> T_PS" and multi: "1 < length (P S)"
    and SnT: "Snside \<in> T_PS" and multiN: "1 < length (P Snside)"
    and F8end: "entry S 0 c = entry Snside 0 cN + shamt"
    and F9end: "entry S 1 c \<le> entry Snside 1 cN"
  shows "entry (last (P S)) 0 0 = entry (last (P Snside)) 0 0 + shamt"
    and "entry (last (P S)) 1 0 \<le> entry (last (P Snside)) 1 0"
proof -
  have eS0: "entry (last (P S)) 0 0 = entry S 0 c" unfolding c_def
    by (rule oper_d1pos_anchor_tail_entry[OF ST multi])
  have eS1: "entry (last (P S)) 1 0 = entry S 1 c" unfolding c_def
    by (rule oper_d1pos_anchor_tail_entry[OF ST multi])
  have eSn0: "entry (last (P Snside)) 0 0 = entry Snside 0 cN" unfolding cN_def
    by (rule oper_d1pos_anchor_tail_entry[OF SnT multiN])
  have eSn1: "entry (last (P Snside)) 1 0 = entry Snside 1 cN" unfolding cN_def
    by (rule oper_d1pos_anchor_tail_entry[OF SnT multiN])
  show "entry (last (P S)) 0 0 = entry (last (P Snside)) 0 0 + shamt"
    using eS0 eSn0 F8end by simp
  show "entry (last (P S)) 1 0 \<le> entry (last (P Snside)) 1 0"
    using eS1 eSn1 F9end by simp
qed

text \<open>§6.8 d0pos ¬brle — BRICK 3 (Br alignment): the \<open>Br\<close>-decomposition of a
  branch slice \<open>seg M j0' j1'\<close> reshaped into the AMBIENT \<open>M\<close>-coordinates.  When the
  branch is non-empty (\<open>TrMax (seg M j0' j1') \<noteq> Lng (seg M j0' j1') - 1\<close>), unfolding
  @{thm [source] Br_def} gives \<open>P\<close> of an inner slice \<open>seg (seg M j0' j1')
  (TrMax+1) (Lng-1)\<close>, which @{thm [source] seg_of_seg} collapses to the single
  ambient slice \<open>seg M (j0' + TrMax (seg M j0' j1') + 1) j1'\<close>.  This is the common
  shape used by BOTH halves of the §6.8 assembly: the \<open>M\<close>-side (\<open>M' = M[n]\<close>-slice,
  \<open>BrM'P\<close>) and the \<open>N\<close>-side (\<open>N\<^sub>p\<close>-slice, \<open>BrNpP\<close>).  DEEP-VERIFIED at rank 8 (KMAX=8,
  python/br3_align_check.py): facts (A)/(B), 1395/1395 (len\<le>12 val\<le>4) and
  3276/3276 (len\<le>11 val\<le>5), 0 failures.\<close>

lemma Br_seg_reshape:
  fixes M :: pairseq
  assumes lt: "j0' < j1'" and jM: "j1' < Lng M"
    and trne: "TrMax (seg M j0' j1') \<noteq> Lng (seg M j0' j1') - 1"
  shows "Br (seg M j0' j1') = P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')"
proof -
  let ?M' = "seg M j0' j1'"
  let ?t = "TrMax ?M'"
  \<comment> \<open>non-empty branch: @{thm [source] Br_def} takes the \<open>P\<close>-of-inner-slice branch\<close>
  have BrM': "Br ?M' = P (seg ?M' (?t + 1) (Lng ?M' - 1))"
    using trne by (simp add: Br_def)
  \<comment> \<open>inner-slice length: \<open>Lng ?M' - 1 = j1' - j0'\<close> (since \<open>j0' < j1'\<close>)\<close>
  have LM': "Lng ?M' - 1 = j1' - j0'" using lt by (simp del: Lng_seg add: Lng_seg)
  \<comment> \<open>seg-of-seg: \<open>a = j0' \<le> b = j1'\<close>, \<open>d = Lng ?M' - 1 \<le> b - a = j1' - j0'\<close>\<close>
  have ab: "j0' \<le> j1'" using lt by linarith
  have db: "Lng ?M' - 1 \<le> j1' - j0'" using LM' by simp
  have reshape: "seg ?M' (?t + 1) (Lng ?M' - 1) = seg M (j0' + (?t + 1)) (j0' + (Lng ?M' - 1))"
    by (rule seg_of_seg[OF ab db])
  \<comment> \<open>the right endpoint \<open>j0' + (Lng ?M' - 1) = j1'\<close>\<close>
  have rend: "j0' + (Lng ?M' - 1) = j1'" using LM' lt by linarith
  have "seg ?M' (?t + 1) (Lng ?M' - 1) = seg M (j0' + ?t + 1) j1'"
    using reshape rend by (simp add: add.assoc)
  thus ?thesis using BrM' by simp
qed

text \<open>§6.8 d0pos ¬brle — BRICK 3 (combined Br alignment).  In the formula-G d1pos
  ¬brle context (the SAME hypotheses as @{thm [source] TrMax_seg_oper_d1pos_eq_span},
  plus \<open>notbrle\<close>), packages the structural skeleton that the main identification stub
  \<open>oper_d1pos_notbrle_LOW_take_eq\<close> (below) assembles:
    (BrM'P)  \<open>Br M' = P (seg M (j0' + T + 1) j1')\<close>,
    (BrNpP)  \<open>Br N\<^sub>p = P (seg N (j0red + T + 1) j1red)\<close>,
  where \<open>T = TrMax M' = TrMax N\<^sub>p\<close> (the SHARED trunk end, via TrEq), and BOTH
  branches are NON-empty (\<open>Br M' \<noteq> []\<close> from \<open>notbrle\<close>; \<open>Br N\<^sub>p \<noteq> []\<close> from \<open>tnc\<close>).
  The N-side endpoint is the FREE \<open>j1red\<close> (NOT \<open>Lng N - 1\<close>).  This is the pure
  structural identification (facts A/B/C/D); the remaining per-component shift
  identity (LOW = \<open>map (IncrFirst^^shamt)\<close> of \<open>take\<close>, fact F) is the documented
  block-fold blocker.  DEEP-VERIFIED rank 8 (python/br3_align_check.py): A/B/C/D
  all 1395/1395 (len\<le>12 val\<le>4) and 3276/3276 (len\<le>11 val\<le>5), 0 failures.\<close>

lemma oper_d1pos_notbrle_Br_align:
  fixes N :: pairseq
  assumes N: "N \<in> T_PS" and L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and n1: "1 \<le> n"
    and qn: "q < n"
    and s0w: "j0red < Lng N - 1"
    and s0eq: "j0red = parent N 1 (Lng N - 1) + s0"
    and s0lt: "s0 < Lng N - 1 - parent N 1 (Lng N - 1)"
    and j0'eq: "j0' = parent N 1 (Lng N - 1)
                  + q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0"
    and shamt: "shamt = q * (entry N 0 (Lng N - 1) - entry N 0 (parent N 1 (Lng N - 1)))"
    and j1redle: "j1red \<le> Lng N - 1"
    and j0j1red: "j0red < j1red"
    and j1redspan: "j1red \<le> j0red + (j1' - j0')"
    and j0j1': "j0' < j1'"
    and j1lt: "j1' < Lng ((N::pairseq)[n])"
    and tnc: "TrMax (seg N j0red j1red) \<le> j1red - 1 - j0red"
    and stop: "\<not> nextR (seg ((N::pairseq)[n]) j0' j1') 1
                  (TrMax (seg N j0red j1red))
                  (TrMax (seg N j0red j1red) + 1)"
    and notbrle: "\<not> (TrMax (seg ((N::pairseq)[n]) j0' j1')
                        = Lng (seg ((N::pairseq)[n]) j0' j1') - 1
                      \<or> le0 (seg ((N::pairseq)[n]) j0' j1')
                            (TrMax (seg ((N::pairseq)[n]) j0' j1') + 1)
                            (Lng (seg ((N::pairseq)[n]) j0' j1') - 1))"
  shows "TrMax (seg ((N::pairseq)[n]) j0' j1') = TrMax (seg N j0red j1red)
       \<and> Br (seg ((N::pairseq)[n]) j0' j1')
           = P (seg ((N::pairseq)[n])
                  (j0' + TrMax (seg ((N::pairseq)[n]) j0' j1') + 1) j1')
       \<and> Br (seg N j0red j1red)
           = P (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red)
       \<and> Br (seg ((N::pairseq)[n]) j0' j1') \<noteq> []
       \<and> Br (seg N j0red j1red) \<noteq> []"
proof -
  let ?M = "(N::pairseq)[n]"
  let ?Mp = "seg ?M j0' j1'"
  let ?Np = "seg N j0red j1red"
  \<comment> \<open>(D) TrEq via the CAPPED-general span keystone\<close>
  have TrEq: "TrMax ?Mp = TrMax ?Np"
    by (rule TrMax_seg_oper_d1pos_eq_span[OF N L notzero hp i1z j0lt n1 qn s0w s0eq
              s0lt j0'eq shamt j1redle j0j1red j1redspan j0j1' j1lt tnc stop])
  \<comment> \<open>(C) M-side non-empty: \<open>notbrle\<close> gives \<open>TrMax ?Mp \<noteq> Lng ?Mp - 1\<close>\<close>
  have trneM: "TrMax ?Mp \<noteq> Lng ?Mp - 1" using notbrle by blast
  \<comment> \<open>(C) N-side non-empty: \<open>tnc\<close> gives \<open>TrMax ?Np \<le> j1red-1-j0red < j1red-j0red = Lng ?Np - 1\<close>\<close>
  have lenNp: "Lng ?Np - 1 = j1red - j0red" using j0j1red by (simp del: Lng_seg add: Lng_seg)
  have trneN: "TrMax ?Np \<noteq> Lng ?Np - 1"
  proof -
    have "TrMax ?Np < j1red - j0red" using tnc j0j1red by linarith
    thus ?thesis using lenNp by simp
  qed
  \<comment> \<open>(A) BrM'P: reshape the M-side branch into ambient \<open>M\<close>-coords\<close>
  have BrM'P: "Br ?Mp = P (seg ?M (j0' + TrMax ?Mp + 1) j1')"
    by (rule Br_seg_reshape[OF j0j1' j1lt trneM])
  \<comment> \<open>(B) BrNpP: reshape the N-side branch into ambient \<open>N\<close>-coords\<close>
  have j1redltN: "j1red < Lng N" using j1redle L by linarith
  have BrNpP: "Br ?Np = P (seg N (j0red + TrMax ?Np + 1) j1red)"
    by (rule Br_seg_reshape[OF j0j1red j1redltN trneN])
  \<comment> \<open>non-emptiness of both branch lists\<close>
  have BrM'ne: "Br ?Mp \<noteq> []" using BrM'P P_nonempty by simp
  have BrNpne: "Br ?Np \<noteq> []" using BrNpP P_nonempty by simp
  show ?thesis using TrEq BrM'P BrNpP BrM'ne BrNpne by blast
qed

text \<open>§6.8 d1pos REGIME A verbatim agreement.  When the index \<open>x\<close> lies BELOW the
  last block boundary \<open>Lng N - 1\<close> (\<open>x \<le> Lng N - 2\<close>, i.e.\ \<open>x < Lng N - 1\<close>), the
  \<open>i\<^sub>1=1\<close> oper reads off \<open>N\<close> VERBATIM: \<open>(N[n]) ! x = N ! x\<close>.  Two sub-cases:
  the prefix \<open>x < j\<^sub>m\<^sub>2\<close> is the verbatim \<open>take j\<^sub>m\<^sub>2 N\<close> (@{thm [source]
  oper_d1pos_nth_prefix}); block 0 (\<open>j\<^sub>m\<^sub>2 \<le> x < Lng N - 1\<close>, offset \<open>s\<^sub>x = x - j\<^sub>m\<^sub>2 < w\<close>,
  \<open>q = 0 < n\<close>) is @{thm [source] oper_d1pos_nth} with NO per-block shift
  (\<open>0\<cdot>\<delta> = 0\<close>) — so it equals \<open>(entry N 0 x, entry N 1 x) = N ! x\<close>.  This is the
  REGIME A keystone simplification: the slice prefix below the first fold is
  literally \<open>N\<close>, so there is NO \<open>(IncrFirst^^shamt)\<close> shift (\<open>shamt = 0\<close>).\<close>

lemma oper_d1pos_nth_low_verbatim:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and n1: "1 \<le> n"
    and xlt: "x < Lng N - 1"
  shows "((N::pairseq)[n]) ! x = N ! x"
proof (cases "x < parent N 1 (Lng N - 1)")
  case True
  show ?thesis by (rule oper_d1pos_nth_prefix[OF L notzero hp i1z True])
next
  case False
  let ?j0 = "parent N 1 (Lng N - 1)"  let ?w = "Lng N - 1 - ?j0"
  have ge: "?j0 \<le> x" using False by simp
  let ?sx = "x - ?j0"
  have sxw: "?sx < ?w" using xlt ge by linarith
  have q0n: "(0::nat) < n" using n1 by simp
  have split: "?j0 + 0 * ?w + ?sx = x" using ge by simp
  have "((N::pairseq)[n]) ! x = ((N::pairseq)[n]) ! (?j0 + 0 * ?w + ?sx)"
    using split by simp
  also have "\<dots> = (entry N 0 (?j0 + ?sx) + 0 * (entry N 0 (Lng N - 1) - entry N 0 ?j0),
                   entry N 1 (?j0 + ?sx))"
    by (rule oper_d1pos_nth[OF L notzero hp i1z j0lt q0n sxw])
  also have "\<dots> = (entry N 0 x, entry N 1 x)" using ge by simp
  also have "\<dots> = N ! x"
  proof -
    have xN: "x < Lng N" using xlt by linarith
    show ?thesis using xN by (cases "N ! x") (simp add: entry_def)
  qed
  finally show ?thesis .
qed

text \<open>§6.8 d1pos PREFIX trunk-confinement \<open>tnc\<close> (\<open>oper_d1pos_ctx_tnc_prefix\<close>) — the
  TWIN of @{thm [source] oper_d1pos_ctx_tnc_capped} for the PREFIX region
  \<open>j'\<^sub>0 < j\<^sub>m\<^sub>2 = parent N 1 (Lng N-1)\<close> (the regA/boundary cells, where
  \<open>j\<^sub>0\<^sup>red = j'\<^sub>0\<close>, \<open>j\<^sub>1\<^sup>red = Lng N-1\<close>, \<open>q = 0\<close>, \<open>shamt = 0\<close>).  In this region the
  periodic gate \<open>s\<^sub>0eq : j\<^sub>0\<^sup>red = j\<^sub>m\<^sub>2 + s\<^sub>0\<close> of \<open>_brle_capped\<close> is UNSATISFIABLE
  (\<open>j'\<^sub>0 < j\<^sub>m\<^sub>2\<close>), so \<open>oper_d1pos_ctx_tnc_capped\<close> does not apply.  The conclusion
  \<open>TrMax (seg N j'\<^sub>0 (Lng N-1)) \<le> Lng N-1-1-j'\<^sub>0 = Lng N\<^sub>p - 2\<close> is exactly the \<open>tnc\<close>
  hypothesis of \<open>oper_d1pos_notbrle_LOW_take_eq_regA\<close> and
  \<open>oper_d1pos_notbrle_LOW_take_eq_boundary\<close> (both defined below).

  ROUTE (no periodic machinery; the VERBATIM-prefix analogue of the \<open>_brle_capped\<close>
  contrapositive).  Write \<open>N\<^sub>p = seg N j'\<^sub>0 (Lng N-1)\<close>, \<open>M' = seg (N[n]) j'\<^sub>0 j'\<^sub>1\<close>,
  \<open>c = Lng N\<^sub>p - 2 = Lng N-1-1-j'\<^sub>0\<close>.  Show \<open>\<not>fill\<close> (\<open>TrMax N\<^sub>p \<noteq> Lng N\<^sub>p - 1\<close>) by
  contradiction; with @{thm [source] TrMax_bound} (\<open>\<le> Lng N\<^sub>p-1\<close>) that gives the
  claim.  Assume \<open>fill : TrMax N\<^sub>p = Lng N\<^sub>p - 1\<close>.  From \<open>\<not>brle\<close> the strict-2
  \<open>M'\<close>-confinement \<open>tncM1 : TrMax M' + 1 \<le> c\<close> and the \<open>M'\<close>-stop
  (@{thm [source] TrMax_stop}) hold exactly as in
  @{thm [source] TrMax_seg_oper_d1pos_eq_notbrle_uncapped}; \<open>M'\<close> and \<open>N\<^sub>p\<close> agree
  VERBATIM on \<open>[0,c]\<close> (the read index \<open>j'\<^sub>0 + s = j'\<^sub>0 + s \<le> Lng N-2 < Lng N-1\<close> is
  strictly below the boundary, @{thm [source] oper_d1pos_nth_low_verbatim}), so the
  symmetric prefix keystone @{thm [source] TrMax_eq_of_prefix_agree_sym} pins
  \<open>TrMax M' = TrMax N\<^sub>p\<close>.  But \<open>tncM1\<close> gives \<open>TrMax M' \<le> c = Lng N\<^sub>p - 2\<close> while
  \<open>fill\<close> gives \<open>TrMax N\<^sub>p = Lng N\<^sub>p - 1\<close>, contradicting \<open>TrMax M' = TrMax N\<^sub>p\<close>.
  EMPIRICAL (rank-stratified \<open>gen_std\<close> = diagSeq\<rightarrow>oper-closure\<rightarrow>is_standard, KMAX=10
  len\<le>12, /tmp/prefix_tnc_verify.py, /tmp/prefix_fillbrle.py): the target \<open>tnc\<close>
  909/909 in-context prefix \<open>\<not>brle\<close> cases; the contrapositive engine
  \<open>fill(N\<^sub>p) \<Longrightarrow> brle(M')\<close> 18/18 (val\<le>4) + 33/33 (val\<le>5) over ALL prefix fill
  slices — SOUND; boundary stop 909/909.\<close>

lemma oper_d1pos_ctx_tnc_prefix:
  fixes N :: pairseq
  assumes N: "N \<in> T_PS" and L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and n1: "1 \<le> n"
    and j0pre: "j0' < parent N 1 (Lng N - 1)"
    and bge: "Lng N - 1 \<le> j1'"
    and j0j1': "j0' < j1'"
    and j1lt: "j1' < Lng ((N::pairseq)[n])"
    \<comment> \<open>\<open>\<not>brle\<close> on the consumer slice \<open>M' = seg (N[n]) j'\<^sub>0 j'\<^sub>1\<close>\<close>
    and notbrle: "\<not> (TrMax (seg ((N::pairseq)[n]) j0' j1')
                        = Lng (seg ((N::pairseq)[n]) j0' j1') - 1
                      \<or> le0 (seg ((N::pairseq)[n]) j0' j1')
                            (TrMax (seg ((N::pairseq)[n]) j0' j1') + 1)
                            (Lng (seg ((N::pairseq)[n]) j0' j1') - 1))"
  shows "TrMax (seg N j0' (Lng N - 1)) \<le> Lng N - 1 - 1 - j0'"
proof -
  let ?M = "(N::pairseq)[n]"
  let ?j1N = "Lng N - 1"
  let ?Mp = "seg ?M j0' j1'"
  let ?Np = "seg N j0' ?j1N"
  let ?c = "?j1N - 1 - j0'"
  \<comment> \<open>prefix geometry: \<open>j'\<^sub>0 < Lng N-1 \<le> j'\<^sub>1\<close>\<close>
  have j0ltN: "j0' < ?j1N" using j0pre j0lt by linarith
  have j0'le: "j0' \<le> j1'" using j0j1' by linarith
  have MpT: "?Mp \<in> T_PS" using j0'le by (simp add: T_PS_def seg_def)
  have NpT: "?Np \<in> T_PS" using j0ltN by (simp add: T_PS_def seg_def)
  have LMp: "Lng ?Mp = Suc j1' - j0'" by simp
  have LNp: "Lng ?Np = Suc ?j1N - j0'" by simp
  have LNp2: "2 \<le> Lng ?Np" using LNp j0ltN by linarith
  have cLNp: "?c = Lng ?Np - 2" using LNp j0ltN by linarith
  have cN: "?c < Lng ?Np" using LNp2 cLNp by linarith
  \<comment> \<open>FLAT \<open>j'\<^sub>0 + c = Lng N-2\<close> via fresh vars (avoid the double-nat-sub linarith loop on
     \<open>j'\<^sub>0 + (Lng N-1-1-j'\<^sub>0)\<close>)\<close>
  obtain a b where ab: "a = j0'" "b = ?j1N" by blast
  have alt: "a < b" using j0ltN ab by simp
  have cab: "?c = b - 1 - a" using ab by simp
  have j0c: "j0' + ?c = ?j1N - 1"
  proof -
    have "j0' + ?c = a + (b - 1 - a)" using ab cab by simp
    also have "\<dots> = b - 1" using alt by simp
    finally show ?thesis using ab by simp
  qed
  have j0c_lt: "j0' + ?c < ?j1N"
  proof -
    have "j0' + ?c = b - 1" using j0c ab by simp
    also have "b - 1 < b" using alt by simp
    finally show ?thesis using ab by simp
  qed
  \<comment> \<open>freeze \<open>c\<close> and \<open>Lng N\<^sub>p\<close> as fresh vars for the arithmetic steps below (the
     \<open>let\<close>-bound \<open>?c = Lng N-1-1-j'\<^sub>0\<close> re-expands to a nested double-nat-sub that
     loops every decision procedure once an extra hyp is supplied)\<close>
  obtain cc where ccdef: "cc = ?c" by blast
  obtain Ln where Lndef: "Ln = Lng ?Np" by blast
  have ccLn: "cc = Ln - 2" using ccdef Lndef cLNp by simp
  have Ln2: "2 \<le> Ln" using Lndef LNp2 by simp
  \<comment> \<open>\<open>cc < Lng M'\<close> via flat fresh vars (no \<open>?c\<close>/\<open>Lng\<close> re-expansion under a decision proc)\<close>
  obtain Bj where Bjdef: "Bj = (j1'::nat)" by blast
  have j0ccb: "j0' + cc < b" using j0c_lt ccdef ab by simp
  have bBj: "b \<le> Bj" using bge ab Bjdef by simp
  have cMcc: "cc < Lng ?Mp"
  proof -
    have "j0' + cc < Suc Bj" using j0ccb bBj by linarith
    hence "cc < Suc Bj - j0'" by linarith
    thus ?thesis using LMp Bjdef by simp
  qed
  have cM: "?c < Lng ?Mp" using cMcc ccdef by simp
  \<comment> \<open>VERBATIM agreement on \<open>[0,c]\<close>: the read index \<open>j'\<^sub>0 + s \<le> Lng N-2 < Lng N-1\<close>\<close>
  have cNcc: "cc < Lng ?Np" using cN ccdef by simp
  have agree: "\<And>s. s \<le> ?c \<Longrightarrow> ?Mp ! s = ?Np ! s"
  proof -
    fix s assume sc0: "s \<le> ?c"
    have sc: "s \<le> cc" using sc0 ccdef by simp
    have sM: "s < Lng ?Mp" using sc cMcc by simp
    have sN: "s < Lng ?Np" using sc cNcc by simp
    have sM': "s < Suc j1' - j0'" using sM LMp by simp
    have sNp: "s < Suc ?j1N - j0'" using sN LNp by simp
    have idxlt: "j0' + s < ?j1N"
    proof -
      have "j0' + s \<le> j0' + ?c" using sc0 by simp
      also have "\<dots> < ?j1N" using j0c_lt by simp
      finally show ?thesis .
    qed
    have "?Mp ! s = ?M ! (j0' + s)" using sM' by (rule seg_nth_eq)
    also have "\<dots> = N ! (j0' + s)"
      by (rule oper_d1pos_nth_low_verbatim[OF L notzero hp i1z j0lt n1 idxlt])
    also have "\<dots> = ?Np ! s" using sNp by (simp add: seg_nth_eq)
    finally show "?Mp ! s = ?Np ! s" .
  qed
  \<comment> \<open>extra boundary geometry: \<open>jm2\<close>, \<open>w\<close>, \<open>delta\<close>; \<open>c+1 = Lng Np-1\<close>, \<open>j'\<^sub>0+(c+1) = Lng N-1\<close>\<close>
  let ?jm2 = "parent N 1 ?j1N"
  let ?w = "?j1N - ?jm2"
  let ?delta = "entry N 0 ?j1N - entry N 0 ?jm2"
  have w0: "0 < ?w" using j0lt by linarith
  have jm2leN: "?jm2 \<le> ?j1N" using j0lt by linarith
  have jm2w: "?jm2 + ?w = ?j1N" using le_add_diff_inverse[OF jm2leN] .
  have idx_c1: "j0' + (?c + 1) = ?j1N"
  proof -
    have "j0' + (?c + 1) = (j0' + ?c) + 1" by simp
    also have "\<dots> = (?j1N - 1) + 1" using j0c by simp
    also have "\<dots> = ?j1N" using j0ltN by simp
    finally show ?thesis .
  qed
  have c1eq: "?c + 1 = ?j1N - j0'"
  proof -
    obtain e where edef: "e = ?c + 1" by blast
    have "j0' + e = ?j1N" using idx_c1 edef by simp
    hence "e = ?j1N - j0'" by simp
    thus ?thesis using edef by simp
  qed
  have c1M: "?c + 1 < Lng ?Mp"
  proof -
    obtain e where edef: "e = ?c + 1" by blast
    have "j0' + e = b" using idx_c1 edef ab by simp
    hence "j0' + e < Suc Bj" using bBj by linarith
    hence "e < Suc Bj - j0'" by linarith
    thus ?thesis using edef LMp Bjdef by simp
  qed
  \<comment> \<open>\<not>fill: assume the \<open>N\<close>-reference trunk fills, derive a contradiction with \<open>\<not>brle\<close>\<close>
  have notfill: "TrMax ?Np \<noteq> Lng ?Np - 1"
  proof
    assume fill: "TrMax ?Np = Lng ?Np - 1"
    \<comment> \<open>\<open>\<not>brle\<close> as its two conjuncts on the \<open>M'\<close>-side\<close>
    have ndisj1: "TrMax ?Mp \<noteq> Lng ?Mp - 1"
      and notle: "\<not> le0 ?Mp (TrMax ?Mp + 1) (Lng ?Mp - 1)" using notbrle by auto
    have tbM: "TrMax ?Mp \<le> Lng ?Mp - 1" by (rule TrMax_bound[OF MpT])
    have Mlt: "TrMax ?Mp < Lng ?Mp - 1" using tbM ndisj1 by linarith
    have LMp2: "2 \<le> Lng ?Mp"
    proof -
      obtain dd where dddef: "dd = ?c + 1" by blast
      have "dd < Lng ?Mp" using c1M dddef by simp
      moreover have "1 \<le> dd" using dddef by simp
      ultimately show ?thesis by linarith
    qed
    \<comment> \<open>\<open>2 \<le> n\<close>: the boundary node \<open>Lng N-1\<close> already sits in block 1 of \<open>M\<close>\<close>
    have bnd: "?j1N < Lng ?M"
    proof -
      have "?j1N \<le> j1'" using bge .
      thus ?thesis using j1lt by linarith
    qed
    have LngMn: "Lng ?M = ?jm2 + n * ?w"
      by (rule oper_d1pos_LngM[OF L notzero hp i1z j0lt])
    have n2: "2 \<le> n"
    proof -
      have "?jm2 + 1 * ?w < ?jm2 + n * ?w" using bnd LngMn jm2w w0 by simp
      hence "1 * ?w < n * ?w" by linarith
      thus ?thesis using w0 by (cases n) auto
    qed
    have qn: "1 < n" using n2 by simp
    \<comment> \<open>=== boundary B3: \<open>entry M' 1 (c+1) \<le> entry M' 1 c\<close> ===\<close>
    \<comment> \<open>\<open>entry M' 1 (c+1) = entry N 1 jm2\<close> (block 1 start, period reset)\<close>
    have e1_c1: "entry ?Mp 1 (?c + 1) = entry N 1 ?jm2"
    proof -
      have e1: "?j1N = ?jm2 + 1 * ?w + 0" using jm2w by simp
      have idxeq1: "j0' + (?c + 1) = ?jm2 + 1 * ?w + 0"
        using idx_c1 e1 by simp
      have "entry ?Mp 1 (?c + 1) = entry ?M 1 (j0' + (?c + 1))"
        using c1M by (simp add: entry_seg)
      also have "\<dots> = entry ?M 1 (?jm2 + 1 * ?w + 0)"
        by (rule arg_cong[OF idxeq1, of "\<lambda>z. entry ?M 1 z"])
      also have "\<dots> = entry N 1 (?jm2 + 0)"
        by (rule oper_d1pos_entry1[OF L notzero hp i1z j0lt qn]) (use w0 in simp)
      finally show ?thesis by simp
    qed
    \<comment> \<open>\<open>entry M' 1 c = entry N 1 (Lng N-2)\<close> (verbatim, \<open>j'\<^sub>0+c = Lng N-2 < Lng N-1\<close>)\<close>
    have idx_c: "j0' + ?c = ?j1N - 1" using j0c .
    have idx_c_lt: "j0' + ?c < ?j1N" using j0c_lt .
    have e1_c: "entry ?Mp 1 ?c = entry N 1 (?j1N - 1)"
    proof -
      have cMlt: "?c < Lng ?Mp" using cM .
      have "entry ?Mp 1 ?c = entry ?M 1 (j0' + ?c)"
        using cMlt by (simp add: entry_seg)
      also have "\<dots> = entry N 1 (j0' + ?c)"
      proof -
        have "?M ! (j0' + ?c) = N ! (j0' + ?c)"
          by (rule oper_d1pos_nth_low_verbatim[OF L notzero hp i1z j0lt n1 idx_c_lt])
        thus ?thesis by (simp add: entry_def)
      qed
      also have "\<dots> = entry N 1 (?j1N - 1)" using idx_c by simp
      finally show ?thesis .
    qed
    \<comment> \<open>B3N (the \<open>N\<close>-side boundary inequality): \<open>entry N 1 jm2 \<le> entry N 1 (Lng N-2)\<close>\<close>
    have haspar1: "hasParent N 1 ?j1N" using hp i1z by simp
    have B3N: "entry N 1 ?jm2 \<le> entry N 1 (?j1N - 1)"
    proof -
      have b3nlem: "entry N 1 (parent N 1 (Lng N - 1)) \<le> entry N 1 (Lng N - 2)"
        by (rule oper_d1pos_b3n_boundary[OF N L haspar1 j0ltN fill])
      have idxeq: "?j1N - 1 = Lng N - 2" by simp
      show ?thesis using b3nlem idxeq by simp
    qed
    have B3: "entry ?Mp 1 (?c + 1) \<le> entry ?Mp 1 ?c"
      using B3N e1_c1 e1_c by simp
    \<comment> \<open>=== confinement \<open>TrMax M' \<le> c\<close> via the boundary stop ===\<close>
    have boundary_stop: "\<not> nextR ?Mp 1 ?c (?c + 1)"
    proof
      assume "nextR ?Mp 1 ?c (?c + 1)"
      hence "nextrel1 ?Mp ?c (?c + 1)" by (simp add: nextR_def)
      hence "entry ?Mp 1 ?c < entry ?Mp 1 (?c + 1)" by (simp add: nextrel1_def)
      thus False using B3 by simp
    qed
    have tncM: "TrMax ?Mp \<le> ?c"
    proof (rule ccontr)
      assume "\<not> TrMax ?Mp \<le> ?c"
      hence "?c < TrMax ?Mp" by simp
      hence "nextR ?Mp 1 ?c (?c + 1)" by (rule TrMax_trunk_step[OF MpT])
      thus False using boundary_stop by simp
    qed
    \<comment> \<open>=== strict-2 \<open>TrMax M' + 1 \<le> c\<close> via the boundary \<open>le0\<close> + \<open>notle\<close> ===\<close>
    \<comment> \<open>\<open>le0 M' (c+1) (Lng M'-1)\<close>: block-1 start \<open>Lng N-1\<close> row-0-reaches any later in-range index\<close>
    have le0bnd: "le0 ?Mp (?c + 1) (Lng ?Mp - 1)"
    proof -
      let ?end = "Lng ?Mp - 1"
      have endeq: "?end = j1' - j0'" using LMp j0j1' by linarith
      have c1le: "?c + 1 \<le> ?end"
      proof -
        have "?c + 1 = ?j1N - j0'" using c1eq .
        also have "\<dots> \<le> j1' - j0'" using bge by linarith
        also have "\<dots> = ?end" using endeq by simp
        finally show ?thesis .
      qed
      have c1leD: "?c + 1 \<le> j1' - j0'" using c1le endeq by simp
      have endleD: "?end \<le> j1' - j0'" using endeq by simp
      have idx_end: "j0' + ?end = j1'" using endeq j0'le by simp
      have seg_iff: "le0 ?Mp (?c + 1) ?end \<longleftrightarrow> le0 ?M (j0' + (?c + 1)) (j0' + ?end)"
        by (rule adm_le0_seg[OF j1lt c1leD endleD j0'le])
      \<comment> \<open>\<open>1 \<cdot> w\<close> block-1 start, \<open>jm2 + 1\<cdot>w = Lng N-1 = j'\<^sub>0+(c+1)\<close>; reach to \<open>j'\<^sub>1\<close>\<close>
      have start1: "?jm2 + 1 * ?w = ?j1N" using jm2w by simp
      have startle: "?jm2 + 1 * ?w \<le> j1'"
      proof -
        have "?jm2 + 1 * ?w = ?j1N" using start1 .
        also have "\<dots> \<le> j1'" using bge by simp
        finally show ?thesis .
      qed
      have reach: "le0 ?M (?jm2 + 1 * ?w) j1'"
        by (rule oper_d1pos_le0_start_to_any[OF N L notzero hp i1z j0lt qn startle j1lt])
      have lhseq: "j0' + (?c + 1) = ?jm2 + 1 * ?w" using idx_c1 start1 by simp
      have reach': "le0 ?M (j0' + (?c + 1)) j1'"
        using reach lhseq by simp
      have "le0 ?M (j0' + (?c + 1)) (j0' + ?end)"
        using reach' idx_end by simp
      thus ?thesis using seg_iff by simp
    qed
    have tncM1: "TrMax ?Mp + 1 \<le> ?c"
    proof -
      have "TrMax ?Mp \<noteq> ?c"
      proof
        assume eq: "TrMax ?Mp = ?c"
        have "le0 ?Mp (TrMax ?Mp + 1) (Lng ?Mp - 1)" using le0bnd eq by simp
        thus False using notle by simp
      qed
      \<comment> \<open>\<open>TrMax M' \<noteq> cc\<close> + \<open>tncM : TrMax M' \<le> cc\<close> \<Rightarrow> \<open>TrMax M' + 1 \<le> cc\<close> (frozen \<open>cc\<close>)\<close>
      have neq': "TrMax ?Mp \<noteq> cc" using \<open>TrMax ?Mp \<noteq> ?c\<close> ccdef by simp
      have le': "TrMax ?Mp \<le> cc" using tncM ccdef by simp
      have "TrMax ?Mp + 1 \<le> cc" using neq' le' by linarith
      thus ?thesis using ccdef by simp
    qed
    \<comment> \<open>prefix keystone: \<open>TrMax M' = TrMax N\<^sub>p\<close> (symmetric, \<open>M'\<close>-side confinement + stop)\<close>
    have stopM: "\<not> nextR ?Mp 1 (TrMax ?Mp) (TrMax ?Mp + 1)"
      by (rule TrMax_stop[OF MpT Mlt])
    have TrEq: "TrMax ?Mp = TrMax ?Np"
      by (rule TrMax_eq_of_prefix_agree_sym[OF MpT NpT agree cM cN tncM1 stopM])
    \<comment> \<open>\<open>fill\<close>: \<open>TrMax N\<^sub>p = Lng N\<^sub>p-1 = cc+1 > cc \<ge> TrMax M'\<close>, contradiction (frozen \<open>cc\<close>/\<open>Ln\<close>)\<close>
    have fillLn: "TrMax ?Np = Ln - 1" using fill Lndef by simp
    have "TrMax ?Np = cc + 1" using fillLn ccLn Ln2 by simp
    hence TrMcc: "TrMax ?Mp = cc + 1" using TrEq by simp
    have "TrMax ?Mp \<le> cc" using tncM ccdef by simp
    thus False using TrMcc by linarith
  qed
  have tb: "TrMax ?Np \<le> Lng ?Np - 1" by (rule TrMax_bound[OF NpT])
  have NpltL: "TrMax ?Np < Ln - 1" using tb notfill Lndef by simp
  have "TrMax ?Np \<le> cc" using NpltL ccLn Ln2 by simp
  thus ?thesis using ccdef by simp
qed

text \<open>§6.8 d1pos REGIME A TrEq keystone (\<open>j'\<^sub>0 < j\<^sub>m\<^sub>2\<close>, so \<open>q = 0\<close>, \<open>shamt = 0\<close>,
  \<open>j\<^sub>0\<^sup>red = j'\<^sub>0\<close>).  Mirrors @{thm [source] TrMax_seg_oper_d1pos_eq_span} but the
  pointwise prefix agreement is the VERBATIM @{thm [source] oper_d1pos_nth_low_verbatim}
  (no \<open>(IncrFirst^^shamt)\<close> shift): on \<open>[0,c]\<close> (\<open>c = j\<^sub>1\<^sup>red - 1 - j\<^sub>0\<^sup>red\<close>, which is
  within both \<open>[j'\<^sub>0,j'\<^sub>1)\<close> and \<open>[j\<^sub>0\<^sup>red,j\<^sub>1\<^sup>red)\<close>) the indices \<open>j'\<^sub>0 + s = j\<^sub>0\<^sup>red + s\<close>
  satisfy \<open>j\<^sub>0\<^sup>red + s \<le> j\<^sub>1\<^sup>red - 1 < Lng N - 1\<close> (STRICTLY below the last boundary —
  the endpoint \<open>j\<^sub>1\<^sup>red\<close> itself is NOT in \<open>[0,c]\<close>), hence read off \<open>N\<close> verbatim on
  BOTH operands.  (NB the full slice \<open>seg ?M j'\<^sub>0 j\<^sub>1\<^sup>red = seg N j'\<^sub>0 j\<^sub>1\<^sup>red\<close> is FALSE
  when \<open>j\<^sub>1\<^sup>red = Lng N - 1\<close>: at the boundary index \<open>Lng N - 1\<close> the oper sits in
  block 1, row-0 still matches via \<open>\<delta>\<close> but row-1 \<open>= entry N 1 j\<^sub>m\<^sub>2 \<noteq> entry N 1 (Lng N-1)\<close>.
  This is why only the STRICT-prefix agreement \<open>[0,c]\<close> is used.)  The
  trunk-confinement (\<open>tnc\<close>) and boundary stop (\<open>stop\<close>) are supplied by the caller
  (same shape as the regime-B keystone).\<close>

lemma TrMax_seg_oper_d1pos_eq_regA:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and n1: "1 \<le> n"
    and j1redle: "j1red \<le> Lng N - 1"
    and j0j1red: "j0red < j1red"
    and j1redspan: "j1red \<le> j0red + (j1' - j0')"
    and j0eqA: "j0red = j0'"
    and j0j1': "j0' < j1'"
    and j1lt: "j1' < Lng ((N::pairseq)[n])"
    and tnc: "TrMax (seg N j0red j1red) \<le> j1red - 1 - j0red"
    and stop: "\<not> nextR (seg ((N::pairseq)[n]) j0' j1') 1
                  (TrMax (seg N j0red j1red))
                  (TrMax (seg N j0red j1red) + 1)"
  shows "TrMax (seg ((N::pairseq)[n]) j0' j1')
       = TrMax (seg N j0red j1red)"
proof -
  let ?M = "(N::pairseq)[n]"
  let ?Mp = "seg ?M j0' j1'"
  let ?Np = "seg N j0red j1red"
  let ?c = "j1red - 1 - j0red"
  have j0'le: "j0' \<le> j1'" using j0j1' by linarith
  have MpT: "?Mp \<in> T_PS" using j0'le by (simp add: T_PS_def seg_def)
  have NpT: "?Np \<in> T_PS" using j0j1red by (simp add: T_PS_def seg_def)
  have LMp: "Lng ?Mp = Suc j1' - j0'" by simp
  have LNp: "Lng ?Np = Suc j1red - j0red" by simp
  have cN: "?c < Lng ?Np" using LNp j0j1red by linarith
  have cM: "?c < Lng ?Mp"
  proof -
    have "?c < j1red - j0red" using j0j1red by linarith
    also have "j1red - j0red \<le> j1' - j0'" using j1redspan by linarith
    also have "j1' - j0' < Suc j1' - j0'" using j0j1' by linarith
    finally show ?thesis using LMp by simp
  qed
  have agree: "\<And>s. s \<le> ?c \<Longrightarrow> ?Mp ! s = ?Np ! s"
  proof -
    fix s assume sc: "s \<le> ?c"
    have sM: "s < Suc j1' - j0'" using sc cM LMp by linarith
    have sNp: "s < Suc j1red - j0red" using sc cN LNp by linarith
    \<comment> \<open>the read index \<open>j0' + s = j0red + s\<close> is STRICTLY below \<open>Lng N - 1\<close>\<close>
    have idxlt: "j0red + s < Lng N - 1"
    proof -
      have "j0red + s \<le> j1red - 1" using sc j0j1red by linarith
      thus ?thesis using j1redle j0j1red by linarith
    qed
    \<comment> \<open>both slices read \<open>?M ! (j0' + s) = N ! (j0' + s)\<close> verbatim (regime A, block-0)\<close>
    have "?Mp ! s = ?M ! (j0' + s)" using sM by (rule seg_nth_eq)
    also have "\<dots> = ?M ! (j0red + s)" using j0eqA by simp
    also have "\<dots> = N ! (j0red + s)"
      by (rule oper_d1pos_nth_low_verbatim[OF L notzero hp i1z j0lt n1 idxlt])
    also have "\<dots> = ?Np ! s" using sNp by (simp add: seg_nth_eq)
    finally show "?Mp ! s = ?Np ! s" .
  qed
  show ?thesis
    by (rule TrMax_eq_of_prefix_agree[OF MpT NpT agree cM cN tnc stop])
qed

text \<open>§6.8 d1pos REGIME A Br alignment (analogue of @{thm [source]
  oper_d1pos_notbrle_Br_align} for \<open>j'\<^sub>0 < j\<^sub>m\<^sub>2\<close>, \<open>shamt = 0\<close>): TrEq via the
  regime-A keystone, both branches non-empty (\<open>notbrle\<close> / \<open>tnc\<close>), and the two
  \<open>Br = P(...)\<close> reshapes (@{thm [source] Br_seg_reshape}).  Identical packaging to
  the regime-B version, only the TrEq witness differs.\<close>

lemma oper_d1pos_notbrle_Br_align_regA:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and n1: "1 \<le> n"
    and j1redle: "j1red \<le> Lng N - 1"
    and j0j1red: "j0red < j1red"
    and j1redspan: "j1red \<le> j0red + (j1' - j0')"
    and j0eqA: "j0red = j0'"
    and j0j1': "j0' < j1'"
    and j1lt: "j1' < Lng ((N::pairseq)[n])"
    and tnc: "TrMax (seg N j0red j1red) \<le> j1red - 1 - j0red"
    and stop: "\<not> nextR (seg ((N::pairseq)[n]) j0' j1') 1
                  (TrMax (seg N j0red j1red))
                  (TrMax (seg N j0red j1red) + 1)"
    and notbrle: "\<not> (TrMax (seg ((N::pairseq)[n]) j0' j1')
                        = Lng (seg ((N::pairseq)[n]) j0' j1') - 1
                      \<or> le0 (seg ((N::pairseq)[n]) j0' j1')
                            (TrMax (seg ((N::pairseq)[n]) j0' j1') + 1)
                            (Lng (seg ((N::pairseq)[n]) j0' j1') - 1))"
  shows "TrMax (seg ((N::pairseq)[n]) j0' j1') = TrMax (seg N j0red j1red)
       \<and> Br (seg ((N::pairseq)[n]) j0' j1')
           = P (seg ((N::pairseq)[n])
                  (j0' + TrMax (seg ((N::pairseq)[n]) j0' j1') + 1) j1')
       \<and> Br (seg N j0red j1red)
           = P (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red)
       \<and> Br (seg ((N::pairseq)[n]) j0' j1') \<noteq> []
       \<and> Br (seg N j0red j1red) \<noteq> []"
proof -
  let ?M = "(N::pairseq)[n]"
  let ?Mp = "seg ?M j0' j1'"
  let ?Np = "seg N j0red j1red"
  have TrEq: "TrMax ?Mp = TrMax ?Np"
    by (rule TrMax_seg_oper_d1pos_eq_regA[OF L notzero hp i1z j0lt n1 j1redle
              j0j1red j1redspan j0eqA j0j1' j1lt tnc stop])
  have trneM: "TrMax ?Mp \<noteq> Lng ?Mp - 1" using notbrle by blast
  have lenNp: "Lng ?Np - 1 = j1red - j0red" using j0j1red by (simp del: Lng_seg add: Lng_seg)
  have trneN: "TrMax ?Np \<noteq> Lng ?Np - 1"
  proof -
    have "TrMax ?Np < j1red - j0red" using tnc j0j1red by linarith
    thus ?thesis using lenNp by simp
  qed
  have BrM'P: "Br ?Mp = P (seg ?M (j0' + TrMax ?Mp + 1) j1')"
    by (rule Br_seg_reshape[OF j0j1' j1lt trneM])
  have j1redltN: "j1red < Lng N" using j1redle L by linarith
  have BrNpP: "Br ?Np = P (seg N (j0red + TrMax ?Np + 1) j1red)"
    by (rule Br_seg_reshape[OF j0j1red j1redltN trneN])
  have BrM'ne: "Br ?Mp \<noteq> []" using BrM'P P_nonempty by simp
  have BrNpne: "Br ?Np \<noteq> []" using BrNpP P_nonempty by simp
  show ?thesis using TrEq BrM'P BrNpP BrM'ne BrNpne by blast
qed

text \<open>§6.8 d1pos LOW verbatim seg (conc-A, regime A).  When the right endpoint
  \<open>b\<close> of a slice stays STRICTLY below the last boundary \<open>Lng N-1\<close>, the periodic
  \<open>N[n]\<close>-extension reads off \<open>N\<close> verbatim on the whole window \<open>[a,b]\<close>, so
  \<open>seg (N[n]) a b = seg N a b\<close>.  Pointwise from
  @{thm [source] oper_d1pos_nth_low_verbatim}.\<close>

lemma oper_d1pos_seg_low_verbatim:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and n1: "1 \<le> n"
    and ble: "b < Lng N - 1"
  shows "seg ((N::pairseq)[n]) a b = seg N a b"
proof (rule nth_equalityI)
  show leq: "length (seg ((N::pairseq)[n]) a b) = length (seg N a b)" by simp
  fix i assume "i < length (seg ((N::pairseq)[n]) a b)"
  hence ic: "i < Suc b - a" by simp
  show "seg ((N::pairseq)[n]) a b ! i = seg N a b ! i"
  proof (cases "a \<le> b")
    case False
    \<comment> \<open>empty window: both sides have length 0, but \<open>ic\<close> already excludes this\<close>
    have "Suc b - a = 0" using False by simp
    thus ?thesis using ic by simp
  next
    case True
    have aib: "a + i \<le> b" using ic True by linarith
    have idxlt: "a + i < Lng N - 1" using aib ble by linarith
    have "seg ((N::pairseq)[n]) a b ! i = ((N::pairseq)[n]) ! (a + i)"
      using ic by (rule seg_nth_eq)
    also have "\<dots> = N ! (a + i)"
      by (rule oper_d1pos_nth_low_verbatim[OF L notzero hp i1z j0lt n1 idxlt])
    also have "\<dots> = seg N a b ! i" using ic by (simp add: seg_nth_eq)
    finally show ?thesis .
  qed
qed

text \<open>§6.8 geomA helper — a START-prefix of a NON-MULTI \<open>T_PS\<close> sequence is itself
  NON-MULTI.  \<open>\<not> multiT M\<close> is \<open>(0,0) \<le>\<^sub>M (0, Lng M-1)\<close> (@{thm [source]
  m_6_2_not_multi_iff_le}), which by ancestor-monotonicity (@{thm [source]
  m_5_1_ancestor_tree_1}) extends to every earlier endpoint \<open>b \<le> Lng M-1\<close>; the
  resulting slice is \<open>monoT\<close> (@{thm [source] m_6_2_mono_ancestor_slice}) when
  \<open>0 < b\<close>, and a singleton (hence non-multi) when \<open>b = 0\<close>.\<close>

lemma notmulti_seg_prefix:
  assumes MT: "M \<in> T_PS" and nm: "\<not> multiT M" and ble: "b < Lng M"
  shows "\<not> multiT (seg M 0 b)"
proof (cases "0 < b")
  case False
  hence b0: "b = 0" by simp
  have L1: "Lng (seg M 0 b) = 1" using b0 by simp
  hence segT: "seg M 0 b \<in> T_PS" by (cases "seg M 0 b") (auto simp: T_PS_def)
  show ?thesis
  proof
    assume mult: "multiT (seg M 0 b)"
    have "1 < Lng (seg M 0 b)" by (rule multiT_imp_Lng_gt1[OF segT mult])
    thus False using L1 by simp
  qed
next
  case True
  have le0: "leR M 0 0 (Lng M - 1)" using m_6_2_not_multi_iff_le[OF MT] nm by simp
  have ble1: "b \<le> Lng M - 1" using ble by linarith
  have leb: "leR M 0 0 b" by (rule m_5_1_ancestor_tree_1[OF MT le0 _ ble1]) simp
  have "monoT (seg M 0 b)" by (rule m_6_2_mono_ancestor_slice[OF MT True leb])
  thus ?thesis by (simp add: multiT_def)
qed

text \<open>§6.8 geomA core (P-prefix anchor stability).  For a multi-\<open>P\<close> \<open>S \<in> T_PS\<close>
  with LAST \<open>FirstNodes\<close> anchor \<open>c = IdxSum (P S) ! (length (P S)-1)\<close>, truncating
  \<open>S\<close> to ANY prefix length \<open>m\<close> STRICTLY ABOVE the anchor (\<open>c < m \<le> Lng S\<close>) leaves
  the \<open>butlast\<close> of its \<open>P\<close>-decomposition UNCHANGED:
    \<open>butlast (P (seg S 0 (m-1))) = butlast (P S)\<close>.
  Both equal the LOW component list \<open>P (seg S 0 (c-1))\<close>: on the whole \<open>S\<close> by the
  anchor split (@{thm [source] oper_d1pos_notbrle_P_split}, tail single), and on
  the prefix \<open>seg S 0 (m-1)\<close> by the SAME split at \<open>c\<close> — the prefix-tail
  \<open>seg S c (m-1)\<close> is a start-prefix of the non-multi last component \<open>seg S c (Lng S-1)\<close>,
  hence non-multi (@{thm [source] notmulti_seg_prefix}).  DEEP-VERIFIED rank 8
  (/tmp/gen_butl_take.py): the identity holds for every \<open>c < m \<le> Lng S\<close>, 47/47.\<close>

lemma P_butlast_take_at_anchor:
  fixes S :: pairseq
  defines "c \<equiv> IdxSum (P S) ! (length (P S) - 1)"
  assumes ST: "S \<in> T_PS" and multi: "1 < length (P S)"
    and cm: "c < m" and mle: "m \<le> Lng S"
  shows "butlast (P (seg S 0 (m - 1))) = butlast (P S)"
proof -
  \<comment> \<open>anchor data on the whole \<open>S\<close>\<close>
  have c0: "0 < c" unfolding c_def by (rule oper_d1pos_branch_anchor(1)[OF ST multi])
  have cle: "c \<le> Lng S - 1" unfolding c_def by (rule oper_d1pos_branch_anchor(2)[OF ST multi])
  have lmin: "\<And>j. j < c \<Longrightarrow> entry S 0 c \<le> entry S 0 j"
    unfolding c_def using oper_d1pos_branch_anchor(3)[OF ST multi] by blast
  have tailnm: "\<not> multiT (seg S c (Lng S - 1))"
    unfolding c_def by (rule oper_d1pos_branch_anchor(4)[OF ST multi])
  have tailseg: "seg S c (Lng S - 1) = last (P S)"
    unfolding c_def by (rule oper_d1pos_branch_anchor(5)[OF ST multi])
  \<comment> \<open>\<open>butlast (P S) = P (seg S 0 (c-1))\<close> via the anchor split on the whole \<open>S\<close>\<close>
  have splitS: "P S = P (seg S 0 (c - 1)) @ [seg S c (Lng S - 1)]"
    by (rule oper_d1pos_notbrle_P_split[OF ST c0 cle lmin tailnm])
  have butS: "butlast (P S) = P (seg S 0 (c - 1))" using splitS by simp
  \<comment> \<open>the prefix \<open>Q = seg S 0 (m-1)\<close>\<close>
  let ?Q = "seg S 0 (m - 1)"
  have Lng_S_pos: "0 < Lng S" using c0 cle by linarith
  have mpos: "0 < m" using cm by linarith
  have LngQ: "Lng ?Q = m" using mle mpos by simp
  have Qne: "?Q \<noteq> []"
  proof
    assume "?Q = []"
    hence "length ?Q = 0" by simp
    thus False using LngQ mpos by simp
  qed
  have QT: "?Q \<in> T_PS" using Qne by (auto simp: T_PS_def seg_def)
  \<comment> \<open>the cut \<open>c\<close> on \<open>Q\<close>: \<open>0 < c\<close>, \<open>c \<le> Lng Q - 1 = m-1\<close>, lmin (entries agree on \<open>[0,m-1]\<close>)\<close>
  have cleQ: "c \<le> Lng ?Q - 1" using cm LngQ by simp
  have agreeE: "\<And>j. j \<le> m - 1 \<Longrightarrow> entry ?Q 0 j = entry S 0 j"
  proof -
    fix j assume jle: "j \<le> m - 1"
    have jlt: "j < Lng S" using jle cm mle by linarith
    show "entry ?Q 0 j = entry S 0 j"
      using jle by (simp add: entry_seg jlt)
  qed
  have lminQ: "\<And>j. j < c \<Longrightarrow> entry ?Q 0 c \<le> entry ?Q 0 j"
  proof -
    fix j assume jc: "j < c"
    have jm1: "j \<le> m - 1" using jc cm by linarith
    have cm1: "c \<le> m - 1" using cm by linarith
    have "entry ?Q 0 c = entry S 0 c" using agreeE[OF cm1] .
    moreover have "entry ?Q 0 j = entry S 0 j" using agreeE[OF jm1] .
    ultimately show "entry ?Q 0 c \<le> entry ?Q 0 j" using lmin[OF jc] by simp
  qed
  \<comment> \<open>the prefix-tail \<open>seg Q c (Lng Q-1) = seg S c (m-1)\<close> is a start-prefix of the
     non-multi last component, hence non-multi\<close>
  have segQtail: "seg ?Q c (Lng ?Q - 1) = seg S c (m - 1)"
  proof -
    have "seg ?Q c (Lng ?Q - 1) = seg ?Q c (m - 1)" using LngQ by simp
    also have "\<dots> = seg S (0 + c) (0 + (m - 1))"
      by (rule seg_of_seg) (use cm in linarith)+
    finally show ?thesis by simp
  qed
  have segS_tail_eq: "seg S c (m - 1) = seg (seg S c (Lng S - 1)) 0 (m - 1 - c)"
  proof -
    have "seg (seg S c (Lng S - 1)) 0 (m - 1 - c) = seg S (c + 0) (c + (m - 1 - c))"
      by (rule seg_of_seg) (use cle mle in linarith)+
    also have "c + (m - 1 - c) = m - 1" using cm by linarith
    finally show ?thesis by simp
  qed
  have tailseg_TPS: "seg S c (Lng S - 1) \<in> T_PS"
  proof -
    have tlen: "length (seg S c (Lng S - 1)) = Suc (Lng S - 1) - c" by simp
    have "seg S c (Lng S - 1) \<noteq> []"
    proof
      assume "seg S c (Lng S - 1) = []"
      hence "length (seg S c (Lng S - 1)) = 0" by simp
      thus False using tlen cle by linarith
    qed
    thus ?thesis by (auto simp: T_PS_def seg_def)
  qed
  have mc_lt: "m - 1 - c < Lng (seg S c (Lng S - 1))"
  proof -
    have "Lng (seg S c (Lng S - 1)) = Suc (Lng S - 1) - c" by simp
    moreover have "m - 1 - c < Suc (Lng S - 1) - c" using cm mle cle by linarith
    ultimately show ?thesis by simp
  qed
  have tailnmQ: "\<not> multiT (seg ?Q c (Lng ?Q - 1))"
  proof -
    have "\<not> multiT (seg (seg S c (Lng S - 1)) 0 (m - 1 - c))"
      by (rule notmulti_seg_prefix[OF tailseg_TPS tailnm mc_lt])
    thus ?thesis using segQtail segS_tail_eq by simp
  qed
  \<comment> \<open>apply the SAME anchor split to \<open>Q\<close>\<close>
  have splitQ: "P ?Q = P (seg ?Q 0 (c - 1)) @ [seg ?Q c (Lng ?Q - 1)]"
    by (rule oper_d1pos_notbrle_P_split[OF QT c0 cleQ lminQ tailnmQ])
  have segQ0: "seg ?Q 0 (c - 1) = seg S 0 (c - 1)"
  proof -
    have "seg ?Q 0 (c - 1) = seg S (0 + 0) (0 + (c - 1))"
      by (rule seg_of_seg) (use cm in linarith)+
    thus ?thesis by simp
  qed
  have "butlast (P ?Q) = P (seg ?Q 0 (c - 1))" using splitQ by simp
  also have "\<dots> = P (seg S 0 (c - 1))" using segQ0 by simp
  also have "\<dots> = butlast (P S)" using butS by simp
  finally show ?thesis .
qed

text \<open>§6.8 d1pos \<open>\<not>brle\<close> REGIME A lowshift (conc-A, \<open>j'\<^sub>0 < j\<^sub>m\<^sub>2\<close>, \<open>shamt = 0\<close>).
  Companion to @{thm [source] oper_d1pos_branch_lowshift_regB}: in regime A the
  block index \<open>q\<^sub>0 = 0\<close> so \<open>shamt = 0\<close> and \<open>j\<^sub>0\<^sup>red = j'\<^sub>0\<close>, and (via the regime-A
  TrEq) the \<open>M\<close>-side branch region \<open>S = seg (N[n]) A E\<close> and the \<open>N\<close>-side region
  \<open>Snside = seg N A E\<^sub>N\<close> START AT THE SAME index \<open>A = A\<^sub>N\<close>.  When the \<open>S\<close>-anchor
  prefix \<open>[A, A+c-1]\<close> stays STRICTLY below the boundary \<open>Lng N-1\<close> (\<open>Abnd\<close>) and the
  anchors coincide (\<open>ccN\<close>: \<open>c = cN\<close>, the deep-verified regime-A realisation —
  267/267, /tmp/regA_butl.py), the LOW prefix is read off \<open>N\<close> verbatim on both
  operands, so both reduce to \<open>seg N A (A+c-1)\<close> and the \<open>(IncrFirst^^0)\<close>-shift is the
  identity.  DEEP-VERIFIED rank 8 (267/267 regime-A cases, the EXACT anchor
  \<open>c = IdxSum (P S) ! (length (P S)-1)\<close>; /tmp/lowshift_exact_verify.py).
  The realisation hyps (\<open>AeqAN\<close>, \<open>ccN\<close>, \<open>Abnd\<close>) are the regime-A counterparts of
  @{thm [source] oper_d1pos_branch_lowshift_regB}'s block hypotheses
  (\<open>Aform\<close>/\<open>e0lt\<close>/\<open>qn\<close>), all three 267/267 at rank 8.\<close>

lemma oper_d1pos_branch_lowshift_regA:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and n1: "1 \<le> n"
    and AeqAN: "A = AN"
    and ccN: "cc = cN"
    and Abnd: "A + (cc - 1) < Lng N - 1"
    and Ele: "A \<le> E" and ccle: "cc - 1 \<le> E - A"
    and ANle: "AN \<le> EN" and cNle: "cN - 1 \<le> EN - AN"
  shows "seg (seg ((N::pairseq)[n]) A E) 0 (cc - 1)
       = (IncrFirst ^^ (0::nat)) (seg (seg N AN EN) 0 (cN - 1))"
proof -
  \<comment> \<open>reshape both LOW prefixes to the ambient \<open>[A,A+c-1]\<close> / \<open>[AN,AN+cN-1]\<close> windows\<close>
  have reM: "seg (seg ((N::pairseq)[n]) A E) 0 (cc - 1) = seg ((N::pairseq)[n]) A (A + (cc - 1))"
    using seg_of_seg[OF Ele ccle] by simp
  have reN: "seg (seg N AN EN) 0 (cN - 1) = seg N AN (AN + (cN - 1))"
    using seg_of_seg[OF ANle cNle] by simp
  \<comment> \<open>the \<open>M\<close>-side window reads \<open>N\<close> verbatim (endpoint below the boundary)\<close>
  have bnd: "A + (cc - 1) < Lng N - 1" using Abnd .
  have verb: "seg ((N::pairseq)[n]) A (A + (cc - 1)) = seg N A (A + (cc - 1))"
    by (rule oper_d1pos_seg_low_verbatim[OF L notzero hp i1z j0lt n1 bnd])
  \<comment> \<open>align the \<open>N\<close>-side window via \<open>A = AN\<close>, \<open>c = cN\<close>\<close>
  have align: "seg N A (A + (cc - 1)) = seg N AN (AN + (cN - 1))"
    using AeqAN ccN by simp
  have "seg (seg ((N::pairseq)[n]) A E) 0 (cc - 1) = seg N AN (AN + (cN - 1))"
    using reM verb align by simp
  also have "\<dots> = seg (seg N AN EN) 0 (cN - 1)" using reN by simp
  also have "\<dots> = (IncrFirst ^^ (0::nat)) (seg (seg N AN EN) 0 (cN - 1))" by simp
  finally show ?thesis .
qed

text \<open>§6.8 geomA ANCHOR COINCIDENCE (the regime-A \<open>c = cN\<close> / \<open>F8end\<close> / \<open>F9end\<close>
  derivation).  In regime A the \<open>M\<close>-side branch region \<open>S = seg (N[n]) A E\<close>
  (\<open>E = j'\<^sub>1 \<ge> Lng N-1\<close>) and the \<open>N\<close>-side region
  \<open>Snside = seg N A (Lng N-1)\<close> START AT THE SAME index \<open>A\<close> (via the regime-A TrEq,
  @{thm [source] TrMax_seg_oper_d1pos_eq_regA}, \<open>A = AN\<close>) and AGREE VERBATIM on the
  common window \<open>[A, Lng N-2]\<close> (the \<open>N[n]\<close>-extension reads \<open>N\<close> off verbatim strictly
  below the boundary, @{thm [source] oper_d1pos_seg_low_verbatim}); they differ only
  at \<open>Snside\<close>'s last index.  Writing \<open>m = Lng Snside - 1 = Lng N - 1 - A\<close> the common
  prefix is \<open>Q = seg S 0 (m-1) = seg Snside 0 (m-1)\<close>.  By the P-prefix anchor
  stability lemma @{thm [source] P_butlast_take_at_anchor} applied to BOTH operands
  (each anchor lies strictly below the differing index, \<open>c < m\<close> / \<open>cN < m\<close>, the
  267/267 regime-A realisation — \<open>len(last(P S)) \<ge> 2\<close> / \<open>len(last(P Snside)) \<ge> 2\<close>,
  /tmp/geomA_lastlen.py):
    \<open>butlast (P S) = butlast (P Q) = butlast (P Snside)\<close>,
  hence the LAST \<open>IdxSum\<close> values coincide (\<open>c = sum_list (map length (butlast (P S)))
  = cN\<close>): \<open>c = cN\<close>.  Then \<open>shamt = 0\<close>, and since the anchor cut sits in the verbatim
  window (\<open>c < m\<close>, \<open>A + c < Lng N - 1\<close>) the row-0/row-1 entries at the cut coincide:
    \<open>F8end : entry S 0 c = entry Snside 0 cN  (= + shamt, shamt = 0)\<close>,
    \<open>F9end : entry S 1 c = entry Snside 1 cN  (\<le>)\<close>.
  DEEP-VERIFIED rank 8 (/tmp/geomA_verify.py): \<open>c = cN\<close>, \<open>F8end\<close>, \<open>F9end\<close> all
  267/267, with \<open>A + c < Lng N-1\<close> and \<open>A + (c-1) < Lng N-1\<close> 267/267.  The bounds
  \<open>c < m\<close>, \<open>cN < m\<close> are the regime-A residual block-fold realisation (the last
  \<open>P\<close>-component spans the whole extended tail, length \<open>\<ge> 2\<close>); everything else is
  derived from the std \<open>d1pos\<close> context.\<close>

lemma oper_d1pos_anchor_coincide_regA:
  fixes N :: pairseq and A E n :: nat
  defines "S \<equiv> seg ((N::pairseq)[n]) A E"
      and "Snside \<equiv> seg N A (Lng N - 1)"
  defines "c \<equiv> IdxSum (P S) ! (length (P S) - 1)"
      and "cN \<equiv> IdxSum (P Snside) ! (length (P Snside) - 1)"
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and n1: "1 \<le> n"
    and Abnd: "A < Lng N - 1"
    and Ele: "Lng N - 1 \<le> E"
    and multi: "1 < length (P S)"
    and multiN: "1 < length (P Snside)"
    and clt: "c < Lng Snside - 1"
    and cNlt: "cN < Lng Snside - 1"
  shows "c = cN"
    and "entry S 0 c = entry Snside 0 cN"
    and "entry S 1 c \<le> entry Snside 1 cN"
proof -
  let ?m = "Lng Snside - 1"
  \<comment> \<open>\<open>S \<in> T_PS\<close>, \<open>Snside \<in> T_PS\<close>\<close>
  have Sne: "S \<noteq> []"
  proof
    assume "S = []"
    hence "P S = [[]]" by (subst P.simps) (simp add: multiT_def zeroT_def monoT_def)
    thus False using multi by simp
  qed
  have ST: "S \<in> T_PS" using Sne unfolding S_def by (auto simp: T_PS_def seg_def)
  have Snne: "Snside \<noteq> []"
  proof
    assume "Snside = []"
    hence "P Snside = [[]]" by (subst P.simps) (simp add: multiT_def zeroT_def monoT_def)
    thus False using multiN by simp
  qed
  have SnT: "Snside \<in> T_PS" using Snne unfolding Snside_def by (auto simp: T_PS_def seg_def)
  \<comment> \<open>geometry of \<open>m\<close>: \<open>Lng Snside = Lng N - A\<close>, so \<open>m = Lng N - 1 - A\<close>, \<open>A + (m-1) = Lng N - 2\<close>\<close>
  have LngSn: "Lng Snside = Suc (Lng N - 1) - A" unfolding Snside_def by simp
  have mpos: "0 < ?m" using cNlt by linarith
  have mval: "?m = Lng N - 1 - A" using LngSn Abnd by linarith
  \<comment> \<open>freeze \<open>e = m-1\<close> so \<open>Lng_seg\<close> cannot re-expand the endpoint mid-reshape\<close>
  obtain e where edef: "e = ?m - 1" by blast
  have AmB: "A + e < Lng N - 1" using edef mval Abnd mpos by linarith
  \<comment> \<open>verbatim common prefix \<open>Q = seg S 0 e = seg Snside 0 e\<close>\<close>
  have ELng: "A \<le> E" using Ele Abnd by linarith
  have mleE: "e \<le> E - A" using edef mval Ele Abnd by linarith
  have reS: "seg S 0 e = seg ((N::pairseq)[n]) A (A + e)"
    unfolding S_def using seg_of_seg[OF ELng mleE] by simp
  have mleN: "e \<le> (Lng N - 1) - A" using edef mval Abnd mpos by linarith
  have ALeN: "A \<le> Lng N - 1" using Abnd by linarith
  have reSn: "seg Snside 0 e = seg N A (A + e)"
    unfolding Snside_def using seg_of_seg[OF ALeN mleN] by simp
  have verb: "seg ((N::pairseq)[n]) A (A + e) = seg N A (A + e)"
    by (rule oper_d1pos_seg_low_verbatim[OF L notzero hp i1z j0lt n1 AmB])
  have Qeq: "seg S 0 e = seg Snside 0 e"
    using reS reSn verb by simp
  \<comment> \<open>P-prefix anchor stability on both operands (anchors strictly below \<open>m\<close>)\<close>
  have mleS: "?m \<le> Lng S"
  proof -
    have "Lng S = Suc E - A" unfolding S_def by simp
    moreover have "?m \<le> Suc E - A" using mval Ele Abnd by linarith
    ultimately show ?thesis by simp
  qed
  have mleSn: "?m \<le> Lng Snside" by linarith
  have cltS: "IdxSum (P S) ! (length (P S) - 1) < ?m" using clt unfolding c_def by simp
  have cltSn: "IdxSum (P Snside) ! (length (P Snside) - 1) < ?m" using cNlt unfolding cN_def by simp
  have butS: "butlast (P (seg S 0 e)) = butlast (P S)"
    using P_butlast_take_at_anchor[OF ST multi cltS mleS] edef by simp
  have butSn: "butlast (P (seg Snside 0 e)) = butlast (P Snside)"
    using P_butlast_take_at_anchor[OF SnT multiN cltSn mleSn] edef by simp
  have butEq: "butlast (P S) = butlast (P Snside)"
    using butS butSn Qeq by simp
  \<comment> \<open>\<open>c = cN\<close>: the last \<open>IdxSum\<close> value is the total length of \<open>butlast (P \<cdot>)\<close>\<close>
  have neS: "P S \<noteq> []" by (rule P_nonempty)
  have neSn: "P Snside \<noteq> []" by (rule P_nonempty)
  have cbutl: "c = sum_list (map length (butlast (P S)))"
  proof -
    have "c = IdxSum (P S) ! (length (P S) - 1)" unfolding c_def ..
    also have "\<dots> = sum_list (map length (take (length (P S) - 1) (P S)))"
      by (simp add: idxsum_nth)
    also have "take (length (P S) - 1) (P S) = butlast (P S)"
      by (simp add: butlast_conv_take)
    finally show ?thesis .
  qed
  have cNbutl: "cN = sum_list (map length (butlast (P Snside)))"
  proof -
    have "cN = IdxSum (P Snside) ! (length (P Snside) - 1)" unfolding cN_def ..
    also have "\<dots> = sum_list (map length (take (length (P Snside) - 1) (P Snside)))"
      by (simp add: idxsum_nth)
    also have "take (length (P Snside) - 1) (P Snside) = butlast (P Snside)"
      by (simp add: butlast_conv_take)
    finally show ?thesis .
  qed
  show ceq: "c = cN" using cbutl cNbutl butEq by simp
  \<comment> \<open>the anchor cut lies in the verbatim window: \<open>entry\<close> agreement at \<open>c = cN\<close>\<close>
  have ccm: "c \<le> e" using clt edef by linarith
  have eqQc0: "entry (seg S 0 e) 0 c = entry (seg Snside 0 e) 0 c"
    using Qeq by simp
  have eqQc1: "entry (seg S 0 e) 1 c = entry (seg Snside 0 e) 1 c"
    using Qeq by simp
  have cltLng: "c < Lng (seg S 0 e)" using ccm by simp
  have cltLngN: "c < Lng (seg Snside 0 e)" using ccm by simp
  have lhs0: "entry (seg S 0 e) 0 c = entry S 0 c"
    using entry_seg[OF cltLng] by simp
  have lhs1: "entry (seg S 0 e) 1 c = entry S 1 c"
    using entry_seg[OF cltLng] by simp
  have rhs0: "entry (seg Snside 0 e) 0 c = entry Snside 0 c"
    using entry_seg[OF cltLngN] by simp
  have rhs1: "entry (seg Snside 0 e) 1 c = entry Snside 1 c"
    using entry_seg[OF cltLngN] by simp
  have e0: "entry S 0 c = entry Snside 0 c" using eqQc0 lhs0 rhs0 by simp
  have e1: "entry S 1 c = entry Snside 1 c" using eqQc1 lhs1 rhs1 by simp
  show "entry S 0 c = entry Snside 0 cN" using e0 ceq by simp
  show "entry S 1 c \<le> entry Snside 1 cN" using e1 ceq by simp
qed

text \<open>§6.8 geomA BLOCKER (regA-close, rank-10 finding).  The \<open>clt\<close>/\<open>cNlt\<close>
  hypotheses of @{thm [source] oper_d1pos_anchor_coincide_regA} (the last
  \<open>P\<close>-component of \<open>S\<close>/\<open>Snside\<close> has length \<open>\<ge> 2\<close>, i.e. \<open>c < m\<close> / \<open>cN < m\<close>) are NOT
  universal: they hold only 3273/3792 at rank 10 (KMAX=10 len 14 val 5,
  /tmp/regA_clt_hi.py).  In the 519 \<open>A > jm2\<close> (flat row-0) cases the last component
  is a SINGLETON and \<open>c = cN = m\<close> (CONCRETE counterexample
  \<open>N=(0,0)(1,1)(2,2)(2,2)(2,2)\<close>, \<open>n=2\<close>, \<open>j'\<^sub>0=0\<close>, \<open>j'\<^sub>1=5\<close>: \<open>Snside=(2,2)(2,2)\<close>,
  \<open>P Snside=[[(2,2)],[(2,2)]]\<close>, \<open>cN=1=m\<close>).  HOWEVER the CONCLUSIONS \<open>c=cN\<close>,
  \<open>entry S 0 c = entry Snside 0 cN\<close> (F8end), \<open>entry S 1 c \<le> entry Snside 1 cN\<close>
  (F9end) ALL hold 3792/3792 UNIVERSALLY (/tmp/regA_ceqcn.py), together with
  \<open>butlast (P S) = butlast (P Snside)\<close>, \<open>entry S 0 m = entry Snside 0 m\<close>,
  \<open>entry S 1 m \<le> entry Snside 1 m\<close>, \<open>len (P S) = len (P Snside)\<close>, and the UNIFORM
  bound \<open>c \<le> m\<close> / \<open>cN \<le> m\<close> (/tmp/regA_boundary.py, /tmp/regA_cle_m.py).
  So @{thm [source] oper_d1pos_anchor_coincide_regA} is OVER-CONDITIONED: it should
  be reproved WITHOUT \<open>clt\<close>/\<open>cNlt\<close>, splitting on \<open>c<m\<close> (current truncate-at-\<open>m-1\<close>
  route) vs \<open>c=m\<close> (singleton-tail boundary).  The MISSING BRICK for the universal
  \<open>c \<le> m\<close> is \<open>no row-0 left-min of S strictly above its boundary index m\<close> (the
  periodic-tail-above-boundary lower bound, the same §6.8 block-fold residual);
  given it, the \<open>anchor_lt_of_uniform_witness\<close> bridge (below) closes \<open>c \<le> m\<close>
  directly.\<close>

text \<open>§6.8 geomA — the ANCHOR-BELOW-\<open>k\<close> bridge (\<open>clt\<close>/\<open>cNlt\<close> from a UNIFORM
  row-0 witness).  PURELY STRUCTURAL: the last \<open>FirstNodes\<close> anchor
  \<open>c = IdxSum (P S) ! (length (P S) - 1)\<close> is a row-0 left-minimum
  (@{thm [source] oper_d1pos_branch_anchor}(3)).  If there is ONE earlier index
  \<open>jj < k\<close> whose row-0 value strictly UNDERCUTS every tail index \<open>x \<in> [k, Lng S-1]\<close>
  (\<open>wit : \<And>x. k \<le> x \<Longrightarrow> x \<le> Lng S-1 \<Longrightarrow> entry S 0 jj < entry S 0 x\<close>), then NO tail
  index is a left-minimum, so the anchor sits strictly below \<open>k\<close>: \<open>c < k\<close>.  (Proof:
  if \<open>c \<ge> k\<close> then \<open>jj < k \<le> c\<close> so the left-min property gives \<open>entry S 0 c \<le> entry
  S 0 jj\<close>, contradicting \<open>wit\<close> at \<open>x = c\<close>.)  This discharges BOTH \<open>clt\<close> (\<open>k = m\<close>,
  \<open>S\<close>) and \<open>cNlt\<close> (\<open>k = m\<close>, \<open>Snside\<close>) of @{thm [source] oper_d1pos_anchor_coincide_regA}
  once the uniform witness is supplied.\<close>

lemma anchor_lt_of_uniform_witness:
  fixes S :: pairseq
  defines "c \<equiv> IdxSum (P S) ! (length (P S) - 1)"
  assumes ST: "S \<in> T_PS" and multi: "1 < length (P S)"
    and jjlt: "jj < k"
    and wit: "\<And>x. k \<le> x \<Longrightarrow> x \<le> Lng S - 1 \<Longrightarrow> entry S 0 jj < entry S 0 x"
  shows "c < k"
proof (rule ccontr)
  assume "\<not> c < k"
  hence kc: "k \<le> c" by simp
  have cle: "c \<le> Lng S - 1" unfolding c_def
    by (rule oper_d1pos_branch_anchor(2)[OF ST multi])
  have lmin: "\<And>j. j < c \<Longrightarrow> entry S 0 c \<le> entry S 0 j" unfolding c_def
    using oper_d1pos_branch_anchor(3)[OF ST multi] by blast
  \<comment> \<open>\<open>jj < k \<le> c\<close>, so the anchor's left-min property applies at \<open>jj\<close>\<close>
  have jjc: "jj < c" using jjlt kc by linarith
  have a: "entry S 0 c \<le> entry S 0 jj" by (rule lmin[OF jjc])
  \<comment> \<open>but \<open>c\<close> is itself a tail index (\<open>k \<le> c \<le> Lng S - 1\<close>), so \<open>wit\<close> undercuts it\<close>
  have b: "entry S 0 jj < entry S 0 c" by (rule wit[OF kc cle])
  show False using a b by linarith
qed

text \<open>§6.8 geomA — \<open>cNlt\<close> from \<open>A \<le> jm2\<close> (the \<open>N\<close>-side, verbatim).  For
  \<open>Snside = seg N A (Lng N-1)\<close> the last index \<open>m = Lng Snside-1\<close> reads N's last
  index (\<open>entry Snside 0 m = entry N 0 (Lng N-1)\<close>) and the witness \<open>jj = jm2-A\<close>
  reads \<open>entry N 0 jm2\<close> (verbatim, \<open>jm2 < Lng N-1\<close>); with \<open>\<delta> = entry N 0 (Lng N-1)
  - entry N 0 jm2 > 0\<close> the strict undercut holds, and since \<open>m\<close> is the ONLY tail
  index of \<open>Snside\<close> the uniform-witness bridge gives \<open>cN < m\<close>.  The supplied
  hypothesis \<open>Ajm2 : A \<le> jm2\<close> covers only the SUB-regime where the slice start
  sits at/below the period base: it is NOT universal — at rank 10 (KMAX=10 len 14
  val 5) \<open>A \<le> jm2\<close> holds only 3273/3792, and in the other 519 (\<open>A > jm2\<close>, flat
  row-0) cases the last \<open>P\<close>-component of \<open>Snside\<close> is a SINGLETON so \<open>cN = m\<close> and
  \<open>cNlt\<close> is FALSE (e.g. \<open>N=(0,0)(1,1)(2,2)(2,2)(2,2)\<close>, \<open>n=2\<close>, \<open>j'\<^sub>0=0\<close>, \<open>j'\<^sub>1=5\<close>:
  \<open>Snside=(2,2)(2,2)\<close>, \<open>P Snside=[[(2,2)],[(2,2)]]\<close>, \<open>cN=1=m\<close>).  See the BLOCKER
  note above @{thm [source] oper_d1pos_anchor_coincide_regA}.  \<open>dpos : entry N 0
  jm2 < entry N 0 (Lng N-1)\<close> is \<open>\<delta>>0\<close>.\<close>

lemma oper_d1pos_cNlt_of_Ajm2:
  fixes N :: pairseq and A :: nat
  defines "Snside \<equiv> seg N A (Lng N - 1)"
  defines "cN \<equiv> IdxSum (P Snside) ! (length (P Snside) - 1)"
  assumes L: "1 < Lng N"
    and Abnd: "A < Lng N - 1"
    and multiN: "1 < length (P Snside)"
    and Ajm2: "A \<le> parent N 1 (Lng N - 1)"
    and jm2lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and dpos: "entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1)"
  shows "cN < Lng Snside - 1"
proof -
  let ?jm2 = "parent N 1 (Lng N - 1)"
  let ?m = "Lng Snside - 1"
  let ?jj = "?jm2 - A"
  have Snne: "Snside \<noteq> []"
  proof
    assume "Snside = []"
    hence "P Snside = [[]]" by (subst P.simps) (simp add: multiT_def zeroT_def monoT_def)
    thus False using multiN by simp
  qed
  have SnT: "Snside \<in> T_PS" using Snne unfolding Snside_def by (auto simp: T_PS_def seg_def)
  \<comment> \<open>geometry: \<open>Lng Snside = Lng N - A\<close>, \<open>m = Lng N - 1 - A\<close>\<close>
  have LngSn: "Lng Snside = Suc (Lng N - 1) - A" unfolding Snside_def by simp
  have mval: "?m = Lng N - 1 - A" using LngSn Abnd by linarith
  have jjlt: "?jj < ?m" using mval Ajm2 jm2lt Abnd by linarith
  \<comment> \<open>freeze \<open>mm = m\<close> and \<open>jj0 = jj\<close> so \<open>entry_seg\<close>'s arithmetic residue can be rewritten\<close>
  obtain mm where mmdef: "mm = ?m" by blast
  obtain jj0 where jj0def: "jj0 = ?jj" by blast
  \<comment> \<open>\<open>m\<close> is the only tail index; \<open>entry Snside 0 m = entry N 0 (Lng N-1)\<close>\<close>
  have mInSn: "A + mm = Lng N - 1" using mval Abnd mmdef by linarith
  have mlt: "mm < Lng Snside" using LngSn Abnd mmdef by linarith
  have eSm: "entry Snside 0 mm = entry N 0 (Lng N - 1)"
  proof -
    have "entry Snside 0 mm = entry N (0::nat) (A + mm)"
      unfolding Snside_def by (rule entry_seg[OF mlt[unfolded Snside_def]])
    thus ?thesis using mInSn by simp
  qed
  \<comment> \<open>witness reads \<open>entry N 0 jm2\<close> verbatim (\<open>jj + A = jm2 < Lng N-1\<close>)\<close>
  have jjInSn: "A + jj0 = ?jm2" using Ajm2 jj0def by simp
  have jjlt2: "jj0 < Lng Snside" using jjlt mlt mmdef jj0def by linarith
  have eSjj: "entry Snside 0 jj0 = entry N 0 ?jm2"
  proof -
    have "entry Snside 0 jj0 = entry N (0::nat) (A + jj0)"
      unfolding Snside_def by (rule entry_seg[OF jjlt2[unfolded Snside_def]])
    thus ?thesis using jjInSn by simp
  qed
  \<comment> \<open>the uniform witness: the ONLY tail index \<open>x \<in> [m, Lng Snside-1]\<close> is \<open>m\<close> itself\<close>
  have jjltmm: "jj0 < mm" using jjlt mmdef jj0def by simp
  have wit: "\<And>x. mm \<le> x \<Longrightarrow> x \<le> Lng Snside - 1 \<Longrightarrow> entry Snside 0 jj0 < entry Snside 0 x"
  proof -
    fix x assume xlo: "mm \<le> x" and xhi: "x \<le> Lng Snside - 1"
    have "x = mm" using xlo xhi mmdef by linarith
    thus "entry Snside 0 jj0 < entry Snside 0 x" using eSjj eSm dpos by simp
  qed
  have "cN < mm" unfolding cN_def
    by (rule anchor_lt_of_uniform_witness[OF SnT multiN jjltmm wit])
  thus "cN < ?m" using mmdef by simp
qed

text \<open>§6.8 geomA — WITHIN-PERIOD row-0 floor.  The period base \<open>j\<^sub>m\<^sub>2 = parent N 1
  (Lng N-1)\<close> carries the row-0 MINIMUM of the closed period window \<open>[j\<^sub>m\<^sub>2, Lng N-1]\<close>:
  \<open>entry N 0 j\<^sub>m\<^sub>2 \<le> entry N 0 (j\<^sub>m\<^sub>2 + s)\<close> for every \<open>s \<le> Lng N-1-j\<^sub>m\<^sub>2\<close>.  The
  slice \<open>seg N j\<^sub>m\<^sub>2 (Lng N-1)\<close> is \<open>monoT\<close> (@{thm [source] m_6_2_mono_ancestor_slice}
  from \<open>leR N 0 j\<^sub>m\<^sub>2 (Lng N-1)\<close>, itself @{thm [source] poper_nextR_imp_le0} on the
  row-1 parent step), so its left end is the row-0 minimum
  (@{thm [source] entry0_ge_min}); transfer back to \<open>N\<close> by @{thm [source] entry_seg}.
  DEEP-VERIFIED rank 10 (1968/1968, /tmp/regA_le0period.py).\<close>

lemma oper_d1pos_period_row0_floor:
  fixes N :: pairseq
  assumes hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and sle: "s \<le> Lng N - 1 - parent N 1 (Lng N - 1)"
  shows "entry N 0 (parent N 1 (Lng N - 1))
       \<le> entry N 0 (parent N 1 (Lng N - 1) + s)"
proof -
  let ?jm2 = "parent N 1 (Lng N - 1)"  let ?j1 = "Lng N - 1"
  have L: "1 < Lng N" using j0lt by linarith
  have NT: "N \<in> T_PS" using L by (cases N) (auto simp: T_PS_def)
  \<comment> \<open>row-1 parent step gives the row-0 reachability \<open>leR N 0 jm2 j1\<close>\<close>
  have hp1: "hasParent N 1 ?j1" using hp i1z by simp
  have parR: "nextR N 1 ?jm2 ?j1"
    using hp1 unfolding hasParent_def parent_def by (rule theI')
  have le0: "leR N 0 ?jm2 ?j1" using poper_nextR_imp_le0[OF parR] by simp
  \<comment> \<open>the period slice is \<open>monoT\<close>; its left end is the row-0 minimum\<close>
  have mono: "monoT (seg N ?jm2 ?j1)"
    by (rule m_6_2_mono_ancestor_slice[OF NT j0lt le0])
  have segT: "seg N ?jm2 ?j1 \<in> T_PS" using j0lt by (auto simp: T_PS_def seg_def)
  have slt: "s < Lng (seg N ?jm2 ?j1)" using sle j0lt by simp
  have z0: "0 < Lng (seg N ?jm2 ?j1)" using j0lt by simp
  have min: "entry (seg N ?jm2 ?j1) 0 0 \<le> entry (seg N ?jm2 ?j1) 0 s"
    by (rule entry0_ge_min[OF segT mono slt])
  \<comment> \<open>transfer both endpoints back to \<open>N\<close>\<close>
  have e0: "entry (seg N ?jm2 ?j1) 0 0 = entry N 0 ?jm2"
    using entry_seg[OF z0] by simp
  have es: "entry (seg N ?jm2 ?j1) 0 s = entry N 0 (?jm2 + s)"
    using entry_seg[OF slt] by simp
  show ?thesis using min e0 es by simp
qed

text \<open>§6.8 geomB — STRICT within-period row-0 floor.  Sharpens
  @{thm [source] oper_d1pos_period_row0_floor} from \<open>\<le>\<close> to \<open><\<close> for a NON-trivial
  offset (\<open>0 < s \<le> w = Lng N-1-j\<^sub>m\<^sub>2\<close>): the period base \<open>j\<^sub>m\<^sub>2\<close> carries the STRICT
  row-0 minimum of the closed period window.  The period slice
  \<open>seg N j\<^sub>m\<^sub>2 (Lng N-1)\<close> is \<open>monoT\<close> (same derivation as the \<open>\<le>\<close> floor), so it is
  NOT \<open>multiT\<close>; @{thm [source] m_6_2_multi_crit_23} (the \<open>(2)=(3)\<close> multi-criterion,
  forward direction from \<open>leR \<cdot> 0 0 (Lng-1)\<close>, which is the \<open>monoT\<close> conjunct) then
  gives the STRICT increase \<open>entry (seg ..) 0 0 < entry (seg ..) 0 s\<close> for every
  \<open>0 < s < Lng (seg ..) = w+1\<close>; transfer both endpoints to \<open>N\<close> by
  @{thm [source] entry_seg}.  This is the missing brick the REGIME-B \<open>clt\<close> witness
  needs to undercut SAME-block tail positions (where the \<open>\<le>\<close> floor is too weak).
  DEEP-VERIFIED rank 10 (515/515 d1pos \<open>N\<close>, /tmp/regB_strictfloor.py).\<close>

lemma oper_d1pos_strict_period_floor:
  fixes N :: pairseq
  assumes hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and s0: "0 < s"
    and sle: "s \<le> Lng N - 1 - parent N 1 (Lng N - 1)"
  shows "entry N 0 (parent N 1 (Lng N - 1))
       < entry N 0 (parent N 1 (Lng N - 1) + s)"
proof -
  let ?jm2 = "parent N 1 (Lng N - 1)"  let ?j1 = "Lng N - 1"
  have L: "1 < Lng N" using j0lt by linarith
  have NT: "N \<in> T_PS" using L by (cases N) (auto simp: T_PS_def)
  \<comment> \<open>row-1 parent step gives the row-0 reachability \<open>leR N 0 jm2 j1\<close>\<close>
  have hp1: "hasParent N 1 ?j1" using hp i1z by simp
  have parR: "nextR N 1 ?jm2 ?j1"
    using hp1 unfolding hasParent_def parent_def by (rule theI')
  have le0: "leR N 0 ?jm2 ?j1" using poper_nextR_imp_le0[OF parR] by simp
  \<comment> \<open>the period slice is \<open>monoT\<close>, hence carries the strict row-0 minimum at its left end\<close>
  have mono: "monoT (seg N ?jm2 ?j1)"
    by (rule m_6_2_mono_ancestor_slice[OF NT j0lt le0])
  have segT: "seg N ?jm2 ?j1 \<in> T_PS" using j0lt by (auto simp: T_PS_def seg_def)
  have leR0: "leR (seg N ?jm2 ?j1) 0 0 (Lng (seg N ?jm2 ?j1) - 1)"
    using mono by (simp add: monoT_def)
  \<comment> \<open>strict row-0 increase for any non-trivial index (multi-criterion (2)=(3))\<close>
  have slt: "s < Lng (seg N ?jm2 ?j1)" using sle j0lt by simp
  have strictseg: "entry (seg N ?jm2 ?j1) 0 0 < entry (seg N ?jm2 ?j1) 0 s"
    using m_6_2_multi_crit_23[OF segT] leR0 s0 slt by blast
  \<comment> \<open>transfer both endpoints to \<open>N\<close>\<close>
  have z0: "0 < Lng (seg N ?jm2 ?j1)" using j0lt by simp
  have e0: "entry (seg N ?jm2 ?j1) 0 0 = entry N 0 ?jm2"
    using entry_seg[OF z0] by simp
  have es: "entry (seg N ?jm2 ?j1) 0 s = entry N 0 (?jm2 + s)"
    using entry_seg[OF slt] by simp
  show ?thesis using strictseg e0 es by simp
qed

text \<open>§6.8 geomA — the REGIME-A \<open>clt\<close> brick (\<open>c < m\<close>, replacing the non-universal
  hypothesis of @{thm [source] oper_d1pos_anchor_coincide_regA}).  For
  \<open>S = seg (N[n]) A E\<close> with \<open>A < j\<^sub>m\<^sub>2\<close> (regime A), the last \<open>FirstNodes\<close> anchor
  \<open>c = IdxSum (P S) ! (len-1)\<close> sits STRICTLY below the boundary index
  \<open>m = Lng (seg N A (Lng N-1)) - 1 = Lng N-1-A\<close>.  WITNESS \<open>jj = j\<^sub>m\<^sub>2 - A < m\<close>:
  \<open>entry S 0 jj = entry N 0 j\<^sub>m\<^sub>2\<close> (verbatim prefix, block 0), while every tail index
  \<open>x \<in> [m, Lng S-1]\<close> reads a HIGHER block (\<open>A+x \<ge> Lng N-1 = j\<^sub>m\<^sub>2 + w\<close>, so block
  \<open>q = (A+x-j\<^sub>m\<^sub>2) div w \<ge> 1\<close>): \<open>entry S 0 x = entry N 0 (j\<^sub>m\<^sub>2+s) + q\<cdot>\<delta>\<close>
  (@{thm [source] oper_d1pos_entry0}) \<open>\<ge> entry N 0 j\<^sub>m\<^sub>2 + \<delta> > entry N 0 j\<^sub>m\<^sub>2\<close>, using
  the within-period floor (@{thm [source] oper_d1pos_period_row0_floor}) and
  \<open>\<delta> > 0\<close>.  The uniform-witness bridge (@{thm [source] anchor_lt_of_uniform_witness},
  \<open>k = m\<close>) then gives \<open>c < m\<close>.  DEEP-VERIFIED rank 10 (3273/3273 regime-A cases,
  /tmp/regA_kwit.py); \<open>c = m\<close> NEVER occurs in regime A (0/3273, /tmp/regA_cNlt_regA.py).\<close>

lemma oper_d1pos_clt_regA:
  fixes N :: pairseq and A E n :: nat
  defines "S \<equiv> seg ((N::pairseq)[n]) A E"
  defines "c \<equiv> IdxSum (P S) ! (length (P S) - 1)"
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and n1: "1 \<le> n"
    and Abnd: "A < parent N 1 (Lng N - 1)"
    and Ele: "Lng N - 1 \<le> E"
    and Eub: "E < Lng ((N::pairseq)[n])"
    and dpos: "entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1)"
    and multi: "1 < length (P S)"
  shows "c < Lng (seg N A (Lng N - 1)) - 1"
proof -
  let ?jm2 = "parent N 1 (Lng N - 1)"  let ?j1 = "Lng N - 1"  let ?w = "?j1 - ?jm2"
  let ?delta = "entry N 0 ?j1 - entry N 0 ?jm2"
  let ?m = "Lng (seg N A ?j1) - 1"
  let ?jj = "?jm2 - A"
  \<comment> \<open>geometry\<close>
  have AltN: "A < ?j1" using Abnd j0lt by linarith
  have mval: "?m = ?j1 - A" using AltN by simp
  have w0: "0 < ?w" using j0lt by linarith
  obtain w where wdef: "?w = w" by blast
  have w0': "0 < w" using w0 wdef by simp
  have lenMn: "Lng ((N::pairseq)[n]) = ?jm2 + n * w"
    using oper_d1pos_LngM[OF L notzero hp i1z j0lt] wdef by simp
  \<comment> \<open>\<open>S \<in> T_PS\<close>\<close>
  have Sne: "S \<noteq> []"
  proof
    assume "S = []"
    hence "P S = [[]]" by (subst P.simps) (simp add: multiT_def zeroT_def monoT_def)
    thus False using multi by simp
  qed
  have ST: "S \<in> T_PS" using Sne unfolding S_def by (auto simp: T_PS_def seg_def)
  \<comment> \<open>\<open>Lng S = Suc E - A\<close>; so a tail index \<open>x \<le> Lng S - 1\<close> has \<open>A + x \<le> E\<close>\<close>
  have LngS: "Lng S = Suc E - A" unfolding S_def by simp
  \<comment> \<open>witness offset \<open>jj = jm2 - A < m\<close>\<close>
  have jjlt: "?jj < ?m" using mval Abnd j0lt by linarith
  \<comment> \<open>\<open>entry S 0 jj = entry N 0 jm2\<close> (verbatim prefix, \<open>A + jj = jm2 < j1\<close>)\<close>
  have jjInS: "A + ?jj = ?jm2" using Abnd by simp
  have jjltS: "?jj < Lng S" using jjlt mval LngS Ele Abnd j0lt by linarith
  have nzero: "0 < n" using n1 by simp
  have eSjj: "entry S 0 ?jj = entry N 0 ?jm2"
  proof -
    \<comment> \<open>\<open>jm2\<close> is the block-0 start (\<open>q = 0\<close>, offset \<open>s = 0\<close>)\<close>
    have blk0: "entry ((N::pairseq)[n]) 0 (?jm2 + 0 * ?w + 0)
              = entry N 0 (?jm2 + 0) + 0 * ?delta"
      by (rule oper_d1pos_entry0[OF L notzero hp i1z j0lt nzero]) (use w0 in simp)
    have "entry S 0 ?jj = entry ((N::pairseq)[n]) 0 (A + ?jj)"
      unfolding S_def by (rule entry_seg[OF jjltS[unfolded S_def]])
    also have "\<dots> = entry ((N::pairseq)[n]) 0 ?jm2" using jjInS by simp
    also have "\<dots> = entry N 0 ?jm2" using blk0 by simp
    finally show ?thesis .
  qed
  \<comment> \<open>the uniform witness: every tail index \<open>x \<in> [m, Lng S-1]\<close> is strictly above \<open>jj\<close>\<close>
  have wit: "\<And>x. ?m \<le> x \<Longrightarrow> x \<le> Lng S - 1 \<Longrightarrow> entry S 0 ?jj < entry S 0 x"
  proof -
    fix x assume xlo: "?m \<le> x" and xhi: "x \<le> Lng S - 1"
    \<comment> \<open>the N[n]-index \<open>A + x\<close> lies in block \<open>q \<ge> 1\<close> of the period\<close>
    have AxlN: "?j1 \<le> A + x" using xlo mval by linarith
    have AxleE: "A + x \<le> E" using xhi LngS Ele AltN by linarith
    let ?q = "(A + x - ?jm2) div w"  let ?s = "(A + x - ?jm2) mod w"
    have sw: "?s < w" using w0' by simp
    have dm: "?q * w + ?s = A + x - ?jm2"
      using div_mult_mod_eq[of "A + x - ?jm2" w] by (simp add: mult.commute)
    have Axge: "?jm2 \<le> A + x" using AxlN j0lt by linarith
    have xsplit: "A + x = ?jm2 + ?q * w + ?s" using dm Axge by linarith
    \<comment> \<open>\<open>q \<ge> 1\<close> since \<open>A + x \<ge> j1 = jm2 + w\<close>\<close>
    have jm2w: "?jm2 + w = ?j1" using wdef j0lt by linarith
    have q1: "1 \<le> ?q"
    proof -
      have "?jm2 + w \<le> A + x" using AxlN jm2w by simp
      hence "w \<le> A + x - ?jm2" using Axge by linarith
      thus ?thesis using w0' by (simp add: div_greater_zero_iff Suc_leI)
    qed
    \<comment> \<open>\<open>q < n\<close> since \<open>A + x \<le> E < Lng (N[n]) = jm2 + n*w\<close>\<close>
    have qn: "?q < n"
    proof -
      have "A + x - ?jm2 < n * w" using AxleE Eub lenMn Axge by linarith
      thus ?thesis by (rule less_mult_imp_div_less)
    qed
    \<comment> \<open>read \<open>entry S 0 x = entry (N[n]) 0 (A+x)\<close> then decode via the block formula\<close>
    have xltS: "x < Lng S" using xhi LngS Ele AltN by linarith
    have eSx: "entry S 0 x = entry ((N::pairseq)[n]) 0 (A + x)"
      unfolding S_def by (rule entry_seg[OF xltS[unfolded S_def]])
    have sw': "?s < ?j1 - ?jm2" using sw wdef by simp
    have block: "entry ((N::pairseq)[n]) 0 (?jm2 + ?q * ?w + ?s)
               = entry N 0 (?jm2 + ?s) + ?q * ?delta"
      by (rule oper_d1pos_entry0[OF L notzero hp i1z j0lt qn sw'])
    have xsplit': "A + x = ?jm2 + ?q * ?w + ?s" using xsplit wdef by simp
    have eSx2: "entry S 0 x = entry N 0 (?jm2 + ?s) + ?q * ?delta"
      using eSx xsplit' block by simp
    \<comment> \<open>within-period floor: \<open>entry N 0 (jm2+s) \<ge> entry N 0 jm2\<close>\<close>
    have floor: "entry N 0 ?jm2 \<le> entry N 0 (?jm2 + ?s)"
      by (rule oper_d1pos_period_row0_floor[OF hp i1z j0lt]) (use sw' in simp)
    \<comment> \<open>\<open>q\<cdot>\<delta> \<ge> \<delta> > 0\<close>\<close>
    have dpos': "0 < ?delta" using dpos by simp
    have qd: "?delta \<le> ?q * ?delta" using q1 by (simp add: mult_le_mono1)
    \<comment> \<open>assemble: \<open>entry S 0 x \<ge> entry N 0 jm2 + delta > entry N 0 jm2 = entry S 0 jj\<close>\<close>
    have "entry S 0 ?jj = entry N 0 ?jm2" using eSjj .
    also have "\<dots> < entry N 0 ?jm2 + ?delta" using dpos' by simp
    also have "\<dots> \<le> entry N 0 (?jm2 + ?s) + ?q * ?delta" using floor qd by linarith
    also have "\<dots> = entry S 0 x" using eSx2 by simp
    finally show "entry S 0 ?jj < entry S 0 x" .
  qed
  have "IdxSum (P S) ! (length (P S) - 1) < ?m"
    by (rule anchor_lt_of_uniform_witness[OF ST multi jjlt wit])
  thus "c < ?m" unfolding c_def .
qed

text \<open>§6.8 geomB — the REGIME-B \<open>c \<le> m\<close> brick (the regime-A \<open>clt\<close> technique
  transferred to \<open>j\<^sub>m\<^sub>2 \<le> A\<close>).  For \<open>S = seg (N[n]) A E\<close> with \<open>j\<^sub>m\<^sub>2 \<le> A\<close> (regime B)
  the last \<open>FirstNodes\<close> anchor \<open>c = IdxSum (P S) ! (len-1)\<close> sits at or below the
  boundary index \<open>m = Lng (seg N A (Lng N-1)) - 1 = Lng N-1-A\<close>.  Unlike regime A,
  the boundary \<open>c = m\<close> CAN (in fact always does) occur, so this is the NON-strict
  universal bound \<open>c \<le> m\<close>, obtained via @{thm [source] anchor_lt_of_uniform_witness}
  at \<open>k = m+1\<close> (which yields \<open>c < m+1\<close>).  WITNESS \<open>jj = (w - s0) mod w\<close> where
  \<open>s0 = (A-j\<^sub>m\<^sub>2) mod w\<close>: this is the S-offset of the FIRST period FLOOR at/after \<open>A\<close>,
  so \<open>A + jj = j\<^sub>m\<^sub>2 + q\<^sub>j\<^sub>j\<cdot>w\<close> (offset 0) and \<open>entry S 0 jj = entry N 0 j\<^sub>m\<^sub>2 + q\<^sub>j\<^sub>j\<cdot>\<delta>\<close>
  (@{thm [source] oper_d1pos_entry0}).  Every STRICT tail index \<open>x \<in> [m+1, Lng S-1]\<close>
  has \<open>A + x \<ge> Lng N = j\<^sub>m\<^sub>2 + q\<^sub>j\<^sub>j\<cdot>w + (\<dots>)\<close> in block \<open>q\<^sub>x \<ge> q\<^sub>j\<^sub>j\<close> at offset \<open>s\<^sub>x\<close>;
  the undercut \<open>entry N 0 j\<^sub>m\<^sub>2 + q\<^sub>j\<^sub>j\<cdot>\<delta> < entry N 0 (j\<^sub>m\<^sub>2+s\<^sub>x) + q\<^sub>x\<cdot>\<delta>\<close> splits:
  HIGHER block (\<open>q\<^sub>x > q\<^sub>j\<^sub>j\<close>) closes by \<open>q\<^sub>x\<cdot>\<delta> \<ge> q\<^sub>j\<^sub>j\<cdot>\<delta> + \<delta>\<close> and the \<open>\<le>\<close> floor;
  SAME block (\<open>q\<^sub>x = q\<^sub>j\<^sub>j\<close>, then \<open>s\<^sub>x > 0\<close>) closes by the STRICT floor
  @{thm [source] oper_d1pos_strict_period_floor}.  DEEP-VERIFIED rank 10 (519/519
  regime-B cases: \<open>c \<le> m\<close> 519/519, witness undercut 519/519, /tmp/regB_clt.py;
  block-index decode in range 519/519, /tmp/regB_qrange.py).  NB \<open>c = m\<close> holds
  519/519 (\<open>c < m\<close> 0/519): the bound is realised at the boundary.\<close>

lemma oper_d1pos_clt_regB:
  fixes N :: pairseq and A E n :: nat
  defines "S \<equiv> seg ((N::pairseq)[n]) A E"
  defines "c \<equiv> IdxSum (P S) ! (length (P S) - 1)"
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and n1: "1 \<le> n"
    and Ajm2: "parent N 1 (Lng N - 1) \<le> A"
    and AltN: "A < Lng N - 1"
    and Ele: "Lng N - 1 \<le> E"
    and Eub: "E < Lng ((N::pairseq)[n])"
    and dpos: "entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1)"
    and multi: "1 < length (P S)"
  shows "c \<le> Lng (seg N A (Lng N - 1)) - 1"
proof -
  let ?jm2 = "parent N 1 (Lng N - 1)"  let ?j1 = "Lng N - 1"  let ?w = "?j1 - ?jm2"
  let ?delta = "entry N 0 ?j1 - entry N 0 ?jm2"
  let ?m = "Lng (seg N A ?j1) - 1"
  \<comment> \<open>geometry\<close>
  have mval: "?m = ?j1 - A" using AltN by simp
  have w0: "0 < ?w" using j0lt by linarith
  obtain w where wdef: "?w = w" by blast
  have w0': "0 < w" using w0 wdef by simp
  have lenMn: "Lng ((N::pairseq)[n]) = ?jm2 + n * w"
    using oper_d1pos_LngM[OF L notzero hp i1z j0lt] wdef by simp
  \<comment> \<open>\<open>S \<in> T_PS\<close>\<close>
  have Sne: "S \<noteq> []"
  proof
    assume "S = []"
    hence "P S = [[]]" by (subst P.simps) (simp add: multiT_def zeroT_def monoT_def)
    thus False using multi by simp
  qed
  have ST: "S \<in> T_PS" using Sne unfolding S_def by (auto simp: T_PS_def seg_def)
  have LngS: "Lng S = Suc E - A" unfolding S_def by simp
  \<comment> \<open>witness offset: \<open>jj = (w - s0) mod w\<close>, the first floor at/after \<open>A\<close>\<close>
  let ?s0 = "(A - ?jm2) mod w"  let ?q0 = "(A - ?jm2) div w"
  let ?jj = "(w - ?s0) mod w"
  \<comment> \<open>KEY: \<open>jm2 \<le> A < jm2 + w\<close> (\<open>A < Lng N - 1 = jm2 + w\<close>), so \<open>A\<close> is in BLOCK 0:
     \<open>q0 = 0\<close>, \<open>s0 = A - jm2\<close>\<close>
  have AmlT: "A - ?jm2 < w" using AltN wdef j0lt Ajm2 by linarith
  have s0val: "?s0 = A - ?jm2" using AmlT by simp
  have q0z: "?q0 = 0" using AmlT by simp
  have s0w: "?s0 < w" using AmlT s0val by simp
  \<comment> \<open>\<open>A + jj = jm2 + qjj*w\<close> with \<open>qjj = (if s0=0 then 0 else 1) \<le> 1\<close>, offset 0\<close>
  obtain qjj where qjjdef: "qjj = (if ?s0 = 0 then 0 else 1 :: nat)" by blast
  have qjj1: "qjj \<le> 1" using qjjdef by simp
  have Ajjfloor: "A + ?jj = ?jm2 + qjj * w"
  proof (cases "?s0 = 0")
    case True
    hence jjz: "?jj = 0" using w0' by simp
    have "A = ?jm2" using s0val True Ajm2 by simp
    thus ?thesis using jjz qjjdef True by simp
  next
    case False
    hence s0pos: "0 < ?s0" by simp
    have "?jj = w - ?s0" using s0w s0pos by simp
    hence "A + ?jj = ?jm2 + ?s0 + (w - ?s0)" using s0val Ajm2 by simp
    also have "\<dots> = ?jm2 + w" using s0w by simp
    finally show ?thesis using qjjdef False by simp
  qed
  \<comment> \<open>\<open>A + jj \<le> j1 = jm2 + w\<close>, hence \<open>jj \<le> m\<close>\<close>
  have Ajjle: "A + ?jj \<le> ?j1"
  proof -
    have "?jm2 + qjj * w \<le> ?jm2 + 1 * w" using qjj1 by (simp add: mult_le_mono1)
    thus ?thesis using Ajjfloor wdef j0lt by linarith
  qed
  have jjle_m: "?jj \<le> ?m" using Ajjle mval by linarith
  \<comment> \<open>\<open>qjj < n\<close>: \<open>jm2 + qjj*w = A + jj \<le> E < Lng (N[n]) = jm2 + n*w\<close>\<close>
  have qjjlt: "qjj < n"
  proof -
    have "A + ?jj \<le> E" using jjle_m mval Ele AltN by linarith
    hence "?jm2 + qjj * w < ?jm2 + n * w" using Ajjfloor Eub lenMn by linarith
    hence "qjj * w < n * w" by simp
    thus ?thesis using w0' by simp
  qed
  \<comment> \<open>witness reads \<open>entry N 0 jm2 + qjj*delta\<close> (floor, offset 0)\<close>
  have jjltS: "?jj < Lng S" using jjle_m mval LngS Ele AltN by linarith
  have eSjj: "entry S 0 ?jj = entry N 0 ?jm2 + qjj * ?delta"
  proof -
    have decode: "entry ((N::pairseq)[n]) 0 (?jm2 + qjj * ?w + 0)
              = entry N 0 (?jm2 + 0) + qjj * ?delta"
      by (rule oper_d1pos_entry0[OF L notzero hp i1z j0lt qjjlt]) (use w0 in simp)
    have "entry S 0 ?jj = entry ((N::pairseq)[n]) 0 (A + ?jj)"
      unfolding S_def by (rule entry_seg[OF jjltS[unfolded S_def]])
    also have "\<dots> = entry ((N::pairseq)[n]) 0 (?jm2 + qjj * ?w + 0)"
      using Ajjfloor wdef by simp
    also have "\<dots> = entry N 0 ?jm2 + qjj * ?delta" using decode by simp
    finally show ?thesis .
  qed
  \<comment> \<open>uniform witness over the STRICT tail \<open>[m+1, Lng S-1]\<close> (\<open>k = m+1\<close>)\<close>
  have wit: "\<And>x. Suc ?m \<le> x \<Longrightarrow> x \<le> Lng S - 1 \<Longrightarrow> entry S 0 ?jj < entry S 0 x"
  proof -
    fix x assume xlo: "Suc ?m \<le> x" and xhi: "x \<le> Lng S - 1"
    \<comment> \<open>the N[n]-index \<open>A + x\<close> lies strictly above \<open>j1 = jm2 + w\<close>\<close>
    have AxgN: "?j1 < A + x" using xlo mval by linarith
    have AxleE: "A + x \<le> E" using xhi LngS Ele AltN by linarith
    let ?qx = "(A + x - ?jm2) div w"  let ?sx = "(A + x - ?jm2) mod w"
    have sxw: "?sx < w" using w0' by simp
    have Axge: "?jm2 \<le> A + x" using AxgN j0lt by linarith
    have xsplit: "A + x = ?jm2 + ?qx * w + ?sx"
      using div_mult_mod_eq[of "A + x - ?jm2" w] Axge by (simp add: mult.commute)
    \<comment> \<open>\<open>qx < n\<close>\<close>
    have qxn: "?qx < n"
    proof -
      have "A + x - ?jm2 < n * w" using AxleE Eub lenMn Axge by linarith
      thus ?thesis by (rule less_mult_imp_div_less)
    qed
    \<comment> \<open>read \<open>entry S 0 x\<close> via the block formula\<close>
    have xltS: "x < Lng S" using xhi LngS Ele AltN by linarith
    have eSx: "entry S 0 x = entry ((N::pairseq)[n]) 0 (A + x)"
      unfolding S_def by (rule entry_seg[OF xltS[unfolded S_def]])
    have sxw': "?sx < ?j1 - ?jm2" using sxw wdef by simp
    have block: "entry ((N::pairseq)[n]) 0 (?jm2 + ?qx * ?w + ?sx)
               = entry N 0 (?jm2 + ?sx) + ?qx * ?delta"
      by (rule oper_d1pos_entry0[OF L notzero hp i1z j0lt qxn sxw'])
    have xsplit': "A + x = ?jm2 + ?qx * ?w + ?sx" using xsplit wdef by simp
    have eSx2: "entry S 0 x = entry N 0 (?jm2 + ?sx) + ?qx * ?delta"
      using eSx xsplit' block by simp
    \<comment> \<open>\<open>qjj \<le> qx\<close>, and \<open>qjj < qx \<or> (qjj = qx \<and> 0 < sx)\<close>\<close>
    have AxgtAjj: "A + ?jj < A + x" using xlo jjle_m by linarith
    have floorlt: "?jm2 + qjj * w < ?jm2 + ?qx * w + ?sx"
      using AxgtAjj Ajjfloor xsplit wdef by simp
    have qjjle: "qjj \<le> ?qx"
    proof (rule ccontr)
      assume "\<not> qjj \<le> ?qx"
      hence sq: "Suc ?qx \<le> qjj" by simp
      have "Suc ?qx * w \<le> qjj * w" by (rule mult_le_mono1[OF sq])
      hence "?qx * w + w \<le> qjj * w" by simp
      hence "?qx * w + ?sx < qjj * w" using sxw by linarith
      thus False using floorlt by linarith
    qed
    have dpos': "0 < ?delta" using dpos by simp
    have floor_le: "entry N 0 ?jm2 \<le> entry N 0 (?jm2 + ?sx)"
      by (rule oper_d1pos_period_row0_floor[OF hp i1z j0lt]) (use sxw' in simp)
    show "entry S 0 ?jj < entry S 0 x"
    proof (cases "qjj = ?qx")
      case True
      \<comment> \<open>SAME block: then \<open>0 < sx\<close>; STRICT floor undercuts\<close>
      have sxpos: "0 < ?sx"
      proof -
        have "?jm2 + qjj * w < ?jm2 + qjj * w + ?sx" using floorlt True by simp
        thus ?thesis by linarith
      qed
      have strict: "entry N 0 ?jm2 < entry N 0 (?jm2 + ?sx)"
        by (rule oper_d1pos_strict_period_floor[OF hp i1z j0lt sxpos]) (use sxw' in simp)
      have "entry S 0 ?jj = entry N 0 ?jm2 + qjj * ?delta" using eSjj .
      also have "\<dots> < entry N 0 (?jm2 + ?sx) + ?qx * ?delta"
        using strict True by simp
      also have "\<dots> = entry S 0 x" using eSx2 by simp
      finally show ?thesis .
    next
      case False
      \<comment> \<open>HIGHER block: \<open>qjj + 1 \<le> qx\<close>, so \<open>qjj*delta + delta \<le> qx*delta\<close>\<close>
      have q1: "Suc qjj \<le> ?qx" using qjjle False by simp
      have qd: "qjj * ?delta + ?delta \<le> ?qx * ?delta"
      proof -
        have "Suc qjj * ?delta \<le> ?qx * ?delta" by (rule mult_le_mono1[OF q1])
        thus ?thesis by simp
      qed
      have "entry S 0 ?jj = entry N 0 ?jm2 + qjj * ?delta" using eSjj .
      also have "\<dots> < entry N 0 ?jm2 + (qjj * ?delta + ?delta)" using dpos' by simp
      also have "\<dots> \<le> entry N 0 (?jm2 + ?sx) + ?qx * ?delta"
        using floor_le qd by linarith
      also have "\<dots> = entry S 0 x" using eSx2 by simp
      finally show ?thesis .
    qed
  qed
  \<comment> \<open>bridge: anchor strictly below \<open>k = m+1\<close>, i.e. \<open>c \<le> m\<close>\<close>
  have jjltk: "?jj < Suc ?m" using jjle_m by simp
  have "IdxSum (P S) ! (length (P S) - 1) < Suc ?m"
    by (rule anchor_lt_of_uniform_witness[OF ST multi jjltk wit])
  thus "c \<le> ?m" unfolding c_def by simp
qed

text \<open>§6.8 d1pos \<not>brle REGIME-A anchor coincidence, clt/cNlt-FREE.  This is the
  reproved @{thm [source] oper_d1pos_anchor_coincide_regA} with the two
  NON-UNIVERSAL hypotheses \<open>clt : c < m\<close> / \<open>cNlt : cN < m\<close> ELIMINATED.  In regime A
  (\<open>A < j\<^sub>m\<^sub>2\<close>, the verbatim-prefix sub-regime, \<open>shamt = 0\<close>) BOTH anchors sit
  strictly below the boundary \<open>m = Lng (seg N A (Lng N-1)) - 1\<close>: \<open>c < m\<close> by
  @{thm [source] oper_d1pos_clt_regA} (the periodic-tail row-0 lower bound) and
  \<open>cN < m\<close> by @{thm [source] oper_d1pos_cNlt_of_Ajm2} (\<open>A \<le> j\<^sub>m\<^sub>2\<close>, the period-base
  witness).  The boundary case \<open>c = m\<close> (singleton last \<open>P\<close>-component) NEVER occurs
  in regime A (deep-verified 0/3273, /tmp/regA_cNlt_regA.py), so the existing
  truncate-at-\<open>(m-1)\<close> agreement of @{thm [source] oper_d1pos_anchor_coincide_regA}
  applies verbatim.  Replaces the over-conditioned regA with a hypothesis set that
  is UNIVERSAL on regime A.\<close>

lemma oper_d1pos_anchor_coincide_regA2:
  fixes N :: pairseq and A E n :: nat
  defines "S \<equiv> seg ((N::pairseq)[n]) A E"
      and "Snside \<equiv> seg N A (Lng N - 1)"
  defines "c \<equiv> IdxSum (P S) ! (length (P S) - 1)"
      and "cN \<equiv> IdxSum (P Snside) ! (length (P Snside) - 1)"
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and n1: "1 \<le> n"
    and Abnd: "A < parent N 1 (Lng N - 1)"
    and Ele: "Lng N - 1 \<le> E"
    and Eub: "E < Lng ((N::pairseq)[n])"
    and dpos: "entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1)"
    and multi: "1 < length (P S)"
    and multiN: "1 < length (P Snside)"
  shows "c = cN"
    and "entry S 0 c = entry Snside 0 cN"
    and "entry S 1 c \<le> entry Snside 1 cN"
proof -
  let ?jm2 = "parent N 1 (Lng N - 1)"
  \<comment> \<open>regime A places \<open>A\<close> strictly below the period base \<open>jm2\<close>, hence below \<open>Lng N-1\<close>\<close>
  have AltN: "A < Lng N - 1" using Abnd j0lt by linarith
  have Ajm2: "A \<le> ?jm2" using Abnd by linarith
  \<comment> \<open>derive the two anchor bounds (UNIVERSAL on regime A)\<close>
  have clt: "c < Lng Snside - 1" unfolding c_def S_def Snside_def
    by (rule oper_d1pos_clt_regA[OF L notzero hp i1z j0lt n1 Abnd Ele Eub dpos
              multi[unfolded S_def c_def]])
  have cNlt: "cN < Lng Snside - 1" unfolding cN_def Snside_def
    by (rule oper_d1pos_cNlt_of_Ajm2[OF L AltN multiN[unfolded Snside_def] Ajm2 j0lt dpos])
  \<comment> \<open>invoke the (truncate-route) anchor coincidence with the now-discharged bounds\<close>
  show "c = cN"
    unfolding c_def cN_def S_def Snside_def
    by (rule oper_d1pos_anchor_coincide_regA(1)[OF L notzero hp i1z j0lt n1 AltN Ele
          multi[unfolded S_def] multiN[unfolded Snside_def]
          clt[unfolded c_def S_def Snside_def] cNlt[unfolded cN_def Snside_def]])
  show "entry S 0 c = entry Snside 0 cN"
    unfolding c_def cN_def S_def Snside_def
    by (rule oper_d1pos_anchor_coincide_regA(2)[OF L notzero hp i1z j0lt n1 AltN Ele
          multi[unfolded S_def] multiN[unfolded Snside_def]
          clt[unfolded c_def S_def Snside_def] cNlt[unfolded cN_def Snside_def]])
  show "entry S 1 c \<le> entry Snside 1 cN"
    unfolding c_def cN_def S_def Snside_def
    by (rule oper_d1pos_anchor_coincide_regA(3)[OF L notzero hp i1z j0lt n1 AltN Ele
          multi[unfolded S_def] multiN[unfolded Snside_def]
          clt[unfolded c_def S_def Snside_def] cNlt[unfolded cN_def Snside_def]])
qed

end
