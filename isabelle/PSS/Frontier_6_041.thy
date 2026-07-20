theory Frontier_6_041
  imports Support_6_023
begin

text \<open>§6.8 d1pos \<open>\<not>brle\<close> CELL-4 (PERIODIC-TAIL) assembly — the GENUINE SHIFT case
  (\<open>shamt = q\<^sub>0\<cdot>\<delta> > 0\<close>).  The slice starts in \<open>M\<close>'s PERIODIC TAIL
  (\<open>j'\<^sub>0 \<ge> Lng N-1\<close>); the block index is \<open>q\<^sub>0 = (j'\<^sub>0-j\<^sub>m\<^sub>2) div w \<ge> 1\<close>, the reduced
  start \<open>j\<^sub>0\<^sup>red = j\<^sub>m\<^sub>2 + (j'\<^sub>0-j\<^sub>m\<^sub>2) mod w < Lng N-1\<close>, \<open>j\<^sub>1\<^sup>red = min (j\<^sub>0\<^sup>red+(j'\<^sub>1-j'\<^sub>0)) (Lng N-1)\<close>.
  Wiring mirrors the regime-B assembly but WITH the shift: (1) the shifted Br
  alignment @{thm [source] oper_d1pos_notbrle_Br_align} (TrEq + both reshapes);
  (2) the anchor coincidence splits INTERIOR (\<open>j\<^sub>1\<^sup>red < Lng N-1\<close>, whole branch in
  block \<open>q\<^sub>0\<close>, @{thm [source] oper_d1pos_anchor_coincide_period_interior} via the
  full shift from @{thm [source] oper_d1pos_LOW_source_eq}) vs BOUNDARY
  (\<open>j\<^sub>1\<^sup>red = Lng N-1\<close>, branch crosses the period boundary,
  @{thm [source] oper_d1pos_anchor_coincide_period_boundary}); (3)
  @{thm [source] oper_d1pos_branch_collapse_concrete} folds \<open>P S\<close> with \<open>shamt = q\<^sub>0\<cdot>\<delta>\<close>;
  (4) @{thm [source] oper_d1pos_tail_junction} lifts F8/F9 to the tail node.
  DEEP-VERIFIED rank 11 (python/cell4_periodic_check.py: full existential 1254/1254,
  c=IdxSum(P S)!(len-1); interior 729 / boundary 525).  The per-case anchor inputs
  (\<open>fullShift\<close> / \<open>shiftEqB\<close>+\<open>boundEq*\<close>+\<open>mLmin_SnB\<close>), the Br-align inputs (\<open>tnc\<close>/\<open>stop\<close>),
  and the multiplicity / \<open>le0\<close> facts are the residual block-fold geometry the parent
  discharges at merge.\<close>

text \<open>§6.8 d1pos \<open>\<not>brle\<close> CELL-4 (PERIODIC-TAIL) \<open>fullShift\<close> DISCHARGER — INTERIOR case.
  The KEY shift fact: in the periodic tail (\<open>j'\<^sub>0 \<ge> Lng N-1\<close>, block index \<open>q\<^sub>0 \<ge> 1\<close>),
  when the whole branch region stays in block \<open>q\<^sub>0\<close> (\<open>j\<^sub>1\<^sup>red < Lng N-1\<close>) the \<open>M\<close>-side
  branch source \<open>S = seg M (j'\<^sub>0+TrMax M'+1) j'\<^sub>1\<close> is EXACTLY the \<open>(IncrFirst^^(q\<^sub>0\<cdot>\<delta>))\<close>-shift
  of its block-0 image \<open>Snside = seg N (j\<^sub>0\<^sup>red+TrMax N\<^sub>p+1) j\<^sub>1\<^sup>red\<close>.  Route: TrEq
  (@{thm [source] oper_d1pos_notbrle_Br_align}, given \<open>tnc\<close>/\<open>stop\<close>) identifies
  \<open>A = j'\<^sub>0+TrMax M'+1 = AN + q\<^sub>0\<cdot>w\<close> (\<open>AN = j\<^sub>0\<^sup>red+TrMax N\<^sub>p+1\<close>) and \<open>j'\<^sub>1 = AN+q\<^sub>0\<cdot>w + e\<^sub>0\<close>,
  \<open>j\<^sub>1\<^sup>red = AN + e\<^sub>0\<close> with the block offsets \<open>0 \<le> (AN-j\<^sub>m\<^sub>2) \<le> e\<^sub>0 < w\<close>; the whole-in-one-block
  shift is then @{thm [source] oper_d1pos_LOW_source_eq}.  DEEP-VERIFIED rank 10
  (python/perdis_check.py, correct SkT_PS gen len 12 KMAX 10: fullShift 669/669
  interior, 0 failures).\<close>

lemma oper_d1pos_notbrle_period_fullShift:
  fixes N :: pairseq and M :: pairseq
  assumes NT: "N \<in> T_PS" and LNgt: "1 < Lng N"
    and notzeroN: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hasparN: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1zN: "idx1 N (Lng N - 1) = 1"
    and Neq: "M = N[n]" and n1: "1 \<le> n"
    and lt: "j0' < j1'" and jM: "j1' < Lng M"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and j0pge: "Lng N - 1 \<le> j0'"
    and q0def: "q0 = (j0' - parent N 1 (Lng N - 1)) div (Lng N - 1 - parent N 1 (Lng N - 1))"
    and s0def: "s0 = (j0' - parent N 1 (Lng N - 1)) mod (Lng N - 1 - parent N 1 (Lng N - 1))"
    and j0reddef: "j0red = parent N 1 (Lng N - 1) + s0"
    and j1reddef: "j1red = min (j0red + (j1' - j0')) (Lng N - 1)"
    and shamtdef: "shamt = q0 * (entry N 0 (Lng N - 1) - entry N 0 (parent N 1 (Lng N - 1)))"
    and tnc: "TrMax (seg N j0red j1red) \<le> j1red - 1 - j0red"
    and stop: "\<not> nextR (seg ((N::pairseq)[n]) j0' j1') 1
                  (TrMax (seg N j0red j1red))
                  (TrMax (seg N j0red j1red) + 1)"
    and notbrle: "\<not> (TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1
                     \<or> le0 (seg M j0' j1') (TrMax (seg M j0' j1') + 1) (Lng (seg M j0' j1') - 1))"
    and interior: "j1red < Lng N - 1"
  shows "seg M (j0' + TrMax (seg M j0' j1') + 1) j1'
       = (IncrFirst ^^ shamt)
           (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red)"
proof -
  let ?M = "(N::pairseq)[n]"
  let ?Mp = "seg ?M j0' j1'"
  let ?jm2 = "parent N 1 (Lng N - 1)"
  let ?w = "Lng N - 1 - ?jm2"
  let ?delta = "entry N 0 (Lng N - 1) - entry N 0 ?jm2"
  let ?Np = "seg N j0red j1red"
  let ?t = "TrMax ?Mp"
  let ?tN = "TrMax ?Np"
  let ?A = "j0' + ?t + 1"
  let ?AN = "j0red + ?tN + 1"
  \<comment> \<open>basic geometry\<close>
  have MNn: "M = ?M" using Neq .
  have j1lt: "j1' < Lng ?M" using jM Neq by simp
  have w0: "0 < ?w" using j0lt by linarith
  have s0lt: "s0 < ?w" using s0def w0 by simp
  have j0reds: "j0red = ?jm2 + s0" using j0reddef .
  have j0redlt: "j0red < Lng N - 1" using j0reds s0lt by linarith
  have j0pge2: "?jm2 \<le> j0'" using j0pge j0lt by linarith
  have j0'split: "j0' - ?jm2 = q0 * ?w + s0"
    using q0def s0def by (simp add: mult.commute)
  have j0'eq: "j0' = ?jm2 + q0 * ?w + s0" using j0'split j0pge2 by linarith
  \<comment> \<open>\<open>q0 < n\<close>\<close>
  have q0n: "q0 < n"
  proof -
    have "j0' < Lng ?M" using lt j1lt by linarith
    hence "j0' < ?jm2 + n * ?w" using oper_d1pos_LngM[OF LNgt notzeroN hasparN i1zN j0lt] Neq by simp
    hence "q0 * ?w + s0 < n * ?w" using j0'eq by linarith
    hence "q0 * ?w < n * ?w" using s0lt by linarith
    thus ?thesis using w0 by simp
  qed
  \<comment> \<open>geometry of \<open>j1red\<close> (interior: the min did NOT cap)\<close>
  have j0j1red: "j0red < j1red"
  proof -
    have "j0red < j0red + (j1' - j0')" using lt by simp
    moreover have "j0red < Lng N - 1" using j0redlt .
    ultimately show ?thesis using j1reddef by simp
  qed
  have j1redspan: "j1red \<le> j0red + (j1' - j0')" using j1reddef by simp
  have j1redle: "j1red \<le> Lng N - 1" using j1reddef by simp
  have j1redInt: "j1red = j0red + (j1' - j0')" using interior j1reddef by simp
  \<comment> \<open>TrEq from the (already-proven) Br-align\<close>
  have notbrle': "\<not> (TrMax ?Mp = Lng ?Mp - 1 \<or> le0 ?Mp (TrMax ?Mp + 1) (Lng ?Mp - 1))"
    using notbrle MNn by simp
  have align: "TrMax ?Mp = ?tN
       \<and> Br ?Mp = P (seg ?M (j0' + TrMax ?Mp + 1) j1')
       \<and> Br ?Np = P (seg N (j0red + ?tN + 1) j1red)
       \<and> Br ?Mp \<noteq> [] \<and> Br ?Np \<noteq> []"
    by (rule oper_d1pos_notbrle_Br_align[OF NT LNgt notzeroN hasparN i1zN j0lt n1 q0n
            j0redlt j0reds s0lt j0'eq shamtdef j1redle j0j1red j1redspan lt j1lt tnc stop notbrle'])
  have TrEq: "?t = ?tN" using align by blast
  \<comment> \<open>block coordinates: \<open>A = jm2 + q0*w + (s0 + tN + 1)\<close>, \<open>j1' = jm2 + q0*w + e0\<close>,
     \<open>j1red = jm2 + (s0 + tN + 1) + (e0 - (s0+tN+1))\<close>; use the in-block slice shift\<close>
  obtain sp where spdef: "sp = s0 + ?tN + 1" by blast
  obtain e0 where e0def: "e0 = j1' - ?jm2 - q0 * ?w" by blast
  \<comment> \<open>\<open>A = jm2 + q0*w + sp\<close>\<close>
  have Aeq: "?A = ?jm2 + q0 * ?w + sp"
  proof -
    have "?A = j0' + ?tN + 1" using TrEq by simp
    also have "\<dots> = (?jm2 + q0 * ?w + s0) + ?tN + 1" using j0'eq by simp
    also have "\<dots> = ?jm2 + q0 * ?w + sp" using spdef by simp
    finally show ?thesis .
  qed
  \<comment> \<open>\<open>j1' = jm2 + q0*w + e0\<close>\<close>
  have j1'ge: "?jm2 + q0 * ?w \<le> j1'"
  proof -
    have "?jm2 + q0 * ?w \<le> j0'" using j0'eq by simp
    thus ?thesis using lt by linarith
  qed
  have j1'eq: "j1' = ?jm2 + q0 * ?w + e0" using e0def j1'ge by linarith
  \<comment> \<open>\<open>AN = jm2 + sp\<close>\<close>
  have ANeq: "?AN = ?jm2 + sp" using j0reds spdef by simp
  \<comment> \<open>\<open>s0 \<le> e0\<close> from \<open>j0' < j1'\<close>\<close>
  have s0e0: "s0 \<le> e0" using j0'eq j1'eq lt by linarith
  \<comment> \<open>\<open>j1red = jm2 + e0\<close>  (interior)\<close>
  have j1redEq: "j1red = ?jm2 + e0"
  proof -
    have "j1' - j0' = e0 - s0" using j0'eq j1'eq by linarith
    hence "j1red = (?jm2 + s0) + (e0 - s0)" using j1redInt j0reds by simp
    thus ?thesis using s0e0 by simp
  qed
  \<comment> \<open>side conditions for @{thm [source] oper_d1pos_LOW_source_eq}: \<open>sp \<le> e0\<close>, \<open>e0 < w\<close>\<close>
  have e0lt: "e0 < ?w"
  proof -
    have "?jm2 + e0 < Lng N - 1" using j1redEq interior by simp
    thus ?thesis by linarith
  qed
  have sple0: "sp \<le> e0"
  proof -
    have "?jm2 + sp = ?AN" using ANeq by simp
    moreover have "?AN \<le> j1red" \<comment> \<open>branch region non-empty placement\<close>
    proof -
      have "?AN = j0red + ?tN + 1" by simp
      moreover have "?tN \<le> j1red - 1 - j0red" using tnc .
      ultimately show ?thesis using j0j1red by linarith
    qed
    ultimately have "?jm2 + sp \<le> j1red" by simp
    thus ?thesis using j1redEq by linarith
  qed
  \<comment> \<open>apply the in-block shift identity (base \<open>N\<close>, block \<open>q0\<close>, offsets \<open>sp..e0\<close>)\<close>
  have src: "seg ?M (?jm2 + q0 * ?w + sp) (?jm2 + q0 * ?w + e0)
           = (IncrFirst ^^ (q0 * ?delta)) (seg N (?jm2 + sp) (?jm2 + e0))"
    by (rule oper_d1pos_LOW_source_eq[OF LNgt notzeroN hasparN i1zN j0lt q0n sple0 e0lt])
  \<comment> \<open>rewrite both sides into the goal's endpoints; bridge \<open>seg M = seg ?M\<close> via \<open>Neq\<close>\<close>
  have goalA: "j0' + TrMax (seg M j0' j1') + 1 = ?jm2 + q0 * ?w + sp"
    using MNn Aeq by simp
  have lhsEq: "seg M (j0' + TrMax (seg M j0' j1') + 1) j1'
             = seg ?M (?jm2 + q0 * ?w + sp) (?jm2 + q0 * ?w + e0)"
  proof -
    have "seg M (j0' + TrMax (seg M j0' j1') + 1) j1'
        = seg ?M (?jm2 + q0 * ?w + sp) j1'" using MNn goalA by simp
    also have "\<dots> = seg ?M (?jm2 + q0 * ?w + sp) (?jm2 + q0 * ?w + e0)" using j1'eq by simp
    finally show ?thesis .
  qed
  have rhsEq: "seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red
             = seg N (?jm2 + sp) (?jm2 + e0)"
  proof -
    have "j0red + TrMax (seg N j0red j1red) + 1 = ?jm2 + sp" using ANeq by simp
    thus ?thesis using j1redEq by simp
  qed
  have shEq: "shamt = q0 * ?delta" using shamtdef by simp
  show ?thesis
    using src lhsEq rhsEq shEq by simp
qed

text \<open>§6.8 d1pos \<open>\<not>brle\<close> CELL-4 (PERIODIC-TAIL) BOUNDARY-junction DISCHARGER.
  When the branch region CROSSES the period boundary (\<open>j\<^sub>1\<^sup>red = Lng N-1\<close>) the
  branch's boundary index \<open>m = Lng Snside-1\<close> sits at the absolute \<open>M\<close>-index
  \<open>A+m = j\<^sub>m\<^sub>2 + (q\<^sub>0+1)\<cdot>w\<close> — the START of block \<open>q\<^sub>0+1\<close> (offset 0).  Three facts:
  (\<open>shiftEqB\<close>) the PREFIX \<open>seg S 0 (m-1)\<close> stays in block \<open>q\<^sub>0\<close>, so it is the
    \<open>(IncrFirst^^(q\<^sub>0\<cdot>\<delta>))\<close>-shift of its block-0 image (@{thm [source] oper_d1pos_LOW_source_eq});
  (\<open>boundEq0B\<close>) the row-0 junction value reads block \<open>q\<^sub>0+1\<close> offset 0
    (@{thm [source] oper_d1pos_entry0}): \<open>entry N 0 j\<^sub>m\<^sub>2 + (q\<^sub>0+1)\<cdot>\<delta> = entry N 0 (Lng N-1) + q\<^sub>0\<cdot>\<delta>\<close>
    using \<open>dpos\<close> (\<open>entry N 0 j\<^sub>m\<^sub>2 + \<delta> = entry N 0 (Lng N-1)\<close>);
  (\<open>boundEq1B\<close>) the row-1 junction value is UNSHIFTED (@{thm [source] oper_d1pos_entry1}):
    \<open>entry N 1 j\<^sub>m\<^sub>2 \<le> entry N 1 (Lng N-1)\<close> via \<open>r1le\<close>.
  Plus (\<open>mleSB\<close>) the span bound \<open>Lng Snside-1 \<le> Lng S-1\<close>.  DEEP-VERIFIED rank 10
  (python/perdis_check.py: boundary 448/448, all of shiftEqB/boundEq0B/boundEq1B/mleSB
  + /tmp/perdis_bnd2.py junction identities 448/448, 0 failures).\<close>

lemma oper_d1pos_notbrle_period_boundary_geom:
  fixes N :: pairseq and M :: pairseq
  assumes NT: "N \<in> T_PS" and LNgt: "1 < Lng N"
    and notzeroN: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hasparN: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1zN: "idx1 N (Lng N - 1) = 1"
    and Neq: "M = N[n]" and n1: "1 \<le> n"
    and lt: "j0' < j1'" and jM: "j1' < Lng M"
    and bge: "Lng N - 1 \<le> j1'"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and j0pge: "Lng N - 1 \<le> j0'"
    and q0def: "q0 = (j0' - parent N 1 (Lng N - 1)) div (Lng N - 1 - parent N 1 (Lng N - 1))"
    and s0def: "s0 = (j0' - parent N 1 (Lng N - 1)) mod (Lng N - 1 - parent N 1 (Lng N - 1))"
    and j0reddef: "j0red = parent N 1 (Lng N - 1) + s0"
    and j1reddef: "j1red = min (j0red + (j1' - j0')) (Lng N - 1)"
    and shamtdef: "shamt = q0 * (entry N 0 (Lng N - 1) - entry N 0 (parent N 1 (Lng N - 1)))"
    and tnc: "TrMax (seg N j0red j1red) \<le> j1red - 1 - j0red"
    and stop: "\<not> nextR (seg ((N::pairseq)[n]) j0' j1') 1
                  (TrMax (seg N j0red j1red))
                  (TrMax (seg N j0red j1red) + 1)"
    and multiNp: "1 < length (P (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red))"
    and notbrle: "\<not> (TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1
                     \<or> le0 (seg M j0' j1') (TrMax (seg M j0' j1') + 1) (Lng (seg M j0' j1') - 1))"
    and boundary: "\<not> j1red < Lng N - 1"
  shows "(seg (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 0
              (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1 - 1)
        = (IncrFirst ^^ shamt)
            (seg (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) 0
                 (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1 - 1)))
     \<and> (entry (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 0
              (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1)
        = entry (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) 0
                (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1) + shamt)
     \<and> (entry (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 1
              (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1)
        \<le> entry (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) 1
                (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1))
     \<and> (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1
        \<le> Lng (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') - 1)"
proof -
  let ?M = "(N::pairseq)[n]"
  let ?Mp = "seg ?M j0' j1'"
  let ?jm2 = "parent N 1 (Lng N - 1)"
  let ?w = "Lng N - 1 - ?jm2"
  let ?delta = "entry N 0 (Lng N - 1) - entry N 0 ?jm2"
  let ?Np = "seg N j0red j1red"
  let ?t = "TrMax ?Mp"
  let ?tN = "TrMax ?Np"
  let ?A = "j0' + ?t + 1"
  let ?AN = "j0red + ?tN + 1"
  let ?S = "seg M ?A j1'"
  let ?Snside = "seg N ?AN j1red"
  let ?m = "Lng ?Snside - 1"
  \<comment> \<open>basic geometry (mirror of \<open>fullShift\<close>)\<close>
  have MNn: "M = ?M" using Neq .
  have j1lt: "j1' < Lng ?M" using jM Neq by simp
  have w0: "0 < ?w" using j0lt by linarith
  have s0lt: "s0 < ?w" using s0def w0 by simp
  have j0reds: "j0red = ?jm2 + s0" using j0reddef .
  have j0redlt: "j0red < Lng N - 1" using j0reds s0lt by linarith
  have j0pge2: "?jm2 \<le> j0'" using j0pge j0lt by linarith
  have j0'split: "j0' - ?jm2 = q0 * ?w + s0"
    using q0def s0def by (simp add: mult.commute)
  have j0'eq: "j0' = ?jm2 + q0 * ?w + s0" using j0'split j0pge2 by linarith
  have q0n: "q0 < n"
  proof -
    have "j0' < Lng ?M" using lt j1lt by linarith
    hence "j0' < ?jm2 + n * ?w" using oper_d1pos_LngM[OF LNgt notzeroN hasparN i1zN j0lt] Neq by simp
    hence "q0 * ?w + s0 < n * ?w" using j0'eq by linarith
    hence "q0 * ?w < n * ?w" using s0lt by linarith
    thus ?thesis using w0 by simp
  qed
  have j0j1red: "j0red < j1red"
  proof -
    have "j0red < j0red + (j1' - j0')" using lt by simp
    moreover have "j0red < Lng N - 1" using j0redlt .
    ultimately show ?thesis using j1reddef by simp
  qed
  have j1redspan: "j1red \<le> j0red + (j1' - j0')" using j1reddef by simp
  have j1redle: "j1red \<le> Lng N - 1" using j1reddef by simp
  have j1redB: "j1red = Lng N - 1" using boundary j1redle by linarith
  \<comment> \<open>TrEq via Br-align\<close>
  have notbrle': "\<not> (TrMax ?Mp = Lng ?Mp - 1 \<or> le0 ?Mp (TrMax ?Mp + 1) (Lng ?Mp - 1))"
    using notbrle MNn by simp
  have align: "TrMax ?Mp = ?tN
       \<and> Br ?Mp = P (seg ?M (j0' + TrMax ?Mp + 1) j1')
       \<and> Br ?Np = P (seg N (j0red + ?tN + 1) j1red)
       \<and> Br ?Mp \<noteq> [] \<and> Br ?Np \<noteq> []"
    by (rule oper_d1pos_notbrle_Br_align[OF NT LNgt notzeroN hasparN i1zN j0lt n1 q0n
            j0redlt j0reds s0lt j0'eq shamtdef j1redle j0j1red j1redspan lt j1lt tnc stop notbrle'])
  have TrEq: "?t = ?tN" using align by blast
  \<comment> \<open>block coordinates\<close>
  obtain sp where spdef: "sp = s0 + ?tN + 1" by blast
  have Aeq: "?A = ?jm2 + q0 * ?w + sp"
  proof -
    have "?A = j0' + ?tN + 1" using TrEq by simp
    also have "\<dots> = (?jm2 + q0 * ?w + s0) + ?tN + 1" using j0'eq by simp
    also have "\<dots> = ?jm2 + q0 * ?w + sp" using spdef by simp
    finally show ?thesis .
  qed
  have ANeq: "?AN = ?jm2 + sp" using j0reds spdef by simp
  \<comment> \<open>\<open>AN \<le> j1red = Lng N-1\<close>, so \<open>sp \<le> w\<close>; and \<open>m = j1red - AN = Lng N-1 - jm2 - sp = w - sp\<close>\<close>
  have ANle: "?AN \<le> j1red"
  proof -
    have "?tN \<le> j1red - 1 - j0red" using tnc .
    thus ?thesis using j0j1red by linarith
  qed
  have spw: "sp \<le> ?w" using ANeq ANle j1redB by linarith
  have LngSn: "Lng ?Snside = Suc j1red - ?AN" by (rule Lng_seg)
  have meq: "?m = ?w - sp"
  proof -
    have "?m = j1red - ?AN" using LngSn ANle by simp
    also have "\<dots> = (?jm2 + ?w) - (?jm2 + sp)" using j1redB ANeq j0lt by simp
    also have "\<dots> = ?w - sp" by simp
    finally show ?thesis .
  qed
  \<comment> \<open>positivity: \<open>0 < m\<close> from \<open>multiNp\<close> (the N-side branch is multi → \<open>Lng Snside > 1\<close>)\<close>
  have Snne: "?Snside \<noteq> []"
  proof
    assume "?Snside = []"
    hence "P ?Snside = [[]]" by (subst P.simps) (simp add: multiT_def zeroT_def monoT_def)
    thus False using multiNp by simp
  qed
  have SnT: "?Snside \<in> T_PS" using Snne by (simp add: T_PS_def)
  have mpos: "0 < ?m"
  proof -
    have "multiT ?Snside" using m_6_2_P_components_2[OF SnT] multiNp by simp
    hence "1 < Lng ?Snside" by (rule multiT_imp_Lng_gt1[OF SnT])
    thus ?thesis by simp
  qed
  have spltw: "sp < ?w" using mpos meq w0 by linarith
  \<comment> \<open>\<open>A \<le> j1'\<close>: \<open>TrMax M' = tN \<le> j1red-1-j0red < j1red-j0red \<le> j1'-j0'\<close>\<close>
  have AleE: "?A \<le> j1'"
  proof -
    have "?tN \<le> j1red - 1 - j0red" using tnc .
    moreover have "j1red - j0red \<le> j1' - j0'" using j1redspan by linarith
    ultimately have "?tN < j1' - j0'" using j0j1red by linarith
    thus ?thesis using TrEq lt by linarith
  qed
  \<comment> \<open>\<open>AN + m = j1red = Lng N-1\<close>, \<open>A + m = jm2 + (q0+1)*w\<close>, and \<open>A + m \<le> j1'\<close>\<close>
  have ANm: "?AN + ?m = j1red" using LngSn ANle by simp
  \<comment> \<open>freeze \<open>jm2\<close>/\<open>w\<close> to fresh vars: the \<open>w = Lng N-1-jm2\<close> double-nat-sub re-expands
     under \<open>algebra_simps\<close>, so do the block algebra abstractly\<close>
  obtain jv wv where jvdef: "jv = ?jm2" and wvdef: "wv = ?w" by blast
  have Amv: "?A + ?m = jv + (q0 + 1) * wv + (0::nat)"
  proof -
    have a1: "?A + ?m = (jv + q0 * wv + sp) + (wv - sp)" using Aeq meq jvdef wvdef by simp
    have a2: "(jv + q0 * wv + sp) + (wv - sp) = jv + q0 * wv + wv" using spw wvdef by simp
    have a3: "jv + q0 * wv + wv = jv + (q0 + 1) * wv + 0" by (simp add: algebra_simps)
    show ?thesis using a1 a2 a3 by simp
  qed
  have Am: "?A + ?m = ?jm2 + (q0 + 1) * ?w + (0::nat)" using Amv jvdef wvdef by simp
  have AmleE: "?A + ?m \<le> j1'"
  proof -
    \<comment> \<open>\<open>AN + m = j1red \<le> j0red + (j1'-j0')\<close>, \<open>AN = jm2 + sp\<close>, \<open>j0red = jm2 + s0\<close>\<close>
    have e1: "?AN + ?m = j1red" using ANm .
    have e2: "?AN = ?jm2 + sp" using ANeq .
    have e3: "j0red = ?jm2 + s0" using j0reds .
    have e4: "j1red \<le> j0red + (j1' - j0')" using j1redspan .
    have spm: "sp + ?m \<le> s0 + (j1' - j0')" using e1 e2 e3 e4 by linarith
    obtain dd where dddef: "dd = j1' - j0'" by blast
    have spm': "sp + ?m \<le> s0 + dd" using spm dddef by simp
    have j1d: "j1' = j0' + dd" using dddef lt by linarith
    show ?thesis using Aeq j0'eq spm' j1d by linarith
  qed
  \<comment> \<open>(shiftEqB) PREFIX \<open>seg S 0 (m-1)\<close> in block \<open>q0\<close> (end offset \<open>sp+(m-1) < w\<close>)\<close>
  have shiftEqB: "seg ?S 0 (?m - 1)
                = (IncrFirst ^^ shamt) (seg ?Snside 0 (?m - 1))"
  proof -
    obtain ep where epdef: "ep = sp + (?m - 1)" by blast
    have eplt: "ep < ?w" using epdef meq mpos spltw by linarith
    have sple: "sp \<le> ep" using epdef by simp
    \<comment> \<open>in-block shift of \<open>seg ?M (jm2+q0*w+sp) (jm2+q0*w+ep)\<close>\<close>
    have src: "seg ?M (?jm2 + q0 * ?w + sp) (?jm2 + q0 * ?w + ep)
             = (IncrFirst ^^ (q0 * ?delta)) (seg N (?jm2 + sp) (?jm2 + ep))"
      by (rule oper_d1pos_LOW_source_eq[OF LNgt notzeroN hasparN i1zN j0lt q0n sple eplt])
    \<comment> \<open>\<open>seg ?S 0 (m-1) = seg ?M A (A+(m-1)) = seg ?M (jm2+q0w+sp) (jm2+q0w+ep)\<close>\<close>
    have segS_pref: "seg ?S 0 (?m - 1) = seg ?M ?A (?A + (?m - 1))"
    proof -
      have h: "?m - 1 \<le> j1' - ?A" using AmleE by linarith
      show ?thesis using seg_of_seg[where M = M and a = ?A and b = j1' and c = 0 and d = "?m - 1"]
          AleE h MNn by simp
    qed
    have lhsP: "seg ?S 0 (?m - 1) = seg ?M (?jm2 + q0 * ?w + sp) (?jm2 + q0 * ?w + ep)"
    proof -
      have "?A + (?m - 1) = ?jm2 + q0 * ?w + ep" using Aeq epdef by simp
      thus ?thesis using segS_pref Aeq by simp
    qed
    have rhsP: "seg ?Snside 0 (?m - 1) = seg N (?jm2 + sp) (?jm2 + ep)"
    proof -
      have ANle': "?AN \<le> j1red" using ANle .
      have hN: "?m - 1 \<le> j1red - ?AN"
      proof -
        have "?m - 1 \<le> ?m" by simp
        thus ?thesis using LngSn ANle by simp
      qed
      have lend: "?AN + 0 = ?jm2 + sp" using ANeq by simp
      have rend: "?AN + (?m - 1) = ?jm2 + ep" using ANeq epdef by (simp add: add.assoc)
      have "seg ?Snside 0 (?m - 1) = seg N (?AN + 0) (?AN + (?m - 1))"
        by (rule seg_of_seg[OF ANle' hN])
      also have "\<dots> = seg N (?jm2 + sp) (?jm2 + ep)"
        by (rule arg_cong2[where f = "seg N", OF lend rend])
      finally show ?thesis .
    qed
    have shEq: "shamt = q0 * ?delta" using shamtdef by simp
    show ?thesis using src lhsP rhsP shEq by simp
  qed
  \<comment> \<open>(boundEq0B/boundEq1B) the junction at \<open>A+m = jm2+(q0+1)*w\<close> (block \<open>q0+1\<close>, offset 0)\<close>
  have q1n: "q0 + 1 < n"
  proof -
    have LngM: "Lng ?M = ?jm2 + n * ?w"
      by (rule oper_d1pos_LngM[OF LNgt notzeroN hasparN i1zN j0lt])
    \<comment> \<open>frozen forms: \<open>A+m = jv + (q0+1)*wv\<close>, \<open>Lng M = jv + n*wv\<close>\<close>
    have Amf: "?A + ?m = jv + (q0 + 1) * wv" using Am jvdef wvdef by simp
    have LngMf: "Lng ?M = jv + n * wv" using LngM jvdef wvdef by simp
    have AmltL: "?A + ?m < Lng ?M" using AmleE j1lt by linarith
    have wvpos: "0 < wv" using w0 wvdef by simp
    have "jv + (q0 + 1) * wv < jv + n * wv" using AmltL Amf LngMf by simp
    hence prod: "(q0 + 1) * wv < n * wv" by linarith
    show "q0 + 1 < n" using prod wvpos mult_less_cancel2[of "q0 + 1" wv n] by simp
  qed
  \<comment> \<open>row-0 junction\<close>
  have e0M: "entry ?M 0 (?A + ?m) = entry N 0 ?jm2 + (q0 + 1) * ?delta"
  proof -
    have "entry ?M 0 (?jm2 + (q0 + 1) * ?w + 0) = entry N 0 (?jm2 + 0) + (q0 + 1) * ?delta"
      by (rule oper_d1pos_entry0[OF LNgt notzeroN hasparN i1zN j0lt q1n w0])
    thus ?thesis using Am by simp
  qed
  have ANmL: "?AN + ?m = Lng N - 1" using ANm trans j1redB by blast
  have e0N: "entry N 0 (?AN + ?m) = entry N 0 (Lng N - 1)"
    using ANmL by (rule arg_cong[where f = "entry N 0"])
  have dpos: "entry N 0 ?jm2 + ?delta = entry N 0 (Lng N - 1)"
    using oper_d1pos_ctx_dpos[OF hasparN i1zN j0lt] by simp
  \<comment> \<open>combine: \<open>entry ?M 0 (A+m) = entry N 0 (Lng N-1) + q0*delta\<close>\<close>
  have boundEq0_abs: "entry ?M 0 (?A + ?m) = entry N 0 (Lng N - 1) + q0 * ?delta"
  proof -
    \<comment> \<open>freeze \<open>delta\<close> and \<open>entry N 0 jm2\<close>: do the linear combination abstractly\<close>
    obtain dv ev where dvdef: "dv = ?delta" and evdef: "ev = entry N 0 ?jm2" by blast
    have q1d: "ev + (q0 + 1) * dv = (ev + dv) + q0 * dv" by (simp add: algebra_simps)
    have e0M': "entry ?M 0 (?A + ?m) = ev + (q0 + 1) * dv"
      using e0M dvdef[symmetric] evdef[symmetric] by simp
    have dpos': "ev + dv = entry N 0 (Lng N - 1)"
      using dpos dvdef[symmetric] evdef[symmetric] by simp
    have "entry ?M 0 (?A + ?m) = (ev + dv) + q0 * dv" using e0M' q1d by simp
    also have "\<dots> = entry N 0 (Lng N - 1) + q0 * ?delta" using dpos' dvdef by simp
    finally show ?thesis .
  qed
  \<comment> \<open>lift to \<open>seg\<close>-coords: \<open>entry ?S 0 m = entry ?M 0 (A+m)\<close>, \<open>entry ?Snside 0 m = entry N 0 (AN+m)\<close>\<close>
  have mlt: "?m < Suc j1' - ?A" using AmleE by linarith
  have segS_m: "entry ?S 0 ?m = entry ?M 0 (?A + ?m)"
    using mlt MNn by (simp add: entry_def seg_nth_eq)
  have segS_m1: "entry ?S 1 ?m = entry ?M 1 (?A + ?m)"
    using mlt MNn by (simp add: entry_def seg_nth_eq)
  have mltN: "?m < Suc j1red - ?AN" using LngSn ANle by simp
  have segSn_m: "entry ?Snside 0 ?m = entry N 0 (?AN + ?m)"
    using mltN by (simp add: entry_def seg_nth_eq)
  have segSn_m1: "entry ?Snside 1 ?m = entry N 1 (?AN + ?m)"
    using mltN by (simp add: entry_def seg_nth_eq)
  \<comment> \<open>(boundEq0B)\<close>
  have boundEq0B: "entry ?S 0 ?m = entry ?Snside 0 ?m + shamt"
  proof -
    have "entry ?S 0 ?m = entry N 0 (Lng N - 1) + q0 * ?delta"
      using segS_m boundEq0_abs by simp
    also have "\<dots> = entry N 0 (?AN + ?m) + shamt" using e0N shamtdef by simp
    also have "\<dots> = entry ?Snside 0 ?m + shamt" using segSn_m by simp
    finally show ?thesis .
  qed
  \<comment> \<open>(boundEq1B) row-1: \<open>entry ?M 1 (A+m) = entry N 1 jm2 \<le> entry N 1 (Lng N-1) = entry N 1 (AN+m)\<close>\<close>
  have e1M: "entry ?M 1 (?A + ?m) = entry N 1 ?jm2"
  proof -
    have "entry ?M 1 (?jm2 + (q0 + 1) * ?w + 0) = entry N 1 (?jm2 + 0)"
      by (rule oper_d1pos_entry1[OF LNgt notzeroN hasparN i1zN j0lt q1n w0])
    thus ?thesis using Am by simp
  qed
  have e1N: "entry N 1 (?AN + ?m) = entry N 1 (Lng N - 1)"
    using ANmL by (rule arg_cong[where f = "entry N 1"])
  have r1le: "entry N 1 ?jm2 \<le> entry N 1 (Lng N - 1)"
    by (rule oper_d1pos_ctx_r1le[OF hasparN i1zN])
  have boundEq1B: "entry ?S 1 ?m \<le> entry ?Snside 1 ?m"
  proof -
    have "entry ?S 1 ?m = entry N 1 ?jm2" using segS_m1 e1M by simp
    also have "\<dots> \<le> entry N 1 (Lng N - 1)" using r1le .
    also have "\<dots> = entry ?Snside 1 ?m" using segSn_m1 e1N by simp
    finally show ?thesis .
  qed
  \<comment> \<open>(mleSB) span bound\<close>
  have mleSB: "?m \<le> Lng ?S - 1"
  proof -
    have LngS: "Lng ?S = Suc j1' - ?A" by (rule Lng_seg)
    show ?thesis using AmleE LngS by linarith
  qed
  \<comment> \<open>bridge \<open>TrMax (seg (N[n]) ..) = TrMax (seg M ..)\<close> (via \<open>M = N[n]\<close>) to match the goal form\<close>
  have TrMMeq: "TrMax (seg ?M j0' j1') = TrMax (seg M j0' j1')" using MNn by simp
  show ?thesis
    using shiftEqB boundEq0B boundEq1B mleSB TrMMeq by simp
qed

text \<open>§6.8 d1pos notbrle CELL-4 (PERIODIC-TAIL) ROW-0 UNIFORM AGREEMENT discharger
  (sub-agent perresid, core).  In the periodic context (j0' >= Lng N-1,
  j0' = jm2 + q0*w + s0, j0red = jm2 + s0, shamt = q0*delta) the row-0 value of the
  consumer slice Mp = seg (N[n]) j0' j1' at every offset j <= Lng Np-1
  (Np = seg N j0red j1red, j1red <= Lng N-1) equals the row-0 value of Np shifted
  up by shamt: entry Mp 0 j = entry Np 0 j + shamt.  Two sub-cases on s = s0+j:
  the in-block case s < w reads block q0 via oper_d1pos_entry0
  (shift q0*delta), the boundary s = w (j0red+j = Lng N-1) reads block q0+1
  offset 0 whose (q0+1)*delta-shift refills the gap by dpos
  (entry N 0 jm2 + delta = entry N 0 (Lng N-1)).  This is the periodic analogue of
  oper_d1pos_row0_agree.  DEEP-VERIFIED rank 10
  (python/perresid_check.py + /tmp/perresid_route.py: row-0 uniform agreement on
  [0,Lng Np-1] 1117/1117, 0 failures).\<close>

lemma oper_d1pos_period_row0_unif:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and q0n: "q0 < n"
    and s0lt: "s0 < Lng N - 1 - parent N 1 (Lng N - 1)"
    and j0reds: "j0red = parent N 1 (Lng N - 1) + s0"
    and j0'eq: "j0' = parent N 1 (Lng N - 1)
                  + q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0"
    and shamt: "shamt = q0 * (entry N 0 (Lng N - 1) - entry N 0 (parent N 1 (Lng N - 1)))"
    and j1redle: "j1red \<le> Lng N - 1"
    and j0j1red: "j0red \<le> j1red"
    and jvalid: "j0' + j < Lng ((N::pairseq)[n])"
    and jle: "j \<le> j1red - j0red"
  shows "entry ((N::pairseq)[n]) 0 (j0' + j) = entry N 0 (j0red + j) + shamt"
proof -
  let ?jm2 = "parent N 1 (Lng N - 1)"  let ?w = "Lng N - 1 - ?jm2"
  let ?delta = "entry N 0 (Lng N - 1) - entry N 0 ?jm2"
  have w0: "0 < ?w" using j0lt by linarith
  \<comment> \<open>\<open>s = s0 + j \<le> w\<close> (\<open>j0red + j \<le> j1red \<le> Lng N-1 = jm2 + w\<close>)\<close>
  have j0redge: "?jm2 \<le> j0red" using j0reds by simp
  have sle: "s0 + j \<le> ?w"
  proof -
    have "j0red + j \<le> j1red" using jle j0j1red by linarith
    hence "j0red + j \<le> Lng N - 1" using j1redle by linarith
    thus ?thesis using j0reds by linarith
  qed
  \<comment> \<open>absolute index \<open>j0' + j = jm2 + q0*w + (s0+j)\<close>\<close>
  have idxeq: "j0' + j = ?jm2 + q0 * ?w + (s0 + j)" using j0'eq by simp
  show ?thesis
  proof (cases "s0 + j < ?w")
    case True
    \<comment> \<open>in-block \<open>q0\<close>\<close>
    have e: "entry ((N::pairseq)[n]) 0 (?jm2 + q0 * ?w + (s0 + j))
           = entry N 0 (?jm2 + (s0 + j)) + q0 * ?delta"
      by (rule oper_d1pos_entry0[OF L notzero hp i1z j0lt q0n True])
    have nshift: "entry N 0 (?jm2 + (s0 + j)) = entry N 0 (j0red + j)"
      using j0reds by (simp add: add.assoc)
    have "entry ((N::pairseq)[n]) 0 (j0' + j)
            = entry ((N::pairseq)[n]) 0 (?jm2 + q0 * ?w + (s0 + j))"
      using idxeq by (rule arg_cong[where f = "entry ((N::pairseq)[n]) 0"])
    also have "\<dots> = entry N 0 (?jm2 + (s0 + j)) + q0 * ?delta" by (rule e)
    also have "\<dots> = entry N 0 (j0red + j) + q0 * ?delta" using nshift by simp
    also have "\<dots> = entry N 0 (j0red + j) + shamt" using shamt by simp
    finally show ?thesis .
  next
    case False
    \<comment> \<open>boundary: \<open>s0 + j = w\<close>, so \<open>j0red + j = Lng N-1\<close>; read block \<open>q0+1\<close> offset 0\<close>
    have seqw: "s0 + j = ?w" using False sle by linarith
    have jredeq: "j0red + j = Lng N - 1" using seqw j0reds w0 by linarith
    \<comment> \<open>FREEZE \<open>w\<close> as a fresh var to avoid the double-nat-sub simp loop on \<open>(q0+1)*w\<close>\<close>
    obtain ww where wwdef: "ww = ?w" by blast
    \<comment> \<open>\<open>q0+1 < n\<close>: index \<open>j0'+j = jm2 + (q0+1)*w\<close> is valid in \<open>N[n] (Lng = jm2+n*w)\<close>\<close>
    have idxeqB: "j0' + j = ?jm2 + (q0 + 1) * ww"
    proof -
      have "j0' + j = ?jm2 + q0 * ww + (s0 + j)" using idxeq wwdef by simp
      also have "\<dots> = ?jm2 + q0 * ww + ww" using seqw wwdef by simp
      also have "\<dots> = ?jm2 + (q0 + 1) * ww" by simp
      finally show ?thesis .
    qed
    have LngNn: "Lng ((N::pairseq)[n]) = ?jm2 + n * ww"
      using oper_d1pos_LngM[OF L notzero hp i1z j0lt] wwdef by simp
    have w0': "0 < ww" using w0 wwdef by simp
    have q1n: "q0 + 1 < n"
    proof -
      have "?jm2 + (q0 + 1) * ww < ?jm2 + n * ww" using jvalid idxeqB LngNn by simp
      hence h: "(q0 + 1) * ww < n * ww" by simp
      show ?thesis
      proof (rule ccontr)
        assume "\<not> q0 + 1 < n"
        hence "n \<le> q0 + 1" by simp
        hence "n * ww \<le> (q0 + 1) * ww" by (rule mult_le_mono1)
        thus False using h by simp
      qed
    qed
    have e: "entry ((N::pairseq)[n]) 0 (?jm2 + (q0 + 1) * ?w + 0)
           = entry N 0 (?jm2 + 0) + (q0 + 1) * ?delta"
      by (rule oper_d1pos_entry0[OF L notzero hp i1z j0lt q1n w0])
    have idxeq2: "j0' + j = ?jm2 + (q0 + 1) * ?w + 0"
      using idxeqB wwdef by simp
    have dpos: "entry N 0 ?jm2 < entry N 0 (Lng N - 1)"
      by (rule oper_d1pos_ctx_dpos[OF hp i1z j0lt])
    \<comment> \<open>FREEZE \<open>delta\<close> as a fresh var to avoid \<open>algebra_simps\<close> distributing the nat-sub\<close>
    obtain dd where dddef: "dd = ?delta" by blast
    have refill: "entry N 0 ?jm2 + dd = entry N 0 (Lng N - 1)" using dpos dddef by simp
    have edd: "entry ((N::pairseq)[n]) 0 (?jm2 + (q0 + 1) * ?w + 0)
             = entry N 0 (?jm2 + 0) + (q0 + 1) * dd" using e dddef by simp
    have splitdd: "(q0 + 1) * dd = dd + q0 * dd" by simp
    have "entry ((N::pairseq)[n]) 0 (j0' + j)
            = entry ((N::pairseq)[n]) 0 (?jm2 + (q0 + 1) * ?w + 0)"
      using idxeq2 by (rule arg_cong[where f = "entry ((N::pairseq)[n]) 0"])
    also have "\<dots> = entry N 0 (?jm2 + 0) + (q0 + 1) * dd" by (rule edd)
    also have "\<dots> = entry N 0 ?jm2 + (dd + q0 * dd)" using splitdd by simp
    also have "\<dots> = (entry N 0 ?jm2 + dd) + q0 * dd" by (simp add: add.assoc)
    also have "\<dots> = entry N 0 (Lng N - 1) + q0 * dd" using refill by simp
    also have "\<dots> = entry N 0 (j0red + j) + q0 * ?delta" using jredeq dddef by simp
    also have "\<dots> = entry N 0 (j0red + j) + shamt" using shamt by simp
    finally show ?thesis .
  qed
qed

text \<open>§6.8 d1pos ROW-0-shift \<open>le0\<close> transfer: if \<open>M\<close> and \<open>N\<close> agree on row 0 up to a
  CONSTANT shift \<open>k\<close> on a prefix \<open>[0,c]\<close> (\<open>entry M 0 j = entry N 0 j + k\<close>), then a
  \<open>nextrel0\<close>/\<open>le0\<close> step of \<open>M\<close> within \<open>[0,c]\<close> transfers to \<open>N\<close>.  Mirror of
  @{thm [source] nextrel0_prefix_row0}/@{thm [source] le0_prefix_row0} with the
  \<open>+k\<close> shift (a constant shift is strictly order-preserving, so \<open>nextrel0\<close> — which
  reads only row-0 strict-\<open><\<close>/\<open>\<le>\<close> comparisons — is invariant).\<close>

lemma nextrel0_prefix_row0_shift:
  assumes agree: "\<And>j. j \<le> c \<Longrightarrow> entry M 0 j = entry N 0 j + k"
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

lemma le0_prefix_row0_shift:
  assumes agree: "\<And>j. j \<le> c \<Longrightarrow> entry M 0 j = entry N 0 j + k"
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
        by (rule nextrel0_prefix_row0_shift[OF agree cN yc zc yz])
      ultimately show "(nextrel0 N)\<^sup>*\<^sup>* a z" by simp
    qed
  qed
  hence "(nextrel0 N)\<^sup>*\<^sup>* a b" using bc by simp
  thus ?thesis using ac bc cN by (simp add: le0_def)
qed

text \<open>§6.8 d1pos CELL-4 (PERIODIC-TAIL) le0Np discharger: le0 N j0red j1red.
  Route (universal, interior+boundary): Mp = seg (N[n]) j0' j1' is monoT
  (le0 Mp 0 (Lng Mp-1)); restrict its row-0 ancestry chain to the boundary index
  Lng Np-1 <= Lng Mp-1 via m_5_1_ancestor_tree_1
  (le0 Mp 0 (Lng Np-1)), transfer Mp -> Np across the +shamt row-0 agreement on
  [0, Lng Np-1] (oper_d1pos_period_row0_unif via le0_prefix_row0_shift) to
  le0 Np 0 (Lng Np-1), then lift the slice via adm_le0_seg to le0 N j0red j1red.
  DEEP-VERIFIED rank 10 (python/perresid_check.py: le0Np 1117/1117;
  /tmp/perresid_route.py: le0 Mp 0 (Lng Np-1) 1117/1117, row-0 unif 1117/1117).\<close>

lemma oper_d1pos_ctx_period_le0Np:
  fixes N :: pairseq and M :: pairseq
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and Neq: "M = (N::pairseq)[n]"
    and le0M: "le0 M j0' j1'"
    and lt: "j0' < j1'" and jM: "j1' < Lng M"
    and q0n: "q0 < n"
    and s0lt: "s0 < Lng N - 1 - parent N 1 (Lng N - 1)"
    and j0reds: "j0red = parent N 1 (Lng N - 1) + s0"
    and j0'eq: "j0' = parent N 1 (Lng N - 1)
                  + q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0"
    and shamt: "shamt = q0 * (entry N 0 (Lng N - 1) - entry N 0 (parent N 1 (Lng N - 1)))"
    and j1redle: "j1red \<le> Lng N - 1"
    and j0j1red: "j0red < j1red"
    and j1redspan: "j1red \<le> j0red + (j1' - j0')"
  shows "le0 N j0red j1red"
proof -
  let ?Mp = "seg M j0' j1'"
  let ?Np = "seg N j0red j1red"
  let ?m = "j1red - j0red"  \<comment> \<open>\<open>= Lng Np - 1\<close>\<close>
  have MT: "M \<in> T_PS" using jM unfolding T_PS_def by (cases M) auto
  have LMp: "Lng ?Mp = Suc j1' - j0'" by simp
  have j0le: "j0' \<le> j1'" using lt by linarith
  \<comment> \<open>\<open>M'\<close> monoT: \<open>le0 M' 0 (Lng M'-1)\<close>\<close>
  have MpT: "?Mp \<in> T_PS" using lt by (simp add: T_PS_def seg_def)
  have le0Mp: "le0 ?Mp 0 (Lng ?Mp - 1)"
  proof -
    have "le0 M j0' j1'" by (rule le0M)
    hence "le0 ?Mp 0 (j1' - j0')"
      using adm_le0_seg[OF jM, where a=0 and b="j1' - j0'" and j0'=j0'] j0le by simp
    thus ?thesis using LMp j0le by simp
  qed
  \<comment> \<open>\<open>j0red \<le> j0'\<close> (period reduction never moves right) hence \<open>j1red \<le> j1'\<close>\<close>
  have j0redlej0': "j0red \<le> j0'" using j0reds j0'eq by simp
  have j1redlej1': "j1red \<le> j1'"
  proof -
    have "j0red + (j1' - j0') \<le> j0' + (j1' - j0')" using j0redlej0' by simp
    also have "\<dots> = j1'" using j0le by simp
    finally show ?thesis using j1redspan by linarith
  qed
  \<comment> \<open>restrict to the boundary index \<open>m = Lng Np - 1 \<le> Lng M'-1\<close>\<close>
  have mleMp: "?m \<le> Lng ?Mp - 1"
  proof -
    have "j1red - j0red \<le> j1' - j0'" using j1redspan j0j1red by linarith
    thus ?thesis using LMp j0le by linarith
  qed
  have leRMp: "leR ?Mp 0 0 (Lng ?Mp - 1)" using le0Mp by (simp add: leR_def)
  have le0Mpm: "le0 ?Mp 0 ?m"
  proof -
    have "leR ?Mp 0 0 ?m"
      by (rule m_5_1_ancestor_tree_1[OF MpT leRMp zero_le mleMp])
    thus ?thesis by (simp add: leR_def)
  qed
  \<comment> \<open>\<open>+shamt\<close> row-0 agreement on \<open>[0,m]\<close>: \<open>entry M' 0 j = entry Np 0 j + shamt\<close>\<close>
  have agree: "\<And>j. j \<le> ?m \<Longrightarrow> entry ?Mp 0 j = entry ?Np 0 j + shamt"
  proof -
    fix j assume jm: "j \<le> ?m"
    have jlt: "j < Suc j1' - j0'" using jm mleMp LMp j0le lt by linarith
    have jltN: "j < Suc j1red - j0red" using jm j0j1red by linarith
    have eMp: "entry ?Mp 0 j = entry M 0 (j0' + j)"
      using jlt by (simp add: entry_def seg_nth_eq)
    have eNp: "entry ?Np 0 j = entry N 0 (j0red + j)"
      using jltN by (simp add: entry_def seg_nth_eq)
    have jval: "j0' + j < Lng ((N::pairseq)[n])"
    proof -
      have "j \<le> j1' - j0'" using jm j1redspan j0j1red by linarith
      hence "j0' + j \<le> j1'" using j0le by linarith
      thus ?thesis using jM Neq lt by simp
    qed
    have j0redlej1red0: "j0red \<le> j1red" using j0j1red by simp
    have "entry ((N::pairseq)[n]) 0 (j0' + j) = entry N 0 (j0red + j) + shamt"
      by (rule oper_d1pos_period_row0_unif[OF L notzero hp i1z j0lt q0n s0lt
            j0reds j0'eq shamt j1redle j0redlej1red0 jval jm])
    thus "entry ?Mp 0 j = entry ?Np 0 j + shamt" using eMp eNp Neq by simp
  qed
  \<comment> \<open>transfer \<open>le0 M' 0 m \<to> le0 Np 0 m\<close>\<close>
  have mMp: "?m < Lng ?Mp" using mleMp LMp lt by linarith
  have LNp: "Lng ?Np = Suc j1red - j0red" by simp
  have mNp: "?m < Lng ?Np" using LNp j0j1red by linarith
  have le0Npm: "le0 ?Np 0 ?m"
    by (rule le0_prefix_row0_shift[OF agree mMp mNp zero_le order.refl le0Mpm])
  \<comment> \<open>lift the slice \<open>le0 Np 0 m\<close> to \<open>le0 N j0red j1red\<close> via @{thm [source] adm_le0_seg}\<close>
  have j1redltN: "j1red < Lng N" using j1redle L by linarith
  have j0redlej1red: "j0red \<le> j1red" using j0j1red by simp
  have ale: "(0::nat) \<le> j1red - j0red" by simp
  have ble: "?m \<le> j1red - j0red" by simp
  have admiff: "le0 ?Np 0 ?m = le0 N (j0red + 0) (j0red + ?m)"
    by (rule adm_le0_seg[OF j1redltN ale ble j0redlej1red])
  have "le0 N (j0red + 0) (j0red + ?m)" using admiff le0Npm by simp
  hence "le0 N j0red j1red" using j0redlej1red by simp
  thus ?thesis .
qed

text \<open>§6.8 d1pos CAPPED BOUNDARY STOP — DIRECT producer of the \<open>stop\<close> hypothesis
  that the four cell-assembly lemmas and every \<open>TrMax_seg_oper_d1pos_eq\<close> variant
  carry.  Target (the exact form the cells need):
  \<open>\<not> nextR (seg (N[n]) j'\<^sub>0 j'\<^sub>1) 1 (TrMax N\<^sub>red) (TrMax N\<^sub>red + 1)\<close>,
  \<open>N\<^sub>red = seg N j\<^sub>0\<^sup>red (Lng N-1)\<close> (capped, \<open>j\<^sub>1\<^sup>red = Lng N-1\<close>).

  This breaks the genuine cycle the capstone hits (\<open>stop \<leftarrow> strict-tnc \<leftarrow>
  notbrleNp \<leftarrow> stop\<close>): it produces \<open>stop\<close> WITHOUT routing through
  @{thm [source] TrMax_seg_oper_d1pos_eq_span} / \<open>notbrleNp\<close> / the M-side
  strict-tnc.  The only intermediate it uses is the contrapositive trunk-
  confinement @{thm [source] oper_d1pos_ctx_tnc_capped} (\<open>tnc : TrMax N\<^sub>red \<le> c\<close>,
  \<open>c = j\<^sub>1\<^sup>red - 1 - j\<^sub>0\<^sup>red = Lng N\<^sub>red - 2\<close>), itself the contrapositive of the green
  @{thm [source] TrMax_seg_oper_d1pos_brle_capped} — NO circularity.

  Proof: the stop index \<open>TrMax N\<^sub>red + 1\<close>; the period-shifted reference
  \<open>N\<^sub>pp = (IncrFirst\<^bsup>shamt\<^esup>) N\<^sub>red\<close> agrees with \<open>M'\<close> on \<open>[0,c]\<close> (identical to the
  \<open>_eq_span\<close> agreement) and has \<open>TrMax N\<^sub>pp = TrMax N\<^sub>red\<close>.  Two cases on \<open>TrMax N\<^sub>red\<close>:
  \<^item> EASY (\<open>TrMax N\<^sub>red < c\<close>): the stop index \<open>TrMax N\<^sub>red + 1 \<le> c\<close> lies in the
    shared prefix, so @{thm [source] nextR1_boundary_stop_of_prefix} transfers the
    \<open>N\<^sub>pp\<close>-side stop (@{thm [source] TrMax_stop}).  This is the ONLY branch that fires
    in-context (the strict-2 confinement holds 1612/1612, rank 10).
  \<^item> HARD (\<open>TrMax N\<^sub>red = c\<close>, the period boundary \<open>TrMax N\<^sub>red + 1 = c+1 = Lng N\<^sub>red - 1\<close>):
    the row-1 step at \<open>c\<close> in \<open>M'\<close> is a NON-increase = boundary B3N.  \<open>entry M' 1 c =
    N\<^bsub>1,Lng N-2\<^esub>\<close> (block \<open>q\<close>, offset \<open>w-1\<close>) and \<open>entry M' 1 (c+1) = N\<^bsub>1,j\<^sub>-\<^sub>2\<^sup>N\<^esub>\<close>
    (block \<open>q+1\<close>, offset 0; \<open>oper_d1pos_entry1\<close>, \<open>q+1<n\<close> from the cap).  B3N
    \<open>N\<^bsub>1,j\<^sub>-\<^sub>2\<^sup>N\<^esub> \<le> N\<^bsub>1,Lng N-2\<^esub>\<close> here splits CLEANLY (no fill needed):
    \<^item> \<open>gap : N\<^bsub>1,j\<^sub>-\<^sub>2\<^sup>N\<^esub> \<le> N\<^bsub>1,j\<^sub>0\<^sup>red\<^esub>\<close> — \<open>j\<^sub>-\<^sub>2\<^sup>N \<le> j\<^sub>0\<^sup>red\<close>; if equal, reflexive, else the
      \<open>nextrel1 N j\<^sub>-\<^sub>2\<^sup>N (Lng N-1)\<close> parent MINIMALITY at \<open>j\<^sub>0\<^sup>red\<close>
      (\<open>le0 N j\<^sub>0\<^sup>red (Lng N-1)\<close> from \<open>N\<^sub>red\<close> monoT) gives \<open>N\<^bsub>1,Lng N-1\<^esub> \<le> N\<^bsub>1,j\<^sub>0\<^sup>red\<^esub>\<close>,
      and \<open>N\<^bsub>1,j\<^sub>-\<^sub>2\<^sup>N\<^esub> < N\<^bsub>1,Lng N-1\<^esub>\<close> (H1) chains.
    \<^item> \<open>sub1 : N\<^bsub>1,j\<^sub>0\<^sup>red\<^esub> \<le> N\<^bsub>1,Lng N-2\<^esub>\<close> — the near-fill \<open>N\<^sub>red\<close>-trunk reaches node
      \<open>c = Lng N\<^sub>red - 2\<close>, so \<open>le1 N\<^sub>red 0 c\<close> (@{thm [source] trunk_le1}) and
      @{thm [source] le1_imp_entry1_le}.
    The HARD branch never fires in-context (it is the contradiction case excluded
    by the strict-2 confinement), but is required because \<open>tnc\<close> gives only \<open>\<le> c\<close>.
  DEEP-VERIFIED rank 10 (rank-stratified \<open>gen_std\<close> = diagSeq\<rightarrow>oper-closure\<rightarrow>
  is_standard; \<open>python/d1pos_capped_stop_probe.py\<close>, \<open>d1pos_capped_idx_probe.py\<close>):
  exact stop 1612/1612 capped \<open>\<not>brle\<close> cases; EASY=1612 HARD=0; in every case the
  failing \<open>nextrel1\<close> disjunct is the row-1 non-increase (row1 1612/1612); the EASY
  route (N-side stop & \<open>[0,c]\<close> agreement & \<open>t+1\<le>c\<close>) 1612/1612, and the HARD route
  (gap & sub1 & B3N) holds on the pure-\<open>N\<close> near-fill instances 28/28.\<close>

lemma oper_d1pos_ctx_stop_direct:
  fixes N :: pairseq
  assumes N: "N \<in> T_PS" and monoN: "monoT N" and std: "N \<in> ST_PS"
    and L: "1 < Lng N"
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
    and cap: "j1red = Lng N - 1"
    and j1redspan: "j1red < j0red + (j1' - j0')"
    and j0j1': "j0' < j1'"
    and j1lt: "j1' < Lng ((N::pairseq)[n])"
    and le0M: "le0 ((N::pairseq)[n]) j0' j1'"
    and notbrle: "\<not> (TrMax (seg ((N::pairseq)[n]) j0' j1')
                        = Lng (seg ((N::pairseq)[n]) j0' j1') - 1
                      \<or> le0 (seg ((N::pairseq)[n]) j0' j1')
                            (TrMax (seg ((N::pairseq)[n]) j0' j1') + 1)
                            (Lng (seg ((N::pairseq)[n]) j0' j1') - 1))"
  shows "\<not> nextR (seg ((N::pairseq)[n]) j0' j1') 1
            (TrMax (seg N j0red j1red))
            (TrMax (seg N j0red j1red) + 1)"
proof -
  let ?M = "(N::pairseq)[n]"
  let ?j1N = "Lng N - 1"
  let ?j0 = "parent N 1 ?j1N"
  let ?w = "?j1N - ?j0"
  let ?delta = "entry N 0 ?j1N - entry N 0 ?j0"
  let ?Mp = "seg ?M j0' j1'"
  let ?Np = "seg N j0red j1red"
  let ?Npp = "(IncrFirst ^^ shamt) ?Np"
  let ?c = "j1red - 1 - j0red"
  let ?t = "TrMax ?Np"
  \<comment> \<open>(tnc) reduced-trunk confinement, the contrapositive of \<open>_brle_capped\<close>\<close>
  have tnc: "?t \<le> ?c"
    by (rule oper_d1pos_ctx_tnc_capped[OF N monoN std L notzero hp i1z j0lt n1 qn
          s0w s0eq s0lt j0'eq shamt j1redle j0j1red cap j1redspan j0j1' j1lt notbrle])
  \<comment> \<open>basic facts\<close>
  have j0'le: "j0' \<le> j1'" using j0j1' by linarith
  have MpT: "?Mp \<in> T_PS" using j0'le by (simp add: T_PS_def seg_def)
  have NpT: "?Np \<in> T_PS" using j0j1red by (simp add: T_PS_def seg_def)
  have NppT: "?Npp \<in> T_PS"
  proof -
    have "?Np \<in> T_PS" using j0j1red by (simp add: T_PS_def seg_def)
    thus ?thesis by (induction shamt) (simp_all add: T_PS_def IncrFirst_def)
  qed
  have LMp: "Lng ?Mp = Suc j1' - j0'" by simp
  have LNp: "Lng ?Np = Suc j1red - j0red" by simp
  have LNpp: "Lng ?Npp = Suc j1red - j0red" by simp
  have trShift: "TrMax ?Npp = TrMax ?Np" by (rule TrMax_funpow_IncrFirst)
  have cLNp: "?c = Lng ?Np - 2" using LNp j0j1red by linarith
  have cN: "?c < Lng ?Npp" using LNpp j0j1red by linarith
  have tNlt: "TrMax ?Npp < Lng ?Npp - 1" using tnc cLNp LNpp LNp j0j1red trShift by linarith
  \<comment> \<open>\<open>c < Lng M'\<close>: the slice crosses the block boundary (capped span overshoots)\<close>
  obtain D where Ddef: "D = j1' - j0'" by blast
  obtain E where Edef: "E = j1red - j0red" by blast
  have Dgt: "0 < D" using Ddef j0j1' by linarith
  have spanE: "E < D" using Edef Ddef j1redspan j0j1red by linarith
  have cE: "?c = E - 1" using Edef by simp
  have LMpD: "Lng ?Mp = Suc D" using LMp Ddef j0j1' by linarith
  have cM: "?c < Lng ?Mp"
  proof -
    have "?c < E" using cE Edef j0j1red by linarith
    also have "E < D" by (rule spanE)
    also have "D < Suc D" by simp
    finally show ?thesis using LMpD by simp
  qed
  have cMlt: "?c + 1 < Lng ?Mp"
  proof -
    have "?c + 1 = E" using cE Edef j0j1red by linarith
    also have "E < D" by (rule spanE)
    also have "D < Suc D" by simp
    finally show ?thesis using LMpD by simp
  qed
  \<comment> \<open>pointwise agreement on \<open>[0,c]\<close> (identical to the \<open>_eq_span\<close> keystone)\<close>
  have agree: "\<And>s. s \<le> ?c \<Longrightarrow> ?Mp ! s = ?Npp ! s"
  proof -
    fix s assume sc: "s \<le> ?c"
    have sM: "s < Suc j1' - j0'" using sc cM LMp by linarith
    have sNp: "s < Suc j1red - j0red" using sc cN LNpp by linarith
    have s0sw: "s0 + s < ?w"
    proof -
      have "j0red + s \<le> j1red - 1" using sc j0j1red by linarith
      hence "?j0 + s0 + s \<le> ?j1N - 1" using s0eq j1redle j0j1red by linarith
      thus ?thesis using j0lt by linarith
    qed
    have lhs_idx: "j0' + s = ?j0 + q * ?w + (s0 + s)" using j0'eq by (simp add: add.assoc)
    have "?Mp ! s = ?M ! (j0' + s)" using sM by (rule seg_nth_eq)
    also have "\<dots> = ?M ! (?j0 + q * ?w + (s0 + s))" by (rule arg_cong[OF lhs_idx, of "(!) ?M"])
    also have "\<dots> = (entry N 0 (?j0 + (s0 + s)) + q * ?delta, entry N 1 (?j0 + (s0 + s)))"
      by (rule oper_d1pos_nth[OF L notzero hp i1z j0lt qn s0sw])
    finally have LHS: "?Mp ! s = (entry N 0 (?j0 + (s0 + s)) + shamt, entry N 1 (?j0 + (s0 + s)))"
      using shamt by simp
    have ii: "s < Lng ?Np" using sNp by simp
    have R0: "entry ?Npp 0 s = entry ?Np 0 s + shamt"
      by (rule entry_funpow_IncrFirst0[OF ii])
    have R1: "entry ?Npp 1 s = entry ?Np 1 s"
      by (rule entry_funpow_IncrFirst1[OF ii])
    have segN0: "entry ?Np 0 s = entry N 0 (?j0 + (s0 + s))"
    proof -
      have "?Np ! s = N ! (j0red + s)" using sNp by (rule seg_nth_eq)
      thus ?thesis using s0eq by (simp add: entry_def add.assoc)
    qed
    have segN1: "entry ?Np 1 s = entry N 1 (?j0 + (s0 + s))"
    proof -
      have "?Np ! s = N ! (j0red + s)" using sNp by (rule seg_nth_eq)
      thus ?thesis using s0eq by (simp add: entry_def add.assoc)
    qed
    have ilenpp: "s < length ?Npp" using LNpp sNp by simp
    have "?Npp ! s = (entry ?Npp 0 s, entry ?Npp 1 s)"
      using ilenpp by (cases "?Npp ! s") (simp add: entry_def)
    also have "\<dots> = (entry N 0 (?j0 + (s0 + s)) + shamt, entry N 1 (?j0 + (s0 + s)))"
      using R0 R1 segN0 segN1 by simp
    finally have RHS: "?Npp ! s = (entry N 0 (?j0 + (s0 + s)) + shamt, entry N 1 (?j0 + (s0 + s)))" .
    show "?Mp ! s = ?Npp ! s" using LHS RHS by simp
  qed
  \<comment> \<open>========== the two cases on \<open>TrMax N\<^sub>red\<close> ==========\<close>
  show ?thesis
  proof (cases "?t < ?c")
    case easy: True
    \<comment> \<open>stop index inside the shared prefix: transfer the \<open>N\<^sub>pp\<close>-side stop\<close>
    have inrange: "TrMax ?Npp + 1 \<le> ?c" using easy trShift by linarith
    have stopShift: "\<not> nextR ?Mp 1 (TrMax ?Npp) (TrMax ?Npp + 1)"
      by (rule nextR1_boundary_stop_of_prefix[OF MpT NppT agree cM cN tNlt inrange])
    show ?thesis using stopShift trShift by simp
  next
    case hard: False
    have teq: "?t = ?c" using tnc hard by linarith
    \<comment> \<open>HARD: \<open>?t + 1 = c+1\<close> at the block boundary; the row-1 step \<open>c \<to> c+1\<close> fails (B3N)\<close>
    \<comment> \<open>boundary index identities (mirroring \<open>_brle_capped\<close>)\<close>
    have w0: "0 < ?w" using j0lt by linarith
    have s0w': "s0 < ?w" using s0lt .
    obtain w where wdef: "?w = w" by blast
    have blockstep: "?j0 + q * ?w + ?w = ?j0 + (q + 1) * ?w"
    proof -
      have "?j0 + q * w + w = ?j0 + (q + 1) * w" by (simp add: algebra_simps)
      thus ?thesis using wdef by simp
    qed
    have LngMn: "Lng ?M = ?j0 + n * ?w"
      by (rule oper_d1pos_LngM[OF L notzero hp i1z j0lt])
    have s0c1: "s0 + (?c + 1) = ?w"
    proof -
      have e: "?c + 1 = ?j1N - j0red" using cap j0j1red by linarith
      have "s0 + (?c + 1) = s0 + (?j1N - (?j0 + s0))" using e s0eq by simp
      also have "\<dots> = ?j1N - ?j0" using s0w' j0lt by linarith
      finally show ?thesis .
    qed
    have idx_c1: "j0' + (?c + 1) = ?j0 + (q + 1) * ?w"
    proof -
      have step1: "j0' + (?c + 1) = ?j0 + q * ?w + (s0 + (?c + 1))" using j0'eq by (simp add: add.assoc)
      have step2: "?j0 + q * ?w + (s0 + (?c + 1)) = ?j0 + q * ?w + ?w"
        by (rule arg_cong[OF s0c1, of "\<lambda>z. ?j0 + q * ?w + z"])
      from step1 step2 have "j0' + (?c + 1) = ?j0 + q * ?w + ?w" by (rule trans)
      from this blockstep show ?thesis by (rule trans)
    qed
    have qn1lt: "?j0 + (q + 1) * ?w < ?j0 + n * ?w"
    proof -
      have "j0' + (?c + 1) \<le> j1'" using cMlt LMp by linarith
      hence "?j0 + (q + 1) * ?w \<le> j1'" using idx_c1 by simp
      also have "j1' < Lng ?M" by (rule j1lt)
      finally show ?thesis using LngMn by simp
    qed
    have qn1: "q + 1 < n"
    proof -
      have "?j0 + (q + 1) * w < ?j0 + n * w" using qn1lt wdef by simp
      hence "(q + 1) * w < n * w" by simp
      moreover have "0 < w" using w0 wdef by simp
      ultimately show ?thesis using mult_less_cancel2[of "q+1" w n] by simp
    qed
    \<comment> \<open>\<open>entry M' 1 (c+1) = entry N 1 j\<^sub>-\<^sub>2\<^sup>N\<close> (block \<open>q+1\<close>, offset \<open>0\<close>)\<close>
    have e1_c1: "entry ?Mp 1 (?c + 1) = entry N 1 ?j0"
    proof -
      have "entry ?Mp 1 (?c + 1) = entry ?M 1 (j0' + (?c + 1))"
        using cMlt by (simp add: entry_seg)
      also have "\<dots> = entry ?M 1 (?j0 + (q + 1) * ?w + 0)" using idx_c1 by simp
      also have "\<dots> = entry N 1 (?j0 + 0)"
        by (rule oper_d1pos_entry1[OF L notzero hp i1z j0lt qn1 w0])
      finally show ?thesis by simp
    qed
    \<comment> \<open>\<open>entry M' 1 c = entry N 1 (Lng N-2)\<close> (block \<open>q\<close>, offset \<open>w-1\<close>)\<close>
    have s0c: "s0 + ?c = ?w - 1" using s0c1 w0 by linarith
    have idx_c: "j0' + ?c = ?j0 + q * ?w + (?w - 1)"
    proof -
      have step1: "j0' + ?c = ?j0 + q * ?w + (s0 + ?c)" using j0'eq by (simp add: add.assoc)
      have step2: "?j0 + q * ?w + (s0 + ?c) = ?j0 + q * ?w + (?w - 1)"
        by (rule arg_cong[OF s0c, of "\<lambda>z. ?j0 + q * ?w + z"])
      show ?thesis using step1 step2 by (rule trans)
    qed
    have wm1w: "?w - 1 < ?w"
    proof -
      have "w - 1 < w" using w0 wdef by simp
      thus ?thesis using wdef by simp
    qed
    have j0le1N: "?j0 \<le> ?j1N" by (rule less_imp_le[OF j0lt])
    have j0w: "?j0 + ?w = ?j1N" using le_add_diff_inverse[OF j0le1N] .
    have j0wm1: "?j0 + (?w - 1) = ?j1N - 1"
    proof -
      have "?j0 + (?w - 1) = ?j0 + ?w - 1" using w0 by simp
      also have "\<dots> = ?j1N - 1" using j0w by simp
      finally show ?thesis .
    qed
    have e1_c: "entry ?Mp 1 ?c = entry N 1 (?j1N - 1)"
    proof -
      have "entry ?Mp 1 ?c = entry ?M 1 (j0' + ?c)"
        using cM by (simp add: entry_seg)
      also have "\<dots> = entry ?M 1 (?j0 + q * ?w + (?w - 1))" using idx_c by simp
      also have "\<dots> = entry N 1 (?j0 + (?w - 1))"
        by (rule oper_d1pos_entry1[OF L notzero hp i1z j0lt qn wm1w])
      also have "\<dots> = entry N 1 (?j1N - 1)" using j0wm1 by simp
      finally show ?thesis .
    qed
    \<comment> \<open>========== B3N: \<open>entry N 1 j\<^sub>-\<^sub>2\<^sup>N \<le> entry N 1 (Lng N-2)\<close> via gap + sub1 ==========\<close>
    \<comment> \<open>parent relation \<open>nextrel1 N j\<^sub>-\<^sub>2\<^sup>N (Lng N-1)\<close>: H1 + minimality\<close>
    have haspar1: "hasParent N 1 ?j1N" using hp i1z by simp
    have parR1: "nextR N 1 ?j0 ?j1N"
      using haspar1 unfolding hasParent_def parent_def by (rule theI')
    have nr1: "nextrel1 N ?j0 ?j1N" using parR1 by (simp add: nextR_def)
    have H1: "entry N 1 ?j0 < entry N 1 ?j1N" using nr1 by (simp add: nextrel1_def)
    have minim: "\<And>j. ?j0 < j \<Longrightarrow> le0 N j ?j1N \<Longrightarrow> entry N 1 ?j1N \<le> entry N 1 j"
      using nr1 by (simp add: nextrel1_def)
    \<comment> \<open>\<open>gap : entry N 1 j\<^sub>-\<^sub>2\<^sup>N \<le> entry N 1 j\<^sub>0\<^sup>red\<close>; \<open>j\<^sub>-\<^sub>2\<^sup>N \<le> j\<^sub>0\<^sup>red\<close> from \<open>s0eq\<close>\<close>
    have j0red_ge: "?j0 \<le> j0red" using s0eq by simp
    \<comment> \<open>\<open>le0 N j\<^sub>0\<^sup>red (Lng N-1)\<close>: cell-4 \<open>le0Np\<close> discharger from the consumer \<open>le0 M' \<close>\<close>
    have le0red: "le0 N j0red ?j1N"
    proof -
      have "le0 N j0red j1red"
        by (rule oper_d1pos_ctx_period_le0Np[OF L notzero hp i1z j0lt refl le0M
              j0j1' j1lt qn s0lt s0eq j0'eq shamt j1redle j0j1red
              less_imp_le[OF j1redspan]])
      thus ?thesis using cap by simp
    qed
    have gap: "entry N 1 ?j0 \<le> entry N 1 j0red"
    proof (cases "?j0 = j0red")
      case True thus ?thesis by simp
    next
      case False
      hence lt: "?j0 < j0red" using j0red_ge by linarith
      have "entry N 1 ?j1N \<le> entry N 1 j0red" by (rule minim[OF lt le0red])
      thus ?thesis using H1 by linarith
    qed
    \<comment> \<open>\<open>sub1 : entry N 1 j\<^sub>0\<^sup>red \<le> entry N 1 (Lng N-2)\<close> from the near-fill \<open>N\<^sub>red\<close>-trunk\<close>
    have cleNp: "?c \<le> TrMax ?Np" using teq by simp
    have le1Np: "le1 ?Np 0 ?c" using trunk_le1[OF NpT zero_le cleNp] by (simp add: leR_def)
    have e_Np0: "entry ?Np 1 0 = entry N 1 j0red"
    proof -
      have "0 < Lng ?Np" using j0j1red by simp
      hence "?Np ! 0 = N ! j0red" by (simp add: seg_nth_eq)
      thus ?thesis by (simp add: entry_def)
    qed
    have e_Npc: "entry ?Np 1 ?c = entry N 1 (?j1N - 1)"
    proof -
      have cltNp: "?c < Suc j1red - j0red" using j0j1red by linarith
      have jc: "j0red + ?c = ?j1N - 1"
      proof -
        have "j0red + ?c = ?j0 + (s0 + ?c)" using s0eq by simp
        also have "\<dots> = ?j0 + (?w - 1)" using s0c by simp
        also have "\<dots> = ?j1N - 1" using j0wm1 by simp
        finally show ?thesis .
      qed
      have "?Np ! ?c = N ! (j0red + ?c)" using cltNp by (rule seg_nth_eq)
      thus ?thesis using jc by (simp add: entry_def)
    qed
    have sub1: "entry N 1 j0red \<le> entry N 1 (?j1N - 1)"
    proof -
      have "entry ?Np 1 0 \<le> entry ?Np 1 ?c"
        by (rule le1_imp_entry1_le[OF le1Np])
      thus ?thesis using e_Np0 e_Npc by simp
    qed
    have B3N: "entry N 1 ?j0 \<le> entry N 1 (?j1N - 1)" using gap sub1 by linarith
    \<comment> \<open>boundary row-1 NON-increase in \<open>M'\<close>, hence the stop at \<open>c = ?t\<close>\<close>
    have B3: "entry ?Mp 1 (?c + 1) \<le> entry ?Mp 1 ?c" using B3N e1_c1 e1_c by simp
    show ?thesis
    proof
      assume "nextR ?Mp 1 ?t (?t + 1)"
      hence "nextrel1 ?Mp ?c (?c + 1)" using teq by (simp add: nextR_def)
      hence "entry ?Mp 1 ?c < entry ?Mp 1 (?c + 1)" by (simp add: nextrel1_def)
      thus False using B3 by simp
    qed
  qed
qed


text \<open>§6.8 d1pos CELL-4 (PERIODIC-TAIL) UNCAPPED stop, STRICT variant of
  @{thm [source] oper_d1pos_ctx_stop_direct}.  The capped sibling REQUIRES
  \<open>j\<^sub>1\<^sup>red = Lng N-1\<close> (\<open>cap\<close>), but ~78/164 in-context periodic cases are UNCAPPED
  (\<open>j\<^sub>1\<^sup>red = j\<^sub>0\<^sup>red + (j'\<^sub>1-j'\<^sub>0) < Lng N-1\<close>, the slice ends strictly inside a block).
  KEY EMPIRICAL FINDING (deep-verified, rank \<ge> 10): ALL uncapped periodic cases
  satisfy the STRICT trunk-confinement \<open>TrMax N\<^sub>red < c = j\<^sub>1\<^sup>red-1-j\<^sub>0\<^sup>red\<close> (0 in the
  HARD/boundary branch), because the reduced trunk is strictly short.  So this
  variant DROPS \<open>cap\<close>, takes \<open>span : j\<^sub>1\<^sup>red = j\<^sub>0\<^sup>red + (j'\<^sub>1-j'\<^sub>0)\<close> (uncapped) and the
  strict hypothesis \<open>tncstrict : TrMax N\<^sub>red < c\<close>, and closes via the EASY branch of
  @{thm [source] oper_d1pos_ctx_stop_direct} ONLY (the period-shifted reference
  \<open>N\<^sub>pp = (IncrFirst\<^bsup>shamt\<^esup>) N\<^sub>red\<close> agrees with \<open>M'\<close> on \<open>[0,c]\<close>, has
  \<open>TrMax N\<^sub>pp = TrMax N\<^sub>red\<close>, and the stop index \<open>TrMax N\<^sub>red + 1 \<le> c\<close> lies in the
  shared prefix, so @{thm [source] nextR1_boundary_stop_of_prefix} transfers the
  \<open>N\<^sub>pp\<close>-side stop @{thm [source] TrMax_stop}).  The EASY branch never uses \<open>cap\<close>;
  the only place stop_direct uses \<open>cap\<close> is its HARD branch, which the strict
  hypothesis excludes.  NO circularity: \<open>tncstrict\<close> is supplied by the caller (the
  uncapped TrEq route @{thm [source] TrMax_seg_oper_d1pos_eq_notbrle_uncapped},
  which derives the M-side stop internally for the uncapped span).\<close>

lemma oper_d1pos_ctx_stop_direct_strict:
  fixes N :: pairseq
  assumes N: "N \<in> T_PS" and monoN: "monoT N" and std: "N \<in> ST_PS"
    and L: "1 < Lng N"
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
    and span: "j1red = j0red + (j1' - j0')"
    and j0j1': "j0' < j1'"
    and j1lt: "j1' < Lng ((N::pairseq)[n])"
    and tncstrict: "TrMax (seg N j0red j1red) < j1red - 1 - j0red"
  shows "\<not> nextR (seg ((N::pairseq)[n]) j0' j1') 1
            (TrMax (seg N j0red j1red))
            (TrMax (seg N j0red j1red) + 1)"
proof -
  let ?M = "(N::pairseq)[n]"
  let ?j1N = "Lng N - 1"
  let ?j0 = "parent N 1 ?j1N"
  let ?w = "?j1N - ?j0"
  let ?delta = "entry N 0 ?j1N - entry N 0 ?j0"
  let ?Mp = "seg ?M j0' j1'"
  let ?Np = "seg N j0red j1red"
  let ?Npp = "(IncrFirst ^^ shamt) ?Np"
  let ?c = "j1red - 1 - j0red"
  let ?t = "TrMax ?Np"
  \<comment> \<open>basic facts\<close>
  have j0'le: "j0' \<le> j1'" using j0j1' by linarith
  have MpT: "?Mp \<in> T_PS" using j0'le by (simp add: T_PS_def seg_def)
  have NpT: "?Np \<in> T_PS" using j0j1red by (simp add: T_PS_def seg_def)
  have NppT: "?Npp \<in> T_PS"
  proof -
    have "?Np \<in> T_PS" using j0j1red by (simp add: T_PS_def seg_def)
    thus ?thesis by (induction shamt) (simp_all add: T_PS_def IncrFirst_def)
  qed
  have LMp: "Lng ?Mp = Suc j1' - j0'" by simp
  have LNp: "Lng ?Np = Suc j1red - j0red" by simp
  have LNpp: "Lng ?Npp = Suc j1red - j0red" by simp
  have trShift: "TrMax ?Npp = TrMax ?Np" by (rule TrMax_funpow_IncrFirst)
  \<comment> \<open>UNCAPPED span (like @{thm [source] TrMax_seg_oper_d1pos_eq_notbrle_uncapped}): \<open>c = Lng M' - 2\<close>\<close>
  have spanD: "j1' - j0' = j1red - j0red" using span j0j1red by linarith
  have cLMp: "?c = Lng ?Mp - 2" using spanD j0j1red j0j1' LMp by linarith
  have cM: "?c < Lng ?Mp" using cLMp LMp j0j1' by linarith
  have cMlt: "?c + 1 < Lng ?Mp" using cLMp LMp j0j1' by linarith
  have cN: "?c < Lng ?Npp" using LNpp j0j1red by linarith
  have tNlt: "TrMax ?Npp < Lng ?Npp - 1"
    using tncstrict LNpp j0j1red trShift by linarith
  \<comment> \<open>pointwise agreement on \<open>[0,c]\<close> (identical to stop_direct / the \<open>_eq_span\<close> keystone)\<close>
  have agree: "\<And>s. s \<le> ?c \<Longrightarrow> ?Mp ! s = ?Npp ! s"
  proof -
    fix s assume sc: "s \<le> ?c"
    have sM: "s < Suc j1' - j0'" using sc cM LMp by linarith
    have sNp: "s < Suc j1red - j0red" using sc cN LNpp by linarith
    have s0sw: "s0 + s < ?w"
    proof -
      have "j0red + s \<le> j1red - 1" using sc j0j1red by linarith
      hence "?j0 + s0 + s \<le> ?j1N - 1" using s0eq j1redle j0j1red by linarith
      thus ?thesis using j0lt by linarith
    qed
    have lhs_idx: "j0' + s = ?j0 + q * ?w + (s0 + s)" using j0'eq by (simp add: add.assoc)
    have "?Mp ! s = ?M ! (j0' + s)" using sM by (rule seg_nth_eq)
    also have "\<dots> = ?M ! (?j0 + q * ?w + (s0 + s))" by (rule arg_cong[OF lhs_idx, of "(!) ?M"])
    also have "\<dots> = (entry N 0 (?j0 + (s0 + s)) + q * ?delta, entry N 1 (?j0 + (s0 + s)))"
      by (rule oper_d1pos_nth[OF L notzero hp i1z j0lt qn s0sw])
    finally have LHS: "?Mp ! s = (entry N 0 (?j0 + (s0 + s)) + shamt, entry N 1 (?j0 + (s0 + s)))"
      using shamt by simp
    have ii: "s < Lng ?Np" using sNp by simp
    have R0: "entry ?Npp 0 s = entry ?Np 0 s + shamt"
      by (rule entry_funpow_IncrFirst0[OF ii])
    have R1: "entry ?Npp 1 s = entry ?Np 1 s"
      by (rule entry_funpow_IncrFirst1[OF ii])
    have segN0: "entry ?Np 0 s = entry N 0 (?j0 + (s0 + s))"
    proof -
      have "?Np ! s = N ! (j0red + s)" using sNp by (rule seg_nth_eq)
      thus ?thesis using s0eq by (simp add: entry_def add.assoc)
    qed
    have segN1: "entry ?Np 1 s = entry N 1 (?j0 + (s0 + s))"
    proof -
      have "?Np ! s = N ! (j0red + s)" using sNp by (rule seg_nth_eq)
      thus ?thesis using s0eq by (simp add: entry_def add.assoc)
    qed
    have ilenpp: "s < length ?Npp" using LNpp sNp by simp
    have "?Npp ! s = (entry ?Npp 0 s, entry ?Npp 1 s)"
      using ilenpp by (cases "?Npp ! s") (simp add: entry_def)
    also have "\<dots> = (entry N 0 (?j0 + (s0 + s)) + shamt, entry N 1 (?j0 + (s0 + s)))"
      using R0 R1 segN0 segN1 by simp
    finally have RHS: "?Npp ! s = (entry N 0 (?j0 + (s0 + s)) + shamt, entry N 1 (?j0 + (s0 + s)))" .
    show "?Mp ! s = ?Npp ! s" using LHS RHS by simp
  qed
  \<comment> \<open>EASY branch ONLY: stop index inside the shared prefix (strict-tnc \<Longrightarrow> no HARD case)\<close>
  have easy: "?t < ?c" using tncstrict by simp
  have inrange: "TrMax ?Npp + 1 \<le> ?c" using easy trShift by linarith
  have stopShift: "\<not> nextR ?Mp 1 (TrMax ?Npp) (TrMax ?Npp + 1)"
    by (rule nextR1_boundary_stop_of_prefix[OF MpT NppT agree cM cN tNlt inrange])
  show ?thesis using stopShift trShift by simp
qed


text \<open>§6.8 d1pos CELL-4 (PERIODIC-TAIL) UNCAPPED STRICT-tnc discharger.  Supplies
  the strict trunk-confinement \<open>tncstrict : TrMax (seg N j\<^sub>0\<^sup>red j\<^sub>1\<^sup>red)
  < j\<^sub>1\<^sup>red - 1 - j\<^sub>0\<^sup>red\<close> that @{thm [source] oper_d1pos_ctx_stop_direct_strict} needs,
  for the UNCAPPED periodic context (\<open>j\<^sub>1\<^sup>red = j\<^sub>0\<^sup>red + (j'\<^sub>1-j'\<^sub>0) < Lng N-1\<close>: the slice
  ends strictly inside a block, so the reduced trunk is strictly short).  Route
  (the SAME one as @{thm [source] TrMax_seg_oper_d1pos_brle_uncapped}, but yielding
  STRICT confinement instead of a contradiction):
  \<^item> the two \<open>\<not>brle (M')\<close> conjuncts \<open>Mlt : TrMax M' < Lng M'-1\<close> (1st conjunct +
    @{thm [source] TrMax_bound}) and \<open>notle : \<not>le0 M' (TrMax M'+1)(Lng M'-1)\<close>
    (2nd conjunct) give \<open>TrMax M' + 1 \<le> Lng M' - 2\<close> (the \<open>tncM1\<close> block of
    @{thm [source] TrMax_seg_oper_d1pos_eq_notbrle_uncapped}: if \<open>TrMax M'+1 = Lng M'-1\<close>
    then @{thm [source] le0_refl} contradicts \<open>notle\<close>);
  \<^item> the uncapped keystone @{thm [source] TrMax_seg_oper_d1pos_eq_notbrle_uncapped}
    (which derives the M-side stop INTERNALLY for the uncapped span) gives
    \<open>TrEq : TrMax M' = TrMax N\<^sub>red\<close>;
  \<^item> the uncapped span gives \<open>LenEq : Lng N\<^sub>red = Lng M'\<close>, so \<open>j\<^sub>1\<^sup>red-1-j\<^sub>0\<^sup>red =
    Lng N\<^sub>red - 2 = Lng M' - 2\<close>, and \<open>TrMax N\<^sub>red = TrMax M' \<le> Lng M'-3 < Lng M'-2\<close>.
  DEEP-VERIFIED rank \<ge> 10 (rank-stratified is_standard generator; uncapped
  periodic cases: ALL satisfy the strict confinement, 0 in the boundary branch).\<close>

lemma oper_d1pos_ctx_period_tncstrict_uncapped:
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
    and span: "j1red = j0red + (j1' - j0')"
    and j0j1': "j0' < j1'"
    and j1lt: "j1' < Lng ((N::pairseq)[n])"
    and notbrle: "\<not> (TrMax (seg ((N::pairseq)[n]) j0' j1')
                        = Lng (seg ((N::pairseq)[n]) j0' j1') - 1
                      \<or> le0 (seg ((N::pairseq)[n]) j0' j1')
                            (TrMax (seg ((N::pairseq)[n]) j0' j1') + 1)
                            (Lng (seg ((N::pairseq)[n]) j0' j1') - 1))"
  shows "TrMax (seg N j0red j1red) < j1red - 1 - j0red"
proof -
  let ?M = "(N::pairseq)[n]"
  let ?Mp = "seg ?M j0' j1'"
  let ?Np = "seg N j0red j1red"
  \<comment> \<open>split \<open>\<not>brle\<close> into its two conjuncts\<close>
  have ndisj1: "TrMax ?Mp \<noteq> Lng ?Mp - 1"
    and notle: "\<not> le0 ?Mp (TrMax ?Mp + 1) (Lng ?Mp - 1)" using notbrle by auto
  \<comment> \<open>\<open>M'\<close> non-empty, in \<open>T_PS\<close>; \<open>TrMax M' \<le> Lng M'-1\<close> turns \<open>ndisj1\<close> into \<open>Mlt\<close>\<close>
  have j0'le: "j0' \<le> j1'" using j0j1' by linarith
  have MpT: "?Mp \<in> T_PS" using j0'le by (simp add: T_PS_def seg_def)
  have tb: "TrMax ?Mp \<le> Lng ?Mp - 1" by (rule TrMax_bound[OF MpT])
  have Mlt: "TrMax ?Mp < Lng ?Mp - 1" using tb ndisj1 by linarith
  \<comment> \<open>UNCAPPED span \<open>\<Longrightarrow>\<close> \<open>c = Lng M' - 2\<close> and \<open>Lng N\<^sub>red = Lng M'\<close>\<close>
  have LNp: "Lng ?Np = Suc j1red - j0red" by simp
  have LMp: "Lng ?Mp = Suc j1' - j0'" by simp
  have spanD: "j1' - j0' = j1red - j0red" using span j0j1red by linarith
  have LenEq: "Lng ?Np = Lng ?Mp" using LNp LMp spanD j0j1red j0j1' by linarith
  have cEq: "j1red - 1 - j0red = Lng ?Mp - 2" using LNp LenEq j0j1red by linarith
  have LMp2: "2 \<le> Lng ?Mp" using LMp j0j1' by linarith
  \<comment> \<open>strict-2 confinement on \<open>M'\<close> (the \<open>tncM1\<close> block of the uncapped keystone)\<close>
  have tncM1: "TrMax ?Mp + 1 \<le> Lng ?Mp - 2"
  proof -
    have le_c: "TrMax ?Mp \<le> Lng ?Mp - 2" using Mlt by linarith
    have "TrMax ?Mp \<noteq> Lng ?Mp - 2"
    proof
      assume eq: "TrMax ?Mp = Lng ?Mp - 2"
      have endlt: "Lng ?Mp - 1 < Lng ?Mp" using LMp2 by linarith
      have "TrMax ?Mp + 1 = Lng ?Mp - 1" using eq LMp2 by linarith
      hence "le0 ?Mp (TrMax ?Mp + 1) (Lng ?Mp - 1)"
        using le0_refl[OF endlt] by simp
      thus False using notle by simp
    qed
    with le_c show ?thesis by linarith
  qed
  \<comment> \<open>uncapped keystone: \<open>TrMax M' = TrMax N\<^sub>red\<close>\<close>
  have TrEq: "TrMax ?Mp = TrMax ?Np"
    by (rule TrMax_seg_oper_d1pos_eq_notbrle_uncapped[OF N L notzero hp i1z j0lt
          n1 qn s0w s0eq s0lt j0'eq shamt j1redle j0j1red span j0j1' j1lt Mlt notle])
  \<comment> \<open>combine: \<open>TrMax N\<^sub>red = TrMax M' \<le> Lng M' - 3 < Lng M' - 2 = c\<close>\<close>
  show ?thesis using TrEq tncM1 cEq by linarith
qed


text \<open>§6.8 d1pos ROW-0-shift \<open>le0\<close> transfer, REVERSE direction.  Same \<open>+k\<close> row-0
  agreement \<open>entry M 0 j = entry N 0 j + k\<close> on \<open>[0,c]\<close>, but transferring a \<open>le0\<close>
  step of \<open>N\<close> back to \<open>M\<close> (a constant shift is an order-iso on row 0, so
  \<open>nextrel0\<close> is invariant in BOTH directions).  Used to pin \<open>\<not>le0 N\<^sub>p .. \<longleftarrow> \<not>le0 M' ..\<close>.\<close>

lemma nextrel0_prefix_row0_shift_rev:
  assumes agree: "\<And>j. j \<le> c \<Longrightarrow> entry M 0 j = entry N 0 j + k"
    and cM: "c < Lng M"
    and xy: "x \<le> c" "y \<le> c"
    and h: "nextrel0 N x y"
  shows "nextrel0 M x y"
proof -
  from h have hx: "x < y" and hv: "entry N 0 x < entry N 0 y"
    and hmid: "\<And>j. x < j \<Longrightarrow> j < y \<Longrightarrow> entry N 0 y \<le> entry N 0 j"
    by (auto simp: nextrel0_def)
  show ?thesis
    unfolding nextrel0_def
  proof (intro conjI allI impI)
    show "x < Lng M" using xy(1) cM by linarith
    show "y < Lng M" using xy(2) cM by linarith
    show "x < y" by (rule hx)
    show "entry M 0 x < entry M 0 y" using hv agree[OF xy(1)] agree[OF xy(2)] by simp
    fix j assume "x < j \<and> j < y"
    hence j1: "x < j" and j2: "j < y" by auto
    have jc: "j \<le> c" using j2 xy(2) by linarith
    show "entry M 0 y \<le> entry M 0 j" using hmid[OF j1 j2] agree[OF xy(2)] agree[OF jc] by simp
  qed
qed

lemma le0_prefix_row0_shift_rev:
  assumes agree: "\<And>j. j \<le> c \<Longrightarrow> entry M 0 j = entry N 0 j + k"
    and cM: "c < Lng M" and cN: "c < Lng N"
    and ac: "a \<le> c" and bc: "b \<le> c"
    and le: "le0 N a b"
  shows "le0 M a b"
proof -
  have rN: "(nextrel0 N)\<^sup>*\<^sup>* a b" using le by (simp add: le0_def)
  have "b \<le> c \<longrightarrow> (nextrel0 M)\<^sup>*\<^sup>* a b"
    using rN
  proof (induction rule: rtranclp_induct)
    case base show ?case by simp
  next
    case (step y z)
    show ?case
    proof
      assume zc: "z \<le> c"
      have yz: "nextrel0 N y z" using step.hyps(2) .
      have ylt: "y < z" using yz by (simp add: nextrel0_def)
      have yc: "y \<le> c" using ylt zc by linarith
      have "(nextrel0 M)\<^sup>*\<^sup>* a y" using step.IH yc by simp
      moreover have "nextrel0 M y z"
        by (rule nextrel0_prefix_row0_shift_rev[OF agree cM yc zc yz])
      ultimately show "(nextrel0 M)\<^sup>*\<^sup>* a z" by simp
    qed
  qed
  hence "(nextrel0 M)\<^sup>*\<^sup>* a b" using bc by simp
  thus ?thesis using ac bc cM by (simp add: le0_def)
qed

text \<open>§6.8 d1pos CELL-4 (PERIODIC-TAIL) \<open>notbrleNp\<close> discharger: the period-reduced
  reference slice \<open>Np = seg N j\<^sub>0\<^sup>red j\<^sub>1\<^sup>red\<close> is NON-brle, transferred from the
  consumer's \<open>\<not>brle (M' = seg (N[n]) j'\<^sub>0 j'\<^sub>1)\<close>.  THE discharger that supplies
  \<open>multiNp\<close> for all 4 cells (via \<open>oper_d1pos_ctx_period_multiNp\<close>, defined below).
  Two \<open>\<not>brle\<close> conjuncts transfer:
  \<^item> D1 \<open>\<not>(TrMax Np = Lng Np-1)\<close>: directly from \<open>tnc\<close> (\<open>TrMax Np \<le> j\<^sub>1\<^sup>red-1-j\<^sub>0\<^sup>red
    < j\<^sub>1\<^sup>red-j\<^sub>0\<^sup>red = Lng Np-1\<close>) — same as the \<open>trneN\<close> brick of
    @{thm [source] oper_d1pos_notbrle_Br_align}.
  \<^item> D2 \<open>\<not>le0 Np (TrMax Np+1)(Lng Np-1)\<close>: by contradiction.  TrEq
    (@{thm [source] TrMax_seg_oper_d1pos_eq_span}) gives \<open>TrMax M' = TrMax Np\<close>;
    the \<open>+shamt\<close> row-0 agreement on \<open>[0,Lng Np-1]\<close>
    (@{thm [source] oper_d1pos_period_row0_unif}) makes \<open>le0\<close> on the window
    \<open>[TrMax Np+1, Lng Np-1]\<close> coincide between \<open>Np\<close> and \<open>M'\<close>
    (@{thm [source] le0_prefix_row0_shift_rev}, both endpoints \<le> Lng Np-1).  So
    \<open>le0 Np (TrMax Np+1)(Lng Np-1)\<close> would give \<open>le0 M' (TrMax M'+1)(Lng Np-1)\<close>.
    In the UNCAPPED case (\<open>j\<^sub>1\<^sup>red = j\<^sub>0\<^sup>red+(j'\<^sub>1-j'\<^sub>0)\<close>) \<open>Lng Np-1 = Lng M'-1\<close>, a direct
    contradiction with \<open>\<not>brle\<close> conj-2.  In the CAPPED case (\<open>j\<^sub>1\<^sup>red = Lng N-1\<close>,
    \<open>j\<^sub>1\<^sup>red < j\<^sub>0\<^sup>red+(j'\<^sub>1-j'\<^sub>0)\<close>) the boundary index \<open>Lng Np-1\<close> reaches \<open>Lng M'-1\<close>
    along row-0 (@{thm [source] oper_d1pos_seg_le0_boundary} = block-\<open>(q+1)\<close> start
    reaches \<open>j'\<^sub>1\<close>), so \<open>le0_trans\<close> extends to \<open>le0 M' (TrMax M'+1)(Lng M'-1)\<close>,
    again contradicting \<open>\<not>brle\<close> conj-2.
  DEEP-VERIFIED rank 10 (python/notbrleNp_check.py: notbrleNp/D1/D2/D2iff/TrEq
  3370/3370; python/notbrleNp_route.py: shiftIff/R/EXTEND 3370/3370;
  python/notbrleNp_extend.py: boundary TAIL = le0 M'(Lng Np-1)(Lng M'-1) 2701/2701).\<close>

lemma oper_d1pos_ctx_notbrleNp:
  fixes N :: pairseq
  assumes N: "N \<in> T_PS" and L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and Neq: "M = (N::pairseq)[n]"
    and n1: "1 \<le> n"
    and q0n: "q0 < n"
    and s0w: "j0red < Lng N - 1"
    and s0lt: "s0 < Lng N - 1 - parent N 1 (Lng N - 1)"
    and j0reds: "j0red = parent N 1 (Lng N - 1) + s0"
    and j0'eq: "j0' = parent N 1 (Lng N - 1)
                  + q0 * (Lng N - 1 - parent N 1 (Lng N - 1)) + s0"
    and shamt: "shamt = q0 * (entry N 0 (Lng N - 1) - entry N 0 (parent N 1 (Lng N - 1)))"
    and j1reddef: "j1red = min (j0red + (j1' - j0')) (Lng N - 1)"
    and j0j1red: "j0red < j1red"
    and j0j1': "j0' < j1'"
    and jM: "j1' < Lng M"
    and tnc: "TrMax (seg N j0red j1red) \<le> j1red - 1 - j0red"
    and stop: "\<not> nextR (seg ((N::pairseq)[n]) j0' j1') 1
                  (TrMax (seg N j0red j1red))
                  (TrMax (seg N j0red j1red) + 1)"
    and notbrle: "\<not> (TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1
                     \<or> le0 (seg M j0' j1') (TrMax (seg M j0' j1') + 1) (Lng (seg M j0' j1') - 1))"
  shows "\<not> (TrMax (seg N j0red j1red) = Lng (seg N j0red j1red) - 1
           \<or> le0 (seg N j0red j1red) (TrMax (seg N j0red j1red) + 1)
                 (Lng (seg N j0red j1red) - 1))"
proof -
  let ?M = "(N::pairseq)[n]"
  let ?Mp = "seg ?M j0' j1'"
  let ?Np = "seg N j0red j1red"
  let ?tN = "TrMax ?Np"
  let ?tM = "TrMax ?Mp"
  let ?m  = "j1red - j0red"   \<comment> \<open>\<open>= Lng Np - 1\<close>\<close>
  have MMn: "M = ?M" using Neq .
  have j1lt: "j1' < Lng ?M" using jM MMn by simp
  \<comment> \<open>geometry; split \<open>j1red\<close> from its \<open>min\<close> definition\<close>
  have j1redle: "j1red \<le> Lng N - 1" using j1reddef by simp
  have j1redspan: "j1red \<le> j0red + (j1' - j0')" using j1reddef by simp
  have LNp: "Lng ?Np = Suc j1red - j0red" by simp
  have LMp: "Lng ?Mp = Suc j1' - j0'" by simp
  have j0'le: "j0' \<le> j1'" using j0j1' by linarith
  have lenNpm: "Lng ?Np - 1 = ?m" using j0j1red by simp
  have MpT: "?Mp \<in> T_PS" using j0'le by (simp add: T_PS_def seg_def)
  have NpT: "?Np \<in> T_PS" using j0j1red by (simp add: T_PS_def seg_def)
  \<comment> \<open>(TrEq) \<open>TrMax M' = TrMax Np\<close> via the CAPPED-general span keystone\<close>
  have TrEq: "?tM = ?tN"
    by (rule TrMax_seg_oper_d1pos_eq_span[OF N L notzero hp i1z j0lt n1 q0n s0w
              j0reds s0lt j0'eq shamt j1redle j0j1red j1redspan j0j1' j1lt tnc stop])
  \<comment> \<open>the two \<open>\<not>brle\<close> conjuncts on the M-side\<close>
  have trneM: "?tM \<noteq> Lng ?Mp - 1" using notbrle MMn by blast
  have notle0M: "\<not> le0 ?Mp (?tM + 1) (Lng ?Mp - 1)" using notbrle MMn by blast
  \<comment> \<open>===== D1: \<open>\<not>(TrMax Np = Lng Np-1)\<close> from \<open>tnc\<close> =====\<close>
  have D1: "?tN \<noteq> Lng ?Np - 1"
  proof -
    have "?tN < ?m" using tnc j0j1red by linarith
    thus ?thesis using lenNpm by simp
  qed
  \<comment> \<open>===== D2: \<open>\<not>le0 Np (TrMax Np+1)(Lng Np-1)\<close> =====\<close>
  \<comment> \<open>\<open>+shamt\<close> row-0 agreement on \<open>[0,m]\<close>: \<open>entry M' 0 j = entry Np 0 j + shamt\<close>\<close>
  have agree: "\<And>j. j \<le> ?m \<Longrightarrow> entry ?Mp 0 j = entry ?Np 0 j + shamt"
  proof -
    fix j assume jm: "j \<le> ?m"
    have jlt: "j < Suc j1' - j0'"
    proof -
      have "?m \<le> j1' - j0'" using j1redspan j0j1red by linarith
      thus ?thesis using jm j0'le by linarith
    qed
    have jltN: "j < Suc j1red - j0red" using jm j0j1red by linarith
    have eMp: "entry ?Mp 0 j = entry ?M 0 (j0' + j)"
      using jlt by (simp add: entry_def seg_nth_eq)
    have eNp: "entry ?Np 0 j = entry N 0 (j0red + j)"
      using jltN by (simp add: entry_def seg_nth_eq)
    have jval: "j0' + j < Lng ((N::pairseq)[n])"
    proof -
      have "j \<le> j1' - j0'" using jm j1redspan j0j1red by linarith
      hence "j0' + j \<le> j1'" using j0'le by linarith
      thus ?thesis using j1lt by linarith
    qed
    have j0redlej1red0: "j0red \<le> j1red" using j0j1red by simp
    have "entry ((N::pairseq)[n]) 0 (j0' + j) = entry N 0 (j0red + j) + shamt"
      by (rule oper_d1pos_period_row0_unif[OF L notzero hp i1z j0lt q0n s0lt
            j0reds j0'eq shamt j1redle j0redlej1red0 jval jm])
    thus "entry ?Mp 0 j = entry ?Np 0 j + shamt" using eMp eNp by simp
  qed
  have mMp: "?m < Lng ?Mp"
  proof -
    have "?m \<le> j1' - j0'" using j1redspan j0j1red by linarith
    thus ?thesis using LMp j0'le by linarith
  qed
  have mNp: "?m < Lng ?Np" using LNp j0j1red by linarith
  have tN1m: "?tN + 1 \<le> ?m" using tnc j0j1red by linarith
  have D2: "\<not> le0 ?Np (?tN + 1) (Lng ?Np - 1)"
  proof
    assume leNp: "le0 ?Np (?tN + 1) (Lng ?Np - 1)"
    have leNpm: "le0 ?Np (?tN + 1) ?m" using leNp lenNpm by simp
    \<comment> \<open>rev shift: \<open>le0 Np \<rightarrow> le0 M'\<close> on \<open>[0,m]\<close>\<close>
    have leMpm: "le0 ?Mp (?tN + 1) ?m"
      by (rule le0_prefix_row0_shift_rev[OF agree mMp mNp tN1m order.refl leNpm])
    \<comment> \<open>fold to the \<open>M'\<close> branch start (\<open>tM+1 = tN+1\<close>) and extend to \<open>Lng M'-1\<close>\<close>
    have leMpm': "le0 ?Mp (?tM + 1) ?m" using leMpm TrEq by simp
    have leMpFull: "le0 ?Mp (?tM + 1) (Lng ?Mp - 1)"
    proof (cases "j1red = j0red + (j1' - j0')")
      case True
      \<comment> \<open>UNCAPPED: \<open>m = Lng Np-1 = Lng M'-1\<close>, endpoints coincide\<close>
      have meq: "?m = Lng ?Mp - 1" using True LMp j0'le by simp
      show ?thesis using leMpm' meq by simp
    next
      case False
      \<comment> \<open>CAPPED: \<open>j1red = Lng N-1\<close> (cap active); \<open>le0 M' m (Lng M'-1)\<close> via boundary reach\<close>
      have spanlt: "j1red < j0red + (j1' - j0')" using j1redspan False by linarith
      \<comment> \<open>\<open>min (j0red+(j1'-j0')) (Lng N-1) < j0red+(j1'-j0')\<close> forces the cap to be \<open>Lng N-1\<close>\<close>
      have cap: "j1red = Lng N - 1" using j1reddef spanlt by linarith
      have c1eq: "j1red - 1 - j0red + 1 = ?m" using j0j1red by simp
      have endTAIL: "le0 ?Mp (j1red - 1 - j0red + 1) (Lng ?Mp - 1)"
        by (rule oper_d1pos_seg_le0_boundary[OF N L notzero hp i1z j0lt n1 q0n
              j0reds s0lt j0'eq cap spanlt j0j1' j1lt])
      have tailMp: "le0 ?Mp ?m (Lng ?Mp - 1)" using endTAIL c1eq by simp
      show ?thesis by (rule le0_trans[OF leMpm' tailMp])
    qed
    show False using leMpFull notle0M by simp
  qed
  show ?thesis using D1 D2 by blast
qed

text \<open>§6.8 d1pos CELL-4 (PERIODIC-TAIL) multiNp discharger:
  1 < length (P (seg N (j0red + TrMax Np + 1) j1red)) (Np = seg N j0red j1red).
  The branch region of the period-reduced N-slice is multi.  Route: this is
  EXACTLY oper_d1pos_ctx_multiM applied to N itself (base N,
  window [j0red, j1red]): Np in T_PS, j0red < j1red, and notbrle Np give the
  multi branch.  notbrle Np is the period transfer of the consumer's notbrle Mp
  (TrEq TrMax Mp = TrMax Np + the +shamt row-0 agreement makes le0 Np / le0 Mp
  coincide on [0, Lng Np-1], so the two brle conjuncts transfer); it is supplied
  by the assembly's already-established TrEq context (the same tnc/stop
  inputs that drive oper_d1pos_notbrle_Br_align).
  DEEP-VERIFIED rank 10 (python/perresid_check.py: multiNp 1117/1117, notbrle Np
  1117/1117 — /tmp/perresid_brle2.py both conjuncts 0 failures).\<close>

text \<open>§6.8 d1pos VERBATIM (regA / boundary) \<open>notbrleNp\<close> discharger.  The mirror of
  @{thm [source] oper_d1pos_ctx_notbrleNp} for the PREFIX cells where the slice start
  \<open>j'\<^sub>0 < jm2\<close>, so the reference slice is read \<open>N\<close>-VERBATIM (\<open>j\<^sub>0\<^sup>red = j'\<^sub>0\<close>, \<open>shamt = 0\<close>,
  \<open>j\<^sub>1\<^sup>red = Lng N-1\<close>) and the period decomposition (\<open>q\<^sub>0/s\<^sub>0/j'\<^sub>0=jm2+q\<^sub>0w+s\<^sub>0\<close>) does NOT
  apply.  Same two-conjunct transfer: D1 from \<open>tnc\<close>; D2 by contradiction via the
  SHAMT-ZERO row-0 agreement @{thm [source] oper_d1pos_row0_agree} (entry \<open>N[n]\<close> = entry
  \<open>N\<close> on \<open>[0,Lng N-1]\<close>), TrEq @{thm [source] TrMax_seg_oper_d1pos_eq_regA}, and — in the
  CAPPED sub-case (\<open>Lng N-1 < j'\<^sub>1\<close>) — the verbatim period boundary reach
  @{thm [source] oper_d1pos_le0_start_to_any} at \<open>k = 1\<close> (\<open>le0 (N[n]) (Lng N-1) j'\<^sub>1\<close>).\<close>

lemma oper_d1pos_ctx_notbrleNp_verbatim:
  fixes N :: pairseq
  assumes N: "N \<in> T_PS" and L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and Neq: "M = (N::pairseq)[n]"
    and n1: "1 \<le> n"
    and j0plt: "j0' < Lng N - 1"
    and j0j1': "j0' < j1'"
    and bge: "Lng N - 1 \<le> j1'"
    and jM: "j1' < Lng M"
    and tnc: "TrMax (seg N j0' (Lng N - 1)) \<le> Lng N - 1 - 1 - j0'"
    and stop: "\<not> nextR (seg ((N::pairseq)[n]) j0' j1') 1
                  (TrMax (seg N j0' (Lng N - 1)))
                  (TrMax (seg N j0' (Lng N - 1)) + 1)"
    and notbrle: "\<not> (TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1
                     \<or> le0 (seg M j0' j1') (TrMax (seg M j0' j1') + 1) (Lng (seg M j0' j1') - 1))"
  shows "\<not> (TrMax (seg N j0' (Lng N - 1)) = Lng (seg N j0' (Lng N - 1)) - 1
           \<or> le0 (seg N j0' (Lng N - 1)) (TrMax (seg N j0' (Lng N - 1)) + 1)
                 (Lng (seg N j0' (Lng N - 1)) - 1))"
proof -
  let ?M = "(N::pairseq)[n]"
  let ?j1N = "Lng N - 1"
  let ?Mp = "seg ?M j0' j1'"
  let ?Np = "seg N j0' ?j1N"
  let ?tN = "TrMax ?Np"
  let ?tM = "TrMax ?Mp"
  let ?m  = "?j1N - j0'"   \<comment> \<open>\<open>= Lng Np - 1\<close>\<close>
  have MMn: "M = ?M" using Neq .
  have j1lt: "j1' < Lng ?M" using jM MMn by simp
  have j0j1red: "j0' < ?j1N" using j0plt .
  have LNp: "Lng ?Np = Suc ?j1N - j0'" by simp
  have LMp: "Lng ?Mp = Suc j1' - j0'" by simp
  have j0'le: "j0' \<le> j1'" using j0j1' by linarith
  have lenNpm: "Lng ?Np - 1 = ?m" using j0j1red by simp
  have MpT: "?Mp \<in> T_PS" using j0'le by (simp add: T_PS_def seg_def)
  have NpT: "?Np \<in> T_PS" using j0j1red by (simp add: T_PS_def seg_def)
  \<comment> \<open>geometry of the cap\<close>
  have j1redle: "?j1N \<le> ?j1N" by simp
  have j1redspan: "?j1N \<le> j0' + (j1' - j0')" using bge j0'le by linarith
  \<comment> \<open>(TrEq) \<open>TrMax M' = TrMax Np\<close> (regA / verbatim keystone, \<open>j\<^sub>0\<^sup>red = j'\<^sub>0\<close>)\<close>
  have TrEq: "?tM = ?tN"
    by (rule TrMax_seg_oper_d1pos_eq_regA[OF L notzero hp i1z j0lt n1
              j1redle j0j1red j1redspan refl j0j1' j1lt tnc stop])
  \<comment> \<open>the two \<open>\<not>brle\<close> conjuncts on the M-side\<close>
  have trneM: "?tM \<noteq> Lng ?Mp - 1" using notbrle MMn by blast
  have notle0M: "\<not> le0 ?Mp (?tM + 1) (Lng ?Mp - 1)" using notbrle MMn by blast
  \<comment> \<open>===== D1: \<open>\<not>(TrMax Np = Lng Np-1)\<close> from \<open>tnc\<close> =====\<close>
  have D1: "?tN \<noteq> Lng ?Np - 1"
  proof -
    have "?tN < ?m" using tnc j0j1red by linarith
    thus ?thesis using lenNpm by simp
  qed
  \<comment> \<open>===== D2: \<open>\<not>le0 Np (TrMax Np+1)(Lng Np-1)\<close> =====\<close>
  \<comment> \<open>SHAMT-ZERO row-0 agreement on \<open>[0,m]\<close>: \<open>entry M' 0 j = entry Np 0 j\<close>\<close>
  have bnd: "Lng N - 1 < Lng ?M" using bge j1lt by linarith
  have agree: "\<And>j. j \<le> ?m \<Longrightarrow> entry ?Mp 0 j = entry ?Np 0 j + (0::nat)"
  proof -
    fix j assume jm: "j \<le> ?m"
    have jlt: "j < Suc j1' - j0'"
    proof -
      have "?m \<le> j1' - j0'" using j1redspan j0j1red by linarith
      thus ?thesis using jm j0'le by linarith
    qed
    have jltN: "j < Suc ?j1N - j0'" using jm j0j1red by linarith
    have eMp: "entry ?Mp 0 j = entry ?M 0 (j0' + j)"
      using jlt by (simp add: entry_def seg_nth_eq)
    have eNp: "entry ?Np 0 j = entry N 0 (j0' + j)"
      using jltN by (simp add: entry_def seg_nth_eq)
    have jle: "j0' + j \<le> ?j1N" using jm j0plt by linarith
    have "entry ?M 0 (j0' + j) = entry N 0 (j0' + j)"
      by (rule oper_d1pos_row0_agree[OF L notzero hp i1z j0lt bnd jle])
    thus "entry ?Mp 0 j = entry ?Np 0 j + (0::nat)" using eMp eNp by simp
  qed
  have mMp: "?m < Lng ?Mp"
  proof -
    have "?m \<le> j1' - j0'" using j1redspan j0j1red by linarith
    thus ?thesis using LMp j0'le by linarith
  qed
  have mNp: "?m < Lng ?Np" using LNp j0j1red by linarith
  have tN1m: "?tN + 1 \<le> ?m" using tnc j0j1red by linarith
  have D2: "\<not> le0 ?Np (?tN + 1) (Lng ?Np - 1)"
  proof
    assume leNp: "le0 ?Np (?tN + 1) (Lng ?Np - 1)"
    have leNpm: "le0 ?Np (?tN + 1) ?m" using leNp lenNpm by simp
    \<comment> \<open>rev shift (\<open>k=0\<close>): \<open>le0 Np \<rightarrow> le0 M'\<close> on \<open>[0,m]\<close>\<close>
    have leMpm: "le0 ?Mp (?tN + 1) ?m"
      by (rule le0_prefix_row0_shift_rev[OF agree mMp mNp tN1m order.refl leNpm])
    have leMpm': "le0 ?Mp (?tM + 1) ?m" using leMpm TrEq by simp
    \<comment> \<open>extend to \<open>Lng M'-1\<close>: UNCAPPED (\<open>m = Lng M'-1\<close>) or CAPPED (boundary reach)\<close>
    have leMpFull: "le0 ?Mp (?tM + 1) (Lng ?Mp - 1)"
    proof (cases "?j1N = j1'")
      case True
      have meq: "?m = Lng ?Mp - 1" using True LMp j0'le by simp
      show ?thesis using leMpm' meq by simp
    next
      case False
      \<comment> \<open>CAPPED: \<open>Lng N-1 < j'\<^sub>1\<close>; reach \<open>m \<rightarrow> Lng M'-1\<close> via verbatim period start-to-any (\<open>k=1\<close>)\<close>
      have capN: "?j1N < j1'" using bge False by linarith
      let ?w = "?j1N - parent N 1 ?j1N"
      have w0: "0 < ?w" using j0lt by linarith
      have LngMn: "Lng ?M = parent N 1 ?j1N + n * ?w"
        by (rule oper_d1pos_LngM[OF L notzero hp i1z j0lt])
      have n1lt: "1 < n"
      proof -
        have "parent N 1 ?j1N + 1 * ?w \<le> ?j1N" using j0lt by simp
        also have "?j1N < j1'" using capN .
        also have "j1' < parent N 1 ?j1N + n * ?w" using j1lt LngMn by simp
        finally have "1 * ?w < n * ?w" by linarith
        thus ?thesis using w0 by (cases n) auto
      qed
      have xge: "parent N 1 ?j1N + 1 * ?w \<le> j1'"
      proof -
        have "parent N 1 ?j1N + 1 * ?w = ?j1N" using j0lt by simp
        thus ?thesis using capN by linarith
      qed
      have boundMn: "le0 ?M (parent N 1 ?j1N + 1 * ?w) j1'"
        by (rule oper_d1pos_le0_start_to_any[OF N L notzero hp i1z j0lt n1lt xge j1lt])
      have boundMn': "le0 ?M ?j1N j1'"
      proof -
        have "parent N 1 ?j1N + 1 * ?w = ?j1N" using j0lt by simp
        thus ?thesis using boundMn by simp
      qed
      \<comment> \<open>translate \<open>le0 M[n] (Lng N-1) j'\<^sub>1\<close> into \<open>M'\<close>-coordinates \<open>[m, Lng M'-1]\<close>\<close>
      have mtrans: "le0 ?Mp ?m (Lng ?Mp - 1)"
      proof -
        have c1: "j1' < Lng ?M" using j1lt .
        have ca: "?m \<le> j1' - j0'" using mMp LMp j0'le by linarith
        have cb: "Lng ?Mp - 1 \<le> j1' - j0'" using LMp j0'le by linarith
        have admeq: "le0 (seg ?M j0' j1') ?m (Lng ?Mp - 1)
                   \<longleftrightarrow> le0 ?M (j0' + ?m) (j0' + (Lng ?Mp - 1))"
          by (rule adm_le0_seg[OF c1 ca cb j0'le])
        have e1: "j0' + ?m = ?j1N" using j0j1red by simp
        have e2: "j0' + (Lng ?Mp - 1) = j1'" using LMp j0'le by linarith
        have "le0 ?M ?j1N j1'" using boundMn' .
        hence "le0 ?M (j0' + ?m) (j0' + (Lng ?Mp - 1))" using e1 e2 by simp
        thus ?thesis using admeq by simp
      qed
      show ?thesis by (rule le0_trans[OF leMpm' mtrans])
    qed
    show False using leMpFull notle0M by simp
  qed
  show ?thesis using D1 D2 by blast
qed

lemma oper_d1pos_ctx_period_multiNp:
  fixes N :: pairseq
  assumes NpT: "seg N j0red j1red \<in> T_PS"
    and j0j1red: "j0red < j1red"
    and notbrleNp: "\<not> (TrMax (seg N j0red j1red) = Lng (seg N j0red j1red) - 1
                     \<or> le0 (seg N j0red j1red) (TrMax (seg N j0red j1red) + 1)
                            (Lng (seg N j0red j1red) - 1))"
  shows "1 < length (P (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red))"
  by (rule oper_d1pos_ctx_multiM[OF NpT j0j1red notbrleNp])

lemma oper_d1pos_notbrle_LOW_take_eq_periodic:
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
    \<comment> \<open>CELL-4 placement: slice start in the PERIODIC TAIL, block index \<open>q\<^sub>0 \<ge> 1\<close>\<close>
    and j0pge: "Lng N - 1 \<le> j0'"
    \<comment> \<open>witness definitions (block-period reduction of the slice start)\<close>
    and q0def: "q0 = (j0' - parent N 1 (Lng N - 1)) div (Lng N - 1 - parent N 1 (Lng N - 1))"
    and s0def: "s0 = (j0' - parent N 1 (Lng N - 1)) mod (Lng N - 1 - parent N 1 (Lng N - 1))"
    and j0reddef: "j0red = parent N 1 (Lng N - 1) + s0"
    and j1reddef: "j1red = min (j0red + (j1' - j0')) (Lng N - 1)"
    and shamtdef: "shamt = q0 * (entry N 0 (Lng N - 1) - entry N 0 (parent N 1 (Lng N - 1)))"
    \<comment> \<open>multiplicity of both branch regions\<close>
    and multiM: "1 < length (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1'))"
    and multiNp: "1 < length (P (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red))"
    \<comment> \<open>Br-align inputs (the shifted TrEq keystone), and \<open>le0\<close>\<close>
    and le0Np: "le0 N j0red j1red"
    and tnc: "TrMax (seg N j0red j1red) \<le> j1red - 1 - j0red"
    and stop: "\<not> nextR (seg ((N::pairseq)[n]) j0' j1') 1
                  (TrMax (seg N j0red j1red))
                  (TrMax (seg N j0red j1red) + 1)"
    \<comment> \<open>UNIFIED anchor inputs (perfix-A): unconditional all-but-last prefix shift +
       boundary junction + component-count match + anchor bound.  NO \<open>fullShift\<close>,
       NO \<open>mLmin_SnB\<close>, NO \<open>cleB\<close> (the last two are FALSE on 458/3369 boundary cases).
       All deep-verified rank 12 (perfix-A: shiftEqB/boundEq0/boundEq1 8019/8019,
       lenPSeq/cleM 922/922 rank 10).\<close>
    and shiftEqB: "seg (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 0
              (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1 - 1)
        = (IncrFirst ^^ shamt)
            (seg (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) 0
                 (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1 - 1))"
    and boundEq0B: "entry (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 0
                (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1)
        = entry (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) 0
                (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1) + shamt"
    and boundEq1B: "entry (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 1
                (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1)
        \<le> entry (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) 1
                (Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1)"
    and lenPSeqB: "length (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1'))
                 = length (P (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red))"
    and cleMB: "IdxSum (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')) !
            (length (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')) - 1)
          \<le> Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1"
    and mleSB: "Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1
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
  let ?jm2 = "parent N 1 (Lng N - 1)"
  let ?w = "Lng N - 1 - ?jm2"
  let ?delta = "entry N 0 (Lng N - 1) - entry N 0 ?jm2"
  let ?Np = "seg N j0red j1red"
  let ?AN = "j0red + TrMax ?Np + 1"
  \<comment> \<open>geometry\<close>
  have MNn: "M = ?M" using Neq .
  have j1lt: "j1' < Lng ?M" using jM Neq by simp
  have w0: "0 < ?w" using j0lt by linarith
  have s0lt: "s0 < ?w" using s0def w0 by simp
  have j0reds: "j0red = ?jm2 + s0" using j0reddef .
  have j0redlt: "j0red < Lng N - 1" using j0reds s0lt by linarith
  \<comment> \<open>\<open>j'\<^sub>0 = jm2 + q0*w + s0\<close> via div/mod, and \<open>q0 \<ge> 1\<close>\<close>
  have j0pge2: "?jm2 \<le> j0'" using j0pge j0lt by linarith
  have j0'split: "j0' - ?jm2 = q0 * ?w + s0"
    using q0def s0def by (simp add: mult.commute)
  have j0'eq: "j0' = ?jm2 + q0 * ?w + s0" using j0'split j0pge2 by linarith
  have q0n: "q0 < n"
  proof -
    have "j0' < Lng ?M" using lt j1lt by linarith
    hence "j0' < ?jm2 + n * ?w" using oper_d1pos_LngM[OF LNgt notzeroN hasparN i1zN j0lt] Neq by simp
    hence "q0 * ?w + s0 < n * ?w" using j0'eq by linarith
    hence "q0 * ?w < n * ?w" using s0lt by linarith
    thus ?thesis using w0 by simp
  qed
  \<comment> \<open>geometry of \<open>j1red\<close>\<close>
  have j1redle: "j1red \<le> Lng N - 1" using j1reddef by simp
  have j0j1red: "j0red < j1red"
  proof -
    have "j0red < j0red + (j1' - j0')" using lt by simp
    moreover have "j0red < Lng N - 1" using j0redlt .
    ultimately show ?thesis using j1reddef by simp
  qed
  have j1redspan: "j1red \<le> j0red + (j1' - j0')" using j1reddef by simp
  \<comment> \<open>\<open>M = N[n]\<close>: consumer slice\<close>
  have Mp_eq: "?M' = seg ?M j0' j1'" using Neq by simp
  have notbrle': "\<not> (TrMax (seg ?M j0' j1') = Lng (seg ?M j0' j1') - 1
                     \<or> le0 (seg ?M j0' j1') (TrMax (seg ?M j0' j1') + 1) (Lng (seg ?M j0' j1') - 1))"
    using notbrle Mp_eq by simp
  have stop': "\<not> nextR (seg ?M j0' j1') 1 (TrMax ?Np) (TrMax ?Np + 1)" using stop .
  \<comment> \<open>(1) the SHIFTED Br alignment (TrEq + both reshapes + non-emptiness)\<close>
  have align: "TrMax (seg ?M j0' j1') = TrMax ?Np
       \<and> Br (seg ?M j0' j1') = P (seg ?M (j0' + TrMax (seg ?M j0' j1') + 1) j1')
       \<and> Br ?Np = P (seg N (j0red + TrMax ?Np + 1) j1red)
       \<and> Br (seg ?M j0' j1') \<noteq> [] \<and> Br ?Np \<noteq> []"
    by (rule oper_d1pos_notbrle_Br_align[OF NT LNgt notzeroN hasparN i1zN j0lt n1 q0n
            j0redlt j0reds s0lt j0'eq shamtdef j1redle j0j1red j1redspan lt j1lt tnc stop' notbrle'])
  have alTrEq: "TrMax (seg ?M j0' j1') = TrMax ?Np" using align by blast
  have alBrM:  "Br (seg ?M j0' j1') = P (seg ?M (j0' + TrMax (seg ?M j0' j1') + 1) j1')"
    using align by blast
  have alBrN:  "Br ?Np = P (seg N (j0red + TrMax ?Np + 1) j1red)" using align by blast
  have alneM:  "Br (seg ?M j0' j1') \<noteq> []" using align by blast
  have alneN:  "Br ?Np \<noteq> []" using align by blast
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
  have BrNpP: "Br ?Np = P (seg N ?AN j1red)" using alBrN .
  have BrM'ne: "Br ?M' \<noteq> []" using alneM Mp_eq by simp
  have BrNpne: "Br ?Np \<noteq> []" using alneN .
  let ?S = "seg ?M ?A j1'"
  let ?Snside = "seg N ?AN j1red"
  have BrM'PS: "Br ?M' = P ?S" using BrM'P .
  have BrNpPS: "Br ?Np = P ?Snside" using BrNpP .
  \<comment> \<open>bridge \<open>?S\<close> to the ambient-\<open>M\<close> branch source (\<open>M = N[n]\<close>, \<open>?A = j0'+TrMax M'+1\<close>),
     so the unified consumer hypotheses (\<open>shiftEqB\<close>/\<open>boundEq*\<close>/\<open>lenPSeqB\<close>/\<open>cleMB\<close>) line up\<close>
  have SeqM: "?S = seg M (j0' + TrMax (seg M j0' j1') + 1) j1'"
  proof -
    have aeq: "j0' + TrMax (seg M j0' j1') + 1 = ?A" by simp
    show ?thesis using Neq aeq by simp
  qed
  \<comment> \<open>multiplicity\<close>
  have multiS: "1 < length (P ?S)" using SeqM multiM by simp
  have multiSn: "1 < length (P ?Snside)" using multiNp by simp
  \<comment> \<open>\<open>S\<close>, \<open>Snside \<in> T_PS\<close>\<close>
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
  \<comment> \<open>anchors\<close>
  let ?c = "IdxSum (P ?S) ! (length (P ?S) - 1)"
  let ?cN = "IdxSum (P ?Snside) ! (length (P ?Snside) - 1)"
  \<comment> \<open>UNIFIED anchor inputs in \<open>?S\<close>/\<open>?Snside\<close> form (via \<open>SeqM\<close>)\<close>
  have shB: "seg ?S 0 (Lng ?Snside - 1 - 1)
           = (IncrFirst ^^ shamt) (seg ?Snside 0 (Lng ?Snside - 1 - 1))"
    using shiftEqB SeqM by simp
  have b0: "entry ?S 0 (Lng ?Snside - 1) = entry ?Snside 0 (Lng ?Snside - 1) + shamt"
    using boundEq0B SeqM by simp
  have b1: "entry ?S 1 (Lng ?Snside - 1) \<le> entry ?Snside 1 (Lng ?Snside - 1)"
    using boundEq1B SeqM by simp
  have lenPS_loc: "length (P ?S) = length (P ?Snside)" using lenPSeqB SeqM by simp
  have cleM_loc: "?c \<le> Lng ?Snside - 1" using cleMB SeqM by simp
  have mleS_loc: "Lng ?Snside - 1 \<le> Lng ?S - 1" using mleSB SeqM by simp
  \<comment> \<open>(2) anchor coincidence: SINGLE unified call (NO interior/boundary dispatch,
     NO \<open>mLmin\<close>, NO \<open>cleB\<close> — the anchor may be \<open>?c < m\<close> with \<open>?S\<close> crossing the boundary)\<close>
  have ceq: "?c = ?cN"
    by (rule oper_d1pos_anchor_coincide_period_unified(1)[OF ST multiS SnT multiSn
          mleS_loc cleM_loc lenPS_loc shB b0 b1])
  have F8end: "entry ?S 0 ?c = entry ?Snside 0 ?cN + shamt"
    by (rule oper_d1pos_anchor_coincide_period_unified(2)[OF ST multiS SnT multiSn
          mleS_loc cleM_loc lenPS_loc shB b0 b1])
  have F9end: "entry ?S 1 ?c \<le> entry ?Snside 1 ?cN"
    by (rule oper_d1pos_anchor_coincide_period_unified(3)[OF ST multiS SnT multiSn
          mleS_loc cleM_loc lenPS_loc shB b0 b1])
  \<comment> \<open>(3) collapse: \<open>P S = map (IncrFirst^^shamt) (butlast (Br Np)) @ [last (P S)]\<close>\<close>
  have butl: "butlast (P ?Snside) = P (seg ?Snside 0 (?cN - 1))"
    by (rule oper_d1pos_branch_butl[OF SnT multiSn])
  \<comment> \<open>\<open>lowshift'\<close>: the prefix shift at the ACTUAL anchor \<open>?c-1\<close> (\<open>?c = ?cN \<le> m\<close>, so
     \<open>?c-1 \<le> m-1\<close> sits in the shifted all-but-last window \<open>shB\<close>) — uniform, no dispatch\<close>
  have lowshift': "seg ?S 0 (IdxSum (P ?S) ! (length (P ?S) - 1) - 1)
                 = (IncrFirst ^^ shamt) (seg ?Snside 0 (?cN - 1))"
  proof -
    have cNlt: "?cN < Lng ?Snside"
    proof -
      have a: "?cN \<le> Lng ?Snside - 1" by (rule oper_d1pos_branch_anchor(2)[OF SnT multiSn])
      have b: "0 < Lng ?Snside" using Snne by (cases ?Snside) auto
      show ?thesis using a b by linarith
    qed
    have cm1lt: "?cN - 1 < Lng ?Snside" using cNlt by linarith
    \<comment> \<open>\<open>?c - 1 = ?cN - 1 \<le> m - 1\<close>; the shift on \<open>seg ?Snside 0 (m-1)\<close> restricts to it\<close>
    have cNle_m: "?cN \<le> Lng ?Snside - 1" by (rule oper_d1pos_branch_anchor(2)[OF SnT multiSn])
    have segShift: "seg ?S 0 (?cN - 1) = (IncrFirst ^^ shamt) (seg ?Snside 0 (?cN - 1))"
    proof -
      have mpos: "0 < Lng ?Snside - 1"
      proof -
        have "0 < ?cN" by (rule oper_d1pos_branch_anchor(1)[OF SnT multiSn])
        thus ?thesis using cNle_m by linarith
      qed
      have cm1le: "?cN - 1 \<le> Lng ?Snside - 1 - 1" using cNle_m mpos by linarith
      \<comment> \<open>restrict the \<open>m-1\<close>-prefix shift \<open>shB\<close> to the sub-prefix \<open>[0, ?cN-1]\<close>\<close>
      have sS: "seg ?S 0 (?cN - 1) = seg (seg ?S 0 (Lng ?Snside - 1 - 1)) 0 (?cN - 1)"
        using seg_of_seg[of 0 "Lng ?Snside - 1 - 1" "?cN - 1" ?S] cm1le by simp
      have sSn: "seg ?Snside 0 (?cN - 1) = seg (seg ?Snside 0 (Lng ?Snside - 1 - 1)) 0 (?cN - 1)"
        using seg_of_seg[of 0 "Lng ?Snside - 1 - 1" "?cN - 1" ?Snside] cm1le by simp
      have cm1ltSeg: "?cN - 1 < Lng (seg ?Snside 0 (Lng ?Snside - 1 - 1))"
        using cm1le mpos by simp
      have "seg (seg ?S 0 (Lng ?Snside - 1 - 1)) 0 (?cN - 1)
          = seg ((IncrFirst ^^ shamt) (seg ?Snside 0 (Lng ?Snside - 1 - 1))) 0 (?cN - 1)"
        using shB by simp
      also have "\<dots> = (IncrFirst ^^ shamt) (seg (seg ?Snside 0 (Lng ?Snside - 1 - 1)) 0 (?cN - 1))"
        by (rule seg_funpow_IncrFirst0[OF cm1ltSeg])
      finally show ?thesis using sS sSn by simp
    qed
    show ?thesis using segShift ceq by simp
  qed
  have butlBN: "butlast (Br ?Np) = P (seg ?Snside 0 (?cN - 1))" using butl BrNpPS by simp
  have collapse: "P ?S = map (IncrFirst ^^ shamt) (butlast (Br ?Np)) @ [last (P ?S)]"
    by (rule oper_d1pos_branch_collapse_concrete[OF ST multiS lowshift' butlBN])
  have collapse0: "Br ?M' = map (IncrFirst ^^ shamt) (butlast (Br ?Np)) @ [last (P ?S)]"
    using collapse BrM'PS by simp
  \<comment> \<open>identify \<open>LOW = butlast (Br M')\<close>, \<open>tail = last (Br M')\<close>\<close>
  have BrM'split: "Br ?M' = butlast (Br ?M') @ [last (Br ?M')]"
    using BrM'ne by (simp add: append_butlast_last_id)
  have LOWeq: "butlast (Br ?M') = map (IncrFirst ^^ shamt) (butlast (Br ?Np))"
    using collapse0 BrM'split by simp
  have tailEq: "last (Br ?M') = last (P ?S)" using collapse0 BrM'split by simp
  \<comment> \<open>(4) tail junction F8/F9\<close>
  have F8: "entry (last (P ?S)) 0 0 = entry (last (P ?Snside)) 0 0 + shamt"
    by (rule oper_d1pos_tail_junction(1)[OF ST multiS SnT multiSn F8end F9end])
  have F9: "entry (last (P ?S)) 1 0 \<le> entry (last (P ?Snside)) 1 0"
    by (rule oper_d1pos_tail_junction(2)[OF ST multiS SnT multiSn F8end F9end])
  have lastNp: "last (P ?Snside) = Br ?Np ! (Lng (Br ?Np) - 1)"
    using BrNpPS BrNpne by (simp add: last_conv_nth)
  \<comment> \<open>length and per-component shift on the LOW prefix\<close>
  have lenLOW: "length (butlast (Br ?M')) = Lng (Br ?Np) - 1"
    using LOWeq BrNpne by simp
  have prefix: "\<forall>J. J < length (butlast (Br ?M'))
                 \<longrightarrow> entry (butlast (Br ?M') ! J) 0 0 = entry (Br ?Np ! J) 0 0 + shamt
                   \<and> entry (butlast (Br ?M') ! J) 1 0 = entry (Br ?Np ! J) 1 0"
  proof (intro allI impI)
    fix J assume JL: "J < length (butlast (Br ?M'))"
    have JLN: "J < length (butlast (Br ?Np))" using JL LOWeq by simp
    have nthEq: "butlast (Br ?M') ! J = (IncrFirst ^^ shamt) (butlast (Br ?Np) ! J)"
      using LOWeq JLN by simp
    have nthBN: "butlast (Br ?Np) ! J = Br ?Np ! J" using JLN by (simp add: nth_butlast)
    have nodeShift: "butlast (Br ?M') ! J = (IncrFirst ^^ shamt) (Br ?Np ! J)"
      using nthEq nthBN by simp
    have JLNp: "J < length (Br ?Np)" using JLN by (simp add: length_butlast)
    have nodePos: "0 < Lng (Br ?Np ! J)"
    proof -
      have "Br ?Np ! J = P ?Snside ! J" using BrNpPS by simp
      moreover have "J < length (P ?Snside)" using JLNp BrNpPS by simp
      ultimately show ?thesis using idxsum_P_component_nonempty[OF SnT] by simp
    qed
    have node0: "entry ((IncrFirst ^^ shamt) (Br ?Np ! J)) 0 0
               = entry (Br ?Np ! J) 0 0 + shamt"
      by (rule entry_funpow_IncrFirst0[OF nodePos])
    have node1: "entry ((IncrFirst ^^ shamt) (Br ?Np ! J)) 1 0
               = entry (Br ?Np ! J) 1 0"
      by (rule entry_funpow_IncrFirst1[OF nodePos])
    show "entry (butlast (Br ?M') ! J) 0 0 = entry (Br ?Np ! J) 0 0 + shamt
        \<and> entry (butlast (Br ?M') ! J) 1 0 = entry (Br ?Np ! J) 1 0"
      using nodeShift node0 node1 by simp
  qed
  have tail0: "entry (last (Br ?M')) 0 0 = entry (Br ?Np ! (Lng (Br ?Np) - 1)) 0 0 + shamt"
    using tailEq F8 lastNp by simp
  have tail1: "entry (last (Br ?M')) 1 0 \<le> entry (Br ?Np ! (Lng (Br ?Np) - 1)) 1 0"
    using tailEq F9 lastNp by simp
  have le0N: "le0 N j0red j1red" using le0Np .
  have body:
    "j0red < j1red \<and> j1red \<le> Lng N - 1
       \<and> le0 N j0red j1red
       \<and> Br ?M' = butlast (Br ?M') @ [last (Br ?M')]
       \<and> Br (seg N j0red j1red) \<noteq> []
       \<and> length (butlast (Br ?M')) = Lng (Br (seg N j0red j1red)) - 1
       \<and> (\<forall>J. J < length (butlast (Br ?M'))
              \<longrightarrow> entry (butlast (Br ?M') ! J) 0 0 = entry (Br (seg N j0red j1red) ! J) 0 0 + shamt
                \<and> entry (butlast (Br ?M') ! J) 1 0 = entry (Br (seg N j0red j1red) ! J) 1 0)
       \<and> entry (last (Br ?M')) 0 0
           = entry (Br (seg N j0red j1red) ! (Lng (Br (seg N j0red j1red)) - 1)) 0 0 + shamt
       \<and> entry (last (Br ?M')) 1 0
           \<le> entry (Br (seg N j0red j1red) ! (Lng (Br (seg N j0red j1red)) - 1)) 1 0"
    using j0j1red j1redle le0N BrM'split BrNpne lenLOW prefix tail0 tail1 by blast
  show ?thesis
    by (intro exI[of _ j0red] exI[of _ j1red] exI[of _ shamt]
              exI[of _ "butlast (Br ?M')"] exI[of _ "last (Br ?M')"]) (rule body)
qed

text \<open>§6.8 cap8 — the bundled \<open>shamt = 0\<close> anchor facts for the LOW regB/boundary
  cells (\<open>jm2 \<le> A < Lng N-1\<close>).  All six facts (\<open>shiftEqB\<close>, \<open>boundEq0B\<close>, \<open>boundEq1B\<close>,
  \<open>lenPSeqB\<close>, \<open>cleMB\<close>, \<open>mleSB\<close>) at \<open>shamt = 0\<close>: the LOW window \<open>[A, A+m-1] \<subseteq> [A, LN-2]\<close>
  is read \<open>N\<close>-verbatim (@{thm [source] oper_d1pos_nth_low_verbatim}); the boundary
  index \<open>m = Lng Snside-1\<close> maps to N-index \<open>LN-1\<close> (row 0 agrees by
  @{thm [source] oper_d1pos_row0_agree}; row 1 reads \<open>entry N 1 jm2 \<le> entry N 1 (LN-1)\<close>
  by @{thm [source] oper_d1pos_ctx_r1le}).  \<open>cleMB\<close> = @{thm [source] oper_d1pos_clt_regB};
  \<open>lenPSeqB\<close> = @{thm [source] oper_d1pos_lenPSeq_unified}.  DEEP-VERIFIED rank-strat
  (python/d1pos_cap8_notbrleNp.py): all LOW dischargers hold.\<close>

lemma oper_d1pos_low_anchor_shamt0:
  fixes N :: pairseq and M :: pairseq
  assumes NT: "N \<in> T_PS" and monoN: "monoT N" and std: "N \<in> ST_PS"
    and LNgt: "1 < Lng N"
    and notzeroN: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hasparN: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1zN: "idx1 N (Lng N - 1) = 1"
    and Neq: "M = N[n]" and n1: "1 \<le> n"
    and j0plt: "j0' < Lng N - 1"
    and lt: "j0' < j1'" and jM: "j1' < Lng M"
    and bge: "Lng N - 1 \<le> j1'"
    and Ajm2: "parent N 1 (Lng N - 1) \<le> j0' + TrMax (seg M j0' j1') + 1"
    and AltN: "j0' + TrMax (seg M j0' j1') + 1 < Lng N - 1"
    and dpos: "entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1)"
    and multiM: "1 < length (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1'))"
    and le0M: "le0 M j0' j1'"
    and notbrle: "\<not> (TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1
                     \<or> le0 (seg M j0' j1') (TrMax (seg M j0' j1') + 1) (Lng (seg M j0' j1') - 1))"
    and tnc: "TrMax (seg N j0' (Lng N - 1)) \<le> Lng N - 1 - 1 - j0'"
    and stop: "\<not> nextR (seg ((N::pairseq)[n]) j0' j1') 1
                  (TrMax (seg N j0' (Lng N - 1))) (TrMax (seg N j0' (Lng N - 1)) + 1)"
  shows "seg (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 0
              (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1 - 1)
        = (IncrFirst ^^ (0::nat))
            (seg (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) 0
                 (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1 - 1))
       \<and> entry (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 0
              (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1)
        = entry (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) 0
                (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1) + (0::nat)
       \<and> entry (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') 1
              (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1)
        \<le> entry (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) 1
                (Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1)
       \<and> length (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1'))
        = length (P (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)))
       \<and> IdxSum (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')) !
            (length (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')) - 1)
          \<le> Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1
       \<and> Lng (seg N (j0' + TrMax (seg M j0' j1') + 1) (Lng N - 1)) - 1
        \<le> Lng (seg M (j0' + TrMax (seg M j0' j1') + 1) j1') - 1"
proof -
  let ?M = "(N::pairseq)[n]"
  let ?j1N = "Lng N - 1"
  let ?jm2 = "parent N 1 ?j1N"
  let ?w = "?j1N - ?jm2"
  let ?delta = "entry N 0 ?j1N - entry N 0 ?jm2"
  let ?T = "TrMax (seg M j0' j1')"
  let ?A = "j0' + ?T + 1"
  let ?S = "seg ?M ?A j1'"
  let ?Snside = "seg N ?A ?j1N"
  let ?m = "Lng ?Snside - 1"
  have j0lt: "?jm2 < ?j1N" by (rule oper_d1pos_ctx_j0lt[OF hasparN i1zN])
  have SeqM: "seg M ?A j1' = ?S" using Neq by simp
  \<comment> \<open>geometry\<close>
  have mval: "?m = ?j1N - ?A" using AltN by simp
  have w0: "0 < ?w" using j0lt by linarith
  have Aj1': "?A \<le> j1'" using AltN bge by linarith
  have LngS: "Lng ?S = Suc j1' - ?A" by simp
  have LngSn: "Lng ?Snside = Suc ?j1N - ?A" by simp
  \<comment> \<open>\<open>S \<in> T_PS\<close>, \<open>Snside \<in> T_PS\<close>\<close>
  have multiS: "1 < length (P ?S)" using multiM SeqM by simp
  have Sne: "?S \<noteq> []"
  proof
    assume "?S = []"
    hence "P ?S = [[]]" by (subst P.simps) (simp add: multiT_def zeroT_def monoT_def)
    thus False using multiS by simp
  qed
  have ST: "?S \<in> T_PS" using Sne by (auto simp: T_PS_def seg_def)
  have AltN': "?A < ?j1N" using AltN .
  have SnT: "?Snside \<in> T_PS" using AltN' by (simp add: T_PS_def seg_def)
  \<comment> \<open>abstract double-nat-sub atoms to fresh vars (CLAUDE.md linarith-loop fix)\<close>
  obtain aa e LS LSn where aa_def: "aa = ?A" and e_def: "e = ?j1N"
    and LS_def: "LS = Lng ?S" and LSn_def: "LSn = Lng ?Snside" by blast
  have mA: "?m = e - aa" using mval aa_def e_def by simp
  have LSeq: "LS = Suc j1' - aa" using LS_def LngS aa_def by simp
  have LSneq: "LSn = Suc e - aa" using LSn_def LngSn aa_def e_def by simp
  have aalt: "aa < e" using AltN' aa_def e_def by simp
  have ele: "e \<le> j1'" using bge e_def by simp
  have multiSn: "1 < length (P ?Snside)"
  proof -
    have notbrleNp: "\<not> (TrMax (seg N j0' ?j1N) = Lng (seg N j0' ?j1N) - 1
                       \<or> le0 (seg N j0' ?j1N) (TrMax (seg N j0' ?j1N) + 1)
                              (Lng (seg N j0' ?j1N) - 1))"
      by (rule oper_d1pos_ctx_notbrleNp_verbatim[OF NT LNgt notzeroN hasparN i1zN j0lt
            Neq n1 j0plt lt bge jM tnc stop notbrle])
    have j1redspanL: "?j1N \<le> j0' + (j1' - j0')" using bge lt by linarith
    have j1ltL: "j1' < Lng ?M" using jM Neq by simp
    have notbrle'L: "\<not> (TrMax (seg ?M j0' j1') = Lng (seg ?M j0' j1') - 1
                       \<or> le0 (seg ?M j0' j1') (TrMax (seg ?M j0' j1') + 1) (Lng (seg ?M j0' j1') - 1))"
      using notbrle Neq by simp
    have align: "TrMax (seg ?M j0' j1') = TrMax (seg N j0' ?j1N)
       \<and> Br (seg ?M j0' j1') = P (seg ?M (j0' + TrMax (seg ?M j0' j1') + 1) j1')
       \<and> Br (seg N j0' ?j1N) = P (seg N (j0' + TrMax (seg N j0' ?j1N) + 1) ?j1N)
       \<and> Br (seg ?M j0' j1') \<noteq> [] \<and> Br (seg N j0' ?j1N) \<noteq> []"
      by (rule oper_d1pos_notbrle_Br_align_regA[OF LNgt notzeroN hasparN i1zN j0lt n1
            le_refl j0plt j1redspanL refl lt j1ltL tnc stop notbrle'L])
    have TrEq: "?T = TrMax (seg N j0' ?j1N)" using align Neq by simp
    have Aeq: "?A = j0' + TrMax (seg N j0' ?j1N) + 1" using TrEq by simp
    have npT: "seg N j0' ?j1N \<in> T_PS" using j0plt by (simp add: T_PS_def seg_def)
    have multi0: "1 < length (P (seg N (j0' + TrMax (seg N j0' ?j1N) + 1) ?j1N))"
      by (rule oper_d1pos_ctx_period_multiNp[OF npT j0plt notbrleNp])
    show ?thesis using multi0 Aeq by simp
  qed
  \<comment> \<open>(mleSB)\<close>
  have mleSB: "?m \<le> Lng ?S - 1"
  proof -
    have "Lng ?Snside \<le> Lng ?S" using LngS LngSn bge AltN' by linarith
    thus ?thesis by linarith
  qed
  \<comment> \<open>(cleMB) via the regime-B anchor bound\<close>
  have Eub: "j1' < Lng ?M" using jM Neq by simp
  have cleMB0: "IdxSum (P ?S) ! (length (P ?S) - 1) \<le> Lng (seg N ?A ?j1N) - 1"
    by (rule oper_d1pos_clt_regB[OF LNgt notzeroN hasparN i1zN j0lt n1 Ajm2 AltN' bge
          Eub dpos multiS])
  \<comment> \<open>(shiftEqB) verbatim window \<open>[A, A+m-1] = [A, LN-2]\<close>: \<open>(IncrFirst^^0) = id\<close>\<close>
  have shiftEqB: "seg ?S 0 (?m - 1) = (IncrFirst ^^ (0::nat)) (seg ?Snside 0 (?m - 1))"
  proof -
    have segeq: "seg ?S 0 (?m - 1) = seg ?Snside 0 (?m - 1)"
    proof (rule nth_equalityI)
      have lenS: "length (seg ?S 0 (?m - 1)) = Suc (?m - 1)"
        unfolding seg_def using mval AltN' bge LngS by (simp add: min_def)
      have lenSn: "length (seg ?Snside 0 (?m - 1)) = Suc (?m - 1)"
        unfolding seg_def using mval AltN' LngSn by (simp add: min_def)
      show "length (seg ?S 0 (?m - 1)) = length (seg ?Snside 0 (?m - 1))"
        using lenS lenSn by simp
      fix k assume "k < length (seg ?S 0 (?m - 1))"
      hence kle: "k \<le> ?m - 1" using lenS by simp
      have kleA: "k \<le> (e - aa) - 1" using kle mA by simp
      have kS: "k < Lng ?S" using kleA aalt ele LSeq LS_def by linarith
      have kSn: "k < Lng ?Snside" using kleA aalt LSneq LSn_def by linarith
      have idxlt: "?A + k < ?j1N"
      proof -
        have "aa + k < e" using kleA aalt by linarith
        thus ?thesis using aa_def e_def by simp
      qed
      have ksuc: "k < Suc (?m - 1) - 0" using kle by simp
      have kSb: "k < Suc j1' - ?A" using kS LngS by simp
      have kSnb: "k < Suc ?j1N - ?A" using kSn LngSn by simp
      have "seg ?S 0 (?m - 1) ! k = ?S ! (0 + k)" by (rule seg_nth_eq[OF ksuc])
      also have "\<dots> = ?S ! k" by simp
      also have "\<dots> = ?M ! (?A + k)" by (rule seg_nth_eq[OF kSb])
      also have "\<dots> = N ! (?A + k)"
        by (rule oper_d1pos_nth_low_verbatim[OF LNgt notzeroN hasparN i1zN j0lt n1 idxlt])
      also have "\<dots> = ?Snside ! k" by (rule seg_nth_eq[OF kSnb, symmetric])
      also have "\<dots> = ?Snside ! (0 + k)" by simp
      also have "\<dots> = seg ?Snside 0 (?m - 1) ! k" by (rule seg_nth_eq[OF ksuc, symmetric])
      finally show "seg ?S 0 (?m - 1) ! k = seg ?Snside 0 (?m - 1) ! k" .
    qed
    thus ?thesis by simp
  qed
  \<comment> \<open>(boundEq0B) the boundary index \<open>m\<close> maps to N-index \<open>LN-1\<close>; row 0 agrees\<close>
  have mInS: "?A + ?m = ?j1N"
  proof -
    have "aa + (e - aa) = e" using aalt by simp
    thus ?thesis using mA aa_def e_def by simp
  qed
  have mSn: "?m < Lng ?Snside"
  proof -
    have "e - aa < LSn" using LSneq aalt by linarith
    thus ?thesis using mA LSn_def by simp
  qed
  have mS: "?m < Lng ?S"
  proof -
    have "e - aa < LS" using LSeq aalt ele by linarith
    thus ?thesis using mA LS_def by simp
  qed
  have bnd: "?j1N < Lng ?M" using bge Eub by linarith
  have boundEq0B: "entry ?S 0 ?m = entry ?Snside 0 ?m + (0::nat)"
  proof -
    have "entry ?S 0 ?m = entry ?M 0 (?A + ?m)" by (rule entry_seg[OF mS])
    also have "\<dots> = entry ?M 0 ?j1N" by (simp only: mInS)
    also have "\<dots> = entry N 0 ?j1N"
      by (rule oper_d1pos_row0_agree[OF LNgt notzeroN hasparN i1zN j0lt bnd order_refl])
    also have "\<dots> = entry ?Snside 0 ?m"
    proof -
      have "entry ?Snside 0 ?m = entry N 0 (?A + ?m)" by (rule entry_seg[OF mSn])
      also have "\<dots> = entry N 0 ?j1N" by (simp only: mInS)
      finally show ?thesis by (rule sym)
    qed
    finally show ?thesis by simp
  qed
  \<comment> \<open>(boundEq1B) row 1 at \<open>m\<close>: \<open>entry M 1 (LN-1) = entry N 1 jm2 \<le> entry N 1 (LN-1)\<close>\<close>
  have boundEq1B: "entry ?S 1 ?m \<le> entry ?Snside 1 ?m"
  proof -
    have n2: "1 < n"
    proof -
      have "Lng ?M = ?jm2 + n * ?w"
        by (rule oper_d1pos_LngM[OF LNgt notzeroN hasparN i1zN j0lt])
      hence "?jm2 + ?w < ?jm2 + n * ?w" using bnd j0lt by linarith
      hence "?w < n * ?w" by linarith
      thus ?thesis using w0 by (cases n) auto
    qed
    have e1M: "entry ?M 1 ?j1N = entry N 1 ?jm2"
    proof -
      have split: "?j1N = ?jm2 + 1 * ?w + 0" using j0lt by simp
      have "entry ?M 1 (?jm2 + 1 * ?w + 0) = entry N 1 (?jm2 + 0)"
        by (rule oper_d1pos_entry1[OF LNgt notzeroN hasparN i1zN j0lt n2]) (use w0 in simp)
      thus ?thesis using split by simp
    qed
    have r1le: "entry N 1 ?jm2 \<le> entry N 1 ?j1N"
      by (rule oper_d1pos_ctx_r1le[OF hasparN i1zN])
    have "entry ?S 1 ?m = entry ?M 1 (?A + ?m)" by (rule entry_seg[OF mS])
    also have "\<dots> = entry ?M 1 ?j1N" by (simp only: mInS)
    also have "\<dots> = entry N 1 ?jm2" using e1M by simp
    also have "\<dots> \<le> entry N 1 ?j1N" using r1le .
    also have "\<dots> = entry ?Snside 1 ?m"
    proof -
      have "entry ?Snside 1 ?m = entry N 1 (?A + ?m)" by (rule entry_seg[OF mSn])
      also have "\<dots> = entry N 1 ?j1N" by (simp only: mInS)
      finally show ?thesis by (rule sym)
    qed
    finally show ?thesis .
  qed
  \<comment> \<open>(lenPSeqB) via the period-unified component-count match\<close>
  have lenPSeqB: "length (P ?S) = length (P ?Snside)"
    by (rule oper_d1pos_lenPSeq_unified[OF ST multiS SnT multiSn mleSB cleMB0 shiftEqB
          boundEq0B])
  show ?thesis using shiftEqB boundEq0B boundEq1B lenPSeqB cleMB0 mleSB SeqM by simp
qed

text \<open>§6.8 cap8 — PERIODIC-BOUNDARY \<open>cleMB\<close>.  When the min-cap is ACTIVE
  (\<open>j1red = Lng N-1\<close>) the branch region \<open>S = seg M A j1'\<close> (\<open>A = AN + q0\<cdot>w\<close>, the
  period-shift image of \<open>Snside = seg N AN (Lng N-1)\<close>) extends PAST the boundary
  index \<open>m = Lng Snside - 1\<close>.  Every tail index \<open>x > m\<close> of \<open>S\<close> maps into the next
  block (\<open>q0+1\<close>), so by \<open>\<delta> > 0\<close> (@{thm [source] oper_d1pos_entry0} +
  @{thm [source] oper_d1pos_period_row0_floor}) it strictly exceeds the row-0 value
  at the boundary witness \<open>jj = m\<close> (which reads the period TOP, block \<open>q0\<close>); hence
  the left-min anchor \<open>c < m+1\<close>, i.e. \<open>c \<le> m\<close>.  Mirror of
  @{thm [source] oper_d1pos_clt_regB} with the boundary witness at \<open>jj = m\<close>.\<close>

lemma oper_d1pos_period_boundary_cleMB:
  fixes N :: pairseq and M :: pairseq
  assumes NT: "N \<in> T_PS" and monoN: "monoT N" and std: "N \<in> ST_PS"
    and LNgt: "1 < Lng N"
    and notzeroN: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hasparN: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1zN: "idx1 N (Lng N - 1) = 1"
    and Neq: "M = N[n]" and n1: "1 \<le> n"
    and lt: "j0' < j1'" and jM: "j1' < Lng M"
    and bge: "Lng N - 1 \<le> j1'"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and periodic: "Lng N - 1 \<le> j0'"
    and q0def: "q0 = (j0' - parent N 1 (Lng N - 1)) div (Lng N - 1 - parent N 1 (Lng N - 1))"
    and s0def: "s0 = (j0' - parent N 1 (Lng N - 1)) mod (Lng N - 1 - parent N 1 (Lng N - 1))"
    and j0reddef: "j0red = parent N 1 (Lng N - 1) + s0"
    and j1reddef: "j1red = min (j0red + (j1' - j0')) (Lng N - 1)"
    and shamtdef: "shamt = q0 * (entry N 0 (Lng N - 1) - entry N 0 (parent N 1 (Lng N - 1)))"
    and tnc: "TrMax (seg N j0red j1red) \<le> j1red - 1 - j0red"
    and stop: "\<not> nextR (seg ((N::pairseq)[n]) j0' j1') 1
                  (TrMax (seg N j0red j1red)) (TrMax (seg N j0red j1red) + 1)"
    and multiNp: "1 < length (P (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red))"
    and multiS: "1 < length (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1'))"
    and notbrle: "\<not> (TrMax (seg M j0' j1') = Lng (seg M j0' j1') - 1
                     \<or> le0 (seg M j0' j1') (TrMax (seg M j0' j1') + 1) (Lng (seg M j0' j1') - 1))"
    and boundary: "\<not> j1red < Lng N - 1"
  shows "IdxSum (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')) !
            (length (P (seg M (j0' + TrMax (seg M j0' j1') + 1) j1')) - 1)
          \<le> Lng (seg N (j0red + TrMax (seg N j0red j1red) + 1) j1red) - 1"
proof -
  let ?M = "(N::pairseq)[n]"
  let ?j1N = "Lng N - 1"
  let ?jm2 = "parent N 1 ?j1N"
  let ?w = "?j1N - ?jm2"
  let ?delta = "entry N 0 ?j1N - entry N 0 ?jm2"
  let ?Mp = "seg ?M j0' j1'"
  let ?Np = "seg N j0red j1red"
  let ?T = "TrMax (seg M j0' j1')"
  let ?A = "j0' + ?T + 1"
  let ?tN = "TrMax ?Np"
  let ?AN = "j0red + ?tN + 1"
  let ?S = "seg ?M ?A j1'"
  let ?Snside = "seg N ?AN j1red"
  let ?m = "Lng ?Snside - 1"
  \<comment> \<open>geometry\<close>
  have MNn: "M = ?M" using Neq .
  have j1lt: "j1' < Lng ?M" using jM Neq by simp
  have w0: "0 < ?w" using j0lt by linarith
  have s0lt: "s0 < ?w" using s0def w0 by simp
  have j0reds: "j0red = ?jm2 + s0" using j0reddef .
  have j0redlt: "j0red < ?j1N" using j0reds s0lt by linarith
  have j0pge2: "?jm2 \<le> j0'" using periodic j0lt by linarith
  have j0'split: "j0' - ?jm2 = q0 * ?w + s0" using q0def s0def by (simp add: mult.commute)
  have j0'eq: "j0' = ?jm2 + q0 * ?w + s0" using j0'split j0pge2 by linarith
  have q0n: "q0 < n"
  proof -
    have "j0' < Lng ?M" using lt j1lt by linarith
    hence "j0' < ?jm2 + n * ?w"
      using oper_d1pos_LngM[OF LNgt notzeroN hasparN i1zN j0lt] Neq by simp
    hence "q0 * ?w + s0 < n * ?w" using j0'eq by linarith
    hence "q0 * ?w < n * ?w" using s0lt by linarith
    thus ?thesis using w0 by simp
  qed
  have j1redb: "j1red = ?j1N" using boundary j1reddef by simp
  have j1redle: "j1red \<le> ?j1N" using j1redb by simp
  have j0j1red: "j0red < j1red" using j0redlt j1redb by simp
  have j1redspan: "j1red \<le> j0red + (j1' - j0')" using j1reddef by simp
  \<comment> \<open>TrEq: \<open>TrMax M' = TrMax Np\<close>, hence \<open>A = AN + q0\<cdot>w\<close>\<close>
  have notbrle': "\<not> (TrMax ?Mp = Lng ?Mp - 1 \<or> le0 ?Mp (TrMax ?Mp + 1) (Lng ?Mp - 1))"
    using notbrle MNn by simp
  have stop': "\<not> nextR ?Mp 1 ?tN (?tN + 1)" using stop .
  have align: "TrMax ?Mp = ?tN
       \<and> Br ?Mp = P (seg ?M (j0' + TrMax ?Mp + 1) j1')
       \<and> Br ?Np = P (seg N (j0red + ?tN + 1) j1red)
       \<and> Br ?Mp \<noteq> [] \<and> Br ?Np \<noteq> []"
    by (rule oper_d1pos_notbrle_Br_align[OF NT LNgt notzeroN hasparN i1zN j0lt n1 q0n
            j0redlt j0reds s0lt j0'eq shamtdef j1redle j0j1red j1redspan lt j1lt tnc stop'
            notbrle'])
  have TrEq: "?T = ?tN" using align MNn by simp
  have Aeq: "?A = ?AN + q0 * ?w"
  proof -
    have "?A = j0' + ?tN + 1" using TrEq by simp
    also have "\<dots> = (?jm2 + q0 * ?w + s0) + ?tN + 1" using j0'eq by simp
    also have "\<dots> = (?jm2 + s0 + ?tN + 1) + q0 * ?w" by simp
    also have "\<dots> = (j0red + ?tN + 1) + q0 * ?w" using j0reds by simp
    finally show ?thesis by simp
  qed
  \<comment> \<open>\<open>S \<in> T_PS\<close>; boundary geometry \<open>m = LN-1 - AN\<close>, \<open>AN < LN-1\<close>\<close>
  have multiSn: "1 < length (P ?Snside)" using multiNp by simp
  have ANlt: "?AN < ?j1N"
  proof (rule ccontr)
    assume "\<not> ?AN < ?j1N"
    hence "j1red \<le> ?AN" using j1redb by simp
    hence "Lng ?Snside \<le> 1" by simp
    hence nc: "\<not> (multiT ?Snside \<and> 1 < Lng ?Snside)" by simp
    have "P ?Snside = [?Snside]" by (subst P.simps) (rule if_not_P[OF nc])
    thus False using multiSn by simp
  qed
  have Sne: "?S \<noteq> []"
  proof
    assume "?S = []"
    hence "P ?S = [[]]" by (subst P.simps) (simp add: multiT_def zeroT_def monoT_def)
    have "P (seg M ?A j1') = P ?S" using MNn by simp
    thus False using multiS TrEq \<open>P ?S = [[]]\<close> by simp
  qed
  have ST: "?S \<in> T_PS" using Sne by (auto simp: T_PS_def seg_def)
  have multiS': "1 < length (P ?S)" using multiS MNn TrEq by simp
  have LngS: "Lng ?S = Suc j1' - ?A" by simp
  have LngSn: "Lng ?Snside = Suc ?j1N - ?AN" using j1redb by simp
  have mval: "?m = ?j1N - ?AN"
  proof -
    obtain an e where an_def: "an = ?AN" and e_def: "e = ?j1N" by blast
    have "?m = (Suc e - an) - 1" using LngSn an_def e_def by simp
    also have "\<dots> = e - an" using ANlt an_def e_def by simp
    finally show ?thesis using an_def e_def by simp
  qed
  obtain w where wdef: "?w = w" by blast
  have w0': "0 < w" using w0 wdef by simp
  have lenMn: "Lng ?M = ?jm2 + n * w"
    using oper_d1pos_LngM[OF LNgt notzeroN hasparN i1zN j0lt] wdef by simp
  \<comment> \<open>witness at the boundary index \<open>jj = m\<close>: \<open>A + m = jm2 + (q0+1)\<cdot>w\<close> (block boundary)\<close>
  have ANqlt: "?AN \<le> ?j1N" using ANlt by linarith
  have jm2w: "?j1N = ?jm2 + w" using wdef j0lt by simp
  have Am: "?A + ?m = ?jm2 + (Suc q0) * w"
  proof -
    have "?A + ?m = ?AN + q0 * w + (?j1N - ?AN)" using Aeq mval wdef by simp
    also have "\<dots> = q0 * w + ?j1N" using ANqlt by simp
    also have "\<dots> = ?jm2 + (Suc q0) * w" using jm2w by simp
    finally show ?thesis .
  qed
  have qsn: "Suc q0 \<le> n" using q0n by simp
  \<comment> \<open>boundary witness sits AT \<open>j1'\<close> or below: \<open>A+m = jm2 + (q0+1)w = j1N + q0\<cdot>w \<le> j1'\<close>,
     the last step from the cap-active span \<open>j1N = j1red \<le> j0red+(j1'-j0') = j1'-q0\<cdot>w\<close>.\<close>
  have spanle: "?j1N + q0 * w \<le> j1'"
  proof -
    have j0'le: "j0' \<le> j1'" using lt by simp
    have sp1: "?j1N \<le> j0red + (j1' - j0')" using j1redspan j1redb by simp
    \<comment> \<open>\<open>j0red + (j1'-j0') = j1' - q0\<cdot>w\<close> via \<open>j0red = jm2+s0\<close>, \<open>j0' = jm2 + q0\<cdot>w + s0\<close>\<close>
    have decomp: "j0red + (j1' - j0') = j1' - q0 * w"
    proof -
      obtain b qw J0 J1 where bdef: "b = ?jm2 + s0" and qwdef: "qw = q0 * w"
        and J0def: "J0 = j0'" and J1def: "J1 = j1'" by blast
      have jr: "j0red = b" using j0reds bdef by simp
      have j0bq: "J0 = b + qw" using j0'eq wdef bdef qwdef J0def by simp
      have J0le: "J0 \<le> J1" using j0'le J0def J1def by simp
      have "j0red + (j1' - j0') = b + (J1 - J0)" using jr J0def J1def by simp
      also have "\<dots> = b + (J1 - (b + qw))" using j0bq by simp
      also have "\<dots> = J1 - qw" using j0bq J0le by linarith
      finally show ?thesis using qwdef J1def by simp
    qed
    have jle: "?j1N \<le> j1' - q0 * w" using sp1 decomp by simp
    have qwle: "q0 * w \<le> j1'"
    proof -
      have "?jm2 + q0 * w + s0 = j0'" using j0'eq wdef by simp
      thus ?thesis using j0'le by linarith
    qed
    show ?thesis using jle qwle by linarith
  qed
  have AmleE: "?A + ?m \<le> j1'"
  proof -
    have "?A + ?m = ?jm2 + Suc q0 * w" using Am .
    also have "\<dots> = ?j1N + q0 * w" using jm2w by simp
    finally show ?thesis using spanle by simp
  qed
  have jjltS: "?m < Lng ?S"
  proof -
    obtain aa LSv where aa_def: "aa = ?A" and LSv_def: "LSv = Lng ?S" by blast
    have "LSv = Suc j1' - aa" using LngS LSv_def aa_def by simp
    moreover have "aa + ?m \<le> j1'" using AmleE aa_def by simp
    ultimately show ?thesis using LSv_def by linarith
  qed
  \<comment> \<open>\<open>entry S 0 m = entry N 0 (LN-1) + q0\<cdot>\<delta>\<close> (block \<open>q0\<close>, offset \<open>w\<close> = top of block)\<close>
  have eSm: "entry ?S 0 ?m = entry N 0 ?j1N + q0 * ?delta"
  proof (cases "Suc q0 < n")
    case True
    have decode: "entry ?M 0 (?jm2 + (Suc q0) * ?w + 0)
                = entry N 0 (?jm2 + 0) + (Suc q0) * ?delta"
      by (rule oper_d1pos_entry0[OF LNgt notzeroN hasparN i1zN j0lt True]) (use w0 in simp)
    have "entry ?S 0 ?m = entry ?M 0 (?A + ?m)" using jjltS by (simp add: entry_seg)
    also have "\<dots> = entry ?M 0 (?jm2 + (Suc q0) * ?w + 0)" using Am wdef by simp
    also have "\<dots> = entry N 0 ?jm2 + (Suc q0) * ?delta" using decode by simp
    also have "\<dots> = entry N 0 ?j1N + q0 * ?delta"
    proof -
      have dpos': "0 < ?delta" using oper_d1pos_ctx_dpos[OF hasparN i1zN j0lt] by simp
      have "entry N 0 ?j1N = entry N 0 ?jm2 + ?delta" using dpos' by simp
      thus ?thesis by simp
    qed
    finally show ?thesis .
  next
    case False
    have qeqn: "Suc q0 = n" using qsn False by simp
    \<comment> \<open>\<open>A + m = jm2 + n\<cdot>w = Lng M\<close>, but \<open>A + m \<le> j1' < Lng M\<close>: contradiction, so vacuous\<close>
    have "?A + ?m = ?jm2 + n * w" using Am qeqn by simp
    hence "?A + ?m = Lng ?M" using lenMn by simp
    moreover have "?A + ?m \<le> j1'" using AmleE .
    ultimately have False using j1lt by simp
    thus ?thesis by simp
  qed
  \<comment> \<open>uniform witness over the STRICT tail \<open>[m+1, Lng S-1]\<close>\<close>
  have wit: "\<And>x. Suc ?m \<le> x \<Longrightarrow> x \<le> Lng ?S - 1 \<Longrightarrow> entry ?S 0 ?m < entry ?S 0 x"
  proof -
    fix x assume xlo: "Suc ?m \<le> x" and xhi: "x \<le> Lng ?S - 1"
    have AxgN: "?jm2 + (Suc q0) * w < ?A + x" using xlo Am by linarith
    have AxleE: "?A + x \<le> j1'"
    proof -
      obtain aa LSv where aa_def: "aa = ?A" and LSv_def: "LSv = Lng ?S" by blast
      have xL: "x \<le> LSv - 1" using xhi LSv_def by simp
      have LSform: "LSv = Suc j1' - aa" using LngS LSv_def aa_def by simp
      have LSpos: "0 < LSv" using jjltS LSv_def by simp
      have aaj: "aa \<le> j1'" using LSform LSpos by linarith
      have "aa + x \<le> j1'" using xL LSform aaj by linarith
      thus ?thesis using aa_def by simp
    qed
    have Aj1'b: "?A \<le> j1'" using AmleE by linarith
    have xltS: "x < Lng ?S"
    proof -
      obtain LSv aa where LSv_def: "LSv = Lng ?S" and aa_def: "aa = ?A" by blast
      have "x \<le> LSv - 1" using xhi LSv_def by simp
      moreover have "LSv = Suc j1' - aa" using LngS LSv_def aa_def by simp
      moreover have "aa \<le> j1'" using Aj1'b aa_def by simp
      ultimately show ?thesis using LSv_def by linarith
    qed
    let ?qx = "(?A + x - ?jm2) div w"  let ?sx = "(?A + x - ?jm2) mod w"
    have sxw: "?sx < w" using w0' by simp
    have Axge: "?jm2 \<le> ?A + x" using AxgN by linarith
    have xsplit: "?A + x = ?jm2 + ?qx * w + ?sx"
      using div_mult_mod_eq[of "?A + x - ?jm2" w] Axge by (simp add: mult.commute)
    have qxn: "?qx < n"
    proof -
      obtain ax where ax_def: "ax = ?A + x" by blast
      have axj: "ax \<le> j1'" using AxleE ax_def by simp
      have axge: "?jm2 \<le> ax" using Axge ax_def by simp
      have "ax - ?jm2 < n * w" using axj j1lt lenMn axge by linarith
      hence "?A + x - ?jm2 < n * w" using ax_def by simp
      thus ?thesis by (rule less_mult_imp_div_less)
    qed
    have sxw': "?sx < ?j1N - ?jm2" using sxw wdef by simp
    have eSx: "entry ?S 0 x = entry N 0 (?jm2 + ?sx) + ?qx * ?delta"
    proof -
      have block: "entry ?M 0 (?jm2 + ?qx * ?w + ?sx)
                 = entry N 0 (?jm2 + ?sx) + ?qx * ?delta"
        by (rule oper_d1pos_entry0[OF LNgt notzeroN hasparN i1zN j0lt qxn sxw'])
      have xsplit': "?A + x = ?jm2 + ?qx * ?w + ?sx" using xsplit wdef by simp
      have "entry ?S 0 x = entry ?M 0 (?A + x)" using xltS by (simp add: entry_seg)
      thus ?thesis using xsplit' block by simp
    qed
    \<comment> \<open>\<open>A + x > jm2 + (Suc q0)*w\<close> so the floor block \<open>qx \<ge> Suc q0\<close>\<close>
    have floorgt: "(Suc q0) * w < ?qx * w + ?sx"
    proof -
      have "?jm2 + (Suc q0) * w < ?jm2 + ?qx * w + ?sx" using AxgN xsplit by simp
      thus ?thesis by linarith
    qed
    have qxgt: "Suc q0 \<le> ?qx"
    proof (rule ccontr)
      assume "\<not> Suc q0 \<le> ?qx"
      hence "?qx \<le> q0" by simp
      hence "?qx * w \<le> q0 * w" by (rule mult_le_mono1)
      hence "?qx * w + ?sx < q0 * w + w" using sxw by linarith
      also have "q0 * w + w = (Suc q0) * w" by simp
      finally show False using floorgt by linarith
    qed
    have dpos': "0 < ?delta"
      using oper_d1pos_ctx_dpos[OF hasparN i1zN j0lt] by simp
    have floor_le: "entry N 0 ?jm2 \<le> entry N 0 (?jm2 + ?sx)"
      by (rule oper_d1pos_period_row0_floor[OF hasparN i1zN j0lt]) (use sxw' in simp)
    have topval: "entry N 0 ?j1N = entry N 0 ?jm2 + ?delta" using dpos' by simp
    have qd: "q0 * ?delta + ?delta \<le> ?qx * ?delta"
    proof -
      have "Suc q0 * ?delta \<le> ?qx * ?delta" by (rule mult_le_mono1[OF qxgt])
      thus ?thesis by simp
    qed
    \<comment> \<open>abstract \<open>\<delta>\<close>-products + entries to fresh vars (linarith \<open>\<delta>\<close>-nat-sub fix)\<close>
    obtain dd ej em eqx where dd_def: "dd = q0 * ?delta + ?delta"
      and ej_def: "ej = entry N 0 ?jm2" and em_def: "em = entry N 0 (?jm2 + ?sx)"
      and eqx_def: "eqx = ?qx * ?delta" by blast
    have qdA: "dd \<le> eqx" using qd dd_def eqx_def by simp
    have floorA: "ej \<le> em" using floor_le ej_def em_def by simp
    have "entry ?S 0 ?m = entry N 0 ?jm2 + ?delta + q0 * ?delta" using eSm topval by simp
    also have "\<dots> = ej + dd" using dd_def ej_def by simp
    also have "\<dots> \<le> em + eqx" using qdA floorA by linarith
    also have "\<dots> = entry N 0 (?jm2 + ?sx) + ?qx * ?delta" using em_def eqx_def by simp
    also have "\<dots> = entry ?S 0 x" using eSx by simp
    finally have le: "entry ?S 0 ?m \<le> entry ?S 0 x" .
    \<comment> \<open>strictness: \<open>qx \<ge> q0+1\<close> gives a strict \<open>\<delta>\<close> gap (case-split below)\<close>
    show "entry ?S 0 ?m < entry ?S 0 x"
    proof (cases "q0 * ?delta + ?delta = ?qx * ?delta \<and> entry N 0 ?jm2 = entry N 0 (?jm2 + ?sx)")
      case True
      \<comment> \<open>tight floor: then \<open>qx = q0+1\<close> and \<open>sx = 0\<close>; but \<open>floorgt\<close> forces \<open>sx > 0\<close> when
         \<open>qx = q0+1\<close>, contradiction, so this case undercuts via STRICT period floor\<close>
      have qeq: "?qx = Suc q0"
      proof -
        have e0: "q0 * ?delta + ?delta = ?qx * ?delta" using True by (rule conjunct1)
        obtain dl ql where dl_def: "dl = ?delta" and ql_def: "ql = ?qx" by blast
        have dlpos: "0 < dl" using dpos' unfolding dl_def by assumption
        have e0': "q0 * dl + dl = ql * dl" using e0 unfolding dl_def ql_def by assumption
        have e2: "Suc q0 * dl = ql * dl"
        proof -
          have "Suc q0 * dl = q0 * dl + dl" by simp
          also have "\<dots> = ql * dl" using e0' by simp
          finally show ?thesis .
        qed
        have dlne: "dl \<noteq> 0" using dlpos by simp
        have "Suc q0 = ql \<or> dl = 0" using e2 by (simp only: mult_cancel2)
        hence sql: "Suc q0 = ql" using dlne by blast
        have "Suc q0 = ?qx" using sql ql_def by simp
        thus ?thesis by (rule sym)
      qed
      have sxpos: "0 < ?sx"
      proof -
        have fg: "(Suc q0) * w < ?qx * w + ?sx" using floorgt .
        have fg2: "(Suc q0) * w < (Suc q0) * w + ?sx" using fg qeq by (simp only: qeq)
        obtain bb sv where bb_def: "bb = (Suc q0) * w" and sv_def: "sv = ?sx" by blast
        have "bb < bb + sv" using fg2 bb_def sv_def by (simp only: bb_def sv_def)
        hence "0 < sv" by linarith
        thus ?thesis using sv_def by (simp only: sv_def)
      qed
      have strict: "entry N 0 ?jm2 < entry N 0 (?jm2 + ?sx)"
        by (rule oper_d1pos_strict_period_floor[OF hasparN i1zN j0lt sxpos]) (use sxw' in simp)
      have strictA: "ej < em" using strict ej_def em_def by simp
      have "entry ?S 0 ?m = entry N 0 ?jm2 + ?delta + q0 * ?delta" using eSm topval by simp
      also have "\<dots> = ej + dd" using dd_def ej_def by simp
      also have "\<dots> < em + eqx" using strictA qdA by linarith
      also have "\<dots> = entry N 0 (?jm2 + ?sx) + ?qx * ?delta" using em_def eqx_def by simp
      also have "\<dots> = entry ?S 0 x" using eSx by simp
      finally show ?thesis .
    next
      case False
      have FalseA: "\<not> (dd = eqx \<and> ej = em)" using False dd_def eqx_def ej_def em_def by simp
      have strictgapA: "dd < eqx \<or> ej < em" using FalseA qdA floorA by linarith
      have "entry ?S 0 ?m = entry N 0 ?jm2 + (q0 * ?delta + ?delta)" using eSm topval by simp
      also have "\<dots> = ej + dd" using dd_def ej_def by simp
      also have "\<dots> < em + eqx" using strictgapA qdA floorA by linarith
      also have "\<dots> = entry N 0 (?jm2 + ?sx) + ?qx * ?delta" using em_def eqx_def by simp
      also have "\<dots> = entry ?S 0 x" using eSx by simp
      finally show ?thesis .
    qed
  qed
  have jjltk: "?m < Suc ?m" by simp
  have "IdxSum (P ?S) ! (length (P ?S) - 1) < Suc ?m"
    by (rule anchor_lt_of_uniform_witness[OF ST multiS' jjltk wit])
  hence "IdxSum (P ?S) ! (length (P ?S) - 1) \<le> ?m" by simp
  thus ?thesis using MNn TrEq by simp
qed

text \<open>§6.8 d0pos \<open>\<not>brle\<close> — agent-A IDENTIFICATION STUB (\<open>oper_d1pos_notbrle_LOW_take_eq\<close>).
  In the residual d0pos \<open>\<not>brle\<close> context (\<open>N\<close> monoT std, \<open>i\<^sub>1=1\<close>, \<open>M=N[n]\<close>,
  \<open>M'=seg M j0' j1'\<close> monoT, \<open>le0 M j0' j1'\<close>, \<open>Lng N-1 \<le> j1'\<close>, \<open>\<not>brle\<close>) the article's
  regime A+B assembly identifies an \<open>N\<close>-side slice \<open>N\<^sub>p = seg N j\<^sub>0\<^sup>red (Lng N-1)\<close>
  (\<open>j\<^sub>0\<^sup>red\<close> the block-period reduction of the LOW source start) whose branch
  \<open>Br N\<^sub>p\<close> is NON-empty, splits as \<open>take J\<^sub>1 (Br N\<^sub>p) @ [Br N\<^sub>p ! J\<^sub>1]\<close> with
  \<open>J\<^sub>1 = Lng (Br N\<^sub>p) - 1\<close>, and yields \<open>Br M' = LOW @ [tail]\<close> where the LOW prefix is
  the \<open>(IncrFirst^^(q\<cdot>\<delta>))\<close>-shift of \<open>take J\<^sub>1 (Br N\<^sub>p)\<close> (per-component) and the tail is
  the single \<open>\<not>multiT\<close> last node, whose head ties the shifted \<open>Br N\<^sub>p ! J\<^sub>1\<close> head in
  row 0 and is \<open>\<le>\<close> in row 1.  This is the precise block-fold + first-node geometry
  (agent-A's job: \<open>oper_d1pos_seg_P_*\<close> + @{thm [source] m_6_4_FirstNodes_TrMax_Joints}
  + @{thm [source] oper_d1pos_notbrle_LOW_eq}); the PARENT replaces this stub at merge.
  DEEP-verified (python/d1pos_notbrle_wire.py, rank-stratified std gen len\<le>9 KMAX=5:
  all 30 \<open>\<not>brle\<close> residual cases admit such \<open>N\<^sub>p\<close> with the full
  \<open>descending_shift_append\<close> fact set — lenPRE, pre0, pre1, tl0, tl1 — 0 failures).
  NB: \<open>Br N\<^sub>p\<close>'s descending-ness is NOT part of the stub — it is supplied by \<open>IHk\<close>
  on \<open>N\<close> (\<open>N \<in> SkT_PS k\<close>) at the assembly site, so the stub stays a pure
  structural identification (no circular/forward citation).\<close>

lemma oper_d1pos_notbrle_LOW_take_eq:
  fixes N :: pairseq and M :: pairseq
  assumes NT: "N \<in> T_PS" and monoN: "monoT N" and std: "N \<in> ST_PS"
    and LNgt: "1 < Lng N"
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
  \<comment> \<open>AGENT-cap8 ASSEMBLY — the 4-cell case-split dispatch.  The precise block-fold
     + first-node geometry is supplied by the four GREEN cell lemmas
     (@{thm [source] oper_d1pos_notbrle_LOW_take_eq_regA} / \<open>_regB\<close> / \<open>_boundary\<close> /
     \<open>_periodic\<close>); this assembly derives the context dischargers, case-splits on the
     regime (\<open>A vs jm2\<close>, \<open>j0' vs jm2\<close>, \<open>j0' vs Lng N-1\<close>), and feeds each cell its
     extra hypotheses.  Witnesses = formula G (see the cell lemmas).  DEEP-VERIFIED
     rank-stratified (python/d1pos_cap8_split.py, _Aeq.py, _notbrleNp.py):
     all residual cases are covered by the 4 cells; \<open>A < Lng N-1\<close> whenever
     \<open>j0' < Lng N-1\<close> (956/0 at KMAX=8); notbrleNp/multiNp/le0Np all TRUE on the low
     branch (264/0 at KMAX=7).\<close>
proof -
  let ?M' = "seg M j0' j1'"
  let ?T = "TrMax ?M'"
  let ?A = "j0' + ?T + 1"
  let ?j1N = "Lng N - 1"
  let ?jm2 = "parent N 1 ?j1N"
  let ?w = "?j1N - ?jm2"
  let ?delta = "entry N 0 ?j1N - entry N 0 ?jm2"
  \<comment> \<open>basic geometry and the regime-agnostic context dischargers\<close>
  have j1lt: "j1' < Lng ((N::pairseq)[n])" using jM Neq by simp
  have j0lt: "?jm2 < ?j1N" by (rule oper_d1pos_ctx_j0lt[OF hasparN i1zN])
  have dpos: "entry N 0 ?jm2 < entry N 0 ?j1N"
    by (rule oper_d1pos_ctx_dpos[OF hasparN i1zN j0lt])
  have multiM: "1 < length (P (seg M ?A j1'))"
    by (rule oper_d1pos_ctx_multiM[OF M'T lt notbrle])
  have notbrle': "\<not> (TrMax (seg ((N::pairseq)[n]) j0' j1')
                        = Lng (seg ((N::pairseq)[n]) j0' j1') - 1
                      \<or> le0 (seg ((N::pairseq)[n]) j0' j1')
                            (TrMax (seg ((N::pairseq)[n]) j0' j1') + 1)
                            (Lng (seg ((N::pairseq)[n]) j0' j1') - 1))"
    using notbrle Neq by simp
  have le0M': "le0 ((N::pairseq)[n]) j0' j1'" using le0M Neq by simp
  \<comment> \<open>case-split on the slice-start position: PERIODIC (\<open>j0' \<ge> Lng N-1\<close>) vs LOW\<close>
  show ?thesis
  proof (cases "?j1N \<le> j0'")
    case periodic: True
    \<comment> \<open>CELL 4 — block index \<open>q0 \<ge> 1\<close>, slice start in the periodic tail.  Formula-G
       witnesses; the min-cap \<open>j1red\<close> splits into INTERIOR (cap inactive) / BOUNDARY.\<close>
    define q0 where "q0 = (j0' - ?jm2) div ?w"
    define s0 where "s0 = (j0' - ?jm2) mod ?w"
    define j0red where "j0red = ?jm2 + s0"
    define j1red where "j1red = min (j0red + (j1' - j0')) ?j1N"
    define shamt where "shamt = q0 * ?delta"
    let ?Np = "seg N j0red j1red"
    let ?AN = "j0red + TrMax ?Np + 1"
    have w0: "0 < ?w" using j0lt by linarith
    have s0lt: "s0 < ?w" using s0_def w0 by simp
    have j0reds: "j0red = ?jm2 + s0" using j0red_def .
    have j0redlt: "j0red < ?j1N" using j0reds s0lt by linarith
    have j0pge2: "?jm2 \<le> j0'" using periodic j0lt by linarith
    have j0'split: "j0' - ?jm2 = q0 * ?w + s0"
      using q0_def s0_def by (simp add: mult.commute)
    have j0'eq: "j0' = ?jm2 + q0 * ?w + s0" using j0'split j0pge2 by linarith
    have q0n: "q0 < n"
    proof -
      have "j0' < Lng ((N::pairseq)[n])" using lt j1lt by linarith
      hence "j0' < ?jm2 + n * ?w"
        using oper_d1pos_LngM[OF LNgt notzeroN hasparN i1zN j0lt] Neq by simp
      hence "q0 * ?w + s0 < n * ?w" using j0'eq by linarith
      hence "q0 * ?w < n * ?w" using s0lt by linarith
      thus ?thesis using w0 by simp
    qed
    have j1redle: "j1red \<le> ?j1N" using j1red_def by simp
    have j0j1red: "j0red < j1red"
    proof -
      have "j0red < j0red + (j1' - j0')" using lt by simp
      moreover have "j0red < ?j1N" using j0redlt .
      ultimately show ?thesis using j1red_def by simp
    qed
    have j1redspan: "j1red \<le> j0red + (j1' - j0')" using j1red_def by simp
    \<comment> \<open>tnc (capped) + stop (capped/uncapped) + notbrleNp + multiNp + le0Np.
       Split on whether the min-cap is ACTIVE (\<open>LN-1 < j0red+(j1'-j0')\<close>).\<close>
    have tnc: "TrMax ?Np \<le> j1red - 1 - j0red"
    proof (cases "?j1N < j0red + (j1' - j0')")
      case capactive: True
      have capeq: "j1red = ?j1N" using j1red_def capactive by simp
      have spanstrict: "j1red < j0red + (j1' - j0')" using capeq capactive by simp
      show ?thesis
        by (rule oper_d1pos_ctx_tnc_capped[OF NT monoN std LNgt notzeroN hasparN i1zN
              j0lt n1 q0n j0redlt j0reds s0lt j0'eq shamt_def j1redle j0j1red capeq
              spanstrict lt j1lt notbrle'])
    next
      case False
      have span: "j1red = j0red + (j1' - j0')" using j1red_def False by simp
      have tncstrict: "TrMax ?Np < j1red - 1 - j0red"
        by (rule oper_d1pos_ctx_period_tncstrict_uncapped[OF NT LNgt notzeroN hasparN
              i1zN j0lt n1 q0n j0redlt j0reds s0lt j0'eq shamt_def j1redle j0j1red span
              lt j1lt notbrle'])
      thus ?thesis by linarith
    qed
    have stop: "\<not> nextR (seg ((N::pairseq)[n]) j0' j1') 1
                  (TrMax ?Np) (TrMax ?Np + 1)"
    proof (cases "?j1N < j0red + (j1' - j0')")
      case capactive: True
      have capeq: "j1red = ?j1N" using j1red_def capactive by simp
      have spanstrict: "j1red < j0red + (j1' - j0')" using capeq capactive by simp
      show ?thesis
        by (rule oper_d1pos_ctx_stop_direct[OF NT monoN std LNgt notzeroN hasparN i1zN
              j0lt n1 q0n j0redlt j0reds s0lt j0'eq shamt_def j1redle j0j1red capeq
              spanstrict lt j1lt le0M' notbrle'])
    next
      case False
      have span: "j1red = j0red + (j1' - j0')" using j1red_def False by simp
      have tncstrict: "TrMax ?Np < j1red - 1 - j0red"
        by (rule oper_d1pos_ctx_period_tncstrict_uncapped[OF NT LNgt notzeroN hasparN
              i1zN j0lt n1 q0n j0redlt j0reds s0lt j0'eq shamt_def j1redle j0j1red span
              lt j1lt notbrle'])
      show ?thesis
        by (rule oper_d1pos_ctx_stop_direct_strict[OF NT monoN std LNgt notzeroN hasparN
              i1zN j0lt n1 q0n j0redlt j0reds s0lt j0'eq shamt_def j1redle j0j1red span
              lt j1lt tncstrict])
    qed
    \<comment> \<open>\<open>Np \<in> T_PS\<close>, le0Np, notbrleNp, multiNp\<close>
    have NpT: "?Np \<in> T_PS" using j0j1red by (simp add: T_PS_def seg_def)
    have le0Np: "le0 N j0red j1red"
      by (rule oper_d1pos_ctx_period_le0Np[OF LNgt notzeroN hasparN i1zN j0lt Neq le0M
            lt jM q0n s0lt j0reds j0'eq shamt_def j1redle j0j1red j1redspan])
    have notbrleNp: "\<not> (TrMax ?Np = Lng ?Np - 1
                       \<or> le0 ?Np (TrMax ?Np + 1) (Lng ?Np - 1))"
      by (rule oper_d1pos_ctx_notbrleNp[OF NT LNgt notzeroN hasparN i1zN j0lt Neq n1
            q0n j0redlt s0lt j0reds j0'eq shamt_def j1red_def j0j1red lt jM tnc stop
            notbrle])
    have multiNp: "1 < length (P (seg N ?AN j1red))"
      by (rule oper_d1pos_ctx_period_multiNp[OF NpT j0j1red notbrleNp])
    \<comment> \<open>(anchor facts) INTERIOR (cap inactive) vs BOUNDARY (cap active) split\<close>
    have anchorBundle:
      "seg (seg M ?A j1') 0 (Lng (seg N ?AN j1red) - 1 - 1)
        = (IncrFirst ^^ shamt) (seg (seg N ?AN j1red) 0 (Lng (seg N ?AN j1red) - 1 - 1))
        \<and> entry (seg M ?A j1') 0 (Lng (seg N ?AN j1red) - 1)
        = entry (seg N ?AN j1red) 0 (Lng (seg N ?AN j1red) - 1) + shamt
        \<and> entry (seg M ?A j1') 1 (Lng (seg N ?AN j1red) - 1)
        \<le> entry (seg N ?AN j1red) 1 (Lng (seg N ?AN j1red) - 1)
        \<and> Lng (seg N ?AN j1red) - 1 \<le> Lng (seg M ?A j1') - 1"
    proof -
      show ?thesis
      proof (cases "j1red < ?j1N")
        case interior: True
        have full: "seg M ?A j1' = (IncrFirst ^^ shamt) (seg N ?AN j1red)"
          by (rule oper_d1pos_notbrle_period_fullShift[OF NT LNgt notzeroN hasparN i1zN
                Neq n1 lt jM j0lt periodic q0_def s0_def j0red_def j1red_def shamt_def
                tnc stop notbrle interior])
        have Lgeq: "Lng (seg M ?A j1') = Lng (seg N ?AN j1red)"
          using full by simp
        have Snne: "seg N ?AN j1red \<noteq> []"
        proof
          assume "seg N ?AN j1red = []"
          hence "P (seg N ?AN j1red) = [[]]"
            by (subst P.simps) (simp add: multiT_def zeroT_def monoT_def)
          thus False using multiNp by simp
        qed
        have mlt: "Lng (seg N ?AN j1red) - 1 < Lng (seg N ?AN j1red)"
          using Snne by (cases "seg N ?AN j1red") auto
        have m2lt: "Lng (seg N ?AN j1red) - 1 - 1 < Lng (seg N ?AN j1red)"
          using mlt by simp
        show ?thesis
        proof (intro conjI)
          show "seg (seg M ?A j1') 0 (Lng (seg N ?AN j1red) - 1 - 1)
              = (IncrFirst ^^ shamt) (seg (seg N ?AN j1red) 0 (Lng (seg N ?AN j1red) - 1 - 1))"
            using full seg_funpow_IncrFirst0[OF m2lt] by simp
          show "entry (seg M ?A j1') 0 (Lng (seg N ?AN j1red) - 1)
              = entry (seg N ?AN j1red) 0 (Lng (seg N ?AN j1red) - 1) + shamt"
            using full entry_funpow_IncrFirst0[OF mlt] by simp
          show "entry (seg M ?A j1') 1 (Lng (seg N ?AN j1red) - 1)
              \<le> entry (seg N ?AN j1red) 1 (Lng (seg N ?AN j1red) - 1)"
            using full entry_funpow_IncrFirst1[OF mlt] by simp
          show "Lng (seg N ?AN j1red) - 1 \<le> Lng (seg M ?A j1') - 1" using Lgeq by simp
        qed
      next
        case False
        have boundary: "\<not> j1red < ?j1N" using False by simp
        show ?thesis
          by (rule oper_d1pos_notbrle_period_boundary_geom[OF NT LNgt notzeroN hasparN
                i1zN Neq n1 lt jM bge j0lt periodic q0_def s0_def j0red_def j1red_def
                shamt_def tnc stop multiNp notbrle boundary])
      qed
    qed
    have shiftEqB: "seg (seg M ?A j1') 0 (Lng (seg N ?AN j1red) - 1 - 1)
        = (IncrFirst ^^ shamt) (seg (seg N ?AN j1red) 0 (Lng (seg N ?AN j1red) - 1 - 1))"
      using anchorBundle by blast
    have boundEq0B: "entry (seg M ?A j1') 0 (Lng (seg N ?AN j1red) - 1)
        = entry (seg N ?AN j1red) 0 (Lng (seg N ?AN j1red) - 1) + shamt"
      using anchorBundle by blast
    have boundEq1B: "entry (seg M ?A j1') 1 (Lng (seg N ?AN j1red) - 1)
        \<le> entry (seg N ?AN j1red) 1 (Lng (seg N ?AN j1red) - 1)"
      using anchorBundle by blast
    have mleSB: "Lng (seg N ?AN j1red) - 1 \<le> Lng (seg M ?A j1') - 1"
      using anchorBundle by blast
    \<comment> \<open>lenPSeqB via the period-unified component-count match; cleMB interior-free /
       boundary via the uniform-witness undercut\<close>
    have multiS0: "1 < length (P (seg M ?A j1'))" using multiM .
    have ST: "seg M ?A j1' \<in> T_PS"
    proof -
      have "seg M ?A j1' \<noteq> []"
      proof
        assume "seg M ?A j1' = []"
        hence "P (seg M ?A j1') = [[]]"
          by (subst P.simps) (simp add: multiT_def zeroT_def monoT_def)
        thus False using multiS0 by simp
      qed
      thus ?thesis by (simp add: T_PS_def seg_def)
    qed
    have SnT: "seg N ?AN j1red \<in> T_PS"
    proof -
      have "seg N ?AN j1red \<noteq> []"
      proof
        assume "seg N ?AN j1red = []"
        hence "P (seg N ?AN j1red) = [[]]"
          by (subst P.simps) (simp add: multiT_def zeroT_def monoT_def)
        thus False using multiNp by simp
      qed
      thus ?thesis by (simp add: T_PS_def seg_def)
    qed
    have multiS: "1 < length (P (seg M ?A j1'))" using multiM .
    have cleMB: "IdxSum (P (seg M ?A j1')) ! (length (P (seg M ?A j1')) - 1)
          \<le> Lng (seg N ?AN j1red) - 1"
    proof (cases "j1red < ?j1N")
      case interior: True
      have full: "seg M ?A j1' = (IncrFirst ^^ shamt) (seg N ?AN j1red)"
        by (rule oper_d1pos_notbrle_period_fullShift[OF NT LNgt notzeroN hasparN i1zN
              Neq n1 lt jM j0lt periodic q0_def s0_def j0red_def j1red_def shamt_def
              tnc stop notbrle interior])
      have Lgeq: "Lng (seg M ?A j1') = Lng (seg N ?AN j1red)" using full by simp
      have cle: "IdxSum (P (seg M ?A j1')) ! (length (P (seg M ?A j1')) - 1)
               \<le> Lng (seg M ?A j1') - 1"
        by (rule oper_d1pos_branch_anchor(2)[OF ST multiS])
      thus ?thesis using Lgeq by simp
    next
      case False
      have boundary: "\<not> j1red < ?j1N" using False by simp
      show ?thesis
        by (rule oper_d1pos_period_boundary_cleMB[OF NT monoN std LNgt notzeroN hasparN
              i1zN Neq n1 lt jM bge j0lt periodic q0_def s0_def j0red_def j1red_def
              shamt_def tnc stop multiNp multiS notbrle boundary])
    qed
    have lenPSeqB: "length (P (seg M ?A j1')) = length (P (seg N ?AN j1red))"
      by (rule oper_d1pos_lenPSeq_unified[OF ST multiS SnT multiNp mleSB cleMB shiftEqB
            boundEq0B])
    \<comment> \<open>dispatch CELL 4\<close>
    show ?thesis
      by (rule oper_d1pos_notbrle_LOW_take_eq_periodic[OF NT monoN LNgt notzeroN hasparN
            i1zN Neq n1 M'T le0M lt jM bge notbrle j0lt dpos periodic q0_def s0_def
            j0red_def j1red_def shamt_def multiM multiNp le0Np tnc stop shiftEqB boundEq0B
            boundEq1B lenPSeqB cleMB mleSB])
  next
    case low: False
    \<comment> \<open>LOW branch: \<open>j0' < Lng N-1\<close>, witnesses \<open>j0red = j0'\<close>, \<open>j1red = Lng N-1\<close>,
       \<open>shamt = 0\<close>.  Sub-split on \<open>A vs jm2\<close> (regA) and \<open>j0' vs jm2\<close> (regB/boundary).\<close>
    have j0plt: "j0' < ?j1N" using low by simp
    let ?S = "seg M ?A j1'"
    let ?Snside = "seg N ?A ?j1N"
    let ?Np = "seg N j0' ?j1N"
    \<comment> \<open>le0Np\<close>
    have le0Np: "le0 N j0' ?j1N"
      by (rule oper_d1pos_ctx_le0Np[OF LNgt notzeroN hasparN i1zN j0lt Neq le0M j0plt jM bge])
    \<comment> \<open>tnc + stop : verbatim-prefix (\<open>j0' < jm2\<close>) vs same-block (\<open>jm2 \<le> j0' < LN-1\<close>)\<close>
    have tnc: "TrMax ?Np \<le> ?j1N - 1 - j0'"
    proof (cases "j0' < ?jm2")
      case True
      show ?thesis
        by (rule oper_d1pos_ctx_tnc_prefix[OF NT LNgt notzeroN hasparN i1zN j0lt n1 True
              bge lt j1lt notbrle'])
    next
      case False
      have jm2le: "?jm2 \<le> j0'" using False by simp
      have qn0: "(0::nat) < n" using n1 by simp
      have s0lt: "j0' - ?jm2 < ?j1N - ?jm2" using j0plt jm2le by linarith
      have s0eq: "j0' = ?jm2 + (j0' - ?jm2)" using jm2le by simp
      have j0'eqc: "j0' = ?jm2 + 0 * (?j1N - ?jm2) + (j0' - ?jm2)" using s0eq by simp
      have shz: "(0::nat) = 0 * ?delta" by simp
      have capj0j1: "j0' < ?j1N" using j0plt .
      show ?thesis
      proof (cases "?j1N < j0' + (j1' - j0')")
        case capactive: True
        have spanstrict: "?j1N < j0' + (j1' - j0')" using capactive .
        have "TrMax (seg N j0' ?j1N) \<le> ?j1N - 1 - j0'"
          by (rule oper_d1pos_ctx_tnc_capped[OF NT monoN std LNgt notzeroN hasparN i1zN
                j0lt n1 qn0 capj0j1 s0eq s0lt j0'eqc shz le_refl capj0j1 refl spanstrict
                lt j1lt notbrle'])
        thus ?thesis by simp
      next
        case False
        have span: "?j1N = j0' + (j1' - j0')" using bge lt low False by linarith
        have "TrMax (seg N j0' ?j1N) < ?j1N - 1 - j0'"
          by (rule oper_d1pos_ctx_period_tncstrict_uncapped[OF NT LNgt notzeroN hasparN
                i1zN j0lt n1 qn0 capj0j1 s0eq s0lt j0'eqc shz le_refl capj0j1 span
                lt j1lt notbrle'])
        thus ?thesis by linarith
      qed
    qed
    have stop: "\<not> nextR (seg ((N::pairseq)[n]) j0' j1') 1
                  (TrMax ?Np) (TrMax ?Np + 1)"
    proof (cases "j0' < ?jm2")
      case True
      have j0'le: "j0' \<le> ?jm2" using True by simp
      show ?thesis
        by (rule nextR1_boundary_stop_d1pos[OF NT LNgt notzeroN hasparN i1zN j0lt n1
              j0'le bge j1lt])
    next
      case False
      have jm2le: "?jm2 \<le> j0'" using False by simp
      have qn0: "(0::nat) < n" using n1 by simp
      have s0lt: "j0' - ?jm2 < ?j1N - ?jm2" using j0plt jm2le by linarith
      have s0eq: "j0' = ?jm2 + (j0' - ?jm2)" using jm2le by simp
      have j0'eqc: "j0' = ?jm2 + 0 * (?j1N - ?jm2) + (j0' - ?jm2)" using s0eq by simp
      have shz: "(0::nat) = 0 * ?delta" by simp
      have capj0j1: "j0' < ?j1N" using j0plt .
      show ?thesis
      proof (cases "?j1N < j0' + (j1' - j0')")
        case capactive: True
        have spanstrict: "?j1N < j0' + (j1' - j0')" using capactive .
        have "\<not> nextR (seg ((N::pairseq)[n]) j0' j1') 1
                (TrMax (seg N j0' ?j1N)) (TrMax (seg N j0' ?j1N) + 1)"
          by (rule oper_d1pos_ctx_stop_direct[OF NT monoN std LNgt notzeroN hasparN i1zN
                j0lt n1 qn0 capj0j1 s0eq s0lt j0'eqc shz le_refl capj0j1 refl spanstrict
                lt j1lt le0M' notbrle'])
        thus ?thesis by simp
      next
        case False
        have span: "?j1N = j0' + (j1' - j0')" using bge lt low False by linarith
        have tncstrict: "TrMax (seg N j0' ?j1N) < ?j1N - 1 - j0'"
          by (rule oper_d1pos_ctx_period_tncstrict_uncapped[OF NT LNgt notzeroN hasparN
                i1zN j0lt n1 qn0 capj0j1 s0eq s0lt j0'eqc shz le_refl capj0j1 span
                lt j1lt notbrle'])
        have "\<not> nextR (seg ((N::pairseq)[n]) j0' j1') 1
                (TrMax (seg N j0' ?j1N)) (TrMax (seg N j0' ?j1N) + 1)"
          by (rule oper_d1pos_ctx_stop_direct_strict[OF NT monoN std LNgt notzeroN hasparN
                i1zN j0lt n1 qn0 capj0j1 s0eq s0lt j0'eqc shz le_refl capj0j1 span
                lt j1lt tncstrict])
        thus ?thesis by simp
      qed
    qed
    \<comment> \<open>notbrleNp (verbatim form) + multiNp\<close>
    have notbrleNp: "\<not> (TrMax ?Np = Lng ?Np - 1
                       \<or> le0 ?Np (TrMax ?Np + 1) (Lng ?Np - 1))"
      by (rule oper_d1pos_ctx_notbrleNp_verbatim[OF NT LNgt notzeroN hasparN i1zN j0lt
            Neq n1 j0plt lt bge jM tnc stop notbrle])
    have NpT: "?Np \<in> T_PS" using j0plt by (simp add: T_PS_def seg_def)
    have j0j1redL: "j0' < ?j1N" using j0plt .
    have multiNp: "1 < length (P (seg N (j0' + TrMax ?Np + 1) ?j1N))"
      by (rule oper_d1pos_ctx_period_multiNp[OF NpT j0j1redL notbrleNp])
    \<comment> \<open>\<open>A < Lng N-1\<close>: \<open>A = Lng N-1\<close> would make \<open>TrMax Snside = Lng Snside - 1\<close>,
       contradicting \<open>notbrleNp\<close>.  We derive TrEq (\<open>TrMax M' = TrMax Snside\<close>) via the
       regime-A Br alignment, then \<open>A \<le> Lng N-1\<close> from \<open>tnc\<close>, and exclude \<open>A = Lng N-1\<close>.\<close>
    have j1redspanL: "?j1N \<le> j0' + (j1' - j0')" using bge lt by linarith
    have alignL: "TrMax (seg ((N::pairseq)[n]) j0' j1') = TrMax (seg N j0' ?j1N)
       \<and> Br (seg ((N::pairseq)[n]) j0' j1')
           = P (seg ((N::pairseq)[n]) (j0' + TrMax (seg ((N::pairseq)[n]) j0' j1') + 1) j1')
       \<and> Br (seg N j0' ?j1N)
           = P (seg N (j0' + TrMax (seg N j0' ?j1N) + 1) ?j1N)
       \<and> Br (seg ((N::pairseq)[n]) j0' j1') \<noteq> [] \<and> Br (seg N j0' ?j1N) \<noteq> []"
      by (rule oper_d1pos_notbrle_Br_align_regA[OF LNgt notzeroN hasparN i1zN j0lt n1
            le_refl j0j1redL j1redspanL refl lt j1lt tnc stop notbrle'])
    have TrEqL: "?T = TrMax ?Np"
    proof -
      have "?T = TrMax (seg ((N::pairseq)[n]) j0' j1')" using Neq by simp
      thus ?thesis using alignL by simp
    qed
    have Aeq': "?A = j0' + TrMax ?Np + 1" using TrEqL by simp
    have multiNpB: "1 < length (P (seg N ?A ?j1N))"
      using multiNp Aeq' by simp
    have AltN: "?A < ?j1N"
    proof (rule ccontr)
      assume "\<not> ?A < ?j1N"
      hence Age: "?j1N \<le> ?A" by simp
      have tncA: "TrMax ?Np \<le> ?j1N - 1 - j0'" using tnc .
      have "?A \<le> ?j1N" using TrEqL tncA j0plt by linarith
      hence Aeq: "?A = ?j1N" using Age by linarith
      \<comment> \<open>\<open>A = LN-1\<close> \<Rightarrow> branch region \<open>seg N A (LN-1)\<close> singleton, contradicting multiNp\<close>
      have "seg N ?A ?j1N = [N ! ?j1N]" using Aeq by (simp add: seg_def)
      hence "P (seg N ?A ?j1N) = [[N ! ?j1N]]"
        by (subst P.simps) (simp add: multiT_def zeroT_def monoT_def)
      thus False using multiNpB by simp
    qed
    \<comment> \<open>dispatch: regA (\<open>A < jm2\<close>) vs regB (\<open>jm2 \<le> A\<close>, \<open>j0' \<ge> jm2\<close>) vs boundary (\<open>j0' < jm2\<close>)\<close>
    show ?thesis
    proof (cases "?A < ?jm2")
      case Areg: True
      have multiNpA: "1 < length (P (seg N (j0' + ?T + 1) ?j1N))"
        using multiNpB by simp
      show ?thesis
        by (rule oper_d1pos_notbrle_LOW_take_eq_regA[OF NT monoN LNgt notzeroN hasparN
              i1zN Neq n1 M'T le0M lt jM bge notbrle j0lt dpos Areg multiM multiNpA le0Np
              tnc stop])
    next
      case False
      have Ajm2: "?jm2 \<le> ?A" using False by simp
      have Areg2: "?jm2 \<le> ?A \<and> ?A < ?j1N" using Ajm2 AltN by simp
      \<comment> \<open>the shamt=0 anchor facts for regB/boundary\<close>
      note anchorB = oper_d1pos_low_anchor_shamt0[OF NT monoN std LNgt notzeroN hasparN i1zN
              Neq n1 j0plt lt jM bge Ajm2 AltN dpos multiM le0M notbrle tnc stop]
      have shiftEqB: "seg (seg M ?A j1') 0 (Lng (seg N ?A ?j1N) - 1 - 1)
          = (IncrFirst ^^ (0::nat)) (seg (seg N ?A ?j1N) 0 (Lng (seg N ?A ?j1N) - 1 - 1))"
        using anchorB[THEN conjunct1] .
      have boundEq0B: "entry (seg M ?A j1') 0 (Lng (seg N ?A ?j1N) - 1)
          = entry (seg N ?A ?j1N) 0 (Lng (seg N ?A ?j1N) - 1) + (0::nat)"
        using anchorB[THEN conjunct2, THEN conjunct1] .
      have boundEq1B: "entry (seg M ?A j1') 1 (Lng (seg N ?A ?j1N) - 1)
          \<le> entry (seg N ?A ?j1N) 1 (Lng (seg N ?A ?j1N) - 1)"
        using anchorB[THEN conjunct2, THEN conjunct2, THEN conjunct1] .
      have lenPSeqB: "length (P (seg M ?A j1')) = length (P (seg N ?A ?j1N))"
        using anchorB[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1] .
      have cleMB: "IdxSum (P (seg M ?A j1')) ! (length (P (seg M ?A j1')) - 1)
            \<le> Lng (seg N ?A ?j1N) - 1"
        using anchorB[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2,
                      THEN conjunct1] .
      have mleSB: "Lng (seg N ?A ?j1N) - 1 \<le> Lng (seg M ?A j1') - 1"
        using anchorB[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2,
                      THEN conjunct2] .
      show ?thesis
      proof (cases "?jm2 \<le> j0'")
        case j0pge: True
        show ?thesis
          by (rule oper_d1pos_notbrle_LOW_take_eq_regB[OF NT monoN LNgt notzeroN hasparN
                i1zN Neq n1 M'T le0M lt jM bge notbrle j0lt dpos Areg2 j0pge multiM
                multiNpB le0Np tnc stop shiftEqB boundEq0B boundEq1B lenPSeqB cleMB mleSB])
      next
        case False
        have j0ltjm2: "j0' < ?jm2" using False by simp
        show ?thesis
          by (rule oper_d1pos_notbrle_LOW_take_eq_boundary[OF NT monoN LNgt notzeroN
                hasparN i1zN Neq n1 M'T le0M lt jM bge notbrle j0lt dpos Areg2 j0ltjm2
                multiM multiNpB le0Np tnc stop shiftEqB boundEq0B boundEq1B lenPSeqB
                cleMB mleSB])
      qed
    qed
  qed
qed

end
