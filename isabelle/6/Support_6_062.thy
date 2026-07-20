theory Support_6_062
  imports Frontier_6_082
begin

text \<open>§6.7 F2 brick: \<open>gstrict_full(N)\<close> from the GLOBAL endpoint slope-1 fact at
  base 0 (\<open>D(N)\<close>: \<open>entry N 0 (Lng N-1) = entry N 0 0 + (Lng N-1)\<close>).  This is the
  \<open>p = 0\<close> instance of @{thm [source] subramp_from_Ep}: the per-step \<open>\<le> +1\<close> cap
  (@{thm [source] ST_row0_step_le}) together with the full-width endpoint forces
  EVERY step on \<open>[0, j\<^sub>1)\<close> to be exactly \<open>+1\<close>.  Cites only the already-GREEN
  @{thm [source] subramp_from_Ep}; no spsy / sblk / RedCond / tail_affine.\<close>

lemma f2_gstrict_from_D:
  fixes N :: pairseq
  assumes N: "N \<in> ST_PS"
    and L: "1 < Lng N"
    and D: "entry N 0 (Lng N - 1) = entry N 0 0 + (Lng N - 1)"
    and y: "y < Lng N - 1"
  shows "entry N 0 (Suc y) = Suc (entry N 0 y)"
proof -
  have p0: "(0::nat) < Lng N - 1" using L by linarith
  have Ep: "entry N 0 (Lng N - 1) = entry N 0 0 + ((Lng N - 1) - 0)" using D by simp
  show ?thesis by (rule subramp_from_Ep[OF N p0 Ep _ y]) simp
qed


text \<open>§6.7 F2 brick: \<open>D(diagSeq a b)\<close> --- the diagonal segment has its row-0
  endpoint exactly \<open>(Lng - 1)\<close> above its base.  Direct from
  @{thm [source] entry_diagSeq}.\<close>

lemma f2_D_diag:
  fixes a b :: nat
  assumes ab: "a \<le> b"
  shows "entry (diagSeq a b) 0 (Lng (diagSeq a b) - 1)
       = entry (diagSeq a b) 0 0 + (Lng (diagSeq a b) - 1)"
proof -
  let ?N = "diagSeq a b"
  have Lpos: "0 < Suc b - a" using ab by simp
  have e0: "entry ?N 0 0 = a" using entry_diagSeq[of 0 b a 0] Lpos by simp
  have hi: "Lng ?N - 1 < Suc b - a" using Lpos by simp
  have ee: "entry ?N 0 (Lng ?N - 1) = a + (Lng ?N - 1)"
    using entry_diagSeq[of "Lng ?N - 1" b a 0] hi by simp
  show ?thesis using e0 ee by simp
qed


text \<open>§6.7 CD reduction brick 2 (GREEN, the spsy TREE clause from \<open>D(N)\<close>).  Given
  the scalar crux \<open>D(N)\<close> for a gated \<open>N \<in> ST\<^sub>PS\<close> and a gated interior node \<open>z\<close>,
  the spsy TREE conclusion follows: \<open>D(N)\<close> upgrades to the global per-step ramp
  \<open>gstrict_full(N)\<close> via @{thm [source] f2_gstrict_from_D}, which
  @{thm [source] gs_tree_from_gstrict} converts to the TREE clause (the row-1
  parent of \<open>parent N 1 z\<close> exists and lands \<open>\<ge> j\<^sub>0\<close>).  This is exactly the \<open>tree\<close>
  premise of @{thm [source] spsy_keystone_via_tree_bridge}; closing \<open>D(N)\<close>
  (the lone residual crux \<open>m_6_7_oper_gstrict\<close>) therefore makes the whole spsy
  cascade unconditional.  Cites only the already-GREEN
  @{thm [source] f2_gstrict_from_D}, @{thm [source] gs_tree_from_gstrict}; no
  spsy / sblk / via_spsy / RedCond / oper / tail_affine.\<close>

lemma cd_tree_from_D:
  fixes N :: pairseq
  assumes N: "N \<in> ST_PS"
    and L: "1 < Lng N"
    and hp1: "hasParent N 1 (Lng N - 1)"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and zlo: "parent N 1 (Lng N - 1) < z"
    and zhi: "z < Lng N - 1"
    and hpz: "hasParent N 1 z"
    and pge: "parent N 1 z \<ge> parent N 1 (Lng N - 1)"
    and pgt: "parent N 1 z > parent N 1 (Lng N - 1)"
    and D: "entry N 0 (Lng N - 1) = entry N 0 0 + (Lng N - 1)"
  shows "hasParent N 1 (parent N 1 z)
         \<and> parent N 1 (parent N 1 z) \<ge> parent N 1 (Lng N - 1)"
proof -
  have gstrict: "\<And>y. y < Lng N - 1 \<Longrightarrow> entry N 0 (Suc y) = Suc (entry N 0 y)"
    by (rule f2_gstrict_from_D[OF N L D])
  show ?thesis
    by (rule gs_tree_from_gstrict[OF L hp1 j0lt zlo zhi hpz pge pgt gstrict])
qed


text \<open>§6.7 FORWARD-CRUX brick (diag case).  \<open>fc_D_diag\<close>: the scalar crux \<open>D(N)\<close>
  always holds for a diagonal segment \<open>N = diagSeq a b\<close> --- its row-0 endpoint is
  exactly the width above its base.  This discharges the diag branch of the
  ST_PS.cases contrapositive (\<open>~D(N)\<close> is vacuously false on diagonals).  Direct
  from @{thm [source] f2_D_diag}; no spsy / sblk / RedCond / oper / tail_affine.\<close>

lemma fc_D_diag:
  fixes a b :: nat
  assumes ab: "a \<le> b"
  shows "entry (diagSeq a b) 0 (Lng (diagSeq a b) - 1)
       = entry (diagSeq a b) 0 0 + (Lng (diagSeq a b) - 1)"
  by (rule f2_D_diag[OF ab])


text \<open>§6.7 FORWARD-CRUX brick (D propagates through the oper).  \<open>fc_D_oper\<close>: for a
  GATED \<open>M\<close> (\<open>1 < Lng M\<close>; endpoint not \<open>(0,0)\<close>; row-1 parent of the endpoint exists;
  \<open>i\<^sub>1 = 1\<close>; \<open>j\<^sub>0 = parent M 1 (Lng M-1) < Lng M-1\<close>) with \<open>M \<in> ST\<^sub>PS\<close>, if the scalar
  crux \<open>D(M)\<close> holds then \<open>D(M[n])\<close> holds for every \<open>n \<ge> 1\<close>.  This is the FORWARD
  D-propagation through the periodic-row1 tiling.  Under \<open>D(M)\<close> the row-0 of \<open>M\<close> is
  the exact \<open>+1\<close> ramp (@{thm [source] f2_gstrict_from_D}), so \<open>entry M 0 j\<^sub>0
  = entry M 0 0 + j\<^sub>0\<close> and the block shift \<open>d\<^sub>0 = entry M 0 j\<^sub>1 - entry M 0 j\<^sub>0\<close>
  equals the width \<open>w = j\<^sub>1 - j\<^sub>0\<close>.  The last column of \<open>M[n]\<close> (block \<open>n-1\<close>, offset
  \<open>w-1\<close>) reads (@{thm [source] oper_d1pos_entry0})
  \<open>entry M 0 (j\<^sub>1-1) + (n-1)\<cdot>w\<close>, the base column reads \<open>entry M 0 0\<close>
  (@{thm [source] operB_gen_entry_prefix} when \<open>0 < j\<^sub>0\<close>, the block-0 read otherwise),
  and the length is \<open>j\<^sub>0 + n\<cdot>w\<close> (@{thm [source] oper_d1pos_LngM}); the arithmetic then
  closes \<open>D(M[n])\<close>.  Cites only the already-GREEN @{thm [source] f2_gstrict_from_D},
  @{thm [source] oper_d1pos_entry0}, @{thm [source] oper_d1pos_LngM},
  @{thm [source] operB_gen_entry_prefix}; no spsy / sblk / RedCond / tail_affine.\<close>

lemma fc_D_oper:
  fixes M :: pairseq
  assumes MST: "M \<in> ST_PS"
    and L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and n1: "1 \<le> n"
    and DM: "entry M 0 (Lng M - 1) = entry M 0 0 + (Lng M - 1)"
  shows "entry ((M::pairseq)[n]) 0 (Lng ((M::pairseq)[n]) - 1)
       = entry ((M::pairseq)[n]) 0 0 + (Lng ((M::pairseq)[n]) - 1)"
proof -
  let ?j1 = "Lng M - 1"  let ?j0 = "parent M 1 ?j1"
  let ?Mn = "(M::pairseq)[n]"
  let ?d0 = "entry M 0 ?j1 - entry M 0 ?j0"
  \<comment> \<open>hold \<open>w\<close> abstract so no decision procedure sees the double-\<open>parent\<close> nat-sub\<close>
  obtain w where wdef: "?j1 - ?j0 = w" by blast
  have w0: "0 < w" using j0lt wdef by linarith
  have n0: "0 < n" using n1 by simp
  obtain m where mdef: "n = Suc m" using n0 by (cases n) auto
  have j0le: "?j0 \<le> ?j1" using j0lt by linarith
  have j1j0: "?j1 = ?j0 + w" using wdef j0le by linarith
  \<comment> \<open>row-0 of \<open>M\<close> is the exact \<open>+1\<close> ramp under \<open>D(M)\<close>\<close>
  have gstrict: "\<And>y. y < ?j1 \<Longrightarrow> entry M 0 (Suc y) = Suc (entry M 0 y)"
    by (rule f2_gstrict_from_D[OF MST L DM])
  have ramp: "\<And>y. y \<le> ?j1 \<Longrightarrow> entry M 0 y = entry M 0 0 + y"
  proof -
    fix y assume "y \<le> ?j1"
    thus "entry M 0 y = entry M 0 0 + y"
    proof (induction y)
      case 0 show ?case by simp
    next
      case (Suc y)
      have yj1: "y < ?j1" using Suc.prems by linarith
      have ih: "entry M 0 y = entry M 0 0 + y" using Suc.IH yj1 by linarith
      have "entry M 0 (Suc y) = Suc (entry M 0 y)" by (rule gstrict[OF yj1])
      thus ?case using ih by simp
    qed
  qed
  \<comment> \<open>the block shift equals the width\<close>
  have e_j0: "entry M 0 ?j0 = entry M 0 0 + ?j0" by (rule ramp[OF j0le])
  have e_j1: "entry M 0 ?j1 = entry M 0 0 + ?j1" using DM by simp
  have d0w: "?d0 = w" using e_j0 e_j1 j0le wdef by simp
  \<comment> \<open>length of \<open>M[n]\<close>, in abstract-\<open>w\<close> form\<close>
  have lenMn: "Lng ?Mn = ?j0 + n * w"
    using oper_d1pos_LngM[OF L notzero hp i1z j0lt] wdef by simp
  have lenMn1: "Lng ?Mn - 1 = ?j0 + m * w + (w - 1)"
  proof -
    have "Lng ?Mn = ?j0 + (Suc m) * w" using lenMn mdef by simp
    also have "\<dots> = ?j0 + m * w + w" by (simp add: algebra_simps)
    finally have "Lng ?Mn = ?j0 + m * w + w" .
    thus ?thesis using w0 by simp
  qed
  \<comment> \<open>read the last column as block \<open>m = n-1\<close>, offset \<open>w-1\<close>\<close>
  have qn: "m < n" using mdef by simp
  have sw: "w - 1 < ?j1 - ?j0" using w0 wdef by simp
  have e_last0: "entry ?Mn 0 (?j0 + m * (?j1 - ?j0) + (w - 1))
              = entry M 0 (?j0 + (w - 1)) + m * ?d0"
    by (rule oper_d1pos_entry0[OF L notzero hp i1z j0lt qn sw])
  have e_last: "entry ?Mn 0 (?j0 + m * w + (w - 1))
              = entry M 0 (?j0 + (w - 1)) + m * w"
    using e_last0 wdef d0w by simp
  have j0w1: "?j0 + (w - 1) = ?j1 - 1" using w0 j1j0 by linarith
  have e_j1m1: "entry M 0 (?j1 - 1) = entry M 0 0 + (?j1 - 1)"
    using ramp[of "?j1 - 1"] by simp
  have e_last': "entry ?Mn 0 (Lng ?Mn - 1) = entry M 0 0 + (?j1 - 1) + m * w"
    using e_last lenMn1 j0w1 e_j1m1 by simp
  \<comment> \<open>the base column reads \<open>entry M 0 0\<close>\<close>
  have e_base: "entry ?Mn 0 0 = entry M 0 0"
  proof (cases "0 < ?j0")
    case True
    have x0: "0 < parent M (idx1 M (Lng M - 1)) (Lng M - 1)" using True i1z by simp
    show ?thesis by (rule operB_gen_entry_prefix[OF L notzero hp x0])
  next
    case False
    hence j00: "?j0 = 0" by simp
    have "entry ?Mn 0 (?j0 + 0 * (?j1 - ?j0) + 0) = entry M 0 (?j0 + 0) + 0 * ?d0"
      by (rule oper_d1pos_entry0[OF L notzero hp i1z j0lt n0]) (use w0 wdef in simp)
    thus ?thesis using j00 by simp
  qed
  \<comment> \<open>assemble \<open>D(M[n])\<close>\<close>
  have width: "Lng ?Mn - 1 = ?j0 + m * w + (w - 1)" using lenMn1 .
  have rhs: "entry ?Mn 0 0 + (Lng ?Mn - 1) = entry M 0 0 + (?j0 + m * w + (w - 1))"
    using e_base width by simp
  have arith: "entry M 0 0 + (?j1 - 1) + m * w
             = entry M 0 0 + (?j0 + m * w + (w - 1))"
  proof -
    have "(?j1 - 1) + m * w = (?j0 + w - 1) + m * w" using j1j0 by simp
    also have "\<dots> = ?j0 + m * w + (w - 1)" using w0 by simp
    finally show ?thesis by simp
  qed
  show ?thesis using e_last' rhs arith by simp
qed


section \<open>§6.5–§6.7 article-faithful standard-reducedness skeleton (bf_)\<close>

text \<open>
  This block rebuilds the article's actual §6.5/§6.6/§6.7 chain for
  \<open>ST\<^sub>PS \<subseteq> RT\<^sub>PS\<close> (標準形の簡約性), as opposed to the existing
  @{thm [source] m_6_7_standard_reduced} which goes directly through the §6.6
  keystone @{thm [source] m_6_6_reduced_iff_cond}.  The faithful chain is:

    (i)  命題（\<open>Red\<close>と基本列の可換性）  @{text m_6_5_Red_oper}:
           \<open>(Red M)[n] = Red (M[n])\<close>, by induction on \<open>j\<^sub>1 = Lng M - 1\<close>:
           \<^item> \<open>j\<^sub>1 = 0\<close>: @{thm [source] roper_base_Lng1} (already GREEN);
           \<^item> NON-SHIFT (\<open>oper\<close> degenerates to \<open>Pred\<close>): @{text bf_roper_nonshift}
             — LIGHT, fully proved here from @{thm [source] m_6_5_Red_Pred};
           \<^item> SHIFT (\<open>oper\<close> = \<open>G \<oplus> \<Oplus> B\<close>): the single HARD residual, isolated as the
             named hypothesis @{text bf_roper_shift_resid}.
    (ii) 簡約性が基本列で保たれること  @{text m_6_6_red_preserved_by_oper}:
           \<open>M \<in> RT\<^sub>PS \<Longrightarrow> M[n] \<in> RT\<^sub>PS\<close>, from @{thm [source] m_6_5_Red_idem} (冪等性)
           + (i).
    (iii) 標準形の簡約性  @{text m_6_7_standard_reduced_faithful}:
           \<open>ST\<^sub>PS \<subseteq> RT\<^sub>PS\<close>, by @{thm [source] ST_PS.induct} (diag base + oper step
           via (ii)).
    (iv) @{text bf_stdCA_faithful}: \<open>\<forall>S \<in> ST\<^sub>PS. RedCondA S\<close>, from (iii) +
           @{thm [source] m_6_6_reduced_iff_cond}.
\<close>

subsection \<open>(i) \<open>Red\<close> と基本列の可換性 — non-shift (LIGHT) and assembly\<close>

text \<open>
  The LIGHT non-shift case.  When the \<open>operator[]\<close> step degenerates to
  \<open>Pred\<close> on \<^emph>\<open>both\<close> \<open>M\<close> and \<open>Red M\<close> (the article's \<open>\<not> ((1,0) <\<^bsub>M\<^esub>\<^sup>Next (1,j\<^sub>1))\<close>
  branch, where \<open>operator[]\<close> reduces to \<open>Pred\<close> by recursion), the commutativity
  of \<open>Red\<close> with the fundamental sequence collapses to the commutativity of
  \<open>Red\<close> with \<open>Pred\<close>, i.e. @{thm [source] m_6_5_Red_Pred}:
    \<open>(Red M)[n] = Pred (Red M) = Red (Pred M) = Red (M[n])\<close>.
\<close>

lemma bf_roper_nonshift:
  assumes MT: "M \<in> T_PS"
    and opM: "(M::pairseq)[n] = Pred M"
    and opR: "(Red M)[n] = Pred (Red M)"
  shows "(Red M)[n] = Red (M[n])"
proof -
  have "(Red M)[n] = Pred (Red M)" by (rule opR)
  also have "\<dots> = Red (Pred M)" by (rule m_6_5_Red_Pred[OF MT, symmetric])
  also have "\<dots> = Red (M[n])" using opM by simp
  finally show ?thesis .
qed

text \<open>
  命題（\<open>Red\<close>と基本列の可換性）, assembled.  Article proof: induction on
  \<open>j\<^sub>1 = Lng M - 1\<close> with a case split on \<open>(1,0) <\<^bsub>M\<^esub>\<^sup>Next (1,j\<^sub>1)\<close>.  In
  mechanized terms the article's split is exactly the \<open>operator[]\<close> case split:
  the step either degenerates (\<open>M[n] = Pred M\<close>) or performs the \<open>G \<oplus> \<Oplus> B\<close>
  tiling (\<open>M[n] \<noteq> Pred M\<close>).

  \<^item> Degenerate / NON-SHIFT (\<open>M[n] = Pred M\<close>; includes \<open>j\<^sub>1 = 0\<close> since then
    \<open>Pred M = M = M[n]\<close>): closed by @{thm [source] bf_roper_nonshift} once the
    \<open>Red\<close>-side also degenerates.  The \<open>Red\<close>-side degeneracy
    \<open>(Red M)[n] = Pred (Red M)\<close> is the SECONDARY (light, structural) residual
    \<open>predRdegen\<close> — it is the "\<open>Red\<close> commutes with the recursive \<open>operator[]\<close>
    case-discriminator" fact the article folds into "\<open>Red\<close>と\<open>operator[]\<close>の
    再帰的定義から".
  \<^item> SHIFT (\<open>M[n] \<noteq> Pred M\<close>): the single HARD residual
    @{text bf_roper_shift_resid} (\<open>shift_resid\<close>), the article's
    "\<open>Red\<close>と\<open>Pred\<close>の可換性と\<open>B\<close>の定義から\<open>n\<close>に関する数学的帰納法" branch.  It
    collapses to the existing \<open>operCA\<close> / \<open>has_gz \<Longrightarrow> D(N)\<close> periodic-tiling
    machinery (e.g. @{thm [source] fc_D_oper}, @{thm [source] operB_gen_LngM}),
    so the existing §6.7 \<open>spsy\<close>/\<open>operCA\<close> work plugs in here.
\<close>

lemma m_6_5_Red_oper:
  fixes M :: pairseq and n :: nat
  assumes MT: "M \<in> T_PS"
    and predRdegen: "(M::pairseq)[n] = Pred M \<Longrightarrow> (Red M)[n] = Pred (Red M)"
    and shift_resid: "(M::pairseq)[n] \<noteq> Pred M \<Longrightarrow> (Red M)[n] = Red (M[n])"
  shows "(Red M)[n] = Red (M[n])"
proof (cases "(M::pairseq)[n] = Pred M")
  case True
  show ?thesis by (rule bf_roper_nonshift[OF MT True predRdegen[OF True]])
next
  case False
  show ?thesis by (rule shift_resid[OF False])
qed


subsection \<open>(ii) 簡約性が基本列で保たれること — \<open>m_6_6_red_preserved_by_oper\<close>\<close>

text \<open>
  簡約性が基本列で保たれること（§6.6）: \<open>M \<in> RT\<^sub>PS \<Longrightarrow> M[n] \<in> RT\<^sub>PS\<close>.
  Article proof: \<open>Red\<close>の冪等性 (@{thm [source] m_6_5_Red_idem}) と
  \<open>Red\<close>と基本列の可換性 (i).  Since \<open>M\<close> reduced means \<open>Red M = M\<close>, we have
    \<open>M[n] = (Red M)[n] = Red (M[n])\<close>  [(i)],
  so \<open>M[n]\<close> is a fixpoint of \<open>Red\<close>, i.e. reduced.

  DOMAIN NOTE (correction A4).  The mechanized §6.5 corollaries
  (@{thm [source] m_6_5_Red_idem}, and the \<open>Red\<close>-oper commutativity that
  @{text shift_resid} packages) live on \<open>anchored_slice\<close>, not all of \<open>T\<^sub>PS\<close>.
  A reduced \<open>M\<close> is its own whole slice \<open>seg M 0 (Lng M - 1)\<close>, but
  \<open>anchored_slice\<close> additionally requires the anchor \<open>le0 M 0 (Lng M - 1)\<close>
  (\<open>\<equiv> \<not> multiT M\<close>), which can FAIL for a general reduced/multi \<open>M\<close>.  Hence the
  \<open>M \<in> anchored_slice\<close> hypothesis is carried explicitly here (named residual
  \<open>Manch\<close>); see the report.  We also thread \<open>M[n] \<in> T_PS\<close> for the final
  \<open>RT\<^sub>PS\<close> membership.
\<close>

lemma m_6_6_red_preserved_by_oper:
  fixes M :: pairseq and n :: nat
  assumes Mred: "M \<in> RT_PS"
    and Manch: "M \<in> anchored_slice"
    and opnT: "(M::pairseq)[n] \<in> T_PS"
    and predRdegen: "(M::pairseq)[n] = Pred M \<Longrightarrow> (Red M)[n] = Pred (Red M)"
    and shift_resid: "(M::pairseq)[n] \<noteq> Pred M \<Longrightarrow> (Red M)[n] = Red (M[n])"
  shows "(M::pairseq)[n] \<in> RT_PS"
proof -
  have MT: "M \<in> T_PS" using Mred by (simp add: RT_PS_def)
  have redM: "Red M = M" using Mred by (simp add: RT_PS_def)
  \<comment> \<open>(i): \<open>(Red M)[n] = Red (M[n])\<close>\<close>
  have comm: "(Red M)[n] = Red (M[n])"
    by (rule m_6_5_Red_oper[OF MT predRdegen shift_resid])
  \<comment> \<open>Rewrite the left with \<open>Red M = M\<close>: \<open>M[n] = Red (M[n])\<close>.\<close>
  have fix_oper: "(M::pairseq)[n] = Red (M[n])" using comm redM by simp
  hence "Red (M[n]) = (M::pairseq)[n]" by (rule sym)
  thus ?thesis using opnT by (simp add: RT_PS_def)
qed


subsection \<open>(iii) 標準形の簡約性 — \<open>m_6_7_standard_reduced_faithful\<close>\<close>

text \<open>
  標準形の簡約性（§6.7）: \<open>ST\<^sub>PS \<subseteq> RT\<^sub>PS\<close>, by @{thm [source] ST_PS.induct}:
  \<^item> diag base: \<open>diagSeq u v\<close> (\<open>u \<le> v\<close>) is reduced — supplied by the named base
    fact \<open>diag_red\<close> (the article's "対角線は簡約である").
  \<^item> oper step: from \<open>M \<in> RT\<^sub>PS\<close> (IH) and \<open>1 \<le> n\<close>, \<open>M[n] \<in> RT\<^sub>PS\<close> by (ii)
    @{thm [source] m_6_6_red_preserved_by_oper}.
  The §6.5 residuals (\<open>anchored_slice\<close> domain, \<open>predRdegen\<close>, \<open>shift_resid\<close>) are
  threaded as universally-quantified hypotheses over the standard \<open>M\<close> that arise
  in the induction.  Conditional on those residuals.
\<close>

lemma m_6_7_standard_reduced_faithful:
  assumes diag_red: "\<And>u v. u \<le> v \<Longrightarrow> diagSeq u v \<in> RT_PS"
    and anch: "\<And>M. M \<in> ST_PS \<Longrightarrow> M \<in> RT_PS \<Longrightarrow> M \<in> anchored_slice"
    and predRdegen: "\<And>M n. \<lbrakk>M \<in> ST_PS; M \<in> RT_PS; 1 \<le> n; (M::pairseq)[n] = Pred M\<rbrakk>
                       \<Longrightarrow> (Red M)[n] = Pred (Red M)"
    and shift_resid: "\<And>M n. \<lbrakk>M \<in> ST_PS; M \<in> RT_PS; 1 \<le> n; (M::pairseq)[n] \<noteq> Pred M\<rbrakk>
                       \<Longrightarrow> (Red M)[n] = Red (M[n])"
  shows "ST_PS \<subseteq> RT_PS"
proof
  fix N assume N: "N \<in> ST_PS"
  thus "N \<in> RT_PS"
  proof (induct N rule: ST_PS.induct)
    case (diag u v)
    show ?case by (rule diag_red[OF diag.hyps])
  next
    case (oper M n)
    have MST: "M \<in> ST_PS" by (rule oper.hyps(1))
    have Mred: "M \<in> RT_PS" by (rule oper.hyps(2))
    have n1: "1 \<le> n" by (rule oper.hyps(3))
    have Manch: "M \<in> anchored_slice" by (rule anch[OF MST Mred])
    have opST: "(M::pairseq)[n] \<in> ST_PS" by (rule ST_PS.oper[OF MST n1])
    have opnT: "(M::pairseq)[n] \<in> T_PS" by (rule ST_PS_T_PS[OF opST])
    show "(M::pairseq)[n] \<in> RT_PS"
      by (rule m_6_6_red_preserved_by_oper[OF Mred Manch opnT
              predRdegen[OF MST Mred n1] shift_resid[OF MST Mred n1]])
  qed
qed


subsection \<open>(iv) \<open>stdCA\<close> — \<open>bf_stdCA_faithful\<close>\<close>

text \<open>
  \<open>stdCA\<close>: \<open>\<forall>S \<in> ST\<^sub>PS. RedCondA S\<close>.  From (iii) \<open>ST\<^sub>PS \<subseteq> RT\<^sub>PS\<close> and the §6.6
  keystone 命題（簡約性と係数の関係） @{thm [source] m_6_6_reduced_iff_cond}
  (簡約 \<longleftrightarrow> (A)\<and>(B)), whose (A)-component is \<open>RedCondA\<close>.  Same residuals as (iii).
\<close>

lemma bf_stdCA_faithful:
  assumes diag_red: "\<And>u v. u \<le> v \<Longrightarrow> diagSeq u v \<in> RT_PS"
    and anch: "\<And>M. M \<in> ST_PS \<Longrightarrow> M \<in> RT_PS \<Longrightarrow> M \<in> anchored_slice"
    and predRdegen: "\<And>M n. \<lbrakk>M \<in> ST_PS; M \<in> RT_PS; 1 \<le> n; (M::pairseq)[n] = Pred M\<rbrakk>
                       \<Longrightarrow> (Red M)[n] = Pred (Red M)"
    and shift_resid: "\<And>M n. \<lbrakk>M \<in> ST_PS; M \<in> RT_PS; 1 \<le> n; (M::pairseq)[n] \<noteq> Pred M\<rbrakk>
                       \<Longrightarrow> (Red M)[n] = Red (M[n])"
    and S: "S \<in> ST_PS"
  shows "RedCondA S"
proof -
  have sub: "ST_PS \<subseteq> RT_PS"
    by (rule m_6_7_standard_reduced_faithful[OF diag_red anch predRdegen shift_resid])
  have Sred: "S \<in> RT_PS" using sub S by blast
  have ST: "S \<in> T_PS" by (rule ST_PS_T_PS[OF S])
  have "RedCondA S \<and> RedCondB S"
    using m_6_6_reduced_iff_cond[OF ST] Sred by blast
  thus ?thesis by simp
qed

end
