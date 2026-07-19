theory Support_6_022
  imports Frontier_6_039
begin

text \<open>§6.8 d1pos \<open>\<not>brle\<close> REGIME B anchor coincidence, clt/cNlt-FREE (the BOUNDARY
  analogue of @{thm [source] oper_d1pos_anchor_coincide_regA2}).  In regime B
  (\<open>j\<^sub>m\<^sub>2 \<le> A < Lng N-1\<close>, where \<open>A = j'\<^sub>0 + TrMax M' + 1\<close>) the slice start \<open>A\<close> sits in
  BLOCK 0 of the period (\<open>q\<^sub>0 = (A-j\<^sub>m\<^sub>2) div w = 0\<close> since \<open>A-j\<^sub>m\<^sub>2 < w\<close>), so
  \<open>shamt = q\<^sub>0\<cdot>\<delta> = 0\<close> and both row-0 anchors AGREE verbatim — but UNLIKE regime A the
  common anchor sits AT the boundary \<open>c = c\<^sub>N = m = Lng (seg N A (Lng N-1)) - 1\<close>
  (the last \<open>P\<close>-component is a singleton, so the strict bound of
  @{thm [source] oper_d1pos_anchor_coincide_regB} is INAPPLICABLE).  We pin the two
  anchors at \<open>m\<close> directly: \<open>c \<le> m\<close> by @{thm [source] oper_d1pos_clt_regB},
  \<open>c \<ge> m\<close> and \<open>c\<^sub>N \<ge> m\<close>/\<open>c\<^sub>N \<le> m\<close> by @{thm [source] anchor_ge_of_leftmin} /
  @{thm [source] oper_d1pos_branch_anchor}(2) from the residual block-fold left-min
  facts \<open>mLmin_S\<close>/\<open>mLmin_Sn\<close> (the boundary index \<open>m\<close>, resp. the last index of
  \<open>Snside\<close>, is a row-0 left-min — DEEP-VERIFIED 519/519, /tmp/regB_mleftmin.py /
  /tmp/regB_cNm.py).  The junction entries are then read at the single index \<open>m\<close>
  (\<open>A+m = Lng N-1 = j\<^sub>m\<^sub>2 + w\<close>, block 1 offset 0): row-0 \<open>entry S 0 m = entry N 0
  (Lng N-1) = entry Snside 0 m\<close> (@{thm [source] oper_d1pos_entry0}, \<open>shamt = 0\<close>),
  row-1 \<open>entry S 1 m = entry N 1 j\<^sub>m\<^sub>2 \<le> entry N 1 (Lng N-1) = entry Snside 1 m\<close>
  (@{thm [source] oper_d1pos_entry1} + the row-1 period bound \<open>r1le\<close>).
  DEEP-VERIFIED rank 10 (519/519, /tmp/regB_ceqm.py, /tmp/regB_entrybd.py,
  /tmp/regB_row1.py).  The hypotheses \<open>mLmin_S\<close>/\<open>mLmin_Sn\<close>/\<open>r1le\<close> are exactly the
  residual block-fold / first-node geometry (parent supplies them).\<close>

lemma oper_d1pos_anchor_coincide_regB2:
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
    and Ajm2: "parent N 1 (Lng N - 1) \<le> A"
    and AltN: "A < Lng N - 1"
    and Ele: "Lng N - 1 \<le> E"
    and Eub: "E < Lng ((N::pairseq)[n])"
    and dpos: "entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1)"
    and multi: "1 < length (P S)"
    and multiN: "1 < length (P Snside)"
    and mLmin_S: "\<forall>j < Lng (seg N A (Lng N - 1)) - 1.
                    entry S 0 (Lng (seg N A (Lng N - 1)) - 1) \<le> entry S 0 j"
    and mLmin_Sn: "\<forall>j < Lng Snside - 1. entry Snside 0 (Lng Snside - 1) \<le> entry Snside 0 j"
    and r1le: "entry N 1 (parent N 1 (Lng N - 1)) \<le> entry N 1 (Lng N - 1)"
  shows "c = cN"
    and "entry S 0 c = entry Snside 0 cN"
    and "entry S 1 c \<le> entry Snside 1 cN"
proof -
  let ?jm2 = "parent N 1 (Lng N - 1)"  let ?j1 = "Lng N - 1"  let ?w = "?j1 - ?jm2"
  let ?delta = "entry N 0 ?j1 - entry N 0 ?jm2"
  let ?m = "Lng (seg N A ?j1) - 1"
  have mval: "?m = ?j1 - A" using AltN by simp
  have w0: "0 < ?w" using j0lt by linarith
  obtain w where wdef: "?w = w" by blast
  have w0': "0 < w" using w0 wdef by simp
  have lenMn: "Lng ((N::pairseq)[n]) = ?jm2 + n * w"
    using oper_d1pos_LngM[OF L notzero hp i1z j0lt] wdef by simp
  \<comment> \<open>\<open>1 < n\<close>: \<open>jm2 + w = Lng N-1 \<le> E < Lng (N[n]) = jm2 + n*w\<close> forces \<open>w < n*w\<close>\<close>
  have jm2w: "?jm2 + w = ?j1" using wdef j0lt by linarith
  have n2: "1 < n"
  proof -
    have "?jm2 + w \<le> E" using Ele jm2w by simp
    hence "?jm2 + w < ?jm2 + n * w" using Eub lenMn by linarith
    hence "w < n * w" by simp
    thus ?thesis using w0' by (simp add: mult.commute)
  qed
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
  have LngS: "Lng S = Suc E - A" unfolding S_def by simp
  have LngSn: "Lng Snside = Suc ?j1 - A" unfolding Snside_def by simp
  have mSn: "Lng Snside - 1 = ?m" using LngSn AltN by simp
  \<comment> \<open>\<open>m\<close> is a valid index of both \<open>S\<close> and \<open>Snside\<close> (\<open>A + m = Lng N-1 \<le> E\<close>)\<close>
  have Amj1: "A + ?m = ?j1" using mval AltN by linarith
  have mltS: "?m < Lng S" using LngS Ele AltN mval by linarith
  have mltSn: "?m < Lng Snside" using mSn LngSn AltN by linarith
  \<comment> \<open>pin \<open>c = m\<close>: \<open>c \<le> m\<close> (clt) and \<open>c \<ge> m\<close> (\<open>m\<close> a leftend of \<open>S\<close>)\<close>
  have cle: "c \<le> ?m" unfolding c_def S_def
    by (rule oper_d1pos_clt_regB[OF L notzero hp i1z j0lt n1 Ajm2 AltN Ele Eub dpos
              multi[unfolded S_def c_def]])
  have mleS1: "?m \<le> Lng S - 1" using mltS by linarith
  have cge: "?m \<le> c" unfolding c_def
    by (rule anchor_ge_of_leftmin[OF ST mleS1]) (use mLmin_S in simp)
  have ceqm: "c = ?m" using cle cge by linarith
  \<comment> \<open>pin \<open>cN = m\<close>: \<open>cN \<le> Lng Snside-1 = m\<close> (anchor) and \<open>cN \<ge> m\<close> (last index a leftend)\<close>
  have cNle: "cN \<le> Lng Snside - 1" unfolding cN_def
    by (rule oper_d1pos_branch_anchor(2)[OF SnT multiN])
  have cNle': "cN \<le> ?m" using cNle mSn by simp
  have mleSn1: "Lng Snside - 1 \<le> Lng Snside - 1" by simp
  have cNge: "Lng Snside - 1 \<le> cN" unfolding cN_def
    by (rule anchor_ge_of_leftmin[OF SnT mleSn1]) (use mLmin_Sn in simp)
  have cNeqm: "cN = ?m" using cNge cNle' mSn by linarith
  \<comment> \<open>c = cN\<close>
  show ceqcN: "c = cN" using ceqm cNeqm by simp
  \<comment> \<open>row-0 at the junction index \<open>m\<close>: both read \<open>entry N 0 (Lng N-1)\<close> (\<open>shamt = 0\<close>)\<close>
  have eSm0: "entry S 0 ?m = entry N 0 ?j1"
  proof -
    have wpos: "(0::nat) < ?w" using w0 .
    have decode: "entry ((N::pairseq)[n]) 0 (?jm2 + 1 * ?w + 0)
              = entry N 0 (?jm2 + 0) + 1 * ?delta"
      by (rule oper_d1pos_entry0[OF L notzero hp i1z j0lt n2 wpos])
    have idx: "A + ?m = ?jm2 + 1 * ?w + 0" using Amj1 wdef j0lt by simp
    have "entry S 0 ?m = entry ((N::pairseq)[n]) 0 (A + ?m)"
      unfolding S_def by (rule entry_seg[OF mltS[unfolded S_def]])
    also have "\<dots> = entry ((N::pairseq)[n]) 0 (?jm2 + 1 * ?w + 0)" using idx by simp
    also have "\<dots> = entry N 0 ?jm2 + ?delta" using decode by simp
    also have "\<dots> = entry N 0 ?j1" using dpos by simp
    finally show ?thesis .
  qed
  have eSnm0: "entry Snside 0 ?m = entry N 0 ?j1"
  proof -
    have "entry Snside 0 ?m = entry N 0 (A + ?m)"
      unfolding Snside_def by (rule entry_seg[OF mltSn[unfolded Snside_def]])
    thus ?thesis using Amj1 by simp
  qed
  show "entry S 0 c = entry Snside 0 cN"
    using eSm0 eSnm0 ceqm cNeqm by simp
  \<comment> \<open>row-1 at the junction index \<open>m\<close>: \<open>entry S 1 m = entry N 1 jm2 \<le> entry N 1 (Lng N-1)
     = entry Snside 1 m\<close>\<close>
  have eSm1: "entry S 1 ?m = entry N 1 ?jm2"
  proof -
    have wpos: "(0::nat) < ?w" using w0 .
    have decode: "entry ((N::pairseq)[n]) 1 (?jm2 + 1 * ?w + 0)
              = entry N 1 (?jm2 + 0)"
      by (rule oper_d1pos_entry1[OF L notzero hp i1z j0lt n2 wpos])
    have idx: "A + ?m = ?jm2 + 1 * ?w + 0" using Amj1 wdef j0lt by simp
    have "entry S 1 ?m = entry ((N::pairseq)[n]) 1 (A + ?m)"
      unfolding S_def by (rule entry_seg[OF mltS[unfolded S_def]])
    also have "\<dots> = entry ((N::pairseq)[n]) 1 (?jm2 + 1 * ?w + 0)" using idx by simp
    also have "\<dots> = entry N 1 ?jm2" using decode by simp
    finally show ?thesis .
  qed
  have eSnm1: "entry Snside 1 ?m = entry N 1 ?j1"
  proof -
    have "entry Snside 1 ?m = entry N 1 (A + ?m)"
      unfolding Snside_def by (rule entry_seg[OF mltSn[unfolded Snside_def]])
    thus ?thesis using Amj1 by simp
  qed
  show "entry S 1 c \<le> entry Snside 1 cN"
    using eSm1 eSnm1 r1le ceqm cNeqm by simp
qed

end
