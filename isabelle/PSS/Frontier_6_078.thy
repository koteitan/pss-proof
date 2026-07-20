theory Frontier_6_078
  imports Support_6_057
begin

text \<open>d1pos (i1=1) le0 BASE-BACK: a within-block-q le0 chain of N[n]
  (le0 (N[n]) (j0+q*w+sp) (j0+q*w+sx), sp < sx < w) projects to the base slice
  le0 N (j0+sp) (j0+sx).  d1pos analog of the i0 oper_d0zero_le0_base_fwd; the
  row-0 per-block +shamt shift is order-preserving, so the projection routes
  through oper_d1pos_ctx_period_le0Np (the j1red span is an equality).
  Empirically 0-fail (i1=1 base-correspondence: 20004/20004).\<close>

lemma oper_d1pos_le0_base_back:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and qn: "q < n"
    and spx: "sp < sx"
    and sxw: "sx < Lng N - 1 - parent N 1 (Lng N - 1)"
    and reach: "le0 ((N::pairseq)[n])
                  (parent N 1 (Lng N - 1)
                     + q * (Lng N - 1 - parent N 1 (Lng N - 1)) + sp)
                  (parent N 1 (Lng N - 1)
                     + q * (Lng N - 1 - parent N 1 (Lng N - 1)) + sx)"
  shows "le0 N (parent N 1 (Lng N - 1) + sp) (parent N 1 (Lng N - 1) + sx)"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N 1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?Nn = "(N::pairseq)[n]"
  let ?jp = "?j0 + q * ?w + sp"  let ?jx = "?j0 + q * ?w + sx"
  let ?shamt = "q * (entry N 0 ?j1 - entry N 0 ?j0)"
  have w0: "0 < ?w" using j0lt by linarith
  have spw: "sp < ?w" using spx sxw by linarith
  have lenNn: "Lng ?Nn = ?j0 + n * ?w"
    using oper_d1pos_LngM[OF L notzero hp i1z j0lt] by simp
  have jxlt: "?jx < Lng ?Nn"
  proof -
    have "?jx < ?j0 + q * ?w + ?w" using sxw by simp
    also have "\<dots> = ?j0 + (q + 1) * ?w" by simp
    also have "\<dots> \<le> ?j0 + n * ?w" using mult_le_mono1[of "q+1" n ?w] qn by simp
    finally show ?thesis using lenNn by simp
  qed
  have jpjx: "?jp < ?jx" using spx by simp
  have Neq: "?Nn = (N::pairseq)[n]" by simp
  have j0reds: "?j0 + sp = parent N 1 (Lng N - 1) + sp" by simp
  have j0'eq: "?jp = parent N 1 (Lng N - 1)
                  + q * (Lng N - 1 - parent N 1 (Lng N - 1)) + sp" by simp
  have shamteq: "?shamt = q * (entry N 0 (Lng N - 1) - entry N 0 (parent N 1 (Lng N - 1)))"
    by simp
  have j1redle: "?j0 + sx \<le> ?j1" using sxw by linarith
  have j0j1red: "?j0 + sp < ?j0 + sx" using spx by simp
  have j1redspan: "?j0 + sx \<le> (?j0 + sp) + (?jx - ?jp)" using spx by simp
  show "le0 N (?j0 + sp) (?j0 + sx)"
    by (rule oper_d1pos_ctx_period_le0Np[OF L notzero hp i1z j0lt Neq reach jpjx jxlt
          qn spw j0reds j0'eq shamteq j1redle j0j1red j1redspan])
qed

text \<open>§6.7 oper-tiling CROSS-BLOCK row-0 le0 reflection (the \<open>H1\<close> brick).  When an
  offset-\<open>sp\<close> node of an EARLIER block \<open>q'\<close> row-0-reaches the START of a LATER
  block \<open>q\<close> (\<open>q' < q\<close>) in \<open>N[n]\<close>, the \<open>N\<close>-side offset node \<open>j\<^sub>0+sp\<close> row-0-reaches the
  block END \<open>j\<^sub>1\<close>.  This is the cross-block companion of
  @{thm [source] oper_d1pos_le0_base_back} (same block), got from the SAME engine
  @{thm [source] oper_d1pos_ctx_period_le0Np} with target \<open>j\<^sub>1red = j\<^sub>1\<close> and the span
  \<open>j\<^sub>1 \<le> (j\<^sub>0+sp) + (j\<^sub>1' - j\<^sub>0')\<close> reducing to \<open>w \<le> (q-q')\<cdot>w\<close>, i.e. \<open>q' < q\<close>.  Feeds the
  boundary-readback valley: with the \<open>nextrel1 N j\<^sub>0 j\<^sub>1\<close> maximality clause it gives
  \<open>entry N 1 (j\<^sub>0+sp) \<ge> entry N 1 j\<^sub>1 > entry N 1 j\<^sub>0\<close> (RedCondA).\<close>

lemma oper_d1pos_le0_cross_back:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and qq: "q' < q"
    and qn: "q < n"
    and spw: "sp < Lng N - 1 - parent N 1 (Lng N - 1)"
    and reach: "le0 ((N::pairseq)[n])
                  (parent N 1 (Lng N - 1)
                     + q' * (Lng N - 1 - parent N 1 (Lng N - 1)) + sp)
                  (parent N 1 (Lng N - 1)
                     + q * (Lng N - 1 - parent N 1 (Lng N - 1)))"
  shows "le0 N (parent N 1 (Lng N - 1) + sp) (Lng N - 1)"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N 1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?Nn = "(N::pairseq)[n]"
  let ?jp = "?j0 + q' * ?w + sp"   \<comment> \<open>\<open>j\<^sub>0'\<close>: block \<open>q'\<close>, offset \<open>sp\<close>\<close>
  let ?jx = "?j0 + q * ?w"         \<comment> \<open>\<open>j\<^sub>1'\<close>: block \<open>q\<close> START (offset 0)\<close>
  let ?shamt = "q' * (entry N 0 ?j1 - entry N 0 ?j0)"
  have w0: "0 < ?w" using j0lt by linarith
  have qpn: "q' < n" using qq qn by simp
  \<comment> \<open>\<open>q = q' + Suc k\<close>, so \<open>(q - q')\<cdot>w \<ge> w\<close> for the span\<close>
  obtain k where qk: "q = q' + Suc k" using qq less_iff_Suc_add by auto
  have lenNn: "Lng ?Nn = ?j0 + n * ?w"
    using oper_d1pos_LngM[OF L notzero hp i1z j0lt] by simp
  have jxlt: "?jx < Lng ?Nn"
  proof -
    have "q * ?w < n * ?w" by (rule mult_strict_right_mono[OF qn w0])
    hence "?jx < ?j0 + n * ?w" by simp
    thus ?thesis using lenNn by simp
  qed
  have jpjx: "?jp < ?jx"
  proof -
    have "?jp < ?j0 + q' * ?w + ?w" using spw by simp
    also have "\<dots> = ?j0 + (q' + 1) * ?w" by simp
    also have "\<dots> \<le> ?j0 + q * ?w" using mult_le_mono1[of "q' + 1" q ?w] qq by simp
    finally show ?thesis by simp
  qed
  have Neq: "?Nn = (N::pairseq)[n]" by simp
  have j0reds: "?j0 + sp = parent N 1 (Lng N - 1) + sp" by simp
  have j0'eq: "?jp = parent N 1 (Lng N - 1)
                  + q' * (Lng N - 1 - parent N 1 (Lng N - 1)) + sp" by simp
  have shamteq: "?shamt = q' * (entry N 0 (Lng N - 1) - entry N 0 (parent N 1 (Lng N - 1)))"
    by simp
  have j1redle: "?j1 \<le> ?j1" by simp
  have j0j1red: "?j0 + sp < ?j1"
  proof -
    have "?j0 + sp < ?j0 + ?w" using spw by simp
    thus ?thesis using w0 by simp
  qed
  \<comment> \<open>SPAN: \<open>j\<^sub>1 \<le> (j\<^sub>0+sp) + (j\<^sub>1' - j\<^sub>0')\<close>.  With \<open>q = q'+Suc k\<close>: \<open>j\<^sub>1' - j\<^sub>0' = Suc k\<cdot>w - sp\<close>,
     and \<open>(j\<^sub>0+sp) + (Suc k\<cdot>w - sp) = j\<^sub>0 + Suc k\<cdot>w \<ge> j\<^sub>0 + w = j\<^sub>1\<close>.\<close>
  have j1redspan: "?j1 \<le> (?j0 + sp) + (?jx - ?jp)"
  proof -
    have e1: "?jx = ?j0 + q' * ?w + Suc k * ?w" using qk by (simp add: add_mult_distrib)
    have e2: "?jx - ?jp = Suc k * ?w - sp" using e1 by simp
    have wle: "?w \<le> Suc k * ?w" by simp
    have sple: "sp \<le> Suc k * ?w" by (rule less_imp_le[OF less_le_trans[OF spw wle]])
    have "(?j0 + sp) + (?jx - ?jp) = ?j0 + sp + (Suc k * ?w - sp)" using e2 by simp
    also have "\<dots> = ?j0 + Suc k * ?w" using sple by simp
    finally have eq: "(?j0 + sp) + (?jx - ?jp) = ?j0 + Suc k * ?w" .
    have "?j1 = ?j0 + ?w" using w0 by simp
    also have "\<dots> \<le> ?j0 + Suc k * ?w" using w0 by simp
    finally show ?thesis using eq by simp
  qed
  show "le0 N (?j0 + sp) ?j1"
    by (rule oper_d1pos_ctx_period_le0Np[OF L notzero hp i1z j0lt Neq reach jpjx jxlt
          qpn spw j0reds j0'eq shamteq j1redle j0j1red j1redspan])
qed

end
