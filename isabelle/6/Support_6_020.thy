theory Support_6_020
  imports Frontier_6_037
begin

text \<open>§6.8 d1pos ¬brle — the \<open>lowshift\<close> hypothesis of
  @{thm [source] oper_d1pos_branch_collapse_concrete} in the UNCAPPED regime B
  (conc-A).  The LOW prefix \<open>seg S 0 (c-1)\<close> of the reshaped \<open>M\<close>-side branch region
  \<open>S = seg (N[n]) A E\<close> (\<open>A = j0' + TrMax M' + 1\<close>) lies, in regime B, in a SINGLE
  block \<open>q\<close> of the periodic \<open>N[n]\<close>-extension (\<open>A \<ge> jm2\<close>, the offset
  \<open>e0 = (A - jm2) - q\<cdot>w + (c-1)\<close> staying \<open><w\<close>), and is therefore an
  \<open>(IncrFirst^^(q\<cdot>\<delta>))\<close>-shift of the \<open>N\<close>-side base slice \<open>seg N (jm2+s0) (jm2+e0)\<close>,
  by @{thm [source] oper_d1pos_LOW_source_eq}.  The single-block realisation
  (\<open>Aform\<close>/\<open>e0lt\<close>/\<open>qn\<close>) is the residual \<open>d1pos\<close> block-fold geometry (the documented
  BLOCKER); given it, this lemma packages \<open>lowshift\<close> with
  \<open>shamt = q\<cdot>(entry N 0 (Lng N-1) - entry N 0 jm2)\<close>,
  \<open>base = seg N (jm2+s0) (jm2+e0)\<close>.  Pure reshape (@{thm [source] seg_of_seg}) +
  @{thm [source] oper_d1pos_LOW_source_eq}.  DEEP-VERIFIED rank 8
  (/tmp/conc_a_verify.py route): the in-block source-eq holds 1128/1128 of the
  regime-B \<open>A \<ge> jm2\<close> cases (the 267 \<open>A < jm2\<close> cases are regime A / the capped
  residual).\<close>

lemma oper_d1pos_branch_lowshift_regB:
  fixes N :: pairseq
  defines "jm2 \<equiv> parent N 1 (Lng N - 1)"
      and "w \<equiv> Lng N - 1 - parent N 1 (Lng N - 1)"
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and qn: "q < n"
    and Aform: "A = jm2 + q * w + s0"
    and s0e0: "s0 \<le> s0 + (cc - 1)"
    and e0lt: "s0 + (cc - 1) < w"
    and Ele: "A \<le> E" and ccle: "cc - 1 \<le> E - A"
  shows "seg (seg (N[n]) A E) 0 (cc - 1)
       = (IncrFirst ^^ (q * (entry N 0 (Lng N - 1) - entry N 0 jm2)))
            (seg N (jm2 + s0) (jm2 + (s0 + (cc - 1))))"
proof -
  let ?j1 = "Lng N - 1"
  have wdef: "w = ?j1 - parent N 1 ?j1" unfolding w_def by simp
  have jm2def: "jm2 = parent N 1 ?j1" unfolding jm2_def by simp
  \<comment> \<open>rule-shaped hypotheses (unfold the \<open>w\<close> abbreviation)\<close>
  have e0lt': "s0 + (cc - 1) < ?j1 - parent N 1 ?j1" using e0lt wdef by simp
  \<comment> \<open>the source-equality from @{thm [source] oper_d1pos_LOW_source_eq}\<close>
  have src: "seg (N[n]) (parent N 1 ?j1 + q * (?j1 - parent N 1 ?j1) + s0)
                        (parent N 1 ?j1 + q * (?j1 - parent N 1 ?j1) + (s0 + (cc - 1)))
       = (IncrFirst ^^ (q * (entry N 0 ?j1 - entry N 0 (parent N 1 ?j1))))
            (seg N (parent N 1 ?j1 + s0) (parent N 1 ?j1 + (s0 + (cc - 1))))"
    by (rule oper_d1pos_LOW_source_eq[OF L notzero hp i1z j0lt qn s0e0 e0lt'])
  \<comment> \<open>rewrite the source-eq into \<open>jm2\<close>/\<open>w\<close> abbreviations\<close>
  have src': "seg (N[n]) A (A + (cc - 1))
       = (IncrFirst ^^ (q * (entry N 0 ?j1 - entry N 0 jm2)))
            (seg N (jm2 + s0) (jm2 + (s0 + (cc - 1))))"
  proof -
    let ?lo = "parent N 1 ?j1 + q * (?j1 - parent N 1 ?j1) + s0"
    let ?hi = "parent N 1 ?j1 + q * (?j1 - parent N 1 ?j1) + (s0 + (cc - 1))"
    have lo: "A = ?lo" using Aform wdef jm2def by simp
    have hi: "A + (cc - 1) = ?hi" using lo by (simp add: add.assoc)
    have jbase: "(jm2 + s0) = parent N 1 ?j1 + s0" using jm2def by simp
    have jhi: "(jm2 + (s0 + (cc - 1))) = parent N 1 ?j1 + (s0 + (cc - 1))"
      using jm2def by simp
    have jshift: "entry N 0 jm2 = entry N 0 (parent N 1 ?j1)" using jm2def by simp
    have "seg (N[n]) A (A + (cc - 1)) = seg (N[n]) ?lo ?hi"
      by (simp only: hi[symmetric] lo[symmetric])
    also have "\<dots> = (IncrFirst ^^ (q * (entry N 0 ?j1 - entry N 0 (parent N 1 ?j1))))
            (seg N (parent N 1 ?j1 + s0) (parent N 1 ?j1 + (s0 + (cc - 1))))"
      by (rule src)
    also have "\<dots> = (IncrFirst ^^ (q * (entry N 0 ?j1 - entry N 0 jm2)))
            (seg N (jm2 + s0) (jm2 + (s0 + (cc - 1))))"
      using jbase jhi jshift by simp
    finally show ?thesis .
  qed
  \<comment> \<open>the LOW prefix is the reshape \<open>seg (seg (N[n]) A E) 0 (cc-1) = seg (N[n]) A (A+(cc-1))\<close>\<close>
  have reshape: "seg (seg (N[n]) A E) 0 (cc - 1) = seg (N[n]) (A + 0) (A + (cc - 1))"
    by (rule seg_of_seg[OF Ele ccle])
  thus ?thesis using src' by simp
qed

end
