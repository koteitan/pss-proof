theory Support_6_058
  imports Frontier_6_078
begin

text \<open>§6.7 oper-tiling ROW-1 parent CHARACTERIZATION (Front B, the \<open>i\<^sub>1 = 1\<close>
  / d1pos HARD case), CONDITIONAL form.  This packages the within-block row-1
  \<open>+1\<close> obligation for \<open>i\<^sub>1=1\<close>, taking the d1pos base-parent CORRESPONDENCE as the
  two hypotheses that @{thm [source] operCA_tiling_within1_via_pbase} needs:
  \<open>hpN\<close> (the period base \<open>x'\<close> of \<open>x\<close> has a row-1 parent in \<open>N\<close>) and \<open>pbase\<close> (the
  base of the \<open>N[n]\<close>-parent's row-1 \<open>N\<close>-entry coincides with that of \<open>parent N 1 x'\<close>).
  These are exactly the d1pos ARGMIN-COINCIDENCE facts (empirically 1422/1422,
  base-parent equality 1512/1512: /tmp/_fb_i1_argmin.py, /tmp/_fb_i1_witness.py).
  The unconditional discharge of \<open>hpN\<close>/\<open>pbase\<close> is the d1pos base-correspondence
  brick (forward witness via @{thm [source] oper_gen_le0_within_forward}, backward
  via @{thm [source] oper_d1pos_ctx_period_le0Np}).\<close>

lemma operCA_tiling_row1_charac_i1_cond:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and condA: "RedCondA N"
    and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> x"
    and hpn: "hasParent ((N::pairseq)[n]) 1 x"
    and hpN: "hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                + (x - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                   mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
    and pbase: "entry N 1 (if parent ((N::pairseq)[n]) 1 x
                              < parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                            then parent ((N::pairseq)[n]) 1 x
                            else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                              + (parent ((N::pairseq)[n]) 1 x
                                 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                                mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
               = entry N 1 (parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                  + (x - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                     mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))))"
  shows "entry ((N::pairseq)[n]) 1 (parent ((N::pairseq)[n]) 1 x) + 1
       = entry ((N::pairseq)[n]) 1 x"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?Nn = "(N::pairseq)[n]"
  let ?p = "parent ?Nn 1 x"
  \<comment> \<open>\<open>x < Lng (N[n])\<close> and \<open>p < Lng (N[n])\<close> from \<open>hpn\<close> via the parent edge\<close>
  have nrel: "nextrel1 ?Nn ?p x"
  proof -
    have "\<exists>!j0. nextR ?Nn 1 j0 x" using hpn unfolding hasParent_def by simp
    hence "nextR ?Nn 1 ?p x" unfolding parent_def by (rule theI')
    thus ?thesis by (simp add: nextR_def)
  qed
  from nrel have plt: "?p < Lng ?Nn" and xNn: "x < Lng ?Nn"
    by (auto simp: nextrel1_def)
  show ?thesis
    by (rule operCA_tiling_within1_via_pbase[OF L notzero hp j0lt condA ge xNn plt hpN pbase])
qed


text \<open>§6.7 oper-tiling brick (Front B): the within-block row-1 \<open>+1\<close> obligation
  \<open>within1\<close> for ALL columns \<open>x \<ge> j\<^sub>0\<close>, branching on \<open>idx1 N (Lng N-1) \<le> 1\<close>:
  \<^item> \<open>i\<^sub>1 = 0\<close> is the GREEN @{thm [source] operCA_tiling_row1_charac_i0};
  \<^item> \<open>i\<^sub>1 = 1\<close> is @{thm [source] operCA_tiling_row1_charac_i1_cond}, fed the d1pos
    base-parent CORRESPONDENCE brick \<open>bcorr\<close> (\<open>hpN\<close> + \<open>pbase\<close>) as an explicit
    hypothesis.
  \<open>idx1\<close> is always \<open>\<le> 1\<close> by @{thm [source] idx1_def}.  Once \<open>bcorr\<close> lands
  unconditionally (the d1pos argmin-coincidence), this is the full \<open>within1\<close>.\<close>

lemma operCA_tiling_within1_cond:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and condA: "RedCondA N"
    and bcorr: "\<And>y. parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y
                 \<Longrightarrow> hasParent ((N::pairseq)[n]) 1 y
                 \<Longrightarrow> idx1 N (Lng N - 1) = 1
                 \<Longrightarrow> hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                        + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                           mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                   \<and> entry N 1 (if parent ((N::pairseq)[n]) 1 y
                                  < parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                                then parent ((N::pairseq)[n]) 1 y
                                else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                                  + (parent ((N::pairseq)[n]) 1 y
                                     - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                                    mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                       = entry N 1 (parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                          + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                             mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))))"
    and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> x"
    and hpn: "hasParent ((N::pairseq)[n]) 1 x"
  shows "entry ((N::pairseq)[n]) 1 (parent ((N::pairseq)[n]) 1 x) + 1
       = entry ((N::pairseq)[n]) 1 x"
proof -
  have idxle: "idx1 N (Lng N - 1) \<le> 1" by (simp add: idx1_def)
  show ?thesis
  proof (cases "idx1 N (Lng N - 1) = 1")
    case False
    hence i1z: "idx1 N (Lng N - 1) = 0" using idxle by simp
    show ?thesis
      by (rule operCA_tiling_row1_charac_i0[OF L notzero hp i1z j0lt condA ge hpn])
  next
    case True
    note i1z = True
    have brk: "hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                 + (x - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                    mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
               \<and> entry N 1 (if parent ((N::pairseq)[n]) 1 x
                              < parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                            then parent ((N::pairseq)[n]) 1 x
                            else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                              + (parent ((N::pairseq)[n]) 1 x
                                 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                                mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                   = entry N 1 (parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                      + (x - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                         mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))))"
      by (rule bcorr[OF ge hpn i1z])
    show ?thesis
      by (rule operCA_tiling_row1_charac_i1_cond[OF L notzero hp i1z j0lt condA ge hpn
            conjunct1[OF brk] conjunct2[OF brk]])
  qed
qed


text \<open>§6.7 oper-tiling brick (Front B): \<open>RedCondA (N[n])\<close> for the genuine TILING
  branch, CONDITIONAL only on the d1pos base-parent correspondence \<open>bcorr\<close>.
  Assembled from the unconditional row-0 brick @{thm [source] operCA_tiling_row0}
  and the within-block row-1 brick @{thm [source] operCA_tiling_within1_cond}
  (which is GREEN for \<open>i\<^sub>1=0\<close> and needs \<open>bcorr\<close> only for \<open>i\<^sub>1=1\<close>), glued by
  @{thm [source] operCA_tiling_cond}.  Once \<open>bcorr\<close> lands unconditionally this is
  the full \<open>operCA\<close> discharging @{thm [source] m_6_7_standard_reduced} /
  @{thm [source] m_6_5_Red_le}.\<close>

lemma operCA_tiling_via_bcorr:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and condA: "RedCondA N"
    and n1: "1 \<le> n"
    and bcorr: "\<And>y. parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y
                 \<Longrightarrow> hasParent ((N::pairseq)[n]) 1 y
                 \<Longrightarrow> idx1 N (Lng N - 1) = 1
                 \<Longrightarrow> hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                        + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                           mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                   \<and> entry N 1 (if parent ((N::pairseq)[n]) 1 y
                                  < parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                                then parent ((N::pairseq)[n]) 1 y
                                else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                                  + (parent ((N::pairseq)[n]) 1 y
                                     - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                                    mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                       = entry N 1 (parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                          + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                             mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))))"
  shows "RedCondA ((N::pairseq)[n])"
proof (rule operCA_tiling_cond[OF L notzero hp j0lt condA])
  fix x assume hpn0: "hasParent ((N::pairseq)[n]) 0 x"
  show "entry ((N::pairseq)[n]) 0 (parent ((N::pairseq)[n]) 0 x) + 1
          = entry ((N::pairseq)[n]) 0 x"
    by (rule operCA_tiling_row0[OF L notzero hp j0lt condA n1 hpn0])
next
  fix x assume ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> x"
    and hpn1: "hasParent ((N::pairseq)[n]) 1 x"
  show "entry ((N::pairseq)[n]) 1 (parent ((N::pairseq)[n]) 1 x) + 1
          = entry ((N::pairseq)[n]) 1 x"
    by (rule operCA_tiling_within1_cond[OF L notzero hp j0lt condA bcorr ge hpn1])
qed

end
