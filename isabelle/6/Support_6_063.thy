theory Support_6_063
  imports Frontier_6_083
begin

subsection \<open>(vii) §6.7 \<open>D(N)\<close> crux assembly — \<open>m_6_7_oper_gstrict\<close> (induct skeleton)\<close>

text \<open>
  The lone open core of §6.7 standard-reducedness, the scalar crux
  \<open>m_6_7_oper_gstrict\<close>: a GATED \<open>N \<in> ST\<^sub>PS\<close> (one possessing a gated interior
  row-1 node \<open>z\<close>: \<open>j\<^sub>0 < z < j\<^sub>1\<close>, \<open>hasParent N 1 z\<close>, \<open>parent N 1 z > j\<^sub>0\<close> with
  \<open>j\<^sub>0 = parent N 1 (Lng N-1)\<close>) has row-0 endpoint at the full width: \<open>D(N)\<close>,
  \<open>entry N 0 (Lng N-1) = entry N 0 0 + (Lng N-1)\<close>.  Once \<open>D(N)\<close> is GREEN, the
  whole spsy/operCA cascade is unconditional (@{thm [source] cd_tree_from_D}
  converts it to the spsy TREE clause).

  This is the INDUCTIVE assembly (\<open>ST_PS.induct\<close>), property \<open>has_gz N \<longrightarrow> D N\<close>:
  \<^item> \<open>diag\<close>: \<open>D(diagSeq u v)\<close> always (@{thm [source] fc_D_diag}), so the implication
    holds trivially.
  \<^item> \<open>oper\<close> \<open>N = M[n]\<close> (\<open>M \<in> ST\<^sub>PS\<close>, \<open>n \<ge> 1\<close>), IH \<open>has_gz M \<longrightarrow> D M\<close>: the gate
    \<open>has_gz(M[n])\<close> FORCES \<open>M\<close> into the genuine tiling branch (\<open>gatekeep\<close>:
    \<open>1 < Lng M\<close>, endpoint \<open>\<noteq> (0,0)\<close>, \<open>hasParent\<close>, \<open>i\<^sub>1 = 1\<close>, \<open>j\<^sub>0 < j\<^sub>1\<close>) — the
    degenerate (\<open>M[n] = Pred M\<close>) and \<open>i\<^sub>1 = 0\<close> branches never carry a gated \<open>z\<close>
    (864 non-gated oper-steps, 0 \<open>has_gz\<close>).  Then the DISJUNCTION core
    (\<open>disj\<close>: \<open>has_gz(M[n]) \<Longrightarrow> has_gz M \<or> D M\<close>, verified 621/0 on the broad ST_PS
    closure) yields \<open>has_gz M \<or> D M\<close>: in the \<open>has_gz M\<close> case the IH gives \<open>D M\<close>,
    in the \<open>D M\<close> case it holds directly; either way @{thm [source] fc_D_oper}
    propagates \<open>D M\<close> to \<open>D (M[n]) = D N\<close>.

  Switching from \<open>ST_PS.cases\<close> to \<open>ST_PS.induct\<close> makes the IH \<open>has_gz M \<longrightarrow> D M\<close>
  available, which is what breaks the apparent circularity of the \<open>w > 1\<close> branch:
  \<open>disj\<close> there reduces to \<open>has_gz(M[n]) \<Longrightarrow> has_gz M\<close> (the \<open>w > 1\<close> gated \<open>z\<close> is
  ALWAYS interior, so it reflects to a gated \<open>z\<close> in \<open>M\<close> via the GREEN INTERIOR
  readback @{thm [source] oper_parent1_readback} — NO boundary valley), then the
  IH discharges \<open>D M\<close>.  The \<open>w = 1\<close> branch reduces to \<open>has_gz(M[n]) \<Longrightarrow> D M\<close>.
  The two analytic cores \<open>gatekeep\<close> and \<open>disj\<close> are carried here as named
  hypotheses; both empirically 0-fail on the broad ST_PS closure.
\<close>

lemma m_6_7_oper_gstrict:
  fixes N :: pairseq
  assumes gatekeep:
      "\<And>M n. \<lbrakk>M \<in> ST_PS; 1 \<le> n;
              \<exists>z. parent ((M::pairseq)[n]) 1 (Lng ((M::pairseq)[n]) - 1) < z
                  \<and> z < Lng ((M::pairseq)[n]) - 1
                  \<and> hasParent ((M::pairseq)[n]) 1 z
                  \<and> parent ((M::pairseq)[n]) 1 z
                       > parent ((M::pairseq)[n]) 1 (Lng ((M::pairseq)[n]) - 1)\<rbrakk>
             \<Longrightarrow> 1 < Lng M
                \<and> \<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)
                \<and> hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)
                \<and> idx1 M (Lng M - 1) = 1
                \<and> parent M 1 (Lng M - 1) < Lng M - 1"
    and disj:
      "\<And>M n. \<lbrakk>M \<in> ST_PS; 1 < Lng M;
              \<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0);
              hasParent M (idx1 M (Lng M - 1)) (Lng M - 1);
              idx1 M (Lng M - 1) = 1;
              parent M 1 (Lng M - 1) < Lng M - 1; 1 \<le> n;
              \<exists>z. parent ((M::pairseq)[n]) 1 (Lng ((M::pairseq)[n]) - 1) < z
                  \<and> z < Lng ((M::pairseq)[n]) - 1
                  \<and> hasParent ((M::pairseq)[n]) 1 z
                  \<and> parent ((M::pairseq)[n]) 1 z
                       > parent ((M::pairseq)[n]) 1 (Lng ((M::pairseq)[n]) - 1)\<rbrakk>
             \<Longrightarrow> (\<exists>z. parent M 1 (Lng M - 1) < z \<and> z < Lng M - 1
                       \<and> hasParent M 1 z \<and> parent M 1 z > parent M 1 (Lng M - 1))
                \<or> entry M 0 (Lng M - 1) = entry M 0 0 + (Lng M - 1)"
    and N: "N \<in> ST_PS"
    and gz: "\<exists>z. parent N 1 (Lng N - 1) < z \<and> z < Lng N - 1
                 \<and> hasParent N 1 z \<and> parent N 1 z > parent N 1 (Lng N - 1)"
  shows "entry N 0 (Lng N - 1) = entry N 0 0 + (Lng N - 1)"
proof -
  have "(\<exists>z. parent N 1 (Lng N - 1) < z \<and> z < Lng N - 1
              \<and> hasParent N 1 z \<and> parent N 1 z > parent N 1 (Lng N - 1))
        \<longrightarrow> entry N 0 (Lng N - 1) = entry N 0 0 + (Lng N - 1)"
    using N
  proof (induct N rule: ST_PS.induct)
    case (diag u v)
    show ?case using fc_D_diag[OF diag.hyps] by blast
  next
    case (oper M n)
    have MST: "M \<in> ST_PS" and n1: "1 \<le> n" using oper.hyps by auto
    show ?case
    proof (rule impI)
      assume gzMn:
        "\<exists>z. parent ((M::pairseq)[n]) 1 (Lng ((M::pairseq)[n]) - 1) < z
             \<and> z < Lng ((M::pairseq)[n]) - 1
             \<and> hasParent ((M::pairseq)[n]) 1 z
             \<and> parent ((M::pairseq)[n]) 1 z
                  > parent ((M::pairseq)[n]) 1 (Lng ((M::pairseq)[n]) - 1)"
      have G: "1 < Lng M
               \<and> \<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)
               \<and> hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)
               \<and> idx1 M (Lng M - 1) = 1
               \<and> parent M 1 (Lng M - 1) < Lng M - 1"
        by (rule gatekeep[OF MST n1 gzMn])
      from G have L: "1 < Lng M"
        and nz: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
        and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
        and i1z: "idx1 M (Lng M - 1) = 1"
        and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1" by auto
      have HD: "(\<exists>z. parent M 1 (Lng M - 1) < z \<and> z < Lng M - 1
                      \<and> hasParent M 1 z \<and> parent M 1 z > parent M 1 (Lng M - 1))
                \<or> entry M 0 (Lng M - 1) = entry M 0 0 + (Lng M - 1)"
        by (rule disj[OF MST L nz hp i1z j0lt n1 gzMn])
      have DM: "entry M 0 (Lng M - 1) = entry M 0 0 + (Lng M - 1)"
        using HD oper.hyps by blast
      show "entry ((M::pairseq)[n]) 0 (Lng ((M::pairseq)[n]) - 1)
            = entry ((M::pairseq)[n]) 0 0 + (Lng ((M::pairseq)[n]) - 1)"
        by (rule fc_D_oper[OF MST L nz hp i1z j0lt n1 DM])
    qed
  qed
  thus ?thesis using gz by blast
qed

end
