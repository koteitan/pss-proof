theory Frontier_6_076
  imports Support_6_055
begin

text \<open>§6.7 oper-tiling brick (Front A, ROW 0): the \<open>i\<^sub>1\<close>-AGNOSTIC \<open>+1\<close> step at the
  FIRST block start \<open>x = j\<^sub>0\<close> (\<open>q = 0\<close>).  Block 0 is VERBATIM (\<open>0\<cdot>d\<^sub>0 = 0\<close>), so
  \<open>e\<^sub>0(N[n],j\<^sub>0) = e\<^sub>0(N,j\<^sub>0)\<close>, the global block-floor minimum
  (@{thm [source] oper_gen_blockfloor_min}).  Any \<open>N[n]\<close>-parent \<open>p\<close> of \<open>j\<^sub>0\<close> has
  row-0 value strictly below this minimum, so it sits in the verbatim PREFIX
  \<open>[0, j\<^sub>0)\<close>; the edge reflects verbatim to \<open>nextrel0 N p j\<^sub>0\<close> (the valley above
  \<open>j\<^sub>0\<close> is automatic by the block-floor min), giving \<open>parent N 0 j\<^sub>0 = p\<close> and
  \<open>RedCondA N\<close> closes the step.  Empirically 0-fail (/tmp/frontA_xj0.py:
  972/972 parent in prefix).\<close>

lemma oper_gen_tiling_row0_blockstart0:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and condA: "RedCondA N"
    and n1: "1 \<le> n"
    and hpn: "hasParent ((N::pairseq)[n]) 0 (parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
  shows "entry ((N::pairseq)[n]) 0 (parent ((N::pairseq)[n]) 0
                (parent N (idx1 N (Lng N - 1)) (Lng N - 1))) + 1
       = entry ((N::pairseq)[n]) 0 (parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?Nn = "(N::pairseq)[n]"
  have w0: "0 < ?w" using j0lt by linarith
  have lenNn: "Lng ?Nn = ?j0 + n * ?w" using operB_gen_LngM[OF L notzero hp j0lt] by simp
  have j0Nn: "?j0 < Lng ?Nn"
  proof -
    have "?j0 + 1 * ?w \<le> ?j0 + n * ?w" using n1 by simp
    thus ?thesis using w0 lenNn by simp
  qed
  \<comment> \<open>verbatim prefix on row 0\<close>
  have pref: "\<And>y. y < ?j0 \<Longrightarrow> entry ?Nn 0 y = entry N 0 y"
    using operB_gen_entry_prefix[OF L notzero hp] by blast
  \<comment> \<open>block 0 verbatim: \<open>x = j\<^sub>0\<close> reads \<open>e\<^sub>0(N,j\<^sub>0)\<close>\<close>
  have n0: "0 < n" using n1 by simp
  have ex: "entry ?Nn 0 ?j0 = entry N 0 ?j0"
    using oper_gen_block_entry0[OF L notzero hp j0lt n0 w0] by simp
  \<comment> \<open>block-floor min\<close>
  have ge_min: "\<And>y. ?j0 \<le> y \<Longrightarrow> y < Lng ?Nn \<Longrightarrow> entry N 0 ?j0 \<le> entry ?Nn 0 y"
    using oper_gen_blockfloor_min[OF L notzero hp j0lt] by blast
  \<comment> \<open>obtain the unique \<open>N[n]\<close>-parent \<open>p\<close> of \<open>j\<^sub>0\<close>\<close>
  have exu: "\<exists>!p. nextrel0 ?Nn p ?j0"
    using hpn unfolding hasParent_def nextR_def by simp
  obtain p where pP: "nextrel0 ?Nn p ?j0"
    and pU: "\<And>p'. nextrel0 ?Nn p' ?j0 \<Longrightarrow> p' = p"
    using exu by blast
  have pjx: "p < ?j0" using pP by (simp add: nextrel0_def)
  have pval0: "entry ?Nn 0 p < entry ?Nn 0 ?j0" using pP by (simp add: nextrel0_def)
  have valley: "\<And>j. p < j \<Longrightarrow> j < ?j0 \<Longrightarrow> entry ?Nn 0 ?j0 \<le> entry ?Nn 0 j"
    using pP by (simp add: nextrel0_def)
  \<comment> \<open>the edge reflects to \<open>nextrel0 N p j\<^sub>0\<close> (prefix verbatim; valley below \<open>j\<^sub>0\<close>)\<close>
  have stepN: "nextrel0 N p ?j0"
    unfolding nextrel0_def
  proof (intro conjI allI impI)
    show "p < Lng N" using pjx j0lt by linarith
    show "?j0 < Lng N" using j0lt by linarith
    show "p < ?j0" by (rule pjx)
    have "entry ?Nn 0 p < entry ?Nn 0 ?j0" by (rule pval0)
    thus "entry N 0 p < entry N 0 ?j0" using pref[OF pjx] ex by simp
  next
    fix j assume jj: "p < j \<and> j < ?j0"
    hence jp: "p < j" and jj0: "j < ?j0" by simp_all
    have "entry ?Nn 0 ?j0 \<le> entry ?Nn 0 j" using valley[OF jp jj0] .
    thus "entry N 0 ?j0 \<le> entry N 0 j" using pref[OF jj0] ex by simp
  qed
  \<comment> \<open>uniqueness back\<close>
  have uniqN: "\<And>p'. nextrel0 N p' ?j0 \<Longrightarrow> p' = p"
  proof -
    fix p' assume Hp': "nextrel0 N p' ?j0"
    have p'j0: "p' < ?j0" using Hp' by (simp add: nextrel0_def)
    have stepNn: "nextrel0 ?Nn p' ?j0"
      unfolding nextrel0_def
    proof (intro conjI allI impI)
      show "p' < Lng ?Nn" using p'j0 j0Nn by linarith
      show "?j0 < Lng ?Nn" by (rule j0Nn)
      show "p' < ?j0" by (rule p'j0)
      have "entry N 0 p' < entry N 0 ?j0" using Hp' by (simp add: nextrel0_def)
      thus "entry ?Nn 0 p' < entry ?Nn 0 ?j0" using pref[OF p'j0] ex by simp
    next
      fix j assume jj: "p' < j \<and> j < ?j0"
      hence jp: "p' < j" and jj0: "j < ?j0" by simp_all
      have "entry N 0 ?j0 \<le> entry N 0 j" using Hp' jp jj0 by (simp add: nextrel0_def)
      thus "entry ?Nn 0 ?j0 \<le> entry ?Nn 0 j" using pref[OF jj0] ex by simp
    qed
    show "p' = p" using pU[OF stepNn] .
  qed
  have stepNR: "nextR N 0 p ?j0" using stepN by (simp add: nextR_def)
  have uniqNR: "\<And>p'. nextR N 0 p' ?j0 \<Longrightarrow> p' = p"
    using uniqN by (simp add: nextR_def)
  have pPR: "nextR ?Nn 0 p ?j0" using pP by (simp add: nextR_def)
  have pUR: "\<And>p'. nextR ?Nn 0 p' ?j0 \<Longrightarrow> p' = p"
    using pU by (simp add: nextR_def)
  have hpNj0: "hasParent N 0 ?j0"
    unfolding hasParent_def using stepNR uniqNR by blast
  have parN: "parent N 0 ?j0 = p" by (rule parent0_eqI[OF stepNR uniqNR])
  have parNn: "parent ?Nn 0 ?j0 = p" by (rule parent0_eqI[OF pPR pUR])
  have baseN: "entry N 0 (parent N 0 ?j0) + 1 = entry N 0 ?j0"
    using condA[unfolded RedCondA_def, rule_format, of 0 ?j0] hpNj0 by simp
  have "entry ?Nn 0 (parent ?Nn 0 ?j0) + 1 = entry N 0 p + 1"
    using parNn pref[OF pjx] by simp
  also have "\<dots> = entry N 0 ?j0" using baseN parN by simp
  also have "\<dots> = entry ?Nn 0 ?j0" using ex by simp
  finally show ?thesis .
qed


text \<open>§6.7 oper-tiling brick (Front A, ROW 0): the FULL row-0 obligation of
  \<open>RedCondA (N[n])\<close>.  For every column \<open>x\<close> of \<open>N[n]\<close> with a row-0 parent the
  \<open>+1\<close> step holds, assembled by splitting on the position of \<open>x\<close> relative to the
  first block start \<open>j\<^sub>0 = parent N i\<^sub>1 (Lng N-1)\<close> and the period \<open>w\<close>:
  \<^item> \<open>x < j\<^sub>0\<close> (verbatim PREFIX): @{thm [source] oper_tiling_row0_prefix};
  \<^item> \<open>x = j\<^sub>0\<close> (\<open>q=0\<close> block start, \<open>i\<^sub>1\<close>-agnostic):
    @{thm [source] oper_gen_tiling_row0_blockstart0};
  \<^item> \<open>x = j\<^sub>0 + q\<cdot>w + s\<close>, \<open>0 < s < w\<close> (block INTERIOR):
    @{thm [source] oper_gen_tiling_row0_interior};
  \<^item> \<open>x = j\<^sub>0 + q\<cdot>w\<close>, \<open>q \<ge> 1\<close> (block BOUNDARY): \<open>i\<^sub>1 = 1\<close> via
    @{thm [source] oper_gen_tiling_row0_boundary} (\<open>d\<^sub>0 > 0\<close> shift), \<open>i\<^sub>1 = 0\<close> via
    @{thm [source] oper_gen_tiling_row0_boundary_i0} (verbatim-periodic).
  Since \<open>idx1 N (Lng N-1) \<in> {0,1}\<close> (@{thm [source] idx1_def}), the boundary split
  is exhaustive.  Together these four bricks discharge the row-0 obligation
  feeding @{thm [source] operCA_tiling_cond} / @{thm [source] operCA_tiling_assemble}.\<close>

lemma operCA_tiling_row0:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and condA: "RedCondA N"
    and n1: "1 \<le> n"
    and hpn: "hasParent ((N::pairseq)[n]) 0 x"
  shows "entry ((N::pairseq)[n]) 0 (parent ((N::pairseq)[n]) 0 x) + 1
       = entry ((N::pairseq)[n]) 0 x"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?Nn = "(N::pairseq)[n]"
  have w0: "0 < ?w" using j0lt by linarith
  have lenNn: "Lng ?Nn = ?j0 + n * ?w" using operB_gen_LngM[OF L notzero hp j0lt] by simp
  have xlt: "x < Lng ?Nn" using hpn unfolding hasParent_def nextR_def nextrel0_def by auto
  show ?thesis
  proof (cases "x < ?j0")
    case True
    show ?thesis by (rule oper_tiling_row0_prefix[OF L notzero hp j0lt condA True hpn])
  next
    case False
    hence xge: "?j0 \<le> x" by simp
    let ?q = "(x - ?j0) div ?w"  let ?s = "(x - ?j0) mod ?w"
    have sw: "?s < ?w" using w0 by simp
    have xmj: "x - ?j0 < n * ?w" using xlt lenNn xge by linarith
    have qn: "?q < n" using less_mult_imp_div_less[OF xmj] .
    have dm: "?q * ?w + ?s = x - ?j0"
      using div_mult_mod_eq[of "x - ?j0" ?w] by (simp add: mult.commute)
    have xsplit: "x = ?j0 + ?q * ?w + ?s" using dm xge by linarith
    show ?thesis
    proof (cases "0 < ?s")
      case True
      \<comment> \<open>block INTERIOR\<close>
      have hpn': "hasParent ?Nn 0 (?j0 + ?q * ?w + ?s)" using hpn xsplit by simp
      have step: "entry ?Nn 0 (parent ?Nn 0 (?j0 + ?q * ?w + ?s)) + 1
                    = entry ?Nn 0 (?j0 + ?q * ?w + ?s)"
        by (rule oper_gen_tiling_row0_interior[OF L notzero hp j0lt condA qn True sw hpn'])
      show ?thesis using step xsplit by simp
    next
      case False
      hence s0: "?s = 0" by simp
      have xsplit0: "x = ?j0 + ?q * ?w" using xsplit s0 by simp
      show ?thesis
      proof (cases "?q = 0")
        case True
        \<comment> \<open>first block start \<open>x = j\<^sub>0\<close>\<close>
        have xj0: "x = ?j0" using xsplit0 True by simp
        have hpn0: "hasParent ?Nn 0 ?j0" using hpn xj0 by simp
        have step: "entry ?Nn 0 (parent ?Nn 0 ?j0) + 1 = entry ?Nn 0 ?j0"
          by (rule oper_gen_tiling_row0_blockstart0[OF L notzero hp j0lt condA n1 hpn0])
        show ?thesis using step xj0 by simp
      next
        case False
        hence q1: "1 \<le> ?q" by simp
        \<comment> \<open>block BOUNDARY \<open>x = j\<^sub>0 + q\<cdot>w\<close>, \<open>q \<ge> 1\<close>; split on \<open>i\<^sub>1\<close>\<close>
        have hpnB: "hasParent ?Nn 0 (?j0 + ?q * ?w)" using hpn xsplit0 by simp
        show ?thesis
        proof (cases "?i1 = 0")
          case True
          have step: "entry ?Nn 0 (parent ?Nn 0 (?j0 + ?q * ?w)) + 1
                        = entry ?Nn 0 (?j0 + ?q * ?w)"
            by (rule oper_gen_tiling_row0_boundary_i0[OF L notzero hp True j0lt condA q1 qn hpnB])
          show ?thesis using step xsplit0 by simp
        next
          case False
          have i1le: "?i1 \<le> 1" by (simp add: idx1_def)
          have i1: "?i1 = 1" using False i1le by linarith
          have step: "entry ?Nn 0 (parent ?Nn 0 (?j0 + ?q * ?w)) + 1
                        = entry ?Nn 0 (?j0 + ?q * ?w)"
            by (rule oper_gen_tiling_row0_boundary[OF L notzero hp i1 j0lt condA q1 qn hpnB])
          show ?thesis using step xsplit0 by simp
        qed
      qed
    qed
  qed
qed


text \<open>§6.7 oper-tiling brick (Front B, ROW 1): the WITHIN-BLOCK row-1 \<open>+1\<close> step
  REDUCED to the base reflection.  For a column \<open>j\<^sub>0 \<le> x\<close> of \<open>N[n]\<close> with a row-1
  parent, suppose the base reflection of its parent edge holds: there is a base
  column \<open>x'\<close> with \<open>hasParent N 1 x'\<close>, the row-1 value of \<open>x\<close> reads off the base
  (\<open>entry (N[n]) 1 x = entry N 1 x'\<close>, the \<open>d\<^sub>1 = 0\<close> verbatim periodicity, supplied
  by @{thm [source] operCA_tiling_entry1_base}), and the \<open>N[n]\<close>-parent reflects to
  the base row-1 parent (\<open>entry (N[n]) 1 (parent (N[n]) 1 x) = entry N 1 (parent N
  1 x')\<close>).  Then the row-1 \<open>+1\<close> step transfers from \<open>RedCondA N\<close> via
  @{thm [source] operCA_tiling_row1_plus1_transfer} (instantiated at the literal
  \<open>N[n]\<close>-parent, so \<open>pp\<close> is reflexive).  This is the structural glue: it isolates
  the remaining content (PENDING) to the parent CHARACTERIZATION supplying the
  base column \<open>x'\<close> and the two entry-match facts.  Empirically the reflection is
  0-fail (/tmp/within1_corr.py: 1890/1890 for verbatim-entry, base-hasParent and
  base-parent agreement).\<close>

lemma operCA_tiling_within1_via_reflect:
  assumes condA: "RedCondA N"
    and hpN: "hasParent N 1 x'"
    and ex: "entry ((N::pairseq)[n]) 1 x = entry N 1 x'"
    and ep: "entry ((N::pairseq)[n]) 1 (parent ((N::pairseq)[n]) 1 x)
               = entry N 1 (parent N 1 x')"
  shows "entry ((N::pairseq)[n]) 1 (parent ((N::pairseq)[n]) 1 x) + 1
       = entry ((N::pairseq)[n]) 1 x"
  by (rule operCA_tiling_row1_plus1_transfer[OF condA hpN ep ex refl])

end
