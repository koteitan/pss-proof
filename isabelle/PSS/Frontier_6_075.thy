theory Frontier_6_075
  imports Support_6_054
begin

text \<open>§6.7 oper-tiling brick (Front B): \<open>RedCondA (N[n])\<close> on the genuine TILING
  branch, assembled from the row-0 obligation \<open>row0CA\<close> (Front A; carried as an
  explicit hypothesis until it lands unconditionally) and the row-1 obligation
  @{thm [source] operCA_tiling_row1} (GREEN prefix + the within-block hypothesis
  \<open>within1\<close>).  The two row obligations feed @{thm [source] operCA_tiling_assemble}.
  Once \<open>row0CA\<close> and \<open>within1\<close> land this becomes the unconditional \<open>operCA\<close> brick
  discharging @{thm [source] m_6_7_standard_RedCondAB}.\<close>

lemma operCA_tiling_cond:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and condA: "RedCondA N"
    and row0CA: "\<And>x. hasParent ((N::pairseq)[n]) 0 x
                   \<Longrightarrow> entry ((N::pairseq)[n]) 0 (parent ((N::pairseq)[n]) 0 x) + 1
                        = entry ((N::pairseq)[n]) 0 x"
    and within1: "\<And>x. parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> x
                   \<Longrightarrow> hasParent ((N::pairseq)[n]) 1 x
                   \<Longrightarrow> entry ((N::pairseq)[n]) 1 (parent ((N::pairseq)[n]) 1 x) + 1
                        = entry ((N::pairseq)[n]) 1 x"
  shows "RedCondA ((N::pairseq)[n])"
proof (rule operCA_tiling_assemble)
  fix x assume "hasParent ((N::pairseq)[n]) 0 x"
  thus "entry ((N::pairseq)[n]) 0 (parent ((N::pairseq)[n]) 0 x) + 1
          = entry ((N::pairseq)[n]) 0 x" by (rule row0CA)
next
  fix x assume hpn1: "hasParent ((N::pairseq)[n]) 1 x"
  show "entry ((N::pairseq)[n]) 1 (parent ((N::pairseq)[n]) 1 x) + 1
          = entry ((N::pairseq)[n]) 1 x"
  proof (cases "x < parent N (idx1 N (Lng N - 1)) (Lng N - 1)")
    case True
    show ?thesis
      by (rule operCA_tiling_row1_prefix[OF L notzero hp j0lt condA True hpn1])
  next
    case False
    hence ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> x" by simp
    show ?thesis by (rule within1[OF ge hpn1])
  qed
qed



text \<open>§6.7 oper-tiling brick (Front A, ROW 0): the BOUNDARY \<open>+1\<close> step for the
  \<open>i\<^sub>1 = 0\<close> (d0zero) layout.  Here row 0 of \<open>N[n]\<close> is VERBATIM-periodic
  (\<open>d\<^sub>0 = 0\<close>), so the block-start \<open>x = j\<^sub>0 + q\<cdot>w\<close> (\<open>q \<ge> 1\<close>) reads
  \<open>e\<^sub>0(N[n],x) = e\<^sub>0(N,j\<^sub>0)\<close>, the row-0 MINIMUM of every block.  Any \<open>N[n]\<close>-parent
  \<open>p\<close> of \<open>x\<close> must therefore have row-0 value strictly below this minimum, which
  pins it into the verbatim PREFIX \<open>[0, j\<^sub>0)\<close> (every column \<open>\<ge> j\<^sub>0\<close> reads
  \<open>\<ge> e\<^sub>0(N,j\<^sub>0)\<close> by @{thm [source] parent_block_entry0_min}).  On the prefix the
  edge reflects verbatim to \<open>nextrel0 N p j\<^sub>0\<close> (the valley window above \<open>j\<^sub>0\<close> is
  automatic, since all block columns sit at or above the minimum), so
  \<open>parent N 0 j\<^sub>0 = p\<close> and \<open>RedCondA N\<close> at \<open>j\<^sub>0\<close> closes the \<open>+1\<close> step.  Empirically
  0-fail (/tmp/frontA_i0.py: 354/354 boundary cases, parent in prefix 354/354).\<close>

lemma oper_gen_tiling_row0_boundary_i0:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 0"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and condA: "RedCondA N"
    and q1: "1 \<le> q" and qn: "q < n"
    and hpn: "hasParent ((N::pairseq)[n]) 0
                (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                   + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
  shows "entry ((N::pairseq)[n]) 0 (parent ((N::pairseq)[n]) 0
                (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                   + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))) + 1
       = entry ((N::pairseq)[n]) 0
                (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                   + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?Nn = "(N::pairseq)[n]"
  let ?x = "?j0 + q * ?w"
  have w0: "0 < ?w" using j0lt by linarith
  have j0eq: "?j0 = parent N 0 ?j1" using i1z by simp
  have hp0: "hasParent N 0 ?j1" using hp i1z by simp
  have parR': "nextR N 0 (parent N 0 ?j1) ?j1"
    using hp0 unfolding hasParent_def parent_def by (rule theI')
  have parR: "nextR N 0 ?j0 ?j1" using parR' j0eq by simp
  have parR0: "nextrel0 N ?j0 ?j1" using parR by (simp add: nextR_def)
  \<comment> \<open>length of \<open>N[n]\<close> and the block reading (\<open>d\<^sub>0 = 0\<close>)\<close>
  have lenNn: "Lng ?Nn = ?j0 + n * ?w" using operB_gen_LngM[OF L notzero hp j0lt] by simp
  \<comment> \<open>verbatim prefix on row 0\<close>
  have pref: "\<And>y. y < ?j0 \<Longrightarrow> entry ?Nn 0 y = entry N 0 y"
    using operB_gen_entry_prefix[OF L notzero hp] by blast
  \<comment> \<open>row-0 reading at any block column \<open>j\<^sub>0 \<le> y < Lng(N[n])\<close>: \<open>e\<^sub>0(N, j\<^sub>0 + (y-j\<^sub>0) mod w)\<close>\<close>
  have blkread: "\<And>y. ?j0 \<le> y \<Longrightarrow> y < Lng ?Nn \<Longrightarrow> entry ?Nn 0 y = entry N 0 (?j0 + (y - ?j0) mod ?w)"
  proof -
    fix y assume yge: "?j0 \<le> y" and ylt: "y < Lng ?Nn"
    have ylt': "y < ?j0 + n * ?w" using ylt lenNn by simp
    show "entry ?Nn 0 y = entry N 0 (?j0 + (y - ?j0) mod ?w)"
      using oper_d0zero_entry0[OF L notzero hp i1z j0lt[unfolded j0eq] yge[unfolded j0eq] ylt'[unfolded j0eq]]
      unfolding j0eq by simp
  qed
  \<comment> \<open>the block-start \<open>x\<close> reads the minimum \<open>e\<^sub>0(N,j\<^sub>0)\<close>\<close>
  have xlt: "?x < Lng ?Nn"
  proof -
    have "Suc q \<le> n" using qn by simp
    hence "Suc q * ?w \<le> n * ?w" by (rule mult_le_mono1)
    hence "?j0 + q * ?w + ?w \<le> ?j0 + n * ?w" by simp
    hence "?x + ?w \<le> Lng ?Nn" using lenNn by simp
    thus ?thesis using w0 by linarith
  qed
  have xge: "?j0 \<le> ?x" by simp
  have xmod0: "(?x - ?j0) mod ?w = 0" by simp
  have ex: "entry ?Nn 0 ?x = entry N 0 ?j0" using blkread[OF xge xlt] xmod0 by simp
  \<comment> \<open>row-0 minimum: every column \<open>\<ge> j\<^sub>0\<close> reads \<open>\<ge> e\<^sub>0(N,j\<^sub>0)\<close>\<close>
  have ge_min: "\<And>y. ?j0 \<le> y \<Longrightarrow> y < Lng ?Nn \<Longrightarrow> entry N 0 ?j0 \<le> entry ?Nn 0 y"
  proof -
    fix y assume yge: "?j0 \<le> y" and ylt: "y < Lng ?Nn"
    have mw: "(y - ?j0) mod ?w < ?w" using w0 by simp
    have "entry N 0 ?j0 \<le> entry N 0 (?j0 + (y - ?j0) mod ?w)"
      using parent_block_entry0_min(1)[OF parR0[unfolded j0eq] mw[unfolded j0eq]]
      unfolding j0eq by simp
    thus "entry N 0 ?j0 \<le> entry ?Nn 0 y" using blkread[OF yge ylt] by simp
  qed
  \<comment> \<open>obtain the unique \<open>N[n]\<close>-parent \<open>p\<close> of \<open>x\<close>\<close>
  have exu: "\<exists>!p. nextrel0 ?Nn p ?x"
    using hpn unfolding hasParent_def nextR_def by simp
  obtain p where pP: "nextrel0 ?Nn p ?x"
    and pU: "\<And>p'. nextrel0 ?Nn p' ?x \<Longrightarrow> p' = p"
    using exu by blast
  have pjx: "p < ?x" using pP by (simp add: nextrel0_def)
  have pval0: "entry ?Nn 0 p < entry ?Nn 0 ?x" using pP by (simp add: nextrel0_def)
  have valley: "\<And>j. p < j \<Longrightarrow> j < ?x \<Longrightarrow> entry ?Nn 0 ?x \<le> entry ?Nn 0 j"
    using pP by (simp add: nextrel0_def)
  \<comment> \<open>\<open>p < j\<^sub>0\<close>: \<open>p\<close>'s row-0 value is strictly below the block minimum\<close>
  have pj0: "p < ?j0"
  proof (rule ccontr)
    assume "\<not> p < ?j0"
    hence pge: "?j0 \<le> p" by simp
    have pltN: "p < Lng ?Nn" using pjx xlt by linarith
    have "entry N 0 ?j0 \<le> entry ?Nn 0 p" using ge_min[OF pge pltN] .
    thus False using pval0 ex by simp
  qed
  \<comment> \<open>length bounds\<close>
  have j0Nn: "?j0 < Lng ?Nn" using xge xlt by linarith
  \<comment> \<open>the edge reflects to \<open>nextrel0 N p j\<^sub>0\<close>\<close>
  have stepN: "nextrel0 N p ?j0"
    unfolding nextrel0_def
  proof (intro conjI allI impI)
    show "p < Lng N" using pj0 j0lt by linarith
    show "?j0 < Lng N" using j0lt by linarith
    show "p < ?j0" by (rule pj0)
    have "entry ?Nn 0 p < entry ?Nn 0 ?x" by (rule pval0)
    thus "entry N 0 p < entry N 0 ?j0" using pref[OF pj0] ex by simp
  next
    fix j assume jj: "p < j \<and> j < ?j0"
    hence jp: "p < j" and jj0: "j < ?j0" by simp_all
    have jx: "j < ?x" using jj0 by simp
    have "entry ?Nn 0 ?x \<le> entry ?Nn 0 j" using valley[OF jp jx] .
    thus "entry N 0 ?j0 \<le> entry N 0 j" using pref[OF jj0] ex by simp
  qed
  \<comment> \<open>uniqueness of the \<open>N\<close>-parent transfers back\<close>
  have uniqN: "\<And>p'. nextrel0 N p' ?j0 \<Longrightarrow> p' = p"
  proof -
    fix p' assume Hp': "nextrel0 N p' ?j0"
    have p'j0: "p' < ?j0" using Hp' by (simp add: nextrel0_def)
    have stepNn: "nextrel0 ?Nn p' ?x"
      unfolding nextrel0_def
    proof (intro conjI allI impI)
      show "p' < Lng ?Nn" using p'j0 j0Nn by linarith
      show "?x < Lng ?Nn" by (rule xlt)
      show "p' < ?x" using p'j0 xge by linarith
      have "entry N 0 p' < entry N 0 ?j0" using Hp' by (simp add: nextrel0_def)
      thus "entry ?Nn 0 p' < entry ?Nn 0 ?x" using pref[OF p'j0] ex by simp
    next
      fix j assume jj: "p' < j \<and> j < ?x"
      hence jp: "p' < j" and jx: "j < ?x" by simp_all
      show "entry ?Nn 0 ?x \<le> entry ?Nn 0 j"
      proof (cases "j < ?j0")
        case True
        have "entry N 0 ?j0 \<le> entry N 0 j" using Hp' jp True by (simp add: nextrel0_def)
        thus ?thesis using pref[OF True] ex by simp
      next
        case False
        hence jge: "?j0 \<le> j" by simp
        have jltN: "j < Lng ?Nn" using jx xlt by linarith
        have "entry N 0 ?j0 \<le> entry ?Nn 0 j" using ge_min[OF jge jltN] .
        thus ?thesis using ex by simp
      qed
    qed
    show "p' = p" using pU[OF stepNn] .
  qed
  \<comment> \<open>recast in \<open>nextR \<cdot> 0\<close> form and conclude \<open>parent N 0 j\<^sub>0 = p\<close>, \<open>parent (N[n]) 0 x = p\<close>\<close>
  have stepNR: "nextR N 0 p ?j0" using stepN by (simp add: nextR_def)
  have uniqNR: "\<And>p'. nextR N 0 p' ?j0 \<Longrightarrow> p' = p"
    using uniqN by (simp add: nextR_def)
  have pPR: "nextR ?Nn 0 p ?x" using pP by (simp add: nextR_def)
  have pUR: "\<And>p'. nextR ?Nn 0 p' ?x \<Longrightarrow> p' = p"
    using pU by (simp add: nextR_def)
  have hpNj0: "hasParent N 0 ?j0"
    unfolding hasParent_def using stepNR uniqNR by blast
  have parN: "parent N 0 ?j0 = p"
    by (rule parent0_eqI[OF stepNR uniqNR])
  have parNn: "parent ?Nn 0 ?x = p"
    by (rule parent0_eqI[OF pPR pUR])
  \<comment> \<open>RedCondA N closes the \<open>+1\<close> step at \<open>j\<^sub>0\<close>; row 0 is verbatim there\<close>
  have baseN: "entry N 0 (parent N 0 ?j0) + 1 = entry N 0 ?j0"
    using condA[unfolded RedCondA_def, rule_format, of 0 ?j0] hpNj0 by simp
  have "entry ?Nn 0 (parent ?Nn 0 ?x) + 1 = entry N 0 p + 1"
    using parNn pref[OF pj0] by simp
  also have "\<dots> = entry N 0 ?j0" using baseN parN by simp
  also have "\<dots> = entry ?Nn 0 ?x" using ex by simp
  finally show ?thesis .
qed

end
