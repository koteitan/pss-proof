theory Frontier_6_074
  imports Support_6_053
begin

text \<open>§6.7 oper-tiling brick (Front B, ROW 1): the \<open>+1\<close> TRANSFER for row 1.  Since
  row-1 entries of \<open>N[n]\<close> are verbatim at the period base (\<open>d\<^sub>1=0\<close>), a row-1
  parent edge \<open>nextR (N[n]) 1 p x\<close> whose base columns \<open>p',x'\<close> form a row-1 parent
  edge in \<open>N\<close> (i.e. \<open>parent N 1 x' = p'\<close>, \<open>hasParent N 1 x'\<close>) inherits the
  reducedness \<open>+1\<close> relation from \<open>RedCondA N\<close>, provided the row-1 entries match:
  \<open>entry (N[n]) 1 p = entry N 1 p'\<close> and \<open>entry (N[n]) 1 x = entry N 1 x'\<close>.
  This is the assembly-facing reduction of the row-1 obligation to \<open>RedCondA N\<close>;
  the remaining content (PENDING) is the parent CHARACTERIZATION that supplies
  the base correspondence \<open>(p',x')\<close> with matching entries — the row-1
  \<open>nextrel1\<close>-confinement, which mirrors the row-0 \<open>oper_d1pos_le0_confined\<close>
  development per period block.\<close>

lemma operCA_tiling_row1_plus1_transfer:
  assumes condA: "RedCondA N"
    and hpN: "hasParent N 1 x'"
    and ep: "entry ((N::pairseq)[n]) 1 p = entry N 1 (parent N 1 x')"
    and ex: "entry ((N::pairseq)[n]) 1 x = entry N 1 x'"
    and pp: "p = parent ((N::pairseq)[n]) 1 x"
  shows "entry ((N::pairseq)[n]) 1 (parent ((N::pairseq)[n]) 1 x) + 1
          = entry ((N::pairseq)[n]) 1 x"
proof -
  have base: "entry N 1 (parent N 1 x') + 1 = entry N 1 x'"
    using condA hpN unfolding RedCondA_def by simp
  have "entry ((N::pairseq)[n]) 1 (parent ((N::pairseq)[n]) 1 x) + 1
          = entry N 1 (parent N 1 x') + 1" using ep pp by simp
  also have "\<dots> = entry N 1 x'" using base .
  also have "\<dots> = entry ((N::pairseq)[n]) 1 x" using ex by simp
  finally show ?thesis .
qed


text \<open>§6.7 oper-tiling brick (Front A, ROW 0): \<open>i\<^sub>1\<close>-AGNOSTIC STRICT period floor.
  For a NON-trivial interior offset \<open>0 < s < w\<close> the row-0 base value strictly
  exceeds the period start: \<open>entry N 0 j\<^sub>0 < entry N 0 (j\<^sub>0 + s)\<close>.  Mirrors
  @{thm [source] oper_d1pos_strict_period_floor} but drops the \<open>idx1 = 1\<close>
  assumption, deriving \<open>leR N 0 j\<^sub>0 j\<^sub>1\<close> directly from the (any-row) parent
  relation @{thm [source] poper_nextR_imp_le0}.  Empirically 0-fail
  (/tmp/frontA_floor.py: i1=0 4/4, i1=1 31/31).\<close>

lemma oper_gen_strict_period_floor:
  fixes N :: pairseq
  assumes hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and s0: "0 < s"
    and sle: "s \<le> Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)"
  shows "entry N 0 (parent N (idx1 N (Lng N - 1)) (Lng N - 1))
       < entry N 0 (parent N (idx1 N (Lng N - 1)) (Lng N - 1) + s)"
proof -
  let ?i1 = "idx1 N (Lng N - 1)"  let ?j0 = "parent N ?i1 (Lng N - 1)"
  let ?j1 = "Lng N - 1"
  have L: "1 < Lng N" using j0lt by linarith
  have NT: "N \<in> T_PS" using L by (cases N) (auto simp: T_PS_def)
  have parR: "nextR N ?i1 ?j0 ?j1"
    using hp unfolding hasParent_def parent_def by (rule theI')
  have le0: "leR N 0 ?j0 ?j1" using poper_nextR_imp_le0[OF parR] by simp
  have mono: "monoT (seg N ?j0 ?j1)"
    by (rule m_6_2_mono_ancestor_slice[OF NT j0lt le0])
  have segT: "seg N ?j0 ?j1 \<in> T_PS" using j0lt by (auto simp: T_PS_def seg_def)
  have leR0: "leR (seg N ?j0 ?j1) 0 0 (Lng (seg N ?j0 ?j1) - 1)"
    using mono by (simp add: monoT_def)
  have slt: "s < Lng (seg N ?j0 ?j1)" using sle j0lt by simp
  have strictseg: "entry (seg N ?j0 ?j1) 0 0 < entry (seg N ?j0 ?j1) 0 s"
    using m_6_2_multi_crit_23[OF segT] leR0 s0 slt by blast
  have z0: "0 < Lng (seg N ?j0 ?j1)" using j0lt by simp
  have e0: "entry (seg N ?j0 ?j1) 0 0 = entry N 0 ?j0"
    using entry_seg[OF z0] by simp
  have es: "entry (seg N ?j0 ?j1) 0 s = entry N 0 (?j0 + s)"
    using entry_seg[OF slt] by simp
  show ?thesis using strictseg e0 es by simp
qed


text \<open>§6.7 oper-tiling brick (Front A, ROW 0): the INTERIOR \<open>+1\<close> step.  For an
  interior column \<open>x = j\<^sub>0 + q\<cdot>w + s\<close> (\<open>0 < s < w\<close>, \<open>q < n\<close>) of \<open>N[n]\<close> that has a
  row-0 parent, the parent edge inherits the \<open>+1\<close> from \<open>RedCondA N\<close>.

  Structure: the \<open>N[n]\<close>-parent \<open>p\<close> of \<open>x\<close> CANNOT lie below block-\<open>q\<close>'s start
  \<open>B = j\<^sub>0 + q\<cdot>w\<close> — \<open>B\<close> carries the block floor \<open>e\<^sub>0(N,j\<^sub>0)+q\<cdot>d\<^sub>0\<close>, which is
  STRICTLY below \<open>e\<^sub>0(N[n],x) = e\<^sub>0(N,j\<^sub>0+s)+q\<cdot>d\<^sub>0\<close> (the strict period floor, since
  \<open>s>0\<close>), so a \<open>B\<close> inside the valley \<open>(p,x)\<close> would break the running-min.  Hence
  \<open>B \<le> p\<close>, both endpoints (and the valley window) sit in block \<open>q\<close>, and the
  uniform \<open>q\<cdot>d\<^sub>0\<close> shift cancels: \<open>nextrel0 (N[n]) p x\<close> reflects down to
  \<open>nextrel0 N (j\<^sub>0+(p-B)) (j\<^sub>0+s)\<close>, so \<open>parent N 0 (j\<^sub>0+s) = p-B\<close>'s offset and
  \<open>RedCondA N\<close> closes the step.  Empirically 0-fail (/tmp/frontA_ids.py: 210/210,
  /tmp/frontA_revconf.py: in-block 210/210).\<close>

lemma oper_gen_tiling_row0_interior:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and condA: "RedCondA N"
    and qn: "q < n"
    and s0: "0 < s"
    and sw: "s < Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and hpn: "hasParent ((N::pairseq)[n]) 0
                (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                   + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)) + s)"
  shows "entry ((N::pairseq)[n]) 0 (parent ((N::pairseq)[n]) 0
                (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                   + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)) + s)) + 1
       = entry ((N::pairseq)[n]) 0
                (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                   + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)) + s)"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?d0 = "if 0 < ?i1 then entry N 0 ?j1 - entry N 0 ?j0 else 0"
  let ?Nn = "(N::pairseq)[n]"
  let ?B = "?j0 + q * ?w"  let ?x = "?B + s"  let ?u = "?j0 + s"
  have w0: "0 < ?w" using j0lt by linarith
  \<comment> \<open>block-\<open>q\<close> row-0 reading at any offset \<open>t < w\<close>\<close>
  have blkq: "\<And>t. t < ?w \<Longrightarrow> entry ?Nn 0 (?B + t) = entry N 0 (?j0 + t) + q * ?d0"
  proof -
    fix t assume t: "t < ?w"
    have "entry ?Nn 0 (?j0 + q * ?w + t) = entry N 0 (?j0 + t) + q * ?d0"
      by (rule oper_gen_block_entry0[OF L notzero hp j0lt qn t])
    thus "entry ?Nn 0 (?B + t) = entry N 0 (?j0 + t) + q * ?d0" by (simp add: add.assoc)
  qed
  have eBx: "entry ?Nn 0 ?x = entry N 0 ?u + q * ?d0" using blkq[OF sw] by (simp add: add.assoc)
  have eBB: "entry ?Nn 0 ?B = entry N 0 ?j0 + q * ?d0" using blkq[of 0] w0 by simp
  \<comment> \<open>obtain the unique \<open>N[n]\<close>-parent \<open>p\<close> of \<open>x\<close>\<close>
  have exu: "\<exists>!p. nextrel0 ?Nn p ?x"
    using hpn unfolding hasParent_def nextR_def by simp
  obtain p where pP: "nextrel0 ?Nn p ?x"
    and pU: "\<And>p'. nextrel0 ?Nn p' ?x \<Longrightarrow> p' = p"
    using exu by blast
  have pjx: "p < ?x" using pP by (simp add: nextrel0_def)
  have valley: "\<And>j. p < j \<Longrightarrow> j < ?x \<Longrightarrow> entry ?Nn 0 ?x \<le> entry ?Nn 0 j"
    using pP by (simp add: nextrel0_def)
  \<comment> \<open>the strict floor: \<open>e\<^sub>0(N[n],B) < e\<^sub>0(N[n],x)\<close>\<close>
  have sfloor: "entry N 0 ?j0 < entry N 0 ?u"
    by (rule oper_gen_strict_period_floor[OF hp j0lt s0]) (use sw in simp)
  have eBlt: "entry ?Nn 0 ?B < entry ?Nn 0 ?x" using eBB eBx sfloor by simp
  \<comment> \<open>so \<open>B \<le> p\<close>: a strictly-lower \<open>B\<close> inside the valley would contradict it\<close>
  have Bp: "?B \<le> p"
  proof (rule ccontr)
    assume "\<not> ?B \<le> p"
    hence pB: "p < ?B" by simp
    have Bx: "?B < ?x" using s0 by simp
    have "entry ?Nn 0 ?x \<le> entry ?Nn 0 ?B" using valley[OF pB Bx] .
    thus False using eBlt by simp
  qed
  \<comment> \<open>both endpoints in block \<open>q\<close>: \<open>p = B + (p-B)\<close> with \<open>p - B < s\<close>\<close>
  have pxB: "p - ?B < s" using pjx Bp by linarith
  have psw: "p - ?B < ?w" using pxB sw by linarith
  have psplit: "p = ?B + (p - ?B)" using Bp by simp
  have eP: "entry ?Nn 0 p = entry N 0 (?j0 + (p - ?B)) + q * ?d0"
    using blkq[OF psw] psplit by simp
  \<comment> \<open>down-transfer: \<open>nextrel0 N (j\<^sub>0+(p-B)) u\<close> (shift cancels)\<close>
  let ?pn = "?j0 + (p - ?B)"
  have ult: "?u < Lng N" using sw j0lt by linarith
  have pnlt: "?pn < Lng N" using psw j0lt by linarith
  have stepN: "nextrel0 N ?pn ?u"
    unfolding nextrel0_def
  proof (intro conjI allI impI)
    show "?pn < Lng N" by (rule pnlt)
    show "?u < Lng N" by (rule ult)
    show "?pn < ?u" using pxB by simp
    have "entry ?Nn 0 p < entry ?Nn 0 ?x" using pP by (simp add: nextrel0_def)
    thus "entry N 0 ?pn < entry N 0 ?u" using eP eBx by simp
  next
    fix j assume jj: "?pn < j \<and> j < ?u"
    hence jlo: "?pn < j" and jhi: "j < ?u" by simp_all
    \<comment> \<open>map \<open>j = j\<^sub>0 + t\<close> back up to \<open>B + t\<close> in block \<open>q\<close>\<close>
    have jge: "?j0 \<le> j" using jlo by linarith
    let ?t = "j - ?j0"
    have tsw: "?t < ?w" using jhi jge sw by linarith
    have jt: "j = ?j0 + ?t" using jge by simp
    have Btlo: "p < ?B + ?t" using jlo jge psplit by linarith
    have Bthi: "?B + ?t < ?x" using jhi jge by linarith
    have "entry ?Nn 0 ?x \<le> entry ?Nn 0 (?B + ?t)" using valley[OF Btlo Bthi] .
    hence "entry N 0 ?u + q * ?d0 \<le> entry N 0 (?j0 + ?t) + q * ?d0"
      using eBx blkq[OF tsw] by simp
    thus "entry N 0 ?u \<le> entry N 0 j" using jt by simp
  qed
  \<comment> \<open>uniqueness of the \<open>N\<close>-parent transfers up, so \<open>parent N 0 u = pn\<close>\<close>
  have uniqN: "\<And>p'. nextrel0 N p' ?u \<Longrightarrow> p' = ?pn"
  proof -
    fix p' assume Hp': "nextrel0 N p' ?u"
    have p'u: "p' < ?u" using Hp' by (simp add: nextrel0_def)
    have p'lt: "p' < Lng N" using Hp' by (simp add: nextrel0_def)
    \<comment> \<open>lift \<open>p'\<close> into block \<open>q\<close> as \<open>B + (p' - j\<^sub>0)\<close>; it must be \<open>\<ge> j\<^sub>0\<close>\<close>
    have p'j0: "?j0 \<le> p'"
    proof (rule ccontr)
      assume "\<not> ?j0 \<le> p'"
      hence p'lo: "p' < ?j0" by simp
      \<comment> \<open>row-0 valley in \<open>N\<close>: \<open>j\<^sub>0\<close> lies in \<open>(p',u)\<close> and the floor at \<open>j\<^sub>0\<close> is below \<open>u\<close>\<close>
      have j0lo: "p' < ?j0" by (rule p'lo)
      have j0hi: "?j0 < ?u" using s0 by simp
      have "entry N 0 ?u \<le> entry N 0 ?j0" using Hp' j0lo j0hi by (simp add: nextrel0_def)
      thus False using sfloor by simp
    qed
    let ?t' = "p' - ?j0"
    have t'sw: "?t' < ?w" using p'u p'j0 sw by linarith
    have p't: "p' = ?j0 + ?t'" using p'j0 by simp
    \<comment> \<open>transfer \<open>nextrel0 N p' u\<close> up to \<open>nextrel0 (N[n]) (B + t') x\<close>\<close>
    let ?P' = "?B + ?t'"
    have LngNn: "Lng ?Nn = ?j0 + n * ?w"
      using operB_gen_LngM[OF L notzero hp j0lt] by simp
    obtain w where wdef: "?w = w" by blast
    have Bwub: "?B + ?w \<le> Lng ?Nn"
    proof -
      have "Suc q \<le> n" using qn by simp
      hence "Suc q * w \<le> n * w" by (rule mult_le_mono1)
      hence "?j0 + q * w + w \<le> ?j0 + n * w" by simp
      thus ?thesis using wdef LngNn by simp
    qed
    have P'lt: "?P' < Lng ?Nn"
    proof -
      have "?B + ?t' < ?B + ?w" by (rule add_strict_left_mono[OF t'sw])
      thus ?thesis using Bwub by linarith
    qed
    have xlt: "?x < Lng ?Nn"
    proof -
      have "?B + s < ?B + ?w" by (rule add_strict_left_mono[OF sw])
      thus ?thesis using Bwub by linarith
    qed
    have eP': "entry ?Nn 0 ?P' = entry N 0 p' + q * ?d0"
      using blkq[OF t'sw] p't by simp
    have stepNn: "nextrel0 ?Nn ?P' ?x"
      unfolding nextrel0_def
    proof (intro conjI allI impI)
      show "?P' < Lng ?Nn" by (rule P'lt)
      show "?x < Lng ?Nn" by (rule xlt)
      show "?P' < ?x" using p'u p'j0 by linarith
      have "entry N 0 p' < entry N 0 ?u" using Hp' by (simp add: nextrel0_def)
      thus "entry ?Nn 0 ?P' < entry ?Nn 0 ?x" using eP' eBx by simp
    next
      fix j assume jj: "?P' < j \<and> j < ?x"
      hence jlo: "?P' < j" and jhi: "j < ?x" by simp_all
      have jge: "?B \<le> j" using jlo by linarith
      let ?t = "j - ?B"
      have tsw: "?t < ?w" using jhi jge sw by linarith
      have jt: "j = ?B + ?t" using jge by simp
      have lo': "?j0 + ?t' < ?j0 + ?t" using jlo jge p't by linarith
      hence tlo: "?t' < ?t" by simp
      have thi: "?j0 + ?t < ?u" using jhi jge by linarith
      have "entry N 0 ?u \<le> entry N 0 (?j0 + ?t)"
        using Hp' tlo thi p't by (simp add: nextrel0_def)
      hence "entry N 0 ?u + q * ?d0 \<le> entry N 0 (?j0 + ?t) + q * ?d0" by simp
      thus "entry ?Nn 0 ?x \<le> entry ?Nn 0 j" using eBx blkq[OF tsw] jt by simp
    qed
    have "?P' = p" using pU[OF stepNn] .
    hence "?B + ?t' = ?B + (p - ?B)" using psplit by simp
    hence "?t' = p - ?B" by simp
    thus "p' = ?pn" using p't by simp
  qed
  \<comment> \<open>recast in \<open>nextR \<cdot> 0\<close> form\<close>
  have stepNR: "nextR N 0 ?pn ?u" using stepN by (simp add: nextR_def)
  have uniqNR: "\<And>p'. nextR N 0 p' ?u \<Longrightarrow> p' = ?pn"
    using uniqN by (simp add: nextR_def)
  have pPR: "nextR ?Nn 0 p ?x" using pP by (simp add: nextR_def)
  have pUR: "\<And>p'. nextR ?Nn 0 p' ?x \<Longrightarrow> p' = p"
    using pU by (simp add: nextR_def)
  have hpN: "hasParent N 0 ?u"
    unfolding hasParent_def using stepNR uniqNR by blast
  have exu1N: "\<exists>!q. nextR N 0 q ?u" using stepNR uniqNR by blast
  have parN: "parent N 0 ?u = ?pn"
    unfolding parent_def[of N 0 ?u] using the1_equality[OF exu1N stepNR] .
  have exu1Nn: "\<exists>!q. nextR ?Nn 0 q ?x" using pPR pUR by blast
  have parNn: "parent ?Nn 0 ?x = p"
    unfolding parent_def[of ?Nn 0 ?x] using the1_equality[OF exu1Nn pPR] .
  \<comment> \<open>RedCondA N closes the \<open>+1\<close> step (shift cancels via \<open>eP\<close>, \<open>eBx\<close>)\<close>
  have baseN: "entry N 0 (parent N 0 ?u) + 1 = entry N 0 ?u"
    using condA[unfolded RedCondA_def, rule_format, of 0 ?u] hpN by simp
  have "entry ?Nn 0 (parent ?Nn 0 ?x) + 1 = entry N 0 ?pn + q * ?d0 + 1"
    using parNn eP by simp
  also have "\<dots> = (entry N 0 ?pn + 1) + q * ?d0" by simp
  also have "\<dots> = entry N 0 ?u + q * ?d0" using baseN parN by simp
  also have "\<dots> = entry ?Nn 0 ?x" using eBx by simp
  finally show ?thesis by (simp add: add.assoc)
qed



text \<open>§6.7 oper-tiling brick (Front B, ROW 1): row-1 \<open>RedCondA\<close> on the verbatim
  PREFIX.  For a column \<open>x < j\<^sub>0\<close> of \<open>N[n]\<close> that HAS a row-1 parent, both the
  parent \<open>p < x < j\<^sub>0\<close> and the whole \<open>nextrel1\<close>-window (\<open>le0\<close>-reachable predecessors
  of \<open>x\<close>, which are \<open>\<le> x \<le> c\<close>) lie in the verbatim prefix \<open>[0,c]\<close> with \<open>c = x\<close>.
  The list-level agreement \<open>(N[n]) ! j = N ! j\<close> for \<open>j < j\<^sub>0\<close>
  (@{thm [source] oper_gen_nth_prefix}) lets @{thm [source] nextrel1_prefix_imp}
  transfer the step both ways, so \<open>parent (N[n]) 1 x = parent N 1 x\<close> and
  \<open>hasParent N 1 x\<close>; \<open>RedCondA N\<close> closes the \<open>+1\<close> step.\<close>

lemma operCA_tiling_row1_prefix:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and condA: "RedCondA N"
    and xj0: "x < parent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and hpn: "hasParent ((N::pairseq)[n]) 1 x"
  shows "entry ((N::pairseq)[n]) 1 (parent ((N::pairseq)[n]) 1 x) + 1
       = entry ((N::pairseq)[n]) 1 x"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?Nn = "(N::pairseq)[n]"
  \<comment> \<open>list-level prefix agreement: \<open>(N[n]) ! j = N ! j\<close> for every \<open>j < j\<^sub>0\<close>\<close>
  have nthpref: "\<And>j. j < ?j0 \<Longrightarrow> ?Nn ! j = N ! j"
    using oper_gen_nth_prefix[OF L notzero hp] by blast
  \<comment> \<open>length bounds: \<open>j\<^sub>0 \<le> Lng N\<close>, \<open>j\<^sub>0 \<le> Lng (N[n])\<close>\<close>
  have j0LN: "?j0 < Lng N" using j0lt by linarith
  have LngNn: "Lng ?Nn = ?j0 + n * (?j1 - ?j0)"
    by (rule operB_gen_LngM[OF L notzero hp j0lt])
  \<comment> \<open>obtain the unique \<open>N[n]\<close>-parent \<open>p\<close>\<close>
  have exu: "\<exists>!q. nextrel1 ?Nn q x"
    using hpn unfolding hasParent_def nextR_def by simp
  obtain p where pP: "nextrel1 ?Nn p x"
    and pU: "\<And>p'. nextrel1 ?Nn p' x \<Longrightarrow> p' = p"
    using exu by blast
  have px: "p < x" using pP by (simp add: nextrel1_def)
  have xLNn: "x < Lng ?Nn" using pP by (simp add: nextrel1_def)
  have xj0': "x < ?j0" using xj0 by simp
  have xLN: "x < Lng N" using xj0' j0LN by linarith
  have pj0: "p < ?j0" using px xj0' by linarith
  \<comment> \<open>both endpoints are \<open>\<le> x\<close>; with \<open>c = x\<close> they sit in the agreement region\<close>
  have cLNn: "x < Lng ?Nn" by (rule xLNn)
  have cLN: "x < Lng N" by (rule xLN)
  \<comment> \<open>agreement on \<open>[0,x]\<close> in BOTH directions (since \<open>x < j\<^sub>0\<close>)\<close>
  have agNn: "\<And>j. j \<le> x \<Longrightarrow> ?Nn ! j = N ! j"
  proof -
    fix j assume "j \<le> x"
    hence "j < ?j0" using xj0' by linarith
    thus "?Nn ! j = N ! j" by (rule nthpref)
  qed
  have agN: "\<And>j. j \<le> x \<Longrightarrow> N ! j = ?Nn ! j"
    using agNn by simp
  \<comment> \<open>transfer the step to \<open>N\<close>\<close>
  have stepN: "nextrel1 N p x"
    by (rule nextrel1_prefix_imp[OF agNn cLNn cLN _ _ pP]) (use px in simp_all)
  \<comment> \<open>uniqueness of the \<open>N\<close>-parent transfers back\<close>
  have uniqN: "\<And>p'. nextrel1 N p' x \<Longrightarrow> p' = p"
  proof -
    fix p' assume Hp': "nextrel1 N p' x"
    have p'x: "p' < x" using Hp' by (simp add: nextrel1_def)
    have stepNn: "nextrel1 ?Nn p' x"
      by (rule nextrel1_prefix_imp[OF agN cLN cLNn _ _ Hp']) (use p'x in simp_all)
    show "p' = p" using pU[OF stepNn] .
  qed
  \<comment> \<open>recast in \<open>nextR \<cdot> 1\<close> form (matches \<open>parent_def\<close> / \<open>hasParent_def\<close>)\<close>
  have stepNR: "nextR N 1 p x" using stepN by (simp add: nextR_def)
  have uniqNR: "\<And>p'. nextR N 1 p' x \<Longrightarrow> p' = p"
    using uniqN by (simp add: nextR_def)
  have pPR: "nextR ?Nn 1 p x" using pP by (simp add: nextR_def)
  have pUR: "\<And>p'. nextR ?Nn 1 p' x \<Longrightarrow> p' = p"
    using pU by (simp add: nextR_def)
  have hpN1: "hasParent N 1 x"
    unfolding hasParent_def using stepNR uniqNR by blast
  have parN: "parent N 1 x = p"
    unfolding parent_def
    by (rule the_equality[where P="\<lambda>q. nextR N 1 q x", OF stepNR uniqNR])
  have parNn: "parent ?Nn 1 x = p"
    unfolding parent_def
    by (rule the_equality[where P="\<lambda>q. nextR ?Nn 1 q x", OF pPR pUR])
  \<comment> \<open>RedCondA N closes the \<open>+1\<close> step; entries are verbatim on the prefix\<close>
  have baseN: "entry N 1 (parent N 1 x) + 1 = entry N 1 x"
    using condA[unfolded RedCondA_def, rule_format, of 1 x] hpN1 by simp
  have epref: "\<And>j. j < ?j0 \<Longrightarrow> entry ?Nn 1 j = entry N 1 j"
    using nthpref by (simp add: entry_def)
  show ?thesis
    using baseN parN parNn epref[OF pj0] epref[OF xj0'] by simp
qed


text \<open>§6.7 oper-tiling brick (Front B): ASSEMBLY of \<open>RedCondA (N[n])\<close> from the two
  per-row obligations.  \<open>RedCondA M\<close> quantifies \<open>i \<le> 1\<close> over every \<open>j1'\<close> with a
  row-\<open>i\<close> parent; since \<open>i \<in> {0,1}\<close>, it splits cleanly into the row-0 obligation
  \<open>row0\<close> and the row-1 obligation \<open>row1\<close>, each ranging over all columns of \<open>N[n]\<close>.
  This is the unconditional combinator: once both row obligations are GREEN
  (row 0 = prefix @{thm [source] oper_tiling_row0_prefix} + within/boundary; row 1
  = prefix @{thm [source] operCA_tiling_row1_prefix} + within/boundary), it yields
  \<open>RedCondA (N[n])\<close> and hence discharges the \<open>operCA\<close> residual.\<close>

lemma operCA_tiling_assemble:
  assumes row0: "\<And>x. hasParent ((N::pairseq)[n]) 0 x
                   \<Longrightarrow> entry ((N::pairseq)[n]) 0 (parent ((N::pairseq)[n]) 0 x) + 1
                        = entry ((N::pairseq)[n]) 0 x"
    and row1: "\<And>x. hasParent ((N::pairseq)[n]) 1 x
                   \<Longrightarrow> entry ((N::pairseq)[n]) 1 (parent ((N::pairseq)[n]) 1 x) + 1
                        = entry ((N::pairseq)[n]) 1 x"
  shows "RedCondA ((N::pairseq)[n])"
  unfolding RedCondA_def
proof (intro allI impI)
  fix i j1' assume i1: "i \<le> 1" and hpn: "hasParent ((N::pairseq)[n]) i j1'"
  show "entry ((N::pairseq)[n]) i (parent ((N::pairseq)[n]) i j1') + 1
          = entry ((N::pairseq)[n]) i j1'"
  proof (cases "i = 0")
    case True
    thus ?thesis using row0[OF hpn[unfolded True]] by simp
  next
    case False
    hence "i = 1" using i1 by simp
    thus ?thesis using row1[OF hpn[unfolded \<open>i = 1\<close>]] by simp
  qed
qed


text \<open>§6.7 oper-tiling brick (Front A, ROW 0): CORRECTED last-index row-0 parent
  EXISTENCE.  For \<open>N\<close> with a row-\<open>i\<^sub>1\<close> parent of the last index \<open>j\<^sub>1 = Lng N-1\<close>,
  \<open>i\<^sub>1 = 1\<close> and \<open>j\<^sub>0 = parent N 1 j\<^sub>1 < j\<^sub>1\<close>, the active slice \<open>seg N j\<^sub>0 j\<^sub>1\<close> is
  \<open>monoT\<close> (@{thm [source] m_6_2_mono_ancestor_slice}), so row 0 STRICTLY increases
  across it: \<open>entry N 0 j\<^sub>0 < entry N 0 j\<^sub>1\<close>.  Hence \<open>j\<^sub>1\<close> HAS a row-0 parent
  (@{thm [source] m_5_1_parent_exists_1}; uniqueness from
  @{thm [source] idxsum_parent0_unique}).  NOTE: the row-0 parent is NOT in
  general the immediate predecessor \<open>j\<^sub>1-1\<close> — empirically (/tmp/d0_check.py,
  /tmp/bnd_char.py) it is \<open>parent N 0 j\<^sub>1 \<in> [j\<^sub>0, j\<^sub>1)\<close>, and at the tiling boundary
  \<open>x = j\<^sub>0 + q\<cdot>w\<close> the \<open>N[n]\<close>-parent is its block-\<open>(q-1)\<close> image
  \<open>j\<^sub>0 + (q-1)\<cdot>w + (parent N 0 j\<^sub>1 - j\<^sub>0)\<close>, with the \<open>+1\<close> step closing via
  \<open>RedCondA N\<close> and the uniform \<open>q\<cdot>d\<^sub>0\<close> shift (\<open>d\<^sub>0 = entry N 0 j\<^sub>1 - entry N 0 j\<^sub>0\<close>).
  This existence fact is the only piece of the (false) prescribed brick (0) that
  survives: \<open>parent N 0 j\<^sub>1 = j\<^sub>1-1\<close> is FALSE on the stated domain (464/1475
  standard counterexamples, /tmp/brick0_std.py).\<close>

lemma oper_last_row0_haspar:
  fixes N :: pairseq
  assumes hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
  shows "hasParent N 0 (Lng N - 1)"
proof -
  let ?j1 = "Lng N - 1"  let ?j0 = "parent N 1 ?j1"
  have L: "1 < Lng N" using j0lt by linarith
  have NT: "N \<in> T_PS" using L by (cases N) (auto simp: T_PS_def)
  have hp1: "hasParent N 1 ?j1" using hp i1 by simp
  have parR: "nextR N 1 ?j0 ?j1"
    using hp1 unfolding hasParent_def parent_def by (rule theI')
  \<comment> \<open>the row-1 parent edge gives \<open>le0\<close>, so the active slice is \<open>monoT\<close>\<close>
  have le0: "leR N 0 ?j0 ?j1" using poper_nextR_imp_le0[OF parR] by simp
  have mono: "monoT (seg N ?j0 ?j1)"
    by (rule m_6_2_mono_ancestor_slice[OF NT j0lt le0])
  \<comment> \<open>row 0 strictly increases across the slice: \<open>entry N 0 j\<^sub>0 < entry N 0 j\<^sub>1\<close>\<close>
  have segT: "seg N ?j0 ?j1 \<in> T_PS" using j0lt by (auto simp: T_PS_def seg_def)
  have leR0: "leR (seg N ?j0 ?j1) 0 0 (Lng (seg N ?j0 ?j1) - 1)"
    using mono by (simp add: monoT_def)
  have wpos: "0 < ?j1 - ?j0" using j0lt by linarith
  have slt: "?j1 - ?j0 < Lng (seg N ?j0 ?j1)" using j0lt by simp
  have strictseg: "entry (seg N ?j0 ?j1) 0 0 < entry (seg N ?j0 ?j1) 0 (?j1 - ?j0)"
    using m_6_2_multi_crit_23[OF segT] leR0 wpos slt by blast
  have z0: "0 < Lng (seg N ?j0 ?j1)" using j0lt by simp
  have e0: "entry (seg N ?j0 ?j1) 0 0 = entry N 0 ?j0"
    using entry_seg[OF z0] by simp
  have es: "entry (seg N ?j0 ?j1) 0 (?j1 - ?j0) = entry N 0 ?j1"
    using entry_seg[OF slt] j0lt by simp
  have strict: "entry N 0 ?j0 < entry N 0 ?j1" using strictseg e0 es by simp
  \<comment> \<open>existence of a row-0 parent of \<open>j\<^sub>1\<close>, then uniqueness\<close>
  have j1lt: "?j0 < ?j1" by (rule j0lt)
  have j1L: "?j1 < Lng N" using L by simp
  obtain p where "?j0 \<le> p \<and> p < ?j1 \<and> nextR N 0 p ?j1"
    using m_5_1_parent_exists_1[OF NT j1lt j1L strict] by blast
  hence pP: "nextR N 0 p ?j1" by simp
  have "\<exists>!q. nextR N 0 q ?j1"
    using pP idxsum_parent0_unique by metis
  thus ?thesis unfolding hasParent_def by simp
qed


text \<open>Helper: \<open>parent\<close> in row 0 from an explicit edge + uniqueness.  Stated with
  abstract \<open>a, k, M\<close> so the \<open>THE\<close>-matching is on simple variables (avoids the
  higher-order unifier blow-up when \<open>a\<close>/\<open>k\<close> are large \<open>parent\<close>-laden terms).\<close>

lemma parent0_eqI:
  assumes edge: "nextR M 0 a k"
    and uniq: "\<And>b. nextR M 0 b k \<Longrightarrow> b = a"
  shows "parent M 0 k = a"
proof -
  have ex1: "\<exists>!b. nextR M 0 b k" using edge uniq by blast
  show ?thesis unfolding parent_def by (rule the1_equality[OF ex1 edge])
qed

text \<open>§6.7 oper-tiling brick (Front A, ROW 0): the BOUNDARY \<open>+1\<close> step.  For a
  block-start column \<open>x = j\<^sub>0 + q\<cdot>w\<close> (\<open>q \<ge> 1\<close>, \<open>i\<^sub>1 = 1\<close>) of \<open>N[n]\<close> that has a
  row-0 parent, the \<open>N[n]\<close>-parent is the block-\<open>(q-1)\<close> IMAGE of the \<open>N\<close>-row-0
  parent of the last index: \<open>P = j\<^sub>0 + (q-1)\<cdot>w + (p\<^sub>N - j\<^sub>0)\<close> with
  \<open>p\<^sub>N = parent N 0 (Lng N-1) \<in> [j\<^sub>0, Lng N-1)\<close> (empirically
  /tmp/bnd_char.py 9612/9612, /tmp/pN0_loc.py 1602/1602 \<open>p\<^sub>N \<ge> j\<^sub>0\<close>).  The valley
  window \<open>(P, x)\<close> sits ENTIRELY in block \<open>q-1\<close> (offsets \<open>(r, w)\<close>, \<open>x\<close> being the
  first column of block \<open>q\<close>), so the edge \<open>nextrel0 (N[n]) P x\<close> reflects EXACTLY
  to the \<open>N\<close>-parent edge \<open>nextrel0 N p\<^sub>N (Lng N-1)\<close> via the block-\<open>q\<close>/\<open>(q-1)\<close>
  decode (@{thm [source] oper_gen_block_entry0}) and the floor identity
  \<open>e\<^sub>0(N,j\<^sub>0)+d\<^sub>0 = e\<^sub>0(N,Lng N-1)\<close>.  The \<open>+1\<close> step then closes by \<open>RedCondA N\<close> at
  the last index (the \<open>q\<cdot>d\<^sub>0\<close> shift cancels).  NOTE: the prescribed brick (0)
  \<open>parent N 0 (Lng N-1) = Lng N-2\<close> and step (1) \<open>parent (N[n]) 0 x = x-1\<close> are both
  FALSE for \<open>w \<ge> 2\<close> (/tmp/bnd_w.py: 3060/5226 have \<open>x - p \<noteq> 1\<close>); this corrected
  characterization is 9612/9612 with \<open>+1\<close>-step 9612/9612.\<close>

lemma oper_gen_tiling_row0_boundary:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1: "idx1 N (Lng N - 1) = 1"
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
  let ?d0 = "if 0 < ?i1 then entry N 0 ?j1 - entry N 0 ?j0 else 0"
  let ?Nn = "(N::pairseq)[n]"
  let ?B = "?j0 + q * ?w"  let ?x = "?B"
  have w0: "0 < ?w" using j0lt by linarith
  have d0def: "?d0 = entry N 0 ?j1 - entry N 0 ?j0" using i1 by simp
  \<comment> \<open>block-\<open>k\<close> row-0 reading at offset \<open>t < w\<close> (for \<open>k < n\<close>)\<close>
  have blk: "\<And>k t. k < n \<Longrightarrow> t < ?w \<Longrightarrow> entry ?Nn 0 (?j0 + k * ?w + t) = entry N 0 (?j0 + t) + k * ?d0"
  proof -
    fix k t assume k: "k < n" and t: "t < ?w"
    show "entry ?Nn 0 (?j0 + k * ?w + t) = entry N 0 (?j0 + t) + k * ?d0"
      by (rule oper_gen_block_entry0[OF L notzero hp j0lt k t])
  qed
  \<comment> \<open>value at the block-start \<open>x = j\<^sub>0 + q\<cdot>w\<close>: \<open>e\<^sub>0(N,j\<^sub>0) + q\<cdot>d\<^sub>0\<close>\<close>
  have ex: "entry ?Nn 0 ?x = entry N 0 ?j0 + q * ?d0" using blk[OF qn w0] by simp
  \<comment> \<open>the \<open>N\<close>-side row-0 parent of the last index and its offset \<open>r = p\<^sub>N - j\<^sub>0 \<in> [0,w)\<close>\<close>
  have hp0: "hasParent N 0 ?j1" by (rule oper_last_row0_haspar[OF hp i1 j0lt[unfolded i1]])
  have parR: "nextR N 0 (parent N 0 ?j1) ?j1"
    using hp0 unfolding hasParent_def parent_def by (rule theI')
  let ?pN = "parent N 0 ?j1"  let ?r = "?pN - ?j0"
  have parN0: "nextrel0 N ?pN ?j1" using parR by (simp add: nextR_def)
  have pNj1: "?pN < ?j1" using parN0 by (simp add: nextrel0_def)
  \<comment> \<open>\<open>p\<^sub>N \<ge> j\<^sub>0\<close>: the row-1 parent edge gives \<open>le0\<close>, so the slice \<open>[j\<^sub>0,j\<^sub>1]\<close> is
     \<open>monoT\<close>; a row-0 parent of \<open>j\<^sub>1\<close> below \<open>j\<^sub>0\<close> would violate the strict floor at \<open>j\<^sub>0\<close>\<close>
  \<comment> \<open>floor identity: \<open>e\<^sub>0(N,j\<^sub>0) < e\<^sub>0(N,j\<^sub>1)\<close> (strict period floor at the full offset \<open>w\<close>)\<close>
  have floor: "entry N 0 ?j0 < entry N 0 ?j1"
  proof -
    have sle: "?w \<le> Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)" by simp
    have jle: "?j0 \<le> ?j1" using j0lt by linarith
    have jeq: "?j0 + ?w = ?j1" using jle by (rule le_add_diff_inverse)
    have flt: "entry N 0 ?j0 < entry N 0 (?j0 + ?w)"
      using oper_gen_strict_period_floor[OF hp j0lt w0 sle] .
    show ?thesis using flt unfolding jeq .
  qed
  have pNge: "?j0 \<le> ?pN"
  proof (rule ccontr)
    assume "\<not> ?j0 \<le> ?pN"
    hence plo: "?pN < ?j0" by simp
    have j0hi: "?j0 < ?j1" by (rule j0lt)
    have "entry N 0 ?j1 \<le> entry N 0 ?j0" using parN0 plo j0hi by (simp add: nextrel0_def)
    thus False using floor by simp
  qed
  have rw: "?r < ?w" using pNj1 pNge by linarith
  have psplit: "?pN = ?j0 + ?r" using pNge by simp
  \<comment> \<open>the candidate \<open>N[n]\<close>-parent \<open>P\<close>: block \<open>q-1\<close>, offset \<open>r\<close>\<close>
  let ?P = "?j0 + (q - 1) * ?w + ?r"
  have q1n: "q - 1 < n" using qn by linarith
  have eP: "entry ?Nn 0 ?P = entry N 0 ?pN + (q - 1) * ?d0"
    using blk[OF q1n rw] psplit by simp
  \<comment> \<open>floor identity: \<open>e\<^sub>0(N,j\<^sub>0) + d\<^sub>0 = e\<^sub>0(N,j\<^sub>1)\<close>\<close>
  have floorid: "entry N 0 ?j0 + ?d0 = entry N 0 ?j1"
    using floor d0def by simp
  \<comment> \<open>once-and-for-all \<open>q\<close>-split arithmetic (\<open>q \<ge> 1\<close>): \<open>q\<cdot>z = (q-1)\<cdot>z + z\<close>\<close>
  have qsplit: "\<And>z::nat. q * z = (q - 1) * z + z"
  proof -
    fix z :: nat
    have "q * z = (Suc (q - 1)) * z" using q1 by simp
    thus "q * z = (q - 1) * z + z" by simp
  qed
  have qw: "q * ?w = (q - 1) * ?w + ?w" by (rule qsplit)
  have qd: "q * ?d0 = (q - 1) * ?d0 + ?d0" by (rule qsplit)
  \<comment> \<open>the \<open>q\<close>-shifted floor: \<open>e\<^sub>0(N,j\<^sub>1) + (q-1)\<cdot>d\<^sub>0 = e\<^sub>0(N,j\<^sub>0) + q\<cdot>d\<^sub>0\<close>\<close>
  have qshift: "entry N 0 ?j1 + (q - 1) * ?d0 = entry N 0 ?j0 + q * ?d0"
  proof -
    have "entry N 0 ?j0 + q * ?d0 = entry N 0 ?j0 + ((q - 1) * ?d0 + ?d0)" using qd by simp
    also have "\<dots> = (entry N 0 ?j0 + ?d0) + (q - 1) * ?d0" by simp
    also have "\<dots> = entry N 0 ?j1 + (q - 1) * ?d0" using floorid by simp
    finally show ?thesis by simp
  qed
  \<comment> \<open>length and \<open>P, x < Lng (N[n])\<close>\<close>
  have LngNn: "Lng ?Nn = ?j0 + n * ?w" using operB_gen_LngM[OF L notzero hp j0lt] by simp
  have Bbound: "\<And>k. k < n \<Longrightarrow> ?j0 + k * ?w + ?w \<le> Lng ?Nn"
  proof -
    fix k assume "k < n" hence "Suc k \<le> n" by simp
    hence "Suc k * ?w \<le> n * ?w" by (rule mult_le_mono1)
    hence "?j0 + k * ?w + ?w \<le> ?j0 + n * ?w" by simp
    thus "?j0 + k * ?w + ?w \<le> Lng ?Nn" using LngNn by simp
  qed
  have xlt: "?x < Lng ?Nn"
  proof -
    have "?j0 + q * ?w < ?j0 + q * ?w + ?w"
      using w0 by (simp only: less_add_same_cancel1)
    thus ?thesis using Bbound[OF qn] by (rule less_le_trans)
  qed
  have Plt: "?P < Lng ?Nn"
  proof -
    have "?j0 + (q-1) * ?w + ?r < ?j0 + (q-1) * ?w + ?w"
      by (rule add_strict_left_mono[OF rw])
    thus ?thesis using Bbound[OF q1n] by (rule less_le_trans)
  qed
  \<comment> \<open>the block-start \<open>x\<close> as block \<open>(q-1)\<close> shifted by one full period\<close>
  have xeq: "?x = ?j0 + (q - 1) * ?w + ?w"
    by (simp only: qw add.assoc)
  have jeqw': "?j0 + ?w = ?j1" using j0lt[THEN less_imp_le] by (rule le_add_diff_inverse)
  \<comment> \<open>\<open>P < x\<close>\<close>
  have Px: "?P < ?x"
  proof -
    have "?j0 + (q-1) * ?w + ?r < ?j0 + (q-1) * ?w + ?w"
      by (rule add_strict_left_mono[OF rw])
    also have "\<dots> = ?x" using xeq by (rule sym)
    finally show ?thesis .
  qed
  \<comment> \<open>the strict step at the edge\<close>
  have stepval: "entry ?Nn 0 ?P < entry ?Nn 0 ?x"
  proof -
    have a: "entry N 0 ?pN < entry N 0 ?j1" using parN0 by (simp add: nextrel0_def)
    have "entry ?Nn 0 ?P = entry N 0 ?pN + (q-1)*?d0" by (rule eP)
    also have "\<dots> < entry N 0 ?j1 + (q-1)*?d0" using a by simp
    also have "\<dots> = entry N 0 ?j0 + q*?d0" using qshift by simp
    also have "\<dots> = entry ?Nn 0 ?x" using ex by simp
    finally show ?thesis .
  qed
  \<comment> \<open>the window \<open>(P, x)\<close> lies in block \<open>q-1\<close> at offsets \<open>(r, w)\<close>; reflect the valley\<close>
  have window: "\<And>j. ?P < j \<Longrightarrow> j < ?x \<Longrightarrow> entry ?Nn 0 ?x \<le> entry ?Nn 0 j"
  proof -
    fix j assume jlo: "?P < j" and jhi: "j < ?x"
    have jge: "?j0 + (q-1) * ?w \<le> j" using jlo by linarith
    let ?t = "j - (?j0 + (q-1) * ?w)"
    have tlo: "?r < ?t" using jlo by linarith
    have xeq': "?x = ?j0 + (q-1) * ?w + ?w" by (rule xeq)
    have thi: "?t < ?w" using jhi jge xeq' by linarith
    have jt: "j = ?j0 + (q-1) * ?w + ?t" using jge by (simp add: add.commute)
    \<comment> \<open>row-0 reading of the window column\<close>
    have ej: "entry ?Nn 0 j = entry N 0 (?j0 + ?t) + (q-1) * ?d0"
      using blk[OF q1n thi] jt by simp
    \<comment> \<open>the \<open>N\<close>-valley of the parent edge at \<open>j\<^sub>0 + t\<close> (since \<open>p\<^sub>N < j\<^sub>0+t < j\<^sub>1\<close>)\<close>
    have lo': "?pN < ?j0 + ?t" using tlo psplit by linarith
    have jeqw: "?j0 + ?w = ?j1" using j0lt[THEN less_imp_le] by (rule le_add_diff_inverse)
    have hi': "?j0 + ?t < ?j1" using thi jeqw by linarith
    have vN: "entry N 0 ?j1 \<le> entry N 0 (?j0 + ?t)" using parN0 lo' hi' by (simp add: nextrel0_def)
    have "entry ?Nn 0 ?x = entry N 0 ?j0 + q*?d0" by (rule ex)
    also have "\<dots> = entry N 0 ?j1 + (q-1)*?d0" using qshift by simp
    also have "\<dots> \<le> entry N 0 (?j0 + ?t) + (q-1)*?d0" using vN by simp
    also have "\<dots> = entry ?Nn 0 j" using ej by simp
    finally show "entry ?Nn 0 ?x \<le> entry ?Nn 0 j" .
  qed
  have edge: "nextrel0 ?Nn ?P ?x"
    unfolding nextrel0_def using Plt xlt Px stepval window by simp
  \<comment> \<open>the block-\<open>(q-1)\<close> start \<open>B' = j\<^sub>0+(q-1)\<cdot>w\<close> carries the floor \<open>e\<^sub>0(N,j\<^sub>0)+(q-1)\<cdot>d\<^sub>0\<close>,
     STRICTLY below \<open>e\<^sub>0(N[n],x)\<close>; this pins any \<open>N[n]\<close>-parent \<open>p'\<close> of \<open>x\<close> into block \<open>q-1\<close>\<close>
  let ?Bp = "?j0 + (q - 1) * ?w"
  have eBp: "entry ?Nn 0 ?Bp = entry N 0 ?j0 + (q - 1) * ?d0"
    using blk[OF q1n w0] by simp
  have BpLT: "entry ?Nn 0 ?Bp < entry ?Nn 0 ?x"
  proof -
    have "entry N 0 ?j0 + (q-1)*?d0 < entry N 0 ?j0 + q*?d0"
    proof -
      have dpos: "0 < ?d0" using floor d0def by simp
      have "(q-1)*?d0 < q*?d0" using qd dpos by simp
      thus ?thesis by simp
    qed
    thus ?thesis using eBp ex by simp
  qed
  \<comment> \<open>uniqueness: any \<open>N[n]\<close>-parent \<open>p'\<close> of \<open>x\<close> equals \<open>P\<close>\<close>
  have uniqNn: "\<And>p'. nextrel0 ?Nn p' ?x \<Longrightarrow> p' = ?P"
  proof -
    fix p' assume Hp': "nextrel0 ?Nn p' ?x"
    have p'x: "p' < ?x" using Hp' by (simp add: nextrel0_def)
    have p'val: "\<And>j. p' < j \<Longrightarrow> j < ?x \<Longrightarrow> entry ?Nn 0 ?x \<le> entry ?Nn 0 j"
      using Hp' by (simp add: nextrel0_def)
    \<comment> \<open>\<open>B' \<le> p'\<close>: a strictly-lower \<open>B'\<close> inside \<open>(p',x)\<close> contradicts the running min\<close>
    have Bpp: "?Bp \<le> p'"
    proof (rule ccontr)
      assume "\<not> ?Bp \<le> p'"
      hence pB: "p' < ?Bp" by simp
      have Bx: "?Bp < ?x" using Px psplit by linarith
      have "entry ?Nn 0 ?x \<le> entry ?Nn 0 ?Bp" using p'val[OF pB Bx] .
      thus False using BpLT by simp
    qed
    \<comment> \<open>so \<open>p' = B' + r'\<close> with \<open>r' = p'-B' < w\<close> (block \<open>q-1\<close>)\<close>
    have xeqBp: "?x = ?Bp + ?w" using xeq by (simp add: add.assoc)
    have r'w: "p' - ?Bp < ?w" using p'x Bpp xeqBp by linarith
    have p'split: "p' = ?Bp + (p' - ?Bp)" using Bpp by simp
    have eP': "entry ?Nn 0 p' = entry N 0 (?j0 + (p' - ?Bp)) + (q-1) * ?d0"
      using blk[OF q1n r'w] p'split by (simp add: add.assoc)
    \<comment> \<open>reflect \<open>nextrel0 (N[n]) p' x\<close> down to \<open>nextrel0 N (j\<^sub>0+r') j\<^sub>1\<close>\<close>
    let ?pn = "?j0 + (p' - ?Bp)"
    have pnlt: "?pn < Lng N" using r'w j0lt by linarith
    have stepN: "nextrel0 N ?pn ?j1"
      unfolding nextrel0_def
    proof (intro conjI allI impI)
      show "?pn < Lng N" by (rule pnlt)
      show "?j1 < Lng N" using L by simp
      show "?pn < ?j1" using r'w j0lt by linarith
      have "entry ?Nn 0 p' < entry ?Nn 0 ?x" using Hp' by (simp add: nextrel0_def)
      hence "entry N 0 ?pn + (q-1)*?d0 < entry N 0 ?j0 + q*?d0" using eP' ex by simp
      hence "entry N 0 ?pn + (q-1)*?d0 < entry N 0 ?j1 + (q-1)*?d0" using qshift by simp
      thus "entry N 0 ?pn < entry N 0 ?j1" by simp
    next
      fix jj assume jjr: "?pn < jj \<and> jj < ?j1"
      hence jlo: "?pn < jj" and jhi: "jj < ?j1" by simp_all
      \<comment> \<open>map \<open>jj = j\<^sub>0 + t\<close> up to \<open>B' + t\<close> in block \<open>q-1\<close>\<close>
      have jge: "?j0 \<le> jj" using jlo r'w by linarith
      let ?t = "jj - ?j0"
      have tw: "?t < ?w" using jhi jge jeqw' by linarith
      have jt: "jj = ?j0 + ?t" using jge by simp
      have tlo: "p' - ?Bp < ?t" using jlo p'split jt by linarith
      have Btlo: "p' < ?Bp + ?t" using jlo p'split jt by linarith
      have Bthi: "?Bp + ?t < ?x" using jhi jt xeqBp jge by linarith
      have "entry ?Nn 0 ?x \<le> entry ?Nn 0 (?Bp + ?t)" using p'val[OF Btlo Bthi] .
      hence "entry N 0 ?j0 + q*?d0 \<le> entry N 0 (?j0+?t) + (q-1)*?d0"
        using ex blk[OF q1n tw] by (simp add: add.assoc)
      hence "entry N 0 ?j1 + (q-1)*?d0 \<le> entry N 0 (?j0+?t) + (q-1)*?d0" using qshift by simp
      hence "entry N 0 ?j1 \<le> entry N 0 (?j0+?t)" by simp
      thus "entry N 0 ?j1 \<le> entry N 0 jj" using jt by simp
    qed
    have "?pn = ?pN" using idxsum_parent0_unique[of N ?pn ?j1 ?pN]
      stepN parN0 by (simp add: nextR_def)
    hence "?j0 + (p' - ?Bp) = ?j0 + ?r" using psplit by simp
    hence "p' - ?Bp = ?r" by simp
    thus "p' = ?P" using p'split by simp
  qed
  \<comment> \<open>\<open>parent (N[n]) 0 x = P\<close> from the explicit edge + uniqueness\<close>
  have parNn: "parent ?Nn 0 ?x = ?P"
  proof -
    have edgeR: "nextR ?Nn 0 ?P ?x" using edge by (simp add: nextR_def)
    have uniqR: "\<And>p'. nextR ?Nn 0 p' ?x \<Longrightarrow> p' = ?P"
      using uniqNn by (simp add: nextR_def)
    show ?thesis by (rule parent0_eqI[OF edgeR uniqR])
  qed
  \<comment> \<open>RedCondA N at the last index closes the \<open>+1\<close> step; the \<open>(q-1)\<cdot>d\<^sub>0\<close> shift cancels\<close>
  have baseN: "entry N 0 ?pN + 1 = entry N 0 ?j1"
    using condA[unfolded RedCondA_def, rule_format, of 0 ?j1] hp0 by simp
  have "entry ?Nn 0 (parent ?Nn 0 ?x) + 1 = entry N 0 ?pN + (q-1) * ?d0 + 1"
    using parNn eP by simp
  also have "\<dots> = (entry N 0 ?pN + 1) + (q-1) * ?d0" by simp
  also have "\<dots> = entry N 0 ?j1 + (q-1) * ?d0" using baseN by simp
  also have "\<dots> = entry N 0 ?j0 + q * ?d0" using qshift by simp
  also have "\<dots> = entry ?Nn 0 ?x" using ex by simp
  finally show ?thesis .
qed

end
