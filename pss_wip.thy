theory pss_wip
  imports pss_mechanized
begin

text \<open>
  Work-in-progress §6.7 lemmas (operCA boundary-valley discharge: the H1/H2 le0
  reflections and the readback assembly).  Stable results graduate back into
  pss_mechanized.thy.  H1 (block, cross-block le0 reflection) already landed in
  pss_mechanized as @{thm [source] oper_d1pos_le0_cross_back}.
\<close>

text \<open>§6.7 oper-tiling PREFIX row-0 le0 reflection (the \<open>H2\<close> brick).  A PREFIX node
  \<open>j' < j\<^sub>0\<close> that row-0-reaches a block START \<open>j\<^sub>0 + q\<cdot>w\<close> in \<open>N[n]\<close> already
  row-0-reaches \<open>j\<^sub>0\<close> (the \<open>le0\<close>-ancestors of a node form a chain,
  @{thm [source] m_5_1_ancestor_tree_1}), and the verbatim prefix \<open>[0,j\<^sub>0]\<close>
  (@{thm [source] le0_prefix_agree}, endpoint via @{thm [source] oper_gen_block_nth}
  at \<open>q=0,s=0\<close>) carries that back to \<open>le0 N j' j\<^sub>0\<close>.  Feeds the boundary-readback
  valley via the \<open>nextrel1 N (parent N 1 j\<^sub>0) j\<^sub>0\<close> maximality clause.\<close>

lemma oper_d1pos_le0_prefix_back:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and qn: "q < n"
    and jpj0: "j' < parent N 1 (Lng N - 1)"
    and reach: "le0 ((N::pairseq)[n]) j'
                  (parent N 1 (Lng N - 1) + q * (Lng N - 1 - parent N 1 (Lng N - 1)))"
  shows "le0 N j' (parent N 1 (Lng N - 1))"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N 1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?Mn = "(N::pairseq)[n]"
  let ?z = "?j0 + q * ?w"
  have w0: "0 < ?w" using j0lt by linarith
  have n0: "0 < n" using qn by simp
  have pj0eq: "parent N (idx1 N ?j1) ?j1 = ?j0" using i1z by simp
  have hpidx: "hasParent N (idx1 N ?j1) ?j1" using hp .
  have j0lt': "parent N (idx1 N ?j1) ?j1 < ?j1" using j0lt pj0eq by simp
  \<comment> \<open>verbatim prefix \<open>[0,j\<^sub>0]\<close>: \<open>N[n] ! x = N ! x\<close> for \<open>x \<le> j\<^sub>0\<close>  (copied green pattern)\<close>
  have nthj0: "?Mn ! ?j0 = N ! ?j0"
  proof -
    have raw: "?Mn ! (parent N (idx1 N ?j1) ?j1
                 + 0 * (?j1 - parent N (idx1 N ?j1) ?j1) + 0)
             = (entry N 0 (parent N (idx1 N ?j1) ?j1 + 0)
                  + 0 * (if 0 < idx1 N ?j1 then entry N 0 ?j1
                           - entry N 0 (parent N (idx1 N ?j1) ?j1) else 0),
                entry N 1 (parent N (idx1 N ?j1) ?j1 + 0))"
      by (rule oper_gen_block_nth[OF L notzero hpidx j0lt' n0, where s=0])
         (use j0lt' in linarith)
    have lhs: "?Mn ! (parent N (idx1 N ?j1) ?j1
                 + 0 * (?j1 - parent N (idx1 N ?j1) ?j1) + 0) = ?Mn ! ?j0"
      using pj0eq by simp
    have rhs: "(entry N 0 (parent N (idx1 N ?j1) ?j1 + 0)
                  + 0 * (if 0 < idx1 N ?j1 then entry N 0 ?j1
                           - entry N 0 (parent N (idx1 N ?j1) ?j1) else 0),
                entry N 1 (parent N (idx1 N ?j1) ?j1 + 0))
             = (entry N 0 ?j0, entry N 1 ?j0)" using pj0eq by simp
    have mj0: "N ! ?j0 = (entry N 0 ?j0, entry N 1 ?j0)"
      by (simp add: entry_def)
    show ?thesis using raw lhs rhs mj0 by simp
  qed
  have agree: "\<And>x. x \<le> ?j0 \<Longrightarrow> ?Mn ! x = N ! x"
  proof -
    fix x assume xj0: "x \<le> ?j0"
    show "?Mn ! x = N ! x"
    proof (cases "x = ?j0")
      case True thus ?thesis using nthj0 by simp
    next
      case False
      have xlt: "x < ?j0" using xj0 False by simp
      show ?thesis by (rule oper_gen_nth_prefix[OF L notzero hpidx]) (use xlt pj0eq in simp)
    qed
  qed
  have lenMn: "Lng ?Mn = ?j0 + n * ?w"
    using oper_d1pos_LngM[OF L notzero hp i1z j0lt] by simp
  have nwpos: "0 < n * ?w" using n0 w0 by simp
  have j0ltMn: "?j0 < Lng ?Mn" using lenMn nwpos by simp
  have NnT: "?Mn \<in> T_PS" using j0ltMn by (cases ?Mn) (auto simp: T_PS_def)
  \<comment> \<open>R1: the prefix node already reaches \<open>j\<^sub>0\<close> (le0-ancestor chain)\<close>
  have jle: "j' \<le> ?j0" using jpj0 by linarith
  have j0lez: "?j0 \<le> ?z" by simp
  have leRz: "leR ?Mn 0 j' ?z" using reach by (simp add: leR_def)
  have R1: "le0 ?Mn j' ?j0"
    using m_5_1_ancestor_tree_1[OF NnT leRz jle j0lez] by (simp add: leR_def)
  have cN: "?j0 < Lng N" using j0lt by linarith
  show "le0 N j' ?j0"
    by (rule le0_prefix_agree[OF agree j0ltMn cN jle order.refl R1])
qed

text \<open>§6.7 oper-tiling BOUNDARY VALLEY: the single residual of
  @{thm [source] oper_parent1_readback_boundary}.  For a le0-predecessor \<open>j'\<close> of
  the block START \<open>z = j\<^sub>0+q\<cdot>w\<close> with \<open>j' > p\<^sub>j = parent N 1 j\<^sub>0\<close>, its row-1 entry is
  \<open>\<ge> entry N 1 j\<^sub>0 = entry (N[n]) 1 z\<close>.  Discharged NON-CIRCULARLY (no GTWF / no
  \<open>D\<close>) by classifying \<open>j'\<close>: PREFIX (@{thm [source] oper_d1pos_le0_prefix_back} \<open>\<rightarrow>\<close>
  the \<open>nextrel1 N p\<^sub>j j\<^sub>0\<close> valley), BLOCK-START (row-1 equals \<open>entry N 1 j\<^sub>0\<close>), or
  INTERIOR (@{thm [source] oper_d1pos_le0_cross_back} \<open>\<rightarrow>\<close> the \<open>nextrel1 N j\<^sub>0 j\<^sub>1\<close>
  valley, with \<open>entry N 1 j\<^sub>0 < entry N 1 j\<^sub>1\<close>); periodic row-1 via
  @{thm [source] oper_d1pos_entry1}, prefix row-1 via
  @{thm [source] operB_gen_entry_prefix}.\<close>

lemma oper_boundary_valley:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and hpMj0: "hasParent N 1 (parent N 1 (Lng N - 1))"
    and qn: "q < n"
    and jpgt: "parent N 1 (parent N 1 (Lng N - 1)) < j'"
    and reach: "le0 ((N::pairseq)[n]) j'
                  (parent N 1 (Lng N - 1) + q * (Lng N - 1 - parent N 1 (Lng N - 1)))"
  shows "entry ((N::pairseq)[n]) 1
             (parent N 1 (Lng N - 1) + q * (Lng N - 1 - parent N 1 (Lng N - 1)))
         \<le> entry ((N::pairseq)[n]) 1 j'"
proof -
  let ?j1 = "Lng N - 1"  let ?j0 = "parent N 1 ?j1"  let ?w = "?j1 - ?j0"
  let ?Mn = "(N::pairseq)[n]"  let ?z = "?j0 + q * ?w"  let ?pj = "parent N 1 ?j0"
  have w0: "0 < ?w" using j0lt by linarith
  have n0: "0 < n" using qn by simp
  \<comment> \<open>row-1 of the block start equals \<open>entry N 1 j\<^sub>0\<close>\<close>
  have ez: "entry ?Mn 1 ?z = entry N 1 ?j0"
    using oper_d1pos_entry1[OF L notzero hp i1z j0lt qn w0] by simp
  \<comment> \<open>the parent edge \<open>nextrel1 N j\<^sub>0 j\<^sub>1\<close> and its valley\<close>
  have hpj1: "hasParent N 1 ?j1" using hp i1z by simp
  have parj1: "nextR N 1 ?j0 ?j1"
    using hpj1 unfolding hasParent_def parent_def by (rule theI')
  have nr1j1: "nextrel1 N ?j0 ?j1" using parj1 by (simp add: nextR_def)
  have ej0j1: "entry N 1 ?j0 < entry N 1 ?j1" using nr1j1 by (simp add: nextrel1_def)
  have valley1: "\<And>j. ?j0 < j \<Longrightarrow> le0 N j ?j1 \<Longrightarrow> entry N 1 ?j1 \<le> entry N 1 j"
    using nr1j1 unfolding nextrel1_def by blast
  \<comment> \<open>the parent edge \<open>nextrel1 N p\<^sub>j j\<^sub>0\<close> and its valley\<close>
  have parj0: "nextR N 1 ?pj ?j0"
    using hpMj0 unfolding hasParent_def parent_def by (rule theI')
  have nr1j0: "nextrel1 N ?pj ?j0" using parj0 by (simp add: nextR_def)
  have valley0: "\<And>j. ?pj < j \<Longrightarrow> le0 N j ?j0 \<Longrightarrow> entry N 1 ?j0 \<le> entry N 1 j"
    using nr1j0 unfolding nextrel1_def by blast
  show ?thesis
  proof (cases "j' < ?j0")
    case True
    \<comment> \<open>PREFIX: reflect to \<open>le0 N j' j\<^sub>0\<close>, apply the \<open>p\<^sub>j\<close>-valley\<close>
    have le0Nj0: "le0 N j' ?j0"
      by (rule oper_d1pos_le0_prefix_back[OF L notzero hp i1z j0lt qn True reach])
    have e1: "entry N 1 ?j0 \<le> entry N 1 j'" using valley0[OF jpgt le0Nj0] .
    have xpre: "j' < parent N (idx1 N (Lng N - 1)) (Lng N - 1)" using True i1z by simp
    have e2: "entry ?Mn 1 j' = entry N 1 j'"
      by (rule operB_gen_entry_prefix[OF L notzero hp xpre])
    show ?thesis using ez e1 e2 by simp
  next
    case False
    hence j0lej: "?j0 \<le> j'" by simp
    \<comment> \<open>\<open>j' \<le> z\<close> (le0 is index-monotone), and block decomposition \<open>j' = j\<^sub>0+q'\<cdot>w+s'\<close>\<close>
    have jlez: "j' \<le> ?z"
    proof -
      have "(nextrel0 ?Mn)\<^sup>*\<^sup>* j' ?z" using reach by (simp add: le0_def)
      thus ?thesis by (rule nextrel0_rtrancl_mono)
    qed
    define s' where "s' = (j' - ?j0) mod ?w"
    define q' where "q' = (j' - ?j0) div ?w"
    have s'w: "s' < ?w" using w0 by (simp add: s'_def)
    have decomp0: "q' * ?w + s' = j' - ?j0"
      by (simp add: s'_def q'_def div_mult_mod_eq)
    have jdecomp: "j' = ?j0 + q' * ?w + s'" using decomp0 j0lej by simp
    have qstep: "q' * ?w + s' \<le> q * ?w" using jlez jdecomp by simp
    have q'wle: "q' * ?w \<le> q * ?w"
    proof -
      have "q' * ?w \<le> q' * ?w + s'" by (rule le_add1)
      thus ?thesis using qstep by (rule order_trans)
    qed
    have q'leq: "q' \<le> q"
    proof (rule ccontr)
      assume "\<not> q' \<le> q"
      hence "q < q'" by simp
      hence "q * ?w < q' * ?w" using w0 by (rule mult_strict_right_mono)
      thus False using q'wle by simp
    qed
    have q'n: "q' < n" using q'leq qn by simp
    show ?thesis
    proof (cases "s' = 0")
      case True
      \<comment> \<open>BLOCK-START: row-1 equals \<open>entry N 1 j\<^sub>0\<close>\<close>
      have "entry ?Mn 1 j' = entry N 1 (?j0 + s')"
        using oper_d1pos_entry1[OF L notzero hp i1z j0lt q'n s'w] jdecomp by simp
      hence "entry ?Mn 1 j' = entry N 1 ?j0" using True by simp
      thus ?thesis using ez by simp
    next
      case False
      hence s'pos: "0 < s'" by simp
      \<comment> \<open>INTERIOR: \<open>q' < q\<close>, reflect to \<open>le0 N (j\<^sub>0+s') j\<^sub>1\<close>, apply the \<open>j\<^sub>0\<close>-valley\<close>
      have q'wlt: "q' * ?w < q * ?w" using qstep s'pos by linarith
      have qq: "q' < q"
      proof (rule ccontr)
        assume "\<not> q' < q"
        hence "q \<le> q'" by simp
        hence "q * ?w \<le> q' * ?w" by (rule mult_le_mono1)
        thus False using q'wlt by simp
      qed
      have reachblk: "le0 ?Mn (?j0 + q' * ?w + s') ?z" using reach jdecomp by simp
      have le0Nj1: "le0 N (?j0 + s') ?j1"
        by (rule oper_d1pos_le0_cross_back[OF L notzero hp i1z j0lt qq qn s'w reachblk])
      have j0lt2: "?j0 < ?j0 + s'" using s'pos by simp
      have ge1: "entry N 1 ?j1 \<le> entry N 1 (?j0 + s')" using valley1[OF j0lt2 le0Nj1] .
      have eper: "entry ?Mn 1 j' = entry N 1 (?j0 + s')"
        using oper_d1pos_entry1[OF L notzero hp i1z j0lt q'n s'w] jdecomp by simp
      have "entry N 1 ?j0 \<le> entry N 1 (?j0 + s')" using ej0j1 ge1 by linarith
      thus ?thesis using ez eper by simp
    qed
  qed
qed

text \<open>§6.7 oper-tiling BLOCK-START row-1 parent readback, UNCONDITIONAL: the
  row-1 parent of a block start \<open>j\<^sub>0+q\<cdot>w\<close> of \<open>N[n]\<close> is the fixed prefix node
  \<open>p\<^sub>j = parent N 1 j\<^sub>0\<close>, INDEPENDENT of the block \<open>q\<close>.  The valley residual of
  @{thm [source] oper_parent1_readback_boundary} is now discharged by
  @{thm [source] oper_boundary_valley}.\<close>

lemma oper_parent1_readback_boundary_uncond:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and qn: "q < n"
    and hpMj0: "hasParent N 1 (parent N 1 (Lng N - 1))"
    and pjlt: "parent N 1 (parent N 1 (Lng N - 1)) < parent N 1 (Lng N - 1)"
  shows "parent ((N::pairseq)[n]) 1
            (parent N 1 (Lng N - 1) + q * (Lng N - 1 - parent N 1 (Lng N - 1)))
       = parent N 1 (parent N 1 (Lng N - 1))"
  by (rule oper_parent1_readback_boundary[OF L notzero hp i1z j0lt qn hpMj0 pjlt
        oper_boundary_valley[OF L notzero hp i1z j0lt hpMj0 qn]])

text \<open>§6.7 operCA BLOCK-START row-1 \<open>+1\<close>: for a block start \<open>z = j\<^sub>0+q\<cdot>w\<close> of \<open>N[n]\<close>
  whose fixed prefix parent \<open>p\<^sub>j = parent N 1 j\<^sub>0\<close> exists, RedCondA holds:
  \<open>entry (N[n]) 1 (parent (N[n]) 1 z) + 1 = entry (N[n]) 1 z\<close>.  The parent is \<open>p\<^sub>j\<close>
  (@{thm [source] oper_parent1_readback_boundary_uncond}); \<open>entry (N[n]) 1 p\<^sub>j =
  entry N 1 p\<^sub>j\<close> (verbatim prefix), \<open>entry (N[n]) 1 z = entry N 1 j\<^sub>0\<close> (periodic), and
  \<open>entry N 1 p\<^sub>j + 1 = entry N 1 j\<^sub>0\<close> is \<open>RedCondA N\<close> at \<open>j\<^sub>0\<close>.\<close>

lemma operCA_block_start_row1:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and qn: "q < n"
    and hpMj0: "hasParent N 1 (parent N 1 (Lng N - 1))"
    and pjlt: "parent N 1 (parent N 1 (Lng N - 1)) < parent N 1 (Lng N - 1)"
    and condA: "RedCondA N"
  shows "entry ((N::pairseq)[n]) 1
            (parent ((N::pairseq)[n]) 1
               (parent N 1 (Lng N - 1) + q * (Lng N - 1 - parent N 1 (Lng N - 1)))) + 1
       = entry ((N::pairseq)[n]) 1
            (parent N 1 (Lng N - 1) + q * (Lng N - 1 - parent N 1 (Lng N - 1)))"
proof -
  let ?j1 = "Lng N - 1"  let ?j0 = "parent N 1 ?j1"  let ?w = "?j1 - ?j0"
  let ?Mn = "(N::pairseq)[n]"  let ?z = "?j0 + q * ?w"  let ?pj = "parent N 1 ?j0"
  have w0: "0 < ?w" using j0lt by linarith
  have pz: "parent ?Mn 1 ?z = ?pj"
    by (rule oper_parent1_readback_boundary_uncond[OF L notzero hp i1z j0lt qn hpMj0 pjlt])
  have ez: "entry ?Mn 1 ?z = entry N 1 ?j0"
    using oper_d1pos_entry1[OF L notzero hp i1z j0lt qn w0] by simp
  have pjpre: "?pj < parent N (idx1 N (Lng N - 1)) (Lng N - 1)" using pjlt i1z by simp
  have epj: "entry ?Mn 1 ?pj = entry N 1 ?pj"
    by (rule operB_gen_entry_prefix[OF L notzero hp pjpre])
  have rca: "entry N 1 ?pj + 1 = entry N 1 ?j0"
    using condA hpMj0 unfolding RedCondA_def by blast
  show ?thesis using pz ez epj rca by simp
qed

text \<open>§6.7 operCA INTERIOR row-1 \<open>+1\<close>: for an interior column \<open>x = j\<^sub>0+q\<cdot>w+s\<close>
  (\<open>0<s<w\<close>) of \<open>N[n]\<close> whose base \<open>j\<^sub>0+s\<close> has a row-1 parent in \<open>N\<close> landing
  \<open>\<ge> j\<^sub>0\<close> (the gate), RedCondA holds.  The parent is \<open>parent N 1 (j\<^sub>0+s) + q\<cdot>w\<close>
  (@{thm [source] oper_parent1_readback}); periodic row-1 (@{thm [source]
  oper_d1pos_entry1}) at both \<open>x\<close> and the parent reduces to \<open>RedCondA N\<close> at \<open>j\<^sub>0+s\<close>.\<close>

lemma operCA_interior_row1:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and condA: "RedCondA N"
    and qn: "q < n"
    and spos: "0 < s"
    and sw: "s < Lng N - 1 - parent N 1 (Lng N - 1)"
    and hpMs: "hasParent N 1 (parent N 1 (Lng N - 1) + s)"
    and pMge: "parent N 1 (parent N 1 (Lng N - 1) + s) \<ge> parent N 1 (Lng N - 1)"
  shows "entry ((N::pairseq)[n]) 1
            (parent ((N::pairseq)[n]) 1
               (parent N 1 (Lng N - 1) + q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s)) + 1
       = entry ((N::pairseq)[n]) 1
            (parent N 1 (Lng N - 1) + q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s)"
proof -
  let ?j1 = "Lng N - 1"  let ?j0 = "parent N 1 ?j1"  let ?w = "?j1 - ?j0"
  let ?Mn = "(N::pairseq)[n]"  let ?x = "?j0 + q * ?w + s"
  let ?sp = "parent N 1 (?j0 + s) - ?j0"
  have w0: "0 < ?w" using j0lt by linarith
  have pread: "parent ?Mn 1 ?x = parent N 1 (?j0 + s) + q * ?w"
    by (rule oper_parent1_readback[OF L notzero hp i1z j0lt qn spos sw hpMs pMge])
  have ex: "entry ?Mn 1 ?x = entry N 1 (?j0 + s)"
    by (rule oper_d1pos_entry1[OF L notzero hp i1z j0lt qn sw])
  have parRb: "nextR N 1 (parent N 1 (?j0 + s)) (?j0 + s)"
    using hpMs unfolding hasParent_def parent_def by (rule theI')
  have plt_b: "parent N 1 (?j0 + s) < ?j0 + s" using parRb by (simp add: nextR_def nextrel1_def)
  have psp: "parent N 1 (?j0 + s) = ?j0 + ?sp" using pMge by simp
  have spw: "?sp < ?w" using plt_b sw psp by linarith
  have eparent: "entry ?Mn 1 (?j0 + q * ?w + ?sp) = entry N 1 (?j0 + ?sp)"
    by (rule oper_d1pos_entry1[OF L notzero hp i1z j0lt qn spw])
  have rca: "entry N 1 (parent N 1 (?j0 + s)) + 1 = entry N 1 (?j0 + s)"
    using condA hpMs unfolding RedCondA_def by blast
  have e1: "parent ?Mn 1 ?x = ?j0 + q * ?w + ?sp"
    using pread psp by (simp add: ac_simps)
  have lhs: "entry ?Mn 1 (parent ?Mn 1 ?x) = entry N 1 (parent N 1 (?j0 + s))"
  proof -
    have "entry ?Mn 1 (parent ?Mn 1 ?x) = entry ?Mn 1 (?j0 + q * ?w + ?sp)"
      using e1 by simp
    also have "\<dots> = entry N 1 (?j0 + ?sp)" using eparent .
    also have "\<dots> = entry N 1 (parent N 1 (?j0 + s))" using psp by simp
    finally show ?thesis .
  qed
  show ?thesis using lhs rca ex by simp
qed

text \<open>operCA assembled MODULO the two ST-PS structural facts hpMs (a block column
  of N[n] with a row-1 parent has its base parented in N) and gate (interior
  row-1 parents land at least j0).  RedCondA(N[n]) follows by operCA_tiling_cond:
  row-0 is operCA_tiling_row0 (green); within1 splits on the block offset
  s = (x-j0) mod w into operCA_block_start_row1 (s=0) and operCA_interior_row1
  (s>0, fed gate).  The remaining operCA residual is exactly hpMs + gate.\<close>

lemma operCA_via_gate_hpMs:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and condA: "RedCondA N"
    and n1: "1 \<le> n"
    and hpMs: "\<And>y. parent N 1 (Lng N - 1) \<le> y \<Longrightarrow> y < Lng ((N::pairseq)[n])
                 \<Longrightarrow> hasParent ((N::pairseq)[n]) 1 y
                 \<Longrightarrow> hasParent N 1 (parent N 1 (Lng N - 1)
                        + (y - parent N 1 (Lng N - 1))
                           mod (Lng N - 1 - parent N 1 (Lng N - 1)))"
    and gate: "\<And>u. parent N 1 (Lng N - 1) < u \<Longrightarrow> u < Lng N - 1 \<Longrightarrow> hasParent N 1 u
                 \<Longrightarrow> parent N 1 (Lng N - 1) \<le> parent N 1 u"
  shows "RedCondA ((N::pairseq)[n])"
proof -
  have j0lt': "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1" using j0lt i1z by simp
  show ?thesis
  proof (rule operCA_tiling_cond[OF L notzero hp j0lt' condA])
    fix x assume "hasParent ((N::pairseq)[n]) 0 x"
    thus "entry ((N::pairseq)[n]) 0 (parent ((N::pairseq)[n]) 0 x) + 1
            = entry ((N::pairseq)[n]) 0 x"
      by (rule operCA_tiling_row0[OF L notzero hp j0lt' condA n1])
  next
    fix x assume gex0: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> x"
      and hpx: "hasParent ((N::pairseq)[n]) 1 x"
    let ?j1 = "Lng N - 1"  let ?j0 = "parent N 1 ?j1"  let ?w = "?j1 - ?j0"
    let ?Mn = "(N::pairseq)[n]"
    have w0: "0 < ?w" using j0lt by linarith
    have gex: "?j0 \<le> x" using gex0 i1z by simp
    have lenMn: "Lng ?Mn = ?j0 + n * ?w"
      using oper_d1pos_LngM[OF L notzero hp i1z j0lt] by simp
    have parRx: "nextR ?Mn 1 (parent ?Mn 1 x) x"
      using hpx unfolding hasParent_def parent_def by (rule theI')
    have xMn: "x < Lng ?Mn" using parRx by (simp add: nextR_def nextrel1_def)
    define s where "s = (x - ?j0) mod ?w"
    define q where "q = (x - ?j0) div ?w"
    have sw: "s < ?w" using w0 by (simp add: s_def)
    have decomp0: "q * ?w + s = x - ?j0" by (simp add: q_def s_def div_mult_mod_eq)
    have decomp: "x = ?j0 + q * ?w + s" using decomp0 gex by simp
    have qwlt: "q * ?w < n * ?w"
    proof -
      have "?j0 + q * ?w + s < ?j0 + n * ?w" using xMn lenMn decomp by simp
      thus ?thesis by linarith
    qed
    have qn: "q < n"
    proof (rule ccontr)
      assume "\<not> q < n" hence "n \<le> q" by simp
      hence "n * ?w \<le> q * ?w" by (rule mult_le_mono1)
      thus False using qwlt by simp
    qed
    have hb: "hasParent N 1 (?j0 + s)"
      using hpMs[OF gex xMn hpx] by (simp add: s_def)
    show "entry ?Mn 1 (parent ?Mn 1 x) + 1 = entry ?Mn 1 x"
    proof (cases "s = 0")
      case True
      have xeq: "x = ?j0 + q * ?w" using decomp True by simp
      have hpMj0: "hasParent N 1 ?j0" using hb True by simp
      have parRj0: "nextR N 1 (parent N 1 ?j0) ?j0"
        using hpMj0 unfolding hasParent_def parent_def by (rule theI')
      have pjlt: "parent N 1 ?j0 < ?j0" using parRj0 by (simp add: nextR_def nextrel1_def)
      show ?thesis
        using operCA_block_start_row1[OF L notzero hp i1z j0lt qn hpMj0 pjlt condA] xeq by simp
    next
      case False
      have spos: "0 < s" using False by simp
      have base_int: "?j0 < ?j0 + s" using spos by simp
      have base_lt: "?j0 + s < ?j1" using sw by simp
      have pMge: "?j0 \<le> parent N 1 (?j0 + s)" using gate[OF base_int base_lt hb] .
      show ?thesis
        using operCA_interior_row1[OF L notzero hp i1z j0lt condA qn spos sw hb pMge] decomp
        by simp
    qed
  qed
qed

text \<open>The GATE ST-PS invariant: for N in ST_PS, every interior column u
  (j0 < u < j1, j0 = parent N 1 j1) with a row-1 parent has parent N 1 u >= j0.
  This is the first residual of operCA (operCA_via_gate_hpMs).  It is an ST_PS
  invariant (false for general reduced sequences, e.g. (0,0)(1,1)(2,1)(2,2)),
  proved by ST_PS.induct.  diag base is vacuous (immediate-predecessor parents);
  the oper step (tiling) is the readback-comparison residual (sorry below).\<close>

lemma gate_ST_PS:
  assumes "N \<in> ST_PS"
  shows "\<forall>u. parent N 1 (Lng N - 1) < u \<and> u < Lng N - 1 \<and> hasParent N 1 u
             \<longrightarrow> parent N 1 (Lng N - 1) \<le> parent N 1 u"
  using assms
proof (induct N rule: ST_PS.induct)
  case (diag u v)
  have uv: "u \<le> v" by (rule diag.hyps)
  show ?case
  proof (intro allI impI)
    fix z
    let ?M = "diagSeq u v"  let ?j1 = "Lng ?M - 1"
    assume H: "parent ?M 1 ?j1 < z \<and> z < ?j1 \<and> hasParent ?M 1 z"
    hence zlt: "z < ?j1" and zgt: "parent ?M 1 ?j1 < z" by auto
    have L1: "1 < Lng ?M" using zlt by linarith
    have lng: "Lng ?M = Suc v - u" by simp
    have j1lt: "Suc (?j1 - 1) < Suc v - u" using L1 lng by simp
    have nx: "nextR ?M 1 (?j1 - 1) (Suc (?j1 - 1))" by (rule nextR1_diagSeq[OF j1lt])
    have suc: "Suc (?j1 - 1) = ?j1" using L1 by simp
    have nxj1: "nextR ?M 1 (?j1 - 1) ?j1" using nx suc by simp
    have hpj1: "hasParent ?M 1 ?j1" unfolding hasParent_def using nxj1 nextR1_unique by blast
    have parR: "nextR ?M 1 (parent ?M 1 ?j1) ?j1"
      using hpj1 unfolding hasParent_def parent_def by (rule theI')
    have pj1: "parent ?M 1 ?j1 = ?j1 - 1" by (rule nextR1_unique[OF parR nxj1])
    have False using zgt zlt pj1 by linarith
    thus "parent ?M 1 ?j1 \<le> parent ?M 1 z" by simp
  qed
next
  case (oper M m)
  have IH: "\<forall>u. parent M 1 (Lng M - 1) < u \<and> u < Lng M - 1 \<and> hasParent M 1 u
                 \<longrightarrow> parent M 1 (Lng M - 1) \<le> parent M 1 u"
    using oper.hyps by blast
  show ?case
  proof (cases "Lng M - 1 = 0")
    case True
    have "(M::pairseq)[m] = M" using True by (simp add: oper_def Let_def)
    thus ?thesis using IH by simp
  next
    case False
    \<comment> \<open>TILING / Pred oper step: the readback-comparison residual.  For interior u'
       of M[m], parent (M[m]) 1 u' (interior/boundary readback, gated by IH=gate(M))
       compared to j0' = parent (M[m]) 1 (last) (readback of the last node).
       Empirically the ST_PS invariant (gate on M[m]) holds (fast_pss 5942/0).\<close>
    show ?thesis sorry
  qed
qed

text \<open>From the single scalar fact entry N1 j0 < entry N1(j0+s) (plus le0 N j0
  (j0+s), which always holds via the tree property), BOTH hpMs (the base j0+s has
  a row-1 parent) and pMge (that parent is >= j0) follow by m_5_1_parent_exists_2
  (existence of a parent in [j0, j0+s)) and nextR1_unique.  This collapses the two
  operCA residuals (hpMs + gate) for an interior base into ONE scalar inequality.\<close>

lemma base_parent_from_entry_lt:
  fixes N :: pairseq
  assumes NT: "N \<in> T_PS"
    and spos: "0 < s"
    and bL: "parent N 1 (Lng N - 1) + s < Lng N"
    and elt: "entry N 1 (parent N 1 (Lng N - 1))
                < entry N 1 (parent N 1 (Lng N - 1) + s)"
    and le0b: "le0 N (parent N 1 (Lng N - 1)) (parent N 1 (Lng N - 1) + s)"
  shows "hasParent N 1 (parent N 1 (Lng N - 1) + s)
       \<and> parent N 1 (Lng N - 1) \<le> parent N 1 (parent N 1 (Lng N - 1) + s)"
proof -
  let ?j0 = "parent N 1 (Lng N - 1)"
  have j0lt: "?j0 < ?j0 + s" using spos by simp
  have leRb: "leR N 0 ?j0 (?j0 + s)" using le0b by (simp add: leR_def)
  have "\<exists>j. ?j0 \<le> j \<and> j < ?j0 + s \<and> nextR N 1 j (?j0 + s)"
    by (rule m_5_1_parent_exists_2[OF NT j0lt bL elt leRb])
  then obtain j where jge: "?j0 \<le> j" and nr: "nextR N 1 j (?j0 + s)" by blast
  have hp: "hasParent N 1 (?j0 + s)"
    unfolding hasParent_def using nr nextR1_unique by blast
  have parR: "nextR N 1 (parent N 1 (?j0 + s)) (?j0 + s)"
    using hp unfolding hasParent_def parent_def by (rule theI')
  have peq: "parent N 1 (?j0 + s) = j" by (rule nextR1_unique[OF parR nr])
  show ?thesis using hp peq jge by simp
qed

end
