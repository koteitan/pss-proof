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


text \<open>cGTWF (conditional global tree wellformedness): for EVERY node k with a
  row-1 parent, the parents of nodes in the open interval (parent k, k) (that
  HAVE parents) land >= parent k -- i.e. the row-1 parent intervals are laminar
  (non-crossing).  This is the TRUE, Pred-stable refinement of the (false) GTWF
  (which wrongly required EXISTENCE of parents for ALL interior nodes).  It is an
  ST_PS invariant (false for general sequences, e.g. (0,0)(1,1)(2,1)(2,2); deep
  closure 18297/0), and being all-k it is preserved by Pred -- which resolves the
  last-node-bound non-monotonicity that blocked the gate's measure induction.
  The gate is the k = Lng N - 1 instance.  diag base vacuous (immediate-pred
  parents); the oper step is the (true, hence provable) readback residual.\<close>

abbreviation cGTWF :: "pairseq \<Rightarrow> bool" where
  "cGTWF M \<equiv> (\<forall>k. hasParent M 1 k
                 \<longrightarrow> (\<forall>u. parent M 1 k < u \<and> u < k \<and> hasParent M 1 u
                          \<longrightarrow> parent M 1 k \<le> parent M 1 u))"

text \<open>Eglobal' (the second ST_PS invariant, carried jointly with cGTWF): for every
  row-0 Next edge a = parent M 0 b -> b WHERE b IS ROW-1-TRIVIAL (entry M 1 b = 0),
  any interior column c (a < c < b) whose row-1 parent escapes the block
  (parent M 1 c < a) has entry M 1 a <= entry M 1 c.  Genuine ST_PS invariant --
  NOT implied by cGTWF/reduced/standard, and the entry-1-trivial restriction on b
  is ESSENTIAL (the unrestricted form is false on ST_PS at row-1-positive b).  The
  b = j1 instance for an idx1=0 sequence (entry M 1 j1 = 0) is exactly what
  cgtw_tile_d0zero needs.\<close>

abbreviation Eglobal :: "pairseq \<Rightarrow> bool" where
  "Eglobal M \<equiv> (\<forall>b. hasParent M 0 b \<and> entry M 1 b = 0
                 \<longrightarrow> (\<forall>c. parent M 0 b < c \<and> c < b \<and> hasParent M 1 c
                          \<and> parent M 1 c < parent M 0 b
                          \<longrightarrow> entry M 1 (parent M 0 b) \<le> entry M 1 c))"

text \<open>Row-0 analogue of @{thm [source] nextR1_pred_agree}: on the shared prefix
  [0, Lng K-2] the row-0 Next edge agrees between K and Pred K (via
  @{thm [source] nextrel0_prefix_imp}).  Used for Eglobal' Pred-stability.\<close>

lemma nextR0_pred_agree:
  assumes L: "1 < Lng K" and xc: "x \<le> Lng K - 2" and yc: "y \<le> Lng K - 2"
  shows "nextR K 0 x y \<longleftrightarrow> nextR (Pred K) 0 x y"
proof -
  have pb: "Pred K = butlast K" using L by (simp add: Pred_def)
  have lbl: "length (butlast K) = Lng K - 1" by simp
  let ?c = "Lng K - 2"
  have agreeKP: "\<And>j. j \<le> ?c \<Longrightarrow> K ! j = (Pred K) ! j"
  proof -
    fix j assume "j \<le> ?c"
    hence jl: "j < length (butlast K)" using L lbl by linarith
    show "K ! j = (Pred K) ! j" using pb jl by (simp add: nth_butlast)
  qed
  have agreePK: "\<And>j. j \<le> ?c \<Longrightarrow> (Pred K) ! j = K ! j" using agreeKP by simp
  have cM: "?c < Lng K" using L by simp
  have cN: "?c < Lng (Pred K)" using L pb lbl by simp
  show ?thesis
  proof
    assume "nextR K 0 x y"
    hence h: "nextrel0 K x y" by (simp add: nextR_def)
    have "nextrel0 (Pred K) x y"
      by (rule nextrel0_prefix_imp[OF agreeKP cN xc yc h])
    thus "nextR (Pred K) 0 x y" by (simp add: nextR_def)
  next
    assume "nextR (Pred K) 0 x y"
    hence h: "nextrel0 (Pred K) x y" by (simp add: nextR_def)
    have "nextrel0 K x y"
      by (rule nextrel0_prefix_imp[OF agreePK cM xc yc h])
    thus "nextR K 0 x y" by (simp add: nextR_def)
  qed
qed

text \<open>cGTWF is preserved by Pred: Pred M is the prefix [0, Lng M-2] of M, on which
  \<open>nextR _ 1\<close> (hence parent / hasParent) agrees (@{thm [source] nextR1_pred_agree}),
  so every k, u of Pred M keep their M-parents and the cGTWF clause transfers from
  cGTWF M.  The Pred branch of the cGTWF oper step.\<close>

lemma cgtw_pred:
  assumes MT: "M \<in> T_PS" and L: "1 < Lng M" and cg: "cGTWF M"
  shows "cGTWF (Pred M)"
proof (intro allI impI)
  fix k u
  assume hpk: "hasParent (Pred M) 1 k"
     and H: "parent (Pred M) 1 k < u \<and> u < k \<and> hasParent (Pred M) 1 u"
  from H have ppku: "parent (Pred M) 1 k < u" and uk: "u < k"
     and hpu: "hasParent (Pred M) 1 u" by auto
  have lp: "Lng (Pred M) = Lng M - 1" using L by (simp add: Pred_def)
  have parPk: "nextR (Pred M) 1 (parent (Pred M) 1 k) k"
    using hpk unfolding hasParent_def parent_def by (rule theI')
  have klt: "k < Lng (Pred M)" using parPk by (simp add: nextR_def nextrel1_def)
  have kc: "k \<le> Lng M - 2" using klt lp by linarith
  have ppk_lt: "parent (Pred M) 1 k < k" using parPk by (simp add: nextR_def nextrel1_def)
  have ppkc: "parent (Pred M) 1 k \<le> Lng M - 2" using ppk_lt kc by linarith
  have parMk: "nextR M 1 (parent (Pred M) 1 k) k"
    using nextR1_pred_agree[OF L ppkc kc] parPk by simp
  have hpMk: "hasParent M 1 k" unfolding hasParent_def using parMk nextR1_unique by blast
  have parMk': "nextR M 1 (parent M 1 k) k"
    using hpMk unfolding hasParent_def parent_def by (rule theI')
  have peqk: "parent M 1 k = parent (Pred M) 1 k" by (rule nextR1_unique[OF parMk' parMk])
  have uc: "u \<le> Lng M - 2" using uk kc by linarith
  have parPu: "nextR (Pred M) 1 (parent (Pred M) 1 u) u"
    using hpu unfolding hasParent_def parent_def by (rule theI')
  have ppu_lt: "parent (Pred M) 1 u < u" using parPu by (simp add: nextR_def nextrel1_def)
  have ppuc: "parent (Pred M) 1 u \<le> Lng M - 2" using ppu_lt uc by linarith
  have parMu: "nextR M 1 (parent (Pred M) 1 u) u"
    using nextR1_pred_agree[OF L ppuc uc] parPu by simp
  have hpMu: "hasParent M 1 u" unfolding hasParent_def using parMu nextR1_unique by blast
  have parMu': "nextR M 1 (parent M 1 u) u"
    using hpMu unfolding hasParent_def parent_def by (rule theI')
  have pequ: "parent M 1 u = parent (Pred M) 1 u" by (rule nextR1_unique[OF parMu' parMu])
  have "parent M 1 k < u \<and> u < k \<and> hasParent M 1 u" using ppku uk hpMu peqk by simp
  hence "parent M 1 k \<le> parent M 1 u" using cg hpMk by blast
  thus "parent (Pred M) 1 k \<le> parent (Pred M) 1 u" using peqk pequ by simp
qed

text \<open>Eglobal' is preserved by Pred: every row-0 edge a->b and interior column c of
  Pred M lies in the shared prefix [0, Lng M-2], where row-0/row-1 Next edges and
  entries agree with M (@{thm [source] nextR0_pred_agree}, @{thm [source]
  nextR1_pred_agree}); the Eglobal' clause then transfers from Eglobal M.\<close>

lemma Eglobal_pred:
  assumes L: "1 < Lng M" and eg: "Eglobal M"
  shows "Eglobal (Pred M)"
proof (intro allI impI)
  fix b c
  assume Hb: "hasParent (Pred M) 0 b \<and> entry (Pred M) 1 b = 0"
     and H: "parent (Pred M) 0 b < c \<and> c < b \<and> hasParent (Pred M) 1 c
              \<and> parent (Pred M) 1 c < parent (Pred M) 0 b"
  from Hb have hpb: "hasParent (Pred M) 0 b" and eb_pred: "entry (Pred M) 1 b = 0" by auto
  from H have pbc: "parent (Pred M) 0 b < c" and cb: "c < b"
    and hpc: "hasParent (Pred M) 1 c" and pc_lt: "parent (Pred M) 1 c < parent (Pred M) 0 b" by auto
  let ?c2 = "Lng M - 2"
  have lpm: "Lng (Pred M) = Lng M - 1" using L by (simp add: Pred_def)
  have ent: "\<And>i j. j \<le> ?c2 \<Longrightarrow> entry (Pred M) i j = entry M i j"
  proof -
    fix i j assume jc: "j \<le> ?c2"
    have pb: "Pred M = butlast M" using L by (simp add: Pred_def)
    have "j < length (butlast M)" using jc L by simp
    thus "entry (Pred M) i j = entry M i j" using pb by (simp add: entry_def nth_butlast)
  qed
  \<comment> \<open>row-0 edge a -> b lifts to M\<close>
  have parPb: "nextR (Pred M) 0 (parent (Pred M) 0 b) b"
    using hpb unfolding hasParent_def parent_def by (rule theI')
  have blt: "b < Lng (Pred M)" using parPb by (simp add: nextR_def nextrel0_def)
  have bc2: "b \<le> ?c2" using blt lpm by linarith
  have pb_lt: "parent (Pred M) 0 b < b" using parPb by (simp add: nextR_def nextrel0_def)
  have pbc2: "parent (Pred M) 0 b \<le> ?c2" using pb_lt bc2 by linarith
  have parMb: "nextR M 0 (parent (Pred M) 0 b) b"
    using nextR0_pred_agree[OF L pbc2 bc2] parPb by simp
  have hpMb: "hasParent M 0 b" unfolding hasParent_def using parMb idxsum_parent0_unique by blast
  have parMb': "nextR M 0 (parent M 0 b) b"
    using hpMb unfolding hasParent_def parent_def by (rule theI')
  have peqb: "parent M 0 b = parent (Pred M) 0 b" by (rule idxsum_parent0_unique[OF parMb' parMb])
  \<comment> \<open>row-1 parent of c lifts to M\<close>
  have cc2: "c \<le> ?c2" using cb bc2 by linarith
  have parPc: "nextR (Pred M) 1 (parent (Pred M) 1 c) c"
    using hpc unfolding hasParent_def parent_def by (rule theI')
  have pc_lt': "parent (Pred M) 1 c < c" using parPc by (simp add: nextR_def nextrel1_def)
  have pcc2: "parent (Pred M) 1 c \<le> ?c2" using pc_lt' cc2 by linarith
  have parMc: "nextR M 1 (parent (Pred M) 1 c) c"
    using nextR1_pred_agree[OF L pcc2 cc2] parPc by simp
  have hpMc: "hasParent M 1 c" unfolding hasParent_def using parMc nextR1_unique by blast
  have parMc': "nextR M 1 (parent M 1 c) c"
    using hpMc unfolding hasParent_def parent_def by (rule theI')
  have peqc: "parent M 1 c = parent (Pred M) 1 c" by (rule nextR1_unique[OF parMc' parMc])
  \<comment> \<open>apply Eglobal M\<close>
  have a_lt_c: "parent M 0 b < c" using pbc peqb by simp
  have pc_lt_a: "parent M 1 c < parent M 0 b" using pc_lt peqb peqc by simp
  have eb: "entry M 1 b = 0" using eb_pred ent[where i=1 and j=b] bc2 by simp
  have eM: "entry M 1 (parent M 0 b) \<le> entry M 1 c"
    using eg hpMb eb a_lt_c cb hpMc pc_lt_a by blast
  have e1: "entry (Pred M) 1 (parent (Pred M) 0 b) = entry M 1 (parent M 0 b)"
    using ent[where i=1 and j="parent (Pred M) 0 b"] pbc2 peqb by simp
  have e2: "entry (Pred M) 1 c = entry M 1 c"
    using ent[where i=1 and j=c] cc2 by simp
  show "entry (Pred M) 1 (parent (Pred M) 0 b) \<le> entry (Pred M) 1 c"
    using eM e1 e2 by simp
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

text \<open>§6.7 oper-tiling REVERSE READBACK — the \<open>parent_inblock\<close> DICHOTOMY: the row-1
  parent of an INTERIOR column \<open>y = j\<^sub>0+q\<cdot>w+s\<close> (\<open>0<s<w\<close>) of \<open>N[n]\<close> lies either in
  the PREFIX (\<open>< j\<^sub>0\<close>) or in y's OWN block \<open>q\<close> (\<open>(p-j\<^sub>0) div w = q\<close>); never in a
  strictly-earlier block.  Proof: the block-q START c0 = j0+q*w ALWAYS reaches y
  (le0 N j0 (j0+s) via the ancestor chain, lifted by
  @{thm [source] oper_d0zero_le0_slice_lift}) and sits above p, so the parent's
  valley forces (row-1) entry y <= entry N1 j0 (the fact 'star').  Then
  sp = (p-j0) mod w = 0 contradicts the parent edge directly; sp > 0 lifts p to the
  block-q start by the le0-ancestor chain and reflects (the H1 brick
  @{thm [source] oper_d1pos_le0_cross_back}) to le0 N (j0+sp) j1, whose
  nextrel1 N j0 j1 valley gives entry N1 j1 <= entry N1 (j0+sp) = entry1 p
  < entry1 y <= entry N1 j0, contradicting entry N1 j0 < entry N1 j1.  Empirically
  5544/5544 block-source parents are same-block, 0/5778 base-offset violations.
  Unblocks the reverse readback (hpMs, oper_interior_hasParent_base below).\<close>

lemma oper_interior_parent_inblock:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and qn: "q < n"
    and spos: "0 < s"
    and sw: "s < Lng N - 1 - parent N 1 (Lng N - 1)"
    and hpy: "hasParent ((N::pairseq)[n]) 1
                (parent N 1 (Lng N - 1) + q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s)"
  shows "parent ((N::pairseq)[n]) 1
            (parent N 1 (Lng N - 1) + q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s)
          < parent N 1 (Lng N - 1)
       \<or> (parent N 1 (Lng N - 1)
            \<le> parent ((N::pairseq)[n]) 1
                 (parent N 1 (Lng N - 1) + q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s)
          \<and> (parent ((N::pairseq)[n]) 1
                 (parent N 1 (Lng N - 1) + q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s)
              - parent N 1 (Lng N - 1))
             div (Lng N - 1 - parent N 1 (Lng N - 1)) = q)"
proof (rule ccontr)
  let ?j1 = "Lng N - 1"  let ?j0 = "parent N 1 ?j1"  let ?w = "?j1 - ?j0"
  let ?Mn = "(N::pairseq)[n]"  let ?y = "?j0 + q * ?w + s"  let ?c0 = "?j0 + q * ?w"
  let ?p = "parent ?Mn 1 ?y"
  assume "\<not> (?p < ?j0 \<or> (?j0 \<le> ?p \<and> (?p - ?j0) div ?w = q))"
  hence pge: "?j0 \<le> ?p" and qpne: "(?p - ?j0) div ?w \<noteq> q" by auto
  have w0: "0 < ?w" using j0lt by linarith
  have n0: "0 < n" using qn by simp
  have j0lt': "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1" using j0lt i1z by simp
  have NT: "N \<in> T_PS" using L by (cases N) (auto simp: T_PS_def)
  \<comment> \<open>the parent edge of y in N[n], its valley\<close>
  have parRy: "nextR ?Mn 1 ?p ?y" using hpy unfolding hasParent_def parent_def by (rule theI')
  have nr1y: "nextrel1 ?Mn ?p ?y" using parRy by (simp add: nextR_def)
  have ple: "?p < ?y" using nr1y by (simp add: nextrel1_def)
  have le0py: "le0 ?Mn ?p ?y" using nr1y by (simp add: nextrel1_def)
  have epy: "entry ?Mn 1 ?p < entry ?Mn 1 ?y" using nr1y by (simp add: nextrel1_def)
  have valleyP: "\<And>j. ?p < j \<Longrightarrow> le0 ?Mn j ?y \<Longrightarrow> entry ?Mn 1 ?y \<le> entry ?Mn 1 j"
    using nr1y unfolding nextrel1_def by blast
  \<comment> \<open>block decomposition of p; qp < q\<close>
  define qp where "qp = (?p - ?j0) div ?w"
  define sp where "sp = (?p - ?j0) mod ?w"
  have spw: "sp < ?w" using w0 by (simp add: sp_def)
  have pdecomp: "?p = ?j0 + qp * ?w + sp"
  proof -
    have "?j0 + qp * ?w + sp = ?j0 + ((?p - ?j0) div ?w * ?w + (?p - ?j0) mod ?w)"
      unfolding qp_def sp_def by simp
    also have "\<dots> = ?j0 + (?p - ?j0)" by (simp add: div_mult_mod_eq)
    also have "\<dots> = ?p" using pge by simp
    finally show ?thesis by simp
  qed
  have qple: "qp \<le> q"
  proof (rule ccontr)
    assume "\<not> qp \<le> q" hence "q + 1 \<le> qp" by simp
    hence "(q + 1) * ?w \<le> qp * ?w" by (rule mult_le_mono1)
    hence "?j0 + q * ?w + ?w \<le> ?p" using pdecomp by simp
    moreover have "?p < ?j0 + q * ?w + s" using ple by simp
    ultimately show False using sw by linarith
  qed
  have qpne': "qp \<noteq> q" using qpne qp_def by simp
  have qq: "qp < q" using le_neq_implies_less[OF qple qpne'] .
  have qpn: "qp < n" using qq qn by simp
  have pc0: "?p < ?c0"
  proof -
    have qp1: "qp + 1 \<le> q" using qq by simp
    have "qp * ?w + sp < (qp + 1) * ?w" using spw by simp
    also have "\<dots> \<le> q * ?w" using qp1 by (rule mult_le_mono1)
    finally show ?thesis using pdecomp by simp
  qed
  \<comment> \<open>the parent edge nextrel1 N j0 j1 (the block period) and its valley\<close>
  have hpj1: "hasParent N 1 ?j1" using hp i1z by simp
  have parj1: "nextR N 1 ?j0 ?j1" using hpj1 unfolding hasParent_def parent_def by (rule theI')
  have nr1j1: "nextrel1 N ?j0 ?j1" using parj1 by (simp add: nextR_def)
  have ej0j1: "entry N 1 ?j0 < entry N 1 ?j1" using nr1j1 by (simp add: nextrel1_def)
  have le0j0j1: "le0 N ?j0 ?j1" using nr1j1 by (simp add: nextrel1_def)
  have valleyJ1: "\<And>j. ?j0 < j \<Longrightarrow> le0 N j ?j1 \<Longrightarrow> entry N 1 ?j1 \<le> entry N 1 j"
    using nr1j1 unfolding nextrel1_def by blast
  \<comment> \<open>(*) the block-q START c0 always reaches y, lies above p: entry1 y <= entry N1 j0\<close>
  have basej1: "?j0 + s \<le> ?j1" using sw by simp
  have leRj0j1: "leR N 0 ?j0 ?j1" using le0j0j1 by (simp add: leR_def)
  have le0j0base: "le0 N ?j0 (?j0 + s)"
    using m_5_1_ancestor_tree_1[OF NT leRj0j1 le_add1 basej1] by (simp add: leR_def)
  have a0: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> ?j0" using i1z by simp
  have bj1: "?j0 + s < Lng N - 1" using sw by simp
  have c0lift: "le0 ?Mn
       (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
          + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
          + (?j0 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
       (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
          + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
          + ((?j0 + s) - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
    by (rule oper_d0zero_le0_slice_lift[OF L notzero hp j0lt' qn a0 bj1 le0j0base])
  have le0c0y: "le0 ?Mn ?c0 ?y" using c0lift i1z by simp
  have e_c0: "entry ?Mn 1 ?c0 = entry N 1 ?j0"
    using oper_d1pos_entry1[OF L notzero hp i1z j0lt qn w0] by simp
  have star: "entry ?Mn 1 ?y \<le> entry N 1 ?j0"
    using valleyP[OF pc0 le0c0y] e_c0 by simp
  \<comment> \<open>periodic row-1 at p\<close>
  have e_p: "entry ?Mn 1 ?p = entry N 1 (?j0 + sp)"
    using oper_d1pos_entry1[OF L notzero hp i1z j0lt qpn spw] pdecomp by simp
  show False
  proof (cases "sp = 0")
    case True
    have "entry N 1 ?j0 < entry ?Mn 1 ?y" using epy e_p True by simp
    thus False using star by simp
  next
    case False
    hence sppos: "0 < sp" by simp
    \<comment> \<open>le0(N[n]) p c0 (ancestor), then H1 reflect to le0 N (j0+sp) j1\<close>
    have j0ltMn: "?j0 < Lng ?Mn"
      using oper_d1pos_LngM[OF L notzero hp i1z j0lt] n0 w0 by simp
    have NnT: "?Mn \<in> T_PS" using j0ltMn by (cases ?Mn) (auto simp: T_PS_def)
    have pc0': "?p \<le> ?c0" using pc0 by simp
    have c0y: "?c0 \<le> ?y" by simp
    have le0pc0: "le0 ?Mn ?p ?c0"
    proof -
      have "leR ?Mn 0 ?p ?c0"
        by (rule m_5_1_ancestor_tree_1[OF NnT _ pc0' c0y]) (use le0py in \<open>simp add: leR_def\<close>)
      thus ?thesis by (simp add: leR_def)
    qed
    have reachH1: "le0 ?Mn (?j0 + qp * ?w + sp) (?j0 + q * ?w)" using le0pc0 pdecomp by simp
    have le0spj1: "le0 N (?j0 + sp) ?j1"
      by (rule oper_d1pos_le0_cross_back[OF L notzero hp i1z j0lt qq qn spw reachH1])
    have j0lt_sp: "?j0 < ?j0 + sp" using sppos by simp
    have ge1: "entry N 1 ?j1 \<le> entry N 1 (?j0 + sp)" using valleyJ1[OF j0lt_sp le0spj1] .
    have "entry N 1 (?j0 + sp) < entry N 1 ?j0" using e_p epy star by simp
    hence "entry N 1 ?j1 < entry N 1 ?j0" using ge1 by simp
    thus False using ej0j1 by simp
  qed
qed


text \<open>§6.7 oper-tiling REVERSE READBACK — hpMs (existence leg): an INTERIOR column
  \<open>y = j\<^sub>0+q\<cdot>w+s\<close> (\<open>0<s<w\<close>) of \<open>N[n]\<close> with a row-1 parent has its base \<open>j\<^sub>0+s\<close>
  parented in \<open>N\<close>.  The \<open>N[n]\<close>-parent \<open>p\<close> reflects (its base \<open>b\<close>) to a strictly
  smaller-row1 \<open>le0\<close>-predecessor of \<open>j\<^sub>0+s\<close> in \<open>N\<close>, whence
  @{thm [source] m_5_1_parent_exists_2} gives a parent.  PREFIX \<open>p<j\<^sub>0\<close>: \<open>le0 N p j\<^sub>0\<close>
  (ancestor chain @{thm [source] m_5_1_ancestor_tree_1} + prefix verbatim
  @{thm [source] oper_d1pos_le0_prefix_back} at block 0) then
  \<open>le0 N j\<^sub>0 (j\<^sub>0+s)\<close> (ancestor inside \<open>nextrel1 N j\<^sub>0 j\<^sub>1\<close>) by
  @{thm [source] le0_trans}; row-1 verbatim.  SAME-BLOCK \<open>(p-j\<^sub>0) div w = q\<close>:
  \<open>sp = (p-j\<^sub>0) mod w < s\<close> from \<open>p<y\<close>, same-block reflection
  @{thm [source] oper_d1pos_le0_base_back}; periodic row-1
  @{thm [source] oper_d1pos_entry1}.  Block classification by
  @{thm [source] oper_interior_parent_inblock}.\<close>

lemma oper_interior_hasParent_base:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and qn: "q < n"
    and spos: "0 < s"
    and sw: "s < Lng N - 1 - parent N 1 (Lng N - 1)"
    and hpy: "hasParent ((N::pairseq)[n]) 1
                (parent N 1 (Lng N - 1) + q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s)"
  shows "hasParent N 1 (parent N 1 (Lng N - 1) + s)"
proof -
  let ?j1 = "Lng N - 1"  let ?j0 = "parent N 1 ?j1"  let ?w = "?j1 - ?j0"
  let ?Mn = "(N::pairseq)[n]"  let ?y = "?j0 + q * ?w + s"  let ?base = "?j0 + s"
  let ?p = "parent ?Mn 1 ?y"
  have w0: "0 < ?w" using j0lt by linarith
  have n0: "0 < n" using qn by simp
  have NT: "N \<in> T_PS" using L by (cases N) (auto simp: T_PS_def)
  \<comment> \<open>the parent edge of \<open>y\<close> in \<open>N[n]\<close>\<close>
  have parRy: "nextR ?Mn 1 ?p ?y"
    using hpy unfolding hasParent_def parent_def by (rule theI')
  have nr1y: "nextrel1 ?Mn ?p ?y" using parRy by (simp add: nextR_def)
  have ple: "?p < ?y" using nr1y by (simp add: nextrel1_def)
  have le0py: "le0 ?Mn ?p ?y" using nr1y by (simp add: nextrel1_def)
  have epy: "entry ?Mn 1 ?p < entry ?Mn 1 ?y" using nr1y by (simp add: nextrel1_def)
  \<comment> \<open>row-1 of \<open>y\<close> = row-1 of the base\<close>
  have ey: "entry ?Mn 1 ?y = entry N 1 ?base"
    by (rule oper_d1pos_entry1[OF L notzero hp i1z j0lt qn sw])
  \<comment> \<open>\<open>base < Lng N\<close>, and \<open>le0 N j\<^sub>0 base\<close> (ancestor inside the \<open>nextrel1 N j\<^sub>0 j\<^sub>1\<close> edge)\<close>
  have baseLt: "?base < Lng N" using sw j0lt by linarith
  have hpj1: "hasParent N 1 ?j1" using hp i1z by simp
  have parj1: "nextR N 1 ?j0 ?j1" using hpj1 unfolding hasParent_def parent_def by (rule theI')
  have nr1j1: "nextrel1 N ?j0 ?j1" using parj1 by (simp add: nextR_def)
  have le0j0j1: "le0 N ?j0 ?j1" using nr1j1 by (simp add: nextrel1_def)
  have basej1: "?base \<le> ?j1" using sw by simp
  have leRj0j1: "leR N 0 ?j0 ?j1" using le0j0j1 by (simp add: leR_def)
  have j0base: "?j0 \<le> ?base" by simp
  have le0j0base: "le0 N ?j0 ?base"
    using m_5_1_ancestor_tree_1[OF NT leRj0j1 j0base basej1] by (simp add: leR_def)
  \<comment> \<open>It suffices to exhibit a strictly-smaller-row1 \<open>le0\<close>-predecessor \<open>b\<close> of \<open>base\<close>\<close>
  have suff: "\<And>b. b < ?base \<Longrightarrow> entry N 1 b < entry N 1 ?base \<Longrightarrow> le0 N b ?base
                  \<Longrightarrow> hasParent N 1 ?base"
  proof -
    fix b assume bb: "b < ?base" and eb: "entry N 1 b < entry N 1 ?base"
      and le0b: "le0 N b ?base"
    have leRb: "leR N 0 b ?base" using le0b by (simp add: leR_def)
    have "\<exists>j. b \<le> j \<and> j < ?base \<and> nextR N 1 j ?base"
      by (rule m_5_1_parent_exists_2[OF NT bb baseLt eb leRb])
    then obtain j where nr: "nextR N 1 j ?base" by blast
    show "hasParent N 1 ?base"
      unfolding hasParent_def using nr nextR1_unique by blast
  qed
  show ?thesis
  proof (cases "?p < ?j0")
    case True
    \<comment> \<open>PREFIX: \<open>b = p\<close>; \<open>le0 N p j\<^sub>0\<close> via ancestor + prefix verbatim, then \<open>le0 N p base\<close>\<close>
    have pj0: "?p \<le> ?j0" using True by simp
    have j0y: "?j0 \<le> ?y" by simp
    have lenMn: "Lng ?Mn = ?j0 + n * ?w"
      using oper_d1pos_LngM[OF L notzero hp i1z j0lt] by simp
    have j0ltMn: "?j0 < Lng ?Mn" using lenMn n0 w0 by simp
    have NnT: "?Mn \<in> T_PS" using j0ltMn by (cases ?Mn) (auto simp: T_PS_def)
    have le0pj0Mn: "le0 ?Mn ?p ?j0"
    proof -
      have "leR ?Mn 0 ?p ?j0"
        by (rule m_5_1_ancestor_tree_1[OF NnT _ pj0 j0y]) (use le0py in \<open>simp add: leR_def\<close>)
      thus ?thesis by (simp add: leR_def)
    qed
    \<comment> \<open>reflect to \<open>N\<close> via the prefix-back brick with block \<open>q = 0\<close> (target \<open>j\<^sub>0 + 0\<cdot>w = j\<^sub>0\<close>)\<close>
    have reach0: "le0 ?Mn ?p (?j0 + 0 * ?w)" using le0pj0Mn by simp
    have le0pj0: "le0 N ?p ?j0"
      by (rule oper_d1pos_le0_prefix_back[OF L notzero hp i1z j0lt n0 True reach0])
    have le0pbase: "le0 N ?p ?base" by (rule le0_trans[OF le0pj0 le0j0base])
    have ep: "entry ?Mn 1 ?p = entry N 1 ?p"
      by (rule operB_gen_entry_prefix[OF L notzero hp]) (use True i1z in simp)
    have epbase: "entry N 1 ?p < entry N 1 ?base" using epy ey ep by simp
    have pbase: "?p < ?base" using True spos by simp
    show ?thesis by (rule suff[OF pbase epbase le0pbase])
  next
    case False
    hence pge: "?j0 \<le> ?p" by simp
    \<comment> \<open>SAME-BLOCK (by the dichotomy): \<open>p = j\<^sub>0+q\<cdot>w+sp\<close>, \<open>sp = (p-j\<^sub>0) mod w < s\<close>\<close>
    have dq: "(?p - ?j0) div ?w = q"
      using oper_interior_parent_inblock[OF L notzero hp i1z j0lt qn spos sw hpy] pge
      by simp
    define sp where "sp = (?p - ?j0) mod ?w"
    have spw: "sp < ?w" using w0 by (simp add: sp_def)
    have pdecomp: "?p = ?j0 + q * ?w + sp"
    proof -
      have "?j0 + q * ?w + sp = ?j0 + ((?p - ?j0) div ?w * ?w + (?p - ?j0) mod ?w)"
        using dq sp_def by simp
      also have "\<dots> = ?j0 + (?p - ?j0)" by (simp add: div_mult_mod_eq)
      also have "\<dots> = ?p" using pge by simp
      finally show ?thesis by simp
    qed
    have sps: "sp < s" using ple pdecomp by simp
    \<comment> \<open>same-block le0 reflection and periodic row-1\<close>
    have reachblk: "le0 ?Mn (?j0 + q * ?w + sp) (?j0 + q * ?w + s)" using le0py pdecomp by simp
    have le0bbase: "le0 N (?j0 + sp) ?base"
      by (rule oper_d1pos_le0_base_back[OF L notzero hp i1z j0lt qn sps sw reachblk])
    have ebp: "entry ?Mn 1 (?j0 + q * ?w + sp) = entry N 1 (?j0 + sp)"
      by (rule oper_d1pos_entry1[OF L notzero hp i1z j0lt qn spw])
    have ebase: "entry N 1 (?j0 + sp) < entry N 1 ?base"
      using epy ey ebp pdecomp by simp
    have bbase: "?j0 + sp < ?base" using sps by simp
    show ?thesis by (rule suff[OF bbase ebase le0bbase])
  qed
qed

text \<open>§6.7 oper-tiling REVERSE READBACK -- hpMs at a BLOCK START (s = 0): a block
  start j0+q*w of N[n] with a row-1 parent forces j0 = parent N 1 j1 itself to be
  parented in N.  Same valley argument as the dichotomy: an earlier-block parent p
  (j0 <= p) reflects (H1 @{thm [source] oper_d1pos_le0_cross_back}) to le0 N (j0+sp) j1,
  contradicting the nextrel1 N j0 j1 valley; hence p < j0 and the prefix-verbatim
  le0 N p j0 (@{thm [source] oper_d1pos_le0_prefix_back}) gives a strictly-smaller-row1
  predecessor of j0, whence @{thm [source] m_5_1_parent_exists_2}.\<close>

lemma oper_blockstart_hasParent_j0:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and qn: "q < n"
    and hpy: "hasParent ((N::pairseq)[n]) 1
                (parent N 1 (Lng N - 1) + q * (Lng N - 1 - parent N 1 (Lng N - 1)))"
  shows "hasParent N 1 (parent N 1 (Lng N - 1))"
proof -
  let ?j1 = "Lng N - 1"  let ?j0 = "parent N 1 ?j1"  let ?w = "?j1 - ?j0"
  let ?Mn = "(N::pairseq)[n]"  let ?y = "?j0 + q * ?w"  let ?p = "parent ?Mn 1 ?y"
  have w0: "0 < ?w" using j0lt by linarith
  have n0: "0 < n" using qn by simp
  have NT: "N \<in> T_PS" using L by (cases N) (auto simp: T_PS_def)
  have j0Lt: "?j0 < Lng N" using j0lt by linarith
  \<comment> \<open>the parent edge of the block start\<close>
  have parRy: "nextR ?Mn 1 ?p ?y" using hpy unfolding hasParent_def parent_def by (rule theI')
  have nr1y: "nextrel1 ?Mn ?p ?y" using parRy by (simp add: nextR_def)
  have ple: "?p < ?y" using nr1y by (simp add: nextrel1_def)
  have le0py: "le0 ?Mn ?p ?y" using nr1y by (simp add: nextrel1_def)
  have epy: "entry ?Mn 1 ?p < entry ?Mn 1 ?y" using nr1y by (simp add: nextrel1_def)
  have ey0: "entry ?Mn 1 ?y = entry N 1 ?j0"
    using oper_d1pos_entry1[OF L notzero hp i1z j0lt qn w0] by simp
  \<comment> \<open>the block period edge nextrel1 N j0 j1 and its valley\<close>
  have hpj1: "hasParent N 1 ?j1" using hp i1z by simp
  have parj1: "nextR N 1 ?j0 ?j1" using hpj1 unfolding hasParent_def parent_def by (rule theI')
  have nr1j1: "nextrel1 N ?j0 ?j1" using parj1 by (simp add: nextR_def)
  have ej0j1: "entry N 1 ?j0 < entry N 1 ?j1" using nr1j1 by (simp add: nextrel1_def)
  have valleyJ1: "\<And>j. ?j0 < j \<Longrightarrow> le0 N j ?j1 \<Longrightarrow> entry N 1 ?j1 \<le> entry N 1 j"
    using nr1j1 unfolding nextrel1_def by blast
  \<comment> \<open>p < j0: an earlier-block parent is excluded by the j0-j1 valley\<close>
  have plt_j0: "?p < ?j0"
  proof (rule ccontr)
    assume "\<not> ?p < ?j0" hence pge: "?j0 \<le> ?p" by simp
    define qp where "qp = (?p - ?j0) div ?w"
    define sp where "sp = (?p - ?j0) mod ?w"
    have spw: "sp < ?w" using w0 by (simp add: sp_def)
    have pdecomp: "?p = ?j0 + qp * ?w + sp"
    proof -
      have "?j0 + qp * ?w + sp = ?j0 + ((?p - ?j0) div ?w * ?w + (?p - ?j0) mod ?w)"
        unfolding qp_def sp_def by simp
      also have "\<dots> = ?j0 + (?p - ?j0)" by (simp add: div_mult_mod_eq)
      also have "\<dots> = ?p" using pge by simp
      finally show ?thesis by simp
    qed
    have qq: "qp < q"
    proof (rule ccontr)
      assume "\<not> qp < q" hence "q \<le> qp" by simp
      hence "q * ?w \<le> qp * ?w" by (rule mult_le_mono1)
      hence "?j0 + q * ?w \<le> ?p" using pdecomp by linarith
      moreover have "?p < ?j0 + q * ?w" using ple by simp
      ultimately show False by linarith
    qed
    have qpn: "qp < n" using qq qn by simp
    have e_p: "entry ?Mn 1 ?p = entry N 1 (?j0 + sp)"
      using oper_d1pos_entry1[OF L notzero hp i1z j0lt qpn spw] pdecomp by simp
    have reachH1: "le0 ?Mn (?j0 + qp * ?w + sp) (?j0 + q * ?w)" using le0py pdecomp by simp
    have le0spj1: "le0 N (?j0 + sp) ?j1"
      by (rule oper_d1pos_le0_cross_back[OF L notzero hp i1z j0lt qq qn spw reachH1])
    have esp_lt: "entry N 1 (?j0 + sp) < entry N 1 ?j0" using e_p epy ey0 by simp
    show False
    proof (cases "sp = 0")
      case True thus False using esp_lt by simp
    next
      case False
      hence j0sp: "?j0 < ?j0 + sp" by simp
      have "entry N 1 ?j1 \<le> entry N 1 (?j0 + sp)" using valleyJ1[OF j0sp le0spj1] .
      thus False using esp_lt ej0j1 by simp
    qed
  qed
  \<comment> \<open>p < j0: prefix-verbatim reflection to le0 N p j0, then existence of a parent\<close>
  have le0pj0: "le0 N ?p ?j0"
    by (rule oper_d1pos_le0_prefix_back[OF L notzero hp i1z j0lt qn plt_j0 le0py])
  have ep_pre: "entry ?Mn 1 ?p = entry N 1 ?p"
    by (rule operB_gen_entry_prefix[OF L notzero hp]) (use plt_j0 i1z in simp)
  have elt: "entry N 1 ?p < entry N 1 ?j0" using epy ey0 ep_pre by simp
  have leRp: "leR N 0 ?p ?j0" using le0pj0 by (simp add: leR_def)
  have "\<exists>j. ?p \<le> j \<and> j < ?j0 \<and> nextR N 1 j ?j0"
    by (rule m_5_1_parent_exists_2[OF NT plt_j0 j0Lt elt leRp])
  then obtain j where nr: "nextR N 1 j ?j0" by blast
  show "hasParent N 1 ?j0"
    unfolding hasParent_def using nr nextR1_unique by blast
qed

lemma oper_d1pos_parent_class:
  fixes M :: pairseq
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and cg: "cGTWF M"
    and hpz: "hasParent ((M::pairseq)[n]) 1 z"
  shows "(z < parent M 1 (Lng M - 1)
            \<and> parent ((M::pairseq)[n]) 1 z = parent M 1 z
            \<and> parent M 1 z < parent M 1 (Lng M - 1))
       \<or> (parent M 1 (Lng M - 1) \<le> z
            \<and> (z - parent M 1 (Lng M - 1)) mod (Lng M - 1 - parent M 1 (Lng M - 1)) = 0
            \<and> parent ((M::pairseq)[n]) 1 z = parent M 1 (parent M 1 (Lng M - 1))
            \<and> parent M 1 (parent M 1 (Lng M - 1)) < parent M 1 (Lng M - 1))
       \<or> (parent M 1 (Lng M - 1) \<le> z
            \<and> 0 < (z - parent M 1 (Lng M - 1)) mod (Lng M - 1 - parent M 1 (Lng M - 1))
            \<and> parent ((M::pairseq)[n]) 1 z
                = parent M 1 (parent M 1 (Lng M - 1)
                     + (z - parent M 1 (Lng M - 1)) mod (Lng M - 1 - parent M 1 (Lng M - 1)))
                  + ((z - parent M 1 (Lng M - 1)) div (Lng M - 1 - parent M 1 (Lng M - 1)))
                     * (Lng M - 1 - parent M 1 (Lng M - 1))
            \<and> parent M 1 (Lng M - 1)
                \<le> parent M 1 (parent M 1 (Lng M - 1)
                     + (z - parent M 1 (Lng M - 1)) mod (Lng M - 1 - parent M 1 (Lng M - 1)))
            \<and> parent M 1 (parent M 1 (Lng M - 1)
                     + (z - parent M 1 (Lng M - 1)) mod (Lng M - 1 - parent M 1 (Lng M - 1)))
                < parent M 1 (Lng M - 1)
                     + (z - parent M 1 (Lng M - 1)) mod (Lng M - 1 - parent M 1 (Lng M - 1)))"
proof -
  let ?j1 = "Lng M - 1"  let ?j0 = "parent M 1 ?j1"  let ?w = "?j1 - ?j0"
  let ?Mn = "(M::pairseq)[n]"
  have w0: "0 < ?w" using j0lt by linarith
  have hpj1G: "hasParent M 1 ?j1" using hp i1z by simp
  have gate: "\<And>v. ?j0 < v \<Longrightarrow> v < ?j1 \<Longrightarrow> hasParent M 1 v \<Longrightarrow> ?j0 \<le> parent M 1 v"
    using cg hpj1G by blast
  have parRz: "nextR ?Mn 1 (parent ?Mn 1 z) z"
    using hpz unfolding hasParent_def parent_def by (rule theI')
  have zL: "z < Lng ?Mn" using parRz by (simp add: nextR_def nextrel1_def)
  have j0lt': "parent M (idx1 M (Lng M - 1)) (Lng M - 1) < Lng M - 1" using j0lt i1z by simp
  show ?thesis
  proof (cases "z < ?j0")
    case True
    have pa: "hasParent ?Mn 1 z = hasParent M 1 z \<and> parent ?Mn 1 z = parent M 1 z"
      by (rule oper_parent1_prefix_agree[OF L notzero hp j0lt' _ zL]) (use True i1z in simp)
    have hpMz: "hasParent M 1 z" using pa hpz by simp
    have parRMz: "nextR M 1 (parent M 1 z) z"
      using hpMz unfolding hasParent_def parent_def by (rule theI')
    have pzlt: "parent M 1 z < z" using parRMz by (simp add: nextR_def nextrel1_def)
    have "parent M 1 z < ?j0" using pzlt True by linarith
    thus ?thesis using pa True by blast
  next
    case False
    hence zge: "?j0 \<le> z" by simp
    have lenMn: "Lng ?Mn = ?j0 + n * ?w"
      using oper_d1pos_LngM[OF L notzero hp i1z j0lt] by simp
    define q where "q = (z - ?j0) div ?w"
    define s where "s = (z - ?j0) mod ?w"
    have sw: "s < ?w" using w0 by (simp add: s_def)
    have zdecomp: "z = ?j0 + q * ?w + s"
    proof -
      have "?j0 + q * ?w + s = ?j0 + ((z - ?j0) div ?w * ?w + (z - ?j0) mod ?w)"
        unfolding q_def s_def by simp
      also have "\<dots> = ?j0 + (z - ?j0)" by (simp add: div_mult_mod_eq)
      also have "\<dots> = z" using zge by simp
      finally show ?thesis by simp
    qed
    have qn: "q < n"
    proof (rule ccontr)
      assume "\<not> q < n" hence "n \<le> q" by simp
      hence "n * ?w \<le> q * ?w" by (rule mult_le_mono1)
      hence "?j0 + n * ?w \<le> z" using zdecomp by linarith
      moreover have "z < ?j0 + n * ?w" using zL lenMn by simp
      ultimately show False by linarith
    qed
    show ?thesis
    proof (cases "s = 0")
      case True
      have zbs: "z = ?j0 + q * ?w" using zdecomp True by simp
      have hpy: "hasParent ?Mn 1 (?j0 + q * ?w)" using hpz zbs by simp
      have hpMj0: "hasParent M 1 ?j0"
        by (rule oper_blockstart_hasParent_j0[OF L notzero hp i1z j0lt qn hpy])
      have parRj0: "nextR M 1 (parent M 1 ?j0) ?j0"
        using hpMj0 unfolding hasParent_def parent_def by (rule theI')
      have pjlt: "parent M 1 ?j0 < ?j0" using parRj0 by (simp add: nextR_def nextrel1_def)
      have pread: "parent ?Mn 1 (?j0 + q * ?w) = parent M 1 ?j0"
        by (rule oper_parent1_readback_boundary_uncond[OF L notzero hp i1z j0lt qn hpMj0 pjlt])
      have "parent ?Mn 1 z = parent M 1 ?j0" using pread zbs by simp
      thus ?thesis using zge True s_def pjlt by simp
    next
      case False
      hence spos: "0 < s" by simp
      have zint: "z = ?j0 + q * ?w + s" using zdecomp .
      have hpy: "hasParent ?Mn 1 (?j0 + q * ?w + s)" using hpz zint by simp
      have hpMs: "hasParent M 1 (?j0 + s)"
        by (rule oper_interior_hasParent_base[OF L notzero hp i1z j0lt qn spos sw hpy])
      have base_gt: "?j0 < ?j0 + s" using spos by simp
      have base_lt: "?j0 + s < ?j1" using sw by simp
      have pMge: "?j0 \<le> parent M 1 (?j0 + s)" using gate[OF base_gt base_lt hpMs] .
      have parRb: "nextR M 1 (parent M 1 (?j0 + s)) (?j0 + s)"
        using hpMs unfolding hasParent_def parent_def by (rule theI')
      have pblt: "parent M 1 (?j0 + s) < ?j0 + s" using parRb by (simp add: nextR_def nextrel1_def)
      have pread: "parent ?Mn 1 (?j0 + q * ?w + s) = parent M 1 (?j0 + s) + q * ?w"
        by (rule oper_parent1_readback[OF L notzero hp i1z j0lt qn spos sw hpMs pMge])
      have "parent ?Mn 1 z = parent M 1 (?j0 + s) + q * ?w" using pread zint by simp
      thus ?thesis using zge spos s_def q_def pMge pblt by simp
    qed
  qed
qed


text \<open>§6.7 oper-tiling REVERSE READBACK, idx1 = 0 (d0zero): an interior column
  j0+q*w+s (0<s<w) of M[n] with a row-1 parent has its base j0+s parented in M.
  Cleaner than the d1pos case: the d0zero le0 reflection
  @{thm [source] oper_d0zero_le0_base_fwd} sends ANY le0-predecessor p of the column
  to le0 M (base p) (j0+s) uniformly (prefix and block via one if), and the row-1
  reading is verbatim periodic @{thm [source] oper_d0zero_entryi_base}; the reflected
  base p is then a strictly-smaller-row1 predecessor of j0+s, whence
  @{thm [source] m_5_1_parent_exists_2}.\<close>

lemma oper_d0zero_interior_hasParent_base:
  fixes M :: pairseq
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z0: "idx1 M (Lng M - 1) = 0"
    and j0lt: "parent M (idx1 M (Lng M - 1)) (Lng M - 1) < Lng M - 1"
    and qn: "q < n"
    and sw: "s < Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and hpy: "hasParent ((M::pairseq)[n]) 1
                (parent M (idx1 M (Lng M - 1)) (Lng M - 1)
                   + q * (Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1)) + s)"
  shows "hasParent M 1 (parent M (idx1 M (Lng M - 1)) (Lng M - 1) + s)"
proof -
  let ?j1 = "Lng M - 1"  let ?j0 = "parent M (idx1 M (Lng M - 1)) ?j1"  let ?w = "?j1 - ?j0"
  let ?Mn = "(M::pairseq)[n]"  let ?y = "?j0 + q * ?w + s"  let ?base = "?j0 + s"
  let ?p = "parent ?Mn 1 ?y"
  let ?bp = "if ?p < ?j0 then ?p else ?j0 + (?p - ?j0) mod ?w"
  have w0: "0 < ?w" using j0lt by linarith
  have NT: "M \<in> T_PS" using L by (cases M) (auto simp: T_PS_def)
  have baseLt: "?base < Lng M" using sw j0lt by linarith
  have parRy: "nextR ?Mn 1 ?p ?y" using hpy unfolding hasParent_def parent_def by (rule theI')
  have nr1y: "nextrel1 ?Mn ?p ?y" using parRy by (simp add: nextR_def)
  have ple: "?p < ?y" using nr1y by (simp add: nextrel1_def)
  have le0py: "le0 ?Mn ?p ?y" using nr1y by (simp add: nextrel1_def)
  have epy: "entry ?Mn 1 ?p < entry ?Mn 1 ?y" using nr1y by (simp add: nextrel1_def)
  have yL: "?y < Lng ?Mn" using nr1y by (simp add: nextrel1_def)
  have pL: "?p < Lng ?Mn" using ple yL by linarith
  \<comment> \<open>row-1 reading of y is its base j0+s\<close>
  have ymod: "(?y - ?j0) mod ?w = s"
  proof -
    have "?y - ?j0 = q * ?w + s" by simp
    thus ?thesis using sw by simp
  qed
  have ey: "entry ?Mn 1 ?y = entry M 1 ?base"
  proof -
    have "entry ?Mn 1 ?y = entry M 1 (if ?y < ?j0 then ?y else ?j0 + (?y - ?j0) mod ?w)"
      by (rule oper_d0zero_entryi_base[OF L notzero hp i1z0 j0lt yL])
    thus ?thesis using ymod by simp
  qed
  have ep: "entry ?Mn 1 ?p = entry M 1 ?bp"
    by (rule oper_d0zero_entryi_base[OF L notzero hp i1z0 j0lt pL])
  have le0bp: "le0 M ?bp ?base"
    by (rule oper_d0zero_le0_base_fwd[OF L notzero hp i1z0 j0lt qn sw le0py])
  have ebp: "entry M 1 ?bp < entry M 1 ?base" using epy ep ey by simp
  have bple: "?bp \<le> ?base"
  proof -
    have "(nextrel0 M)\<^sup>*\<^sup>* ?bp ?base" using le0bp by (simp add: le0_def)
    thus ?thesis by (rule nextrel0_rtrancl_mono)
  qed
  have bpne: "?bp \<noteq> ?base" using ebp by auto
  have bpbase: "?bp < ?base" using bple bpne by simp
  have leRbp: "leR M 0 ?bp ?base" using le0bp by (simp add: leR_def)
  have "\<exists>j. ?bp \<le> j \<and> j < ?base \<and> nextR M 1 j ?base"
    by (rule m_5_1_parent_exists_2[OF NT bpbase baseLt ebp leRbp])
  then obtain j where nr: "nextR M 1 j ?base" by blast
  show "hasParent M 1 ?base"
    unfolding hasParent_def using nr nextR1_unique by blast
qed

text \<open>§6.7 d0zero PARENT base-readback (the idx1=0 crux): the row-1 parent of an
  interior column j0+q*w+s of M[n] is the lift of parent N1(j0+s) -- itself if it
  is a prefix node, else translated into block q.  Built from the candidate via
  uniqueness: le0 N pb (j0+s) lifts (oper_d0zero_le0_lift) to le0 (M[n]) c x, the
  valley reflects every le0-pred j of x (j>c, so j is in block q by index bounds,
  base j > pb) back by oper_d0zero_le0_base_fwd into the nextrel1 N pb (j0+s)
  valley; rows read off periodically by oper_d0zero_entryi_base.\<close>

lemma oper_d0zero_parent1_readback:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z0: "idx1 N (Lng N - 1) = 0"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and qn: "q < n"
    and sw: "s < Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and hpb: "hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1) + s)"
  shows "parent ((N::pairseq)[n]) 1
            (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
               + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)) + s)
       = (if parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1) + s)
              < parent N (idx1 N (Lng N - 1)) (Lng N - 1)
          then parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1) + s)
          else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
               + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
               + (parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1) + s)
                  - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
proof -
  let ?j1 = "Lng N - 1"  let ?j0 = "parent N (idx1 N (Lng N - 1)) ?j1"  let ?w = "?j1 - ?j0"
  let ?Mn = "(N::pairseq)[n]"  let ?x = "?j0 + q * ?w + s"  let ?base = "?j0 + s"
  let ?pb = "parent N 1 ?base"
  let ?c = "if ?pb < ?j0 then ?pb else ?j0 + q * ?w + (?pb - ?j0)"
  have w0: "0 < ?w" using j0lt by linarith
  have basej1: "?base < ?j1" using sw by simp
  have parRb: "nextR N 1 ?pb ?base" using hpb unfolding hasParent_def parent_def by (rule theI')
  have nr1b: "nextrel1 N ?pb ?base" using parRb by (simp add: nextR_def)
  have pblt: "?pb < ?base" using nr1b by (simp add: nextrel1_def)
  have epb: "entry N 1 ?pb < entry N 1 ?base" using nr1b by (simp add: nextrel1_def)
  have le0b: "le0 N ?pb ?base" using nr1b by (simp add: nextrel1_def)
  have valleyb: "\<And>j. ?pb < j \<Longrightarrow> le0 N j ?base \<Longrightarrow> entry N 1 ?base \<le> entry N 1 j"
    using nr1b unfolding nextrel1_def by blast
  have pbsub: "?pb - ?j0 < ?w"
  proof (cases "?pb < ?j0")
    case True thus ?thesis using w0 by linarith
  next
    case False thus ?thesis using pblt sw by linarith
  qed
  \<comment> \<open>le0 (N[n]) c x is exactly the d0zero forward lift of le0 N pb base\<close>
  have le0cx: "le0 ?Mn ?c ?x"
    using oper_d0zero_le0_lift[OF L notzero hp i1z0 j0lt qn sw le0b] by simp
  \<comment> \<open>base of c is pb, so its row-1 reading is entry N 1 pb\<close>
  have cL: "?c < Lng ?Mn" using le0cx by (simp add: le0_def)
  have basec: "(if ?c < ?j0 then ?c else ?j0 + (?c - ?j0) mod ?w) = ?pb"
  proof (cases "?pb < ?j0")
    case True thus ?thesis by simp
  next
    case False
    hence cval: "?c = ?j0 + q * ?w + (?pb - ?j0)" by simp
    have "(?c - ?j0) mod ?w = (q * ?w + (?pb - ?j0)) mod ?w" using cval by simp
    also have "\<dots> = (?pb - ?j0) mod ?w" by simp
    also have "\<dots> = ?pb - ?j0" using pbsub by simp
    finally have cmod: "(?c - ?j0) mod ?w = ?pb - ?j0" .
    moreover have "\<not> ?c < ?j0" using cval by simp
    ultimately show ?thesis using False by simp
  qed
  have ec: "entry ?Mn 1 ?c = entry N 1 ?pb"
  proof -
    have "entry ?Mn 1 ?c = entry N 1 (if ?c < ?j0 then ?c else ?j0 + (?c - ?j0) mod ?w)"
      by (rule oper_d0zero_entryi_base[OF L notzero hp i1z0 j0lt cL])
    thus ?thesis using basec by simp
  qed
  have xL: "?x < Lng ?Mn" using le0cx by (simp add: le0_def)
  have ex: "entry ?Mn 1 ?x = entry N 1 ?base"
  proof -
    have "entry ?Mn 1 ?x = entry N 1 (if ?x < ?j0 then ?x else ?j0 + (?x - ?j0) mod ?w)"
      by (rule oper_d0zero_entryi_base[OF L notzero hp i1z0 j0lt xL])
    moreover have "(?x - ?j0) mod ?w = s"
    proof -
      have "(?x - ?j0) mod ?w = (q * ?w + s) mod ?w" by simp
      also have "\<dots> = s mod ?w" by simp
      also have "\<dots> = s" using sw by simp
      finally show ?thesis .
    qed
    moreover have "\<not> ?x < ?j0" by simp
    ultimately show ?thesis by simp
  qed
  have ecx: "entry ?Mn 1 ?c < entry ?Mn 1 ?x" using ec ex epb by simp
  have cxlt: "?c < ?x"
  proof (cases "?pb < ?j0")
    case True
    have "?pb < ?j0 + q * ?w + s" using True by linarith
    thus ?thesis using True by simp
  next
    case False
    hence "?c = ?j0 + q * ?w + (?pb - ?j0)" by simp
    moreover have "?pb - ?j0 < s" using pblt False by linarith
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>the valley: every le0-pred j of x above c has entry1 j >= entry1 x\<close>
  have valley: "\<And>j. ?c < j \<Longrightarrow> le0 ?Mn j ?x \<Longrightarrow> entry ?Mn 1 ?x \<le> entry ?Mn 1 j"
  proof -
    fix j assume cj: "?c < j" and le0j: "le0 ?Mn j ?x"
    have jx: "j \<le> ?x"
    proof -
      have "(nextrel0 ?Mn)\<^sup>*\<^sup>* j ?x" using le0j by (simp add: le0_def)
      thus ?thesis by (rule nextrel0_rtrancl_mono)
    qed
    define bj where "bj = (if j < ?j0 then j else ?j0 + (j - ?j0) mod ?w)"
    have le0Nbj: "le0 N bj ?base"
    proof -
      have "le0 N (if j < ?j0 then j else ?j0 + (j - ?j0) mod ?w) (?j0 + s)"
        by (rule oper_d0zero_le0_base_fwd[OF L notzero hp i1z0 j0lt qn sw le0j])
      thus ?thesis using bj_def by simp
    qed
    have pbbj: "?pb < bj"
    proof (cases "?pb < ?j0")
      case True
      have cpb: "?c = ?pb" using \<open>?pb < ?j0\<close> by simp
      show ?thesis
      proof (cases "j < ?j0")
        case True
        hence "bj = j" by (simp add: bj_def)
        thus ?thesis using cj cpb by simp
      next
        case False
        hence "bj = ?j0 + (j - ?j0) mod ?w" by (simp add: bj_def)
        thus ?thesis using \<open>?pb < ?j0\<close> by linarith
      qed
    next
      case False
      hence cge: "?c = ?j0 + q * ?w + (?pb - ?j0)" by simp
      have jge: "?j0 \<le> j" using cj cge by linarith
      have jblk: "?j0 + q * ?w \<le> j" using cj cge by linarith
      have hi: "j - ?j0 - q * ?w \<le> s" using jx jblk by linarith
      have off_lt: "j - ?j0 - q * ?w < ?w" using hi sw by linarith
      have qwle: "q * ?w \<le> j - ?j0" using jblk by linarith
      have jdec: "j - ?j0 = q * ?w + (j - ?j0 - q * ?w)" using qwle by linarith
      have jr: "(j - ?j0) mod ?w = j - ?j0 - q * ?w"
      proof -
        have "(j - ?j0) mod ?w = (q * ?w + (j - ?j0 - q * ?w)) mod ?w" using jdec by simp
        also have "\<dots> = (j - ?j0 - q * ?w) mod ?w" by simp
        also have "\<dots> = j - ?j0 - q * ?w" using off_lt by simp
        finally show ?thesis .
      qed
      have lo: "?pb - ?j0 < j - ?j0 - q * ?w" using cj cge by linarith
      have bjeq: "bj = ?j0 + (j - ?j0 - q * ?w)" using jge jr by (simp add: bj_def)
      thus ?thesis using lo False by linarith
    qed
    have "entry N 1 ?base \<le> entry N 1 bj" by (rule valleyb[OF pbbj le0Nbj])
    moreover have "entry ?Mn 1 j = entry N 1 bj"
    proof -
      have jL: "j < Lng ?Mn" using jx xL by linarith
      have "entry ?Mn 1 j = entry N 1 (if j < ?j0 then j else ?j0 + (j - ?j0) mod ?w)"
        by (rule oper_d0zero_entryi_base[OF L notzero hp i1z0 j0lt jL])
      thus ?thesis using bj_def by simp
    qed
    ultimately show "entry ?Mn 1 ?x \<le> entry ?Mn 1 j" using ex by simp
  qed
  have nr1cx: "nextrel1 ?Mn ?c ?x"
    unfolding nextrel1_def using cL xL cxlt ecx le0cx valley by blast
  have ncx: "nextR ?Mn 1 ?c ?x" using nr1cx by (simp add: nextR_def)
  have hpx: "hasParent ?Mn 1 ?x" unfolding hasParent_def using ncx nextR1_unique by blast
  have parRx: "nextR ?Mn 1 (parent ?Mn 1 ?x) ?x"
    using hpx unfolding hasParent_def parent_def by (rule theI')
  show ?thesis using nextR1_unique[OF parRx ncx] by simp
qed

text \<open>§6.7 d0zero PREFIX-PARENT EQUALITY (the keystone C for cgtw_tile_d0zero):
  for the last row-0 block of a standard idx1=0 sequence (j0 = parent N 0 j1), an
  INTERIOR column c = j0+s (0<s<w) whose row-1 parent escapes into the PREFIX
  (parent N 1 c < j0) actually shares j0's own row-1 parent: parent N 1 c =
  parent N 1 j0 (and j0 has a row-1 parent at all).  This is exactly what closes
  the d0zero cGTWF worry case (two interior prefix-parent columns have EQUAL
  parents).  cGTWF alone does not give it (the standard/reduced/cGTWF non-ST_PS
  witness (0,0)(1,1)(2,2)(3,1)(3,0) violates it); the missing ingredient is the
  ST_PS invariant Eglobal' (here as hypothesis E: entry N 1 j0 <= entry N 1 c).
  Proof: L0 (le0 N j0 c) by the ancestor-tree linearity m_5_1_ancestor_tree_1;
  the row-1 parent ps of c and j0 are both le0-ancestors of c, so linearly
  ordered -> le0 N ps j0, giving hasParent N 1 j0 (m_5_1_parent_exists_2) with
  entry N 1 ps < entry N 1 j0 = entry N 1 c (E + the c-valley collapse).  cGTWF
  at c (z=j0) gives ps <= p0 := parent N 1 j0; then nextrel1 N p0 c holds
  (entry p0 < entry j0 = entry c; le0 p0 c by transitivity; valley from ps<=p0 +
  c's valley), so by uniqueness parent N 1 c = p0 = parent N 1 j0.\<close>

lemma oper_d0zero_prefix_parent_eq:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z0: "idx1 N (Lng N - 1) = 0"
    and cg: "cGTWF N"
    and spos: "0 < s"
    and sj1: "parent N 0 (Lng N - 1) + s < Lng N - 1"
    and hpc: "hasParent N 1 (parent N 0 (Lng N - 1) + s)"
    and pre: "parent N 1 (parent N 0 (Lng N - 1) + s) < parent N 0 (Lng N - 1)"
    and E: "entry N 1 (parent N 0 (Lng N - 1)) \<le> entry N 1 (parent N 0 (Lng N - 1) + s)"
  shows "hasParent N 1 (parent N 0 (Lng N - 1))
         \<and> parent N 1 (parent N 0 (Lng N - 1) + s) = parent N 1 (parent N 0 (Lng N - 1))"
proof -
  let ?j1 = "Lng N - 1"  let ?j0 = "parent N 0 ?j1"  let ?c = "?j0 + s"
  let ?ps = "parent N 1 ?c"
  have NT: "N \<in> T_PS" using L by (cases N) (auto simp: T_PS_def)
  have hp0: "hasParent N 0 ?j1" using hp i1z0 by simp
  have parRj0j1: "nextR N 0 ?j0 ?j1" using hp0 unfolding hasParent_def parent_def by (rule theI')
  have nr0: "nextrel0 N ?j0 ?j1" using parRj0j1 by (simp add: nextR_def)
  have b0: "?j0 < Lng N \<and> ?j1 < Lng N" using nr0 unfolding nextrel0_def by blast
  have le0j0j1: "le0 N ?j0 ?j1"
    unfolding le0_def using b0 nr0 by (blast intro: r_into_rtranclp)
  have j0ltj1: "?j0 < ?j1" using nr0 by (simp add: nextrel0_def)
  have c_lt: "?c < ?j1" using sj1 by simp
  have cle: "?c \<le> ?j1" using c_lt by simp
  have j0c: "?j0 < ?c" using spos by simp
  have j0c_le: "?j0 \<le> ?c" using j0c by simp
  have j0Lng: "?j0 < Lng N" using b0 by simp
  have cLng: "?c < Lng N" using c_lt b0 by simp
  \<comment> \<open>L0: j0 reaches the interior column c (ancestor-tree linearity)\<close>
  have leRj0j1: "leR N 0 ?j0 ?j1" using le0j0j1 by (simp add: leR_def)
  have le0j0c: "le0 N ?j0 ?c"
    using m_5_1_ancestor_tree_1[OF NT leRj0j1 le_add1 cle] by (simp add: leR_def)
  \<comment> \<open>c's row-1 parent edge and its valley\<close>
  have parRc: "nextR N 1 ?ps ?c" using hpc unfolding hasParent_def parent_def by (rule theI')
  have nr1c: "nextrel1 N ?ps ?c" using parRc by (simp add: nextR_def)
  have epsc: "entry N 1 ?ps < entry N 1 ?c" using nr1c by (simp add: nextrel1_def)
  have le0psc: "le0 N ?ps ?c" using nr1c by (simp add: nextrel1_def)
  have valleyc: "\<And>j. ?ps < j \<Longrightarrow> le0 N j ?c \<Longrightarrow> entry N 1 ?c \<le> entry N 1 j"
    using nr1c unfolding nextrel1_def by blast
  \<comment> \<open>the c-valley collapses entry at j0: entry j0 = entry c\<close>
  have ecj0: "entry N 1 ?c \<le> entry N 1 ?j0" using valleyc[OF pre le0j0c] .
  have e_eq: "entry N 1 ?j0 = entry N 1 ?c" using ecj0 E by simp
  have e_ps_j0: "entry N 1 ?ps < entry N 1 ?j0" using epsc e_eq by simp
  \<comment> \<open>ps and j0 are both le0-ancestors of c -> le0 N ps j0 (linearity)\<close>
  have leRpsc: "leR N 0 ?ps ?c" using le0psc by (simp add: leR_def)
  have psj0: "?ps \<le> ?j0" using pre by simp
  have le0psj0: "le0 N ?ps ?j0"
    using m_5_1_ancestor_tree_1[OF NT leRpsc psj0 j0c_le] by (simp add: leR_def)
  \<comment> \<open>hence j0 has a row-1 parent\<close>
  have leRpsj0: "leR N 0 ?ps ?j0" using le0psj0 by (simp add: leR_def)
  have "\<exists>j. ?ps \<le> j \<and> j < ?j0 \<and> nextR N 1 j ?j0"
    by (rule m_5_1_parent_exists_2[OF NT pre j0Lng e_ps_j0 leRpsj0])
  then obtain jj where nrjj: "nextR N 1 jj ?j0" by blast
  have hpj0: "hasParent N 1 ?j0"
    unfolding hasParent_def using nrjj nextR1_unique by blast
  let ?p0 = "parent N 1 ?j0"
  have parRj0: "nextR N 1 ?p0 ?j0" using hpj0 unfolding hasParent_def parent_def by (rule theI')
  have nr1j0: "nextrel1 N ?p0 ?j0" using parRj0 by (simp add: nextR_def)
  have p0j0: "?p0 < ?j0" using nr1j0 by (simp add: nextrel1_def)
  have ep0j0: "entry N 1 ?p0 < entry N 1 ?j0" using nr1j0 by (simp add: nextrel1_def)
  have le0p0j0: "le0 N ?p0 ?j0" using nr1j0 by (simp add: nextrel1_def)
  \<comment> \<open>cGTWF at c (z = j0): ps <= p0\<close>
  have psp0: "?ps \<le> ?p0" using cg hpc pre j0c hpj0 by blast
  \<comment> \<open>build nextrel1 N p0 c -> p0 = ps by uniqueness\<close>
  have p0c: "?p0 < ?c" using p0j0 j0c by linarith
  have p0Lng: "?p0 < Lng N" using p0j0 j0Lng by linarith
  have le0p0c: "le0 N ?p0 ?c" using le0p0j0 le0j0c by (rule le0_trans)
  have ep0c: "entry N 1 ?p0 < entry N 1 ?c" using ep0j0 e_eq by simp
  have valleyp0: "\<forall>j. ?p0 < j \<and> le0 N j ?c \<longrightarrow> entry N 1 ?c \<le> entry N 1 j"
  proof (intro allI impI)
    fix j assume H: "?p0 < j \<and> le0 N j ?c"
    have "?ps < j" using H psp0 by linarith
    thus "entry N 1 ?c \<le> entry N 1 j" using valleyc H by blast
  qed
  have nr1p0c: "nextrel1 N ?p0 ?c"
    unfolding nextrel1_def using p0Lng cLng p0c ep0c le0p0c valleyp0 by simp
  have "nextR N 1 ?p0 ?c" using nr1p0c by (simp add: nextR_def)
  hence "?p0 = ?ps" using parRc by (rule nextR1_unique)
  thus ?thesis using hpj0 by simp
qed

text \<open>§6.7 d0zero PARENT-CLASS: the row-1 parent of a column z of N[n] is classified
  by z's position (prefix / copy-block-interior).  No gate (d0=d1=0): for z >= j0 the
  base column is j0 + (z-j0) mod w and the parent reads off via
  @{thm [source] oper_d0zero_parent1_readback} -- either the verbatim prefix parent
  (pb < j0) or the lifted block parent (pb >= j0).\<close>

lemma oper_d0zero_parent_class:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z0: "idx1 N (Lng N - 1) = 0"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and hpz: "hasParent ((N::pairseq)[n]) 1 z"
  shows "(z < parent N (idx1 N (Lng N - 1)) (Lng N - 1)
            \<and> parent ((N::pairseq)[n]) 1 z = parent N 1 z
            \<and> parent N 1 z < parent N (idx1 N (Lng N - 1)) (Lng N - 1))
       \<or> (parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> z
            \<and> hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                 + (z - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                    mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
            \<and> parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                 + (z - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                    mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                < parent N (idx1 N (Lng N - 1)) (Lng N - 1)
            \<and> parent ((N::pairseq)[n]) 1 z
                = parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                     + (z - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                        mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))))
       \<or> (parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> z
            \<and> hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                 + (z - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                    mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
            \<and> parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                \<le> parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                     + (z - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                        mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
            \<and> parent ((N::pairseq)[n]) 1 z
                = parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                  + ((z - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                       div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                     * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                  + (parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                       + (z - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                          mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                     - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
proof -
  let ?j1 = "Lng N - 1"  let ?j0 = "parent N (idx1 N ?j1) ?j1"  let ?w = "?j1 - ?j0"
  let ?Mn = "(N::pairseq)[n]"
  have w0: "0 < ?w" using j0lt by linarith
  have parRz: "nextR ?Mn 1 (parent ?Mn 1 z) z"
    using hpz unfolding hasParent_def parent_def by (rule theI')
  have zL: "z < Lng ?Mn" using parRz by (simp add: nextR_def nextrel1_def)
  show ?thesis
  proof (cases "z < ?j0")
    case True
    have pa: "hasParent ?Mn 1 z = hasParent N 1 z \<and> parent ?Mn 1 z = parent N 1 z"
      by (rule oper_parent1_prefix_agree[OF L notzero hp j0lt True zL])
    have hpNz: "hasParent N 1 z" using pa hpz by simp
    have parRNz: "nextR N 1 (parent N 1 z) z"
      using hpNz unfolding hasParent_def parent_def by (rule theI')
    have pzlt: "parent N 1 z < z" using parRNz by (simp add: nextR_def nextrel1_def)
    have "parent N 1 z < ?j0" using pzlt True by linarith
    thus ?thesis using pa True by blast
  next
    case False
    hence zge: "?j0 \<le> z" by simp
    have lenMn: "Lng ?Mn = ?j0 + n * ?w"
      using operB_gen_LngM[OF L notzero hp j0lt] by simp
    define q where "q = (z - ?j0) div ?w"
    define s where "s = (z - ?j0) mod ?w"
    have sw: "s < ?w" using w0 by (simp add: s_def)
    have zdecomp: "z = ?j0 + q * ?w + s"
    proof -
      have "?j0 + q * ?w + s = ?j0 + ((z - ?j0) div ?w * ?w + (z - ?j0) mod ?w)"
        unfolding q_def s_def by simp
      also have "\<dots> = ?j0 + (z - ?j0)" by (simp add: div_mult_mod_eq)
      also have "\<dots> = z" using zge by simp
      finally show ?thesis by simp
    qed
    have qn: "q < n"
    proof (rule ccontr)
      assume "\<not> q < n" hence "n \<le> q" by simp
      hence "n * ?w \<le> q * ?w" by (rule mult_le_mono1)
      hence "?j0 + n * ?w \<le> z" using zdecomp by linarith
      moreover have "z < ?j0 + n * ?w" using zL lenMn by simp
      ultimately show False by linarith
    qed
    have hpy: "hasParent ?Mn 1 (?j0 + q * ?w + s)" using hpz zdecomp by simp
    have hpMs: "hasParent N 1 (?j0 + s)"
      by (rule oper_d0zero_interior_hasParent_base[OF L notzero hp i1z0 j0lt qn sw hpy])
    have smod: "(z - ?j0) mod ?w = s" using s_def by simp
    have sdiv: "(z - ?j0) div ?w = q" using q_def by simp
    have base_eq: "?j0 + (z - ?j0) mod ?w = ?j0 + s" using smod by simp
    have hpMs': "hasParent N 1 (?j0 + (z - ?j0) mod ?w)" using hpMs base_eq by simp
    have pread: "parent ?Mn 1 (?j0 + q * ?w + s)
        = (if parent N 1 (?j0 + s) < ?j0 then parent N 1 (?j0 + s)
           else ?j0 + q * ?w + (parent N 1 (?j0 + s) - ?j0))"
      by (rule oper_d0zero_parent1_readback[OF L notzero hp i1z0 j0lt qn sw hpMs])
    have pval: "parent ?Mn 1 z
        = (if parent N 1 (?j0 + s) < ?j0 then parent N 1 (?j0 + s)
           else ?j0 + q * ?w + (parent N 1 (?j0 + s) - ?j0))"
      using pread zdecomp by simp
    show ?thesis
    proof (cases "parent N 1 (?j0 + s) < ?j0")
      case True
      have "parent ?Mn 1 z = parent N 1 (?j0 + s)" using pval True by simp
      thus ?thesis using zge hpMs' base_eq True smod by auto
    next
      case False
      hence pge: "?j0 \<le> parent N 1 (?j0 + s)" by simp
      have "parent ?Mn 1 z = ?j0 + q * ?w + (parent N 1 (?j0 + s) - ?j0)"
        using pval False by simp
      thus ?thesis using zge hpMs' base_eq pge smod sdiv by auto
    qed
  qed
qed

text \<open>cgtw_tile, idx1 = 0 (d0zero) branch: cGTWF (N[n]) from cGTWF N [IH] plus the
  ST_PS invariant Eglobal' (here the hypothesis Eg, the b = j1 instance: for an
  interior column j0+s of the last block whose row-1 parent escapes the prefix,
  entry N 1 j0 <= entry N 1 (j0+s)).  Comparison via @{thm [source]
  oper_d0zero_parent_class}: prefix-vs-prefix by cGTWF N; same-block by cGTWF N at
  the base columns; the cross-copy worry case (both parents in the prefix) by the
  keystone @{thm [source] oper_d0zero_prefix_parent_eq} (both equal parent N 1 j0).\<close>

lemma cgtw_tile_d0zero:
  fixes M :: pairseq
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z0: "idx1 M (Lng M - 1) = 0"
    and cg: "cGTWF M"
    and Eg: "\<And>s. 0 < s \<Longrightarrow> parent M 0 (Lng M - 1) + s < Lng M - 1
              \<Longrightarrow> hasParent M 1 (parent M 0 (Lng M - 1) + s)
              \<Longrightarrow> parent M 1 (parent M 0 (Lng M - 1) + s) < parent M 0 (Lng M - 1)
              \<Longrightarrow> entry M 1 (parent M 0 (Lng M - 1))
                  \<le> entry M 1 (parent M 0 (Lng M - 1) + s)"
  shows "cGTWF ((M::pairseq)[n])"
proof -
  let ?j1 = "Lng M - 1"  let ?j0 = "parent M (idx1 M ?j1) ?j1"  let ?w = "?j1 - ?j0"
  let ?Mn = "(M::pairseq)[n]"
  have hp0: "hasParent M 0 ?j1" using hp i1z0 by simp
  have parRj0j1: "nextR M 0 ?j0 ?j1" using hp0 i1z0
    unfolding hasParent_def parent_def by simp (rule theI')
  have j0lt: "?j0 < ?j1" using parRj0j1 by (simp add: nextR_def nextrel0_def)
  have w0: "0 < ?w" using j0lt by linarith
  have lenMn: "Lng ?Mn = ?j0 + n * ?w" using operB_gen_LngM[OF L notzero hp j0lt] by simp
  have j0eq: "parent M 0 ?j1 = ?j0" using i1z0 by simp
  \<comment> \<open>keystone C, specialised: a copy-prefix-parent base column equals parent M 1 j0\<close>
  have Cbase: "\<And>s. s < ?w \<Longrightarrow> hasParent M 1 (?j0 + s) \<Longrightarrow> parent M 1 (?j0 + s) < ?j0
                \<Longrightarrow> parent M 1 (?j0 + s) = parent M 1 ?j0 \<and> hasParent M 1 ?j0"
  proof -
    fix s assume sw: "s < ?w" and hpb: "hasParent M 1 (?j0 + s)" and pblt: "parent M 1 (?j0 + s) < ?j0"
    show "parent M 1 (?j0 + s) = parent M 1 ?j0 \<and> hasParent M 1 ?j0"
    proof (cases "s = 0")
      case True thus ?thesis using hpb by simp
    next
      case False
      hence spos: "0 < s" by simp
      have sj1: "parent M 0 ?j1 + s < ?j1" using sw j0eq by simp
      have hpb': "hasParent M 1 (parent M 0 ?j1 + s)" using hpb j0eq by simp
      have pblt': "parent M 1 (parent M 0 ?j1 + s) < parent M 0 ?j1" using pblt j0eq by simp
      have e: "entry M 1 (parent M 0 ?j1) \<le> entry M 1 (parent M 0 ?j1 + s)"
        by (rule Eg[OF spos sj1 hpb' pblt'])
      have key: "hasParent M 1 (parent M 0 ?j1)
              \<and> parent M 1 (parent M 0 ?j1 + s) = parent M 1 (parent M 0 ?j1)"
        by (rule oper_d0zero_prefix_parent_eq[OF L hp i1z0 cg spos sj1 hpb' pblt' e])
      show ?thesis using key j0eq by simp
    qed
  qed
  show "cGTWF ?Mn"
  proof (intro allI impI)
    fix k u
    assume hpk: "hasParent ?Mn 1 k"
       and H: "parent ?Mn 1 k < u \<and> u < k \<and> hasParent ?Mn 1 u"
    from H have pku: "parent ?Mn 1 k < u" and uk: "u < k" and hpu: "hasParent ?Mn 1 u" by auto
    have parRk: "nextR ?Mn 1 (parent ?Mn 1 k) k"
      using hpk unfolding hasParent_def parent_def by (rule theI')
    have kL: "k < Lng ?Mn" using parRk by (simp add: nextR_def nextrel1_def)
    note CK = oper_d0zero_parent_class[OF L notzero hp i1z0 j0lt hpk]
    note CU = oper_d0zero_parent_class[OF L notzero hp i1z0 j0lt hpu]
    \<comment> \<open>abbreviations for the base columns of k and u\<close>
    define sk where "sk = (k - ?j0) mod ?w"
    define qk where "qk = (k - ?j0) div ?w"
    define su where "su = (u - ?j0) mod ?w"
    define qu where "qu = (u - ?j0) div ?w"
    from CK show "parent ?Mn 1 k \<le> parent ?Mn 1 u"
    proof (elim disjE conjE)
      \<comment> \<open>D1(k): k in the prefix; u < k < j0, both verbatim, cGTWF M\<close>
      assume kpre: "k < ?j0" and pk_eq: "parent ?Mn 1 k = parent M 1 k"
        and pk_lt: "parent M 1 k < ?j0"
      have ult: "u < ?j0" using uk kpre by linarith
      have pak: "hasParent ?Mn 1 k = hasParent M 1 k \<and> parent ?Mn 1 k = parent M 1 k"
        by (rule oper_parent1_prefix_agree[OF L notzero hp j0lt kpre kL])
      have hpMk: "hasParent M 1 k" using pak hpk by simp
      have uL: "u < Lng ?Mn" using uk kL by linarith
      have pau: "hasParent ?Mn 1 u = hasParent M 1 u \<and> parent ?Mn 1 u = parent M 1 u"
        by (rule oper_parent1_prefix_agree[OF L notzero hp j0lt ult uL])
      have hpMu: "hasParent M 1 u" using pau hpu by simp
      have "parent M 1 k < u" using pku pk_eq by simp
      hence "parent M 1 k \<le> parent M 1 u" using cg hpMk uk hpMu by blast
      thus "parent ?Mn 1 k \<le> parent ?Mn 1 u" using pk_eq pau by simp
    next
      \<comment> \<open>D2(k): copy-block-interior with prefix parent (the worry source)\<close>
      assume kge: "?j0 \<le> k" and hpbk: "hasParent M 1 (?j0 + (k - ?j0) mod ?w)"
        and pbk_lt: "parent M 1 (?j0 + (k - ?j0) mod ?w) < ?j0"
        and pk_eq: "parent ?Mn 1 k = parent M 1 (?j0 + (k - ?j0) mod ?w)"
      have skw: "sk < ?w" using w0 sk_def by simp
      have hpbk': "hasParent M 1 (?j0 + sk)" using hpbk sk_def by simp
      have pbk_lt': "parent M 1 (?j0 + sk) < ?j0" using pbk_lt sk_def by simp
      have Ck: "parent M 1 (?j0 + sk) = parent M 1 ?j0 \<and> hasParent M 1 ?j0"
        by (rule Cbase[OF skw hpbk' pbk_lt'])
      have pk_pj: "parent ?Mn 1 k = parent M 1 ?j0" using pk_eq sk_def Ck by simp
      have pkj0: "parent M 1 ?j0 < ?j0" using pbk_lt' Ck by simp
      have bkj1: "?j0 + sk < ?j1" using skw by simp
      from CU show "parent ?Mn 1 k \<le> parent ?Mn 1 u"
      proof (elim disjE conjE)
        \<comment> \<open>u prefix: cGTWF M at base column j0+sk\<close>
        assume upre: "u < ?j0" and pu_eq: "parent ?Mn 1 u = parent M 1 u"
          and pu_lt: "parent M 1 u < ?j0"
        have uL: "u < Lng ?Mn" using uk kL by linarith
        have pau: "hasParent ?Mn 1 u = hasParent M 1 u \<and> parent ?Mn 1 u = parent M 1 u"
          by (rule oper_parent1_prefix_agree[OF L notzero hp j0lt upre uL])
        have hpMu: "hasParent M 1 u" using pau hpu by simp
        have pbku: "parent M 1 (?j0 + sk) < u" using pku pk_eq sk_def Ck by simp
        have ubk: "u < ?j0 + sk" using upre by simp
        have "parent M 1 (?j0 + sk) \<le> parent M 1 u"
          using cg hpbk' pbku ubk hpMu by blast
        thus "parent ?Mn 1 k \<le> parent ?Mn 1 u" using pk_pj Ck pau by simp
      next
        \<comment> \<open>u copy-prefix-parent (the worry): both equal parent M 1 j0\<close>
        assume uge: "?j0 \<le> u" and hpbu: "hasParent M 1 (?j0 + (u - ?j0) mod ?w)"
          and pbu_lt: "parent M 1 (?j0 + (u - ?j0) mod ?w) < ?j0"
          and pu_eq: "parent ?Mn 1 u = parent M 1 (?j0 + (u - ?j0) mod ?w)"
        have suw: "su < ?w" using w0 su_def by simp
        have hpbu': "hasParent M 1 (?j0 + su)" using hpbu su_def by simp
        have pbu_lt': "parent M 1 (?j0 + su) < ?j0" using pbu_lt su_def by simp
        have Cu: "parent M 1 (?j0 + su) = parent M 1 ?j0 \<and> hasParent M 1 ?j0"
          by (rule Cbase[OF suw hpbu' pbu_lt'])
        have "parent ?Mn 1 u = parent M 1 ?j0" using pu_eq su_def Cu by simp
        thus "parent ?Mn 1 k \<le> parent ?Mn 1 u" using pk_pj by simp
      next
        \<comment> \<open>u copy-block-parent: pu >= j0 > pk\<close>
        assume uge: "?j0 \<le> u" and "hasParent M 1 (?j0 + (u - ?j0) mod ?w)"
          and pbu_ge: "?j0 \<le> parent M 1 (?j0 + (u - ?j0) mod ?w)"
          and pu_eq: "parent ?Mn 1 u = ?j0 + ((u - ?j0) div ?w) * ?w
                      + (parent M 1 (?j0 + (u - ?j0) mod ?w) - ?j0)"
        have "?j0 \<le> parent ?Mn 1 u" using pu_eq by simp
        thus "parent ?Mn 1 k \<le> parent ?Mn 1 u" using pk_pj pkj0 by simp
      qed
    next
      \<comment> \<open>D3(k): copy-block-interior with in-block parent; u sits in the same block qk\<close>
      assume kge: "?j0 \<le> k" and hpbk: "hasParent M 1 (?j0 + (k - ?j0) mod ?w)"
        and pbk_ge: "?j0 \<le> parent M 1 (?j0 + (k - ?j0) mod ?w)"
        and pk_eq: "parent ?Mn 1 k = ?j0 + ((k - ?j0) div ?w) * ?w
                    + (parent M 1 (?j0 + (k - ?j0) mod ?w) - ?j0)"
      have skw: "sk < ?w" using w0 sk_def by simp
      have keq: "k = ?j0 + qk * ?w + sk"
      proof -
        have "?j0 + qk * ?w + sk = ?j0 + ((k - ?j0) div ?w * ?w + (k - ?j0) mod ?w)"
          unfolding qk_def sk_def by simp
        also have "\<dots> = ?j0 + (k - ?j0)" by (simp add: div_mult_mod_eq)
        also have "\<dots> = k" using kge by simp
        finally show ?thesis by simp
      qed
      have hpbk': "hasParent M 1 (?j0 + sk)" using hpbk sk_def by simp
      have pbk_ge': "?j0 \<le> parent M 1 (?j0 + sk)" using pbk_ge sk_def by simp
      have parRbk: "nextR M 1 (parent M 1 (?j0 + sk)) (?j0 + sk)"
        using hpbk' unfolding hasParent_def parent_def by (rule theI')
      have pbk_child: "parent M 1 (?j0 + sk) < ?j0 + sk" using parRbk by (simp add: nextR_def nextrel1_def)
      have pk_eq': "parent ?Mn 1 k = ?j0 + qk * ?w + (parent M 1 (?j0 + sk) - ?j0)"
        using pk_eq sk_def qk_def by simp
      have pk_lo: "?j0 + qk * ?w \<le> parent ?Mn 1 k" using pk_eq' pbk_ge' by simp
      have ulo: "?j0 + qk * ?w < u" using pk_lo pku by linarith
      have uhi: "u < ?j0 + qk * ?w + sk" using uk keq by simp
      have uge: "?j0 \<le> u" using ulo by linarith
      \<comment> \<open>u is in block qk: qu = qk, su = u - j0 - qk*w < sk and > parent M1 bk - j0\<close>
      have qkw: "qk * ?w \<le> u - ?j0" using ulo by linarith
      define r where "r = u - ?j0 - qk * ?w"
      have ueq2: "u - ?j0 = r + qk * ?w" using qkw r_def by linarith
      have rlt: "r < ?w" using uhi ulo skw r_def by linarith
      have su_eq: "su = r" using ueq2 rlt by (simp add: su_def mod_mult_self1)
      have qu_eq: "qu = qk"
      proof -
        have "qu = (r + qk * ?w) div ?w" using qu_def ueq2 by simp
        also have "\<dots> = qk" using rlt by (simp add: div_mult_self1)
        finally show ?thesis .
      qed
      have ueq3: "u = ?j0 + qk * ?w + su" using ueq2 su_eq qkw uge by linarith
      have suw: "su < ?w" using rlt su_eq by simp
      have susk: "su < sk" using ueq3 uhi by linarith
      have bu_gt: "parent M 1 (?j0 + sk) < ?j0 + su"
        using ueq3 pku pk_eq' pbk_ge' by linarith
      have bu_lt: "?j0 + su < ?j0 + sk" using susk by simp
      from CU show "parent ?Mn 1 k \<le> parent ?Mn 1 u"
      proof (elim disjE conjE)
        assume "u < ?j0"
        thus ?thesis using uge by linarith
      next
        \<comment> \<open>D2(u) in the same block contradicts pbk >= j0 (vacuous)\<close>
        assume "?j0 \<le> u" and hpbu: "hasParent M 1 (?j0 + (u - ?j0) mod ?w)"
          and pbu_lt: "parent M 1 (?j0 + (u - ?j0) mod ?w) < ?j0"
          and pu_eq: "parent ?Mn 1 u = parent M 1 (?j0 + (u - ?j0) mod ?w)"
        have hpbu': "hasParent M 1 (?j0 + su)" using hpbu su_def by simp
        have "parent M 1 (?j0 + sk) \<le> parent M 1 (?j0 + su)"
          using cg hpbk' bu_gt bu_lt hpbu' by blast
        moreover have "parent M 1 (?j0 + su) < ?j0" using pbu_lt su_def by simp
        ultimately have False using pbk_ge' by linarith
        thus ?thesis by simp
      next
        \<comment> \<open>D3(u) same block: cGTWF M at base column gives the comparison\<close>
        assume "?j0 \<le> u" and hpbu: "hasParent M 1 (?j0 + (u - ?j0) mod ?w)"
          and pbu_ge: "?j0 \<le> parent M 1 (?j0 + (u - ?j0) mod ?w)"
          and pu_eq: "parent ?Mn 1 u = ?j0 + ((u - ?j0) div ?w) * ?w
                      + (parent M 1 (?j0 + (u - ?j0) mod ?w) - ?j0)"
        have hpbu': "hasParent M 1 (?j0 + su)" using hpbu su_def by simp
        have pbu_ge': "?j0 \<le> parent M 1 (?j0 + su)" using pbu_ge su_def by simp
        have le: "parent M 1 (?j0 + sk) \<le> parent M 1 (?j0 + su)"
          using cg hpbk' bu_gt bu_lt hpbu' by blast
        have pu_eq': "parent ?Mn 1 u = ?j0 + qk * ?w + (parent M 1 (?j0 + su) - ?j0)"
          using pu_eq su_def qu_def qu_eq by simp
        show ?thesis using pk_eq' pu_eq' le pbk_ge' pbu_ge' by linarith
      qed
    qed
  qed
qed

text \<open>cgtw_tile, idx1 = 1 (d1pos) branch: cGTWF (M[n]) from cGTWF M [IH] via the
  classified parent readback @{thm [source] oper_d1pos_parent_class}, case analysis
  on the positions of k and u, closed by cGTWF M plus the gate (k = j1 instance).\<close>
lemma cgtw_tile_d1pos:
  fixes M :: pairseq
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and cg: "cGTWF M"
  shows "cGTWF ((M::pairseq)[n])"
proof -
  let ?j1 = "Lng M - 1"  let ?j0 = "parent M 1 ?j1"  let ?w = "?j1 - ?j0"
  let ?Mn = "(M::pairseq)[n]"
  have hpj1: "hasParent M 1 ?j1" using hp i1z by simp
  have parRj1: "nextR M 1 ?j0 ?j1" using hpj1 unfolding hasParent_def parent_def by (rule theI')
  have j0lt: "?j0 < ?j1" using parRj1 by (simp add: nextR_def nextrel1_def)
  have j0lt': "parent M (idx1 M (Lng M - 1)) (Lng M - 1) < Lng M - 1" using j0lt i1z by simp
  have w0: "0 < ?w" using j0lt by linarith
  have gate: "\<And>v. ?j0 < v \<Longrightarrow> v < ?j1 \<Longrightarrow> hasParent M 1 v \<Longrightarrow> ?j0 \<le> parent M 1 v"
    using cg hpj1 by blast
  show "cGTWF ?Mn"
  proof (intro allI impI)
    fix k u
    assume hpk: "hasParent ?Mn 1 k"
       and H: "parent ?Mn 1 k < u \<and> u < k \<and> hasParent ?Mn 1 u"
    from H have pku: "parent ?Mn 1 k < u" and uk: "u < k" and hpu: "hasParent ?Mn 1 u" by auto
    have parRk: "nextR ?Mn 1 (parent ?Mn 1 k) k"
      using hpk unfolding hasParent_def parent_def by (rule theI')
    have kL: "k < Lng ?Mn" using parRk by (simp add: nextR_def nextrel1_def)
    have uL: "u < Lng ?Mn" using uk kL by linarith
    have lenMn: "Lng ?Mn = ?j0 + n * ?w"
      using oper_d1pos_LngM[OF L notzero hp i1z j0lt] by simp
    note CK = oper_d1pos_parent_class[OF L notzero hp i1z j0lt cg hpk]
    note CU = oper_d1pos_parent_class[OF L notzero hp i1z j0lt cg hpu]
    from CK show "parent ?Mn 1 k \<le> parent ?Mn 1 u"
    proof (elim disjE conjE)
      \<comment> \<open>=== k PREFIX: u < k < j0 prefix, cGTWF M at k ===\<close>
      assume kpre: "k < ?j0" and pk_eq: "parent ?Mn 1 k = parent M 1 k"
        and pk_lt: "parent M 1 k < ?j0"
      have ult: "u < ?j0" using uk kpre by linarith
      have pak: "hasParent ?Mn 1 k = hasParent M 1 k \<and> parent ?Mn 1 k = parent M 1 k"
        by (rule oper_parent1_prefix_agree[OF L notzero hp j0lt' _ kL]) (use kpre i1z in simp)
      have hpMk: "hasParent M 1 k" using pak hpk by simp
      have pau: "hasParent ?Mn 1 u = hasParent M 1 u \<and> parent ?Mn 1 u = parent M 1 u"
        by (rule oper_parent1_prefix_agree[OF L notzero hp j0lt' _ uL]) (use ult i1z in simp)
      have hpMu: "hasParent M 1 u" using pau hpu by simp
      have "parent M 1 k < u" using pku pk_eq by simp
      hence "parent M 1 k \<le> parent M 1 u" using cg hpMk uk hpMu by blast
      thus "parent ?Mn 1 k \<le> parent ?Mn 1 u" using pk_eq pau by simp
    next
      \<comment> \<open>=== k BLOCK-START: pk = pj = parent M 1 j0 < j0 ===\<close>
      assume kge: "?j0 \<le> k" and ksz: "(k - ?j0) mod ?w = 0"
        and pk_eq: "parent ?Mn 1 k = parent M 1 ?j0" and pj_lt: "parent M 1 ?j0 < ?j0"
      define qk where "qk = (k - ?j0) div ?w"
      have keq: "k = ?j0 + qk * ?w"
      proof -
        have "?j0 + qk * ?w = ?j0 + ((k - ?j0) div ?w * ?w + (k - ?j0) mod ?w)"
          unfolding qk_def using ksz by simp
        also have "\<dots> = ?j0 + (k - ?j0)" by (simp add: div_mult_mod_eq)
        also have "\<dots> = k" using kge by simp
        finally show ?thesis by simp
      qed
      have qkn: "qk < n"
      proof (rule ccontr)
        assume "\<not> qk < n" hence "n \<le> qk" by simp
        hence "n * ?w \<le> qk * ?w" by (rule mult_le_mono1)
        hence "?j0 + n * ?w \<le> k" using keq by linarith
        thus False using kL lenMn by linarith
      qed
      have hpMj0: "hasParent M 1 ?j0"
        by (rule oper_blockstart_hasParent_j0[OF L notzero hp i1z j0lt qkn]) (use hpk keq in simp)
      have pju: "parent M 1 ?j0 < u" using pku pk_eq by simp
      from CU show "parent ?Mn 1 k \<le> parent ?Mn 1 u"
      proof (elim disjE conjE)
        assume upre: "u < ?j0" and pu_eq: "parent ?Mn 1 u = parent M 1 u"
          and pu_lt: "parent M 1 u < ?j0"
        have pau: "hasParent ?Mn 1 u = hasParent M 1 u \<and> parent ?Mn 1 u = parent M 1 u"
          by (rule oper_parent1_prefix_agree[OF L notzero hp j0lt' _ uL]) (use upre i1z in simp)
        have hpMu: "hasParent M 1 u" using pau hpu by simp
        have "parent M 1 ?j0 \<le> parent M 1 u"
          using cg hpMj0 pju upre hpMu by blast
        thus "parent ?Mn 1 k \<le> parent ?Mn 1 u" using pk_eq pu_eq by simp
      next
        assume "?j0 \<le> u" and "(u - ?j0) mod ?w = 0"
          and pu_eq: "parent ?Mn 1 u = parent M 1 ?j0" and "parent M 1 ?j0 < ?j0"
        show "parent ?Mn 1 k \<le> parent ?Mn 1 u" using pk_eq pu_eq by simp
      next
        assume uge: "?j0 \<le> u" and "0 < (u - ?j0) mod ?w"
          and pu_eq: "parent ?Mn 1 u = parent M 1 (?j0 + (u - ?j0) mod ?w) + ((u - ?j0) div ?w) * ?w"
          and pu_ge: "?j0 \<le> parent M 1 (?j0 + (u - ?j0) mod ?w)"
          and "parent M 1 (?j0 + (u - ?j0) mod ?w) < ?j0 + (u - ?j0) mod ?w"
        have "?j0 \<le> parent ?Mn 1 u" using pu_eq pu_ge by simp
        thus "parent ?Mn 1 k \<le> parent ?Mn 1 u" using pk_eq pj_lt by simp
      qed
    next
      \<comment> \<open>=== k INTERIOR: pk = parent M 1 (j0+sk) + qk*w, same block as u ===\<close>
      assume kge: "?j0 \<le> k" and ksp: "0 < (k - ?j0) mod ?w"
        and pk_eq: "parent ?Mn 1 k
              = parent M 1 (?j0 + (k - ?j0) mod ?w) + ((k - ?j0) div ?w) * ?w"
        and pk_ge: "?j0 \<le> parent M 1 (?j0 + (k - ?j0) mod ?w)"
        and pk_blt: "parent M 1 (?j0 + (k - ?j0) mod ?w) < ?j0 + (k - ?j0) mod ?w"
      define qk where "qk = (k - ?j0) div ?w"
      define sk where "sk = (k - ?j0) mod ?w"
      have skpos: "0 < sk" using ksp sk_def by simp
      have skw: "sk < ?w" using w0 sk_def by simp
      have keq: "k = ?j0 + qk * ?w + sk"
      proof -
        have "?j0 + qk * ?w + sk = ?j0 + ((k - ?j0) div ?w * ?w + (k - ?j0) mod ?w)"
          unfolding qk_def sk_def by simp
        also have "\<dots> = ?j0 + (k - ?j0)" by (simp add: div_mult_mod_eq)
        also have "\<dots> = k" using kge by simp
        finally show ?thesis by simp
      qed
      have qkn: "qk < n"
      proof (rule ccontr)
        assume "\<not> qk < n" hence "n \<le> qk" by simp
        hence "n * ?w \<le> qk * ?w" by (rule mult_le_mono1)
        hence "?j0 + n * ?w \<le> k" using keq by linarith
        thus False using kL lenMn by linarith
      qed
      have psk_ge: "?j0 \<le> parent M 1 (?j0 + sk)" using pk_ge sk_def by simp
      have psk_lt: "parent M 1 (?j0 + sk) < ?j0 + sk" using pk_blt sk_def by simp
      have hpMsk: "hasParent M 1 (?j0 + sk)"
        by (rule oper_interior_hasParent_base[OF L notzero hp i1z j0lt qkn skpos skw]) (use hpk keq in simp)
      have pk_eq': "parent ?Mn 1 k = parent M 1 (?j0 + sk) + qk * ?w"
        using pk_eq sk_def qk_def by simp
      \<comment> \<open>u lies strictly inside block qk: j0+qk*w <= pk < u < k = j0+qk*w+sk\<close>
      have pk_lo: "?j0 + qk * ?w \<le> parent ?Mn 1 k" using pk_eq' psk_ge by simp
      have ulo: "?j0 + qk * ?w < u" using pk_lo pku by linarith
      have uhi: "u < ?j0 + qk * ?w + sk" using uk keq by simp
      have uge: "?j0 \<le> u" using ulo by linarith
      define su where "su = u - ?j0 - qk * ?w"
      have ueq: "u = ?j0 + qk * ?w + su" using su_def ulo by simp
      have supos: "0 < su" using ulo ueq by simp
      have susk: "su < sk" using uhi ueq by simp
      have suw: "su < ?w" using susk skw by simp
      have hpMsu: "hasParent M 1 (?j0 + su)"
        by (rule oper_interior_hasParent_base[OF L notzero hp i1z j0lt qkn supos suw]) (use hpu ueq in simp)
      have pu_read: "parent ?Mn 1 u = parent M 1 (?j0 + su) + qk * ?w"
      proof -
        have base_gt: "?j0 < ?j0 + su" using supos by simp
        have base_lt: "?j0 + su < ?j1" using suw by simp
        have pMge: "?j0 \<le> parent M 1 (?j0 + su)" using gate[OF base_gt base_lt hpMsu] .
        have "parent ?Mn 1 (?j0 + qk * ?w + su) = parent M 1 (?j0 + su) + qk * ?w"
          by (rule oper_parent1_readback[OF L notzero hp i1z j0lt qkn supos suw hpMsu pMge])
        thus ?thesis using ueq by simp
      qed
      \<comment> \<open>cGTWF M at j0+sk gives parent M 1 (j0+sk) <= parent M 1 (j0+su)\<close>
      have lo: "parent M 1 (?j0 + sk) < ?j0 + su" using pku pk_eq' ueq by linarith
      have hi: "?j0 + su < ?j0 + sk" using susk by simp
      have "parent M 1 (?j0 + sk) \<le> parent M 1 (?j0 + su)"
        using cg hpMsk lo hi hpMsu by blast
      thus "parent ?Mn 1 k \<le> parent ?Mn 1 u" using pk_eq' pu_read by simp
    qed
  qed
qed


text \<open>cgEg0 joint ST_PS invariant: cGTWF /\ Eglobal' carried together over the
  ST_PS induction.  The two tiles each need BOTH halves of the IH -- the d0zero
  cGTWF tile needs Eglobal' (its Eg hypothesis, the b = j1 instance), and the
  d0zero Eglobal' tile needs cGTWF (for the keystone prefix-parent collapse) --
  so they cannot be proved by separate inductions; the joint induction supplies
  each tile the full pair @{term "cGTWF M \<and> Eglobal M"} for M.  Below, cGTWF_ST_PS
  and Eglobal_ST_PS fall out as the two projections of cgEg0_ST_PS.\<close>

text \<open>Eglobal' tile, idx1 = 1 (d1pos) branch.  RESIDUAL (joint induction stub).\<close>
lemma Eglobal_tile_d1pos:
  fixes M :: pairseq
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and cg: "cGTWF M"
    and eg: "Eglobal M"
    and n1: "1 \<le> n"
  shows "Eglobal ((M::pairseq)[n])"
  sorry

text \<open>Eglobal' tile, idx1 = 0 (d0zero) branch.  RESIDUAL (joint induction stub).
  Reduces each N[n]-instance to an M-instance via the base map (3 cases: all
  prefix; a,c prefix with b a block-start (base b = j0); all in one copy block).
  Verified empirically clean (python/_eg_tile_cases.py: 3 cases, all readbacks
  hold).  The cross case a<j0, c>=j0 is excluded by the keystone collapse + the
  block-start row-0 minimum.\<close>
lemma Eglobal_tile_d0zero:
  fixes M :: pairseq
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z0: "idx1 M (Lng M - 1) = 0"
    and cg: "cGTWF M"
    and eg: "Eglobal M"
    and n1: "1 \<le> n"
  shows "Eglobal ((M::pairseq)[n])"
proof -
  let ?j1 = "Lng M - 1"  let ?j0 = "parent M (idx1 M (Lng M - 1)) (Lng M - 1)"
  let ?w = "?j1 - ?j0"  let ?N = "(M::pairseq)[n]"
  have hp0: "hasParent M 0 ?j1" using hp i1z0 by simp
  have parRj0j1: "nextR M 0 ?j0 ?j1" using hp0 i1z0
    unfolding hasParent_def parent_def by simp (rule theI')
  have j0lt: "?j0 < ?j1" using parRj0j1 by (simp add: nextR_def nextrel0_def)
  have w0: "0 < ?w" using j0lt by linarith
  have nr0j1: "nextrel0 M ?j0 ?j1" using parRj0j1 by (simp add: nextR_def)
  have j0eq: "?j0 = parent M 0 ?j1" using i1z0 by simp
  have nr0j1u: "nextrel0 M (parent M 0 ?j1) ?j1" using nr0j1 j0eq by simp
  have lenN: "Lng ?N = ?j0 + n * ?w" using operB_gen_LngM[OF L notzero hp j0lt] by simp
  have e1j1: "entry M 1 ?j1 = 0" using i1z0 by (simp add: idx1_def split: if_split_asm)
  \<comment> \<open>row-0 block minima\<close>
  have minL: "\<And>s. s < ?w \<Longrightarrow> entry M 0 ?j0 \<le> entry M 0 (?j0 + s)"
  proof -
    fix s assume "s < ?w"
    hence sw: "s < Lng M - 1 - parent M 0 ?j1" using j0eq by simp
    have "entry M 0 (parent M 0 ?j1) \<le> entry M 0 (parent M 0 ?j1 + s)"
      by (rule parent_block_entry0_min(1)[OF nr0j1u sw])
    thus "entry M 0 ?j0 \<le> entry M 0 (?j0 + s)" using j0eq by simp
  qed
  have minS: "\<And>s. 0 < s \<Longrightarrow> s < ?w \<Longrightarrow> entry M 0 ?j0 < entry M 0 (?j0 + s)"
  proof -
    fix s assume sp: "0 < s" and "s < ?w"
    hence sw: "s < Lng M - 1 - parent M 0 ?j1" using j0eq by simp
    have "entry M 0 (parent M 0 ?j1) < entry M 0 (parent M 0 ?j1 + s)"
      by (rule parent_block_entry0_min(2)[OF nr0j1u sw sp])
    thus "entry M 0 ?j0 < entry M 0 (?j0 + s)" using j0eq by simp
  qed
  \<comment> \<open>Eg: the b = j1 instance of Eglobal M\<close>
  have Eg: "\<And>s. 0 < s \<Longrightarrow> ?j0 + s < ?j1 \<Longrightarrow> hasParent M 1 (?j0 + s)
              \<Longrightarrow> parent M 1 (?j0 + s) < ?j0 \<Longrightarrow> entry M 1 ?j0 \<le> entry M 1 (?j0 + s)"
  proof -
    fix s assume sp: "0 < s" and sj: "?j0 + s < ?j1"
      and hps: "hasParent M 1 (?j0 + s)" and pre: "parent M 1 (?j0 + s) < ?j0"
    from eg have egj1: "hasParent M 0 ?j1 \<and> entry M 1 ?j1 = 0 \<longrightarrow>
        (\<forall>c. parent M 0 ?j1 < c \<and> c < ?j1 \<and> hasParent M 1 c
              \<and> parent M 1 c < parent M 0 ?j1 \<longrightarrow> entry M 1 (parent M 0 ?j1) \<le> entry M 1 c)"
      by blast
    have allc0: "\<forall>c. parent M 0 ?j1 < c \<and> c < ?j1 \<and> hasParent M 1 c
              \<and> parent M 1 c < parent M 0 ?j1 \<longrightarrow> entry M 1 (parent M 0 ?j1) \<le> entry M 1 c"
      using egj1 hp0 e1j1 by blast
    have allc: "\<forall>c. ?j0 < c \<and> c < ?j1 \<and> hasParent M 1 c \<and> parent M 1 c < ?j0
                \<longrightarrow> entry M 1 ?j0 \<le> entry M 1 c"
      using allc0 j0eq by simp
    have c1: "?j0 < ?j0 + s" using sp by simp
    show "entry M 1 ?j0 \<le> entry M 1 (?j0 + s)" using allc c1 sj hps pre by blast
  qed
  show "Eglobal ?N"
  proof (intro allI impI)
    fix b c
    assume Hb: "hasParent ?N 0 b \<and> entry ?N 1 b = 0"
    assume H: "parent ?N 0 b < c \<and> c < b \<and> hasParent ?N 1 c \<and> parent ?N 1 c < parent ?N 0 b"
    let ?a = "parent ?N 0 b"
    from Hb have hpNb: "hasParent ?N 0 b" and e1Nb: "entry ?N 1 b = 0" by auto
    from H have ac: "?a < c" and cb: "c < b" and hpNc: "hasParent ?N 1 c"
      and pca: "parent ?N 1 c < ?a" by auto
    have parRb: "nextR ?N 0 ?a b" using hpNb unfolding hasParent_def parent_def by (rule theI')
    have nr0Nab: "nextrel0 ?N ?a b" using parRb by (simp add: nextR_def)
    have ab: "?a < b" using nr0Nab by (simp add: nextrel0_def)
    have bN: "b < Lng ?N" using nr0Nab by (simp add: nextrel0_def)
    have e0ab: "entry ?N 0 ?a < entry ?N 0 b" using nr0Nab by (simp add: nextrel0_def)
    have valley0: "\<And>j. ?a < j \<Longrightarrow> j < b \<Longrightarrow> entry ?N 0 b \<le> entry ?N 0 j"
      using nr0Nab by (simp add: nextrel0_def)
    have aN: "?a < Lng ?N" using ab bN by linarith
    have cN: "c < Lng ?N" using cb bN by linarith
    have e1Nc_pos: "0 < entry ?N 1 c"
    proof -
      have "nextR ?N 1 (parent ?N 1 c) c" using hpNc unfolding hasParent_def parent_def by (rule theI')
      hence "entry ?N 1 (parent ?N 1 c) < entry ?N 1 c" by (simp add: nextR_def nextrel1_def)
      thus ?thesis by linarith
    qed
    show "entry ?N 1 ?a \<le> entry ?N 1 c"
    proof (cases "b < ?j0")
      case True
      \<comment> \<open>C1: a < c < b < j0, all in the prefix\<close>
      have cj0: "c < ?j0" using cb True by linarith
      have aj0: "?a < ?j0" using ab True by linarith
      have eNa: "entry ?N 1 ?a = entry M 1 ?a"
        using oper_d0zero_entryi_base[OF L notzero hp i1z0 j0lt aN, of 1] aj0 by simp
      have eNc: "entry ?N 1 c = entry M 1 c"
        using oper_d0zero_entryi_base[OF L notzero hp i1z0 j0lt cN, of 1] cj0 by simp
      have eNb: "entry ?N 1 b = entry M 1 b"
        using oper_d0zero_entryi_base[OF L notzero hp i1z0 j0lt bN, of 1] True by simp
      have e1Mb: "entry M 1 b = 0" using e1Nb eNb by simp
      have qn0: "(0::nat) < n" using n1 by simp
      have zcf: "b < ?j0 + (0 + 1) * ?w" using True w0 by linarith
      have nrMab: "nextrel0 M ?a b"
      proof -
        have "nextrel0 M (if ?a < ?j0 then ?a else ?j0 + (?a - ?j0) mod ?w)
                         (if b < ?j0 then b else ?j0 + (b - ?j0) mod ?w)"
          by (rule oper_d0zero_nextrel0_base[OF L notzero hp i1z0 j0lt qn0 zcf nr0Nab])
        thus ?thesis using aj0 True by simp
      qed
      have parRMb: "nextR M 0 ?a b" using nrMab by (simp add: nextR_def)
      have hpMb: "hasParent M 0 b"
        unfolding hasParent_def
      proof (rule ex1I)
        show "nextR M 0 ?a b" by (rule parRMb)
      next
        fix j assume "nextR M 0 j b" thus "j = ?a" using parRMb idxsum_parent0_unique by blast
      qed
      have pMb: "parent M 0 b = ?a"
      proof -
        have "nextR M 0 (parent M 0 b) b"
          using hpMb unfolding hasParent_def parent_def by (rule theI')
        thus ?thesis using parRMb by (rule idxsum_parent0_unique)
      qed
      have pa_c: "hasParent ?N 1 c = hasParent M 1 c \<and> parent ?N 1 c = parent M 1 c"
        by (rule oper_parent1_prefix_agree[OF L notzero hp j0lt cj0 cN])
      have hpMc: "hasParent M 1 c" using pa_c hpNc by simp
      have pMc_lt: "parent M 1 c < ?a" using pa_c pca by simp
      have cond: "parent M 0 b < c \<and> c < b \<and> hasParent M 1 c \<and> parent M 1 c < parent M 0 b"
        using pMb ac cb hpMc pMc_lt by simp
      have "entry M 1 (parent M 0 b) \<le> entry M 1 c" using eg hpMb e1Mb cond by blast
      hence "entry M 1 ?a \<le> entry M 1 c" using pMb by simp
      thus "entry ?N 1 ?a \<le> entry ?N 1 c" using eNa eNc by simp
    next
      case False
      hence bge: "?j0 \<le> b" by simp
      define qb where "qb = (b - ?j0) div ?w"
      define sb where "sb = (b - ?j0) mod ?w"
      have sbw: "sb < ?w" using w0 sb_def by simp
      have bmj: "b - ?j0 < n * ?w" using bN lenN bge by linarith
      have qbn: "qb < n" using less_mult_imp_div_less[OF bmj] qb_def by simp
      have bsplit: "b = ?j0 + qb * ?w + sb"
      proof -
        have "qb * ?w + sb = b - ?j0"
          using div_mult_mod_eq[of "b - ?j0" ?w] qb_def sb_def by (simp add: mult.commute)
        thus ?thesis using bge by linarith
      qed
      have baseb: "?j0 + (b - ?j0) mod ?w = ?j0 + sb" using sb_def by simp
      have eNb: "entry ?N 1 b = entry M 1 (?j0 + sb)"
        using oper_d0zero_entryi_base[OF L notzero hp i1z0 j0lt bN, of 1] bge baseb by simp
      have e1Msb: "entry M 1 (?j0 + sb) = 0" using e1Nb eNb by simp
      have zcf: "b < ?j0 + (qb + 1) * ?w"
      proof -
        have "b = ?j0 + qb * ?w + sb" by (rule bsplit)
        also have "\<dots> < ?j0 + qb * ?w + ?w" using sbw by (rule add_strict_left_mono)
        also have "\<dots> = ?j0 + (qb + 1) * ?w" by (simp add: distrib_right)
        finally show ?thesis .
      qed
      have nrMbase: "nextrel0 M (if ?a < ?j0 then ?a else ?j0 + (?a - ?j0) mod ?w) (?j0 + sb)"
      proof -
        have "nextrel0 M (if ?a < ?j0 then ?a else ?j0 + (?a - ?j0) mod ?w)
                         (if b < ?j0 then b else ?j0 + (b - ?j0) mod ?w)"
          by (rule oper_d0zero_nextrel0_base[OF L notzero hp i1z0 j0lt qbn zcf nr0Nab])
        thus ?thesis using bge baseb by simp
      qed
      \<comment> \<open>position fact (A): a < j0 ==> b is a block-start (sb = 0)\<close>
      have posA: "?a < ?j0 \<Longrightarrow> sb = 0"
      proof -
        assume alt: "?a < ?j0"
        show "sb = 0"
        proof (rule ccontr)
        assume "sb \<noteq> 0"
        hence sbp: "0 < sb" by simp
        let ?bs = "?j0 + qb * ?w"
        have bs_lt_b: "?bs < b" using bsplit sbp by linarith
        have a_lt_bs: "?a < ?bs" using alt by linarith
        have vb: "entry ?N 0 b \<le> entry ?N 0 ?bs" using valley0 a_lt_bs bs_lt_b by simp
        have bsN: "?bs < Lng ?N"
        proof -
          have "qb * ?w < n * ?w" using mult_strict_right_mono[OF qbn w0] .
          thus ?thesis using lenN by simp
        qed
        have bsmod: "?j0 + (?bs - ?j0) mod ?w = ?j0" by simp
        have eNbs: "entry ?N 0 ?bs = entry M 0 ?j0"
          using oper_d0zero_entryi_base[OF L notzero hp i1z0 j0lt bsN, of 0] bsmod by simp
        have eNb0: "entry ?N 0 b = entry M 0 (?j0 + sb)"
          using oper_d0zero_entryi_base[OF L notzero hp i1z0 j0lt bN, of 0] bge baseb by simp
        have "entry M 0 ?j0 < entry M 0 (?j0 + sb)" using minS sbp sbw by simp
        hence "entry ?N 0 ?bs < entry ?N 0 b" using eNbs eNb0 by simp
        thus False using vb by simp
        qed
      qed
      \<comment> \<open>position fact (B): j0 <= a ==> sb > 0\<close>
      have posB: "?j0 \<le> ?a \<Longrightarrow> 0 < sb"
      proof -
        assume age: "?j0 \<le> ?a"
        show "0 < sb"
        proof (rule ccontr)
        assume "\<not> 0 < sb"
        hence sb0: "sb = 0" by simp
        define sa where "sa = (?a - ?j0) mod ?w"
        have basea: "?j0 + (?a - ?j0) mod ?w = ?j0 + sa" using sa_def by simp
        have saw: "sa < ?w" using w0 sa_def by simp
        have eNa0: "entry ?N 0 ?a = entry M 0 (?j0 + sa)"
          using oper_d0zero_entryi_base[OF L notzero hp i1z0 j0lt aN, of 0] age basea by simp
        have eNb0: "entry ?N 0 b = entry M 0 (?j0 + sb)"
          using oper_d0zero_entryi_base[OF L notzero hp i1z0 j0lt bN, of 0] bge baseb by simp
        have "entry M 0 ?j0 \<le> entry M 0 (?j0 + sa)" using minL saw by simp
        moreover have "entry M 0 (?j0 + sb) = entry M 0 ?j0" using sb0 by simp
        ultimately have "entry ?N 0 b \<le> entry ?N 0 ?a" using eNa0 eNb0 by simp
        thus False using e0ab by simp
        qed
      qed
      show "entry ?N 1 ?a \<le> entry ?N 1 c"
      proof (cases "?a < ?j0")
        case True
        \<comment> \<open>C2: a < j0, b a block-start (base b = j0), c forced into the prefix\<close>
        have sb0: "sb = 0" using posA True by simp
        have e1Mj0: "entry M 1 ?j0 = 0" using e1Msb sb0 by simp
        have nrMaj0: "nextrel0 M ?a ?j0" using nrMbase True sb0 by simp
        have parRMj0: "nextR M 0 ?a ?j0" using nrMaj0 by (simp add: nextR_def)
        have hpMj0b: "hasParent M 0 ?j0"
          unfolding hasParent_def
        proof (rule ex1I)
          show "nextR M 0 ?a ?j0" by (rule parRMj0)
        next
          fix j assume "nextR M 0 j ?j0" thus "j = ?a" using parRMj0 idxsum_parent0_unique by blast
        qed
        have pMj0: "parent M 0 ?j0 = ?a"
        proof -
          have "nextR M 0 (parent M 0 ?j0) ?j0"
            using hpMj0b unfolding hasParent_def parent_def by (rule theI')
          thus ?thesis using parRMj0 by (rule idxsum_parent0_unique)
        qed
        \<comment> \<open>alpha: c < j0\<close>
        have cj0: "c < ?j0"
        proof (rule ccontr)
          assume "\<not> c < ?j0" hence cge: "?j0 \<le> c" by simp
          define sc where "sc = (c - ?j0) mod ?w"
          have scw: "sc < ?w" using w0 sc_def by simp
          have basec: "?j0 + (c - ?j0) mod ?w = ?j0 + sc" using sc_def by simp
          note CC = oper_d0zero_parent_class[OF L notzero hp i1z0 j0lt hpNc]
          from CC show False
          proof (elim disjE conjE)
            assume cc: "c < ?j0" and "parent ?N 1 c = parent M 1 c" and "parent M 1 c < ?j0"
            from cc cge show False by simp
          next
            assume "?j0 \<le> c" and hpMsc: "hasParent M 1 (?j0 + (c - ?j0) mod ?w)"
              and psclt: "parent M 1 (?j0 + (c - ?j0) mod ?w) < ?j0"
              and "parent ?N 1 c = parent M 1 (?j0 + (c - ?j0) mod ?w)"
            show False
            proof (cases "sc = 0")
              case True
              have "entry ?N 1 c = entry M 1 (?j0 + sc)"
                using oper_d0zero_entryi_base[OF L notzero hp i1z0 j0lt cN, of 1] cge basec by simp
              hence "entry ?N 1 c = 0" using True e1Mj0 by simp
              thus False using e1Nc_pos by simp
            next
              case False
              hence scp: "0 < sc" by simp
              have hpMsc': "hasParent M 1 (?j0 + sc)" using hpMsc basec by simp
              have psclt': "parent M 1 (?j0 + sc) < ?j0" using psclt basec by simp
              have scj1: "?j0 + sc < ?j1" using scw by simp
              have E: "entry M 1 ?j0 \<le> entry M 1 (?j0 + sc)" using Eg[OF scp scj1 hpMsc' psclt'] .
              have sj1': "parent M 0 ?j1 + sc < ?j1" using scj1 j0eq by simp
              have hpc': "hasParent M 1 (parent M 0 ?j1 + sc)" using hpMsc' j0eq by simp
              have pre': "parent M 1 (parent M 0 ?j1 + sc) < parent M 0 ?j1" using psclt' j0eq by simp
              have E': "entry M 1 (parent M 0 ?j1) \<le> entry M 1 (parent M 0 ?j1 + sc)" using E j0eq by simp
              have key: "hasParent M 1 (parent M 0 ?j1)
                  \<and> parent M 1 (parent M 0 ?j1 + sc) = parent M 1 (parent M 0 ?j1)"
                by (rule oper_d0zero_prefix_parent_eq[OF L hp i1z0 cg scp sj1' hpc' pre' E'])
              have hpMj0': "hasParent M 1 ?j0" using key j0eq by simp
              have "nextR M 1 (parent M 1 ?j0) ?j0"
                using hpMj0' unfolding hasParent_def parent_def by (rule theI')
              hence "entry M 1 (parent M 1 ?j0) < entry M 1 ?j0" by (simp add: nextR_def nextrel1_def)
              thus False using e1Mj0 by simp
            qed
          next
            assume "?j0 \<le> c" and "hasParent M 1 (?j0 + (c - ?j0) mod ?w)"
              and "?j0 \<le> parent M 1 (?j0 + (c - ?j0) mod ?w)"
              and pceq3: "parent ?N 1 c = ?j0 + ((c - ?j0) div ?w) * ?w
                          + (parent M 1 (?j0 + (c - ?j0) mod ?w) - ?j0)"
            have "?j0 \<le> parent ?N 1 c" using pceq3 by simp
            moreover have "parent ?N 1 c < ?j0" using pca True by linarith
            ultimately show False by simp
          qed
        qed
        have eNa: "entry ?N 1 ?a = entry M 1 ?a"
          using oper_d0zero_entryi_base[OF L notzero hp i1z0 j0lt aN, of 1] True by simp
        have eNc: "entry ?N 1 c = entry M 1 c"
          using oper_d0zero_entryi_base[OF L notzero hp i1z0 j0lt cN, of 1] cj0 by simp
        have pa_c: "hasParent ?N 1 c = hasParent M 1 c \<and> parent ?N 1 c = parent M 1 c"
          by (rule oper_parent1_prefix_agree[OF L notzero hp j0lt cj0 cN])
        have hpMc: "hasParent M 1 c" using pa_c hpNc by simp
        have pMc_lt: "parent M 1 c < ?a" using pa_c pca by simp
        have cond: "parent M 0 ?j0 < c \<and> c < ?j0 \<and> hasParent M 1 c \<and> parent M 1 c < parent M 0 ?j0"
          using pMj0 ac cj0 hpMc pMc_lt by simp
        have "entry M 1 (parent M 0 ?j0) \<le> entry M 1 c" using eg hpMj0b e1Mj0 cond by blast
        hence "entry M 1 ?a \<le> entry M 1 c" using pMj0 by simp
        thus "entry ?N 1 ?a \<le> entry ?N 1 c" using eNa eNc by simp
      next
        case False
        \<comment> \<open>C3: j0 <= a, b interior (sb > 0); a, b, c in one copy block\<close>
        hence age: "?j0 \<le> ?a" by simp
        have sbp: "0 < sb" using posB age by simp
        define sa where "sa = (?a - ?j0) mod ?w"
        define qa where "qa = (?a - ?j0) div ?w"
        have saw: "sa < ?w" using w0 sa_def by simp
        have basea: "?j0 + (?a - ?j0) mod ?w = ?j0 + sa" using sa_def by simp
        have amj: "?a - ?j0 < n * ?w" using aN lenN age by linarith
        have qan: "qa < n" using less_mult_imp_div_less[OF amj] qa_def by simp
        have asplit: "?a = ?j0 + qa * ?w + sa"
        proof -
          have "qa * ?w + sa = ?a - ?j0"
            using div_mult_mod_eq[of "?a - ?j0" ?w] qa_def sa_def by (simp add: mult.commute)
          thus ?thesis using age by linarith
        qed
        \<comment> \<open>same block: qa = qb\<close>
        have qa_le: "qa \<le> qb"
        proof (rule ccontr)
          assume "\<not> qa \<le> qb" hence "Suc qb \<le> qa" by simp
          hence "(Suc qb) * ?w \<le> qa * ?w" by (rule mult_le_mono1)
          hence ge: "?w + qb * ?w \<le> qa * ?w" by (simp add: mult_Suc)
          have alt: "?j0 + qa * ?w + sa < b" using ab asplit by linarith
          show False using alt ge bsplit sbw by linarith
        qed
        have qb_le: "qb \<le> qa"
        proof (rule ccontr)
          assume "\<not> qb \<le> qa" hence "Suc qa \<le> qb" by simp
          hence "(Suc qa) * ?w \<le> qb * ?w" by (rule mult_le_mono1)
          hence ge: "?w + qa * ?w \<le> qb * ?w" by (simp add: mult_Suc)
          let ?bs = "?j0 + qb * ?w"
          have bs_lt_b: "?bs < b" using bsplit sbp by linarith
          have a_lt_bs: "?a < ?bs" using asplit saw ge by linarith
          have vb: "entry ?N 0 b \<le> entry ?N 0 ?bs" using valley0 a_lt_bs bs_lt_b by simp
          have bsN: "?bs < Lng ?N"
          proof -
            have "qb * ?w < n * ?w" using mult_strict_right_mono[OF qbn w0] .
            thus ?thesis using lenN by simp
          qed
          have bsmod: "?j0 + (?bs - ?j0) mod ?w = ?j0" by simp
          have eNbs: "entry ?N 0 ?bs = entry M 0 ?j0"
            using oper_d0zero_entryi_base[OF L notzero hp i1z0 j0lt bsN, of 0] bsmod by simp
          have eNb0: "entry ?N 0 b = entry M 0 (?j0 + sb)"
            using oper_d0zero_entryi_base[OF L notzero hp i1z0 j0lt bN, of 0] bge baseb by simp
          have "entry M 0 ?j0 < entry M 0 (?j0 + sb)" using minS sbp sbw by simp
          hence "entry ?N 0 ?bs < entry ?N 0 b" using eNbs eNb0 by simp
          thus False using vb by simp
        qed
        have qab: "qa = qb" using qa_le qb_le by simp
        have bsplit': "b = ?j0 + qa * ?w + sb" using bsplit qab by simp
        have sasb: "sa < sb" using asplit bsplit' ab by linarith
        have nrMab2: "nextrel0 M (?j0 + sa) (?j0 + sb)" using nrMbase age basea by simp
        have parRMbsb: "nextR M 0 (?j0 + sa) (?j0 + sb)" using nrMab2 by (simp add: nextR_def)
        have hpMbsb: "hasParent M 0 (?j0 + sb)"
          unfolding hasParent_def
        proof (rule ex1I)
          show "nextR M 0 (?j0 + sa) (?j0 + sb)" by (rule parRMbsb)
        next
          fix j assume "nextR M 0 j (?j0 + sb)"
          thus "j = ?j0 + sa" using parRMbsb idxsum_parent0_unique by blast
        qed
        have pMbsb: "parent M 0 (?j0 + sb) = ?j0 + sa"
        proof -
          have "nextR M 0 (parent M 0 (?j0 + sb)) (?j0 + sb)"
            using hpMbsb unfolding hasParent_def parent_def by (rule theI')
          thus ?thesis using parRMbsb by (rule idxsum_parent0_unique)
        qed
        have cge: "?j0 \<le> c" using ac age by linarith
        define sc where "sc = c - (?j0 + qa * ?w)"
        have c_lo: "?j0 + qa * ?w + sa < c" using ac asplit by linarith
        have c_hi: "c < ?j0 + qa * ?w + sb" using cb bsplit' by linarith
        have cge2: "?j0 + qa * ?w \<le> c" using c_lo by linarith
        have csplit: "c = ?j0 + qa * ?w + sc" using sc_def cge2 by simp
        have scsa: "sa < sc" using csplit c_lo by linarith
        have scsb: "sc < sb" using csplit c_hi by linarith
        have scw: "sc < ?w" using scsb sbw by linarith
        have cmj: "c - ?j0 = sc + qa * ?w" using csplit by simp
        have scmod: "(c - ?j0) mod ?w = sc" using cmj scw by (simp add: mod_mult_self1)
        have scdiv: "(c - ?j0) div ?w = qa"
        proof -
          have "(c - ?j0) div ?w = (sc + qa * ?w) div ?w" using cmj by simp
          also have "\<dots> = qa" using scw by (simp add: div_mult_self1)
          finally show ?thesis .
        qed
        have basec: "?j0 + (c - ?j0) mod ?w = ?j0 + sc" using scmod by simp
        note CC = oper_d0zero_parent_class[OF L notzero hp i1z0 j0lt hpNc]
        have Mfacts: "hasParent M 1 (?j0 + sc) \<and> parent M 1 (?j0 + sc) < ?j0 + sa"
          using CC
        proof (elim disjE conjE)
          assume cc: "c < ?j0" and "parent ?N 1 c = parent M 1 c" and "parent M 1 c < ?j0"
          from cc cge show ?thesis by simp
        next
          assume "?j0 \<le> c" and h: "hasParent M 1 (?j0 + (c - ?j0) mod ?w)"
            and p: "parent M 1 (?j0 + (c - ?j0) mod ?w) < ?j0"
            and "parent ?N 1 c = parent M 1 (?j0 + (c - ?j0) mod ?w)"
          have "hasParent M 1 (?j0 + sc)" using h basec by simp
          moreover have "parent M 1 (?j0 + sc) < ?j0 + sa" using p basec by simp
          ultimately show ?thesis by simp
        next
          assume "?j0 \<le> c" and h: "hasParent M 1 (?j0 + (c - ?j0) mod ?w)"
            and pge: "?j0 \<le> parent M 1 (?j0 + (c - ?j0) mod ?w)"
            and peq: "parent ?N 1 c = ?j0 + ((c - ?j0) div ?w) * ?w
                      + (parent M 1 (?j0 + (c - ?j0) mod ?w) - ?j0)"
          have hM: "hasParent M 1 (?j0 + sc)" using h basec by simp
          have peq2: "parent ?N 1 c = ?j0 + qa * ?w + (parent M 1 (?j0 + sc) - ?j0)"
            using peq scdiv basec by simp
          have "?j0 + qa * ?w + (parent M 1 (?j0 + sc) - ?j0) < ?j0 + qa * ?w + sa"
            using peq2 pca asplit by linarith
          hence "parent M 1 (?j0 + sc) - ?j0 < sa" by simp
          hence "parent M 1 (?j0 + sc) < ?j0 + sa" using pge by linarith
          thus ?thesis using hM by simp
        qed
        have hpMc2: "hasParent M 1 (?j0 + sc)" using Mfacts by simp
        have pMc2: "parent M 1 (?j0 + sc) < ?j0 + sa" using Mfacts by simp
        have cond: "parent M 0 (?j0 + sb) < ?j0 + sc \<and> ?j0 + sc < ?j0 + sb
                    \<and> hasParent M 1 (?j0 + sc) \<and> parent M 1 (?j0 + sc) < parent M 0 (?j0 + sb)"
          using pMbsb scsa scsb hpMc2 pMc2 by simp
        have "entry M 1 (parent M 0 (?j0 + sb)) \<le> entry M 1 (?j0 + sc)"
          using eg hpMbsb e1Msb cond by blast
        hence le: "entry M 1 (?j0 + sa) \<le> entry M 1 (?j0 + sc)" using pMbsb by simp
        have eNa: "entry ?N 1 ?a = entry M 1 (?j0 + sa)"
          using oper_d0zero_entryi_base[OF L notzero hp i1z0 j0lt aN, of 1] age basea by simp
        have eNc: "entry ?N 1 c = entry M 1 (?j0 + sc)"
          using oper_d0zero_entryi_base[OF L notzero hp i1z0 j0lt cN, of 1] cge basec by simp
        show "entry ?N 1 ?a \<le> entry ?N 1 c" using eNa eNc le by simp
      qed
    qed
  qed
qed

lemma cgEg0_ST_PS:
  assumes "N \<in> ST_PS"
  shows "cGTWF N \<and> Eglobal N"
  using assms
proof (induct N rule: ST_PS.induct)
  case (diag a b)
  have uv: "a \<le> b" by (rule diag.hyps)
  let ?M = "diagSeq a b"
  have cgD: "cGTWF ?M"
  proof (intro allI impI)
    fix k u
    assume hpk: "hasParent ?M 1 k"
       and H: "parent ?M 1 k < u \<and> u < k \<and> hasParent ?M 1 u"
    have parR: "nextR ?M 1 (parent ?M 1 k) k"
      using hpk unfolding hasParent_def parent_def by (rule theI')
    have i1: "(1::nat) \<le> 1" by simp
    have suc: "Suc (parent ?M 1 k) = k" by (rule kfwd_nextR_diagSeq_parent[OF uv i1 parR])
    have False using H suc by linarith
    thus "parent ?M 1 k \<le> parent ?M 1 u" by simp
  qed
  have egD: "Eglobal ?M"
  proof (intro allI impI)
    fix b' c
    assume Hb: "hasParent ?M 0 b' \<and> entry ?M 1 b' = 0"
       and H: "parent ?M 0 b' < c \<and> c < b' \<and> hasParent ?M 1 c
               \<and> parent ?M 1 c < parent ?M 0 b'"
    have hpb0: "hasParent ?M 0 b'" using Hb by blast
    have parR0: "nextR ?M 0 (parent ?M 0 b') b'"
      using hpb0 unfolding hasParent_def parent_def by (rule theI')
    have i0: "(0::nat) \<le> 1" by simp
    have suc: "Suc (parent ?M 0 b') = b'" by (rule kfwd_nextR_diagSeq_parent[OF uv i0 parR0])
    have False using H suc by linarith
    thus "entry ?M 1 (parent ?M 0 b') \<le> entry ?M 1 c" by simp
  qed
  show ?case using cgD egD by blast
next
  case (oper M n)
  have IHc: "cGTWF M" and IHe: "Eglobal M" using oper.hyps by blast+
  have MST: "M \<in> ST_PS" using oper.hyps by blast
  have MT: "M \<in> T_PS" by (rule ST_PS_T_PS[OF MST])
  have n1: "1 \<le> n" using oper.hyps by blast
  show ?case
  proof (cases "Lng M - 1 = 0")
    case True
    have "(M::pairseq)[n] = M" using True by (simp add: oper_def Let_def)
    thus ?thesis using IHc IHe by simp
  next
    case False
    hence L: "1 < Lng M" by linarith
    show ?thesis
    proof (cases "Lng M - 1 = 0
                  \<or> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)
                  \<or> \<not> hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)")
      case True
      have eqP: "(M::pairseq)[n] = Pred M" by (rule oper_nontile_eq_Pred[OF True])
      have "cGTWF (Pred M)" by (rule cgtw_pred[OF MT L IHc])
      moreover have "Eglobal (Pred M)" by (rule Eglobal_pred[OF L IHe])
      ultimately show ?thesis using eqP by simp
    next
      case False
      have nz: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)" using False by blast
      have hpar: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)" using False by blast
      show ?thesis
      proof (cases "idx1 M (Lng M - 1) = 1")
        case True
        have "cGTWF ((M::pairseq)[n])" by (rule cgtw_tile_d1pos[OF L nz hpar True IHc])
        moreover have "Eglobal ((M::pairseq)[n])"
          by (rule Eglobal_tile_d1pos[OF L nz hpar True IHc IHe n1])
        ultimately show ?thesis by blast
      next
        case False
        have i1z0: "idx1 M (Lng M - 1) = 0"
          using False by (simp add: idx1_def split: if_split_asm)
        have e1j1: "entry M 1 (Lng M - 1) = 0"
          using i1z0 by (simp add: idx1_def split: if_split_asm)
        have hp0: "hasParent M 0 (Lng M - 1)" using hpar i1z0 by simp
        \<comment> \<open>Eg: the b = j1 instance of Eglobal M (entry M 1 j1 = 0)\<close>
        have Eg: "\<And>s. 0 < s \<Longrightarrow> parent M 0 (Lng M - 1) + s < Lng M - 1
              \<Longrightarrow> hasParent M 1 (parent M 0 (Lng M - 1) + s)
              \<Longrightarrow> parent M 1 (parent M 0 (Lng M - 1) + s) < parent M 0 (Lng M - 1)
              \<Longrightarrow> entry M 1 (parent M 0 (Lng M - 1))
                  \<le> entry M 1 (parent M 0 (Lng M - 1) + s)"
        proof -
          fix s assume sp: "0 < s"
            and sj: "parent M 0 (Lng M - 1) + s < Lng M - 1"
            and hps: "hasParent M 1 (parent M 0 (Lng M - 1) + s)"
            and pre: "parent M 1 (parent M 0 (Lng M - 1) + s) < parent M 0 (Lng M - 1)"
          have c1: "parent M 0 (Lng M - 1) < parent M 0 (Lng M - 1) + s" using sp by simp
          show "entry M 1 (parent M 0 (Lng M - 1))
                  \<le> entry M 1 (parent M 0 (Lng M - 1) + s)"
            using IHe hp0 e1j1 c1 sj hps pre by blast
        qed
        have "cGTWF ((M::pairseq)[n])"
          by (rule cgtw_tile_d0zero[OF L nz hpar i1z0 IHc Eg])
        moreover have "Eglobal ((M::pairseq)[n])"
          by (rule Eglobal_tile_d0zero[OF L nz hpar i1z0 IHc IHe n1])
        ultimately show ?thesis by blast
      qed
    qed
  qed
qed

lemma cGTWF_ST_PS:
  assumes "N \<in> ST_PS"
  shows "cGTWF N"
  using cgEg0_ST_PS[OF assms] by blast

lemma Eglobal_ST_PS:
  assumes "N \<in> ST_PS"
  shows "Eglobal N"
  using cgEg0_ST_PS[OF assms] by blast




text \<open>§6.7 operCA, idx1 = 0 (d0zero) branch: RedCondA (N[n]) from N standard in
  ST_PS.  operCA_tiling_cond and operCA_tiling_row0 are idx1-agnostic, so row-0 is
  free; the within-block row-1 +1 is operCA_tiling_within1_via_reflect (also
  idx1-agnostic) fed the d0zero readbacks: hpN by oper_d0zero_interior_hasParent_base
  (s >= 0), ex by oper_d0zero_entryi_base, and ep by the base-readback
  oper_d0zero_parent1_readback (whose lift has base pb = parent N1(j0+s)).\<close>

lemma operCA_d0zero:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z0: "idx1 N (Lng N - 1) = 0"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and condA: "RedCondA N"
    and n1: "1 \<le> n"
  shows "RedCondA ((N::pairseq)[n])"
proof (rule operCA_tiling_cond[OF L notzero hp j0lt condA])
  fix x assume "hasParent ((N::pairseq)[n]) 0 x"
  thus "entry ((N::pairseq)[n]) 0 (parent ((N::pairseq)[n]) 0 x) + 1
          = entry ((N::pairseq)[n]) 0 x"
    by (rule operCA_tiling_row0[OF L notzero hp j0lt condA n1])
next
  fix x
  assume ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> x"
    and hpx: "hasParent ((N::pairseq)[n]) 1 x"
  let ?j1 = "Lng N - 1"  let ?j0 = "parent N (idx1 N (Lng N - 1)) ?j1"  let ?w = "?j1 - ?j0"
  let ?Mn = "(N::pairseq)[n]"
  have w0: "0 < ?w" using j0lt by linarith
  have lenMn: "Lng ?Mn = ?j0 + n * ?w"
    using operB_gen_LngM[OF L notzero hp j0lt] by simp
  have parRx: "nextR ?Mn 1 (parent ?Mn 1 x) x"
    using hpx unfolding hasParent_def parent_def by (rule theI')
  have xL: "x < Lng ?Mn" using parRx by (simp add: nextR_def nextrel1_def)
  define q where "q = (x - ?j0) div ?w"
  define s where "s = (x - ?j0) mod ?w"
  have sw: "s < ?w" using w0 by (simp add: s_def)
  have xdecomp: "x = ?j0 + q * ?w + s"
  proof -
    have "?j0 + q * ?w + s = ?j0 + ((x - ?j0) div ?w * ?w + (x - ?j0) mod ?w)"
      unfolding q_def s_def by simp
    also have "\<dots> = ?j0 + (x - ?j0)" by (simp add: div_mult_mod_eq)
    also have "\<dots> = x" using ge by simp
    finally show ?thesis by simp
  qed
  have qn: "q < n"
  proof (rule ccontr)
    assume "\<not> q < n" hence "n \<le> q" by simp
    hence "n * ?w \<le> q * ?w" by (rule mult_le_mono1)
    hence "?j0 + n * ?w \<le> x" using xdecomp by linarith
    moreover have "x < ?j0 + n * ?w" using xL lenMn by simp
    ultimately show False by linarith
  qed
  let ?base = "?j0 + s"
  let ?pb = "parent N 1 ?base"
  let ?c = "if ?pb < ?j0 then ?pb else ?j0 + q * ?w + (?pb - ?j0)"
  have hpyf: "hasParent ?Mn 1 (?j0 + q * ?w + s)" using hpx xdecomp by simp
  have hpN: "hasParent N 1 ?base"
    by (rule oper_d0zero_interior_hasParent_base[OF L notzero hp i1z0 j0lt qn sw hpyf])
  have parRb: "nextR N 1 ?pb ?base" using hpN unfolding hasParent_def parent_def by (rule theI')
  have pblt: "?pb < ?base" using parRb by (simp add: nextR_def nextrel1_def)
  have pbsub: "?pb - ?j0 < ?w" using pblt sw by linarith
  \<comment> \<open>ex: row-1 of x reads off its base\<close>
  have ex: "entry ?Mn 1 x = entry N 1 ?base"
  proof -
    have "entry ?Mn 1 x = entry N 1 (if x < ?j0 then x else ?j0 + (x - ?j0) mod ?w)"
      by (rule oper_d0zero_entryi_base[OF L notzero hp i1z0 j0lt xL])
    moreover have "(x - ?j0) mod ?w = s" using s_def by simp
    moreover have "\<not> x < ?j0" using ge by simp
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>ep: row-1 of the N[n]-parent reads off parent N 1 base\<close>
  have pread: "parent ?Mn 1 x = ?c"
    using oper_d0zero_parent1_readback[OF L notzero hp i1z0 j0lt qn sw hpN] xdecomp by simp
  have cL: "?c < Lng ?Mn"
  proof -
    have "parent ?Mn 1 x < Lng ?Mn" using parRx by (simp add: nextR_def nextrel1_def)
    thus ?thesis using pread by simp
  qed
  have basec: "(if ?c < ?j0 then ?c else ?j0 + (?c - ?j0) mod ?w) = ?pb"
  proof (cases "?pb < ?j0")
    case True thus ?thesis by simp
  next
    case False
    hence cval: "?c = ?j0 + q * ?w + (?pb - ?j0)" by simp
    have "(?c - ?j0) mod ?w = (q * ?w + (?pb - ?j0)) mod ?w" using cval by simp
    also have "\<dots> = (?pb - ?j0) mod ?w" by simp
    also have "\<dots> = ?pb - ?j0" using pbsub by simp
    finally have "(?c - ?j0) mod ?w = ?pb - ?j0" .
    moreover have "\<not> ?c < ?j0" using cval by simp
    ultimately show ?thesis using False by simp
  qed
  have ep: "entry ?Mn 1 (parent ?Mn 1 x) = entry N 1 ?pb"
  proof -
    have "entry ?Mn 1 ?c = entry N 1 (if ?c < ?j0 then ?c else ?j0 + (?c - ?j0) mod ?w)"
      by (rule oper_d0zero_entryi_base[OF L notzero hp i1z0 j0lt cL])
    thus ?thesis using basec pread by simp
  qed
  show "entry ?Mn 1 (parent ?Mn 1 x) + 1 = entry ?Mn 1 x"
    by (rule operCA_tiling_within1_via_reflect[OF condA hpN ex ep])
qed


text \<open>§6.7 operCA, FULL (both i1): RedCondA (N[n]) for a tiling step from a
  standard N in ST_PS.  i1 = 1 (d1pos) is discharged by
  @{thm [source] operCA_via_gate_hpMs}, fed the gate (the k = j1 instance of
  cGTWF N via @{thm [source] cGTWF_ST_PS}) and hpMs packaged from the reverse
  readbacks (@{thm [source] oper_blockstart_hasParent_j0} for the block start,
  @{thm [source] oper_interior_hasParent_base} for interior columns).  i1 = 0
  (d0zero) is discharged by operCA_d0zero.\<close>

lemma operCA_tiling_full:
  assumes Nst: "N \<in> ST_PS" and condA: "RedCondA N" and condB: "RedCondB N"
    and n1: "1 \<le> n"
    and tile: "\<not> (Lng N - 1 = 0
                  \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                  \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1))"
  shows "RedCondA ((N::pairseq)[n])"
proof -
  from tile have ndeg: "Lng N - 1 \<noteq> 0"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)" by auto
  have L: "1 < Lng N" using ndeg by linarith
  show ?thesis
  proof (cases "idx1 N (Lng N - 1) = 1")
    case True
    note i1z = True
    have hpj1: "hasParent N 1 (Lng N - 1)" using hp i1z by simp
    have parRj1: "nextR N 1 (parent N 1 (Lng N - 1)) (Lng N - 1)"
      using hpj1 unfolding hasParent_def parent_def by (rule theI')
    have j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
      using parRj1 by (simp add: nextR_def nextrel1_def)
    have cg: "cGTWF N" by (rule cGTWF_ST_PS[OF Nst])
    have gate: "\<And>u. parent N 1 (Lng N - 1) < u \<Longrightarrow> u < Lng N - 1 \<Longrightarrow> hasParent N 1 u
                 \<Longrightarrow> parent N 1 (Lng N - 1) \<le> parent N 1 u"
      using cg hpj1 by blast
    have hpMs: "\<And>y. parent N 1 (Lng N - 1) \<le> y \<Longrightarrow> y < Lng ((N::pairseq)[n])
                 \<Longrightarrow> hasParent ((N::pairseq)[n]) 1 y
                 \<Longrightarrow> hasParent N 1 (parent N 1 (Lng N - 1)
                        + (y - parent N 1 (Lng N - 1))
                           mod (Lng N - 1 - parent N 1 (Lng N - 1)))"
    proof -
      fix y
      assume yge: "parent N 1 (Lng N - 1) \<le> y" and yL: "y < Lng ((N::pairseq)[n])"
        and hpy: "hasParent ((N::pairseq)[n]) 1 y"
      let ?j1 = "Lng N - 1"  let ?j0 = "parent N 1 ?j1"  let ?w = "?j1 - ?j0"
      have w0: "0 < ?w" using j0lt by linarith
      have lenMn: "Lng ((N::pairseq)[n]) = ?j0 + n * ?w"
        using oper_d1pos_LngM[OF L notzero hp i1z j0lt] by simp
      define q where "q = (y - ?j0) div ?w"
      define s where "s = (y - ?j0) mod ?w"
      have sw: "s < ?w" using w0 by (simp add: s_def)
      have ydecomp: "y = ?j0 + q * ?w + s"
      proof -
        have "?j0 + q * ?w + s = ?j0 + ((y - ?j0) div ?w * ?w + (y - ?j0) mod ?w)"
          unfolding q_def s_def by simp
        also have "\<dots> = ?j0 + (y - ?j0)" by (simp add: div_mult_mod_eq)
        also have "\<dots> = y" using yge by simp
        finally show ?thesis by simp
      qed
      have qn: "q < n"
      proof (rule ccontr)
        assume "\<not> q < n" hence "n \<le> q" by simp
        hence "n * ?w \<le> q * ?w" by (rule mult_le_mono1)
        hence "?j0 + n * ?w \<le> y" using ydecomp by linarith
        moreover have "y < ?j0 + n * ?w" using yL lenMn by simp
        ultimately show False by linarith
      qed
      show "hasParent N 1 (?j0 + (y - ?j0) mod ?w)"
      proof (cases "s = 0")
        case True
        have ybs: "y = ?j0 + q * ?w" using ydecomp True by simp
        have "hasParent N 1 ?j0"
          by (rule oper_blockstart_hasParent_j0[OF L notzero hp i1z j0lt qn]) (use hpy ybs in simp)
        thus ?thesis using True s_def by simp
      next
        case False
        hence spos: "0 < s" by simp
        have "hasParent N 1 (?j0 + s)"
          by (rule oper_interior_hasParent_base[OF L notzero hp i1z j0lt qn spos sw])
             (use hpy ydecomp in simp)
        thus ?thesis using s_def by simp
      qed
    qed
    show ?thesis
      using operCA_via_gate_hpMs[OF L notzero hp i1z j0lt condA n1] hpMs gate by blast
  next
    case False
    have i1z0: "idx1 N (Lng N - 1) = 0"
      using False by (simp add: idx1_def split: if_split_asm)
    have parRj0: "nextR N (idx1 N (Lng N - 1))
                    (parent N (idx1 N (Lng N - 1)) (Lng N - 1)) (Lng N - 1)"
      using hp unfolding hasParent_def parent_def by (rule theI')
    have j0lt0: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
      using parRj0 i1z0 by (simp add: nextR_def nextrel0_def)
    show ?thesis by (rule operCA_d0zero[OF L notzero hp i1z0 j0lt0 condA n1])
  qed
qed


text \<open>§6.7 standard-form reducedness ST_PS \<subseteq> RT_PS (the theorem
  @{thm [source] m_6_7_standard_reduced}), now discharged: operCA by
  @{thm [source] operCA_tiling_full} (modulo the i1 = 0 residuals) and operCB by
  the green @{thm [source] operCB_tiling}.\<close>

lemma m_6_7_ST_PS_subseteq_RT_PS: "ST_PS \<subseteq> RT_PS"
  by (rule m_6_7_standard_reduced[OF operCA_tiling_full operCB_tiling])

end
