theory Frontier_6_087
  imports Support_6_066
begin

section \<open>Graduated from pss_wip.thy (2026-06-11): §6.5/§6.6/§6.7 completion
  (gate-free operCA, monoCong closed form, A4 corollaries, reduced_oper,
  Red-oper commutativity)\<close>


text \<open>
  Work-in-progress §6.7 lemmas (operCA boundary-valley discharge: the H1/H2 le0
  reflections and the readback assembly).  Stable results graduate back into
  the shared §6 support layer.  H1 (block, cross-block le0 reflection) already landed in
  the shared §6 support layer as @{thm [source] oper_d1pos_le0_cross_back}.
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

text \<open>§6.7 oper-tiling ESCAPE READBACK, idx1 = 1 (d1pos), interior offset 0 < s < w:
  when the base column's row-1 parent ESCAPES into the prefix
  (parent N 1 (j0+s) < j0), the N[n]-parent of the lifted column j0+q*w+s is that
  same prefix column VERBATIM.  This is the gate-free third branch of the d1pos
  parent classification; together with @{thm [source] oper_parent1_readback}
  (in-block parent) and @{thm [source] oper_parent1_readback_boundary_uncond}
  (block start) it eliminates the cGTWF gate from operCA entirely -- matching the
  article's one-line proof of 標準形の簡約性 (reducedness preserved by oper, no
  ST_PS-specific invariant).  Empirically verified with NO hypotheses beyond the
  tiling trigger (1292665 in-block parent checks, 0 mismatches).
  Proof: the dichotomy @{thm [source] oper_interior_parent_inblock} splits the
  actual N[n]-parent p of y = j0+q*w+s.  SAME-BLOCK p = j0+q*w+sp is impossible:
  j0+sp would then be a row-1 parent of j0+s in N (le0 by
  @{thm [source] oper_d1pos_le0_base_back}; valley by lifting every N-competitor
  into block q via @{thm [source] oper_d1pos_le0_block_lift_fwd} and reading the
  N[n] valley back through the periodic row 1), so parent N 1 (j0+s) = j0+sp >= j0
  by uniqueness, contradicting the escape.  PREFIX p < j0: nextrel1 N p (j0+s)
  holds (le0 via the N[n] ancestor-interval down to the block start q, the prefix
  reflection @{thm [source] oper_d1pos_le0_prefix_back}, and le0 N j0 (j0+s)
  inside the nextrel1 N j0 j1 edge; valley by lifting prefix competitors via
  @{thm [source] oper_d1pos_le0_prefix_lift_fwd} and in-block competitors via
  @{thm [source] oper_d1pos_le0_block_lift_fwd}), so p = parent N 1 (j0+s) by
  @{thm [source] nextR1_unique}.\<close>

lemma oper_d1pos_parent1_readback_escape:
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
    and hpMs: "hasParent N 1 (parent N 1 (Lng N - 1) + s)"
    and pesc: "parent N 1 (parent N 1 (Lng N - 1) + s) < parent N 1 (Lng N - 1)"
  shows "parent ((N::pairseq)[n]) 1
            (parent N 1 (Lng N - 1) + q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s)
         = parent N 1 (parent N 1 (Lng N - 1) + s)"
proof -
  let ?j1 = "Lng N - 1"  let ?j0 = "parent N 1 ?j1"  let ?w = "?j1 - ?j0"
  let ?Mn = "(N::pairseq)[n]"  let ?y = "?j0 + q * ?w + s"  let ?base = "?j0 + s"
  let ?p = "parent ?Mn 1 ?y"  let ?pb = "parent N 1 ?base"
  have w0: "0 < ?w" using j0lt by linarith
  have n0: "0 < n" using qn by simp
  have n1: "1 \<le> n" using n0 by simp
  have NT: "N \<in> T_PS" using L by (cases N) (auto simp: T_PS_def)
  have j0lt': "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1" using j0lt i1z by simp
  have pj0eq: "parent N (idx1 N ?j1) ?j1 = ?j0" using i1z by simp
  have lenMn: "Lng ?Mn = ?j0 + n * ?w"
    using oper_d1pos_LngM[OF L notzero hp i1z j0lt] by simp
  have basej1: "?base < ?j1" using sw by linarith
  have baseLtN: "?base < Lng N" using basej1 L by linarith
  \<comment> \<open>the N-edge pb -> base and its valley\<close>
  have parRb: "nextR N 1 ?pb ?base" using hpMs unfolding hasParent_def parent_def by (rule theI')
  have nr1b: "nextrel1 N ?pb ?base" using parRb by (simp add: nextR_def)
  have valleyN: "\<And>j. ?pb < j \<Longrightarrow> le0 N j ?base \<Longrightarrow> entry N 1 ?base \<le> entry N 1 j"
    using nr1b unfolding nextrel1_def by blast
  \<comment> \<open>y bounds and the N[n]-edge p -> y with its valley\<close>
  have yLt: "?y < Lng ?Mn"
  proof -
    have "q * ?w + s < ?w + q * ?w" using sw by linarith
    also have "\<dots> = Suc q * ?w" by (simp add: mult_Suc)
    also have "\<dots> \<le> n * ?w" using qn by (intro mult_le_mono1) simp
    finally show ?thesis using lenMn by simp
  qed
  have parRy: "nextR ?Mn 1 ?p ?y" using hpy unfolding hasParent_def parent_def by (rule theI')
  have nr1y: "nextrel1 ?Mn ?p ?y" using parRy by (simp add: nextR_def)
  have ply: "?p < ?y" using nr1y by (simp add: nextrel1_def)
  have le0py: "le0 ?Mn ?p ?y" using nr1y by (simp add: nextrel1_def)
  have epy: "entry ?Mn 1 ?p < entry ?Mn 1 ?y" using nr1y by (simp add: nextrel1_def)
  have valleyMn: "\<And>j. ?p < j \<Longrightarrow> le0 ?Mn j ?y \<Longrightarrow> entry ?Mn 1 ?y \<le> entry ?Mn 1 j"
    using nr1y unfolding nextrel1_def by blast
  have ey: "entry ?Mn 1 ?y = entry N 1 ?base"
    by (rule oper_d1pos_entry1[OF L notzero hp i1z j0lt qn sw])
  \<comment> \<open>le0 N j0 base: base is an index-intermediate point of the nextrel1 N j0 j1 edge\<close>
  have hpj1: "hasParent N 1 ?j1" using hp i1z by simp
  have parj1: "nextR N 1 ?j0 ?j1" using hpj1 unfolding hasParent_def parent_def by (rule theI')
  have nr1j1: "nextrel1 N ?j0 ?j1" using parj1 by (simp add: nextR_def)
  have le0j0j1: "le0 N ?j0 ?j1" using nr1j1 by (simp add: nextrel1_def)
  have le0j0base: "le0 N ?j0 ?base"
  proof -
    have leRj0j1: "leR N 0 ?j0 ?j1" using le0j0j1 by (simp add: leR_def)
    have "leR N 0 ?j0 ?base"
      by (rule m_5_1_ancestor_tree_1[OF NT leRj0j1 le_add1]) (use basej1 in simp)
    thus ?thesis by (simp add: leR_def)
  qed
  have j0ltMn: "?j0 < Lng ?Mn" using lenMn n0 w0 by simp
  have NnT: "?Mn \<in> T_PS" using j0ltMn by (cases ?Mn) (auto simp: T_PS_def)
  \<comment> \<open>STEP 1: the same-block branch of the dichotomy is impossible under the escape\<close>
  have plt: "?p < ?j0"
  proof (rule ccontr)
    assume "\<not> ?p < ?j0"
    hence pge: "?j0 \<le> ?p" by simp
    have dq: "(?p - ?j0) div ?w = q"
      using oper_interior_parent_inblock[OF L notzero hp i1z j0lt qn spos sw hpy] pge by simp
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
    have sps: "sp < s" using ply pdecomp by simp
    have reachblk: "le0 ?Mn (?j0 + q * ?w + sp) (?j0 + q * ?w + s)" using le0py pdecomp by simp
    have le0spb: "le0 N (?j0 + sp) ?base"
      by (rule oper_d1pos_le0_base_back[OF L notzero hp i1z j0lt qn sps sw reachblk])
    have esp: "entry ?Mn 1 ?p = entry N 1 (?j0 + sp)"
      using oper_d1pos_entry1[OF L notzero hp i1z j0lt qn spw] pdecomp by simp
    have e_lt: "entry N 1 (?j0 + sp) < entry N 1 ?base" using epy ey esp by simp
    have vall: "\<forall>j. ?j0 + sp < j \<and> le0 N j ?base \<longrightarrow> entry N 1 ?base \<le> entry N 1 j"
    proof (intro allI impI)
      fix j assume H: "?j0 + sp < j \<and> le0 N j ?base"
      from H have jgt: "?j0 + sp < j" and jle0: "le0 N j ?base" by auto
      have jb: "j \<le> ?base" using jle0 nextrel0_rtrancl_mono[of N j ?base] by (simp add: le0_def)
      have jge: "?j0 \<le> j" using jgt by linarith
      have liftj0: "le0 ?Mn (?j0 + q * ?w + (j - ?j0)) (?j0 + q * ?w + (?base - ?j0))"
        using oper_d1pos_le0_block_lift_fwd[OF L notzero hp j0lt' qn _ _ jle0] jge basej1 pj0eq
        by simp
      have basesub: "?base - ?j0 = s" by simp
      have liftj: "le0 ?Mn (?j0 + q * ?w + (j - ?j0)) ?y" using liftj0 basesub by simp
      have pltj: "?p < ?j0 + q * ?w + (j - ?j0)" using pdecomp jgt jge by linarith
      have ev: "entry ?Mn 1 ?y \<le> entry ?Mn 1 (?j0 + q * ?w + (j - ?j0))"
        by (rule valleyMn[OF pltj liftj])
      have jmw: "j - ?j0 < ?w" using jb basej1 jge by linarith
      have ej: "entry ?Mn 1 (?j0 + q * ?w + (j - ?j0)) = entry N 1 (?j0 + (j - ?j0))"
        by (rule oper_d1pos_entry1[OF L notzero hp i1z j0lt qn jmw])
      have jval: "?j0 + (j - ?j0) = j" using jge by simp
      show "entry N 1 ?base \<le> entry N 1 j" using ev ey ej jval by simp
    qed
    have spLtN: "?j0 + sp < Lng N" using spw j0lt by linarith
    have spltbase: "?j0 + sp < ?base" using sps by simp
    have nr1N: "nextrel1 N (?j0 + sp) ?base"
      unfolding nextrel1_def using spLtN baseLtN spltbase e_lt le0spb vall by simp
    have "nextR N 1 (?j0 + sp) ?base" using nr1N by (simp add: nextR_def)
    hence "?j0 + sp = ?pb" using parRb by (rule nextR1_unique)
    thus False using pesc by simp
  qed
  \<comment> \<open>STEP 2: prefix p; build nextrel1 N p base and conclude by uniqueness\<close>
  have le0pj0Mn: "le0 ?Mn ?p (?j0 + q * ?w)"
  proof -
    have leRpy: "leR ?Mn 0 ?p ?y" using le0py by (simp add: leR_def)
    have pbs: "?p \<le> ?j0 + q * ?w" using plt by linarith
    have bsy: "?j0 + q * ?w \<le> ?y" by simp
    have "leR ?Mn 0 ?p (?j0 + q * ?w)" by (rule m_5_1_ancestor_tree_1[OF NnT leRpy pbs bsy])
    thus ?thesis by (simp add: leR_def)
  qed
  have le0pj0N: "le0 N ?p ?j0"
    by (rule oper_d1pos_le0_prefix_back[OF L notzero hp i1z j0lt qn plt le0pj0Mn])
  have le0pbase: "le0 N ?p ?base" by (rule le0_trans[OF le0pj0N le0j0base])
  have ep: "entry ?Mn 1 ?p = entry N 1 ?p"
    by (rule operB_gen_entry_prefix[OF L notzero hp]) (use plt i1z in simp)
  have e_p_lt: "entry N 1 ?p < entry N 1 ?base" using epy ey ep by simp
  have vallp: "\<forall>j. ?p < j \<and> le0 N j ?base \<longrightarrow> entry N 1 ?base \<le> entry N 1 j"
  proof (intro allI impI)
    fix j assume H: "?p < j \<and> le0 N j ?base"
    from H have jgt: "?p < j" and jle0: "le0 N j ?base" by auto
    have jb: "j \<le> ?base" using jle0 nextrel0_rtrancl_mono[of N j ?base] by (simp add: le0_def)
    show "entry N 1 ?base \<le> entry N 1 j"
    proof (cases "j < ?j0")
      case True
      have j0y: "?j0 \<le> ?y" by simp
      have liftj: "le0 ?Mn j ?y"
        by (rule oper_d1pos_le0_prefix_lift_fwd[OF L notzero hp i1z j0lt n1 True _ basej1
                    jle0 j0y yLt]) simp
      have ev: "entry ?Mn 1 ?y \<le> entry ?Mn 1 j" by (rule valleyMn[OF jgt liftj])
      have ej: "entry ?Mn 1 j = entry N 1 j"
        by (rule operB_gen_entry_prefix[OF L notzero hp]) (use True i1z in simp)
      show ?thesis using ev ey ej by simp
    next
      case False
      hence jge: "?j0 \<le> j" by simp
      have liftj0: "le0 ?Mn (?j0 + q * ?w + (j - ?j0)) (?j0 + q * ?w + (?base - ?j0))"
        using oper_d1pos_le0_block_lift_fwd[OF L notzero hp j0lt' qn _ _ jle0] jge basej1 pj0eq
        by simp
      have basesub: "?base - ?j0 = s" by simp
      have liftj: "le0 ?Mn (?j0 + q * ?w + (j - ?j0)) ?y" using liftj0 basesub by simp
      have pltj: "?p < ?j0 + q * ?w + (j - ?j0)" using plt by linarith
      have ev: "entry ?Mn 1 ?y \<le> entry ?Mn 1 (?j0 + q * ?w + (j - ?j0))"
        by (rule valleyMn[OF pltj liftj])
      have jmw: "j - ?j0 < ?w" using jb basej1 jge by linarith
      have ej: "entry ?Mn 1 (?j0 + q * ?w + (j - ?j0)) = entry N 1 (?j0 + (j - ?j0))"
        by (rule oper_d1pos_entry1[OF L notzero hp i1z j0lt qn jmw])
      have jval: "?j0 + (j - ?j0) = j" using jge by simp
      show ?thesis using ev ey ej jval by simp
    qed
  qed
  have pLngN: "?p < Lng N" using plt j0lt L by linarith
  have pltbase: "?p < ?base" using plt by linarith
  have nr1pN: "nextrel1 N ?p ?base"
    unfolding nextrel1_def using pLngN baseLtN pltbase e_p_lt le0pbase vallp by simp
  have "nextR N 1 ?p ?base" using nr1pN by (simp add: nextR_def)
  hence "?p = ?pb" using parRb by (rule nextR1_unique)
  thus ?thesis .
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

text \<open>§6.7 operCA ESCAPE row-1 \<open>+1\<close> (d1pos, interior offset, prefix-escaping base
  parent): the gate-free counterpart of @{thm [source] operCA_interior_row1}.  The
  N[n]-parent is the escaped prefix column verbatim
  (@{thm [source] oper_d1pos_parent1_readback_escape}); row-1 entries transfer by
  prefix agreement and periodicity, closing via
  @{thm [source] operCA_tiling_within1_via_reflect}.\<close>

lemma operCA_escape_row1:
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
    and hpy: "hasParent ((N::pairseq)[n]) 1
                (parent N 1 (Lng N - 1) + q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s)"
    and hpMs: "hasParent N 1 (parent N 1 (Lng N - 1) + s)"
    and pesc: "parent N 1 (parent N 1 (Lng N - 1) + s) < parent N 1 (Lng N - 1)"
  shows "entry ((N::pairseq)[n]) 1
            (parent ((N::pairseq)[n]) 1
               (parent N 1 (Lng N - 1) + q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s)) + 1
       = entry ((N::pairseq)[n]) 1
            (parent N 1 (Lng N - 1) + q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s)"
proof -
  let ?j1 = "Lng N - 1"  let ?j0 = "parent N 1 ?j1"  let ?w = "?j1 - ?j0"
  let ?Mn = "(N::pairseq)[n]"  let ?x = "?j0 + q * ?w + s"  let ?pb = "parent N 1 (?j0 + s)"
  have pread: "parent ?Mn 1 ?x = ?pb"
    by (rule oper_d1pos_parent1_readback_escape[OF L notzero hp i1z j0lt qn spos sw hpy hpMs pesc])
  have ex: "entry ?Mn 1 ?x = entry N 1 (?j0 + s)"
    by (rule oper_d1pos_entry1[OF L notzero hp i1z j0lt qn sw])
  have eppre: "entry ?Mn 1 ?pb = entry N 1 ?pb"
    by (rule operB_gen_entry_prefix[OF L notzero hp]) (use pesc i1z in simp)
  have ep: "entry ?Mn 1 (parent ?Mn 1 ?x) = entry N 1 (parent N 1 (?j0 + s))"
    using pread eppre by simp
  show ?thesis by (rule operCA_tiling_within1_via_reflect[OF condA hpMs ex ep])
qed

text \<open>§6.7 operCA, idx1 = 1 (d1pos) branch, GATE-FREE: RedCondA (N[n]) from
  RedCondA N alone (no cGTWF, no ST_PS) -- the article-faithful form of the
  d1pos tiling step in the one-line proof of 標準形の簡約性 (reducedness is
  preserved by the fundamental sequence).  Mirrors operCA_d0zero (below):
  row 0 is @{thm [source] operCA_tiling_row0}; a row-1 column x >= j0 decomposes
  as j0+q*w+s and splits into block start (s = 0,
  @{thm [source] operCA_block_start_row1}), interior with in-block base parent
  (@{thm [source] operCA_interior_row1}) and interior with prefix-escaping base
  parent (@{thm [source] operCA_escape_row1}); existence of the base parents by
  @{thm [source] oper_blockstart_hasParent_j0} /
  @{thm [source] oper_interior_hasParent_base}.\<close>

lemma operCA_d1pos:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and condA: "RedCondA N"
    and n1: "1 \<le> n"
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
    fix x
    assume ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> x"
      and hpx: "hasParent ((N::pairseq)[n]) 1 x"
    let ?j1 = "Lng N - 1"  let ?j0 = "parent N 1 ?j1"  let ?w = "?j1 - ?j0"
    let ?Mn = "(N::pairseq)[n]"
    have gex: "?j0 \<le> x" using ge i1z by simp
    have w0: "0 < ?w" using j0lt by linarith
    have lenMn: "Lng ?Mn = ?j0 + n * ?w"
      using oper_d1pos_LngM[OF L notzero hp i1z j0lt] by simp
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
      also have "\<dots> = x" using gex by simp
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
    show "entry ?Mn 1 (parent ?Mn 1 x) + 1 = entry ?Mn 1 x"
    proof (cases "s = 0")
      case True
      have xbs: "x = ?j0 + q * ?w" using xdecomp True by simp
      have hpy: "hasParent ?Mn 1 (?j0 + q * ?w)" using hpx xbs by simp
      have hpMj0: "hasParent N 1 ?j0"
        by (rule oper_blockstart_hasParent_j0[OF L notzero hp i1z j0lt qn hpy])
      have parRj0: "nextR N 1 (parent N 1 ?j0) ?j0"
        using hpMj0 unfolding hasParent_def parent_def by (rule theI')
      have pjlt: "parent N 1 ?j0 < ?j0" using parRj0 by (simp add: nextR_def nextrel1_def)
      have "entry ?Mn 1 (parent ?Mn 1 (?j0 + q * ?w)) + 1 = entry ?Mn 1 (?j0 + q * ?w)"
        by (rule operCA_block_start_row1[OF L notzero hp i1z j0lt qn hpMj0 pjlt condA])
      thus ?thesis using xbs by simp
    next
      case False
      hence spos: "0 < s" by simp
      have hpy: "hasParent ?Mn 1 (?j0 + q * ?w + s)" using hpx xdecomp by simp
      have hpMs: "hasParent N 1 (?j0 + s)"
        by (rule oper_interior_hasParent_base[OF L notzero hp i1z j0lt qn spos sw hpy])
      show ?thesis
      proof (cases "parent N 1 (?j0 + s) < ?j0")
        case True
        have "entry ?Mn 1 (parent ?Mn 1 (?j0 + q * ?w + s)) + 1
                = entry ?Mn 1 (?j0 + q * ?w + s)"
          by (rule operCA_escape_row1[OF L notzero hp i1z j0lt condA qn spos sw hpy hpMs True])
        thus ?thesis using xdecomp by simp
      next
        case False
        hence pMge: "parent N 1 (?j0 + s) \<ge> ?j0" by simp
        have "entry ?Mn 1 (parent ?Mn 1 (?j0 + q * ?w + s)) + 1
                = entry ?Mn 1 (?j0 + q * ?w + s)"
          by (rule operCA_interior_row1[OF L notzero hp i1z j0lt condA qn spos sw hpMs pMge])
        thus ?thesis using xdecomp by simp
      qed
    qed
  qed
qed

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


text \<open>§6.7 operCA, FULL (both i1): RedCondA (N[n]) for a tiling step, GATE-FREE --
  from RedCondA N alone (the Nst/condB assumptions are kept only for interface
  compatibility with @{thm [source] m_6_7_standard_reduced}).  i1 = 1 (d1pos) is
  discharged by @{thm [source] operCA_d1pos} (block start / in-block parent /
  prefix-escaping parent, no cGTWF); i1 = 0 (d0zero) by
  @{thm [source] operCA_d0zero}.  This matches the article's one-line proof of
  標準形の簡約性: reducedness is preserved by the fundamental sequence, with no
  ST_PS-specific invariant.\<close>

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
    show ?thesis by (rule operCA_d1pos[OF L notzero hp i1z j0lt condA n1])
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

end
