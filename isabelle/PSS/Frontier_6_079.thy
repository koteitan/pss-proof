theory Frontier_6_079
  imports Support_6_058
begin

text \<open>§6.7 oper-tiling ROW-1 (Front A, \<open>i\<^sub>1=1\<close> valley helper): a confined N-chain
  \<open>j \<rightarrow>\<^sup>* x'\<close> with \<open>j\<^sub>0 \<le> j\<close>, \<open>x' < j\<^sub>1\<close> lifts to block \<open>q\<close> of \<open>N[n]\<close>.  We first
  upgrade the plain \<open>(nextrel0 N)\<^sup>*\<^sup>*\<close> chain to the RESTRICTED relation
  (\<open>nextrel0 N u v \<and> j\<^sub>0 \<le> u \<and> v < j\<^sub>1\<close>) — every node lies in \<open>[j, x'] \<subseteq> [j\<^sub>0, j\<^sub>1)\<close>
  by monotonicity — then apply @{thm [source] oper_gen_le0_within_forward}.\<close>

lemma oper_d1pos_le0_block_lift_fwd:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and qn: "q < n"
    and j0j: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> j"
    and xpj1: "xp < Lng N - 1"
    and reach: "le0 N j xp"
  shows "le0 ((N::pairseq)[n])
            (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
               + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
               + (j - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
            (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
               + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
               + (xp - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?R = "\<lambda>u v. nextrel0 N u v \<and> ?j0 \<le> u \<and> v < ?j1"
  have chain0: "(nextrel0 N)\<^sup>*\<^sup>* j xp" using reach by (simp add: le0_def)
  \<comment> \<open>upgrade to the restricted relation by CONVERSE (back-to-front) peeling: every
     node \<open>b\<close> on the suffix \<open>b \<rightarrow>\<^sup>* xp\<close> satisfies \<open>b \<le> xp < j\<^sub>1\<close>, and \<open>j\<^sub>0 \<le> b\<close> is
     carried as a side condition.\<close>
  have main: "\<And>b. (nextrel0 N)\<^sup>*\<^sup>* b xp \<Longrightarrow> ?j0 \<le> b \<Longrightarrow> ?R\<^sup>*\<^sup>* b xp"
  proof -
    fix b assume "(nextrel0 N)\<^sup>*\<^sup>* b xp"
    thus "?j0 \<le> b \<Longrightarrow> ?R\<^sup>*\<^sup>* b xp"
    proof (induction rule: converse_rtranclp_induct)
      case base show ?case by simp
    next
      case (step c y)
      have ncy: "nextrel0 N c y" by (rule step.hyps(1))
      have yxp: "y \<le> xp" using step.hyps(2) by (rule nextrel0_rtrancl_mono)
      have yj1: "y < ?j1" using yxp xpj1 by (rule le_less_trans)
      have rstep: "?R c y" using ncy step.prems yj1 by simp
      have tail: "?R\<^sup>*\<^sup>* y xp"
      proof -
        have cy: "c < y" using ncy by (simp add: nextrel0_def)
        have "?j0 \<le> y" using step.prems cy by linarith
        thus ?thesis by (rule step.IH)
      qed
      show ?case using rstep tail by (rule converse_rtranclp_into_rtranclp)
    qed
  qed
  have rchain: "?R\<^sup>*\<^sup>* j xp" by (rule main[OF chain0 j0j])
  have jxp': "j \<le> xp" using chain0 by (rule nextrel0_rtrancl_mono)
  have aj1: "j < ?j1" using jxp' xpj1 by (rule le_less_trans)
  show ?thesis
    by (rule oper_gen_le0_within_forward[OF L notzero hp j0lt qn j0j aj1 rchain])
qed


text \<open>§6.7 oper-tiling ROW-1 (Front A, \<open>i\<^sub>1=1\<close> PREFIX-competitor lift): a PREFIX
  node \<open>j < j\<^sub>0\<close> that is a row-0 ancestor of an active-slice column \<open>x' < j\<^sub>1\<close>
  (\<open>le0 N j x'\<close>) reaches ANY within-block column \<open>x = j\<^sub>0 + q\<cdot>w + s\<^sub>x\<close> of \<open>N[n]\<close>
  with \<open>x \<ge> j\<^sub>0\<close>, \<open>q < n\<close>.  Route: \<open>j\<^sub>0\<close> is on \<open>j\<close>'s ancestor path
  (@{thm [source] m_5_1_ancestor_tree_1}, endpoint restriction \<open>x' \<rightsquigarrow> j\<^sub>0\<close>),
  the prefix \<open>[0,j\<^sub>0]\<close> is row-0 verbatim in \<open>N[n]\<close>
  (@{thm [source] oper_d1pos_row0_agree} / @{thm [source] le0_prefix_row0}), giving
  \<open>le0 (N[n]) j j\<^sub>0\<close>, and \<open>j\<^sub>0 \<rightsquigarrow> x\<close> is @{thm [source] oper_d1pos_le0_start_to_any}.\<close>

lemma oper_d1pos_le0_prefix_lift_fwd:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and n1: "1 \<le> n"
    and jpre: "j < parent N 1 (Lng N - 1)"
    and xpge: "parent N 1 (Lng N - 1) \<le> xp"
    and xpj1: "xp < Lng N - 1"
    and reach: "le0 N j xp"
    and xge: "parent N 1 (Lng N - 1) \<le> x"
    and xlt: "x < Lng ((N::pairseq)[n])"
  shows "le0 ((N::pairseq)[n]) j x"
proof -
  let ?j1 = "Lng N - 1"  let ?j0 = "parent N 1 ?j1"
  have NT: "N \<in> T_PS" using L by (cases N) (auto simp: T_PS_def)
  have i1z': "idx1 N ?j1 = 1" using i1z .
  \<comment> \<open>(a) restrict the ancestor path \<open>j \<rightsquigarrow> x'\<close> down to \<open>j\<^sub>0\<close>\<close>
  have jx': "j \<le> xp" using reach nextrel0_rtrancl_mono[of N j xp] by (simp add: le0_def)
  have leRjxp: "leR N 0 j xp" using reach by (simp add: leR_def)
  have jj0: "j \<le> ?j0" using jpre by simp
  have j0xp: "?j0 \<le> xp" using xpge .
  have leRjj0: "leR N 0 j ?j0"
    by (rule m_5_1_ancestor_tree_1[OF NT leRjxp jj0 j0xp])
  have le0Njj0: "le0 N j ?j0" using leRjj0 by (simp add: leR_def)
  \<comment> \<open>(b) row-0 prefix transfer \<open>N \<rightarrow> N[n]\<close> on \<open>[0, j\<^sub>0]\<close>\<close>
  have j0ltNn: "?j0 < Lng ((N::pairseq)[n])"
  proof -
    have "?j0 \<le> x" using xge by simp
    thus ?thesis using xlt by (rule le_less_trans)
  qed
  have j0ltN: "?j0 < Lng N" using j0lt L by linarith
  have k0n0: "(0::nat) < n" using n1 by simp
  \<comment> \<open>row-0 agreement on \<open>[0, j\<^sub>0]\<close> directly: prefix verbatim below \<open>j\<^sub>0\<close>, and the
     block-0 start \<open>j\<^sub>0\<close> reads \<open>entry N 0 j\<^sub>0\<close> (\<open>q=0\<close>, shift \<open>0\<cdot>\<delta>=0\<close>).\<close>
  have agree: "\<And>z. z \<le> ?j0 \<Longrightarrow> entry N 0 z = entry ((N::pairseq)[n]) 0 z"
  proof -
    fix z assume zj0: "z \<le> ?j0"
    show "entry N 0 z = entry ((N::pairseq)[n]) 0 z"
    proof (cases "z < ?j0")
      case True
      have "((N::pairseq)[n]) ! z = N ! z"
        by (rule oper_d1pos_nth_prefix[OF L notzero hp i1z' True])
      thus ?thesis by (simp add: entry_def)
    next
      case False
      hence zeq: "z = ?j0" using zj0 by simp
      have w0: "0 < ?j1 - ?j0" using j0lt by simp
      have "((N::pairseq)[n]) ! (?j0 + 0 * (?j1 - ?j0) + 0)
              = (entry N 0 (?j0 + 0) + 0 * (entry N 0 ?j1 - entry N 0 ?j0),
                 entry N 1 (?j0 + 0))"
        by (rule oper_d1pos_nth[OF L notzero hp i1z' j0lt k0n0 w0])
      hence "((N::pairseq)[n]) ! ?j0 = (entry N 0 ?j0, entry N 1 ?j0)" by simp
      thus ?thesis using zeq by (simp add: entry_def)
    qed
  qed
  have le0Nnjj0: "le0 ((N::pairseq)[n]) j ?j0"
    by (rule le0_prefix_row0[OF agree j0ltN j0ltNn jj0 order.refl le0Njj0])
  \<comment> \<open>(c) start-block reach \<open>j\<^sub>0 \<rightsquigarrow> x\<close>\<close>
  have k0n: "(0::nat) < n" using n1 by simp
  have xge0: "?j0 + 0 * (?j1 - ?j0) \<le> x" using xge by simp
  have le0Nnj0x: "le0 ((N::pairseq)[n]) (?j0 + 0 * (?j1 - ?j0)) x"
    by (rule oper_d1pos_le0_start_to_any[OF NT L notzero hp i1z' j0lt k0n xge0 xlt])
  have le0Nnj0x': "le0 ((N::pairseq)[n]) ?j0 x" using le0Nnj0x by simp
  show ?thesis by (rule le0_trans[OF le0Nnjj0 le0Nnj0x'])
qed

end
