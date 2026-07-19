theory Support_6_013
  imports Frontier_6_030
begin

text \<open>§6.8 d0pos confinement — REFORMULATED (status: the naive d0zero-style block
  confinement is FALSE here).

  In the \<open>i\<^sub>1 = 0\<close> (d0zero) layout every block-start carries the row-0 minimum
  \<open>M\<^bsub>0,j\<^sub>0\<^esub>\<close>, which acts as a barrier, so a row-0 chain from \<open>a \<ge> j\<^sub>0\<close> stays inside
  \<open>a\<close>'s block (@{thm [source] oper_d0zero_le0_confined}).

  In the \<open>i\<^sub>1 = 1\<close> (d0pos) layout, block \<open>k\<close>'s row-0 floor is
  \<open>M\<^bsub>0,j\<^sub>0\<^esub> + k\<cdot>\<delta>\<close> with \<open>\<delta> = M\<^bsub>0,Lng M-1\<^esub> - M\<^bsub>0,j\<^sub>0\<^esub> > 0\<close> (\<open>\<delta>>0\<close> always, since
  \<open>j\<^sub>0 = parent M 1 (Lng M-1)\<close> and \<open>nextR M 1 j\<^sub>0 (Lng M-1)\<close> entails \<open>le0\<close>, hence a
  strict row-0 increase across the slice).  Because the per-block floor strictly
  INCREASES with \<open>k\<close>, a \<open>nextrel0\<close> chain is no longer barred at block boundaries:
  it can climb into arbitrarily later blocks.  Concretely \<open>M = (0,0)(1,1)\<close> gives
  \<open>M[n] = (0,0)(1,0)\<dots>(n-1,0)\<close> (\<open>j\<^sub>0=0\<close>, \<open>w=1\<close>, \<open>\<delta>=1\<close>), whose row-0 is the strictly
  increasing chain \<open>0,1,\<dots>,n-1\<close>; the single \<open>nextrel0\<close> chain from \<open>a=0\<close> reaches
  \<open>b=n-1\<close>, crossing every block.  So the d0zero bound
  \<open>b < j\<^sub>0 + ((a-j\<^sub>0) div w + 1)\<cdot>w\<close> fails for every \<open>n>1\<close> (1260/2268 reachability
  pairs violate it in the standard-filtered KMAX=6 enumeration; the floor- and
  offset-based repairs fail too — the climb is genuinely unbounded by blocks).

  The strongest TRUE confinement that survives is the row-0-monotone one: a chain
  from \<open>a\<close> has \<open>a \<le> b < Lng (M[n])\<close> with \<open>M[n]\<^bsub>0,a\<^esub> \<le> M[n]\<^bsub>0,b\<^esub>\<close>.  The d0pos
  case-analysis (Z5–Z9) must therefore not assume single-block confinement; it
  works with this monotone bound (the slice \<open>seg (M[n]) a b\<close> may span several
  blocks, each shifted by \<open>\<delta>\<close>).\<close>

lemma oper_d1pos_le0_confined:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and a0: "parent M 1 (Lng M - 1) \<le> a"
    and alt: "a < Lng ((M::pairseq)[n])"
    and ab: "(nextrel0 ((M::pairseq)[n]))\<^sup>*\<^sup>* a b"
  shows "a \<le> b \<and> entry ((M::pairseq)[n]) 0 a \<le> entry ((M::pairseq)[n]) 0 b
         \<and> (a < b \<longrightarrow> b < Lng ((M::pairseq)[n]))"
proof (intro conjI impI)
  show "a \<le> b" using ab by (rule nextrel0_rtrancl_mono)
  show "entry ((M::pairseq)[n]) 0 a \<le> entry ((M::pairseq)[n]) 0 b"
    using ab by (rule nextrel0_rtrancl_entry0_mono)
  assume ablt: "a < b"
  \<comment> \<open>a strict chain ends in a genuine \<open>nextrel0\<close> step, whose target is in range\<close>
  from ab ablt show "b < Lng ((M::pairseq)[n])"
  proof (induction rule: rtranclp_induct)
    case base thus ?case by simp
  next
    case (step y z)
    have "z < Lng ((M::pairseq)[n])" using step.hyps(2) by (simp add: nextrel0_def)
    thus ?case .
  qed
qed

end
