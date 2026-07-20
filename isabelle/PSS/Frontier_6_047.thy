theory Frontier_6_047
  imports Support_6_028
begin

(* ===== keystone foundation block from workflow kf-local ===== *)
text \<open>
  §6.4 (構造的基礎) — parent block-locality (L1).  Engine lemma: a row-0
  left-minimum \<open>a\<close> (\<open>\<forall> x < a. entry M 0 x \<ge> entry M 0 a\<close>) is never crossed
  backward by a single \<open>nextrel0\<close> edge: there is no \<open>nextrel0 M x y\<close> with
  \<open>x < a \<le> y\<close>.  This is a self-contained consequence of the left-minimum
  property alone (no block structure needed).  Empirically TRUE: 0 crossing
  edges over all left-minima of \<open>maxlen 4, maxe 4\<close> sequences.
\<close>

lemma nextrel0_leftmin_no_cross:
  assumes lmin: "\<forall>z < a. entry M 0 z \<ge> entry M 0 a"
    and xa: "x < a" and ay: "a \<le> y"
  shows "\<not> nextrel0 M x y"
proof
  assume nx: "nextrel0 M x y"
  hence xy: "x < y" and val: "entry M 0 x < entry M 0 y"
    and mid: "\<forall>z. x < z \<and> z < y \<longrightarrow> entry M 0 z \<ge> entry M 0 y"
    by (auto simp: nextrel0_def)
  show False
  proof (cases "a = y")
    case True
    \<comment> \<open>edge lands exactly at \<open>a\<close>: contradicts left-minimum at the source \<open>x < a\<close>\<close>
    have "entry M 0 x \<ge> entry M 0 a" using lmin xa by blast
    thus False using val True by simp
  next
    case False
    hence ay': "a < y" using ay by simp
    \<comment> \<open>\<open>a\<close> strictly between \<open>x\<close> and \<open>y\<close>: middle condition gives \<open>entry a \<ge> entry y\<close>\<close>
    have "entry M 0 a \<ge> entry M 0 y" using mid xa ay' by blast
    moreover have "entry M 0 x \<ge> entry M 0 a" using lmin xa by blast
    ultimately have "entry M 0 x \<ge> entry M 0 y" by simp
    thus False using val by simp
  qed
qed

text \<open>
  Chain version: a row-0 left-minimum \<open>a\<close> is never crossed backward by an
  \<open>le0\<close> (\<open>(nextrel0)\<^sup>*\<^sup>*\<close>) chain either: any \<open>le0\<close>-ancestor \<open>p\<close> of a node
  \<open>j \<ge> a\<close> satisfies \<open>p \<ge> a\<close>.  Proved by reverse induction on the chain using
  the single-edge no-cross lemma.
\<close>

lemma le0_leftmin_ancestor_ge:
  assumes lmin: "\<forall>z < a. entry M 0 z \<ge> entry M 0 a"
    and chain: "(nextrel0 M)\<^sup>*\<^sup>* p j" and aj: "a \<le> j"
  shows "a \<le> p"
  using chain
proof (induction rule: converse_rtranclp_induct)
  case base
  show ?case using aj by simp
next
  case (step p z)
  \<comment> \<open>\<open>nextrel0 M p z\<close>, \<open>(nextrel0)\<^sup>*\<^sup>* z j\<close>; IH gives \<open>a \<le> z\<close>\<close>
  have az: "a \<le> z" using step.IH .
  show "a \<le> p"
  proof (rule ccontr)
    assume "\<not> a \<le> p"
    hence pa: "p < a" by simp
    have "\<not> nextrel0 M p z"
      by (rule nextrel0_leftmin_no_cross[OF lmin pa az])
    thus False using step.hyps(1) by simp
  qed
qed

end
