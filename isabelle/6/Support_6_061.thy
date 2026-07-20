theory Support_6_061
  imports Frontier_6_081
begin

text \<open>6.7 Qprime CORE -- the genuinely-new framing (attempt R).

  Empirically (red_model, 192/0 on standard N; 41 indirect instances all
  closing): the pure-N fact @{text Qprime}
    \<open>j\<^sub>0 < z < j\<^sub>1 \<Longrightarrow> hasParent N 1 z \<Longrightarrow> parent N 1 z \<ge> j\<^sub>0
        \<Longrightarrow> entry N 1 j\<^sub>0 < entry N 1 z\<close>
  (\<open>j\<^sub>0 = parent N 1 j\<^sub>1\<close>, \<open>j\<^sub>1 = Lng N - 1\<close>) is NOT a tiling/oper fact: it follows
  by a PURE STRONG INDUCTION ON @{text z} inside a fixed @{text N}, with NO
  @{text ST_PS.induct}, NO periodicity, NO oper step.

  The recursion: let \<open>p = parent N 1 z\<close>.  The row-1 parent edge \<open>nextR N 1 p z\<close>
  gives the base inequality \<open>entry N 1 p < entry N 1 z\<close> directly (def. of
  @{const nextrel1}).
    \<^item> if \<open>p = j\<^sub>0\<close>: \<open>entry N 1 j\<^sub>0 < entry N 1 z\<close> immediately.
    \<^item> if \<open>p > j\<^sub>0\<close>: \<open>p\<close> is a SMALLER @{text Qprime} instance (\<open>j\<^sub>0 < p < z < j\<^sub>1\<close>,
      @{text "hasParent N 1 p"}, \<open>parent N 1 p \<ge> j\<^sub>0\<close>), so the IH gives
      \<open>entry N 1 j\<^sub>0 < entry N 1 p\<close>; chain with the base edge.

  Empirically verified load-bearing facts for the \<open>p > j\<^sub>0\<close> branch (41/41 on
  standard N, fA=fB=fC=0):
    (A) @{text "hasParent N 1 p"}   (B) \<open>parent N 1 p \<ge> j\<^sub>0\<close>   (C) \<open>p < z\<close>.
  (C) is structural (parent precedes child).  (A),(B) are the standardness
  carrier and are the ONLY residual: they say the row-1 ancestor tree above
  \<open>j\<^sub>0\<close> is well-formed (every row-1 reachable interior point of \<open>(j\<^sub>0,j\<^sub>1)\<close> has a
  row-1 parent, itself \<open>\<ge> j\<^sub>0\<close>).  This lemma proves @{text Qprime} GREEN,
  taking exactly (A),(B) as the named hypothesis @{text tree}.  The induction
  skeleton is unconditional; the residual is isolated to @{text tree}.

  Non-circular: uses only @{const nextrel1} / @{const parent} / @{const nextR}
  and the strong induction.  No spsy, sblk, via_spsy, RedCond, oper, diag.\<close>

lemma Qprime_via_tree:
  fixes N :: pairseq
  defines "j1 \<equiv> Lng N - 1"  and "j0 \<equiv> parent N 1 (Lng N - 1)"
  assumes tree: "\<And>z. j0 < z \<Longrightarrow> z < j1 \<Longrightarrow> hasParent N 1 z
                    \<Longrightarrow> parent N 1 z \<ge> j0 \<Longrightarrow> parent N 1 z > j0
                    \<Longrightarrow> hasParent N 1 (parent N 1 z)
                        \<and> parent N 1 (parent N 1 z) \<ge> j0"
    and zlo: "j0 < z"  and zhi: "z < j1"
    and hpz: "hasParent N 1 z"  and pge: "parent N 1 z \<ge> j0"
  shows "entry N 1 j0 < entry N 1 z"
proof -
  \<comment> \<open>strong induction on the endpoint \<open>z\<close>; the four side-conditions travel along\<close>
  have main: "\<And>z. j0 < z \<Longrightarrow> z < j1 \<Longrightarrow> hasParent N 1 z \<Longrightarrow> parent N 1 z \<ge> j0
                  \<Longrightarrow> entry N 1 j0 < entry N 1 z"
  proof -
    fix z0 :: nat
    show "j0 < z0 \<Longrightarrow> z0 < j1 \<Longrightarrow> hasParent N 1 z0 \<Longrightarrow> parent N 1 z0 \<ge> j0
              \<Longrightarrow> entry N 1 j0 < entry N 1 z0"
    proof (induction z0 rule: less_induct)
      case (less z0)
      let ?p = "parent N 1 z0"
      \<comment> \<open>the row-1 parent edge of \<open>z0\<close>\<close>
      have parR: "nextR N 1 ?p z0"
        using less.prems(3) unfolding hasParent_def parent_def by (rule theI')
      have nr1: "nextrel1 N ?p z0" using parR by (simp add: nextR_def)
      have baseedge: "entry N 1 ?p < entry N 1 z0"
        using nr1 by (simp add: nextrel1_def)
      have plt: "?p < z0" using nr1 by (simp add: nextrel1_def)
      show ?case
      proof (cases "?p = j0")
        case True
        show ?thesis using baseedge True by simp
      next
        case False
        have pgt: "?p > j0" using less.prems(4) False by linarith
        \<comment> \<open>(A),(B): the residual tree facts give \<open>p\<close> a valid row-1 parent \<open>\<ge> j\<^sub>0\<close>\<close>
        have AB: "hasParent N 1 ?p \<and> parent N 1 ?p \<ge> j0"
          using tree[OF less.prems(1) less.prems(2) less.prems(3) less.prems(4) pgt] .
        have hpp: "hasParent N 1 ?p" using AB by simp
        have ppge: "parent N 1 ?p \<ge> j0" using AB by simp
        \<comment> \<open>\<open>p\<close> is a strictly smaller @{text Qprime} instance: \<open>j\<^sub>0 < p < z0 < j\<^sub>1\<close>\<close>
        have pj1: "?p < j1" using plt less.prems(2) by linarith
        have IH: "entry N 1 j0 < entry N 1 ?p"
          using less.IH[OF plt pgt pj1 hpp ppge] .
        show ?thesis using IH baseedge by simp
      qed
    qed
  qed
  show ?thesis using main[OF zlo zhi hpz pge] .
qed


text \<open>6.7 ASSEMBLY (attempt T) -- the spsy mod-inequality for one standard \<open>N\<close>,
  taking exactly the two residuals \<open>tree\<close> (RESIDUAL 1) and \<open>bridge\<close> (RESIDUAL 2)
  as named hypotheses.  This is the composition node: it shows that closing both
  residuals (GREEN, for \<open>N \<in> ST_PS\<close>) discharges the per-\<open>N\<close> instance of the
  \<open>spsy\<close> premise of @{thm [source] m_6_7_standard_reduced_via_spsy_valley} /
  @{thm [source] m_6_5_ST_PS_imp_RedCondA_via_spsy_valley}, hence (with the FREE
  \<open>valley\<close>) makes the whole cascade unconditional.

  Route (no circular citation: cites only @{thm [source] spsy_keystone_via_Q},
  @{thm [source] Qprime_via_tree}, and the two residual hypotheses):
    \<^item> \<open>w = 1\<close>: the LEFT @{text Q}-disjunct is immediate.
    \<^item> \<open>w > 1\<close>: set \<open>s\<^sub>y = (y-j\<^sub>0) mod w\<close>.  Here \<open>s\<^sub>y > 0\<close> is FORCED: the keystone
      @{thm [source] spsy_keystone_via_Q} only ever uses the RIGHT @{text Q}
      disjunct \<^emph>\<open>strictly\<close> (it derives \<open>entry N 1 j\<^sub>0 < entry N 1 (j\<^sub>0+s\<^sub>y)\<close> from
      \<open>Q \<and> w>1\<close>), so a true \<open>Q\<close> under \<open>w>1\<close> requires \<open>s\<^sub>y > 0\<close> -- equivalently, the
      arising \<open>y\<close> (which has a row-1 parent in \<open>N[n]\<close>) is never a period start.
      That non-degeneracy \<open>s\<^sub>y > 0\<close> is supplied here as the named premise
      @{text sy_pos} (empirically 0 counterexamples on genuine \<open>ST_PS\<close>:
      \<open>sy=0 \<and> w>1\<close> never co-occurs with \<open>hasParent (N[n]) 1 y\<close> and \<open>p \<ge> j\<^sub>0\<close>,
      /tmp/_sy0.py 0/402).  With \<open>s\<^sub>y > 0\<close>, \<open>bridge\<close> gives
      \<open>hasParent N 1 (j\<^sub>0+s\<^sub>y)\<close> and \<open>parent N 1 (j\<^sub>0+s\<^sub>y) \<ge> j\<^sub>0\<close>; then
      @{thm [source] Qprime_via_tree} at \<open>z = j\<^sub>0+s\<^sub>y\<close> (its \<open>tree\<close> premise is
      RESIDUAL 1) yields \<open>entry N 1 j\<^sub>0 < entry N 1 (j\<^sub>0+s\<^sub>y)\<close>, the RIGHT
      @{text Q}-disjunct.
  Then @{thm [source] spsy_keystone_via_Q} consumes \<open>Q\<close>.\<close>

lemma spsy_keystone_via_tree_bridge:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y"
    and hpny: "hasParent ((N::pairseq)[n]) 1 y"
    and pge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> parent ((N::pairseq)[n]) 1 y"
    \<comment> \<open>non-degeneracy of the arising \<open>y\<close> when \<open>w > 1\<close> (forced; see header)\<close>
    and sy_pos: "1 < Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                 \<Longrightarrow> (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                       mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)) > 0"
    \<comment> \<open>RESIDUAL 1 (tree), specialised to this \<open>N\<close> with \<open>j\<^sub>0 = parent N 1 (Lng N-1)\<close>,
       \<open>j\<^sub>1 = Lng N - 1\<close>\<close>
    and tree: "\<And>z. parent N 1 (Lng N - 1) < z \<Longrightarrow> z < Lng N - 1
                  \<Longrightarrow> hasParent N 1 z
                  \<Longrightarrow> parent N 1 z \<ge> parent N 1 (Lng N - 1)
                  \<Longrightarrow> parent N 1 z > parent N 1 (Lng N - 1)
                  \<Longrightarrow> hasParent N 1 (parent N 1 z)
                      \<and> parent N 1 (parent N 1 z) \<ge> parent N 1 (Lng N - 1)"
    \<comment> \<open>RESIDUAL 2 (bridge), specialised to this \<open>N,n,y\<close>; only the \<open>s\<^sub>y > 0\<close>
       instance is needed\<close>
    and bridge: "(y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                      mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)) > 0
                 \<Longrightarrow> hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                        + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                           mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                     \<and> parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                        + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                           mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                       \<ge> parent N (idx1 N (Lng N - 1)) (Lng N - 1)"
  shows "(parent ((N::pairseq)[n]) 1 y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
            mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
        \<le> (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
            mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?sy = "(y - ?j0) mod ?w"
  have j0eq1: "?j0 = parent N 1 ?j1" using i1z by simp
  \<comment> \<open>the @{text Q}-disjunction\<close>
  have Q: "?w = 1 \<or> entry N 1 ?j0 < entry N 1 (?j0 + ?sy)"
  proof (cases "?w = 1")
    case True thus ?thesis by simp
  next
    case False
    hence w1: "1 < ?w" using j0lt by linarith
    have sy0: "?sy > 0" using sy_pos w1 by simp
    have sygt: "0 < ?sy" using sy0 by simp
    have hpzpge: "hasParent N 1 (?j0 + ?sy) \<and> parent N 1 (?j0 + ?sy) \<ge> ?j0"
      using bridge sygt by blast
    have hpz: "hasParent N 1 (?j0 + ?sy)" using hpzpge by simp
    have pgez: "parent N 1 (?j0 + ?sy) \<ge> ?j0" using hpzpge by simp
    have zlo: "?j0 < ?j0 + ?sy" using sygt by simp
    have syw: "?sy < ?w" using w1 by simp
    have j0w1: "?j0 + ?w = ?j1" using j0lt by simp
    have zhi: "?j0 + ?sy < ?j1" using syw j0w1 by linarith
    \<comment> \<open>specialise the keystone's \<open>j\<^sub>0,j\<^sub>1\<close> to the \<open>parent N 1 (Lng N-1)\<close> form\<close>
    have zlo': "parent N 1 ?j1 < ?j0 + ?sy" using zlo j0eq1 by simp
    have zhi': "?j0 + ?sy < Lng N - 1" using zhi by simp
    have pgez': "parent N 1 (?j0 + ?sy) \<ge> parent N 1 ?j1" using pgez j0eq1 by simp
    have strict: "entry N 1 (parent N 1 ?j1) < entry N 1 (?j0 + ?sy)"
      by (rule Qprime_via_tree[OF tree zlo' zhi' hpz pgez'])
    have "entry N 1 ?j0 < entry N 1 (?j0 + ?sy)" using strict j0eq1 by simp
    thus ?thesis by blast
  qed
  show ?thesis
    by (rule spsy_keystone_via_Q[OF L notzero hp i1z j0lt ge hpny pge Q])
qed


text \<open>§6.7 RESIDUAL 1 (tree), reduced to ONE crisp row-0 brick.  Given the spsy
  domain facts and an interior node \<open>z\<close> (\<open>j\<^sub>0 < z < j\<^sub>1\<close>) with row-1 parent
  \<open>p = parent N 1 z > j\<^sub>0\<close>, the well-formedness \<open>hasParent N 1 p \<and> parent N 1 p \<ge> j\<^sub>0\<close>
  follows from the §5.1 ancestor-tree machinery alone PROVIDED the single row-0
  reachability brick \<open>le0 N p j\<^sub>1\<close> (\<open>p\<close> reaches \<open>j\<^sub>1\<close> in row 0).  Route:
    \<^item> \<open>m_5_1_ancestor_basic_2\<close> at \<open>(j\<^sub>0, p, j\<^sub>1)\<close> (using \<open>leR N 1 j\<^sub>0 j\<^sub>1\<close> from the root
      edge \<open>nextrel1 N j\<^sub>0 j\<^sub>1\<close>, and \<open>leR N 0 p j\<^sub>1\<close> = the brick) gives
      \<open>entry N 1 j\<^sub>0 < entry N 1 p\<close>, NON-circularly (NOT via \<open>Qprime_via_tree\<close>);
    \<^item> \<open>m_5_1_ancestor_tree_1\<close> at \<open>(j\<^sub>0, p, z)\<close> (\<open>leR N 0 j\<^sub>0 z\<close>, \<open>j\<^sub>0 \<le> p \<le> z\<close>) gives
      \<open>leR N 0 j\<^sub>0 p\<close>;
    \<^item> \<open>m_5_1_parent_exists_2\<close> at \<open>(j\<^sub>0, p)\<close> then yields a row-1 parent of \<open>p\<close> in
      \<open>[j\<^sub>0, p)\<close>, i.e. \<open>hasParent N 1 p\<close> and \<open>parent N 1 p \<ge> j\<^sub>0\<close>.
  Empirically the brick holds 0-fail on genuine ST_PS (/tmp/_reach2.py: \<open>le0 N p j\<^sub>1\<close>
  402/0); so does the conclusion (/tmp/_tree_oper.py 402/0).  Cites only §5.1
  lemmas + le0 transitivity; no RedCond, no spsy, no via_spsy, no
  \<open>Qprime_via_tree\<close>.\<close>

lemma m_6_7_tree_wellformed:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and hp1: "hasParent N 1 (Lng N - 1)"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and zlo: "parent N 1 (Lng N - 1) < z"
    and zhi: "z < Lng N - 1"
    and hpz: "hasParent N 1 z"
    and pge: "parent N 1 z \<ge> parent N 1 (Lng N - 1)"
    and pgt: "parent N 1 z > parent N 1 (Lng N - 1)"
    \<comment> \<open>RESIDUAL BRICK (row-0 reach): \<open>p = parent N 1 z\<close> reaches \<open>j\<^sub>1\<close> in row 0.
       Empirically 0-fail on ST_PS (/tmp/_reach2.py 402/0).\<close>
    and reach: "le0 N (parent N 1 z) (Lng N - 1)"
  shows "hasParent N 1 (parent N 1 z)
         \<and> parent N 1 (parent N 1 z) \<ge> parent N 1 (Lng N - 1)"
proof -
  let ?j1 = "Lng N - 1"  let ?j0 = "parent N 1 ?j1"  let ?p = "parent N 1 z"
  have NT: "N \<in> T_PS" using L by (cases N) (auto simp: T_PS_def)
  have zL: "z < Lng N" using zhi by linarith
  have j1L: "?j1 < Lng N" using L by linarith
  \<comment> \<open>the root edge \<open>nextrel1 N j\<^sub>0 j\<^sub>1\<close> (\<open>j\<^sub>0\<close> is the row-1 parent of \<open>j\<^sub>1\<close>)\<close>
  have parRj1: "nextR N 1 ?j0 ?j1"
    using hp1 unfolding hasParent_def parent_def by (rule theI')
  have nr1j: "nextrel1 N ?j0 ?j1" using parRj1 by (simp add: nextR_def)
  have le0j0j1: "le0 N ?j0 ?j1" using nr1j by (simp add: nextrel1_def)
  have leR1j0j1: "leR N 1 ?j0 ?j1"
    using nr1j unfolding leR_def le1_def
    by (auto simp: nextrel1_def r_into_rtranclp)
  \<comment> \<open>the parent edge \<open>nextrel1 N p z\<close>\<close>
  have parRz: "nextR N 1 ?p z"
    using hpz unfolding hasParent_def parent_def by (rule theI')
  have nr1z: "nextrel1 N ?p z" using parRz by (simp add: nextR_def)
  have le0pz: "le0 N ?p z" using nr1z by (simp add: nextrel1_def)
  have plt: "?p < z" using nr1z by (simp add: nextrel1_def)
  have pgtj0: "?j0 < ?p" using pgt .
  have pltj1: "?p < ?j1" using plt zhi by linarith
  have pL: "?p < Lng N" using pltj1 j1L by linarith
  \<comment> \<open>\<open>leR N 0 j\<^sub>0 z\<close> by \<open>m_5_1_ancestor_tree_1\<close> (\<open>j\<^sub>0 \<le> z \<le> j\<^sub>1\<close>), then \<open>leR N 0 j\<^sub>0 p\<close>\<close>
  have leR0j0j1: "leR N 0 ?j0 ?j1" using le0j0j1 by (simp add: leR_def)
  have leR0j0z: "leR N 0 ?j0 z"
  proof (rule m_5_1_ancestor_tree_1[OF NT leR0j0j1])
    show "?j0 \<le> z" using zlo by linarith
    show "z \<le> ?j1" using zhi by linarith
  qed
  have leR0j0p: "leR N 0 ?j0 ?p"
  proof (rule m_5_1_ancestor_tree_1[OF NT leR0j0z])
    show "?j0 \<le> ?p" using pgtj0 by linarith
    show "?p \<le> z" using plt by linarith
  qed
  \<comment> \<open>\<open>leR N 0 p j\<^sub>1\<close> from the brick\<close>
  have leR0pj1: "leR N 0 ?p ?j1" using reach by (simp add: leR_def)
  \<comment> \<open>\<open>entry N 1 j\<^sub>0 < entry N 1 p\<close> NON-circularly via \<open>m_5_1_ancestor_basic_2\<close>\<close>
  have e1lt: "entry N 1 ?j0 < entry N 1 ?p"
    by (rule m_5_1_ancestor_basic_2[OF NT pgtj0 _ leR1j0j1 leR0pj1])
       (use pltj1 in linarith)
  \<comment> \<open>\<open>m_5_1_parent_exists_2\<close> yields a row-1 parent of \<open>p\<close> in \<open>[j\<^sub>0, p)\<close>\<close>
  obtain j' where j'ge: "?j0 \<le> j'" and j'lt: "j' < ?p" and j'par: "nextR N 1 j' ?p"
    using m_5_1_parent_exists_2[OF NT pgtj0 pL e1lt leR0j0p] by blast
  have hpp: "hasParent N 1 ?p"
    unfolding hasParent_def
  proof (rule ex_ex1I)
    show "\<exists>a. nextR N 1 a ?p" using j'par by blast
  next
    fix a b assume "nextR N 1 a ?p" "nextR N 1 b ?p"
    thus "a = b" using nextR1_unique by blast
  qed
  have parp_eq: "parent N 1 ?p = j'"
  proof -
    have "(THE a. nextR N 1 a ?p) = j'"
    proof (rule the1_equality)
      show "\<exists>!a. nextR N 1 a ?p" using hpp unfolding hasParent_def .
      show "nextR N 1 j' ?p" using j'par .
    qed
    thus ?thesis unfolding parent_def .
  qed
  have ppge: "parent N 1 ?p \<ge> ?j0" using parp_eq j'ge by simp
  show ?thesis using hpp ppge by blast
qed


text \<open>§6.7 BRICK reduction (attempt C) -- the row-0 reach \<open>le0 N q j\<^sub>1\<close> for an
  interior tail node \<open>q\<close> (\<open>j\<^sub>0 < q < j\<^sub>1\<close>, \<open>j\<^sub>0 = parent N 1 j\<^sub>1\<close>, \<open>j\<^sub>1 = Lng N-1\<close>)
  follows UNCONDITIONALLY from the single tail invariant \<open>tail_affine\<close>: that the
  row-0 reading on the tail \<open>[j\<^sub>0, j\<^sub>1]\<close> is the affine ramp
  \<open>entry N 0 x = entry N 0 j\<^sub>0 + (x - j\<^sub>0)\<close>.  Indeed the ramp makes \<open>entry N 0\<close>
  strictly increasing on \<open>(q, j\<^sub>1]\<close>, so @{thm [source] le0_build} chains
  \<open>q \<rightarrow>\<^sup>* j\<^sub>1\<close> in row 0.  EMPIRICALLY the ramp holds 142/0 and \<open>le0 N q j\<^sub>1\<close>
  231/0 on genuine ST_PS (\<open>is_standard\<close> diag+oper closure), and BOTH are FALSE on
  general T_PS, so \<open>tail_affine\<close> is the genuine ST_PS carrier of the brick.
  Cites only @{thm [source] le0_build}; no spsy / sblk / via_spsy / RedCond / oper.\<close>

lemma brick_from_tail_affine:
  fixes N :: pairseq
  assumes NT: "N \<in> T_PS"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and qlo: "parent N 1 (Lng N - 1) < q"
    and qhi: "q < Lng N - 1"
    and affine: "\<And>x. parent N 1 (Lng N - 1) \<le> x \<Longrightarrow> x \<le> Lng N - 1
                   \<Longrightarrow> entry N 0 x = entry N 0 (parent N 1 (Lng N - 1)) + (x - parent N 1 (Lng N - 1))"
  shows "le0 N q (Lng N - 1)"
proof -
  let ?j1 = "Lng N - 1"  let ?j0 = "parent N 1 ?j1"
  have qj1: "q < ?j1" using qhi .
  have j1L: "?j1 < Lng N" using j0lt by linarith
  have qL: "q < Lng N" using qj1 j1L by linarith
  have qge: "?j0 \<le> q" using qlo by linarith
  \<comment> \<open>strict row-0 increase on \<open>(q, j\<^sub>1]\<close> from the affine ramp\<close>
  have strict: "\<And>j. q < j \<Longrightarrow> j \<le> ?j1 \<Longrightarrow> entry N 0 q < entry N 0 j"
  proof -
    fix j assume jq: "q < j" and jj1: "j \<le> ?j1"
    have qx: "?j0 \<le> q" using qge .
    have qle: "q \<le> ?j1" using qj1 by linarith
    have eq_q: "entry N 0 q = entry N 0 ?j0 + (q - ?j0)" by (rule affine[OF qx qle])
    have jx: "?j0 \<le> j" using qx jq by linarith
    have eq_j: "entry N 0 j = entry N 0 ?j0 + (j - ?j0)" by (rule affine[OF jx jj1])
    have "q - ?j0 < j - ?j0" using jq qx by linarith
    thus "entry N 0 q < entry N 0 j" using eq_q eq_j by linarith
  qed
  \<comment> \<open>build the row-0 chain \<open>q \<rightarrow>\<^sup>* j\<^sub>1\<close>\<close>
  have chain: "(nextrel0 N)\<^sup>*\<^sup>* q ?j1"
  proof (rule le0_build[OF NT j1L qj1])
    show "\<forall>j. q < j \<and> j \<le> ?j1 \<longrightarrow> entry N 0 q < entry N 0 j"
      using strict by blast
  qed
  show ?thesis using chain qL j1L by (simp add: le0_def)
qed

text \<open>§6.7 RESIDUAL 1 (tree), fully reduced to the single tail invariant
  \<open>tail_affine\<close> (attempt C).  Combines @{thm [source] brick_from_tail_affine}
  (tail-affine \<open>\<Longrightarrow>\<close> the row-0 reach brick \<open>le0 N p j\<^sub>1\<close>) with
  @{thm [source] m_6_7_tree_wellformed} (brick \<open>\<Longrightarrow>\<close> tree well-formedness).
  The ONLY hypothesis beyond the standard spsy-domain facts is \<open>tail_affine\<close>:
  on the tail \<open>[j\<^sub>0, j\<^sub>1]\<close> the row-0 reading is the affine ramp
  \<open>entry N 0 x = entry N 0 j\<^sub>0 + (x - j\<^sub>0)\<close> (empirically 142/0 on genuine ST_PS,
  FALSE on general T_PS).  Cites only @{thm [source] brick_from_tail_affine},
  @{thm [source] m_6_7_tree_wellformed}; no spsy / sblk / via_spsy / RedCond / oper.\<close>

lemma m_6_7_tree_wellformed_via_affine:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and hp1: "hasParent N 1 (Lng N - 1)"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and zlo: "parent N 1 (Lng N - 1) < z"
    and zhi: "z < Lng N - 1"
    and hpz: "hasParent N 1 z"
    and pge: "parent N 1 z \<ge> parent N 1 (Lng N - 1)"
    and pgt: "parent N 1 z > parent N 1 (Lng N - 1)"
    and affine: "\<And>x. parent N 1 (Lng N - 1) \<le> x \<Longrightarrow> x \<le> Lng N - 1
                   \<Longrightarrow> entry N 0 x = entry N 0 (parent N 1 (Lng N - 1)) + (x - parent N 1 (Lng N - 1))"
  shows "hasParent N 1 (parent N 1 z)
         \<and> parent N 1 (parent N 1 z) \<ge> parent N 1 (Lng N - 1)"
proof -
  let ?j1 = "Lng N - 1"  let ?j0 = "parent N 1 ?j1"  let ?p = "parent N 1 z"
  have NT: "N \<in> T_PS" using L by (cases N) (auto simp: T_PS_def)
  \<comment> \<open>\<open>p = parent N 1 z\<close> is an interior tail node \<open>j\<^sub>0 < p < j\<^sub>1\<close>\<close>
  have parRz: "nextR N 1 ?p z"
    using hpz unfolding hasParent_def parent_def by (rule theI')
  have nr1z: "nextrel1 N ?p z" using parRz by (simp add: nextR_def)
  have plt: "?p < z" using nr1z by (simp add: nextrel1_def)
  have pgtj0: "?j0 < ?p" using pgt .
  have pltj1: "?p < ?j1" using plt zhi by linarith
  \<comment> \<open>the brick \<open>le0 N p j\<^sub>1\<close> from the tail-affine invariant\<close>
  have reach: "le0 N ?p ?j1"
    by (rule brick_from_tail_affine[OF NT j0lt pgtj0 pltj1 affine])
  \<comment> \<open>feed it to the already-GREEN tree well-formedness reduction\<close>
  show ?thesis
    by (rule m_6_7_tree_wellformed[OF L hp1 j0lt zlo zhi hpz pge pgt reach])
qed


text \<open>§6.7 BRICK reduction (TREE route, SOUND) -- the row-0 reach \<open>le0 N p j\<^sub>1\<close>
  for the row-1 parent \<open>p = parent N 1 z\<close> of an interior node \<open>z\<close>, STRICTLY above
  the root \<open>j\<^sub>0\<close> (\<open>p > j\<^sub>0\<close>), follows from the SUB-RANGE \<open>+1\<close> ramp on \<open>[p, j\<^sub>1]\<close>:
  \<open>entry N 0 (x+1) = entry N 0 x + 1\<close> for \<open>p \<le> x < j\<^sub>1\<close>.  This ramp makes
  \<open>entry N 0\<close> strictly increasing on \<open>(p, j\<^sub>1]\<close>, so @{thm [source] le0_build}
  chains \<open>p \<rightarrow>\<^sup>* j\<^sub>1\<close> in row 0.  EMPIRICALLY the consecutive-\<open>+1\<close> ramp on the
  SUB-range \<open>[p, j\<^sub>1)\<close> holds 739/0 on the broad genuine ST_PS closure (it is the
  SOUND replacement of the FALSE whole-tail \<open>tail_affine\<close> on \<open>[j\<^sub>0, j\<^sub>1]\<close>: the strict
  condition \<open>p > j\<^sub>0\<close> excludes the degenerate flat-tail members, where the only
  interior \<open>z\<close> has \<open>parent = j\<^sub>0\<close>, so this hypothesis is VACUOUS there).
  Cites only @{thm [source] le0_build}; no spsy / sblk / via_spsy / RedCond / oper.\<close>

lemma brick_from_subramp:
  fixes N :: pairseq
  assumes NT: "N \<in> T_PS"
    and j1L: "Lng N - 1 < Lng N"
    and pj1: "p < Lng N - 1"
    and ramp: "\<And>x. p \<le> x \<Longrightarrow> x < Lng N - 1
                  \<Longrightarrow> entry N 0 (Suc x) = Suc (entry N 0 x)"
  shows "le0 N p (Lng N - 1)"
proof -
  let ?j1 = "Lng N - 1"
  \<comment> \<open>the ramp gives \<open>entry N 0 (p+t) = entry N 0 p + t\<close> on \<open>[p, j\<^sub>1]\<close>\<close>
  have ramp_abs: "\<And>t. p + t \<le> ?j1 \<Longrightarrow> entry N 0 (p + t) = entry N 0 p + t"
  proof -
    fix t assume "p + t \<le> ?j1"
    thus "entry N 0 (p + t) = entry N 0 p + t"
    proof (induction t)
      case 0 show ?case by simp
    next
      case (Suc t)
      have le1: "p + t \<le> ?j1" using Suc.prems by simp
      have lt: "p + t < ?j1" using Suc.prems by simp
      have pge: "p \<le> p + t" by simp
      have "entry N 0 (Suc (p + t)) = Suc (entry N 0 (p + t))"
        by (rule ramp[OF pge lt])
      also have "entry N 0 (p + t) = entry N 0 p + t" using Suc.IH[OF le1] .
      finally show ?case by simp
    qed
  qed
  \<comment> \<open>strict row-0 increase on \<open>(p, j\<^sub>1]\<close>\<close>
  have strict: "\<forall>j. p < j \<and> j \<le> ?j1 \<longrightarrow> entry N 0 p < entry N 0 j"
  proof (intro allI impI)
    fix j assume j: "p < j \<and> j \<le> ?j1"
    obtain t where jt: "j = p + t" and tpos: "0 < t"
      using j by (metis less_imp_add_positive)
    have ple: "p + t \<le> ?j1" using j jt by simp
    have "entry N 0 j = entry N 0 p + t" using ramp_abs[OF ple] jt by simp
    thus "entry N 0 p < entry N 0 j" using tpos by simp
  qed
  have chain: "(nextrel0 N)\<^sup>*\<^sup>* p ?j1"
    by (rule le0_build[OF NT j1L pj1 strict])
  show ?thesis using chain pj1 j1L by (simp add: le0_def)
qed


text \<open>§6.7 RESIDUAL 1 (tree), reduced to the SOUND sub-range \<open>+1\<close> ramp on
  \<open>[p, j\<^sub>1]\<close> (\<open>p = parent N 1 z > j\<^sub>0\<close>).  Combines @{thm [source] brick_from_subramp}
  (sub-ramp \<open>\<Longrightarrow>\<close> the row-0 reach brick \<open>le0 N p j\<^sub>1\<close>) with
  @{thm [source] m_6_7_tree_wellformed} (brick \<open>\<Longrightarrow>\<close> tree well-formedness).
  Cites only @{thm [source] brick_from_subramp},
  @{thm [source] m_6_7_tree_wellformed}; no spsy / sblk / via_spsy / RedCond / oper.\<close>

lemma m_6_7_tree_wellformed_via_subramp:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and hp1: "hasParent N 1 (Lng N - 1)"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and zlo: "parent N 1 (Lng N - 1) < z"
    and zhi: "z < Lng N - 1"
    and hpz: "hasParent N 1 z"
    and pge: "parent N 1 z \<ge> parent N 1 (Lng N - 1)"
    and pgt: "parent N 1 z > parent N 1 (Lng N - 1)"
    and ramp: "\<And>x. parent N 1 z \<le> x \<Longrightarrow> x < Lng N - 1
                  \<Longrightarrow> entry N 0 (Suc x) = Suc (entry N 0 x)"
  shows "hasParent N 1 (parent N 1 z)
         \<and> parent N 1 (parent N 1 z) \<ge> parent N 1 (Lng N - 1)"
proof -
  let ?j1 = "Lng N - 1"  let ?j0 = "parent N 1 ?j1"  let ?p = "parent N 1 z"
  have NT: "N \<in> T_PS" using L by (cases N) (auto simp: T_PS_def)
  have j1L: "?j1 < Lng N" using L by linarith
  \<comment> \<open>\<open>p = parent N 1 z\<close> is an interior tail node \<open>j\<^sub>0 < p < j\<^sub>1\<close>\<close>
  have parRz: "nextR N 1 ?p z"
    using hpz unfolding hasParent_def parent_def by (rule theI')
  have nr1z: "nextrel1 N ?p z" using parRz by (simp add: nextR_def)
  have plt: "?p < z" using nr1z by (simp add: nextrel1_def)
  have pltj1: "?p < ?j1" using plt zhi by linarith
  \<comment> \<open>the brick \<open>le0 N p j\<^sub>1\<close> from the sub-range ramp\<close>
  have reach: "le0 N ?p ?j1"
    by (rule brick_from_subramp[OF NT j1L pltj1 ramp])
  \<comment> \<open>feed it to the already-GREEN tree well-formedness reduction\<close>
  show ?thesis
    by (rule m_6_7_tree_wellformed[OF L hp1 j0lt zlo zhi hpz pge pgt reach])
qed


lemma SkT_row0_step_le:
  shows "N \<in> SkT_PS k \<Longrightarrow> Suc j < Lng N
         \<Longrightarrow> entry N 0 (Suc j) \<le> Suc (entry N 0 j)"
proof -
  have "\<forall>N. N \<in> SkT_PS k \<longrightarrow>
          (\<forall>j. Suc j < Lng N \<longrightarrow> entry N 0 (Suc j) \<le> Suc (entry N 0 j))"
  proof (induction k)
    case 0
    show ?case
    proof (intro allI impI)
      fix N j
      assume N0: "N \<in> SkT_PS 0" and A: "Suc j < Lng N"
      from N0 obtain u v where Nuv: "N = diagSeq u v" and uv: "u \<le> v" by auto
      have lt: "Suc j < Lng N" using A by simp
      have jlt: "j < Suc v - u" using lt Nuv by simp
      have sjlt: "Suc j < Suc v - u" using lt Nuv by simp
      have e0j: "entry N 0 j = u + j" using Nuv jlt by (simp add: entry_diagSeq)
      have e0sj: "entry N 0 (Suc j) = u + Suc j" using Nuv sjlt by (simp add: entry_diagSeq)
      show "entry N 0 (Suc j) \<le> Suc (entry N 0 j)" using e0j e0sj by simp
    qed
  next
    case (Suc k)
    note IHk = Suc.IH
    show ?case
    proof (intro allI impI)
      fix N j
      assume NS: "N \<in> SkT_PS (Suc k)" and A: "Suc j < Lng N"
      from NS obtain M n where Neq: "N = (M::pairseq)[n]"
        and MS: "M \<in> SkT_PS k" and n1: "1 \<le> n" by auto
      have MT: "M \<in> T_PS" using MS SkT_PS_subset_ST_PS ST_PS_T_PS by blast
      from A have sjlt: "Suc j < Lng N" by simp
      let ?j1 = "Lng M - 1"  let ?i1 = "idx1 M ?j1"  let ?j0 = "parent M ?i1 ?j1"
      \<comment> \<open>Degenerate oper guards: \<open>N = Pred M\<close>.  Reduce adjacent increments to \<open>M\<close>, IH.\<close>
      have pred_case: "N = Pred M \<Longrightarrow> entry N 0 (Suc j) \<le> Suc (entry N 0 j)"
      proof -
        assume Npred: "N = Pred M"
        show "entry N 0 (Suc j) \<le> Suc (entry N 0 j)"
        proof (cases "Lng M \<le> 1")
          case True
          hence "Pred M = M" by (simp add: Pred_def)
          hence Nm: "N = M" using Npred by simp
          have sjM: "Suc j < Lng M" using sjlt Nm by simp
          have "entry M 0 (Suc j) \<le> Suc (entry M 0 j)" using IHk MS sjM by blast
          thus ?thesis using Nm by simp
        next
          case False
          hence Lgt: "1 < Lng M" by simp
          hence Nbl: "N = butlast M" using Npred by (simp add: Pred_def)
          have lbl: "Lng (butlast M) = Lng M - 1" by simp
          have sjbl: "Suc j < Lng M - 1" using sjlt Nbl lbl by simp
          have sjM: "Suc j < Lng M" using sjbl by simp
          have jblbl: "j < length (butlast M)" using sjbl lbl by simp
          have sjblbl: "Suc j < length (butlast M)" using sjbl lbl by simp
          have ej: "entry N i j = entry M i j" for i
            using Nbl jblbl by (simp add: entry_def nth_butlast)
          have esj: "entry N i (Suc j) = entry M i (Suc j)" for i
            using Nbl sjblbl by (simp add: entry_def nth_butlast)
          have "entry M 0 (Suc j) \<le> Suc (entry M 0 j)" using IHk MS sjM by blast
          thus ?thesis using ej esj by simp
        qed
      qed
      show "entry N 0 (Suc j) \<le> Suc (entry N 0 j)"
      proof (cases "?j1 = 0")
        case True
        hence Nm: "N = M" using Neq by (simp add: oper_def Let_def)
        have "Lng M \<le> 1" using True by simp
        hence "Pred M = M" by (simp add: Pred_def)
        hence "N = Pred M" using Nm by simp
        thus ?thesis using pred_case by simp
      next
        case j1pos: False
        hence Lgt: "1 < Lng M" by simp
        show ?thesis
        proof (cases "entry M 0 ?j1 = 0 \<and> entry M 1 ?j1 = 0")
          case True
          hence "N = Pred M" using Neq j1pos by (simp add: oper_def Let_def)
          thus ?thesis using pred_case by simp
        next
          case notzero: False
          show ?thesis
          proof (cases "hasParent M ?i1 ?j1")
            case False
            hence "N = Pred M" using Neq notzero j1pos by (simp add: oper_def Let_def)
            thus ?thesis using pred_case by simp
          next
            case hp: True
            \<comment> \<open>Expansion branch.  \<open>j\<^sub>0 < j\<^sub>1\<close>, \<open>w = j\<^sub>1 - j\<^sub>0 \<ge> 1\<close>.\<close>
            have parR: "nextR M ?i1 ?j0 ?j1"
              using hp unfolding hasParent_def parent_def by (rule theI')
            have j0lt: "?j0 < ?j1" using poper_nextR_imp_le0[OF parR] by simp
            let ?w = "?j1 - ?j0"
            let ?d0 = "if 0 < ?i1 then entry M 0 ?j1 - entry M 0 ?j0 else 0"
            have w1: "1 \<le> ?w" using j0lt by simp
            have w0: "0 < ?w" using w1 by simp
            have lenN: "Lng N = ?j0 + n * ?w"
            proof -
              let ?d1 = "if 1 < ?i1 then entry M 1 ?j1 - entry M 1 ?j0 else 0"
              let ?Braw = "\<lambda>k. map (\<lambda>jj. (entry M 0 jj + k * ?d0, entry M 1 jj + k * ?d1)) [?j0..<?j1]"
              have expand: "M[n] = take ?j0 M @ concat (map ?Braw [0..<n])"
                by (rule poper_oper_expand[OF Lgt notzero hp, of n, unfolded Let_def])
              have t: "length (take ?j0 M) = ?j0" using j0lt Lgt by simp
              have lmap: "map Lng (map ?Braw [0..<n]) = replicate n ?w"
              proof -
                have "map Lng (map ?Braw [0..<n]) = map (\<lambda>k. ?w) [0..<n]" by simp
                thus ?thesis by (simp add: map_replicate_const)
              qed
              have lc: "length (concat (map ?Braw [0..<n])) = n * ?w"
                by (subst length_concat, subst lmap) (simp add: sum_list_replicate)
              show ?thesis using expand t lc Neq by simp
            qed
            have blk0: "\<And>q s. q < n \<Longrightarrow> s < ?w \<Longrightarrow>
                          entry N 0 (?j0 + q * ?w + s) = entry M 0 (?j0 + s) + q * ?d0"
              using oper_gen_block_entry0[OF Lgt notzero hp j0lt] Neq by simp
            have pre: "\<And>x i. x < ?j0 \<Longrightarrow> entry N i x = entry M i x"
              using oper_gen_nth_prefix[OF Lgt notzero hp] Neq by (simp add: entry_def)
            have sjN: "Suc j < ?j0 + n * ?w" using sjlt lenN by simp
            show ?thesis
            proof (cases "Suc j \<le> ?j0")
              case prefix: True
              have jlt: "j < ?j0" using prefix by simp
              have ej: "entry N 0 j = entry M 0 j" using pre[OF jlt] by simp
              have esj: "entry N 0 (Suc j) = entry M 0 (Suc j)"
              proof (cases "Suc j < ?j0")
                case True
                show "entry N 0 (Suc j) = entry M 0 (Suc j)" using pre[OF True] by simp
              next
                case False
                hence sjeq: "Suc j = ?j0" using prefix by linarith
                have e0: "entry N 0 (?j0 + 0 * ?w + 0) = entry M 0 (?j0 + 0) + 0 * ?d0"
                  by (rule blk0[OF _ ]) (use n1 w1 in auto)
                show "entry N 0 (Suc j) = entry M 0 (Suc j)" using e0 sjeq by simp
              qed
              have sjM: "Suc j < Lng M" using prefix j0lt by simp
              have "entry M 0 (Suc j) \<le> Suc (entry M 0 j)" using IHk MS sjM by blast
              thus ?thesis using ej esj by simp
            next
              case AB: False
              hence j0lej: "?j0 \<le> j" by simp
              define s where "s = (j - ?j0) mod ?w"
              define q where "q = (j - ?j0) div ?w"
              have sw: "s < ?w" using w0 by (simp add: s_def)
              have jsplit: "j = ?j0 + q * ?w + s"
                using j0lej div_mult_mod_eq[of "j - ?j0" ?w]
                by (simp add: s_def q_def algebra_simps)
              have jblk: "j < ?j0 + n * ?w" using sjN by simp
              have qn: "q < n"
              proof -
                have "q * ?w + s < n * ?w" using jblk jsplit by linarith
                hence "q * ?w < n * ?w" using sw by linarith
                thus ?thesis using w0 by simp
              qed
              show ?thesis
              proof (cases "s + 1 < ?w")
                case within: True
                have sjsplit: "Suc j = ?j0 + q * ?w + (s + 1)" using jsplit by simp
                have e0j: "entry N 0 j = entry M 0 (?j0 + s) + q * ?d0"
                  using blk0[OF qn sw] jsplit by simp
                have e0sj: "entry N 0 (Suc j) = entry M 0 (?j0 + (s+1)) + q * ?d0"
                  using blk0[OF qn within] sjsplit by simp
                have sjM: "Suc (?j0 + s) < Lng M" using within sw j0lt by simp
                have "entry M 0 (Suc (?j0 + s)) \<le> Suc (entry M 0 (?j0 + s))"
                  using IHk MS sjM by blast
                hence "entry M 0 (?j0 + (s+1)) \<le> Suc (entry M 0 (?j0 + s))" by simp
                thus ?thesis using e0j e0sj by simp
              next
                case boundary: False
                have seq: "s = ?w - 1" using boundary sw by linarith
                obtain WW where WWdef: "WW = ?w" and WW1: "1 \<le> WW" using w1 by blast
                obtain JJ where JJdef: "JJ = ?j0" by blast
                have jend: "j = JJ + q * WW + (WW - 1)"
                  using jsplit seq WWdef JJdef by simp
                have sjstart: "Suc j = JJ + (q+1) * WW + 0"
                  using jend WW1 by (simp add: algebra_simps)
                have sjstart': "Suc j = ?j0 + (q+1) * ?w + 0"
                  using sjstart WWdef JJdef by simp
                have q1n: "q + 1 < n"
                proof -
                  have sjNW: "Suc j < JJ + n * WW" using sjN WWdef JJdef by simp
                  have "JJ + (q+1) * WW < JJ + n * WW" using sjNW sjstart by simp
                  hence lt: "(q+1) * WW < n * WW" by simp
                  have W0: "0 < WW" using WW1 by simp
                  show ?thesis using lt W0 mult_less_cancel2[of "q+1" WW n] by simp
                qed
                have jend': "j = ?j0 + q * ?w + (?w - 1)"
                  using jend WWdef JJdef by simp
                have w1le: "?w - 1 < ?w" using w0 by simp
                have j0w1: "?j0 + (?w - 1) = ?j1 - 1" using j0lt by simp
                have e0j: "entry N 0 j = entry M 0 (?j1 - 1) + q * ?d0"
                  using blk0[OF qn w1le] jend' j0w1 by simp
                have e0sj: "entry N 0 (Suc j) = entry M 0 ?j0 + (q+1) * ?d0"
                  using blk0[OF q1n w0] sjstart' by simp
                show ?thesis
                proof (cases "?i1 = 0")
                  case i0: True
                  hence d0z: "?d0 = 0" by simp
                  have nr0: "nextrel0 M ?j0 ?j1" using parR i0 by (simp add: nextR_def)
                  have lt0: "entry M 0 ?j0 < entry M 0 ?j1" using nr0 by (simp add: nextrel0_def)
                  \<comment> \<open>Goal (\<open>d\<^sub>0=0\<close>): \<open>M\<^bsub>0,j\<^sub>0\<^esub> \<le> Suc M\<^bsub>0,j\<^sub>1-1\<^esub>\<close>.  \<open>w=1\<close>: \<open>j\<^sub>1-1=j\<^sub>0\<close>, trivial.
                     \<open>w\<ge>2\<close>: \<open>j\<^sub>1-1\<close> interior so \<open>M\<^bsub>0,j\<^sub>1\<^esub> \<le> M\<^bsub>0,j\<^sub>1-1\<^esub>\<close> (nextrel0 descent), with
                     \<open>M\<^bsub>0,j\<^sub>0\<^esub> < M\<^bsub>0,j\<^sub>1\<^esub>\<close>.\<close>
                  have goal0: "entry M 0 ?j0 \<le> Suc (entry M 0 (?j1 - 1))"
                  proof (cases "?w = 1")
                    case wone: True
                    have "?j1 - 1 = ?j0" using wone j0lt by simp
                    thus ?thesis by simp
                  next
                    case wgt: False
                    have w2: "2 \<le> ?w" using wgt w1 by linarith
                    have interior: "?j0 < ?j1 - 1 \<and> ?j1 - 1 < ?j1" using w2 j0lt by linarith
                    have ge: "entry M 0 ?j1 \<le> entry M 0 (?j1 - 1)"
                      using nr0 interior by (simp add: nextrel0_def)
                    show ?thesis using lt0 ge by linarith
                  qed
                  thus ?thesis using e0j e0sj d0z by simp
                next
                  case i1: False
                  have i1one: "?i1 = 1"
                    using i1 unfolding idx1_def by (cases "entry M 1 ?j1 > 0") simp_all
                  have d0v: "?d0 = entry M 0 ?j1 - entry M 0 ?j0" using i1one by simp
                  have nr1: "nextrel1 M ?j0 ?j1" using parR i1one by (simp add: nextR_def)
                  have le0j: "le0 M ?j0 ?j1" using nr1 by (simp add: nextrel1_def)
                  have le0r: "entry M 0 ?j0 \<le> entry M 0 ?j1"
                    using le0j by (simp add: le0_def nextrel0_rtrancl_entry0_mono)
                  \<comment> \<open>\<open>e0sj = M\<^bsub>0,j\<^sub>0\<^esub> + (q+1)\<cdot>d\<^sub>0 = (M\<^bsub>0,j\<^sub>1\<^esub>) + q\<cdot>d\<^sub>0\<close>; \<open>e0j = M\<^bsub>0,j\<^sub>1-1\<^esub> + q\<cdot>d\<^sub>0\<close>.
                     IH on \<open>M\<close> at \<open>(j\<^sub>1-1, j\<^sub>1)\<close> gives \<open>M\<^bsub>0,j\<^sub>1\<^esub> \<le> Suc M\<^bsub>0,j\<^sub>1-1\<^esub>\<close>.\<close>
                  have e0sj': "entry N 0 (Suc j) = entry M 0 ?j1 + q * ?d0"
                    using e0sj d0v le0r by simp
                  have j1ge1: "1 \<le> ?j1" using j0lt by linarith
                  have sucj1: "Suc (?j1 - 1) = ?j1" using j1ge1 by simp
                  have sjM: "Suc (?j1 - 1) < Lng M" using sucj1 Lgt by simp
                  have IHadj: "entry M 0 (Suc (?j1 - 1)) \<le> Suc (entry M 0 (?j1 - 1))"
                    using IHk MS sjM by blast
                  have IHj1: "entry M 0 ?j1 \<le> Suc (entry M 0 (?j1 - 1))" using IHadj sucj1 by simp
                  show ?thesis using e0j e0sj' IHj1 by simp
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  thus "N \<in> SkT_PS k \<Longrightarrow> Suc j < Lng N
         \<Longrightarrow> entry N 0 (Suc j) \<le> Suc (entry N 0 j)" by blast
qed

text \<open>The step bound (S) lifted to \<open>ST\<^sub>PS\<close> via the stratification
  @{thm [source] ST_PS_in_some_SkT}.\<close>

lemma ST_row0_step_le:
  assumes N: "N \<in> ST_PS" and sj: "Suc j < Lng N"
  shows "entry N 0 (Suc j) \<le> Suc (entry N 0 j)"
proof -
  obtain k where Nk: "N \<in> SkT_PS k"
    using N ST_PS_in_some_SkT unfolding in_some_SkT_def by blast
  show ?thesis by (rule SkT_row0_step_le[OF Nk sj])
qed


text \<open>§6.7 SUBRAMP ARITHMETIC GLUE (GREEN, unconditional finite-arith).  For
  \<open>N \<in> ST\<^sub>PS\<close> the row-0 step UPPER bound (@{thm [source] ST_row0_step_le}) gives
  \<open>entry N 0 (x+1) \<le> entry N 0 x + 1\<close> on \<open>[p, j\<^sub>1)\<close>, hence cumulatively
  \<open>entry N 0 x \<le> entry N 0 p + (x - p)\<close> for \<open>p \<le> x \<le> j\<^sub>1\<close>.  If, in addition, the
  ENDPOINT slope-1 fact (@{text E_p}) holds --- the total over \<open>[p, j\<^sub>1]\<close> is the
  full width: \<open>entry N 0 j\<^sub>1 = entry N 0 p + (j\<^sub>1 - p)\<close> --- then NO step can fall
  short of \<open>+1\<close> (a deficit anywhere would make the endpoint strictly below the
  width), so EVERY step on \<open>[p, j\<^sub>1)\<close> is EXACTLY \<open>+1\<close>: the precise sub-ramp
  hypothesis of @{thm [source] brick_from_subramp} /
  @{thm [source] m_6_7_tree_wellformed_via_subramp}.  EMPIRICALLY both the
  per-step bound (21452/0) and the resulting \<open>+1\<close> sub-ramp (2977/0) hold on the
  broad genuine ST_PS closure (depth\<ge>5, maxlen\<le>14).  Cites only
  @{thm [source] ST_row0_step_le}; no spsy / sblk / RedCond / oper / tail_affine.\<close>

lemma subramp_from_Ep:
  fixes N :: pairseq
  assumes N: "N \<in> ST_PS"
    and pj1: "p < Lng N - 1"
    and Ep: "entry N 0 (Lng N - 1) = entry N 0 p + ((Lng N - 1) - p)"
    and xlo: "p \<le> x"
    and xhi: "x < Lng N - 1"
  shows "entry N 0 (Suc x) = Suc (entry N 0 x)"
proof -
  let ?j1 = "Lng N - 1"
  \<comment> \<open>cumulative upper bound from the per-step \<open>\<le> +1\<close> reading, from any base \<open>b\<close>\<close>
  have upper_from: "\<And>b s. b + s \<le> ?j1 \<Longrightarrow> entry N 0 (b + s) \<le> entry N 0 b + s"
  proof -
    fix b s assume "b + s \<le> ?j1"
    thus "entry N 0 (b + s) \<le> entry N 0 b + s"
    proof (induction s)
      case 0 show ?case by simp
    next
      case (Suc s)
      have le1: "b + s \<le> ?j1" using Suc.prems by simp
      have ssj: "Suc (b + s) < Lng N" using Suc.prems by simp
      have step: "entry N 0 (Suc (b + s)) \<le> Suc (entry N 0 (b + s))"
        by (rule ST_row0_step_le[OF N ssj])
      have ih: "entry N 0 (b + s) \<le> entry N 0 b + s" using Suc.IH[OF le1] .
      have "entry N 0 (b + (Suc s)) = entry N 0 (Suc (b + s))" by simp
      thus ?case using step ih by simp
    qed
  qed
  \<comment> \<open>the upper bound, in absolute (\<open>y\<close>) form, for \<open>a \<le> y \<le> j\<^sub>1\<close>\<close>
  have upper_abs: "\<And>a y. a \<le> y \<Longrightarrow> y \<le> ?j1 \<Longrightarrow> entry N 0 y \<le> entry N 0 a + (y - a)"
  proof -
    fix a y assume ay: "a \<le> y" and yj1: "y \<le> ?j1"
    obtain s where ys: "y = a + s" using ay le_Suc_ex by blast
    have "a + s \<le> ?j1" using ys yj1 by simp
    from upper_from[OF this] have "entry N 0 (a + s) \<le> entry N 0 a + s" .
    thus "entry N 0 y \<le> entry N 0 a + (y - a)" using ys by simp
  qed
  \<comment> \<open>every node on \<open>[p, j\<^sub>1]\<close> sits EXACTLY on the slope-1 line\<close>
  have exact: "\<And>y. p \<le> y \<Longrightarrow> y \<le> ?j1 \<Longrightarrow> entry N 0 y = entry N 0 p + (y - p)"
  proof -
    fix y assume py: "p \<le> y" and yj1: "y \<le> ?j1"
    have le_y: "entry N 0 y \<le> entry N 0 p + (y - p)" by (rule upper_abs[OF py yj1])
    have le_rest: "entry N 0 ?j1 \<le> entry N 0 y + (?j1 - y)" by (rule upper_abs[OF yj1 le_refl])
    have width_eq: "(y - p) + (?j1 - y) = ?j1 - p" using py yj1 by linarith
    \<comment> \<open>width \<open>= E_p \<le> (line at y) + (rest) \<le> width\<close>, forcing equality at \<open>y\<close>\<close>
    have squeeze: "entry N 0 p + (?j1 - p) \<le> entry N 0 y + (?j1 - y)"
      using Ep le_rest by linarith
    have ge_y: "entry N 0 p + (y - p) \<le> entry N 0 y"
      using squeeze width_eq by linarith
    show "entry N 0 y = entry N 0 p + (y - p)" using le_y ge_y by linarith
  qed
  \<comment> \<open>read off the \<open>+1\<close> step at \<open>x\<close>\<close>
  have sxj1: "Suc x \<le> ?j1" using xhi by simp
  have xj1: "x \<le> ?j1" using xhi by simp
  have ex_x: "entry N 0 x = entry N 0 p + (x - p)" by (rule exact[OF xlo xj1])
  have psx: "p \<le> Suc x" using xlo by simp
  have ex_sx: "entry N 0 (Suc x) = entry N 0 p + (Suc x - p)" by (rule exact[OF psx sxj1])
  have "Suc x - p = Suc (x - p)" using xlo by simp
  thus ?thesis using ex_x ex_sx by simp
qed


text \<open>§6.7 RESIDUAL 1 (tree) -- COMPLETE ASSEMBLY modulo the endpoint slope-1
  fact \<open>E_p\<close>.  Given the standard subramp-applicability hypotheses (interior
  \<open>z\<close>, \<open>p = parent N 1 z > j\<^sub>0\<close>) AND the SINGLE remaining \<open>E_p\<close> input --- the
  total row-0 rise over \<open>[p, j\<^sub>1]\<close> equals the width
  (\<open>entry N 0 j\<^sub>1 = entry N 0 p + (j\<^sub>1 - p)\<close>, EMPIRICALLY 2977/0 on the broad
  ST_PS closure) --- the tree well-formedness conclusion follows: the arithmetic
  glue (@{thm [source] subramp_from_Ep}) upgrades \<open>E_p\<close> + the per-step \<open>\<le>+1\<close>
  bound to the exact \<open>+1\<close> sub-ramp on \<open>[p, j\<^sub>1)\<close>, which
  @{thm [source] m_6_7_tree_wellformed_via_subramp} converts to the tree.
  Cites only @{thm [source] subramp_from_Ep},
  @{thm [source] m_6_7_tree_wellformed_via_subramp}; no spsy / sblk / via_spsy /
  RedCond / oper / tail_affine.  This reduces RESIDUAL 1 to the lone \<open>E_p\<close>
  row-1-ancestor fact.\<close>

lemma m_6_7_tree_wellformed_via_Ep:
  fixes N :: pairseq
  assumes N: "N \<in> ST_PS"
    and L: "1 < Lng N"
    and hp1: "hasParent N 1 (Lng N - 1)"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and zlo: "parent N 1 (Lng N - 1) < z"
    and zhi: "z < Lng N - 1"
    and hpz: "hasParent N 1 z"
    and pge: "parent N 1 z \<ge> parent N 1 (Lng N - 1)"
    and pgt: "parent N 1 z > parent N 1 (Lng N - 1)"
    and Ep: "entry N 0 (Lng N - 1)
               = entry N 0 (parent N 1 z) + ((Lng N - 1) - parent N 1 z)"
  shows "hasParent N 1 (parent N 1 z)
         \<and> parent N 1 (parent N 1 z) \<ge> parent N 1 (Lng N - 1)"
proof -
  let ?j1 = "Lng N - 1"  let ?j0 = "parent N 1 ?j1"  let ?p = "parent N 1 z"
  \<comment> \<open>\<open>p = parent N 1 z\<close> is an interior tail node \<open>j\<^sub>0 < p < j\<^sub>1\<close>\<close>
  have parRz: "nextR N 1 ?p z"
    using hpz unfolding hasParent_def parent_def by (rule theI')
  have nr1z: "nextrel1 N ?p z" using parRz by (simp add: nextR_def)
  have plt: "?p < z" using nr1z by (simp add: nextrel1_def)
  have pltj1: "?p < ?j1" using plt zhi by linarith
  \<comment> \<open>the exact \<open>+1\<close> sub-ramp on \<open>[p, j\<^sub>1)\<close> via the arithmetic glue\<close>
  have ramp: "\<And>x. ?p \<le> x \<Longrightarrow> x < ?j1 \<Longrightarrow> entry N 0 (Suc x) = Suc (entry N 0 x)"
    by (rule subramp_from_Ep[OF N pltj1 Ep])
  \<comment> \<open>convert to the tree via the already-GREEN sub-ramp reduction\<close>
  show ?thesis
    by (rule m_6_7_tree_wellformed_via_subramp[OF L hp1 j0lt zlo zhi hpz pge pgt ramp])
qed


text \<open>§6.7 E_p VIA THE row-0 le0-TAIL (GREEN bridge, unconditional finite-arith +
  already-GREEN row-0 facts).  This isolates the EXACT remaining structural input
  of \<open>E_p\<close> to a single clean reachability hypothesis and discharges everything
  else.  The hypothesis \<open>tailReach\<close>: every index \<open>x\<close> on \<open>[p, j\<^sub>1)\<close> row-0-reaches
  the endpoint \<open>j\<^sub>1 = Lng N - 1\<close> (\<open>le0 N x j\<^sub>1\<close>).  EMPIRICALLY this is exactly the
  fact that holds 2977/0 on the broad ST_PS closure for \<open>p = parent N 1 z\<close> with
  interior \<open>z\<close> (the row-1 ancestor structure forces it), while the unconditional
  per-step UPPER bound (@{thm [source] ST_row0_step_le}) caps each step at \<open>+1\<close>.

  Argument: from \<open>le0 N x j\<^sub>1\<close> the rtrancl chain \<open>x \<rightarrow>\<^sup>* j\<^sub>1\<close> gives, via
  @{thm [source] le0_ances_aux} at \<open>j = Suc x\<close> (\<open>x < Suc x \<le> j\<^sub>1\<close>), the strict
  increase \<open>entry N 0 x < entry N 0 (Suc x)\<close>, i.e. each step is \<open>\<ge> +1\<close>; combined
  with the \<open>\<le> +1\<close> cap this pins EVERY step on \<open>[p, j\<^sub>1)\<close> to EXACTLY \<open>+1\<close>.
  Cumulating from \<open>p\<close> yields the endpoint slope-1 equation \<open>E_p\<close>.  Cites only
  @{thm [source] ST_row0_step_le}, @{thm [source] le0_ances_aux},
  @{thm [source] le0_def}; no spsy / sblk / via_spsy / RedCond / oper /
  tail_affine.  Feeds @{thm [source] subramp_from_Ep} /
  @{thm [source] m_6_7_tree_wellformed_via_Ep} with no further glue.\<close>

lemma Ep_from_le0_tail:
  fixes N :: pairseq
  assumes N: "N \<in> ST_PS"
    and pj1: "p < Lng N - 1"
    and tailReach: "\<And>x. p \<le> x \<Longrightarrow> x < Lng N - 1 \<Longrightarrow> le0 N x (Lng N - 1)"
  shows "entry N 0 (Lng N - 1) = entry N 0 p + ((Lng N - 1) - p)"
proof -
  let ?j1 = "Lng N - 1"
  \<comment> \<open>each step on \<open>[p, j\<^sub>1)\<close> is EXACTLY \<open>+1\<close>: strict \<open>\<ge>\<close> from le0-reach, cap \<open>\<le>\<close> from the step bound\<close>
  have step1: "\<And>x. p \<le> x \<Longrightarrow> x < ?j1 \<Longrightarrow> entry N 0 (Suc x) = Suc (entry N 0 x)"
  proof -
    fix x assume xlo: "p \<le> x" and xhi: "x < ?j1"
    have reach: "le0 N x ?j1" by (rule tailReach[OF xlo xhi])
    have chain: "(nextrel0 N)\<^sup>*\<^sup>* x ?j1" using reach by (simp add: le0_def)
    have ances: "\<forall>j. x < j \<and> j \<le> ?j1 \<longrightarrow> entry N 0 x < entry N 0 j"
      by (rule le0_ances_aux[OF chain])
    have sxle: "Suc x \<le> ?j1" using xhi by simp
    have strict: "entry N 0 x < entry N 0 (Suc x)" using ances sxle by simp
    have ssj: "Suc x < Lng N" using xhi by simp
    have cap: "entry N 0 (Suc x) \<le> Suc (entry N 0 x)" by (rule ST_row0_step_le[OF N ssj])
    show "entry N 0 (Suc x) = Suc (entry N 0 x)" using strict cap by simp
  qed
  \<comment> \<open>cumulate the exact \<open>+1\<close> ramp from \<open>p\<close>: \<open>entry N 0 (p+t) = entry N 0 p + t\<close> on \<open>[p, j\<^sub>1]\<close>\<close>
  have ramp_abs: "\<And>t. p + t \<le> ?j1 \<Longrightarrow> entry N 0 (p + t) = entry N 0 p + t"
  proof -
    fix t assume "p + t \<le> ?j1"
    thus "entry N 0 (p + t) = entry N 0 p + t"
    proof (induction t)
      case 0 show ?case by simp
    next
      case (Suc t)
      have le1: "p + t \<le> ?j1" using Suc.prems by simp
      have lt: "p + t < ?j1" using Suc.prems by simp
      have pge: "p \<le> p + t" by simp
      have "entry N 0 (Suc (p + t)) = Suc (entry N 0 (p + t))"
        by (rule step1[OF pge lt])
      also have "entry N 0 (p + t) = entry N 0 p + t" using Suc.IH[OF le1] .
      finally show ?case by simp
    qed
  qed
  \<comment> \<open>read off the endpoint \<open>j\<^sub>1 = p + (j\<^sub>1 - p)\<close>\<close>
  have peq: "p + (?j1 - p) = ?j1" using pj1 by simp
  have prem: "p + (?j1 - p) \<le> ?j1" using peq by simp
  have "entry N 0 (p + (?j1 - p)) = entry N 0 p + (?j1 - p)"
    by (rule ramp_abs[OF prem])
  thus ?thesis using peq by simp
qed


text \<open>§6.7 \<open>tailReach\<close> FROM ROW-0 STRICT CONSECUTIVE INCREASE (GREEN, unconditional
  pure row-0 chaining).  This isolates the EXACT remaining structural input of
  @{thm [source] Ep_from_le0_tail}'s reachability hypothesis to a single clean
  arithmetic fact: STRICT consecutive row-0 increase on the strict-ancestor tail
  \<open>[p, j\<^sub>1)\<close> (\<open>entry N 0 x < entry N 0 (Suc x)\<close> for \<open>p \<le> x < j\<^sub>1\<close>).  EMPIRICALLY this
  strict-increase fact holds 2977/0 on the broad ST_PS closure (the same population
  on which \<open>tailReach\<close> itself is 19395/0); the consecutive nextrel0-chain reading
  is verified (818/0 sampled), and via the global \<open>\<le> +1\<close> cap
  (@{thm [source] ST_row0_step_le}) each such strict step is in fact EXACTLY \<open>+1\<close>.

  Argument: a consecutive pair \<open>(x, Suc x)\<close> with \<open>Suc x < Lng N\<close> and
  \<open>entry N 0 x < entry N 0 (Suc x)\<close> is a @{const nextrel0} edge (the
  \<open>\<forall>j. x < j < Suc x \<longrightarrow> \<dots>\<close> minimality clause is vacuous), hence \<open>le0 N x (Suc x)\<close>.
  Chaining these edges UPWARD from \<open>x\<close> to \<open>j\<^sub>1\<close> by induction on the remaining
  distance \<open>j\<^sub>1 - x\<close> (@{thm [source] le0_trans}, base \<open>le0_refl\<close> at \<open>j\<^sub>1\<close>) yields
  \<open>le0 N x j\<^sub>1\<close> for EVERY \<open>x\<close> on \<open>[p, j\<^sub>1)\<close> --- exactly the \<open>tailReach\<close> hypothesis
  consumed by @{thm [source] Ep_from_le0_tail}.  Cites only @{thm [source] le0_def},
  @{thm [source] nextrel0_def}, @{thm [source] le0_trans}, @{thm [source] le0_refl};
  no spsy / sblk / via_spsy / RedCond / oper / tail_affine / parent-readback.
  This reduces the row-0 reachability \<open>tailReach\<close> to the lone STRICT-INCREASE fact,
  which the SkT_PS per-block tiling supplies (companion lower bound to the GREEN
  per-step \<open>\<le> +1\<close> upper bound @{thm [source] SkT_row0_step_le}).\<close>

lemma le0_step_consec:
  fixes N :: pairseq
  assumes sxL: "Suc x < Lng N"
    and inc: "entry N 0 x < entry N 0 (Suc x)"
  shows "le0 N x (Suc x)"
proof -
  have xL: "x < Lng N" using sxL by simp
  have nr0: "nextrel0 N x (Suc x)"
    using xL sxL inc by (auto simp: nextrel0_def)
  have "(nextrel0 N)\<^sup>*\<^sup>* x (Suc x)" using nr0 by blast
  thus ?thesis using xL sxL by (simp add: le0_def)
qed

lemma tailReach_from_row0_strict:
  fixes N :: pairseq
  assumes j1L: "Lng N - 1 < Lng N"
    and strict: "\<And>y. p \<le> y \<Longrightarrow> y < Lng N - 1 \<Longrightarrow> entry N 0 y < entry N 0 (Suc y)"
    and xlo: "p \<le> x"
    and xhi: "x < Lng N - 1"
  shows "le0 N x (Lng N - 1)"
proof -
  let ?j1 = "Lng N - 1"
  \<comment> \<open>chain upward from any base \<open>b \<in> [p, j\<^sub>1)\<close> to \<open>j\<^sub>1\<close>, by induction on the gap \<open>j\<^sub>1 - b\<close>\<close>
  have chain: "\<And>b. p \<le> b \<Longrightarrow> b \<le> ?j1 \<Longrightarrow> le0 N b ?j1"
  proof -
    fix b assume "p \<le> b" and "b \<le> ?j1"
    then show "le0 N b ?j1"
    proof (induction "?j1 - b" arbitrary: b)
      case 0
      \<comment> \<open>gap \<open>0\<close>: \<open>b = j\<^sub>1\<close>, reflexive\<close>
      have "b = ?j1" using 0 by linarith
      thus ?case using j1L by (simp add: le0_refl)
    next
      case (Suc d)
      \<comment> \<open>gap \<open>Suc d\<close>: \<open>b < j\<^sub>1\<close>; strict step \<open>b \<rightarrow> Suc b\<close>, then IH on \<open>Suc b\<close>\<close>
      have blt: "b < ?j1" using Suc.hyps(2) by linarith
      have pb: "p \<le> b" using Suc.prems(1) .
      have inc: "entry N 0 b < entry N 0 (Suc b)" by (rule strict[OF pb blt])
      have sbL: "Suc b < Lng N" using blt by simp
      have step: "le0 N b (Suc b)" by (rule le0_step_consec[OF sbL inc])
      have dEq: "d = ?j1 - Suc b" using Suc.hyps(2) by linarith
      have psb: "p \<le> Suc b" using pb by simp
      have sble: "Suc b \<le> ?j1" using blt by simp
      have rest: "le0 N (Suc b) ?j1" using Suc.hyps(1)[OF dEq psb sble] .
      show ?case by (rule le0_trans[OF step rest])
    qed
  qed
  have xle: "x \<le> ?j1" using xhi by simp
  show ?thesis by (rule chain[OF xlo xle])
qed


lemma reach_from_z_tail:
  fixes N :: pairseq
  assumes hpz: "hasParent N 1 z"
    and zj1: "le0 N z (Lng N - 1)"
  shows "le0 N (parent N 1 z) (Lng N - 1)"
proof -
  let ?p = "parent N 1 z"
  have parRz: "nextR N 1 ?p z"
    using hpz unfolding hasParent_def parent_def by (rule theI')
  have nr1z: "nextrel1 N ?p z" using parRz by (simp add: nextR_def)
  have le0pz: "le0 N ?p z" using nr1z by (simp add: nextrel1_def)
  show ?thesis by (rule le0_trans[OF le0pz zj1])
qed


text \<open>§6.7 RESIDUAL 1 (tree) via the INTERIOR-NODE reach \<open>le0 N z j\<^sub>1\<close>
  (attempt X).  Combines @{thm [source] reach_from_z_tail} (the parent edge
  carries \<open>p \<rightarrow>\<^sup>* z\<close>) with @{thm [source] m_6_7_tree_wellformed}.  This is the
  cleanest single-hypothesis form: the entire §6.7 RESIDUAL 1 (tree) now hangs
  on the lone reach FROM \<open>z\<close> \<open>le0 N z (Lng N - 1)\<close>, which the row-1 ancestor
  structure forces (the interior row-1 node \<open>z\<close> with \<open>parent N 1 z > j\<^sub>0\<close> sits on
  the row-0 ramp to the endpoint).  Cites only @{thm [source] reach_from_z_tail},
  @{thm [source] m_6_7_tree_wellformed}; no spsy / sblk / via_spsy / RedCond /
  oper / tail_affine.\<close>

lemma m_6_7_tree_wellformed_via_z:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and hp1: "hasParent N 1 (Lng N - 1)"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and zlo: "parent N 1 (Lng N - 1) < z"
    and zhi: "z < Lng N - 1"
    and hpz: "hasParent N 1 z"
    and pge: "parent N 1 z \<ge> parent N 1 (Lng N - 1)"
    and pgt: "parent N 1 z > parent N 1 (Lng N - 1)"
    and zj1: "le0 N z (Lng N - 1)"
  shows "hasParent N 1 (parent N 1 z)
         \<and> parent N 1 (parent N 1 z) \<ge> parent N 1 (Lng N - 1)"
proof -
  have reach: "le0 N (parent N 1 z) (Lng N - 1)"
    by (rule reach_from_z_tail[OF hpz zj1])
  show ?thesis
    by (rule m_6_7_tree_wellformed[OF L hp1 j0lt zlo zhi hpz pge pgt reach])
qed


text \<open>§6.7 INTERIOR-NODE reach \<open>le0 N z j\<^sub>1\<close> FROM THE \<open>z\<close>-ENDPOINT slope-1 fact
  (attempt X).  The single residual reach \<open>le0 N z (Lng N - 1)\<close> consumed by
  @{thm [source] m_6_7_tree_wellformed_via_z} follows from the \<open>z\<close>-anchored
  endpoint equation \<open>E\<^sub>z : entry N 0 j\<^sub>1 = entry N 0 z + (j\<^sub>1 - z)\<close> (the total
  row-0 rise over \<open>[z, j\<^sub>1]\<close> equals the width).  The already-GREEN arithmetic glue
  @{thm [source] subramp_from_Ep} (instantiated with base \<open>z\<close>) upgrades \<open>E\<^sub>z\<close> +
  the per-step \<open>\<le> +1\<close> cap to the exact \<open>+1\<close> sub-ramp on \<open>[z, j\<^sub>1)\<close>; that
  per-step strict increase chains (@{thm [source] tailReach_from_row0_strict}) to
  \<open>le0 N z j\<^sub>1\<close>.  EMPIRICALLY \<open>E\<^sub>z\<close> holds 0-fail (1117/0) on the broad ST_PS
  closure for interior \<open>z\<close> with \<open>parent N 1 z > j\<^sub>0\<close>.  Cites only
  @{thm [source] subramp_from_Ep}, @{thm [source] tailReach_from_row0_strict};
  no spsy / sblk / via_spsy / RedCond / oper / tail_affine.\<close>

lemma le0_z_j1_from_Ez:
  fixes N :: pairseq
  assumes N: "N \<in> ST_PS"
    and zj1lt: "z < Lng N - 1"
    and Ez: "entry N 0 (Lng N - 1) = entry N 0 z + ((Lng N - 1) - z)"
  shows "le0 N z (Lng N - 1)"
proof -
  let ?j1 = "Lng N - 1"
  have j1L: "?j1 < Lng N" using zj1lt by linarith
  \<comment> \<open>the exact \<open>+1\<close> sub-ramp on \<open>[z, j\<^sub>1)\<close> from the endpoint fact\<close>
  have ramp: "\<And>x. z \<le> x \<Longrightarrow> x < ?j1 \<Longrightarrow> entry N 0 (Suc x) = Suc (entry N 0 x)"
    by (rule subramp_from_Ep[OF N zj1lt Ez])
  \<comment> \<open>read off the strict consecutive increase on \<open>[z, j\<^sub>1)\<close>\<close>
  have strict: "\<And>y. z \<le> y \<Longrightarrow> y < ?j1 \<Longrightarrow> entry N 0 y < entry N 0 (Suc y)"
  proof -
    fix y assume yz: "z \<le> y" and yj1: "y < ?j1"
    have "entry N 0 (Suc y) = Suc (entry N 0 y)" by (rule ramp[OF yz yj1])
    thus "entry N 0 y < entry N 0 (Suc y)" by simp
  qed
  \<comment> \<open>chain the strict increase to the endpoint\<close>
  show ?thesis
    by (rule tailReach_from_row0_strict[OF j1L strict le_refl zj1lt])
qed


text \<open>§6.7 RESIDUAL 1 (tree) via the \<open>z\<close>-ENDPOINT slope-1 fact \<open>E\<^sub>z\<close>
  (attempt X) --- the cleanest assembly.  Combines @{thm [source] le0_z_j1_from_Ez}
  (\<open>E\<^sub>z \<Longrightarrow> le0 N z j\<^sub>1\<close>) with @{thm [source] m_6_7_tree_wellformed_via_z}
  (\<open>le0 N z j\<^sub>1 \<Longrightarrow> tree\<close>, the parent edge supplies \<open>p \<rightarrow>\<^sup>* z\<close>).  The ENTIRE
  §6.7 RESIDUAL 1 (tree) now hangs on the lone SCALAR endpoint equation
  \<open>entry N 0 (Lng N - 1) = entry N 0 z + ((Lng N - 1) - z)\<close> at the interior row-1
  node \<open>z\<close> (EMPIRICALLY 1117/0).  Cites only @{thm [source] le0_z_j1_from_Ez},
  @{thm [source] m_6_7_tree_wellformed_via_z}; no spsy / sblk / via_spsy /
  RedCond / oper / tail_affine.\<close>

lemma m_6_7_tree_wellformed_via_Ez:
  fixes N :: pairseq
  assumes N: "N \<in> ST_PS"
    and L: "1 < Lng N"
    and hp1: "hasParent N 1 (Lng N - 1)"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and zlo: "parent N 1 (Lng N - 1) < z"
    and zhi: "z < Lng N - 1"
    and hpz: "hasParent N 1 z"
    and pge: "parent N 1 z \<ge> parent N 1 (Lng N - 1)"
    and pgt: "parent N 1 z > parent N 1 (Lng N - 1)"
    and Ez: "entry N 0 (Lng N - 1) = entry N 0 z + ((Lng N - 1) - z)"
  shows "hasParent N 1 (parent N 1 z)
         \<and> parent N 1 (parent N 1 z) \<ge> parent N 1 (Lng N - 1)"
proof -
  have zj1: "le0 N z (Lng N - 1)"
    by (rule le0_z_j1_from_Ez[OF N zhi Ez])
  show ?thesis
    by (rule m_6_7_tree_wellformed_via_z[OF L hp1 j0lt zlo zhi hpz pge pgt zj1])
qed

end
