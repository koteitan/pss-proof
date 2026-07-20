theory Frontier_6_030
  imports Support_6_012
begin

text \<open>§6.8 (a): the LOW SOURCE seg-shift identity (d0pos, \<open>i\<^sub>1=1\<close>).  A slice of
  \<open>M[n]\<close> that lies entirely INSIDE one period-block \<open>q\<close> (from block-offset \<open>s\<^sub>0\<close> to
  block-offset \<open>e\<^sub>0\<close>, \<open>s\<^sub>0 \<le> e\<^sub>0 < w\<close>) is exactly the corresponding slice of the base
  \<open>M\<close> (from \<open>j\<^sub>0+s\<^sub>0\<close> to \<open>j\<^sub>0+e\<^sub>0\<close>) with every row-0 entry shifted up by \<open>q\<cdot>\<delta>\<close>, i.e.
  \<open>(IncrFirst^^(q\<cdot>\<delta>))\<close> applied.  This is the article's LOW source decomposition:
  in the §6.8 closure the base is \<open>N\<close> (\<open>M = N[n]\<close>), \<open>j\<^sub>0 = j\<^sub>-\<^sub>2\<^sup>N\<close>, the slice
  starts at \<open>j'\<^sub>0 = j\<^sub>0+q\<cdot>w+s\<^sub>0\<close> and ends at \<open>fnM-1 = j\<^sub>0+q\<cdot>w+e\<^sub>0\<close> (the LOW part stays
  in one block, empirically 2132/2132, python/notbrle_low_check.py).
  Proof: nth-equality; each element reads off via @{thm [source] oper_d1pos_nth}
  (LHS) and @{thm [source] entry_funpow_IncrFirst0}/@{thm [source] entry_funpow_IncrFirst1}
  (RHS).  Empirically (a) holds 2132/2132 (same script, rank-stratified std gen).\<close>

lemma oper_d1pos_LOW_source_eq:
  fixes M :: pairseq
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and q: "q < n"
    and s0e0: "s0 \<le> e0"
    and e0lt: "e0 < Lng M - 1 - parent M 1 (Lng M - 1)"
  shows "seg (M[n])
              (parent M 1 (Lng M - 1) + q * (Lng M - 1 - parent M 1 (Lng M - 1)) + s0)
              (parent M 1 (Lng M - 1) + q * (Lng M - 1 - parent M 1 (Lng M - 1)) + e0)
       = (IncrFirst ^^ (q * (entry M 0 (Lng M - 1) - entry M 0 (parent M 1 (Lng M - 1)))))
            (seg M (parent M 1 (Lng M - 1) + s0) (parent M 1 (Lng M - 1) + e0))"
proof (rule nth_equalityI)
  let ?j1 = "Lng M - 1"  let ?j0 = "parent M 1 ?j1"  let ?w = "?j1 - ?j0"
  let ?delta = "entry M 0 ?j1 - entry M 0 ?j0"
  let ?sh = "q * ?delta"
  let ?lo = "?j0 + q * ?w + s0"  let ?hi = "?j0 + q * ?w + e0"
  let ?L = "seg (M[n]) ?lo ?hi"
  let ?R = "(IncrFirst ^^ ?sh) (seg M (?j0 + s0) (?j0 + e0))"
  \<comment> \<open>both slices have the same length \<open>e\<^sub>0 - s\<^sub>0 + 1\<close>\<close>
  have lenseg: "Suc (?j0 + e0) - (?j0 + s0) = Suc e0 - s0" using s0e0 by simp
  show lenEq: "length ?L = length ?R"
    using lenseg by (simp)
  fix i assume "i < length ?L"
  hence ic: "i < Suc e0 - s0" by simp
  hence ie: "s0 + i \<le> e0" using s0e0 by linarith
  have ielt: "s0 + i < ?w" using ie e0lt by linarith
  \<comment> \<open>LHS element: oper block-read at block \<open>q\<close>, offset \<open>s\<^sub>0+i\<close>\<close>
  have lhs_idx: "?lo + i = ?j0 + q * ?w + (s0 + i)" by simp
  have "?L ! i = (M[n]) ! (?lo + i)" using ic by (simp add: seg_nth_eq)
  also have "\<dots> = (M[n]) ! (?j0 + q * ?w + (s0 + i))" by (simp add: add.assoc)
  also have "\<dots> = (entry M 0 (?j0 + (s0 + i)) + q * ?delta, entry M 1 (?j0 + (s0 + i)))"
    by (rule oper_d1pos_nth[OF L notzero hp i1z j0lt q ielt])
  finally have LHS: "?L ! i = (entry M 0 (?j0 + (s0 + i)) + ?sh, entry M 1 (?j0 + (s0 + i)))" .
  \<comment> \<open>RHS element: base slice node \<open>j\<^sub>0+s\<^sub>0+i\<close> with row 0 shifted by \<open>?sh\<close>, row 1 unchanged\<close>
  have rseg_idx: "i < Suc (?j0 + e0) - (?j0 + s0)" using ic lenseg by linarith
  have segidxN: "?j0 + s0 + i < Lng M"
    using ielt j0lt by (simp add: add.assoc)
  have R0: "entry ?R 0 i = entry (seg M (?j0 + s0) (?j0 + e0)) 0 i + ?sh"
  proof -
    have ii: "i < Lng (seg M (?j0 + s0) (?j0 + e0))" using rseg_idx by simp
    show ?thesis by (rule entry_funpow_IncrFirst0[OF ii])
  qed
  have R1: "entry ?R 1 i = entry (seg M (?j0 + s0) (?j0 + e0)) 1 i"
  proof -
    have ii: "i < Lng (seg M (?j0 + s0) (?j0 + e0))" using rseg_idx by simp
    show ?thesis by (rule entry_funpow_IncrFirst1[OF ii])
  qed
  have segN0: "entry (seg M (?j0 + s0) (?j0 + e0)) 0 i = entry M 0 (?j0 + (s0 + i))"
  proof -
    have "seg M (?j0 + s0) (?j0 + e0) ! i = M ! (?j0 + s0 + i)"
      using rseg_idx by (rule seg_nth_eq)
    thus ?thesis by (simp add: entry_def add.assoc)
  qed
  have segN1: "entry (seg M (?j0 + s0) (?j0 + e0)) 1 i = entry M 1 (?j0 + (s0 + i))"
  proof -
    have "seg M (?j0 + s0) (?j0 + e0) ! i = M ! (?j0 + s0 + i)"
      using rseg_idx by (rule seg_nth_eq)
    thus ?thesis by (simp add: entry_def add.assoc)
  qed
  have ilenR: "i < length ?R" using lenEq \<open>i < length ?L\<close> by simp
  have "?R ! i = (entry ?R 0 i, entry ?R 1 i)"
    using ilenR by (cases "?R ! i") (simp add: entry_def)
  also have "\<dots> = (entry M 0 (?j0 + (s0 + i)) + ?sh, entry M 1 (?j0 + (s0 + i)))"
    using R0 R1 segN0 segN1 by simp
  finally have RHS: "?R ! i = (entry M 0 (?j0 + (s0 + i)) + ?sh, entry M 1 (?j0 + (s0 + i)))" .
  show "?L ! i = ?R ! i" using LHS RHS by simp
qed

text \<open>Periodicity in index form: inside block \<open>q < n\<close> at offset \<open>s\<close>, \<open>M[n]\<close> reads
  off \<open>M\<close> at \<open>j\<^sub>0 + s\<close>.\<close>

lemma oper_d0zero_nth:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 0"
    and j0lt: "parent M 0 (Lng M - 1) < Lng M - 1"
    and q: "q < n"
    and s: "s < Lng M - 1 - parent M 0 (Lng M - 1)"
  shows "(M[n]) ! (parent M 0 (Lng M - 1)
                   + q * (Lng M - 1 - parent M 0 (Lng M - 1)) + s)
       = M ! (parent M 0 (Lng M - 1) + s)"
proof -
  let ?j1 = "Lng M - 1"  let ?j0 = "parent M 0 ?j1"  let ?w = "?j1 - ?j0"
  let ?B = "map ((!) M) [?j0..<?j1]"
  have lenB: "length ?B = ?w" by simp
  have j0le: "?j0 \<le> Lng M" using j0lt by linarith
  have lentake: "length (take ?j0 M) = ?j0" using j0le by simp
  have idxge: "?j0 \<le> ?j0 + q * ?w + s" by simp
  have expand: "M[n] = take ?j0 M @ concat (replicate n ?B)"
    using oper_d0zero_expand[OF L notzero hp i1z] by simp
  have "(M[n]) ! (?j0 + q * ?w + s) = concat (replicate n ?B) ! (q * ?w + s)"
    using expand lentake idxge by (simp add: nth_append)
  also have "\<dots> = ?B ! s"
    using nth_concat_replicate[OF _ q, of s ?B] s lenB by simp
  also have "\<dots> = M ! (?j0 + s)"
    using s by (simp add: nth_upt)
  finally show ?thesis .
qed

text \<open>Row-0 value at an index \<open>x \<ge> j\<^sub>0\<close> of the \<open>i\<^sub>1=0\<close> oper: it equals \<open>M\<close>'s
  row-0 value at \<open>j\<^sub>0 + (x-j\<^sub>0) mod w\<close> (the offset within \<open>x\<close>'s block).\<close>

lemma oper_d0zero_entry0:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 0"
    and j0lt: "parent M 0 (Lng M - 1) < Lng M - 1"
    and x0: "parent M 0 (Lng M - 1) \<le> x"
    and xlt: "x < parent M 0 (Lng M - 1) + n * (Lng M - 1 - parent M 0 (Lng M - 1))"
  shows "entry (M[n]) 0 x
       = entry M 0 (parent M 0 (Lng M - 1) + (x - parent M 0 (Lng M - 1)) mod (Lng M - 1 - parent M 0 (Lng M - 1)))"
proof -
  let ?j0 = "parent M 0 (Lng M - 1)"  let ?w = "Lng M - 1 - ?j0"
  have w0: "0 < ?w" using j0lt by linarith
  let ?q = "(x - ?j0) div ?w"  let ?s = "(x - ?j0) mod ?w"
  have sw: "?s < ?w" using w0 by simp
  have xmj: "x - ?j0 < n * ?w" using xlt x0 by linarith
  have qn: "?q < n" using less_mult_imp_div_less[OF xmj] .
  have dm: "?q * ?w + ?s = x - ?j0"
    using div_mult_mod_eq[of "x - ?j0" ?w] by (simp add: mult.commute)
  have xsplit: "x = ?j0 + ?q * ?w + ?s" using dm x0 by linarith
  have "(M[n]) ! x = (M[n]) ! (?j0 + ?q * ?w + ?s)" using xsplit by simp
  also have "\<dots> = M ! (?j0 + ?s)"
    by (rule oper_d0zero_nth[OF L notzero hp i1z j0lt qn sw])
  finally have "(M[n]) ! x = M ! (?j0 + ?s)" .
  thus ?thesis by (simp add: entry_def)
qed

text \<open>In a standard parent step \<open>(0,j\<^sub>0) <\<^sup>Next (0,j\<^sub>1)\<close>, \<open>j\<^sub>0\<close> is the row-0 minimum
  of the closed block \<open>[j\<^sub>0, j\<^sub>1)\<close>: strictly below every interior index.\<close>

lemma parent_block_entry0_min:
  assumes parR: "nextrel0 M (parent M 0 (Lng M - 1)) (Lng M - 1)"
    and s: "s < Lng M - 1 - parent M 0 (Lng M - 1)"
  shows "entry M 0 (parent M 0 (Lng M - 1)) \<le> entry M 0 (parent M 0 (Lng M - 1) + s)"
    and "0 < s \<Longrightarrow> entry M 0 (parent M 0 (Lng M - 1)) < entry M 0 (parent M 0 (Lng M - 1) + s)"
proof -
  let ?j0 = "parent M 0 (Lng M - 1)"
  have lt01: "entry M 0 ?j0 < entry M 0 (Lng M - 1)"
    using parR by (simp add: nextrel0_def)
  show "0 < s \<Longrightarrow> entry M 0 ?j0 < entry M 0 (?j0 + s)"
  proof -
    assume sp: "0 < s"
    have between: "?j0 < ?j0 + s \<and> ?j0 + s < Lng M - 1" using sp s by linarith
    hence "entry M 0 (Lng M - 1) \<le> entry M 0 (?j0 + s)"
      using parR by (simp add: nextrel0_def)
    thus "entry M 0 ?j0 < entry M 0 (?j0 + s)" using lt01 by linarith
  qed
  thus "entry M 0 ?j0 \<le> entry M 0 (?j0 + s)" by (cases "0 < s") auto
qed

text \<open>Block ancestry: in the standard parent step \<open>(0,j\<^sub>0) <\<^sup>Next (0,Lng M-1)\<close>, the
  block start \<open>j\<^sub>0\<close> is the row-0 ancestor (\<open>\<le>\<^sub>0\<close>) of every index in the open block
  \<open>[j\<^sub>0, Lng M-1)\<close>.  Proof: strong induction on the offset \<open>s\<close>; for \<open>s>0\<close> pick the
  immediate row-0 predecessor \<open>p\<close> of \<open>x = j\<^sub>0+s\<close>, which lies in \<open>[j\<^sub>0, x)\<close> because
  \<open>j\<^sub>0\<close> itself has strictly smaller row-0 (\<open>parent_block_entry0_min\<close>), so \<open>p = j\<^sub>0+s'\<close>
  with \<open>s'<s\<close> and \<open>nextrel0 M p x\<close>; chain by IH + \<open>le0_trans\<close>.\<close>

lemma parent_block_le0:
  assumes parR: "nextrel0 M (parent M 0 (Lng M - 1)) (Lng M - 1)"
    and s: "s < Lng M - 1 - parent M 0 (Lng M - 1)"
  shows "le0 M (parent M 0 (Lng M - 1)) (parent M 0 (Lng M - 1) + s)"
proof -
  let ?j0 = "parent M 0 (Lng M - 1)"
  have j0lt: "?j0 < Lng M - 1" using parR by (simp add: nextrel0_def)
  have Lpos: "0 < Lng M" using j0lt by linarith
  have key: "t < Lng M - 1 - ?j0 \<Longrightarrow> le0 M ?j0 (?j0 + t)" for t
  proof (induct t rule: less_induct)
    case (less t)
    note IH = less.hyps
    show ?case
    proof -
      have tw: "t < Lng M - 1 - ?j0" using less.prems .
      let ?x = "?j0 + t"
      have xlt: "?x < Lng M" using tw j0lt by linarith
      have j0ltM: "?j0 < Lng M" using j0lt by linarith
      show "le0 M ?j0 ?x"
      proof (cases "t = 0")
        case True thus ?thesis using le0_refl[OF j0ltM] by simp
      next
        case False
        hence t0: "0 < t" by simp
        \<comment> \<open>\<open>j\<^sub>0\<close> has strictly smaller row-0 than \<open>x\<close>, so the set of strict-row-0
           predecessors of \<open>x\<close> within \<open>[j\<^sub>0, x)\<close> is non-empty; take its maximum \<open>p\<close>.\<close>
        have j0x: "entry M 0 ?j0 < entry M 0 ?x"
          using parent_block_entry0_min(2)[OF parR tw] t0 by simp
        define S where "S = {p. ?j0 \<le> p \<and> p < ?x \<and> entry M 0 p < entry M 0 ?x}"
        have j0S: "?j0 \<in> S" using j0x t0 unfolding S_def by simp
        have Sfin: "finite S" unfolding S_def by simp
        have Sne: "S \<noteq> {}" using j0S by blast
        define p where "p = Max S"
        have pS: "p \<in> S" unfolding p_def using Sfin Sne by (rule Max_in)
        have pmax: "\<And>q. q \<in> S \<Longrightarrow> q \<le> p" unfolding p_def using Sfin by (rule Max_ge)
        from pS have pge: "?j0 \<le> p" and plt: "p < ?x"
          and prow: "entry M 0 p < entry M 0 ?x" unfolding S_def by auto
        \<comment> \<open>between \<open>p\<close> and \<open>x\<close> every row-0 is \<open>\<ge> entry M 0 x\<close> (else a bigger member of \<open>S\<close>)\<close>
        have pnext: "nextrel0 M p ?x"
        proof -
          have "\<forall>j. p < j \<and> j < ?x \<longrightarrow> entry M 0 j \<ge> entry M 0 ?x"
          proof (intro allI impI)
            fix j assume j: "p < j \<and> j < ?x"
            show "entry M 0 j \<ge> entry M 0 ?x"
            proof (rule ccontr)
              assume "\<not> entry M 0 j \<ge> entry M 0 ?x"
              hence jrow: "entry M 0 j < entry M 0 ?x" by simp
              have "?j0 \<le> j" using j pge by linarith
              hence "j \<in> S" using j jrow unfolding S_def by simp
              hence "j \<le> p" using pmax by simp
              thus False using j by simp
            qed
          qed
          moreover have "p < Lng M" using plt xlt by linarith
          ultimately show ?thesis using plt xlt prow
            unfolding nextrel0_def by blast
        qed
        have pstep: "le0 M p ?x"
        proof -
          have "p < Lng M" using plt xlt by linarith
          thus ?thesis using pnext xlt by (auto simp: le0_def intro: r_into_rtranclp)
        qed
        show ?thesis
        proof (cases "p = ?j0")
          case True thus ?thesis using pstep by simp
        next
          case False
          hence pgt: "?j0 < p" using pge by simp
          define s' where "s' = p - ?j0"
          have ps': "p = ?j0 + s'" unfolding s'_def using pge by simp
          have s'lt: "s' < t" unfolding s'_def using plt pge by linarith
          have s'w: "s' < Lng M - 1 - ?j0" using s'lt tw by linarith
          have lej0p: "le0 M ?j0 p" using IH[OF s'lt s'w] ps' by simp
          show ?thesis using le0_trans[OF lej0p pstep] by simp
        qed
      qed
    qed
  qed
  show ?thesis using key[OF s] .
qed

text \<open>Above the row-0 parent \<open>j\<^sub>0\<close> of the trunk leaf \<open>b = Lng N - 1\<close> there is no
  proper row-0 ancestor of \<open>b\<close>: \<open>j\<^sub>0\<close> is the nearest strict-row-0 predecessor of
  \<open>b\<close> (\<open>nextrel0 N j\<^sub>0 b\<close>), so every interior index \<open>k \<in> (j\<^sub>0, b)\<close> has row-0
  \<open>\<ge> N\<^bsub>0,b\<^esub>\<close>; a reachability chain into \<open>b\<close> would need a final strict-row-0
  increase, which no such \<open>k\<close> provides.  Hence any \<open>x > j\<^sub>0\<close> with
  \<open>(nextrel0 N)\<^sup>*\<^sup>* x b\<close> must already equal \<open>b\<close>.  This pins
  \<open>Pcut (seg N a b) = b - a\<close> in §6.8 d0zero case-A, where the slice starts
  strictly above \<open>j\<^sub>0\<close>.\<close>

lemma nextrel0_above_parent_trivial:
  assumes par: "nextrel0 N j0 b"
    and chain: "(nextrel0 N)\<^sup>*\<^sup>* x b"
    and xgt: "j0 < x"
  shows "x = b"
proof -
  have barrier: "\<And>k. j0 < k \<Longrightarrow> k < b \<Longrightarrow> entry N 0 b \<le> entry N 0 k"
    using par by (simp add: nextrel0_def)
  have "(nextrel0 N)\<^sup>*\<^sup>* x b \<Longrightarrow> j0 < x \<longrightarrow> x = b"
  proof (induction rule: converse_rtranclp_induct)
    case base show ?case by simp
  next
    case (step y z)
    note nyz = step.hyps(1) and IH = step.IH
    show ?case
    proof
      assume yj0: "j0 < y"
      have yz: "y < z" using nyz by (simp add: nextrel0_def)
      hence j0z: "j0 < z" using yj0 by linarith
      have zb: "z = b" using IH j0z by simp
      have "entry N 0 y < entry N 0 b" using nyz zb by (simp add: nextrel0_def)
      moreover have "y < b" using yz zb by simp
      ultimately have False using barrier[OF yj0] by linarith
      thus "y = b" by simp
    qed
  qed
  thus ?thesis using chain xgt by simp
qed

text \<open>Confinement (article 1510): in the \<open>i\<^sub>1=0\<close> periodic layout each block-start
  carries the row-0 minimum \<open>M\<^bsub>0,j\<^sub>0\<^esub>\<close>, which acts as a barrier — a row-0
  reachability chain starting at \<open>a \<ge> j\<^sub>0\<close> cannot cross into a later block, so
  its target stays below the end of \<open>a\<close>'s block.\<close>

lemma oper_d0zero_le0_confined:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 0"
    and a0: "parent M 0 (Lng M - 1) \<le> a"
    and alt: "a < Lng ((M::pairseq)[n])"
    and ab: "(nextrel0 ((M::pairseq)[n]))\<^sup>*\<^sup>* a b"
  shows "b < parent M 0 (Lng M - 1)
           + ((a - parent M 0 (Lng M - 1)) div (Lng M - 1 - parent M 0 (Lng M - 1)) + 1)
             * (Lng M - 1 - parent M 0 (Lng M - 1))"
proof -
  let ?j0 = "parent M 0 (Lng M - 1)"  let ?w = "Lng M - 1 - ?j0"
  let ?q = "(a - ?j0) div ?w"
  have hp0: "hasParent M 0 (Lng M - 1)" using hp i1z by simp
  have parR: "nextR M 0 ?j0 (Lng M - 1)"
    using hp0 unfolding hasParent_def parent_def by (rule theI')
  have parR0: "nextrel0 M ?j0 (Lng M - 1)" using parR by (simp add: nextR_def)
  have j0lt: "?j0 < Lng M - 1" using poper_nextR_imp_le0[OF parR] by simp
  have w0: "0 < ?w" using j0lt by linarith
  have lenM: "Lng ((M::pairseq)[n]) = ?j0 + n * ?w"
  proof -
    have e: "M[n] = take ?j0 M @ concat (replicate n (map ((!) M) [?j0..<Lng M - 1]))"
      by (rule oper_d0zero_expand[OF L notzero hp i1z])
    have t: "length (take ?j0 M) = ?j0" using j0lt L by simp
    have b: "length (map ((!) M) [?j0..<Lng M - 1]) = ?w" by simp
    show ?thesis using e t b by (simp add: length_concat sum_list_replicate)
  qed
  have qn: "?q < n"
  proof -
    have "a - ?j0 < n * ?w" using alt lenM a0 by linarith
    thus ?thesis using less_mult_imp_div_less by simp
  qed
  \<comment> \<open>strengthened invariant along the reachability chain\<close>
  have main: "?j0 \<le> b \<and> b < ?j0 + (?q + 1) * ?w"
    using ab
  proof (induction rule: rtranclp_induct)
    case base
    have md: "a - ?j0 = ?q * ?w + (a - ?j0) mod ?w"
      using div_mult_mod_eq[of "a - ?j0" ?w] by (simp add: mult.commute)
    have "(a - ?j0) mod ?w < ?w" using w0 by simp
    hence "a - ?j0 < (?q + 1) * ?w" using md by (simp add: algebra_simps)
    thus ?case using a0 by linarith
  next
    case (step y z)
    from step.IH have Py: "?j0 \<le> y" and Pyb: "y < ?j0 + (?q + 1) * ?w" by auto
    have yz: "nextrel0 ((M::pairseq)[n]) y z" using step.hyps(2) .
    have ylt: "y < z" and zlt: "z < Lng ((M::pairseq)[n])"
      and vlt: "entry ((M::pairseq)[n]) 0 y < entry ((M::pairseq)[n]) 0 z"
      using yz by (auto simp: nextrel0_def)
    have ybar: "\<And>j. y < j \<Longrightarrow> j < z \<Longrightarrow> entry ((M::pairseq)[n]) 0 z \<le> entry ((M::pairseq)[n]) 0 j"
      using yz by (auto simp: nextrel0_def)
    show ?case
    proof (intro conjI)
      show "?j0 \<le> z" using Py ylt by linarith
      show "z < ?j0 + (?q + 1) * ?w"
      proof (rule ccontr)
        assume "\<not> z < ?j0 + (?q + 1) * ?w"
        hence zge: "?j0 + (?q + 1) * ?w \<le> z" by linarith
        let ?B = "?j0 + (?q + 1) * ?w"
        have q1n: "?q + 1 < n"
        proof -
          have "?j0 + (?q + 1) * ?w \<le> z" by (rule zge)
          also have "z < ?j0 + n * ?w" using zlt lenM by simp
          finally have "(?q + 1) * ?w < n * ?w" by simp
          thus ?thesis using w0 by (metis mult_less_cancel2)
        qed
        have Blt: "?B < Lng ((M::pairseq)[n])"
          using mult_less_mono1[OF q1n w0] lenM by simp
        \<comment> \<open>row-0 value at the block-start \<open>?B\<close> is the minimum \<open>M\<^bsub>0,j\<^sub>0\<^esub>\<close>\<close>
        have offB: "(?B - ?j0) mod ?w = 0" by simp
        have entryB: "entry ((M::pairseq)[n]) 0 ?B = entry M 0 ?j0"
          using oper_d0zero_entry0[OF L notzero hp i1z j0lt, of ?B n] offB
                Blt lenM by simp
        \<comment> \<open>row-0 value at any \<open>x\<in>[j\<^sub>0,Lng)\<close> is \<open>\<ge> M\<^bsub>0,j\<^sub>0\<^esub>\<close>, with \<open>=\<close> only at block-starts\<close>
        have ge_min: "\<And>x. ?j0 \<le> x \<Longrightarrow> x < Lng ((M::pairseq)[n]) \<Longrightarrow> entry M 0 ?j0 \<le> entry ((M::pairseq)[n]) 0 x"
        proof -
          fix x assume xx: "?j0 \<le> x" "x < Lng ((M::pairseq)[n])"
          have "(x - ?j0) mod ?w < ?w" using w0 by simp
          hence "entry M 0 ?j0 \<le> entry M 0 (?j0 + (x - ?j0) mod ?w)"
            using parent_block_entry0_min(1)[OF parR0] by blast
          thus "entry M 0 ?j0 \<le> entry ((M::pairseq)[n]) 0 x"
            using oper_d0zero_entry0[OF L notzero hp i1z j0lt, of x n] xx lenM by simp
        qed
        have eq_min_imp: "\<And>x. ?j0 \<le> x \<Longrightarrow> x < Lng ((M::pairseq)[n]) \<Longrightarrow>
              entry ((M::pairseq)[n]) 0 x = entry M 0 ?j0 \<Longrightarrow> (x - ?j0) mod ?w = 0"
        proof -
          fix x assume xx: "?j0 \<le> x" "x < Lng ((M::pairseq)[n])"
            and xeq: "entry ((M::pairseq)[n]) 0 x = entry M 0 ?j0"
          have xval: "entry ((M::pairseq)[n]) 0 x = entry M 0 (?j0 + (x - ?j0) mod ?w)"
            using oper_d0zero_entry0[OF L notzero hp i1z j0lt, of x n] xx lenM by simp
          show "(x - ?j0) mod ?w = 0"
          proof (rule ccontr)
            assume "(x - ?j0) mod ?w \<noteq> 0"
            hence sp: "0 < (x - ?j0) mod ?w" by simp
            have "(x - ?j0) mod ?w < ?w" using w0 by simp
            hence "entry M 0 ?j0 < entry M 0 (?j0 + (x - ?j0) mod ?w)"
              using parent_block_entry0_min(2)[OF parR0] sp by blast
            thus False using xval xeq by simp
          qed
        qed
        \<comment> \<open>case on whether \<open>?B\<close> equals \<open>z\<close> or lies strictly inside \<open>(y,z)\<close>\<close>
        have yB: "y < ?B" using Pyb by simp
        show False
        proof (cases "?B = z")
          case True
          have "entry ((M::pairseq)[n]) 0 y < entry M 0 ?j0" using vlt entryB True by simp
          moreover have "entry M 0 ?j0 \<le> entry ((M::pairseq)[n]) 0 y"
            using ge_min[of y] Py ylt zlt by linarith
          ultimately show False by simp
        next
          case False
          hence Bin: "y < ?B \<and> ?B < z" using yB zge by linarith
          have "entry ((M::pairseq)[n]) 0 z \<le> entry ((M::pairseq)[n]) 0 ?B" using ybar Bin by simp
          hence zle: "entry ((M::pairseq)[n]) 0 z \<le> entry M 0 ?j0" using entryB by simp
          have zge_min: "entry M 0 ?j0 \<le> entry ((M::pairseq)[n]) 0 z"
            using ge_min[of z] Py ylt zlt by linarith
          have zeq: "entry ((M::pairseq)[n]) 0 z = entry M 0 ?j0" using zle zge_min by simp
          \<comment> \<open>then \<open>z\<close> is a block-start, so \<open>M\<^bsub>0,y\<^esub> < M\<^bsub>0,j\<^sub>0\<^esub>\<close> — impossible for \<open>y \<ge> j\<^sub>0\<close>\<close>
          have "entry ((M::pairseq)[n]) 0 y < entry M 0 ?j0" using vlt zeq by simp
          moreover have "entry M 0 ?j0 \<le> entry ((M::pairseq)[n]) 0 y"
            using ge_min[of y] Py ylt zlt by linarith
          ultimately show False by simp
        qed
      qed
    qed
  qed
  show ?thesis using main by simp
qed

text \<open>Row-0 is weakly monotone along a \<open>nextrel0\<close>-reachability chain: every step
  requires a strict row-0 increase (\<open>nextrel0_def\<close>), so the reflexive-transitive
  closure gives \<open>entry M 0 a \<le> entry M 0 b\<close>.  (Used by the §6.8 d0pos confinement,
  which — unlike d0zero — cannot confine the chain to a single block.)\<close>

lemma nextrel0_rtrancl_entry0_mono:
  assumes "(nextrel0 M)\<^sup>*\<^sup>* a b"
  shows "entry M 0 a \<le> entry M 0 b"
  using assms by (induction rule: rtranclp_induct) (auto simp: nextrel0_def)

end
