theory Frontier_7_048
  imports Support_7_041
begin

section \<open>§7.2 BT fundamental sequence on successor-form terms (conjuncts (1),(1-2))\<close>

text \<open>\<open>endsD00 a\<close>: the last principal component of \<open>a\<close> is \<open>D\<^sub>0 0\<close>.  Then
  \<open>domB a = {0}\<close> (\<open>domB\<close> reads only the last component, @{thm [source]
  domB_last_component}).\<close>

definition endsD00 :: "BT \<Rightarrow> bool" where
  "endsD00 a \<longleftrightarrow> (case a of Trm xs \<Rightarrow> xs \<noteq> [] \<and> last xs = DB 0 (Trm []))"

lemma endsD00_addD00: "endsD00 (t' +\<^sub>B Dpt 0 0\<^sub>B)"
  by (cases t') (simp add: endsD00_def)

lemma domB_endsD00:
  assumes "endsD00 a" shows "domB a = {Trm []}"
proof -
  obtain xs where a: "a = Trm xs" by (cases a)
  have ne: "xs \<noteq> []" and lst: "last xs = DB 0 (Trm [])"
    using assms a by (auto simp: endsD00_def)
  have "domB a = domB (Trm [last xs])"
    unfolding a by (rule domB_last_component[OF ne])
  also have "\<dots> = domB (Trm [DB 0 (Trm [])])" using lst by simp
  also have "\<dots> = {Trm []}" by (subst domB_unfold) simp
  finally show ?thesis .
qed

text \<open>\<open>d0succ a\<close>: the structural class on which the \<open>operB \<dash> z\<close> recursion only
  ever hits the SIMPLE \<open>db = {0}\<close> branch (so its domain holds, independently of
  the deferred [Buc1] Lemma 3.2 / general \<open>operB\<close> totality).\<close>

text \<open>\<open>d0succ\<close> via a \<^typ>\<open>BP\<close>-recursive helper on the LAST principal: this reads
  only the last component (computed once, not in the recursion), and recurses
  structurally into the principal body \<open>b\<close> of \<open>D\<^sub>v b\<close> — so termination is the
  built-in structural measure (no \<open>last\<close> in the recursion).\<close>

lemma size_last_lt_BP:
  "ys \<noteq> [] \<Longrightarrow> size (last ys) < Suc (Suc (size_list size ys))"
proof (induction ys)
  case Nil thus ?case by simp
next
  case (Cons a as)
  show ?case
  proof (cases as)
    case Nil thus ?thesis by simp
  next
    case (Cons b bs)
    have "last (a # as) \<in> set as" using Cons by simp
    hence "size (last (a # as)) \<le> size_list size as"
      by (induction as) auto
    thus ?thesis using Cons by simp
  qed
qed

function d0succ_BP :: "BP \<Rightarrow> bool" where
  "d0succ_BP (DB v b) =
     (if b = Trm [] then v = 0
      else endsD00 b \<and> (case b of Trm ys \<Rightarrow> ys \<noteq> [] \<and> d0succ_BP (last ys)))"
  by pat_completeness auto
termination
  by (relation "measure size") (auto simp: size_last_lt_BP)

definition d0succ :: "BT \<Rightarrow> bool" where
  "d0succ a = (case a of Trm xs \<Rightarrow> xs \<noteq> [] \<and> d0succ_BP (last xs))"

lemma d0succ_D00: "d0succ (Dpt 0 0\<^sub>B)"
  by (simp add: d0succ_def)

text \<open>\<open>d0succ\<close> on a single principal \<open>D\<^sub>v b\<close> with \<open>b\<close> a nonempty \<open>endsD00\<close>
  successor body that is itself \<open>d0succ\<close>.\<close>
lemma d0succ_single_nonzero:
  assumes "b \<noteq> Trm []" "endsD00 b" "d0succ b"
  shows "d0succ (Dpt v b)"
proof -
  obtain ys where ys: "b = Trm ys" by (cases b)
  have yne: "ys \<noteq> []" using assms(1) ys by auto
  have dB: "d0succ_BP (last ys)" using assms(3) ys by (simp add: d0succ_def)
  have "d0succ_BP (DB v b)"
    using assms(1,2) ys yne dB by simp
  thus ?thesis by (simp add: d0succ_def)
qed

text \<open>Any term whose last component is \<open>D\<^sub>0 0\<close> is \<open>d0succ\<close>.\<close>
lemma d0succ_last_D00:
  assumes "xs \<noteq> []" and "last xs = DB 0 (Trm [])"
  shows "d0succ (Trm xs)"
  using assms by (simp add: d0succ_def)

lemma d0succ_addD00: "d0succ (t' +\<^sub>B Dpt 0 0\<^sub>B)"
proof -
  obtain xs where x: "t' = Trm xs" by (cases t')
  have e: "t' +\<^sub>B Dpt 0 0\<^sub>B = Trm (xs @ [DB 0 (Trm [])])" using x by simp
  have ne: "xs @ [DB 0 (Trm [])] \<noteq> []" by simp
  have lst: "last (xs @ [DB 0 (Trm [])]) = DB 0 (Trm [])" by simp
  show ?thesis using e d0succ_last_D00[OF ne lst] by simp
qed

text \<open>\<open>operB \<dash> z\<close> is defined on every \<open>d0succ\<close> term: the only recursive
  \<open>operB\<close>/\<open>xseq\<close> calls reachable are the \<open>db = {0}\<close> single-branch
  \<open>operB b (Trm [])\<close> (\<open>b\<close> again \<open>d0succ\<close>) and the multi-branch
  \<open>operB (Trm [last \<dots>]) z\<close>; the \<open>domB b\<close> call is total
  (@{thm [source] domB_dom_all}), and the \<open>xseq\<close>/\<open>else\<close> branches cannot fire
  because \<open>domB b = {0}\<close> on a \<open>d0succ\<close> body.\<close>

lemma operB_dom_d0succ:
  "d0succ a \<Longrightarrow> domB_operB_xseq_dom (Inr (Inl (a, z)))"
proof (induction a arbitrary: z rule: measure_induct_rule[where f=size])
  case (less a z)
  \<comment> \<open>from \<open>a = Trm [DB v b]\<close>, \<open>b \<noteq> 0\<close> and \<open>d0succ a\<close> we get \<open>endsD00 b\<close>,
     \<open>d0succ b\<close>, hence \<open>domB b = {0}\<close> (so the \<open>xseq\<close>/\<open>else\<close> guards are false)\<close>
  have single: "endsD00 x2 \<and> d0succ x2 \<and> domB x2 = {Trm []}"
    if "a = Trm [DB x1 x2]" "x2 \<noteq> Trm []" for x1 x2
  proof -
    have d0: "d0succ (Trm [DB x1 x2])" using less.prems that(1) by simp
    have bp: "d0succ_BP (DB x1 x2)" using d0 by (simp add: d0succ_def)
    have e: "endsD00 x2" using bp that(2) by (simp split: if_splits)
    obtain ys where ys: "x2 = Trm ys" by (cases x2)
    have d: "d0succ x2"
      using bp that(2) ys by (auto simp: d0succ_def split: if_splits)
    show ?thesis using e d domB_endsD00[OF e] by simp
  qed
  \<comment> \<open>uniform discharge of every \<open>domintros(2)\<close> premise.  The recursive calls in
     \<open>operB\<close>'s body are: \<open>domB b\<close> (\<open>Inl b\<close>, total); the single-branch
     \<open>operB b (Trm [])\<close> under \<open>db = {0}\<close>; the \<open>xseq\<close>/\<open>else\<close> calls, all under the
     guard \<open>domB b \<noteq> {0}\<close> which is FALSE on a \<open>d0succ\<close> body; and the multi-branch
     \<open>operB (Trm [last \<dots>]) z\<close>.  Every premise carries the pattern \<open>a = Trm [DB v b]\<close>
     (resp.\ \<open>a = Trm (p#q#rest)\<close>) and \<open>b \<noteq> 0\<close>, from which @{thm [source] single}
     applies; the \<open>Inl\<close> (domB) premises hold by @{thm [source] domB_dom_all}.\<close>
  show ?case
  proof (rule domB_operB_xseq.domintros(2))
    \<comment> \<open>(0) \<open>domB b\<close> total (\<open>Inl\<close>)\<close>
    show "domB_operB_xseq_dom (Inl x2)"
      if "a = Trm [DB x1 x2]" "x2 \<noteq> Trm []" for x1 x2
      by (rule domB_dom_all)
  next
    \<comment> \<open>(1) single-branch \<open>operB b (Trm [])\<close> under \<open>db = {0}\<close>: reachable, IH\<close>
    show "domB_operB_xseq_dom (Inr (Inl (x2, Trm [])))"
      if "a = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "{Trm []} = domB x2" for x1 x2
    proof -
      have "size x2 < size a" using that(1) by simp
      thus ?thesis using less.IH single[OF that(1,2)] by blast
    qed
  next
    \<comment> \<open>(2) \<open>xseq\<close>-guard side condition: \<open>domB b = T\<^sub>u\<close> forces \<open>T\<^sub>u = {0}\<close> by
       @{thm [source] single}, so any \<open>xb \<in> T\<^sub>u\<close> is \<open>0\<close>\<close>
    show "xb = Trm []"
      if "a = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "x1 \<le> enat u"
         "domB x2 = TBv (enat u)"
         "\<not> domB_operB_xseq_dom
              (Inr (Inr (x2, enat (tbvIdx (TBv (enat u))), numNat z)))"
         "xb \<in> TBv (enat u)" for x1 x2 u xb
    proof -
      have "domB x2 = {Trm []}" using single[OF that(1,2)] by simp
      hence "TBv (enat u) = {Trm []}" using that(4) by simp
      thus ?thesis using that(6) by simp
    qed
  next
    \<comment> \<open>(3) \<open>0 \<in> T\<^sub>u\<close>: \<open>0 = Trm []\<close> has no principals, so it lies in every \<open>T\<^sub>u\<close>\<close>
    show "Trm [] \<in> TBv (enat u)"
      if "a = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "x1 \<le> enat u"
         "domB x2 = TBv (enat u)"
         "\<not> domB_operB_xseq_dom
              (Inr (Inr (x2, enat (tbvIdx (TBv (enat u))), numNat z)))"
         for x1 x2 u
      by (simp add: TBv_def)
  next
    \<comment> \<open>(4) inner \<open>operB b (xseq \<dots>)\<close> guard side condition, same collapse as (2)\<close>
    show "xb = Trm []"
      if "a = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "x1 \<le> enat u"
         "domB x2 = TBv (enat u)"
         "\<not> domB_operB_xseq_dom
              (Inr (Inl (x2, xseq x2 (enat (tbvIdx (TBv (enat u)))) (numNat z))))"
         "xb \<in> TBv (enat u)" for x1 x2 u xb
    proof -
      have "domB x2 = {Trm []}" using single[OF that(1,2)] by simp
      hence "TBv (enat u) = {Trm []}" using that(4) by simp
      thus ?thesis using that(6) by simp
    qed
  next
    \<comment> \<open>(5) \<open>0 \<in> T\<^sub>u\<close> again\<close>
    show "Trm [] \<in> TBv (enat u)"
      if "a = Trm [DB x1 x2]" "x2 \<noteq> Trm []" "x1 \<le> enat u"
         "domB x2 = TBv (enat u)"
         "\<not> domB_operB_xseq_dom
              (Inr (Inl (x2, xseq x2 (enat (tbvIdx (TBv (enat u)))) (numNat z))))"
         for x1 x2 u
      by (simp add: TBv_def)
  next
    \<comment> \<open>(6) \<open>else\<close>-guard side condition: \<open>domB b = {0}\<close>, so any \<open>xb \<in> domB b\<close> is \<open>0\<close>\<close>
    show "xb = Trm []"
      if "a = Trm [DB x1 x2]" "x2 \<noteq> Trm []"
         "\<forall>u. x1 \<le> enat u \<longrightarrow> domB x2 \<noteq> TBv (enat u)"
         "\<not> domB_operB_xseq_dom (Inr (Inl (x2, z)))"
         "xb \<in> domB x2" for x1 x2 xb
    proof -
      have "domB x2 = {Trm []}" using single[OF that(1,2)] by simp
      thus ?thesis using that(5) by simp
    qed
  next
    \<comment> \<open>(7) \<open>0 \<in> domB b\<close>: \<open>domB b = {0}\<close> by @{thm [source] single}\<close>
    show "Trm [] \<in> domB x2"
      if "a = Trm [DB x1 x2]" "x2 \<noteq> Trm []"
         "\<forall>u. x1 \<le> enat u \<longrightarrow> domB x2 \<noteq> TBv (enat u)"
         "\<not> domB_operB_xseq_dom (Inr (Inl (x2, z)))" for x1 x2
    proof -
      have "domB x2 = {Trm []}" using single[OF that(1,2)] by simp
      thus ?thesis by simp
    qed
  next
    \<comment> \<open>(8) two-component multi \<open>Trm [p, q]\<close>: recurse into \<open>Trm [q]\<close>\<close>
    show "domB_operB_xseq_dom (Inr (Inl (Trm [x21a], z)))"
      if "a = Trm [DB x1 x2, x21a]" for x1 x2 x21a
    proof -
      have ds: "d0succ (Trm [x21a])"
        using less.prems that by (simp add: d0succ_def)
      have "size (Trm [x21a] :: BT) < size a" using that by simp
      thus ?thesis using less.IH ds by blast
    qed
  next
    \<comment> \<open>(9) \<open>(\<ge>3)\<close>-component multi: recurse into \<open>Trm [last x22a]\<close>\<close>
    show "domB_operB_xseq_dom (Inr (Inl (Trm [last x22a], z)))"
      if "a = Trm (DB x1 x2 # x21a # x22a)" "x22a \<noteq> []" for x1 x2 x21a x22a
    proof -
      have ds: "d0succ (Trm [last x22a])"
        using less.prems that by (simp add: d0succ_def)
      have "last x22a \<in> set x22a" using that(2) by simp
      hence "size (last x22a) \<le> size_list size x22a"
        by (induction x22a) auto
      hence "size (Trm [last x22a] :: BT) < size a"
        using that by (cases x22a) auto
      thus ?thesis using less.IH ds by blast
    qed
  qed
qed

text \<open>The conditional \<open>operB.psimps\<close> now fires on every \<open>d0succ\<close> term.\<close>

lemma operB_d0succ_unfold:
  assumes "d0succ a"
  shows "operB a z =
     (case a of Trm xs \<Rightarrow> (case xs of
        [] \<Rightarrow> Trm []
      | [DB v b] \<Rightarrow>
          (if b = Trm [] then
             (if v = 0 then Trm []
              else if v = \<infinity> then Dprin (enat (numNat z + 1)) (Trm [])
              else z)
           else
             (let db = domB b in
              if db = {Trm []} then multBT (Dprin v (operB b (Trm []))) (numNat z + 1)
              else if (\<exists>u. v \<le> enat u \<and> db = TBv (enat u))
                   then Dprin v (operB b (xseq b (enat (tbvIdx db)) (numNat z)))
              else Dprin v (operB b z)))
      | (p # q # rest) \<Rightarrow>
          addBT (Trm (butlast (p # q # rest))) (operB (Trm [last (p # q # rest)]) z)))"
  by (rule operB.psimps[OF operB_dom_d0succ[OF assms]])

text \<open>Multi-component peel: \<open>operB\<close> on a \<open>d0succ\<close> term with \<open>\<ge> 2\<close> principals
  splits off all but the last component (the multi-branch of @{thm [source]
  operB_d0succ_unfold} fires on the concrete \<open>(p#q#rest)\<close> pattern).\<close>

lemma operB_d0succ_multi_peel:
  assumes "d0succ (Trm (p # q # rest))"
  shows "operB (Trm (p # q # rest)) z
           = addBT (Trm (butlast (p # q # rest))) (operB (Trm [last (p # q # rest)]) z)"
proof (cases p)
  case (DB v b)
  show ?thesis
    using operB_d0succ_unfold[OF assms, of z] DB by simp
qed

text \<open>Multi-component peel from the bare \<open>operB\<close>-domain (no \<open>d0succ\<close> needed):
  for a \<open>\<ge> 2\<close>-principal term \<open>operB\<close> splits off all but the last component.
  We \<open>cases\<close> on the head \<open>p\<close> first so the nested \<open>list\<close>/\<open>BP\<close> \<open>case\<close> in
  @{thm [source] operB.psimps} reduces concretely (a bare \<open>simp\<close> stalls on the
  abstract head \<open>case p of DB v b \<Rightarrow> \<dots>\<close>).\<close>

lemma operB_dom_multi_peel:
  assumes "domB_operB_xseq_dom (Inr (Inl (Trm (p # q # rest), z)))"
  shows "operB (Trm (p # q # rest)) z
           = addBT (Trm (butlast (p # q # rest))) (operB (Trm [last (p # q # rest)]) z)"
proof (cases p)
  case (DB v b)
  show ?thesis
    using operB.psimps[OF assms] DB by simp
qed

text \<open>\<open>numNat (numBT n) = n\<close>; \<open>multBT a 1 = a\<close>.\<close>

lemma numNat_numBT: "numNat (numBT n) = n"
  by (simp add: numNat_def numBT_def)

text \<open>Strip a trailing \<open>D\<^sub>0 0\<close> with \<open>z = 0\<close>: \<open>operB (t' +\<^sub>B D\<^sub>0 0) 0 = t'\<close>.\<close>

lemma operB_strip_d0:
  shows "operB (t' +\<^sub>B Dpt 0 0\<^sub>B) (Trm []) = t'"
proof -
  let ?b = "t' +\<^sub>B Dpt 0 0\<^sub>B"
  obtain xs where x: "t' = Trm xs" by (cases t')
  have ds: "d0succ ?b" by (rule d0succ_addD00)
  show ?thesis
  proof (cases xs)
    case Nil
    \<comment> \<open>\<open>t' = 0\<close>: \<open>?b = D\<^sub>0 0\<close>, single base branch \<open>v = 0\<close> returns \<open>0 = t'\<close>\<close>
    have be: "?b = Trm [DB 0 (Trm [])]" using x Nil by simp
    have "operB ?b (Trm []) = Trm []"
      using operB_d0succ_unfold[OF ds] be by (simp)
    thus ?thesis using x Nil by simp
  next
    case (Cons p ps)
    \<comment> \<open>\<open>t'\<close> nonempty: \<open>?b = Trm (p # q # rest)\<close> with last \<open>= D\<^sub>0 0\<close>, multi-peel\<close>
    obtain q rest where qr: "ps @ [DB 0 (Trm [])] = q # rest"
      by (cases "ps @ [DB 0 (Trm [])]") auto
    have be: "?b = Trm (p # q # rest)" using x Cons qr by simp
    have ds': "d0succ (Trm (p # q # rest))" using ds be by simp
    have peel: "operB ?b (Trm [])
                  = addBT (Trm (butlast (p # q # rest)))
                          (operB (Trm [last (p # q # rest)]) (Trm []))"
      using operB_d0succ_multi_peel[OF ds'] be by simp
    have pqr: "p # q # rest = p # ps @ [DB 0 (Trm [])]" using qr by simp
    have lst: "last (p # q # rest) = DB 0 (Trm [])" using pqr by simp
    have but: "butlast (p # q # rest) = p # ps" using pqr by (simp add: butlast_append)
    \<comment> \<open>\<open>operB (Trm [DB 0 0]) 0 = 0\<close> (base branch v=0)\<close>
    have d00: "d0succ (Trm [DB 0 (Trm [])])" by (rule d0succ_D00)
    have base: "operB (Trm [DB 0 (Trm [])]) (Trm []) = Trm []"
      using operB_d0succ_unfold[OF d00] by simp
    have "operB ?b (Trm []) = addBT (Trm (p # ps)) (Trm [])"
      using peel lst but base by simp
    also have "\<dots> = Trm (p # ps)" by simp
    finally show ?thesis using x Cons by simp
  qed
qed

text \<open>Single-principal successor evaluation:
  \<open>operB (D\<^sub>v(t' +\<^sub>B D\<^sub>0 0)) z = multBT (D\<^sub>v t') (numNat z + 1)\<close>.\<close>

lemma operB_single_succ:
  "operB (Dpt v (t' +\<^sub>B Dpt 0 0\<^sub>B)) z = multBT (Dpt v t') (numNat z + 1)"
proof -
  let ?b = "t' +\<^sub>B Dpt 0 0\<^sub>B"
  have bne: "?b \<noteq> Trm []" by (cases t') simp
  have ends: "endsD00 ?b" by (rule endsD00_addD00)
  have ds_b: "d0succ ?b" by (rule d0succ_addD00)
  have ds: "d0succ (Dpt v ?b)"
    by (rule d0succ_single_nonzero[OF bne ends ds_b])
  have dbeq: "domB ?b = {Trm []}" by (rule domB_endsD00[OF ends])
  have "operB (Dpt v ?b) z
          = (let db = domB ?b in
             if db = {Trm []} then multBT (Dprin v (operB ?b (Trm []))) (numNat z + 1)
             else if (\<exists>u. v \<le> enat u \<and> db = TBv (enat u))
                  then Dprin v (operB ?b (xseq ?b (enat (tbvIdx db)) (numNat z)))
             else Dprin v (operB ?b z))"
    using operB_d0succ_unfold[OF ds] bne by simp
  also have "\<dots> = multBT (Dprin v (operB ?b (Trm []))) (numNat z + 1)"
    using dbeq by (simp add: Let_def)
  also have "operB ?b (Trm []) = t'" by (rule operB_strip_d0)
  finally show ?thesis by simp
qed

end
