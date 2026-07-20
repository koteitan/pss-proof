theory Frontier_7_021
  imports Support_7_018
begin

section \<open>Term-level \<open>lessBT\<close> facts about \<open>+\<^sub>B\<close> (end-context inequality extension)\<close>

text \<open>The building blocks of the article's 部分表現の不等式の延長性 (content.md 1749)
  for the special case of an \<^emph>\<open>end\<close>-context (\<open>b = ()\<close>): appending on the right of
  a principal-term list.  (E1) appending a non-zero term strictly increases;
  (E2) \<open>+\<^sub>B\<close> is strictly monotone in its right argument.  Both are purely
  lexicographic facts about @{const lessBT} (\<open>+\<^sub>B\<close> = list \<open>@\<close> on the principal
  lists), proved by induction on the common prefix.  Used by the §7.3 \<open>Pred\<close>-on-
  \<open>Trans\<close> descent (the multi-recursion step \<open>Trans M = Trans A +\<^sub>B (\<dots>)\<close>).\<close>

lemma lessBT_addBT_self:
  assumes "c \<noteq> 0\<^sub>B"
  shows "lessBT t (t +\<^sub>B c)"
proof -
  obtain ts where t: "t = Trm ts" by (cases t)
  obtain cs where c: "c = Trm cs" by (cases c)
  have cs: "cs \<noteq> []" using assms c by auto
  have "lessBT (Trm ts) (Trm (ts @ cs))"
    by (induction ts) (simp_all add: cs)
  thus ?thesis using t c by simp
qed

lemma lessBT_addBT_mono_right:
  assumes "lessBT a b"
  shows "lessBT (t +\<^sub>B a) (t +\<^sub>B b)"
proof -
  obtain ts where t: "t = Trm ts" by (cases t)
  obtain as where a: "a = Trm as" by (cases a)
  obtain bs where b: "b = Trm bs" by (cases b)
  have "lessBT (Trm (ts @ as)) (Trm (ts @ bs))"
    using assms a b by (induction ts) simp_all
  thus ?thesis using t a b by simp
qed


section \<open>§7.3 部分表現の不等式の延長性 (scb inequality-extension, content.md 1749)\<close>

text \<open>The join-sweep helper for the strict-order extension: in a \<open>CM\<close>-joined
  component list closed by the outer \<open>RP\<close>, an occurrence of a principal string
  \<open>flatBP cp\<close> with all-\<open>RP\<close> tail \<open>b\<close> lies inside a single component, and only the
  LAST one (boundary-crossing gives a negative \<open>flatinj_dsum\<close> proper prefix,
  contradicting @{thm [source] flatinj_prefix_nonneg_BP}).  Replacing that
  component by a \<open>lessBP\<close>-larger one (supplied by the inductive hypothesis) makes
  the whole join-list \<open>lessBT\<close>-larger.  This mirrors @{thm [source] scbimg_join}
  but carries the strict-order conclusion instead of bare existence.\<close>

lemma scbjoin_lessBT:
  assumes IHr: "\<And>r s b. r \<in> set rs \<Longrightarrow> flatBP r = s @ flatBP cp @ b
                  \<Longrightarrow> \<forall>x \<in> set b. x = RP \<Longrightarrow> lessBP cp cp'
                  \<Longrightarrow> \<exists>r'. flatBP r' = s @ flatBP cp' @ b \<and> lessBP r r'"
    and eq: "concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP] = s @ flatBP cp @ b"
    and rb: "\<forall>x \<in> set b. x = RP"
    and lt: "lessBP cp cp'"
  shows "\<exists>rs'. length rs' = length rs
             \<and> concat (map (\<lambda>r. CM # flatBP r) rs') @ [RP] = s @ flatBP cp' @ b
             \<and> lessBT (Trm rs) (Trm rs')"
  using IHr eq rb
proof (induction rs arbitrary: s b)
  case Nil
  obtain w cb where cpw: "cp = DB w cb" by (cases cp) auto
  show ?case
    using Nil.prems(2) cpw by (cases s) auto
next
  case (Cons r0 rs)
  obtain w cb where cpw: "cp = DB w cb" by (cases cp) auto
  have fchd: "flatBP cp = Dsym w # flatBT cb" using cpw by simp
  have eq0: "CM # flatBP r0 @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]
             = s @ flatBP cp @ b"
    using Cons.prems(2) by simp
  have sne: "s \<noteq> []"
  proof
    assume "s = []"
    hence "CM = Dsym w" using eq0 fchd by simp
    thus False by simp
  qed
  then obtain s1 where ss: "s = CM # s1"
    using eq0 by (cases s) auto
  have eq1: "flatBP r0 @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]
             = s1 @ flatBP cp @ b"
    using eq0 ss by simp
  from append_eq_append_conv2[THEN iffD1, OF eq1]
  obtain us where split:
      "flatBP r0 = s1 @ us \<and> us @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]
                              = flatBP cp @ b
     \<or> flatBP r0 @ us = s1 \<and> concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]
                              = us @ flatBP cp @ b" by blast
  show ?case
  proof (cases "flatBP r0 @ us = s1 \<and> concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]
                              = us @ flatBP cp @ b")
    case True
    \<comment> \<open>occurrence beyond \<open>r0\<close>: recurse into the tail join; \<open>r0\<close> kept unchanged\<close>
    have IHtail: "\<And>r s b. r \<in> set rs \<Longrightarrow> flatBP r = s @ flatBP cp @ b
                    \<Longrightarrow> \<forall>x \<in> set b. x = RP \<Longrightarrow> lessBP cp cp'
                    \<Longrightarrow> \<exists>r'. flatBP r' = s @ flatBP cp' @ b \<and> lessBP r r'"
      using Cons.prems(1) by simp
    have tail: "concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP] = us @ flatBP cp @ b"
      using True by simp
    have "\<exists>rs'. length rs' = length rs
              \<and> concat (map (\<lambda>r. CM # flatBP r) rs') @ [RP] = us @ flatBP cp' @ b
              \<and> lessBT (Trm rs) (Trm rs')"
      by (rule Cons.IH[OF IHtail tail Cons.prems(3)])
    then obtain rs' where rs': "length rs' = length rs"
        "concat (map (\<lambda>r. CM # flatBP r) rs') @ [RP] = us @ flatBP cp' @ b"
        "lessBT (Trm rs) (Trm rs')" by blast
    have lentl: "lessBT (Trm (r0 # rs)) (Trm (r0 # rs'))"
      using rs'(3) by simp
    have "concat (map (\<lambda>r. CM # flatBP r) (r0 # rs')) @ [RP]
          = CM # flatBP r0 @ us @ flatBP cp' @ b" using rs'(2) by simp
    also have "\<dots> = s @ flatBP cp' @ b" using ss True by simp
    finally show ?thesis using rs'(1) lentl
      by (intro exI[of _ "r0 # rs'"]) simp
  next
    case False
    with split have inr0: "flatBP r0 = s1 @ us"
        and rest: "us @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP] = flatBP cp @ b"
      by auto
    from append_eq_append_conv2[THEN iffD1, OF rest[symmetric]]
    obtain vs where split2:
        "flatBP cp = us @ vs \<and> vs @ b = concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]
       \<or> flatBP cp @ vs = us \<and> b = vs @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]"
      by blast
    show ?thesis
    proof (cases "flatBP cp @ vs = us \<and> b = vs @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]")
      case True
      \<comment> \<open>occurrence wholly inside \<open>r0\<close>: tail of \<open>b\<close> forces \<open>rs = []\<close>\<close>
      have ball: "\<forall>x \<in> set (vs @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]). x = RP"
        using True Cons.prems(3) by simp
      have rsnil: "rs = []"
      proof (cases rs)
        case (Cons r1 rs1)
        hence "CM \<in> set (concat (map (\<lambda>r. CM # flatBP r) rs))" by simp
        thus ?thesis using ball by auto
      qed simp
      have vsRP: "\<forall>x \<in> set vs. x = RP" using ball by auto
      have r0eq: "flatBP r0 = s1 @ flatBP cp @ vs" using inr0 True by simp
      obtain r0' where r0': "flatBP r0' = s1 @ flatBP cp' @ vs" "lessBP r0 r0'"
        using Cons.prems(1)[of r0 s1 vs] r0eq vsRP lt by auto
      have "lessBT (Trm [r0]) (Trm [r0'])" using r0'(2) by simp
      hence lentl: "lessBT (Trm (r0 # rs)) (Trm (r0' # rs))" using rsnil by simp
      have "concat (map (\<lambda>r. CM # flatBP r) [r0']) @ [RP]
            = CM # s1 @ flatBP cp' @ vs @ [RP]" using r0'(1) by simp
      also have "\<dots> = s @ flatBP cp' @ b" using ss True rsnil by simp
      finally show ?thesis using rsnil lentl
        by (intro exI[of _ "[r0']"]) simp
    next
      case False
      with split2 have fcsplit: "flatBP cp = us @ vs"
          and vsb: "vs @ b = concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]" by auto
      have vsne: "vs \<noteq> []"
      proof
        assume v0: "vs = []"
        hence "flatBP cp = us" using fcsplit by simp
        hence "b = concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]" using vsb v0 by simp
        hence "flatBP cp @ vs = us \<and> b = vs @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]"
          using fcsplit v0 vsb by simp
        thus False using False by simp
      qed
      show ?thesis
      proof (cases "us = []")
        case True
        have "flatBP cp = vs" using fcsplit True by simp
        hence hd: "hd (vs @ b) = Dsym w" using fchd vsne by (cases vs) auto
        have "hd (concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]) = CM
              \<or> hd (concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]) = RP"
          by (cases rs) auto
        thus ?thesis using vsb hd by auto
      next
        case False
        have dsus_neg: "flatinj_dsum us < 0"
        proof -
          have "flatinj_dsum (flatBP r0) = -1"
            by (rule flatinj_dsum_flatBP)
          moreover have "0 \<le> flatinj_dsum s1"
            using flatinj_prefix_nonneg_BP[OF inr0] False by simp
          moreover have "flatinj_dsum (flatBP r0) = flatinj_dsum s1 + flatinj_dsum us"
            using inr0 by simp
          ultimately show ?thesis by simp
        qed
        have "0 \<le> flatinj_dsum us"
          using flatinj_prefix_nonneg_BP[OF fcsplit] vsne by simp
        thus ?thesis using dsus_neg by simp
      qed
    qed
  qed
qed


text \<open>部分表現の不等式の延長性 (content.md 1749): replacing a principal sub-term
  \<open>cp\<close> (a \<open>BP\<close>) by a \<open>lessBP\<close>-larger principal \<open>cp'\<close> at a fixed scb position
  (common prefix \<open>s\<close>, common all-\<open>RP\<close> tail \<open>b\<close>) is strictly monotone for the
  Buchholz order: the whole terms satisfy \<open>lessBT t t'\<close> / \<open>lessBP p p'\<close>.
  Empirically 0/114,000 mismatches.  Same induction as
  @{thm [source] scbimg_image_BT}, but the comparison target's structure is read
  off the given decomposition via @{thm [source] m_7_flatBT_inj}.\<close>

lemma scbext_lessBT:
  "flatBT t = s @ flatBP cp @ b \<Longrightarrow> flatBT t' = s @ flatBP cp' @ b
   \<Longrightarrow> (\<forall>x \<in> set b. x = RP) \<Longrightarrow> lessBP cp cp' \<Longrightarrow> lessBT t t'"
  and scbext_lessBP:
  "flatBP p = s @ flatBP cp @ b \<Longrightarrow> flatBP p' = s @ flatBP cp' @ b
   \<Longrightarrow> (\<forall>x \<in> set b. x = RP) \<Longrightarrow> lessBP cp cp' \<Longrightarrow> lessBP p p'"
proof (induct t and p arbitrary: s b t' and s b p' rule: flatBT_flatBP.induct)
  case (1 s b t')
  obtain w cb where cpw: "cp = DB w cb" by (cases cp) auto
  show ?case using 1(1) cpw by (cases s) auto
next
  case (2 p s b t')
  \<comment> \<open>\<open>flatBT (Trm [p]) = flatBP p\<close>; recover \<open>t' = Trm [p']\<close> from its flat string.\<close>
  have ep: "flatBP p = s @ flatBP cp @ b" using 2(2) by simp
  obtain w cb where cpw: "cp = DB w cb" by (cases cp) auto
  obtain pu pa where pp: "p = DB pu pa" by (cases p) auto
  obtain tps where tt': "t' = Trm tps" by (cases t')
  have ftt': "flatBT (Trm tps) = s @ flatBP cp' @ b" using 2(3) tt' by simp
  have tps_ne: "tps \<noteq> []"
  proof
    assume "tps = []"
    hence "[Zsym] = s @ flatBP cp' @ b" using ftt' by simp
    moreover obtain w' cb' where "cp' = DB w' cb'" using 2(5) cpw by (cases cp') auto
    ultimately show False by (cases s) auto
  qed
  show ?case
  proof (cases tps)
    case (Cons p' rest)
    show ?thesis
    proof (cases rest)
      case Nil
      \<comment> \<open>single principal: \<open>flatBT t' = flatBP p'\<close>, apply IH \<open>scbext_lessBP\<close>.\<close>
      have ep': "flatBP p' = s @ flatBP cp' @ b" using ftt' Cons Nil by simp
      have "lessBP p p'" using 2(1)[OF ep ep' 2(4) 2(5)] .
      thus ?thesis using tt' Cons Nil by simp
    next
      case (Cons q' qs')
      \<comment> \<open>tuple \<open>t' = Trm (p' # q' # qs')\<close>: its flat head is \<open>LP\<close>, but the head of
          \<open>s @ flatBP cp' @ b\<close> equals the head of \<open>flatBP p\<close> (\<open>= Dsym pu\<close>): clash.\<close>
      have tps3: "tps = p' # q' # qs'" using \<open>tps = p' # rest\<close> Cons by simp
      have "s @ flatBP cp' @ b = flatBT (Trm (p' # q' # qs'))"
        using ftt' tps3 by simp
      hence hdLP: "hd (s @ flatBP cp' @ b) = LP" by simp
      have "hd (s @ flatBP cp' @ b) \<noteq> LP"
      proof (cases s)
        case Nil
        obtain w' cb' where cp'w: "cp' = DB w' cb'" using 2(5) cpw by (cases cp') auto
        show ?thesis using Nil cp'w by simp
      next
        case (Cons c cs)
        \<comment> \<open>head \<open>= c\<close>, also the head of \<open>flatBP p = s @ flatBP cp @ b\<close>, i.e. \<open>Dsym pu\<close>\<close>
        have "c = Dsym pu" using ep pp Cons by simp
        thus ?thesis using Cons by simp
      qed
      thus ?thesis using hdLP by simp
    qed
  qed (use tps_ne in simp)
next
  case (3 p q ps s b t')
  obtain w cb where cpw: "cp = DB w cb" by (cases cp) auto
  have fchd: "flatBP cp = Dsym w # flatBT cb" using cpw by simp
  let ?JOIN = "concat (map (\<lambda>r. CM # flatBP r) (q # ps))"
  have flat3: "flatBT (Trm (p # q # ps)) = LP # (flatBP p @ ?JOIN) @ [RP]" by simp
  have sne: "s \<noteq> []"
  proof
    assume "s = []"
    hence "LP = Dsym w" using 3(3) fchd flat3 by simp
    thus False by simp
  qed
  then obtain s1 where ss: "s = LP # s1" using 3(3) flat3 by (cases s) auto
  have eq1: "flatBP p @ ?JOIN @ [RP] = s1 @ flatBP cp @ b"
    using 3(3) flat3 ss by simp
  from append_eq_append_conv2[THEN iffD1, OF eq1]
  obtain us where split:
      "flatBP p = s1 @ us \<and> us @ ?JOIN @ [RP] = flatBP cp @ b
     \<or> flatBP p @ us = s1 \<and> ?JOIN @ [RP] = us @ flatBP cp @ b" by blast
  show ?case
  proof (cases "flatBP p @ us = s1 \<and> ?JOIN @ [RP] = us @ flatBP cp @ b")
    case True
    \<comment> \<open>occurrence in the join: first component \<open>p\<close> unchanged, replace inside join.\<close>
    have IHr: "\<And>r s b. r \<in> set (q # ps) \<Longrightarrow> flatBP r = s @ flatBP cp @ b
                 \<Longrightarrow> \<forall>x \<in> set b. x = RP \<Longrightarrow> lessBP cp cp'
                 \<Longrightarrow> \<exists>r'. flatBP r' = s @ flatBP cp' @ b \<and> lessBP r r'"
    proof -
      fix r s b
      assume rin: "r \<in> set (q # ps)" and req: "flatBP r = s @ flatBP cp @ b"
        and rrb: "\<forall>x \<in> set b. x = RP" and rlt: "lessBP cp cp'"
      obtain r' where r': "flatBP r' = s @ flatBP cp' @ b"
        using scbimg_image_BP[OF req rrb] by blast
      have "lessBP r r'" using 3(2)[OF rin req r' rrb rlt] .
      thus "\<exists>r'. flatBP r' = s @ flatBP cp' @ b \<and> lessBP r r'"
        using r' by blast
    qed
    have joineq: "concat (map (\<lambda>r. CM # flatBP r) (q # ps)) @ [RP] = us @ flatBP cp @ b"
      using True by simp
    have "\<exists>rs'. length rs' = length (q # ps)
              \<and> concat (map (\<lambda>r. CM # flatBP r) rs') @ [RP] = us @ flatBP cp' @ b
              \<and> lessBT (Trm (q # ps)) (Trm rs')"
      by (rule scbjoin_lessBT[where cp = cp, OF IHr joineq 3(5) 3(6)])
    then obtain rs' where rs': "length rs' = length (q # ps)"
        "concat (map (\<lambda>r. CM # flatBP r) rs') @ [RP] = us @ flatBP cp' @ b"
        "lessBT (Trm (q # ps)) (Trm rs')" by blast
    obtain r1' rest' where rsc: "rs' = r1' # rest'"
      using rs' by (cases rs') auto
    have "flatBT (Trm (p # r1' # rest'))
          = LP # flatBP p @ (concat (map (\<lambda>r. CM # flatBP r) rs') @ [RP])"
      using rsc by simp
    also have "\<dots> = LP # flatBP p @ us @ flatBP cp' @ b" using rs'(2) by simp
    also have "\<dots> = s @ flatBP cp' @ b" using ss True by simp
    also have "\<dots> = flatBT t'" using 3(4) by simp
    finally have eqt': "flatBT (Trm (p # r1' # rest')) = flatBT t'" .
    have "lessBT (Trm (p # q # ps)) (Trm (p # r1' # rest'))"
      using rs'(3) rsc by simp
    moreover have "t' = Trm (p # r1' # rest')"
      using m_7_flatBT_inj[OF eqt'[symmetric]] .
    ultimately show ?thesis by simp
  next
    case False
    with split have inp: "flatBP p = s1 @ us"
        and rest: "us @ ?JOIN @ [RP] = flatBP cp @ b" by auto
    \<comment> \<open>occurrence (purportedly) in the first component: impossible (as in scbimg)\<close>
    from append_eq_append_conv2[THEN iffD1, OF rest]
    obtain vs where split2:
        "us = flatBP cp @ vs \<and> vs @ ?JOIN @ [RP] = b
       \<or> us @ vs = flatBP cp \<and> ?JOIN @ [RP] = vs @ b" by blast
    have False
    proof (cases "us = flatBP cp @ vs \<and> vs @ ?JOIN @ [RP] = b")
      case True
      hence "CM \<in> set b" by auto
      thus False using 3(5) by auto
    next
      case False
      with split2 have fcsplit: "us @ vs = flatBP cp"
          and jrest: "?JOIN @ [RP] = vs @ b" by auto
      show False
      proof (cases "us = []")
        case True
        hence "vs = flatBP cp" using fcsplit by simp
        hence hdD: "hd (vs @ b) = Dsym w" using fchd by simp
        have "vs @ b = CM # flatBP q @ concat (map (\<lambda>r. CM # flatBP r) ps) @ [RP]"
          using jrest by simp
        hence "hd (vs @ b) = CM" by simp
        thus False using hdD by simp
      next
        case usne: False
        have vsne: "vs \<noteq> []"
        proof
          assume v0: "vs = []"
          hence "?JOIN @ [RP] = b" using jrest by simp
          hence "CM \<in> set b" by auto
          thus False using 3(5) by auto
        qed
        have "flatinj_dsum us < 0"
        proof -
          have "flatinj_dsum (flatBP p) = -1" by (rule flatinj_dsum_flatBP)
          moreover have "0 \<le> flatinj_dsum s1"
            using flatinj_prefix_nonneg_BP[OF inp usne] .
          moreover have "flatinj_dsum (flatBP p) = flatinj_dsum s1 + flatinj_dsum us"
            using inp by simp
          ultimately show ?thesis by simp
        qed
        moreover have "0 \<le> flatinj_dsum us"
          using flatinj_prefix_nonneg_BP[OF fcsplit[symmetric] vsne] .
        ultimately show False by simp
      qed
    qed
    thus ?thesis ..
  qed
next
  case (4 u a s b p')
  show ?case
  proof (cases "s = []")
    case True
    \<comment> \<open>\<open>s = []\<close>: \<open>flatBP (DB u a) = flatBP cp @ b\<close>, all-\<open>RP\<close> \<open>b\<close> forces \<open>b = []\<close>,
        \<open>cp = DB u a\<close>; likewise \<open>p' = cp'\<close>; the goal is the given \<open>lessBP cp cp'\<close>.\<close>
    obtain w cb where cpw: "cp = DB w cb" by (cases cp) auto
    obtain w' cb' where cpw': "cp' = DB w' cb'" by (cases cp')
    obtain pu' pa' where pp': "p' = DB pu' pa'" by (cases p')
    have e: "flatBP (DB u a) @ [] = flatBP cp @ b" using 4(2) True by simp
    have cpeq: "flatBP (DB u a) = flatBP cp"
      using flatinj_flatBP_cancel[OF e] by blast
    \<comment> \<open>\<open>Dsym u # flatBT a = Dsym w # flatBT cb\<close>: split into head + body\<close>
    have ua: "u = w" and acb: "flatBT a = flatBT cb" using cpeq cpw by auto
    have p1: "DB u a = cp" using ua acb cpw m_7_flatBT_inj by simp
    have e': "flatBP p' @ [] = flatBP cp' @ b" using 4(3) True by simp
    have cpeq': "flatBP p' = flatBP cp'"
      using flatinj_flatBP_cancel[OF e'] by blast
    have ua': "pu' = w'" and acb': "flatBT pa' = flatBT cb'"
      using cpeq' cpw' pp' by auto
    have p2: "p' = cp'" using ua' acb' cpw' pp' m_7_flatBT_inj by simp
    show ?thesis using p1 p2 4(5) by simp
  next
    case False
    have "Dsym u # flatBT a = s @ flatBP cp @ b" using 4(2) by simp
    then obtain s1 where ss: "s = Dsym u # s1" and aeq: "flatBT a = s1 @ flatBP cp @ b"
      using False by (cases s) auto
    obtain pu' pa' where pp': "p' = DB pu' pa'" by (cases p')
    have "Dsym pu' # flatBT pa' = s @ flatBP cp' @ b" using 4(3) pp' by simp
    hence headeq: "Dsym pu' = Dsym u" and aeq': "flatBT pa' = s1 @ flatBP cp' @ b"
      using ss by auto
    have "lessBT a pa'" using 4(1)[OF aeq aeq' 4(4) 4(5)] .
    hence "lessBP (DB u a) (DB u pa')" by simp
    thus ?thesis using pp' headeq by simp
  qed
qed


section \<open>§7.3 \<open>c\<^sub>2\<close> is a single principal term (claim (2) of \<open>p_7_3_c1_c2\<close>)\<close>

text \<open>\<open>transC2 M\<close> is unconditionally of the form \<open>D\<^sub>v(\<dots>)\<close> (every branch of the
  case definition is \<open>Dpt v _\<close>), hence has exactly one principal component.
  This discharges claim (2) of the article's 命題（\<open>c\<^sub>1\<close>と\<open>c\<^sub>2\<close>の大小関係）
  (content.md 2270) with no hypotheses.\<close>

lemma Lng_PB_Dpt [simp]: "Lng (PB (Dpt v t)) = 1"
  by (simp add: PB_def)

lemma transC2_single_principal: "Lng (PB (transC2 M)) = 1"
  by (simp add: transC2_def Let_def)


section \<open>§7.3 \<open>c\<^sub>1\<close> is a single principal term (claim (1) of \<open>p_7_3_c1_c2\<close>)\<close>

text \<open>A flat string that IS a principal term's flat (\<open>isPTB_str\<close>) has exactly one
  principal component (\<open>c = Trm [p]\<close> by injectivity of @{const flatBT}).\<close>

lemma isPTB_str_imp_Lng_PB_1:
  assumes "isPTB_str (flatBT c)"
  shows "Lng (PB c) = 1"
proof -
  from assms obtain p where p: "flatBT c = flatBP p"
    by (auto simp: isPTB_str_def)
  have "flatBT c = flatBT (Trm [p])" using p by simp
  hence "c = Trm [p]" by (rule m_7_flatBT_inj)
  thus ?thesis by (simp add: PB_def)
qed

text \<open>Claim (1) of 命題（\<open>c\<^sub>1\<close>と\<open>c\<^sub>2\<close>の大小関係） (content.md 2270): under the
  recursion's branch conditions (\<open>M\<close> reduced \<open>\<and>\<close> mono, \<open>j\<^sub>1 > 0\<close>, \<open>t\<^sub>1 \<noteq> 0\<close>),
  \<open>c\<^sub>1 = Mark(Pred M)(j\<^sub>-\<^sub>1)\<close> is a single principal term.  Article reason
  (content.md 2110): \<open>(t\<^sub>1, c\<^sub>1) \<in> T\<^bsub>B\<^esub>\<^sup>Marked\<close> and \<open>t\<^sub>1 \<noteq> 0\<close> give \<open>c\<^sub>1 \<in> PT\<^bsub>B\<^esub>\<close>.
  Here \<open>(t\<^sub>1, c\<^sub>1) \<in> MarkedB\<close> comes from the value invariant on \<open>Pred M\<close> with the
  \<open>c\<^sub>1\<close>-call membership @{thm [source] Marked_Pred_Adm}, and the scb-decomposition's
  \<open>isPTB_str\<close> side condition (valid since \<open>t\<^sub>1 \<noteq> 0\<^sub>B\<close>) pins \<open>c\<^sub>1\<close> to one principal.\<close>

lemma transC1_single_principal:
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and J1: "transJ1 M > 0" and T1: "transT1 M \<noteq> 0\<^sub>B"
  shows "Lng (PB (transC1 M)) = 1"
proof -
  have MT: "M \<in> T_PS" using MP by (simp add: PT_PS_def)
  have mono: "monoT M" using MP by (simp add: PT_PS_def)
  have L: "1 < Lng M" using J1 by (simp add: transJ1_def)
  have hp: "hasParent M 0 (Lng M - 1)" by (rule monoT_hasParent0_last[OF MT mono L])
  have mkd: "(Pred M, Adm M (parent M 0 (Lng M - 1))) \<in> Marked"
    by (rule Marked_Pred_Adm[OF MT L hp])
  have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have c1eq: "transC1 M = Mark (Pred M) (Adm M (parent M 0 (Lng M - 1)))"
    by (simp add: transC1_def transJm1_def transJ0_def transJ1_def)
  have t1ne: "Trans (Pred M) \<noteq> 0\<^sub>B" using T1 by (simp add: transT1_def)
  have inv: "(Trans (Pred M), Mark (Pred M) (Adm M (parent M 0 (Lng M - 1)))) \<in> MarkedB"
    using Trans_Mark_invariant_aux predRT mkd by blast
  then obtain s b where
    sd: "scb_decomp (Trans (Pred M)) s (flatBT (transC1 M)) b"
    using c1eq by (auto simp: MarkedB_def)
  have "isPTB_str (flatBT (transC1 M))"
    using sd t1ne by (simp add: scb_decomp_def)
  thus ?thesis by (rule isPTB_str_imp_Lng_PB_1)
qed


section \<open>§7.3 命題（右端第1基点の \<open>Mark\<close> の基本性質）— content.md 2294 (forward)\<close>

text \<open>For a NON-zero reduced pair sequence \<open>M\<close>, the rightmost mark
  \<open>m = j\<^sub>1 = Lng M - 1\<close> is the single principal \<open>D\<^bsub>M\<^bsub>1,j\<^sub>1\<^esub>\<^esub> 0\<close>.  Proved by
  \<open>Lng\<close>-strong induction, evaluating \<open>Mark M (Lng M - 1)\<close> by the conditional
  recursion @{thm [source] Mark.psimps} (domain from
  @{thm [source] m_7_3_Mark_welldef}), collapsing only the OUTER ifs to reach
  the wanted branch.  The excluded zero base \<open>[(0,0)]\<close> is the sole counterexample
  (correction A17), hence the \<open>\<not> zeroT M\<close> hypothesis.\<close>

lemma Mark_rightmost1_forward:
  assumes "M \<in> RT_PS" and "\<not> zeroT M" and "(M, Lng M - 1) \<in> Marked"
  shows "Mark M (Lng M - 1) = Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B"
proof -
  have "M \<in> RT_PS \<longrightarrow> \<not> zeroT M \<longrightarrow> (M, Lng M - 1) \<in> Marked
        \<longrightarrow> Mark M (Lng M - 1) = Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B"
  proof (induction M rule: measure_induct_rule[where f=Lng])
    case (less M)
    show ?case
    proof (intro impI)
      assume MR: "M \<in> RT_PS" and nzM: "\<not> zeroT M" and mM: "(M, Lng M - 1) \<in> Marked"
      have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
      have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
      have domK: "\<And>m. Trans_Mark_dom (Inr (M, m))" by (rule m_7_3_Mark_welldef[OF MR])
      let ?j1 = "Lng M - 1"
      show "Mark M ?j1 = Dpt (enat (entry M 1 ?j1)) 0\<^sub>B"
      proof (cases "Lng M = 1")
        case True
        \<comment> \<open>(A) base length 1, \<open>j\<^sub>1 = 0\<close>: \<open>M = [(v,v)]\<close> with \<open>v > 0\<close>\<close>
        obtain v where Mv: "M = [(v, v)]"
          using m_6_6_oneColumn[OF MT] MR True by auto
        have v0: "v \<noteq> 0" using nzM Mv by (simp add: zeroT_def entry_def)
        have j10: "?j1 = 0" using True by simp
        have "Mark M ?j1 = Dpt (enat v) 0\<^sub>B" using Mv Mark_singleton v0 j10 by simp
        moreover have "entry M 1 ?j1 = v" using Mv j10 by (simp add: entry_def)
        ultimately show ?thesis by simp
      next
        case notone: False
        have L: "1 < Lng M" using Mne notone by (cases M) auto
        have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
        have j1pos: "0 < ?j1" using L by simp
        show ?thesis
        proof (cases "monoT M")
          case mono: True
          have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
          show ?thesis
          proof (cases "Trans (Pred M) = 0\<^sub>B")
            case t1z: True
            \<comment> \<open>(B) mono, \<open>t\<^sub>1 = 0\<close>: branch yields \<open>Dpt (entry M 1 j\<^sub>1) 0\<close> since \<open>j\<^sub>1 \<noteq> 0\<close>\<close>
            have kv: "Mark M ?j1 = (if ?j1 = 0 then Dpt 0 (Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)
                                    else Dpt (enat (entry M 1 ?j1)) 0\<^sub>B)"
              using Mark.psimps[OF domK] MR Lgt1 mono t1z by (simp add: Let_def)
            show ?thesis using kv j1pos by simp
          next
            case t1ne: False
            \<comment> \<open>(B) mono, \<open>t\<^sub>1 \<noteq> 0\<close>: outer \<open>if m < j\<^sub>1\<close> is False (\<open>m = j\<^sub>1\<close>)\<close>
            have c1: "(M \<notin> RT_PS) = False" using MR by simp
            have c2: "(?j1 = 0) = False" using j1pos by simp
            have c3: "monoT M = True" using mono by simp
            have c4: "(Trans (Pred M) = 0\<^sub>B) = False" using t1ne by simp
            have c5: "(?j1 < ?j1) = False" by simp
            show ?thesis
              by (subst Mark.psimps[OF domK])
                 (simp only: c1 c2 c3 c4 c5 if_False if_True Let_def)
          qed
        next
          case nmono: False
          \<comment> \<open>(C) multiT branch\<close>
          have muM: "multiT M" using nzM nmono by (simp add: multiT_def)
          have cut: "0 < Pcut M \<and> Pcut M \<le> ?j1" using Pcut_le[OF L] by simp
          let ?PJ = "drop (Pcut M) M"
          have PJeq: "P M ! (Lng (P M) - 1) = ?PJ"
            by (rule trans_multiT_last_component(1)[OF MT muM])
          have LdJ: "Lng (drop (Pcut M) M) = Lng M - Pcut M" by simp
          have meq2: "\<And>m. m - (?j1 - Lng (drop (Pcut M) M) + 1) = m - Pcut M"
          proof -
            fix m
            have "?j1 - Lng (drop (Pcut M) M) + 1 = Pcut M"
              using LdJ Pcut_le[OF L] by linarith
            thus "m - (?j1 - Lng (drop (Pcut M) M) + 1) = m - Pcut M" by simp
          qed
          have c1: "(M \<notin> RT_PS) = False" using MR by simp
          have c2: "(?j1 = 0) = False" using j1pos by simp
          have c3: "monoT M = False" using nmono by simp
          have markM: "\<And>m. Mark M m = (if ?PJ = [(0, 0)] then Dpt 0 0\<^sub>B
                                        else Mark ?PJ (m - Pcut M))"
          proof -
            fix m
            have raw: "Mark M m =
                (if P M ! (Lng (P M) - 1) = [(0, 0)] then Dpt 0 0\<^sub>B
                 else Mark (P M ! (Lng (P M) - 1))
                        (m - (?j1 - Lng (P M ! (Lng (P M) - 1)) + 1)))"
              by (subst Mark.psimps[OF domK]) (simp only: c1 c2 c3 if_False Let_def)
            show "Mark M m = (if ?PJ = [(0, 0)] then Dpt 0 0\<^sub>B else Mark ?PJ (m - Pcut M))"
              unfolding raw PJeq meq2 ..
          qed
          \<comment> \<open>last column of \<open>?PJ\<close> = last column of \<open>M\<close>\<close>
          have LPJ: "Lng ?PJ = Lng M - Pcut M" by simp
          have PJne: "?PJ \<noteq> []" using cut LPJ L by (cases ?PJ) auto
          have lastcol: "entry ?PJ 1 (Lng ?PJ - 1) = entry M 1 ?j1"
          proof -
            have pl: "Pcut M < Lng M" using cut L by linarith
            have idx: "Pcut M + (Lng ?PJ - 1) = ?j1" using LPJ cut pl by linarith
            have "?PJ ! (Lng ?PJ - 1) = M ! (Pcut M + (Lng ?PJ - 1))"
              by (rule nth_drop) (use LPJ cut pl in linarith)
            also have "\<dots> = M ! ?j1" using idx by simp
            finally have "?PJ ! (Lng ?PJ - 1) = M ! ?j1" .
            thus ?thesis by (simp add: entry_def)
          qed
          show ?thesis
          proof (cases "?PJ = [(0, 0)]")
            case True
            \<comment> \<open>last column is \<open>(0,0)\<close>, so \<open>entry M 1 j\<^sub>1 = 0\<close>\<close>
            have "entry ?PJ 1 (Lng ?PJ - 1) = 0" using True by (simp add: entry_def)
            hence e0: "entry M 1 ?j1 = 0" using lastcol by simp
            have "Mark M ?j1 = Dpt 0 0\<^sub>B" using markM True by simp
            thus ?thesis using e0 by (simp add: zero_enat_def)
          next
            case False
            \<comment> \<open>recurse into \<open>?PJ\<close> (smaller \<open>Lng\<close>) via the IH\<close>
            have Pne: "P M \<noteq> []" by (rule P_nonempty)
            have J1lt: "Lng (P M) - 1 < Lng (P M)" using Pne by (cases "P M") auto
            have PJRT: "?PJ \<in> RT_PS"
              using m_6_6_P_reduced[OF MT] MR J1lt PJeq by auto
            have PJT: "?PJ \<in> T_PS" using PJRT by (simp add: RT_PS_def)
            have nzPJ: "\<not> zeroT ?PJ"
            proof
              assume z: "zeroT ?PJ"
              have L1: "Lng ?PJ = 1" using z by (simp add: zeroT_def)
              then obtain v where v: "?PJ = [(v, v)]"
                using m_6_6_oneColumn[OF PJT] PJRT by auto
              have "entry ?PJ 1 0 = 0" using z by (simp add: zeroT_def)
              hence "v = 0" using v by (simp add: entry_def)
              thus False using False v by simp
            qed
            have LPJlt: "Lng ?PJ < Lng M" using LPJ cut L by linarith
            have mPJ: "(?PJ, Lng ?PJ - 1) \<in> Marked"
            proof -
              have "(?PJ, ?j1 - Pcut M) \<in> Marked"
                by (rule multi_Marked_last_component(2)[OF MT muM mM])
              moreover have "?j1 - Pcut M = Lng ?PJ - 1" using LPJ cut L by linarith
              ultimately show ?thesis by simp
            qed
            have IH: "Mark ?PJ (Lng ?PJ - 1)
                      = Dpt (enat (entry ?PJ 1 (Lng ?PJ - 1))) 0\<^sub>B"
              using less.IH[OF LPJlt] PJRT nzPJ mPJ by blast
            have meq: "?j1 - Pcut M = Lng ?PJ - 1" using LPJ cut L by linarith
            have "Mark M ?j1 = Mark ?PJ (?j1 - Pcut M)" using markM False by simp
            also have "\<dots> = Mark ?PJ (Lng ?PJ - 1)" using meq by simp
            also have "\<dots> = Dpt (enat (entry ?PJ 1 (Lng ?PJ - 1))) 0\<^sub>B" using IH .
            also have "\<dots> = Dpt (enat (entry M 1 ?j1)) 0\<^sub>B" using lastcol by simp
            finally show ?thesis .
          qed
        qed
      qed
    qed
  qed
  thus ?thesis using assms by blast
qed


lemma principal_reconstruct:
  assumes "Lng (PB c) = 1" shows "c = Dpt (bpHeadV c) (bpHeadT c)"
proof -
  obtain ps where cps: "c = Trm ps" by (cases c)
  from assms have "length ps = 1" by (simp add: PB_def cps)
  then obtain p where psp: "ps = [p]" by (cases ps) auto
  obtain w u where pwu: "p = DB w u" by (cases p)
  show ?thesis using cps psp pwu by simp
qed

lemma SigmaB_snoc: "SigmaB (xs @ [x]) = SigmaB xs +\<^sub>B x"
  by (cases x) (simp add: SigmaB_def)

lemma transC1_lessBT_transC2:
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and J1pos: "transJ1 M > 0" and T1: "transT1 M \<noteq> 0\<^sub>B"
    and VIfact: "transCondVI M \<Longrightarrow>
                   lessBT (transT2 M) (Dpt (enat (entry M 1 (transJ1 M))) 0\<^sub>B)"
  shows "lessBT (transC1 M) (transC2 M)"
proof -
  define t2 where "t2 = transT2 M"
  define j1 where "j1 = transJ1 M"
  define jp where "jp = transJ0 M"
  define Dj1 where "Dj1 = Dpt (enat (entry M 1 j1)) 0\<^sub>B"
  have Dj1ne: "Dj1 \<noteq> 0\<^sub>B" by (simp add: Dj1_def)
  \<comment> \<open>1. \<open>c\<^sub>1\<close> is a single principal term\<close>
  have pc1: "Lng (PB (transC1 M)) = 1"
    by (rule transC1_single_principal[OF MR MP J1pos T1])
  \<comment> \<open>2. \<open>c\<^sub>1 = D\<^bsub>v\<^esub> t\<^sub>2\<close>\<close>
  have c1eq: "transC1 M = Dpt (transV M) t2"
    using principal_reconstruct[OF pc1]
    by (simp add: transV_def transT2_def t2_def)
  \<comment> \<open>3. \<open>t\<^sub>2 \<in> T\<^bsub>B\<^esub>\<close>\<close>
  have MT: "M \<in> T_PS" using MP by (simp add: PT_PS_def)
  have mono: "monoT M" using MP by (simp add: PT_PS_def)
  have L: "1 < Lng M" using J1pos by (simp add: transJ1_def)
  have hp: "hasParent M 0 (Lng M - 1)" by (rule monoT_hasParent0_last[OF MT mono L])
  have mkd: "(Pred M, Adm M (parent M 0 (Lng M - 1))) \<in> Marked"
    by (rule Marked_Pred_Adm[OF MT L hp])
  have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have c1val: "transC1 M = Mark (Pred M) (Adm M (parent M 0 (Lng M - 1)))"
    by (simp add: transC1_def transJm1_def transJ0_def transJ1_def)
  have c1TB: "transC1 M \<in> T_B"
    using m_7_3_Mark_in_T_B[OF predRT mkd] c1val by simp
  have t2TB: "t2 \<in> T_B"
    using c1TB unfolding c1eq by (auto simp: T_B_def)
  \<comment> \<open>4. case split, reducing each branch of \<open>transC2\<close>\<close>
  show ?thesis
  proof (cases "transCondI M \<or> transCondIII M \<or> transCondV M")
    case True
    have c2: "transC2 M = Dpt (transV M) (t2 +\<^sub>B Dj1)"
      using True
      by (simp add: transC2_def Let_def transV_def transT2_def transJ1_def Dj1_def
                    j1_def t2_def)
    have "lessBT t2 (t2 +\<^sub>B Dj1)" by (rule lessBT_addBT_self[OF Dj1ne])
    thus ?thesis using c1eq c2 by simp
  next
    case notA: False
    show ?thesis
    proof (cases "transCondVI M")
      case True
      have c2: "transC2 M = Dpt (transV M) Dj1"
        using notA True
        by (simp add: transC2_def Let_def transV_def transJ1_def Dj1_def j1_def)
      have "lessBT t2 Dj1"
        using VIfact[OF True] by (simp add: t2_def j1_def Dj1_def)
      thus ?thesis using c1eq c2 by simp
    next
      case notVI: False
      show ?thesis
      proof (cases "t2 = 0\<^sub>B")
        case True
        have c2: "transC2 M
                  = Dpt (transV M) (Dpt (enat (entry M 1 jp)) Dj1)"
          using notA notVI True
          by (simp add: transC2_def Let_def transV_def transT2_def transJ1_def
                        transJ0_def Dj1_def j1_def jp_def t2_def)
        have "lessBT t2 (Dpt (enat (entry M 1 jp)) Dj1)"
          using True by simp
        thus ?thesis using c1eq c2 by simp
      next
        case t2ne: False
        define J1 where "J1 = Lng (PB t2) - 1"
        define pj where "pj = PB t2 ! J1"
        \<comment> \<open>\<open>PB t\<^sub>2 \<noteq> []\<close>\<close>
        have lng_ne: "Lng (PB t2) \<noteq> 0"
          using m_7_1_term_components[OF t2TB] t2ne by auto
        have pbne: "PB t2 \<noteq> []" using lng_ne by auto
        \<comment> \<open>split off the last component\<close>
        have splitlast: "PB t2 = take J1 (PB t2) @ [pj]"
        proof -
          have "take J1 (PB t2) = butlast (PB t2)"
            by (simp add: J1_def butlast_conv_take)
          moreover have "pj = last (PB t2)"
            using pbne by (simp add: pj_def J1_def last_conv_nth)
          ultimately show ?thesis
            using append_butlast_last_id[OF pbne] by simp
        qed
        have t2split: "t2 = SigmaB (take J1 (PB t2)) +\<^sub>B pj"
        proof -
          have "t2 = SigmaB (PB t2)" using m_7_1_term_components[OF t2TB] by simp
          also have "\<dots> = SigmaB (take J1 (PB t2) @ [pj])"
            using splitlast by simp
          also have "\<dots> = SigmaB (take J1 (PB t2)) +\<^sub>B pj"
            by (rule SigmaB_snoc)
          finally show ?thesis .
        qed
        \<comment> \<open>\<open>pj\<close> is a single principal term\<close>
        have pjprinc: "Lng (PB pj) = 1"
        proof -
          have Jlt: "J1 < length (untrm t2)"
            using pbne by (simp add: J1_def PB_def)
          have "pj = (map (\<lambda>p. Trm [p]) (untrm t2)) ! J1"
            by (simp add: pj_def PB_def)
          also have "\<dots> = Trm [untrm t2 ! J1]" using Jlt by simp
          finally show ?thesis by (simp add: PB_def)
        qed
        have pjrec: "pj = Dpt (bpHeadV pj) (bpHeadT pj)"
          by (rule principal_reconstruct[OF pjprinc])
        show ?thesis
        proof (cases "bpHeadV pj = enat (entry M 1 jp)")
          case leftDj0: True
          have c2: "transC2 M
                    = Dpt (transV M)
                        (SigmaB (take J1 (PB t2))
                          +\<^sub>B Dpt (enat (entry M 1 jp))
                                (bpHeadT pj +\<^sub>B Dj1))"
            using notA notVI t2ne leftDj0
            by (simp add: transC2_def Let_def transV_def transT2_def transJ1_def
                          transJ0_def Dj1_def j1_def jp_def t2_def J1_def pj_def)
          \<comment> \<open>\<open>pj = D\<^bsub>M\<^bsub>1,jp\<^esub>\<^esub> (bpHeadT pj)\<close>, so \<open>t\<^sub>2 = \<Sigma>(prefix) + pj\<close>\<close>
          have pjval: "pj = Dpt (enat (entry M 1 jp)) (bpHeadT pj)"
            using pjrec leftDj0 by simp
          have t2eq: "t2 = SigmaB (take J1 (PB t2))
                            +\<^sub>B Dpt (enat (entry M 1 jp)) (bpHeadT pj)"
            using t2split pjval by simp
          have inner: "lessBT (Dpt (enat (entry M 1 jp)) (bpHeadT pj))
                              (Dpt (enat (entry M 1 jp)) (bpHeadT pj +\<^sub>B Dj1))"
            using lessBT_addBT_self[OF Dj1ne] by simp
          have "lessBT
                  (SigmaB (take J1 (PB t2))
                    +\<^sub>B Dpt (enat (entry M 1 jp)) (bpHeadT pj))
                  (SigmaB (take J1 (PB t2))
                    +\<^sub>B Dpt (enat (entry M 1 jp)) (bpHeadT pj +\<^sub>B Dj1))"
            by (rule lessBT_addBT_mono_right[OF inner])
          hence "lessBT t2
                  (SigmaB (take J1 (PB t2))
                    +\<^sub>B Dpt (enat (entry M 1 jp)) (bpHeadT pj +\<^sub>B Dj1))"
            using t2eq by simp
          thus ?thesis using c1eq c2 by simp
        next
          case leftDj0: False
          have c2: "transC2 M
                    = Dpt (transV M)
                        (t2 +\<^sub>B Dpt (enat (entry M 1 jp)) (t2 +\<^sub>B Dj1))"
            using notA notVI t2ne leftDj0
            by (simp add: transC2_def Let_def transV_def transT2_def transJ1_def
                          transJ0_def Dj1_def j1_def jp_def t2_def J1_def pj_def)
          have "lessBT t2 (t2 +\<^sub>B Dpt (enat (entry M 1 jp)) (t2 +\<^sub>B Dj1))"
            by (rule lessBT_addBT_self) simp
          thus ?thesis using c1eq c2 by simp
        qed
      qed
    qed
  qed
qed

text \<open>If \<open>t\<close> is a nonzero term whose first principal node-value \<open>bpHeadV t\<close> is
  strictly below \<open>w\<close>, then \<open>t\<close> is \<open>lessBT\<close>-below the single principal \<open>D\<^bsub>w\<^esub> 0\<^bsub>B\<^esub>\<close>:
  the very first principal of \<open>t\<close> already loses on its node value.\<close>

lemma lessBT_bpHeadV_lt:
  assumes "t \<noteq> 0\<^sub>B" and "bpHeadV t < w"
  shows "lessBT t (Dpt w 0\<^sub>B)"
proof -
  obtain ps where t: "t = Trm ps" by (cases t)
  have psne: "ps \<noteq> []" using \<open>t \<noteq> 0\<^sub>B\<close> t by auto
  obtain p ps' where ps: "ps = p # ps'" using psne by (cases ps) auto
  obtain v u where p: "p = DB v u" by (cases p)
  have hv: "bpHeadV t = v" using t ps p by simp
  hence vw: "v < w" using \<open>bpHeadV t < w\<close> by simp
  have "lessBP (DB v u) (DB w 0\<^sub>B)" using vw by simp
  hence "lessBT (Trm (DB v u # ps')) (Trm [DB w 0\<^sub>B])" by simp
  thus ?thesis using t ps p by simp
qed

text \<open>Condition-VI half of \<open>c\<^sub>1 < c\<^sub>2\<close> reduced to its only non-admissible
  sub-case: a Mark second-index bound (\<open>NAbound\<close>).  The admissible sub-case is
  discharged here outright (it forces \<open>transT2 M = 0\<^bsub>B\<^esub>\<close>).\<close>

lemma transC1_lessBT_transC2_modNA:
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and J1pos: "transJ1 M > 0" and T1: "transT1 M \<noteq> 0\<^sub>B"
    and NAbound: "transCondVI M \<Longrightarrow> \<not> adm M (transJ0 M) \<Longrightarrow> transT2 M \<noteq> 0\<^sub>B
                    \<Longrightarrow> bpHeadV (transT2 M) < enat (entry M 1 (transJ1 M))"
  shows "lessBT (transC1 M) (transC2 M)"
proof -
  have MT: "M \<in> T_PS" using MP by (simp add: PT_PS_def)
  have mono: "monoT M" using MP by (simp add: PT_PS_def)
  have L: "1 < Lng M" using J1pos by (simp add: transJ1_def)
  have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have VIfact: "transCondVI M \<Longrightarrow>
                  lessBT (transT2 M) (Dpt (enat (entry M 1 (transJ1 M))) 0\<^sub>B)"
  proof -
    assume VI: "transCondVI M"
    define Dj1 where "Dj1 = Dpt (enat (entry M 1 (transJ1 M))) 0\<^sub>B"
    show "lessBT (transT2 M) Dj1"
    proof (cases "transT2 M = 0\<^sub>B")
      case True
      have "lessBT (Trm []) Dj1" by (simp add: Dj1_def)
      thus ?thesis using True by simp
    next
      case t2ne: False
      show ?thesis
      proof (cases "adm M (transJ0 M)")
        case adm: True
        \<comment> \<open>admissible sub-case: \<open>transT2 M = 0\<^bsub>B\<^esub>\<close>, contradicting \<open>t2ne\<close>\<close>
        have j0eq: "transJ0 M = Lng M - 2"
        proof -
          have "parent M 0 (Lng M - 1) + 1 = Lng M - 1"
            using VI by (simp add: transCondVI_def)
          moreover have "transJ0 M = parent M 0 (Lng M - 1)"
            by (simp add: transJ0_def transJ1_def)
          ultimately show ?thesis by simp
        qed
        have jm1eq: "transJm1 M = transJ0 M"
          using adm by (simp add: transJm1_def Adm_def)
        have hp: "hasParent M 0 (Lng M - 1)"
          by (rule monoT_hasParent0_last[OF MT mono L])
        have mkd0: "(Pred M, Adm M (parent M 0 (Lng M - 1))) \<in> Marked"
          by (rule Marked_Pred_Adm[OF MT L hp])
        have parj0: "parent M 0 (Lng M - 1) = transJ0 M"
          by (simp add: transJ0_def transJ1_def)
        have admj0: "Adm M (transJ0 M) = transJ0 M"
          using adm by (simp add: Adm_def)
        have mkd: "(Pred M, transJ0 M) \<in> Marked"
          using mkd0 parj0 admj0 by simp
        have lngPred: "Lng (Pred M) - 1 = transJ0 M"
          using L j0eq by (simp add: Pred_def)
        have mkd': "(Pred M, Lng (Pred M) - 1) \<in> Marked"
          using mkd lngPred by simp
        have nzPred: "\<not> zeroT (Pred M)"
        proof
          assume "zeroT (Pred M)"
          hence "Trans (Pred M) = 0\<^sub>B" using m_7_3_Trans_zeroT[OF predRT] by simp
          thus False using T1 by (simp add: transT1_def)
        qed
        have markval: "Mark (Pred M) (Lng (Pred M) - 1)
                         = Dpt (enat (entry (Pred M) 1 (Lng (Pred M) - 1))) 0\<^sub>B"
          by (rule Mark_rightmost1_forward[OF predRT nzPred mkd'])
        have markj0: "Mark (Pred M) (transJm1 M)
                        = Dpt (enat (entry (Pred M) 1 (Lng (Pred M) - 1))) 0\<^sub>B"
          using markval lngPred jm1eq by simp
        have "transT2 M = bpHeadT (Mark (Pred M) (transJm1 M))"
          by (simp add: transT2_def transC1_def)
        also have "\<dots> = bpHeadT (Dpt (enat (entry (Pred M) 1 (Lng (Pred M) - 1))) 0\<^sub>B)"
          using markj0 by simp
        also have "\<dots> = 0\<^sub>B" by simp
        finally have "transT2 M = 0\<^sub>B" .
        thus ?thesis using t2ne by simp
      next
        case nadm: False
        have hbound: "bpHeadV (transT2 M) < enat (entry M 1 (transJ1 M))"
          by (rule NAbound[OF VI nadm t2ne])
        show ?thesis unfolding Dj1_def
          by (rule lessBT_bpHeadV_lt[OF t2ne hbound])
      qed
    qed
  qed
  show ?thesis by (rule transC1_lessBT_transC2[OF MR MP J1pos T1 VIfact])
qed


section \<open>§7.3 NAbound prerequisite: index-set of a \<open>BT\<close> term (\<open>flatIdx\<close>)\<close>

text \<open>\<open>flatIdx t\<close> = the set of \<open>D\<close>-indices occurring anywhere in \<open>t\<close>, read off the
  flat string (so a substring containment of \<open>flatBT\<close> immediately bounds it).
  The keystone for NAbound is a suffix-max bound on the indices of \<open>Mark N m\<close>.\<close>

definition flatIdx :: "BT \<Rightarrow> enat set" where
  "flatIdx t = {v. Dsym v \<in> set (flatBT t)}"

lemma flatIdx_zero [simp]: "flatIdx 0\<^sub>B = {}"
  by (simp add: flatIdx_def)

text \<open>The \<open>Dsym\<close>-letters of a tuple are the union over its principal components.\<close>

lemma flatIdx_Trm: "flatIdx (Trm xs) = (\<Union>p \<in> set xs. {v. Dsym v \<in> set (flatBP p)})"
proof (cases xs)
  case Nil thus ?thesis by (simp add: flatIdx_def)
next
  case (Cons p rest)
  show ?thesis
  proof (cases rest)
    case Nil thus ?thesis using Cons by (simp add: flatIdx_def)
  next
    case (Cons q ps)
    have "set (flatBT (Trm (p # q # ps)))
          = {LP, RP} \<union> set (flatBP p)
            \<union> (\<Union>r \<in> set (q # ps). insert CM (set (flatBP r)))"
      by auto
    thus ?thesis using \<open>xs = p # rest\<close> \<open>rest = q # ps\<close>
      by (auto simp: flatIdx_def)
  qed
qed

lemma flatIdx_Dpt [simp]: "flatIdx (Dpt v t) = insert v (flatIdx t)"
  by (auto simp: flatIdx_def)

lemma flatIdx_addBT [simp]: "flatIdx (a +\<^sub>B b) = flatIdx a \<union> flatIdx b"
proof -
  obtain as where a: "a = Trm as" by (cases a)
  obtain bs where b: "b = Trm bs" by (cases b)
  have "a +\<^sub>B b = Trm (as @ bs)" using a b by simp
  thus ?thesis using a b by (simp add: flatIdx_Trm)
qed

lemma flatIdx_SigmaB: "flatIdx (SigmaB ts) = (\<Union>t \<in> set ts. flatIdx t)"
proof -
  have "flatIdx (SigmaB ts) = (\<Union>p \<in> set (concat (map untrm ts)). {v. Dsym v \<in> set (flatBP p)})"
    by (simp add: SigmaB_def flatIdx_Trm)
  also have "\<dots> = (\<Union>t \<in> set ts. \<Union>p \<in> set (untrm t). {v. Dsym v \<in> set (flatBP p)})"
    by auto
  also have "\<dots> = (\<Union>t \<in> set ts. flatIdx t)"
  proof -
    have "\<And>t. flatIdx t = (\<Union>p \<in> set (untrm t). {v. Dsym v \<in> set (flatBP p)})"
      by (metis flatIdx_Trm untrm.simps untrm.cases)
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

text \<open>The leftmost index \<open>bpHeadV t\<close> occurs in \<open>t\<close>.\<close>

lemma bpHeadV_in_flatIdx:
  assumes "t \<noteq> 0\<^sub>B" shows "bpHeadV t \<in> flatIdx t"
proof -
  obtain ps where t: "t = Trm ps" by (cases t)
  have "ps \<noteq> []" using assms t by auto
  then obtain p ps' where ps: "ps = p # ps'" by (cases ps) auto
  obtain v u where p: "p = DB v u" by (cases p)
  have "bpHeadV t = v" using t ps p by simp
  moreover have "v \<in> flatIdx t"
    using t ps p by (auto simp: flatIdx_Trm)
  ultimately show ?thesis by simp
qed

text \<open>A flat-string containment (all-\<open>RP\<close> tail) bounds \<open>flatIdx\<close>: if
  \<open>flatBT t = s \<frown> flatBT c \<frown> b\<close> with \<open>b\<close> all-\<open>RP\<close> and \<open>s\<close> a prefix of the flat of
  some term \<open>c\<^sub>0\<close>, then every index of \<open>t\<close> lies in \<open>flatIdx c\<^sub>0 \<union> flatIdx c\<close>.\<close>

lemma flatIdx_scb_sub:
  assumes "flatBT t = s @ flatBT c @ b"
    and "flatBT c\<^sub>0 = s @ flatBT c\<^sub>1 @ b\<^sub>0"
    and "\<forall>x \<in> set b. x = RP"
  shows "flatIdx t \<subseteq> flatIdx c\<^sub>0 \<union> flatIdx c"
proof
  fix v assume "v \<in> flatIdx t"
  hence "Dsym v \<in> set (flatBT t)" by (simp add: flatIdx_def)
  hence "Dsym v \<in> set s \<union> set (flatBT c) \<union> set b" using assms(1) by auto
  moreover have "Dsym v \<notin> set b" using assms(3) by auto
  ultimately have "Dsym v \<in> set s \<union> set (flatBT c)" by auto
  moreover have "set s \<subseteq> set (flatBT c\<^sub>0)" using assms(2) by auto
  ultimately show "v \<in> flatIdx c\<^sub>0 \<union> flatIdx c" by (auto simp: flatIdx_def)
qed

text \<open>\<open>bpHeadT t\<close> is a sub-term, so its indices are among \<open>t\<close>'s.\<close>

lemma flatIdx_bpHeadT_sub:
  assumes "t = Trm (p # ps)"
  shows "flatIdx (bpHeadT t) \<subseteq> flatIdx t"
proof -
  obtain v u where p: "p = DB v u" by (cases p)
  have "bpHeadT t = u" using assms p by simp
  moreover have "flatIdx u \<subseteq> flatIdx (Trm (DB v u # ps))"
    by (cases ps) (auto simp: flatIdx_def)
  ultimately show ?thesis using assms p by simp
qed

text \<open>Surgery-position relationships (the mono \<open>m < j\<^sub>1\<close> branch of \<open>Mark\<close>): the
  mark \<open>m\<close> sits at or below the row-0 parent \<open>j\<^sub>p\<close> of \<open>j\<^sub>1\<close> and its
  admissibilization \<open>j\<^sub>-\<^sub>1 = Adm N j\<^sub>p\<close>.\<close>

lemma surg_parent_ge:
  assumes mk: "(N, m) \<in> Marked" and mono: "monoT N" and L: "1 < Lng N"
    and mlt: "m < Lng N - 1"
  shows "m \<le> parent N 0 (Lng N - 1)"
proof -
  have NT: "N \<in> T_PS" using mk by (simp add: Marked_def)
  have hp: "hasParent N 0 (Lng N - 1)" by (rule monoT_hasParent0_last[OF NT mono L])
  have nxt: "nextR N 0 (parent N 0 (Lng N - 1)) (Lng N - 1)"
    using hp unfolding hasParent_def parent_def by (rule theI')
  have le: "leR N 0 m (Lng N - 1)" using mk by (simp add: Marked_def)
  show ?thesis by (rule parent_max[OF hp nxt le mlt])
qed

lemma surg_adm_ge:
  assumes adm: "adm N m" and le: "m \<le> j"
  shows "m \<le> Adm N j"
proof (cases "adm N j")
  case True thus ?thesis using le by (simp add: Adm_def)
next
  case False
  hence Adm: "Adm N j = Max {j'. adm N j' \<and> j' < j}" by (simp add: Adm_def)
  have mlt: "m < j" using le False adm by (cases "m = j") auto
  have fin: "finite {j'. adm N j' \<and> j' < j}"
    by (rule finite_subset[of _ "{0..<j}"]) auto
  have mem: "m \<in> {j'. adm N j' \<and> j' < j}" using adm mlt by simp
  have "m \<le> Max {j'. adm N j' \<and> j' < j}" by (rule Max_ge[OF fin mem])
  thus ?thesis using Adm by simp
qed

text \<open>Every index of \<open>c\<^sub>2 = transC2 N\<close> lies in \<open>c\<^sub>1 = transC1 N\<close> or is one of the two
  explicit row-1 entries \<open>N\<^bsub>1,j\<^sub>1\<^esub>\<close>, \<open>N\<^bsub>1,j\<^sub>p\<^esub>\<close> introduced by the definition.  Every
  branch is \<open>D\<^bsub>v\<^esub>(\<dots>)\<close> with \<open>v = bpHeadV c\<^sub>1\<close>, and the inner term is built from
  \<open>t\<^sub>2 = bpHeadT c\<^sub>1\<close> (or sub-sums/last-principal of it) plus \<open>D\<^bsub>N\<^sub>1\<^sub>,\<^sub>j\<^sub>1\<^esub>\<close>/\<open>D\<^bsub>N\<^sub>1\<^sub>,\<^sub>j\<^sub>p\<^esub>\<close>.\<close>

lemma flatIdx_transC2_sub:
  assumes c1ne: "transC1 N \<noteq> 0\<^sub>B" and t2TB: "transT2 N \<in> T_B"
  shows "flatIdx (transC2 N)
           \<subseteq> flatIdx (transC1 N)
              \<union> {enat (entry N 1 (transJ1 N)), enat (entry N 1 (transJ0 N))}"
proof -
  obtain xs where xs: "transC1 N = Trm xs" by (cases "transC1 N")
  have "xs \<noteq> []" using c1ne xs by auto
  then obtain p ps where "xs = p # ps" by (cases xs) auto
  hence c1form: "transC1 N = Trm (p # ps)" using xs by simp
  \<comment> \<open>\<open>v = transV N = bpHeadV c\<^sub>1 \<in> flatIdx c\<^sub>1\<close>\<close>
  have vin: "transV N \<in> flatIdx (transC1 N)"
    unfolding transV_def by (rule bpHeadV_in_flatIdx[OF c1ne])
  \<comment> \<open>\<open>flatIdx t\<^sub>2 \<subseteq> flatIdx c\<^sub>1\<close>\<close>
  have t2sub: "flatIdx (transT2 N) \<subseteq> flatIdx (transC1 N)"
    unfolding transT2_def using flatIdx_bpHeadT_sub[OF c1form] by simp
  \<comment> \<open>\<open>SigmaB(take k (PB t\<^sub>2))\<close> and any \<open>PB t\<^sub>2 ! k\<close> have indices within \<open>t\<^sub>2\<close>\<close>
  have sigsub: "\<And>k. flatIdx (SigmaB (take k (PB (transT2 N)))) \<subseteq> flatIdx (transT2 N)"
  proof -
    fix k
    have "flatIdx (SigmaB (take k (PB (transT2 N))))
          = (\<Union>t \<in> set (take k (PB (transT2 N))). flatIdx t)" by (rule flatIdx_SigmaB)
    also have "\<dots> \<subseteq> (\<Union>t \<in> set (PB (transT2 N)). flatIdx t)"
      using set_take_subset by fastforce
    also have "\<dots> = flatIdx (SigmaB (PB (transT2 N)))" by (rule flatIdx_SigmaB[symmetric])
    also have "\<dots> = flatIdx (transT2 N)" using m_7_1_term_components[OF t2TB] by simp
    finally show "flatIdx (SigmaB (take k (PB (transT2 N)))) \<subseteq> flatIdx (transT2 N)" .
  qed
  have pjsub: "\<And>k. k < Lng (PB (transT2 N)) \<Longrightarrow> flatIdx (PB (transT2 N) ! k) \<subseteq> flatIdx (transT2 N)"
  proof -
    fix k assume "k < Lng (PB (transT2 N))"
    hence "PB (transT2 N) ! k \<in> set (PB (transT2 N))" by (rule nth_mem)
    hence "flatIdx (PB (transT2 N) ! k) \<subseteq> (\<Union>t \<in> set (PB (transT2 N)). flatIdx t)" by auto
    also have "\<dots> = flatIdx (transT2 N)"
      using flatIdx_SigmaB[symmetric] m_7_1_term_components[OF t2TB] by simp
    finally show "flatIdx (PB (transT2 N) ! k) \<subseteq> flatIdx (transT2 N)" .
  qed
  have bpHeadT_pj: "\<And>k. k < Lng (PB (transT2 N))
        \<Longrightarrow> flatIdx (bpHeadT (PB (transT2 N) ! k)) \<subseteq> flatIdx (transT2 N)"
  proof -
    fix k assume k: "k < Lng (PB (transT2 N))"
    have "PB (transT2 N) ! k \<in> set (PB (transT2 N))" using k by (rule nth_mem)
    then obtain q where q: "PB (transT2 N) ! k = Trm [q]" by (auto simp: PB_def)
    have "flatIdx (bpHeadT (PB (transT2 N) ! k)) \<subseteq> flatIdx (PB (transT2 N) ! k)"
      using flatIdx_bpHeadT_sub[OF q] by simp
    thus "flatIdx (bpHeadT (PB (transT2 N) ! k)) \<subseteq> flatIdx (transT2 N)"
      using pjsub[OF k] by blast
  qed
  \<comment> \<open>now bound \<open>flatIdx (transC2 N)\<close> branch by branch\<close>
  let ?j1 = "enat (entry N 1 (transJ1 N))"  let ?jp = "enat (entry N 1 (transJ0 N))"
  let ?Dj1 = "Dpt (enat (entry N 1 (transJ1 N))) 0\<^sub>B"
  have inner: "flatIdx (transC2 N) \<subseteq> insert (transV N) (flatIdx (transT2 N) \<union> {?j1, ?jp})"
  proof (cases "transCondI N \<or> transCondIII N \<or> transCondV N")
    case True
    hence "transC2 N = Dpt (transV N) (transT2 N +\<^sub>B ?Dj1)"
      by (simp add: transC2_def Let_def)
    thus ?thesis by (auto simp: flatIdx_addBT flatIdx_Dpt)
  next
    case notA: False
    show ?thesis
    proof (cases "transCondVI N")
      case True
      hence "transC2 N = Dpt (transV N) ?Dj1" using notA
        by (simp add: transC2_def Let_def)
      thus ?thesis by (auto simp: flatIdx_Dpt)
    next
      case notVI: False
      show ?thesis
      proof (cases "transT2 N = 0\<^sub>B")
        case True
        hence "transC2 N = Dpt (transV N) (Dpt (enat (entry N 1 (transJ0 N))) ?Dj1)"
          using notA notVI by (simp add: transC2_def Let_def)
        thus ?thesis by (auto simp: flatIdx_Dpt)
      next
        case t2nz: False
        have J1lt: "Lng (PB (transT2 N)) - 1 < Lng (PB (transT2 N))"
          using m_7_1_term_components[OF t2TB] t2nz by (cases "Lng (PB (transT2 N))") auto
        have b1: "flatIdx (SigmaB (take (Lng (PB (transT2 N)) - 1) (PB (transT2 N)))) \<subseteq> flatIdx (transT2 N)"
          by (rule sigsub)
        have b2: "flatIdx (bpHeadT (PB (transT2 N) ! (Lng (PB (transT2 N)) - 1))) \<subseteq> flatIdx (transT2 N)"
          by (rule bpHeadT_pj[OF J1lt])
        show ?thesis
        proof (cases "bpHeadV (PB (transT2 N) ! (Lng (PB (transT2 N)) - 1)) = enat (entry N 1 (transJ0 N))")
          case leftDj0: True
          hence "transC2 N = Dpt (transV N)
                   (SigmaB (take (Lng (PB (transT2 N)) - 1) (PB (transT2 N)))
                    +\<^sub>B Dpt (enat (entry N 1 (transJ0 N)))
                          (bpHeadT (PB (transT2 N) ! (Lng (PB (transT2 N)) - 1)) +\<^sub>B ?Dj1))"
            using notA notVI t2nz by (simp add: transC2_def Let_def)
          thus ?thesis using b1 b2 by (auto simp: flatIdx_addBT flatIdx_Dpt)
        next
          case False
          hence "transC2 N = Dpt (transV N)
                   (transT2 N +\<^sub>B Dpt (enat (entry N 1 (transJ0 N))) (transT2 N +\<^sub>B ?Dj1))"
            using notA notVI t2nz by (simp add: transC2_def Let_def)
          thus ?thesis by (auto simp: flatIdx_addBT flatIdx_Dpt)
        qed
      qed
    qed
  qed
  show ?thesis using inner vin t2sub by auto
qed


text \<open>\<open>transC2 N\<close> is a dfree term whenever \<open>c\<^sub>1 = transC1 N\<close> is a (nonzero) dfree
  principal term: every branch of @{thm [source] transC2_def} is \<open>D\<^bsub>v\<^esub>(\<dots>)\<close> built
  from \<open>v = transV N\<close> (the finite head index of \<open>c\<^sub>1\<close>), \<open>t\<^sub>2 = transT2 N\<close> (the
  dfree tail of \<open>c\<^sub>1\<close>), its sub-sums, and finite \<open>enat\<close> row-1 entries.\<close>

lemma dfree_transC2:
  assumes vne: "transV N \<noteq> \<infinity>" and t2df: "dfree_BT (transT2 N)"
  shows "dfree_BT (transC2 N)"
proof -
  define v where "v = transV N"
  define t2 where "t2 = transT2 N"
  have vne': "v \<noteq> \<infinity>" using vne v_def by simp
  have t2df': "dfree_BT t2" using t2df t2_def by simp
  let ?j1 = "transJ1 N"  let ?jp = "transJ0 N"
  let ?Dj1 = "Dpt (enat (entry N 1 ?j1)) 0\<^sub>B"
  have dfDj1: "dfree_BT ?Dj1" by simp
  show ?thesis
  proof (cases "transCondI N \<or> transCondIII N \<or> transCondV N")
    case True
    have "transC2 N = Dpt v (t2 +\<^sub>B ?Dj1)"
      using True by (simp add: transC2_def Let_def v_def t2_def transT2_def
                                transJ1_def transV_def)
    moreover have "dfree_BT (t2 +\<^sub>B ?Dj1)"
      using t2df' dfDj1 by (cases t2) auto
    ultimately show ?thesis using vne' by simp
  next
    case notA: False
    show ?thesis
    proof (cases "transCondVI N")
      case True
      have "transC2 N = Dpt v ?Dj1"
        using notA True by (simp add: transC2_def Let_def v_def transV_def
                                       transJ1_def)
      thus ?thesis using vne' dfDj1 by simp
    next
      case notVI: False
      show ?thesis
      proof (cases "t2 = 0\<^sub>B")
        case True
        have "transC2 N = Dpt v (Dpt (enat (entry N 1 ?jp)) ?Dj1)"
          using notA notVI True
          by (simp add: transC2_def Let_def v_def t2_def transV_def transT2_def
                        transJ1_def transJ0_def)
        thus ?thesis using vne' dfDj1 by simp
      next
        case t2nz: False
        define J1 where "J1 = Lng (PB t2) - 1"
        define pj where "pj = PB t2 ! J1"
        have df_sig: "dfree_BT (SigmaB (take J1 (PB t2)))"
          using t2df' by (cases t2) (auto simp: SigmaB_def PB_def dest!: in_set_takeD)
        have untrmne: "untrm t2 \<noteq> []" using t2nz by (cases t2) auto
        have J1lt: "J1 < Lng (PB t2)"
          using untrmne by (simp add: J1_def PB_def)
        have df_bphead: "dfree_BT (bpHeadT pj)"
        proof -
          have "pj \<in> set (PB t2)" using pj_def J1lt by simp
          hence "dfree_BT pj" using t2df' by (cases t2) (auto simp: PB_def)
          thus ?thesis by (cases pj rule: bpHeadT.cases) auto
        qed
        show ?thesis
        proof (cases "bpHeadV pj = enat (entry N 1 ?jp)")
          case leftDj0: True
          have "transC2 N = Dpt v
                  (SigmaB (take J1 (PB t2))
                    +\<^sub>B Dpt (enat (entry N 1 ?jp)) (bpHeadT pj +\<^sub>B ?Dj1))"
            using notA notVI t2nz leftDj0
            by (simp add: transC2_def Let_def v_def t2_def transV_def transT2_def
                          transJ1_def transJ0_def J1_def pj_def)
          moreover have "dfree_BT (bpHeadT pj +\<^sub>B ?Dj1)"
            using df_bphead dfDj1 by (cases "bpHeadT pj") auto
          moreover have "dfree_BT (SigmaB (take J1 (PB t2))
                    +\<^sub>B Dpt (enat (entry N 1 ?jp)) (bpHeadT pj +\<^sub>B ?Dj1))"
            using df_sig calculation(2)
            by (cases "SigmaB (take J1 (PB t2))") auto
          ultimately show ?thesis using vne' by simp
        next
          case False
          have "transC2 N = Dpt v
                  (t2 +\<^sub>B Dpt (enat (entry N 1 ?jp)) (t2 +\<^sub>B ?Dj1))"
            using notA notVI t2nz False
            by (simp add: transC2_def Let_def v_def t2_def transV_def transT2_def
                          transJ1_def transJ0_def J1_def pj_def)
          moreover have "dfree_BT (t2 +\<^sub>B ?Dj1)"
            using t2df' dfDj1 by (cases t2) auto
          moreover have "dfree_BT (t2 +\<^sub>B Dpt (enat (entry N 1 ?jp)) (t2 +\<^sub>B ?Dj1))"
            using t2df' calculation(2) by (cases t2) auto
          ultimately show ?thesis using vne' by simp
        qed
      qed
    qed
  qed
qed

text \<open>The \<open>Mark\<close>-index suffix-max bound: every \<open>D\<close>-index occurring in \<open>Mark N m\<close>
  is \<open>\<le>\<close> the maximum row-1 entry of \<open>N\<close> over the suffix columns \<open>{m .. Lng N - 1}\<close>.
  Strong \<open>Lng\<close>-induction, mirroring @{thm [source] Trans_Mark_invariant_aux};
  the surgery branch mirrors @{thm [source] trans_inv_B_hard}, bounding via
  @{thm [source] flatIdx_scb_sub} / @{thm [source] flatIdx_transC2_sub}.
  Empirically 0 violations over 9699 marked cases.\<close>

lemma Mark_flatIdx_bound:
  "(N, m) \<in> Marked \<longrightarrow> N \<in> RT_PS
   \<longrightarrow> (\<forall>v \<in> flatIdx (Mark N m). v \<le> enat (Max ((\<lambda>j. entry N 1 j) ` {m..Lng N - 1})))"
proof (induction N arbitrary: m rule: measure_induct_rule[where f=Lng])
  case (less N)
  show ?case
  proof (intro impI)
    assume mM: "(N, m) \<in> Marked" and NR: "N \<in> RT_PS"
    have NT: "N \<in> T_PS" using NR by (simp add: RT_PS_def)
    have Nne: "N \<noteq> []" using NT by (simp add: T_PS_def)
    have domK: "\<And>m. Trans_Mark_dom (Inr (N, m))" by (rule m_7_3_Mark_welldef[OF NR])
    \<comment> \<open>\<open>m \<le> Lng N - 1\<close> from the \<open>Marked\<close> reach relation\<close>
    have leM: "leR N 0 m (Lng N - 1)" using mM by (simp add: Marked_def)
    have mleN: "m < Lng N" using leM by (simp add: leR_def le0_def)
    have mle: "m \<le> Lng N - 1" using mleN by linarith
    have admN: "adm N m" using mM by (simp add: Marked_def)
    \<comment> \<open>the suffix-max abbreviation and its membership bound\<close>
    let ?B = "\<lambda>N m. enat (Max ((\<lambda>j. entry N 1 j) ` {m..Lng N - 1}))"
    have ble: "\<And>k. m \<le> k \<Longrightarrow> k \<le> Lng N - 1 \<Longrightarrow> enat (entry N 1 k) \<le> ?B N m"
    proof -
      fix k assume "m \<le> k" and "k \<le> Lng N - 1"
      hence "entry N 1 k \<in> (\<lambda>j. entry N 1 j) ` {m..Lng N - 1}" by auto
      hence "entry N 1 k \<le> Max ((\<lambda>j. entry N 1 j) ` {m..Lng N - 1})"
        by (simp add: Max_ge)
      thus "enat (entry N 1 k) \<le> ?B N m" by simp
    qed
    have zle: "(0::enat) \<le> ?B N m" by simp
    show "\<forall>v \<in> flatIdx (Mark N m). v \<le> ?B N m"
    proof (cases "Lng N = 1")
      case True
      \<comment> \<open>(A) length 1: \<open>N = [(v,v)]\<close>, \<open>m = 0\<close>\<close>
      obtain v where Nv: "N = [(v, v)]"
        using m_6_6_oneColumn[OF NT] NR True by auto
      have m0: "m = 0" using mle True by simp
      have kv: "Mark N m = (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)"
        using Nv Mark_singleton by simp
      have ev: "entry N 1 0 = v" using Nv by (simp add: entry_def)
      show ?thesis
      proof
        fix x assume "x \<in> flatIdx (Mark N m)"
        hence "x \<in> {enat v}" using kv by (cases "v = 0") auto
        hence "x = enat v" by simp
        moreover have "enat v \<le> ?B N m"
          using ble[of 0] m0 mle ev True by simp
        ultimately show "x \<le> ?B N m" by simp
      qed
    next
      case notone: False
      have L: "1 < Lng N" using Nne notone by (cases N) auto
      have Lgt1: "\<not> Lng N \<le> Suc 0" using L by simp
      let ?j1 = "Lng N - 1"
      show ?thesis
      proof (cases "monoT N")
        case mono: True
        have predRT: "Pred N \<in> RT_PS" by (rule Pred_RT_PS[OF NR])
        have predb: "Pred N = butlast N" using L by (simp add: Pred_def)
        have LPred: "Lng (Pred N) = Lng N - 1" using predb by simp
        have LPredlt: "Lng (Pred N) < Lng N" using LPred L by simp
        \<comment> \<open>row-1 entries agree on the kept columns\<close>
        have entryP: "\<And>j. j \<le> Lng N - 2 \<Longrightarrow> entry (Pred N) 1 j = entry N 1 j"
        proof -
          fix j assume "j \<le> Lng N - 2"
          hence "j < Lng N - 1" using L by linarith
          hence "j < length (butlast N)" using L by simp
          thus "entry (Pred N) 1 j = entry N 1 j"
            using predb by (simp add: entry_def nth_butlast)
        qed
        show ?thesis
        proof (cases "Trans (Pred N) = 0\<^sub>B")
          case t1z: True
          \<comment> \<open>(B) \<open>t\<^sub>1 = 0\<close>\<close>
          have kv: "Mark N m = (if m = 0 then Dpt 0 (Dpt (enat (entry N 1 ?j1)) 0\<^sub>B)
                                else Dpt (enat (entry N 1 ?j1)) 0\<^sub>B)"
            using Mark.psimps[OF domK] NR Lgt1 mono t1z by (simp add: Let_def)
          show ?thesis
          proof
            fix x assume "x \<in> flatIdx (Mark N m)"
            hence "x \<in> {0, enat (entry N 1 ?j1)} \<or> x \<in> {enat (entry N 1 ?j1)}"
              using kv by (cases "m = 0") (auto simp: flatIdx_Dpt zero_enat_def)
            hence "x = 0 \<or> x = enat (entry N 1 ?j1)" by auto
            thus "x \<le> ?B N m"
              using zle ble[of ?j1] mle by auto
          qed
        next
          case t1ne: False
          \<comment> \<open>(B) \<open>t\<^sub>1 \<noteq> 0\<close>\<close>
          have hp: "hasParent N 0 ?j1" by (rule monoT_hasParent0_last[OF NT mono L])
          let ?bv = "entry N 1 (Lng N - 1)"
          define jp where "jp = parent N 0 (Lng N - 1)"
          define jm1 where "jm1 = Adm N jp"
          \<comment> \<open>identify the def's \<open>c\<^sub>1\<close>/\<open>c\<^sub>2\<close> with the \<open>trans*\<close> components\<close>
          have transJ1eq: "transJ1 N = ?j1" by (simp add: transJ1_def)
          have transJ0eq: "transJ0 N = jp" by (simp add: transJ0_def transJ1_def jp_def)
          have transJm1eq: "transJm1 N = jm1"
            by (simp add: transJm1_def jm1_def transJ0eq)
          \<comment> \<open>the surgery define-chain, mirroring @{thm [source] trans_inv_B_hard}\<close>
          define c1 where "c1 = Mark (Pred N) (Adm N jp)"
          define vv where "vv = bpHeadV c1"
          define tt2 where "tt2 = bpHeadT c1"
          define JJ1 where "JJ1 = Lng (PB tt2) - 1"
          define pj where "pj = PB tt2 ! JJ1"
          define ldj where "ldj = (bpHeadV pj = enat (entry N 1 jp))"
          define tt3 where "tt3 = (if ldj then SigmaB (take JJ1 (PB tt2)) else tt2)"
          define tt4 where "tt4 = (if ldj then bpHeadT pj else tt2)"
          define c2 where "c2 = (if transCondI N \<or> transCondIII N \<or> transCondV N
                         then Dpt vv (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)
                         else if transCondVI N
                         then Dpt vv (Dpt (enat ?bv) 0\<^sub>B)
                         else if tt2 = 0\<^sub>B
                         then Dpt vv (Dpt (enat (entry N 1 jp)) (Dpt (enat ?bv) 0\<^sub>B))
                         else Dpt vv (tt3 +\<^sub>B Dpt (enat (entry N 1 jp))
                                            (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)))"
          \<comment> \<open>\<open>c\<^sub>1 = transC1 N\<close>, \<open>c\<^sub>2 = transC2 N\<close>\<close>
          have c1eqT: "c1 = transC1 N"
            by (simp add: c1_def transC1_def transJm1eq jm1_def)
          have c2eqT: "c2 = transC2 N"
            unfolding c2_def transC2_def Let_def
              vv_def tt2_def c1eqT transV_def transT2_def
              JJ1_def pj_def ldj_def tt3_def tt4_def transJ1_def transJ0eq
            by simp
          have c1eq: "c1 = Mark (Pred N) jm1"
            by (simp add: c1_def jm1_def)
          \<comment> \<open>\<open>(Pred N, jm1) \<in> Marked\<close>; \<open>c\<^sub>1\<close> nonzero and \<open>t\<^sub>2 \<in> T\<^sub>B\<close>\<close>
          have mkjm1: "(Pred N, jm1) \<in> Marked"
            using Marked_Pred_Adm[OF NT L hp] jp_def jm1_def by simp
          have NP: "N \<in> PT_PS" using NT mono by (simp add: PT_PS_def)
          have J1pos: "transJ1 N > 0" using L by (simp add: transJ1_def)
          have T1ne: "transT1 N \<noteq> 0\<^sub>B" using t1ne by (simp add: transT1_def)
          have pc1: "Lng (PB (transC1 N)) = 1"
            by (rule transC1_single_principal[OF NR NP J1pos T1ne])
          have c1ne: "transC1 N \<noteq> 0\<^sub>B"
          proof
            assume "transC1 N = 0\<^sub>B"
            thus False using pc1 by (simp add: PB_def)
          qed
          have c1TB: "transC1 N \<in> T_B"
            using m_7_3_Mark_in_T_B[OF predRT mkjm1] c1eq c1eqT by simp
          have c1Dpt: "transC1 N = Dpt (transV N) (transT2 N)"
            using principal_reconstruct[OF pc1]
            by (simp add: transV_def transT2_def)
          have t2TB: "transT2 N \<in> T_B"
            using c1TB unfolding c1Dpt by (auto simp: T_B_def)
          \<comment> \<open>flatIdx of \<open>c\<^sub>2\<close> bound (def brick)\<close>
          have c2sub: "flatIdx c2
              \<subseteq> flatIdx (transC1 N) \<union> {enat (entry N 1 ?j1), enat (entry N 1 jp)}"
            using flatIdx_transC2_sub[OF c1ne t2TB]
            by (simp add: c2eqT transJ1eq transJ0eq)
          \<comment> \<open>position facts: \<open>m \<le> jp \<le> j\<^sub>1\<close> and \<open>m \<le> jm1\<close>\<close>
          have jplt: "jp < ?j1"
          proof -
            have "nextR N 0 jp ?j1"
              using hp unfolding hasParent_def parent_def jp_def by (rule theI')
            thus ?thesis by (simp add: nextR_def nextrel0_def)
          qed
          have jple: "jp \<le> ?j1" using jplt by simp
          \<comment> \<open>the suffix-max for \<open>Pred N\<close> at an index \<open>i \<ge> m\<close> is below \<open>?B N m\<close>\<close>
          have predB_le: "\<And>i. m \<le> i \<Longrightarrow> i \<le> Lng N - 2 \<Longrightarrow> ?B (Pred N) i \<le> ?B N m"
          proof -
            fix i assume mi: "m \<le> i" and iN: "i \<le> Lng N - 2"
            have sub: "{i..Lng (Pred N) - 1} \<subseteq> {m..Lng N - 1}"
              using LPred mi L by auto
            have fin: "finite ((\<lambda>j. entry N 1 j) ` {m..Lng N - 1})" by simp
            have ne: "{i..Lng (Pred N) - 1} \<noteq> {}" using iN LPred L by auto
            have imgeq: "(\<lambda>j. entry (Pred N) 1 j) ` {i..Lng (Pred N) - 1}
                  = (\<lambda>j. entry N 1 j) ` {i..Lng (Pred N) - 1}"
            proof (rule image_cong[OF refl])
              fix j assume "j \<in> {i..Lng (Pred N) - 1}"
              hence "j \<le> Lng (Pred N) - 1" by simp
              hence jb: "j \<le> Lng N - 2" using LPred by linarith
              show "entry (Pred N) 1 j = entry N 1 j" by (rule entryP[OF jb])
            qed
            have "Max ((\<lambda>j. entry (Pred N) 1 j) ` {i..Lng (Pred N) - 1})
                  = Max ((\<lambda>j. entry N 1 j) ` {i..Lng (Pred N) - 1})"
              using imgeq by simp
            also have "\<dots> \<le> Max ((\<lambda>j. entry N 1 j) ` {m..Lng N - 1})"
            proof (rule Max_mono)
              show "(\<lambda>j. entry N 1 j) ` {i..Lng (Pred N) - 1}
                    \<subseteq> (\<lambda>j. entry N 1 j) ` {m..Lng N - 1}"
                using sub by auto
              show "(\<lambda>j. entry N 1 j) ` {i..Lng (Pred N) - 1} \<noteq> {}"
                using ne by auto
              show "finite ((\<lambda>j. entry N 1 j) ` {m..Lng N - 1})" by simp
            qed
            finally show "?B (Pred N) i \<le> ?B N m" by simp
          qed
          \<comment> \<open>IH on \<open>Pred N\<close>\<close>
          have IHpred: "\<And>i. (Pred N, i) \<in> Marked
              \<Longrightarrow> \<forall>v \<in> flatIdx (Mark (Pred N) i). v \<le> ?B (Pred N) i"
            using less.IH[OF LPredlt] predRT by blast
          show ?thesis
          proof (cases "m < ?j1")
            case mlt_false: False
            \<comment> \<open>(B) \<open>m = j\<^sub>1\<close>: \<open>Mark N m = D\<^bsub>N\<^bsub>1,j\<^sub>1\<^esub>\<^esub> 0\<close>\<close>
            have kv: "Mark N m = Dpt (enat (entry N 1 ?j1)) 0\<^sub>B"
              using Mark.psimps[OF domK] NR Lgt1 mono t1ne mlt_false
              unfolding Let_def jp_def[symmetric]
              by simp
            show ?thesis
            proof
              fix x assume "x \<in> flatIdx (Mark N m)"
              hence "x = enat (entry N 1 ?j1)" using kv by (simp add: flatIdx_Dpt)
              thus "x \<le> ?B N m" using ble[of ?j1] mle by simp
            qed
          next
            case mlt: True
            \<comment> \<open>(B) surgery branch, \<open>m < j\<^sub>1\<close>\<close>
            define c0 where "c0 = Mark (Pred N) m"
            define sm1 where
              "sm1 = (SOME sb. scb_decomp c0 (fst sb) (flatBT c1) (snd sb))"
            have mark_val_raw: "Mark N m = (if (Mark (Pred N) m, c1) \<in> MarkedB
                  then unflatBT
                         (fst (SOME sb. scb_decomp (Mark (Pred N) m) (fst sb)
                                          (flatBT c1) (snd sb))
                          @ flatBT c2
                          @ snd (SOME sb. scb_decomp (Mark (Pred N) m) (fst sb)
                                            (flatBT c1) (snd sb)))
                  else Dpt (enat ?bv) 0\<^sub>B)"
              using Mark.psimps[OF domK] NR Lgt1 mono t1ne mlt
              unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
                        tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
                        ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
                        c2_def[symmetric]
              by simp
            have mark_val: "Mark N m = (if (c0, c1) \<in> MarkedB
                  then unflatBT (fst sm1 @ flatBT c2 @ snd sm1)
                  else Dpt (enat ?bv) 0\<^sub>B)"
              using mark_val_raw by (simp add: c0_def sm1_def)
            show ?thesis
            proof (cases "(c0, c1) \<in> MarkedB")
              case mbc_false: False
              have kv: "Mark N m = Dpt (enat (entry N 1 ?j1)) 0\<^sub>B"
                using mark_val mbc_false by simp
              show ?thesis
              proof
                fix x assume "x \<in> flatIdx (Mark N m)"
                hence "x = enat (entry N 1 ?j1)" using kv by (simp add: flatIdx_Dpt)
                thus "x \<le> ?B N m" using ble[of ?j1] mle by simp
              qed
            next
              case mbc: True
              \<comment> \<open>\<open>(Pred N, m) \<in> Marked\<close> and its \<open>c\<^sub>1\<close>-shape\<close>
              have mPred: "(Pred N, m) \<in> Marked"
                by (rule Marked_Pred[OF NT L mM mlt])
              \<comment> \<open>\<open>c\<^sub>0 = Mark (Pred N) m\<close> is principal\<close>
              have c1form: "transC1 N = Trm [DB (transV N) (transT2 N)]"
                using c1Dpt by simp
              have c1p: "c1 = Trm [DB (transV N) (transT2 N)]"
                using c1form c1eqT by simp
              \<comment> \<open>the \<open>SOME\<close> decomposition of \<open>c\<^sub>0\<close>\<close>
              have exsm: "\<exists>sb. scb_decomp c0 (fst sb) (flatBT c1) (snd sb)"
                using mbc unfolding MarkedB_def by auto
              have dsm: "scb_decomp c0 (fst sm1) (flatBT c1) (snd sm1)"
                unfolding sm1_def by (rule someI_ex[OF exsm])
              \<comment> \<open>\<open>c\<^sub>0\<close> is a single principal term\<close>
              have c1Dsym: "flatBT c1 = Dsym (transV N) # flatBT (transT2 N)"
                using c1eqT c1Dpt by simp
              have c0ne: "c0 \<noteq> 0\<^sub>B"
              proof
                assume z: "c0 = 0\<^sub>B"
                have "flatBT c0 = fst sm1 @ flatBT c1 @ snd sm1"
                  using dsm by (simp add: scb_decomp_def)
                hence "Dsym (transV N) \<in> set (flatBT c0)"
                  using c1Dsym by simp
                thus False using z by simp
              qed
              \<comment> \<open>\<open>c\<^sub>0\<close> is a marked left member of \<open>Trans (Pred N) \<noteq> 0\<close>, hence principal\<close>
              have mb0: "(Trans (Pred N), c0) \<in> MarkedB"
                using m_7_3_Trans_Mark_MarkedB[OF predRT mPred] c0_def by simp
              obtain s0 b0 where d0: "scb_decomp (Trans (Pred N)) s0 (flatBT c0) b0"
                using mb0 by (auto simp: MarkedB_def)
              have t1neT: "Trans (Pred N) \<noteq> Trm []" using t1ne by simp
              have iptc0: "isPTB_str (flatBT c0)"
                using d0 t1neT by (simp add: scb_decomp_def)
              then obtain pc0 where pc0l: "flatBT c0 = flatBP pc0"
                  and pc0d: "dfree_BP pc0"
                by (auto simp: isPTB_str_def)
              have c0p: "c0 = Trm [pc0]"
              proof -
                have "flatBT c0 = flatBT (Trm [pc0])" using pc0l by simp
                thus ?thesis by (rule m_7_flatBT_inj)
              qed
              \<comment> \<open>\<open>c\<^sub>2\<close> is a single principal dfree term, hence \<open>isPTB_str\<close>\<close>
              have vne: "transV N \<noteq> \<infinity>" using c1TB c1Dpt by (auto simp: T_B_def)
              have t2df: "dfree_BT (transT2 N)"
                using c1TB c1Dpt by (auto simp: T_B_def)
              have c2df: "dfree_BT c2"
                using dfree_transC2[OF vne t2df] c2eqT by simp
              have c2pc1: "Lng (PB c2) = 1"
                using transC2_single_principal c2eqT by simp
              have c2recon: "c2 = Dpt (bpHeadV c2) (bpHeadT c2)"
                by (rule principal_reconstruct[OF c2pc1])
              obtain pc2 where c2p: "c2 = Trm [pc2]"
                using c2recon by (metis BT.exhaust untrm.simps)
              have iptc2: "isPTB_str (flatBT (Trm [pc2]))"
              proof -
                have "dfree_BT (Trm [pc2])" using c2df c2p by simp
                then obtain p where "pc2 = p" and "dfree_BP p" by auto
                thus ?thesis by (auto simp: isPTB_str_def)
              qed
              \<comment> \<open>reconstruct the replaced \<open>Mark\<close> value as a principal term\<close>
              have dsm': "scb_decomp (Trm [pc0]) (fst sm1)
                            (flatBT (Trm [DB (transV N) (transT2 N)])) (snd sm1)"
                using dsm c0p c1p by simp
              obtain pm where pmf: "flatBP pm = fst sm1 @ flatBT (Trm [pc2]) @ snd sm1"
                  and pmd: "scb_decomp (Trm [pm]) (fst sm1) (flatBT (Trm [pc2])) (snd sm1)"
                using scb_replace_principal_BP[OF dsm' iptc2] by blast
              have markM: "Mark N m = Trm [pm]"
              proof -
                have "flatBT (Trm [pm]) = fst sm1 @ flatBT c2 @ snd sm1"
                  using pmf c2p by simp
                thus ?thesis
                  using mark_val mbc unflatBT_flat[of "Trm [pm]"] by simp
              qed
              \<comment> \<open>\<open>flatBT (Mark N m) = fst sm1 @ flatBT c2 @ snd sm1\<close>\<close>
              have flatMark: "flatBT (Mark N m) = fst sm1 @ flatBT c2 @ snd sm1"
                using markM pmf c2p by simp
              have flatc0: "flatBT c0 = fst sm1 @ flatBT c1 @ snd sm1"
                using dsm by (simp add: scb_decomp_def)
              have brp: "\<forall>x \<in> set (snd sm1). x = RP"
                using dsm by (simp add: scb_decomp_def)
              \<comment> \<open>the containment bound\<close>
              have fsub: "flatIdx (Mark N m) \<subseteq> flatIdx c0 \<union> flatIdx c2"
                by (rule flatIdx_scb_sub[OF flatMark flatc0 brp])
              \<comment> \<open>bound \<open>flatIdx c0\<close> via the IH on \<open>Pred N\<close>\<close>
              have c0bound: "\<forall>v \<in> flatIdx c0. v \<le> ?B N m"
              proof
                fix v assume "v \<in> flatIdx c0"
                hence "v \<le> ?B (Pred N) m"
                  using IHpred[OF mPred] c0_def by simp
                also have "\<dots> \<le> ?B N m"
                proof -
                  have "m \<le> Lng N - 2" using mlt L by linarith
                  thus ?thesis using predB_le[of m] by simp
                qed
                finally show "v \<le> ?B N m" .
              qed
              \<comment> \<open>bound \<open>flatIdx c2\<close>\<close>
              have mjp: "m \<le> jp"
                using surg_parent_ge[OF mM mono L mlt] jp_def by simp
              have mjm1: "m \<le> jm1"
                using surg_adm_ge[OF admN mjp] jm1_def by simp
              have jm1lt: "jm1 \<le> Lng N - 2"
              proof -
                have "jm1 \<le> jp" using adm_Adm_le jm1_def by simp
                thus ?thesis using jplt by linarith
              qed
              have c1bound: "\<forall>v \<in> flatIdx (transC1 N). v \<le> ?B N m"
              proof
                fix v assume "v \<in> flatIdx (transC1 N)"
                hence "v \<in> flatIdx (Mark (Pred N) jm1)" using c1eq c1eqT by simp
                hence "v \<le> ?B (Pred N) jm1"
                  using IHpred[OF mkjm1] by simp
                also have "\<dots> \<le> ?B N m"
                  using predB_le[of jm1] mjm1 jm1lt by simp
                finally show "v \<le> ?B N m" .
              qed
              have c2bound: "\<forall>v \<in> flatIdx c2. v \<le> ?B N m"
              proof
                fix v assume "v \<in> flatIdx c2"
                hence "v \<in> flatIdx (transC1 N)
                       \<or> v = enat (entry N 1 ?j1) \<or> v = enat (entry N 1 jp)"
                  using c2sub by auto
                thus "v \<le> ?B N m"
                proof (elim disjE)
                  assume "v \<in> flatIdx (transC1 N)"
                  thus ?thesis using c1bound by simp
                next
                  assume "v = enat (entry N 1 ?j1)"
                  thus ?thesis using ble[of ?j1] mle by simp
                next
                  assume "v = enat (entry N 1 jp)"
                  thus ?thesis using ble[of jp] mjp jple by simp
                qed
              qed
              show ?thesis using fsub c0bound c2bound by auto
            qed
          qed
        qed
      next
        case nmono: False
        \<comment> \<open>(C) multiT branch\<close>
        have nzN: "\<not> zeroT N" using notone by (auto simp: zeroT_def)
        have muN: "multiT N" using nzN nmono by (simp add: multiT_def)
        have cut: "0 < Pcut N \<and> Pcut N \<le> ?j1" using Pcut_le[OF L] by simp
        let ?PJ = "drop (Pcut N) N"
        have PJeq: "P N ! (Lng (P N) - 1) = ?PJ"
          by (rule trans_multiT_last_component(1)[OF NT muN])
        have Pne: "P N \<noteq> []" by (rule P_nonempty)
        have J1lt: "Lng (P N) - 1 < Lng (P N)" using Pne by (cases "P N") auto
        have PJRT: "?PJ \<in> RT_PS"
          using m_6_6_P_reduced[OF NT] NR J1lt PJeq by auto
        have PJT: "?PJ \<in> T_PS" using PJRT by (simp add: RT_PS_def)
        have LPJ: "Lng ?PJ = Lng N - Pcut N" by simp
        have LPJlt: "Lng ?PJ < Lng N" using LPJ cut L by linarith
        have cmle: "Pcut N \<le> m" by (rule multi_Marked_last_component(1)[OF NT muN mM])
        \<comment> \<open>identify the def's PJ / j0\<close>
        have c1: "(N \<notin> RT_PS) = False" using NR by simp
        have c2: "(?j1 = 0) = False" using L by simp
        have c3: "monoT N = False" using nmono by simp
        have meq2: "m - (?j1 - Lng (drop (Pcut N) N) + 1) = m - Pcut N"
        proof -
          have "?j1 - Lng ?PJ + 1 = Pcut N"
            using LPJ cut by linarith
          thus ?thesis by simp
        qed
        have markM: "Mark N m = (if ?PJ = [(0, 0)] then Dpt 0 0\<^sub>B
                                 else Mark ?PJ (m - Pcut N))"
        proof -
          have raw: "Mark N m =
              (if P N ! (Lng (P N) - 1) = [(0, 0)] then Dpt 0 0\<^sub>B
               else Mark (P N ! (Lng (P N) - 1))
                      (m - (?j1 - Lng (P N ! (Lng (P N) - 1)) + 1)))"
            by (subst Mark.psimps[OF domK]) (simp only: c1 c2 c3 if_False Let_def)
          show ?thesis unfolding raw PJeq meq2 ..
        qed
        \<comment> \<open>row-1 entries: \<open>?PJ\<close> is a suffix of \<open>N\<close>\<close>
        have entryPJ: "\<And>k. k < Lng ?PJ \<Longrightarrow> entry ?PJ 1 k = entry N 1 (Pcut N + k)"
          by (simp add: entry_def)
        show ?thesis
        proof (cases "?PJ = [(0, 0)]")
          case True
          have kv: "Mark N m = Dpt 0 0\<^sub>B" using markM True by simp
          show ?thesis
          proof
            fix x assume "x \<in> flatIdx (Mark N m)"
            hence "x = 0" using kv by (simp add: flatIdx_Dpt zero_enat_def)
            thus "x \<le> ?B N m" using zle by simp
          qed
        next
          case False
          have kv: "Mark N m = Mark ?PJ (m - Pcut N)" using markM False by simp
          have mPJ: "(?PJ, m - Pcut N) \<in> Marked"
            by (rule multi_Marked_last_component(2)[OF NT muN mM])
          have IHJ: "\<forall>v \<in> flatIdx (Mark ?PJ (m - Pcut N)). v \<le> ?B ?PJ (m - Pcut N)"
            using less.IH[OF LPJlt] mPJ PJRT by blast
          \<comment> \<open>\<open>?B ?PJ (m - Pcut N) \<le> ?B N m\<close>\<close>
          have shiftB: "?B ?PJ (m - Pcut N) \<le> ?B N m"
          proof -
            have mPcut: "m - Pcut N \<le> Lng ?PJ - 1"
              using mle LPJ cut by linarith
            have ne: "{m - Pcut N..Lng ?PJ - 1} \<noteq> {}" using mPcut by auto
            have shift_img:
              "(\<lambda>j. entry ?PJ 1 j) ` {m - Pcut N..Lng ?PJ - 1}
               = (\<lambda>j. entry N 1 j) ` {m..Lng N - 1}"
            proof
              show "(\<lambda>j. entry ?PJ 1 j) ` {m - Pcut N..Lng ?PJ - 1}
                    \<subseteq> (\<lambda>j. entry N 1 j) ` {m..Lng N - 1}"
              proof
                fix y assume "y \<in> (\<lambda>j. entry ?PJ 1 j) ` {m - Pcut N..Lng ?PJ - 1}"
                then obtain k where k: "k \<in> {m - Pcut N..Lng ?PJ - 1}"
                    and yk: "y = entry ?PJ 1 k" by auto
                have klt: "k < Lng ?PJ" using k LPJ cut L by auto
                have "y = entry N 1 (Pcut N + k)" using yk entryPJ[OF klt] by simp
                moreover have "Pcut N + k \<in> {m..Lng N - 1}"
                  using k cmle LPJ cut by auto
                ultimately show "y \<in> (\<lambda>j. entry N 1 j) ` {m..Lng N - 1}" by auto
              qed
            next
              show "(\<lambda>j. entry N 1 j) ` {m..Lng N - 1}
                    \<subseteq> (\<lambda>j. entry ?PJ 1 j) ` {m - Pcut N..Lng ?PJ - 1}"
              proof
                fix y assume "y \<in> (\<lambda>j. entry N 1 j) ` {m..Lng N - 1}"
                then obtain j where j: "j \<in> {m..Lng N - 1}" and yj: "y = entry N 1 j"
                  by auto
                have jge: "Pcut N \<le> j" using j cmle by auto
                define k where "k = j - Pcut N"
                have klt: "k < Lng ?PJ" using j LPJ cut k_def by auto
                have "entry ?PJ 1 k = entry N 1 (Pcut N + k)" by (rule entryPJ[OF klt])
                moreover have "Pcut N + k = j" using jge k_def by simp
                ultimately have "entry ?PJ 1 k = y" using yj by simp
                moreover have "k \<in> {m - Pcut N..Lng ?PJ - 1}"
                  using j klt k_def cmle by auto
                ultimately show "y \<in> (\<lambda>j. entry ?PJ 1 j) ` {m - Pcut N..Lng ?PJ - 1}"
                  by auto
              qed
            qed
            show ?thesis using shift_img by simp
          qed
          show ?thesis
          proof
            fix x assume "x \<in> flatIdx (Mark N m)"
            hence "x \<in> flatIdx (Mark ?PJ (m - Pcut N))" using kv by simp
            hence "x \<le> ?B ?PJ (m - Pcut N)" using IHJ by simp
            also have "\<dots> \<le> ?B N m" using shiftB .
            finally show "x \<le> ?B N m" .
          qed
        qed
      qed
    qed
  qed
qed


section \<open>§7.3 NAbound: condition-VI structural bound (Lemma B) and assembly\<close>

text \<open>Lemma B: when \<open>j\<^sub>0\<close> is non-\<open>M\<close>-admissible, the indices in \<open>(Adm M j\<^sub>0, j\<^sub>0]\<close> are
  all non-admissible, so by the \<open>nadm \<Longrightarrow> nextR\<^sub>1 \<Longrightarrow> strict row-1 increase\<close> chain
  row-1 is non-decreasing on \<open>[Adm M j\<^sub>0, j\<^sub>0]\<close>; hence its max there is \<open>M\<^bsub>1,j\<^sub>0\<^esub>\<close>.\<close>

lemma viB_suffix_max:
  assumes nadm0: "\<not> adm M j0" and j0lt: "j0 < Lng M"
  shows "Max ((\<lambda>j. entry M 1 j) ` {Adm M j0 .. j0}) \<le> entry M 1 j0"
proof -
  let ?jm1 = "Adm M j0"
  have admdef: "?jm1 = Max {j'. adm M j' \<and> j' < j0}"
    using nadm0 by (simp add: Adm_def)
  have fin: "finite {j'. adm M j' \<and> j' < j0}"
    by (rule finite_subset[of _ "{0..<j0}"]) auto
  \<comment> \<open>every index strictly above \<open>?jm1\<close> up to \<open>j\<^sub>0\<close> is non-admissible\<close>
  have nonadm_seg: "\<And>j'. ?jm1 < j' \<Longrightarrow> j' \<le> j0 \<Longrightarrow> \<not> adm M j'"
  proof -
    fix j' assume a: "?jm1 < j'" and b: "j' \<le> j0"
    show "\<not> adm M j'"
    proof (cases "j' = j0")
      case True thus ?thesis using nadm0 by simp
    next
      case False
      hence jlt: "j' < j0" using b by simp
      show ?thesis
      proof
        assume "adm M j'"
        hence "j' \<in> {j'. adm M j' \<and> j' < j0}" using jlt by simp
        hence "j' \<le> ?jm1" using fin admdef by simp
        thus False using a by simp
      qed
    qed
  qed
  \<comment> \<open>the strict-increase step\<close>
  have step: "\<And>j. ?jm1 \<le> j \<Longrightarrow> j < j0 \<Longrightarrow> entry M 1 j < entry M 1 (Suc j)"
  proof -
    fix j assume jge: "?jm1 \<le> j" and jlt: "j < j0"
    have "?jm1 < Suc j" using jge by simp
    moreover have "Suc j \<le> j0" using jlt by simp
    ultimately have "\<not> adm M (Suc j)" by (rule nonadm_seg)
    hence nadmS: "nadm M (Suc j)" by (simp add: adm_def)
    have "Suc j \<le> Lng M" using jlt j0lt by simp
    hence "nextR M 1 (Suc j - 1) (Suc j)" using nadmS by (simp add: nadm_def)
    hence "nextrel1 M j (Suc j)" by (simp add: nextR_def)
    thus "entry M 1 j < entry M 1 (Suc j)" by (simp add: nextrel1_def)
  qed
  \<comment> \<open>hence monotone up to \<open>j\<^sub>0\<close>\<close>
  have mono: "\<And>a. ?jm1 \<le> a \<Longrightarrow> a \<le> j0 \<Longrightarrow> entry M 1 a \<le> entry M 1 j0"
  proof -
    fix a assume A: "?jm1 \<le> a" and B: "a \<le> j0"
    from B A show "entry M 1 a \<le> entry M 1 j0"
    proof (induction "j0 - a" arbitrary: a)
      case 0 hence "a = j0" by simp thus ?case by simp
    next
      case (Suc d)
      have alt: "a < j0" using Suc.hyps(2) Suc.prems(1) by linarith
      have "entry M 1 a < entry M 1 (Suc a)" by (rule step[OF Suc.prems(2) alt])
      moreover have "entry M 1 (Suc a) \<le> entry M 1 j0"
      proof (rule Suc.hyps(1))
        show "d = j0 - Suc a" using Suc.hyps(2) by simp
        show "Suc a \<le> j0" using alt by simp
        show "?jm1 \<le> Suc a" using Suc.prems(2) by simp
      qed
      ultimately show ?case by simp
    qed
  qed
  have adm0: "adm M 0" by (simp add: adm_def nadm_def nextR_def nextrel1_def)
  have j0pos: "0 < j0" using nadm0 adm0 by (cases "j0 = 0") auto
  have nemax: "{j'. adm M j' \<and> j' < j0} \<noteq> {}" using adm0 j0pos by auto
  have jm1lt: "?jm1 < j0"
  proof -
    have "Max {j'. adm M j' \<and> j' < j0} \<in> {j'. adm M j' \<and> j' < j0}"
      by (rule Max_in[OF fin nemax])
    thus ?thesis using admdef by simp
  qed
  have fin2: "finite ((\<lambda>j. entry M 1 j) ` {?jm1 .. j0})" by simp
  have ne2: "(\<lambda>j. entry M 1 j) ` {?jm1 .. j0} \<noteq> {}" using jm1lt by auto
  have "\<forall>x \<in> (\<lambda>j. entry M 1 j) ` {?jm1 .. j0}. x \<le> entry M 1 j0"
    using mono by auto
  thus ?thesis using fin2 ne2 by (simp add: Max_le_iff)
qed

text \<open>NAbound: the non-admissible condition-VI Mark second-index bound, discharged
  by the keystone @{thm [source] Mark_flatIdx_bound} (on \<open>Pred M\<close> at \<open>j\<^sub>-\<^sub>1\<close>) and
  Lemma B @{thm [source] viB_suffix_max}.\<close>

lemma NAbound_holds:
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS" and T1: "transT1 M \<noteq> 0\<^sub>B"
    and VI: "transCondVI M" and nadm: "\<not> adm M (transJ0 M)" and t2nz: "transT2 M \<noteq> 0\<^sub>B"
  shows "bpHeadV (transT2 M) < enat (entry M 1 (transJ1 M))"
proof -
  have MT: "M \<in> T_PS" using MP by (simp add: PT_PS_def)
  have mono: "monoT M" using MP by (simp add: PT_PS_def)
  have VIc: "entry M 1 (Lng M - 1) > 0
           \<and> entry M 1 (parent M 0 (Lng M - 1)) + 1 = entry M 1 (Lng M - 1)
           \<and> parent M 0 (Lng M - 1) + 1 = Lng M - 1"
    using VI by (simp add: transCondVI_def)
  have L: "1 < Lng M" using VIc by linarith
  let ?j0 = "transJ0 M"  let ?j1 = "transJ1 M"  let ?jm1 = "transJm1 M"
  have j1eq: "?j1 = Lng M - 1" by (simp add: transJ1_def)
  have j0eq: "?j0 = parent M 0 (Lng M - 1)" by (simp add: transJ0_def transJ1_def)
  have jm1eq: "?jm1 = Adm M ?j0" by (simp add: transJm1_def transJ0_def transJ1_def)
  have j0val: "?j0 = Lng M - 2" using VIc j0eq by linarith
  have j0lt: "?j0 < Lng M" using j0val L by simp
  have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have hp: "hasParent M 0 (Lng M - 1)" by (rule monoT_hasParent0_last[OF MT mono L])
  have mkjm1: "(Pred M, ?jm1) \<in> Marked"
    using Marked_Pred_Adm[OF MT L hp] j0eq jm1eq by simp
  have c1eq: "transC1 M = Mark (Pred M) ?jm1" by (simp add: transC1_def transJm1_def)
  \<comment> \<open>\<open>c\<^sub>1 \<noteq> 0\<close> and principal-list form\<close>
  have J1p: "transJ1 M > 0" using L by (simp add: transJ1_def)
  have pc1: "Lng (PB (transC1 M)) = 1" by (rule transC1_single_principal[OF MR MP J1p T1])
  have c1ne: "transC1 M \<noteq> 0\<^sub>B" using pc1 by (auto simp: PB_def)
  obtain p ps where c1form: "transC1 M = Trm (p # ps)"
  proof -
    obtain xs where xs: "transC1 M = Trm xs" by (cases "transC1 M")
    have "xs \<noteq> []" using c1ne xs by auto
    then obtain p ps where "xs = p # ps" by (cases xs) auto
    thus thesis using xs that by simp
  qed
  \<comment> \<open>\<open>bpHeadV t\<^sub>2 \<in> flatIdx c\<^sub>1\<close>\<close>
  have hv_in: "bpHeadV (transT2 M) \<in> flatIdx (transC1 M)"
  proof -
    have "bpHeadV (transT2 M) \<in> flatIdx (transT2 M)" by (rule bpHeadV_in_flatIdx[OF t2nz])
    moreover have "flatIdx (transT2 M) \<subseteq> flatIdx (transC1 M)"
      unfolding transT2_def using flatIdx_bpHeadT_sub[OF c1form] by simp
    ultimately show ?thesis by auto
  qed
  \<comment> \<open>Lemma A on \<open>Pred M\<close> at \<open>?jm1\<close>\<close>
  have LPred: "Lng (Pred M) - 1 = ?j0" using j0val L by (simp add: Pred_def)
  have bound: "\<forall>v \<in> flatIdx (Mark (Pred M) ?jm1).
                  v \<le> enat (Max ((\<lambda>j. entry (Pred M) 1 j) ` {?jm1 .. Lng (Pred M) - 1}))"
    using Mark_flatIdx_bound mkjm1 predRT by blast
  \<comment> \<open>entries of \<open>Pred M\<close> agree with \<open>M\<close> up to \<open>?j0\<close>\<close>
  have entryagree: "\<And>j. j \<le> ?j0 \<Longrightarrow> entry (Pred M) 1 j = entry M 1 j"
  proof -
    fix j assume "j \<le> ?j0"
    hence "j < Lng M - 1" using j0val L by simp
    thus "entry (Pred M) 1 j = entry M 1 j"
      using L by (simp add: Pred_def entry_def nth_butlast)
  qed
  have maxeq: "(\<lambda>j. entry (Pred M) 1 j) ` {?jm1 .. Lng (Pred M) - 1}
             = (\<lambda>j. entry M 1 j) ` {?jm1 .. ?j0}"
    by (rule image_cong) (use LPred entryagree in auto)
  \<comment> \<open>Lemma B\<close>
  have lemB: "Max ((\<lambda>j. entry M 1 j) ` {?jm1 .. ?j0}) \<le> entry M 1 ?j0"
    using viB_suffix_max[OF nadm j0lt] jm1eq by simp
  \<comment> \<open>combine to \<open>\<le> M\<^bsub>1,j\<^sub>0\<^esub>\<close>\<close>
  have step1: "bpHeadV (transT2 M) \<le> enat (entry M 1 ?j0)"
  proof -
    have "bpHeadV (transT2 M)
          \<le> enat (Max ((\<lambda>j. entry (Pred M) 1 j) ` {?jm1 .. Lng (Pred M) - 1}))"
      using hv_in c1eq bound by auto
    also have "\<dots> = enat (Max ((\<lambda>j. entry M 1 j) ` {?jm1 .. ?j0}))" using maxeq by simp
    also have "\<dots> \<le> enat (entry M 1 ?j0)" using lemB by simp
    finally show ?thesis .
  qed
  \<comment> \<open>\<open>M\<^bsub>1,j\<^sub>0\<^esub> < M\<^bsub>1,j\<^sub>1\<^esub>\<close>\<close>
  have lt: "entry M 1 ?j0 < entry M 1 ?j1"
  proof -
    have "entry M 1 ?j0 + 1 = entry M 1 ?j1" using VIc j0eq j1eq by simp
    thus ?thesis by simp
  qed
  show ?thesis using step1 lt by (metis enat_ord_simps(2) le_less_trans)
qed

end
