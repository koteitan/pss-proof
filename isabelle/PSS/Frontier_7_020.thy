theory Frontier_7_020
  imports Support_7_017
begin

text \<open>Brick 3 (the join sweep): in a \<open>CM\<close>-joined component list closed by the
  outer \<open>RP\<close>, an occurrence of a principal string \<open>flatBP cp\<close> with all-\<open>RP\<close>
  tail \<open>b\<close> lies inside a single component, and only the LAST one — crossing a
  component boundary would give the occurrence a proper prefix of negative
  \<open>flatinj_dsum\<close> (the component suffix), contradicting
  @{thm [source] flatinj_prefix_nonneg_BP}.  The component is then replaced
  via the supplied (inductive) replacement hypothesis.\<close>

lemma scbimg_join:
  assumes IHr: "\<And>r s b. r \<in> set rs \<Longrightarrow> flatBP r = s @ flatBP cp @ b
                  \<Longrightarrow> \<forall>x \<in> set b. x = RP
                  \<Longrightarrow> \<exists>r'. flatBP r' = s @ flatBP cp' @ b"
    and eq: "concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP] = s @ flatBP cp @ b"
    and rb: "\<forall>x \<in> set b. x = RP"
  shows "\<exists>rs'. length rs' = length rs
             \<and> concat (map (\<lambda>r. CM # flatBP r) rs') @ [RP] = s @ flatBP cp' @ b"
  using IHr eq rb
proof (induction rs arbitrary: s b)
  case Nil
  \<comment> \<open>\<open>[RP] = s @ flatBP cp @ b\<close>: but \<open>flatBP cp\<close> starts with \<open>Dsym\<close>.\<close>
  obtain w cb where cpw: "cp = DB w cb" by (cases cp) auto
  show ?case
    using Nil.prems(2) cpw by (cases s) auto
next
  case (Cons r0 rs)
  obtain w cb where cpw: "cp = DB w cb" by (cases cp) auto
  have fchd: "flatBP cp = Dsym w # flatBT cb" using cpw by simp
  \<comment> \<open>peel the leading \<open>CM\<close>\<close>
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
  \<comment> \<open>split at the end of \<open>flatBP r0\<close>\<close>
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
    \<comment> \<open>occurrence beyond \<open>r0\<close>: recurse into the tail join\<close>
    have IHtail: "\<And>r s b. r \<in> set rs \<Longrightarrow> flatBP r = s @ flatBP cp @ b
                    \<Longrightarrow> \<forall>x \<in> set b. x = RP
                    \<Longrightarrow> \<exists>r'. flatBP r' = s @ flatBP cp' @ b"
    proof -
      fix r s b
      assume "r \<in> set rs" "flatBP r = s @ flatBP cp @ b" "\<forall>x \<in> set b. x = RP"
      thus "\<exists>r'. flatBP r' = s @ flatBP cp' @ b"
        using Cons.prems(1)[of r s b] by simp
    qed
    have tail: "concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP] = us @ flatBP cp @ b"
      using True by simp
    have "\<exists>rs'. length rs' = length rs
              \<and> concat (map (\<lambda>r. CM # flatBP r) rs') @ [RP] = us @ flatBP cp' @ b"
      by (rule Cons.IH[OF IHtail tail Cons.prems(3)])
    then obtain rs' where rs': "length rs' = length rs"
        "concat (map (\<lambda>r. CM # flatBP r) rs') @ [RP] = us @ flatBP cp' @ b" by blast
    have "concat (map (\<lambda>r. CM # flatBP r) (r0 # rs')) @ [RP]
          = CM # flatBP r0 @ us @ flatBP cp' @ b" using rs' by simp
    also have "\<dots> = s @ flatBP cp' @ b" using ss True by simp
    finally show ?thesis using rs' by (intro exI[of _ "r0 # rs'"]) simp
  next
    case False
    with split have inr0: "flatBP r0 = s1 @ us"
        and rest: "us @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP] = flatBP cp @ b"
      by auto
    \<comment> \<open>split \<open>fc\<close> against \<open>us\<close>\<close>
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
      obtain r0' where r0': "flatBP r0' = s1 @ flatBP cp' @ vs"
        using Cons.prems(1)[of r0 s1 vs] r0eq vsRP by auto
      have "concat (map (\<lambda>r. CM # flatBP r) [r0']) @ [RP]
            = CM # s1 @ flatBP cp' @ vs @ [RP]" using r0' by simp
      also have "\<dots> = s @ flatBP cp' @ b" using ss True rsnil by simp
      finally show ?thesis using rsnil by (intro exI[of _ "[r0']"]) simp
    next
      case False
      with split2 have fcsplit: "flatBP cp = us @ vs"
          and vsb: "vs @ b = concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]" by auto
      \<comment> \<open>crossing: \<open>us\<close> is a PROPER suffix-piece of \<open>r0\<close> and a proper prefix of
          \<open>fc\<close> with negative depth-sum — contradiction\<close>
      have vsne: "vs \<noteq> []"
      proof
        assume v0: "vs = []"
        hence "flatBP cp = us" using fcsplit by simp
        hence "b = concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]" using vsb v0 by simp
        \<comment> \<open>then the whole tail join is in \<open>b\<close>: \<open>rs = []\<close> as above, so
            \<open>flatBP r0 = s1 @ flatBP cp\<close> with \<open>vs = []\<close> — covered by the
            inside-\<open>r0\<close> case, contradicting \<open>False\<close>\<close>
        hence "flatBP cp @ vs = us \<and> b = vs @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]"
          using fcsplit v0 vsb by simp
        thus False using False by simp
      qed
      have usne_or: "us = [] \<or> us \<noteq> []" by simp
      show ?thesis
      proof (cases "us = []")
        case True
        \<comment> \<open>\<open>fc = vs\<close> begins exactly at the tail join, whose head is \<open>CM\<close> or \<open>RP\<close>\<close>
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


text \<open>The image-existence lemma (§7.3 value-invariant prerequisite): replacing
  the principal middle of an scb-style split (all-\<open>RP\<close> tail) by any other
  principal string stays inside the image of \<open>flatBT\<close>.  Empirically 0/7,224
  (python/scb_image_audit.py).\<close>

lemma scbimg_image_BT:
  "flatBT t = s @ flatBP cp @ b \<Longrightarrow> \<forall>x \<in> set b. x = RP
   \<Longrightarrow> \<exists>t'. flatBT t' = s @ flatBP cp' @ b"
  and scbimg_image_BP:
  "flatBP p = s @ flatBP cp @ b \<Longrightarrow> \<forall>x \<in> set b. x = RP
   \<Longrightarrow> \<exists>p'. flatBP p' = s @ flatBP cp' @ b"
proof (induct t and p arbitrary: s b and s b rule: flatBT_flatBP.induct)
  case (1 s b)
  obtain w cb where cpw: "cp = DB w cb" by (cases cp) auto
  show ?case using 1(1) cpw by (cases s) auto
next
  case (2 p s b)
  have "flatBP p = s @ flatBP cp @ b" using 2(2) by simp
  then obtain p' where "flatBP p' = s @ flatBP cp' @ b"
    using 2(1) 2(3) by blast
  thus ?case by (intro exI[of _ "Trm [p']"]) simp
next
  case (3 p q ps s b)
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
    \<comment> \<open>occurrence in the join: brick 3\<close>
    have IHr: "\<And>r s b. r \<in> set (q # ps) \<Longrightarrow> flatBP r = s @ flatBP cp @ b
                 \<Longrightarrow> \<forall>x \<in> set b. x = RP
                 \<Longrightarrow> \<exists>r'. flatBP r' = s @ flatBP cp' @ b"
    proof -
      fix r s b
      assume rin: "r \<in> set (q # ps)" and req: "flatBP r = s @ flatBP cp @ b"
        and rrb: "\<forall>x \<in> set b. x = RP"
      show "\<exists>r'. flatBP r' = s @ flatBP cp' @ b"
        using 3(2) rin req rrb by blast
    qed
    have "\<exists>rs'. length rs' = length (q # ps)
              \<and> concat (map (\<lambda>r. CM # flatBP r) rs') @ [RP] = us @ flatBP cp' @ b"
    proof (rule scbimg_join[where cp = cp])
      fix r s b
      assume "r \<in> set (q # ps)" "flatBP r = s @ flatBP cp @ b"
        "\<forall>x \<in> set b. x = RP"
      thus "\<exists>r'. flatBP r' = s @ flatBP cp' @ b" by (rule IHr)
    next
      show "concat (map (\<lambda>r. CM # flatBP r) (q # ps)) @ [RP]
            = us @ flatBP cp @ b" using True by simp
    next
      show "\<forall>x \<in> set b. x = RP" by (rule 3(4))
    qed
    then obtain rs' where rs': "length rs' = length (q # ps)"
        "concat (map (\<lambda>r. CM # flatBP r) rs') @ [RP] = us @ flatBP cp' @ b"
      by blast
    obtain r1' rest' where rsc: "rs' = r1' # rest'"
      using rs' by (cases rs') auto
    have "flatBT (Trm (p # r1' # rest'))
          = LP # (flatBP p @ concat (map (\<lambda>r. CM # flatBP r) rs')) @ [RP]"
      using rsc by simp
    also have "\<dots> = LP # flatBP p @ (concat (map (\<lambda>r. CM # flatBP r) rs') @ [RP])"
      by simp
    also have "\<dots> = LP # flatBP p @ us @ flatBP cp' @ b" using rs'(2) by simp
    also have "\<dots> = s @ flatBP cp' @ b" using ss True by simp
    finally show ?thesis by blast
  next
    case False
    with split have inp: "flatBP p = s1 @ us"
        and rest: "us @ ?JOIN @ [RP] = flatBP cp @ b" by auto
    \<comment> \<open>occurrence (purportedly) inside the FIRST component: impossible\<close>
    from append_eq_append_conv2[THEN iffD1, OF rest]
    obtain vs where split2:
        "us = flatBP cp @ vs \<and> vs @ ?JOIN @ [RP] = b
       \<or> us @ vs = flatBP cp \<and> ?JOIN @ [RP] = vs @ b" by blast
    have False
    proof (cases "us = flatBP cp @ vs \<and> vs @ ?JOIN @ [RP] = b")
      case True
      hence "CM \<in> set b" by auto
      thus False using 3(4) by auto
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
          thus False using 3(4) by auto
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
  case (4 u a s b)
  show ?case
  proof (cases "s = []")
    case True
    have "flatBP (DB u a) @ [] = flatBP cp @ b" using 4(2) True by simp
    hence "flatBP (DB u a) = flatBP cp \<and> [] = b"
      using flatinj_flatBP_cancel by blast
    thus ?thesis using True by (intro exI[of _ cp']) simp
  next
    case False
    have "Dsym u # flatBT a = s @ flatBP cp @ b" using 4(2) by simp
    then obtain s1 where ss: "s = Dsym u # s1" and aeq: "flatBT a = s1 @ flatBP cp @ b"
      using False by (cases s) auto
    obtain a' where "flatBT a' = s1 @ flatBP cp' @ b"
      using 4(1)[OF aeq 4(3)] by blast
    thus ?thesis using ss by (intro exI[of _ "DB u a'"]) simp
  qed
qed


text \<open>The corrected scb replacement (A12, now with the image hypothesis
  DISCHARGED by @{thm [source] scbimg_image_BT}): replacing the principal
  middle of an scb-decomposition yields a term with the corresponding
  scb-decomposition.\<close>

lemma scb_replace_principal:
  assumes d: "scb_decomp t s (flatBT (Trm [cp])) b"
    and pc': "isPTB_str (flatBT (Trm [cp']))"
  shows "\<exists>t'. flatBT t' = s @ flatBT (Trm [cp']) @ b
            \<and> scb_decomp t' s (flatBT (Trm [cp'])) b"
proof -
  from d have eq: "flatBT t = s @ flatBP cp @ b"
    and rb: "\<forall>x \<in> set b. x = RP"
    by (auto simp: scb_decomp_def)
  obtain t' where t': "flatBT t' = s @ flatBP cp' @ b"
    using scbimg_image_BT[OF eq rb] by blast
  have "scb_decomp t' s (flatBT (Trm [cp'])) b"
    unfolding scb_decomp_def using t' pc' rb by simp
  thus ?thesis using t' by auto
qed

text \<open>\<open>dfree\<close> reads off the flat string: no \<open>Dsym \<infinity>\<close> letters.  Transfers
  \<open>T\<^sub>B\<close>-membership to terms built by string surgery.\<close>

lemma dfree_flat_BT: "dfree_BT t \<longleftrightarrow> (\<forall>v. Dsym v \<in> set (flatBT t) \<longrightarrow> v \<noteq> \<infinity>)"
  and dfree_flat_BP: "dfree_BP p \<longleftrightarrow> (\<forall>v. Dsym v \<in> set (flatBP p) \<longrightarrow> v \<noteq> \<infinity>)"
proof (induct t and p rule: flatBT_flatBP.induct)
  case 1 show ?case by simp
next
  case (2 p) thus ?case by simp
next
  case (3 p q ps)
  have "dfree_BT (Trm (p # q # ps))
        \<longleftrightarrow> (dfree_BP p \<and> (\<forall>r \<in> set (q # ps). dfree_BP r))" by simp
  also have "\<dots> \<longleftrightarrow> ((\<forall>v. Dsym v \<in> set (flatBP p) \<longrightarrow> v \<noteq> \<infinity>)
        \<and> (\<forall>r \<in> set (q # ps). \<forall>v. Dsym v \<in> set (flatBP r) \<longrightarrow> v \<noteq> \<infinity>))"
    using 3(1) 3(2) by blast
  also have "\<dots> \<longleftrightarrow> (\<forall>v. Dsym v \<in> set (flatBT (Trm (p # q # ps))) \<longrightarrow> v \<noteq> \<infinity>)"
  proof -
    have sf: "set (flatBT (Trm (p # q # ps)))
          = {LP, RP} \<union> set (flatBP p)
            \<union> (\<Union>r \<in> set (q # ps). insert CM (set (flatBP r)))"
      by auto
    show ?thesis unfolding sf by auto
  qed
  finally show ?case .
next
  case (4 u a) thus ?case by auto
qed


text \<open>Marked-pair bookkeeping for the \<open>Trans\<close>/\<open>Mark\<close> value invariant: the
  recursion's \<open>Mark (Pred M) \<dots>\<close> calls stay inside \<open>Marked\<close>.  Empirically
  0/1,575 and 0/2,313 (anchor: ancestor-interval property
  @{thm [source] m_5_1_ancestor_tree_1} + verbatim prefix transfer
  @{thm [source] le0_prefix_agree} / @{thm [source] nextR1_pred_agree}).\<close>

lemma adm_Pred_transfer:
  assumes L: "1 < Lng M" and mlt: "m < Lng M - 1" and a: "adm M m"
  shows "adm (Pred M) m"
proof -
  have pb: "Pred M = butlast M" using L by (simp add: Pred_def)
  have LP: "Lng (Pred M) = Lng M - 1" using pb by simp
  show ?thesis
  proof (cases "m + 1 < Lng M - 1")
    case True
    have "\<not> nadm (Pred M) m"
    proof
      assume n: "nadm (Pred M) m"
      have "\<not> m > Lng (Pred M)" using mlt LP by simp
      hence pair: "nextR (Pred M) 1 (m - 1) m \<and> nextR (Pred M) 1 m (m + 1)"
        using n by (simp add: nadm_def)
      have b1: "m - 1 \<le> Lng M - 2" and b2: "m \<le> Lng M - 2"
        and b3: "m + 1 \<le> Lng M - 2" using True by simp_all
      have "nextR M 1 (m - 1) m \<and> nextR M 1 m (m + 1)"
        using pair nextR1_pred_agree[OF L b1 b2] nextR1_pred_agree[OF L b2 b3]
        by simp
      hence "nadm M m" by (simp add: nadm_def)
      thus False using a by (simp add: adm_def)
    qed
    thus ?thesis by (simp add: adm_def)
  next
    case False
    \<comment> \<open>\<open>m + 1 \<ge> Lng (Pred M)\<close>: the second \<open>nextR\<close> of \<open>nadm\<close> is out of range\<close>
    have "\<not> nextR (Pred M) 1 m (m + 1)"
      using False LP by (auto simp: nextR_def nextrel1_def)
    hence "\<not> nadm (Pred M) m" using mlt LP by (auto simp: nadm_def)
    thus ?thesis by (simp add: adm_def)
  qed
qed

lemma Marked_Pred:
  assumes MT: "M \<in> T_PS" and L: "1 < Lng M"
    and mM: "(M, m) \<in> Marked" and mlt: "m < Lng M - 1"
  shows "(Pred M, m) \<in> Marked"
proof -
  from mM have admM: "adm M m" and leM: "leR M 0 m (Lng M - 1)"
    by (auto simp: Marked_def)
  have pb: "Pred M = butlast M" using L by (simp add: Pred_def)
  have LP: "Lng (Pred M) = Lng M - 1" using pb by simp
  have PT: "Pred M \<in> T_PS"
  proof -
    have "0 < Lng (Pred M)" using LP L by simp
    thus ?thesis using length_greater_0_conv by (fastforce simp: T_PS_def)
  qed
  have le2: "leR M 0 m (Lng M - 2)"
    by (rule m_5_1_ancestor_tree_1[OF MT leM]) (use mlt in linarith)+
  have leP: "le0 (Pred M) m (Lng M - 2)"
  proof (rule le0_prefix_agree[of "Lng M - 2" M "Pred M"])
    show "\<And>j. j \<le> Lng M - 2 \<Longrightarrow> M ! j = Pred M ! j"
      using pb L by (simp add: nth_butlast)
    show "Lng M - 2 < Lng M" using L by linarith
    show "Lng M - 2 < Lng (Pred M)" using LP L by linarith
    show "m \<le> Lng M - 2" using mlt by linarith
    show "Lng M - 2 \<le> Lng M - 2" by simp
    show "le0 M m (Lng M - 2)" using le2 by (simp add: leR_def)
  qed
  have admP: "adm (Pred M) m" by (rule adm_Pred_transfer[OF L mlt admM])
  show ?thesis using PT admP leP LP
    by (simp add: Marked_def leR_def numeral_2_eq_2)
qed

lemma Marked_Pred_Adm:
  assumes MT: "M \<in> T_PS" and L: "1 < Lng M"
    and hp: "hasParent M 0 (Lng M - 1)"
  shows "(Pred M, Adm M (parent M 0 (Lng M - 1))) \<in> Marked"
proof -
  let ?j1 = "Lng M - 1"  let ?jp = "parent M 0 ?j1"  let ?a = "Adm M ?jp"
  have parR: "nextR M 0 ?jp ?j1"
    using hp unfolding hasParent_def parent_def by (rule theI')
  have jplt: "?jp < ?j1" using parR by (simp add: nextR_def nextrel0_def)
  have jpb: "?jp \<le> Lng M - 1" using jplt by simp
  have admA: "adm M ?a" by (rule adm_Adm_adm)
  have aLe: "?a \<le> ?jp" by (rule adm_Adm_le)
  have alt: "?a < ?j1" using aLe jplt by linarith
  \<comment> \<open>row-1 ancestry to \<open>?jp\<close>, then the row-0 parent step to \<open>?j1\<close>\<close>
  have le1a: "leR M 1 ?a ?jp" by (rule adm_row1_ancestry[OF MT jpb])
  have le0a: "leR M 0 ?a ?jp" by (rule m_le1_imp_le0[OF le1a])
  have "le0 M ?a ?j1"
  proof -
    have st: "nextrel0 M ?jp ?j1" using parR by (simp add: nextR_def)
    have "(nextrel0 M)\<^sup>*\<^sup>* ?a ?jp" using le0a by (simp add: leR_def le0_def)
    hence "(nextrel0 M)\<^sup>*\<^sup>* ?a ?j1" using st by (rule rtranclp.rtrancl_into_rtrancl)
    moreover have "?a < Lng M" using alt by linarith
    moreover have "?j1 < Lng M" using L by linarith
    ultimately show ?thesis by (simp add: le0_def)
  qed
  hence leMa: "leR M 0 ?a ?j1" by (simp add: leR_def)
  show ?thesis
    by (rule Marked_Pred[OF MT L _ alt])
       (use MT admA leMa in \<open>simp add: Marked_def\<close>)
qed


text \<open>Marked bookkeeping for the (C) multiT branch: a marked column of a multi
  \<open>M\<close> lies in the LAST \<open>P\<close>-component (directly from \<open>Pcut\<close> being the LEAST
  anchored cut), and restricts to a marked column of it.
  Empirically 0/6,080.\<close>

lemma multi_Marked_last_component:
  assumes MT: "M \<in> T_PS" and mu: "multiT M"
    and mM: "(M, m) \<in> Marked"
  shows "Pcut M \<le> m" and "(drop (Pcut M) M, m - Pcut M) \<in> Marked"
proof -
  have L: "1 < Lng M" by (rule multiT_imp_Lng_gt1[OF MT mu])
  from mM have admM: "adm M m" and leM: "leR M 0 m (Lng M - 1)"
    by (auto simp: Marked_def)
  have mlt: "m < Lng M" using leM by (simp add: leR_def le0_def)
  have m0: "0 < m"
  proof (rule ccontr)
    assume "\<not> 0 < m"
    hence "leR M 0 0 (Lng M - 1)" using leM by simp
    thus False using m_6_2_not_multi_iff_le[OF MT] mu by simp
  qed
  show cut: "Pcut M \<le> m"
    unfolding Pcut_def
    by (rule Least_le) (use m0 mlt leM in linarith)
  \<comment> \<open>now the component view\<close>
  let ?j0 = "Pcut M"  let ?j1 = "Lng M - 1"  let ?K = "drop ?j0 M"
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have L0: "0 < Lng M" using L by linarith
  have segK: "?K = seg M ?j0 ?j1" using seg_to_last_eq_drop[OF L0] by simp
  have cb: "0 < ?j0 \<and> ?j0 \<le> ?j1" using Pcut_le[OF L] by simp
  have j1lt: "?j1 < Lng M" using L by simp
  have LK: "Lng ?K = Lng M - ?j0" by simp
  have KT: "?K \<in> T_PS"
  proof -
    have "0 < Lng ?K" using LK cb L by linarith
    thus ?thesis using length_greater_0_conv by (fastforce simp: T_PS_def)
  qed
  \<comment> \<open>le0 restricts to the component window\<close>
  have leK: "le0 ?K (m - ?j0) (Lng ?K - 1)"
  proof -
    have b1: "m - ?j0 \<le> ?j1 - ?j0" using mlt by linarith
    have b2: "?j1 - ?j0 \<le> ?j1 - ?j0" by simp
    have "le0 (seg M ?j0 ?j1) (m - ?j0) (?j1 - ?j0)
          \<longleftrightarrow> le0 M (?j0 + (m - ?j0)) (?j0 + (?j1 - ?j0))"
      by (rule adm_le0_seg[OF j1lt b1 b2]) (use cb in linarith)
    moreover have "?j0 + (m - ?j0) = m" using cut by simp
    moreover have "?j0 + (?j1 - ?j0) = ?j1" using cb by linarith
    ultimately have "le0 (seg M ?j0 ?j1) (m - ?j0) (?j1 - ?j0)"
      using leM by (simp add: leR_def)
    moreover have "Lng ?K - 1 = ?j1 - ?j0" using LK cb by linarith
    ultimately show ?thesis using segK by simp
  qed
  \<comment> \<open>admissibility restricts (last component: the right edges align)\<close>
  have admK: "adm ?K (m - ?j0)"
  proof -
    have "\<not> nadm ?K (m - ?j0)"
    proof
      assume n: "nadm ?K (m - ?j0)"
      have mb: "m - ?j0 \<le> Lng ?K" using LK mlt by linarith
      hence pair: "nextR ?K 1 (m - ?j0 - 1) (m - ?j0)
                 \<and> nextR ?K 1 (m - ?j0) (m - ?j0 + 1)"
        using n by (simp add: nadm_def)
      have r2: "nextrel1 ?K (m - ?j0) (m - ?j0 + 1)"
        using pair by (simp add: nextR_def)
      have ub: "m - ?j0 + 1 < Lng ?K" using r2 by (simp add: nextrel1_def)
      have b0: "m - ?j0 - 1 < Lng (seg M ?j0 ?j1)"
        and b1: "m - ?j0 < Lng (seg M ?j0 ?j1)"
        and b2: "m - ?j0 + 1 < Lng (seg M ?j0 ?j1)"
        using ub segK by simp_all
      have t1: "nextrel1 M (?j0 + (m - ?j0 - 1)) (?j0 + (m - ?j0))"
        using pair adm_nextrel1_seg[OF j1lt b0 b1] segK by (simp add: nextR_def)
      have t2: "nextrel1 M (?j0 + (m - ?j0)) (?j0 + (m - ?j0 + 1))"
        using r2 adm_nextrel1_seg[OF j1lt b1 b2] segK by simp
      have e1: "?j0 + (m - ?j0) = m" using cut by simp
      have "nextrel1 M (m - 1) m"
      proof (cases "m - ?j0 = 0")
        case True
        \<comment> \<open>then \<open>t1\<close> is \<open>nextrel1 M m m\<close>, impossible\<close>
        have "nextrel1 M m m" using t1 True e1 by simp
        thus ?thesis by (simp add: nextrel1_def)
      next
        case False
        have "?j0 + (m - ?j0 - 1) = m - 1" using cut False by linarith
        thus ?thesis using t1 e1 by simp
      qed
      moreover have "nextrel1 M m (m + 1)" using t2 e1 cut by simp
      ultimately have "nadm M m" by (simp add: nadm_def nextR_def)
      thus False using admM by (simp add: adm_def)
    qed
    thus ?thesis by (simp add: adm_def)
  qed
  show "(?K, m - ?j0) \<in> Marked"
    using KT admK leK by (simp add: Marked_def leR_def)
qed


text \<open>\<open>MarkedB\<close> depends only on the LAST principal component: the all-\<open>RP\<close>
  tail pins the marked occurrence into the last component (the
  @{thm [source] scbimg_join} crossing analysis, as an extractor), and a
  component-level occurrence lifts into any term sharing that last component
  (in particular across \<open>+\<^sub>B\<close>: the (C) branch of the \<open>Trans\<close>/\<open>Mark\<close>
  invariant).\<close>

lemma scbext_join:
  assumes eq: "concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP] = s @ flatBP cp @ b"
    and rb: "\<forall>x \<in> set b. x = RP"
  shows "\<exists>sc bc. flatBP (last rs) = sc @ flatBP cp @ bc \<and> (\<forall>x \<in> set bc. x = RP)"
  using eq rb
proof (induction rs arbitrary: s b)
  case Nil
  obtain w cb where cpw: "cp = DB w cb" by (cases cp) auto
  show ?case using Nil.prems(1) cpw by (cases s) auto
next
  case (Cons r0 rs)
  obtain w cb where cpw: "cp = DB w cb" by (cases cp) auto
  have fchd: "flatBP cp = Dsym w # flatBT cb" using cpw by simp
  have eq0: "CM # flatBP r0 @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]
             = s @ flatBP cp @ b"
    using Cons.prems(1) by simp
  have sne: "s \<noteq> []"
  proof
    assume "s = []"
    hence "CM = Dsym w" using eq0 fchd by simp
    thus False by simp
  qed
  then obtain s1 where ss: "s = CM # s1" using eq0 by (cases s) auto
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
    have rsne: "rs \<noteq> []"
    proof
      assume "rs = []"
      hence "[RP] = us @ flatBP cp @ b" using True by simp
      thus False using fchd by (cases us) auto
    qed
    have "\<exists>sc bc. flatBP (last rs) = sc @ flatBP cp @ bc \<and> (\<forall>x \<in> set bc. x = RP)"
      using Cons.IH True Cons.prems(2) by blast
    thus ?thesis using rsne by simp
  next
    case False
    with split have inr0: "flatBP r0 = s1 @ us"
        and rest: "us @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP] = flatBP cp @ b" by auto
    from append_eq_append_conv2[THEN iffD1, OF rest[symmetric]]
    obtain vs where split2:
        "flatBP cp = us @ vs \<and> vs @ b = concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]
       \<or> flatBP cp @ vs = us \<and> b = vs @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]"
      by blast
    show ?thesis
    proof (cases "flatBP cp @ vs = us \<and> b = vs @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]")
      case True
      have ball: "\<forall>x \<in> set (vs @ concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]). x = RP"
        using True Cons.prems(2) by simp
      have rsnil: "rs = []"
      proof (cases rs)
        case (Cons r1 rs1)
        hence "CM \<in> set (concat (map (\<lambda>r. CM # flatBP r) rs))" by simp
        thus ?thesis using ball by auto
      qed simp
      have vsRP: "\<forall>x \<in> set vs. x = RP" using ball by auto
      have "flatBP r0 = s1 @ flatBP cp @ vs" using inr0 True by simp
      thus ?thesis using rsnil vsRP by auto
    next
      case False
      with split2 have fcsplit: "flatBP cp = us @ vs"
          and jrest: "vs @ b = concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]" by auto
      have False
      proof (cases "us = []")
        case True
        hence "vs = Dsym w # flatBT cb" using fcsplit fchd by simp
        hence "hd (vs @ b) = Dsym w" by simp
        moreover have "vs @ b = concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]"
          using jrest by simp
        moreover have "hd (concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]) = CM
              \<or> hd (concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]) = RP"
          by (cases rs) auto
        ultimately show False by auto
      next
        case usne: False
        have vsne: "vs \<noteq> []"
        proof
          assume v0: "vs = []"
          hence "flatBP cp = us \<and> b = concat (map (\<lambda>r. CM # flatBP r) rs) @ [RP]"
            using fcsplit jrest by simp
          thus False using False v0 by simp
        qed
        have "flatinj_dsum us < 0"
        proof -
          have "flatinj_dsum (flatBP r0) = -1" by (rule flatinj_dsum_flatBP)
          moreover have "0 \<le> flatinj_dsum s1"
            using flatinj_prefix_nonneg_BP[OF inr0 usne] .
          moreover have "flatinj_dsum (flatBP r0) = flatinj_dsum s1 + flatinj_dsum us"
            using inr0 by simp
          ultimately show ?thesis by simp
        qed
        moreover have "0 \<le> flatinj_dsum us"
          using flatinj_prefix_nonneg_BP[OF fcsplit vsne] .
        ultimately show False by simp
      qed
      thus ?thesis ..
    qed
  qed
qed

text \<open>Destructor: an scb-decomposition pins to the last principal component.\<close>

lemma scb_to_last_component:
  assumes d: "scb_decomp u s (flatBT (Trm [cp])) b" and une: "u \<noteq> Trm []"
  shows "\<exists>sc bc. flatBP (last (untrm u)) = sc @ flatBP cp @ bc
               \<and> (\<forall>x \<in> set bc. x = RP)"
proof -
  from d have eq: "flatBT u = s @ flatBP cp @ b" and rb: "\<forall>x \<in> set b. x = RP"
    by (auto simp: scb_decomp_def)
  obtain w cb where cpw: "cp = DB w cb" by (cases cp) auto
  show ?thesis
  proof (cases u)
    case (Trm ps)
    show ?thesis
    proof (cases ps)
      case Nil thus ?thesis using Trm une by simp
    next
      case (Cons p0 ps1)
      show ?thesis
      proof (cases ps1)
        case Nil
        \<comment> \<open>single component: the decomposition is already component-level\<close>
        have "flatBP p0 = s @ flatBP cp @ b" using eq Trm Cons Nil by simp
        thus ?thesis using Trm Cons Nil rb by auto
      next
        case (Cons q ps2)
        have eq3: "LP # (flatBP p0
              @ concat (map (\<lambda>r. CM # flatBP r) (q # ps2))) @ [RP]
              = s @ flatBP cp @ b"
          using eq Trm \<open>ps = p0 # ps1\<close> Cons by simp
        have sne: "s \<noteq> []"
        proof
          assume "s = []"
          hence "LP = Dsym w" using eq3 cpw by simp
          thus False by simp
        qed
        then obtain s1 where ss: "s = LP # s1" using eq3 by (cases s) auto
        have eq4: "flatBP p0 @ concat (map (\<lambda>r. CM # flatBP r) (q # ps2)) @ [RP]
              = s1 @ flatBP cp @ b"
          using eq3 ss by simp
        \<comment> \<open>first-component occurrence is impossible; join occurrence extracts\<close>
        from append_eq_append_conv2[THEN iffD1, OF eq4]
        obtain us where split:
            "flatBP p0 = s1 @ us \<and> us @ concat (map (\<lambda>r. CM # flatBP r) (q # ps2)) @ [RP]
                                    = flatBP cp @ b
           \<or> flatBP p0 @ us = s1 \<and> concat (map (\<lambda>r. CM # flatBP r) (q # ps2)) @ [RP]
                                    = us @ flatBP cp @ b" by blast
        show ?thesis
        proof (cases "flatBP p0 @ us = s1
              \<and> concat (map (\<lambda>r. CM # flatBP r) (q # ps2)) @ [RP]
                = us @ flatBP cp @ b")
          case True
          have "\<exists>sc bc. flatBP (last (q # ps2)) = sc @ flatBP cp @ bc
                      \<and> (\<forall>x \<in> set bc. x = RP)"
            using scbext_join True rb by blast
          thus ?thesis using Trm \<open>ps = p0 # ps1\<close> Cons by simp
        next
          case False
          with split have inp: "flatBP p0 = s1 @ us"
              and rest: "us @ concat (map (\<lambda>r. CM # flatBP r) (q # ps2)) @ [RP]
                         = flatBP cp @ b" by auto
          from append_eq_append_conv2[THEN iffD1, OF rest[symmetric]]
          obtain vs where split2:
              "flatBP cp = us @ vs
                 \<and> vs @ b = concat (map (\<lambda>r. CM # flatBP r) (q # ps2)) @ [RP]
             \<or> flatBP cp @ vs = us
                 \<and> b = vs @ concat (map (\<lambda>r. CM # flatBP r) (q # ps2)) @ [RP]"
            by blast
          have False
          proof (cases "flatBP cp @ vs = us
                \<and> b = vs @ concat (map (\<lambda>r. CM # flatBP r) (q # ps2)) @ [RP]")
            case True
            hence "CM \<in> set b" by auto
            thus False using rb by auto
          next
            case False
            with split2 have fcsplit: "flatBP cp = us @ vs"
                and jrest: "vs @ b
                  = concat (map (\<lambda>r. CM # flatBP r) (q # ps2)) @ [RP]" by auto
            show False
            proof (cases "us = []")
              case True
              hence "vs = Dsym w # flatBT cb" using fcsplit cpw by simp
              hence "hd (vs @ b) = Dsym w" by simp
              moreover have "hd (concat (map (\<lambda>r. CM # flatBP r) (q # ps2)) @ [RP]) = CM"
                by simp
              ultimately show False using jrest by simp
            next
              case usne: False
              have vsne: "vs \<noteq> []"
              proof
                assume v0: "vs = []"
                hence "flatBP cp @ vs = us \<and> b
                  = vs @ concat (map (\<lambda>r. CM # flatBP r) (q # ps2)) @ [RP]"
                  using fcsplit jrest by simp
                thus False using False by simp
              qed
              have "flatinj_dsum us < 0"
              proof -
                have "flatinj_dsum (flatBP p0) = -1" by (rule flatinj_dsum_flatBP)
                moreover have "0 \<le> flatinj_dsum s1"
                  using flatinj_prefix_nonneg_BP[OF inp usne] .
                moreover have "flatinj_dsum (flatBP p0)
                  = flatinj_dsum s1 + flatinj_dsum us" using inp by simp
                ultimately show ?thesis by simp
              qed
              moreover have "0 \<le> flatinj_dsum us"
                using flatinj_prefix_nonneg_BP[OF fcsplit vsne] .
              ultimately show False by simp
            qed
          qed
          thus ?thesis ..
        qed
      qed
    qed
  qed
qed

text \<open>Constructor: a component-level occurrence lifts into any term sharing
  that last component.\<close>

lemma scb_from_last_component:
  assumes comp: "flatBP (last (untrm w)) = sc @ flatBP cp @ bc"
    and rb: "\<forall>x \<in> set bc. x = RP"
    and wne: "untrm w \<noteq> []"
    and pc: "dfree_BP cp"
  shows "\<exists>s' b'. scb_decomp w s' (flatBT (Trm [cp])) b'"
proof -
  obtain ws where wTrm: "w = Trm ws" by (cases w) auto
  have ipt: "isPTB_str (flatBT (Trm [cp])) \<or> True" by simp
  show ?thesis
  proof (cases ws)
    case Nil thus ?thesis using wTrm wne by simp
  next
    case (Cons p0 ps1)
    show ?thesis
    proof (cases ps1)
      case Nil
      have "flatBT w = sc @ flatBP cp @ bc"
        using wTrm Cons Nil comp by simp
      hence "scb_decomp w sc (flatBT (Trm [cp])) bc"
        unfolding scb_decomp_def using rb pc
        by (auto simp: isPTB_str_def intro: exI[of _ cp])
      thus ?thesis by blast
    next
      case (Cons q ps2)
      have lastc: "last ws = last (q # ps2)" using \<open>ws = p0 # ps1\<close> Cons by simp
      have joinsnoc: "concat (map (\<lambda>r. CM # flatBP r) (q # ps2))
            = concat (map (\<lambda>r. CM # flatBP r) (butlast (q # ps2)))
              @ CM # flatBP (last (q # ps2))"
      proof -
        have eq: "q # ps2 = butlast (q # ps2) @ [last (q # ps2)]"
          by (simp add: append_butlast_last_id)
        have "concat (map (\<lambda>r. CM # flatBP r) (q # ps2))
            = concat (map (\<lambda>r. CM # flatBP r) (butlast (q # ps2) @ [last (q # ps2)]))"
          using eq by (rule arg_cong[where f="\<lambda>xs. concat (map (\<lambda>r. CM # flatBP r) xs)"])
        also have "\<dots> = concat (map (\<lambda>r. CM # flatBP r) (butlast (q # ps2)))
                      @ CM # flatBP (last (q # ps2))"
          by simp
        finally show ?thesis .
      qed
      have "flatBT w = LP # (flatBP p0
            @ concat (map (\<lambda>r. CM # flatBP r) (q # ps2))) @ [RP]"
        using wTrm \<open>ws = p0 # ps1\<close> Cons by simp
      also have "\<dots> = (LP # flatBP p0
            @ concat (map (\<lambda>r. CM # flatBP r) (butlast (q # ps2)))
            @ CM # sc) @ flatBP cp @ (bc @ [RP])"
        using joinsnoc comp wTrm lastc \<open>ws = p0 # ps1\<close> by simp
      finally have "scb_decomp w (LP # flatBP p0
            @ concat (map (\<lambda>r. CM # flatBP r) (butlast (q # ps2)))
            @ CM # sc) (flatBT (Trm [cp])) (bc @ [RP])"
        unfolding scb_decomp_def using rb pc
        by (auto simp: isPTB_str_def intro: exI[of _ cp])
      thus ?thesis by blast
    qed
  qed
qed


text \<open>The combined transfer: \<open>MarkedB\<close> membership depends only on the last
  principal component (used for the \<open>+\<^sub>B\<close> assembly in the (C) branch of the
  \<open>Trans\<close>/\<open>Mark\<close> value invariant).\<close>

lemma MarkedB_last_component_transfer:
  assumes uc: "(u, c) \<in> MarkedB" and une: "u \<noteq> Trm []"
    and lc: "last (untrm u) = last (untrm w)"
    and wne: "untrm w \<noteq> []"
  shows "(w, c) \<in> MarkedB"
proof -
  from uc obtain s b where d: "scb_decomp u s (flatBT c) b"
    by (auto simp: MarkedB_def)
  have ipt: "isPTB_str (flatBT c)" using d une by (simp add: scb_decomp_def)
  then obtain p where pf: "dfree_BP p" and pfl: "flatBT c = flatBP p"
    by (auto simp: isPTB_str_def)
  have cp: "c = Trm [p]"
  proof -
    have "flatBT c = flatBT (Trm [p])" using pfl by simp
    thus ?thesis by (rule m_7_flatBT_inj)
  qed
  have d': "scb_decomp u s (flatBT (Trm [p])) b" using d cp by simp
  obtain sc bc where comp: "flatBP (last (untrm u)) = sc @ flatBP p @ bc"
      and rbc: "\<forall>x \<in> set bc. x = RP"
    using scb_to_last_component[OF d' une] by blast
  have comp': "flatBP (last (untrm w)) = sc @ flatBP p @ bc"
    using comp lc by simp
  have "\<exists>s' b'. scb_decomp w s' (flatBT (Trm [p])) b'"
    by (rule scb_from_last_component[OF comp' rbc wne pf])
  thus ?thesis using cp by (auto simp: MarkedB_def)
qed


text \<open>A mono sequence's last column has a (unique) row-0 parent: its row-0
  entry strictly exceeds the left end (@{thm [source] m_5_1_ancestor_basic_1}),
  so it is not a running minimum (@{thm [source] idxsum_no_parent0_iff}).\<close>

lemma monoT_hasParent0_last:
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and L: "1 < Lng M"
  shows "hasParent M 0 (Lng M - 1)"
proof -
  have j1lt: "Lng M - 1 < Lng M" using L by simp
  have leM: "leR M 0 0 (Lng M - 1)" using mono by (simp add: monoT_def)
  have "entry M 0 0 < entry M 0 (Lng M - 1)"
    by (rule m_5_1_ancestor_basic_1[OF MT _ order.refl leM]) (use L in linarith)
  hence "\<not> (\<forall>j < Lng M - 1. entry M 0 j \<ge> entry M 0 (Lng M - 1))"
    using L by (auto intro!: exI[of _ 0])
  thus ?thesis
    using idxsum_no_parent0_iff[OF MT j1lt]
    unfolding hasParent_def by blast
qed


text \<open>Three small \<open>MarkedB\<close>/scb helpers for the value-invariant assembly:
  lifting a decomposition through a principal head, through a right summand
  of \<open>+\<^sub>B\<close>, and the \<open>BP\<close>-level principal replacement (principality of the
  replaced term).\<close>

lemma scb_Dpt_lift:
  assumes d: "scb_decomp X s c b" and ipt: "isPTB_str c"
  shows "scb_decomp (Dpt v X) (Dsym v # s) c b"
proof -
  from d have "flatBT X = s @ c @ b" and "\<forall>x \<in> set b. x = RP"
    by (auto simp: scb_decomp_def)
  moreover have "flatBT (Dpt v X) = Dsym v # flatBT X" by simp
  ultimately show ?thesis using ipt by (simp add: scb_decomp_def)
qed

lemma MarkedB_addBT_right:
  assumes mb: "(X, c) \<in> MarkedB" and Xne: "X \<noteq> 0\<^sub>B"
  shows "(Y +\<^sub>B X, c) \<in> MarkedB"
proof -
  obtain as where Yt: "Y = Trm as" by (cases Y) auto
  obtain bs where Xt: "X = Trm bs" by (cases X) auto
  have bsne: "bs \<noteq> []" using Xne Xt by simp
  have lastEq: "last (untrm X) = last (untrm (Y +\<^sub>B X))"
    using Yt Xt bsne by simp
  have wne: "untrm (Y +\<^sub>B X) \<noteq> []" using Yt Xt bsne by simp
  show ?thesis
    by (rule MarkedB_last_component_transfer[OF mb _ lastEq wne])
       (use Xne Xt in simp)
qed

lemma scb_replace_principal_BP:
  assumes d: "scb_decomp (Trm [p0]) s (flatBT (Trm [cp])) b"
    and pc': "isPTB_str (flatBT (Trm [cp']))"
  shows "\<exists>p'. flatBP p' = s @ flatBT (Trm [cp']) @ b
            \<and> scb_decomp (Trm [p']) s (flatBT (Trm [cp'])) b"
proof -
  from d have eq: "flatBP p0 = s @ flatBP cp @ b"
    and rb: "\<forall>x \<in> set b. x = RP"
    by (auto simp: scb_decomp_def)
  obtain p' where p': "flatBP p' = s @ flatBP cp' @ b"
    using scbimg_image_BP[OF eq rb] by blast
  have "scb_decomp (Trm [p']) s (flatBT (Trm [cp'])) b"
    unfolding scb_decomp_def using p' pc' rb by simp
  thus ?thesis using p' by auto
qed


text \<open>\<open>MarkedB\<close> through a principal head.\<close>

lemma MarkedB_Dpt_lift:
  assumes mb: "(X, c) \<in> MarkedB" and ipt: "isPTB_str (flatBT c)"
  shows "(Dpt v X, c) \<in> MarkedB"
proof -
  from mb obtain s b where "scb_decomp X s (flatBT c) b"
    by (auto simp: MarkedB_def)
  hence "scb_decomp (Dpt v X) (Dsym v # s) (flatBT c) b"
    by (rule scb_Dpt_lift[OF _ ipt])
  thus ?thesis unfolding MarkedB_def by auto
qed

text \<open>The hard (B) branch of the \<open>Trans\<close>/\<open>Mark\<close> value invariant
  (\<open>monoT M\<close>, \<open>t\<^sub>1 \<noteq> 0\<close>), as a dedicated lemma taking the induction
  hypotheses for \<open>Pred M\<close> as named assumptions.\<close>

lemma trans_inv_B_hard:
  assumes MR: "M \<in> RT_PS" and mono: "monoT M" and L: "1 < Lng M"
    and t1ne: "Trans (Pred M) \<noteq> 0\<^sub>B"
    and IHt1: "dfree_BT (Trans (Pred M))"
    and IHmk: "\<And>m'. (Pred M, m') \<in> Marked
                 \<Longrightarrow> dfree_BT (Mark (Pred M) m')
                   \<and> (Trans (Pred M), Mark (Pred M) m') \<in> MarkedB"
  shows "dfree_BT (Trans M) \<and> Trans M \<noteq> 0\<^sub>B
       \<and> (\<forall>m. (M, m) \<in> Marked
              \<longrightarrow> dfree_BT (Mark M m) \<and> (Trans M, Mark M m) \<in> MarkedB)"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
  have domT: "Trans_Mark_dom (Inl M)" by (rule m_7_3_Trans_welldef[OF MR])
  have domK: "\<And>m. Trans_Mark_dom (Inr (M, m))" by (rule m_7_3_Mark_welldef[OF MR])
  have hp: "hasParent M 0 (Lng M - 1)" by (rule monoT_hasParent0_last[OF MT mono L])
  let ?t1 = "Trans (Pred M)"
  let ?bv = "entry M 1 (Lng M - 1)"
  define jp where "jp = parent M 0 (Lng M - 1)"
  define c1 where "c1 = Mark (Pred M) (Adm M jp)"
  define vv where "vv = bpHeadV c1"
  define tt2 where "tt2 = bpHeadT c1"
  define JJ1 where "JJ1 = Lng (PB tt2) - 1"
  define pj where "pj = PB tt2 ! JJ1"
  define ldj where "ldj = (bpHeadV pj = enat (entry M 1 jp))"
  define tt3 where "tt3 = (if ldj then SigmaB (take JJ1 (PB tt2)) else tt2)"
  define tt4 where "tt4 = (if ldj then bpHeadT pj else tt2)"
  define c2 where "c2 = (if transCondI M \<or> transCondIII M \<or> transCondV M
                         then Dpt vv (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)
                         else if transCondVI M
                         then Dpt vv (Dpt (enat ?bv) 0\<^sub>B)
                         else if tt2 = 0\<^sub>B
                         then Dpt vv (Dpt (enat (entry M 1 jp)) (Dpt (enat ?bv) 0\<^sub>B))
                         else Dpt vv (tt3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                            (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)))"
  define sb1 where "sb1 = (SOME sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb))"
  have trans_val: "Trans M = unflatBT (fst sb1 @ flatBT c2 @ snd sb1)"
    using Trans.psimps[OF domT] MR Lgt1 mono t1ne
    unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
              tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
              ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
              c2_def[symmetric] sb1_def[symmetric]
    by simp
  \<comment> \<open>induction facts for \<open>c\<^sub>1\<close>\<close>
  have mkdA: "(Pred M, Adm M jp) \<in> Marked"
    using Marked_Pred_Adm[OF MT L hp] jp_def by simp
  have c1df: "dfree_BT c1" and mb1: "(?t1, c1) \<in> MarkedB"
    using IHmk[OF mkdA] c1_def by auto
  have t1neT: "?t1 \<noteq> Trm []" using t1ne by simp
  \<comment> \<open>the SOME decomposition exists\<close>
  have exsb: "\<exists>sb. scb_decomp ?t1 (fst sb) (flatBT c1) (snd sb)"
    using mb1 unfolding MarkedB_def by auto
  have dsome: "scb_decomp ?t1 (fst sb1) (flatBT c1) (snd sb1)"
    unfolding sb1_def by (rule someI_ex[OF exsb])
  \<comment> \<open>\<open>c\<^sub>1\<close> is a principal dfree term\<close>
  have iptc1: "isPTB_str (flatBT c1)"
    using dsome t1neT by (simp add: scb_decomp_def)
  then obtain pc where pcf: "dfree_BP pc" and pcl: "flatBT c1 = flatBP pc"
    by (auto simp: isPTB_str_def)
  have c1p: "c1 = Trm [pc]"
  proof -
    have "flatBT c1 = flatBT (Trm [pc])" using pcl by simp
    thus ?thesis by (rule m_7_flatBT_inj)
  qed
  obtain wv tb where pcw: "pc = DB wv tb" by (cases pc) auto
  have vvv: "vv = wv" using vv_def c1p pcw by simp
  have tt2v: "tt2 = tb" using tt2_def c1p pcw by simp
  have wvne: "wv \<noteq> \<infinity>" and tbdf: "dfree_BT tb" using pcf pcw by auto
  \<comment> \<open>\<open>c\<^sub>2\<close> is a principal dfree term ending (spine-wise) in \<open>D\<^bsub>?bv\<^esub> 0\<close>\<close>
  have c2shape: "\<exists>X. c2 = Dpt vv X \<and> dfree_BT X \<and> (X, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
  proof -
    have selfb: "(Dpt (enat ?bv) 0\<^sub>B, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
    proof -
      have "scb_decomp (Dpt (enat ?bv) 0\<^sub>B) [] (flatBT (Dpt (enat ?bv) 0\<^sub>B)) []"
        by (rule scb_decomp_self) (rule isPTB_str_Dpt, simp_all)
      thus ?thesis unfolding MarkedB_def by auto
    qed
    have iptb: "isPTB_str (flatBT (Dpt (enat ?bv) 0\<^sub>B))"
      by (rule isPTB_str_Dpt) simp_all
    have dbne: "Dpt (enat ?bv) 0\<^sub>B \<noteq> 0\<^sub>B" by simp
    consider (A) "transCondI M \<or> transCondIII M \<or> transCondV M"
      | (VI) "\<not> (transCondI M \<or> transCondIII M \<or> transCondV M)" "transCondVI M"
      | (Z) "\<not> (transCondI M \<or> transCondIII M \<or> transCondV M)" "\<not> transCondVI M"
            "tt2 = 0\<^sub>B"
      | (E) "\<not> (transCondI M \<or> transCondIII M \<or> transCondV M)" "\<not> transCondVI M"
            "tt2 \<noteq> 0\<^sub>B"
      by blast
    thus ?thesis
    proof cases
      case A
      have x: "c2 = Dpt vv (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)" using A c2_def by simp
      have df: "dfree_BT (tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)"
        using tt2v tbdf by (cases tb) auto
      have mb: "(tt2 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
        by (rule MarkedB_addBT_right[OF selfb dbne])
      show ?thesis using x df mb by blast
    next
      case VI
      have x: "c2 = Dpt vv (Dpt (enat ?bv) 0\<^sub>B)" using VI c2_def by simp
      have mb: "(Dpt (enat ?bv) 0\<^sub>B, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB" by (rule selfb)
      show ?thesis using x mb by auto
    next
      case Z
      have x: "c2 = Dpt vv (Dpt (enat (entry M 1 jp)) (Dpt (enat ?bv) 0\<^sub>B))"
        using Z c2_def by simp
      have mb: "(Dpt (enat (entry M 1 jp)) (Dpt (enat ?bv) 0\<^sub>B),
                 Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
        by (rule MarkedB_Dpt_lift[OF selfb iptb])
      show ?thesis using x mb by auto
    next
      case E
      have x: "c2 = Dpt vv (tt3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                   (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B))"
        using E c2_def by simp
      have df3: "dfree_BT tt3"
      proof -
        have "dfree_BT (SigmaB (take JJ1 (PB tb)))"
          using tbdf by (cases tb) (auto simp: SigmaB_def PB_def dest!: in_set_takeD)
        thus ?thesis using tt3_def tt2v tbdf by simp
      qed
      have df4: "dfree_BT tt4"
      proof -
        have tbne: "untrm tb \<noteq> []" using E(3) tt2v by (cases tb) auto
        have inr: "JJ1 < Lng (PB tb)"
          using JJ1_def tt2v tbne by (simp add: PB_def)
        have "pj \<in> set (PB tb)" using pj_def tt2v inr by simp
        hence "dfree_BT pj" using tbdf by (cases tb) (auto simp: PB_def)
        hence "dfree_BT (bpHeadT pj)" by (cases pj rule: bpHeadT.cases) auto
        thus ?thesis using tt4_def tt2v tbdf by simp
      qed
      have dfsum: "dfree_BT (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B)"
        using df4 by (cases tt4) auto
      have mbin: "(tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
        by (rule MarkedB_addBT_right[OF selfb dbne])
      have mbmid: "(Dpt (enat (entry M 1 jp)) (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B),
                    Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
        by (rule MarkedB_Dpt_lift[OF mbin iptb])
      have mbout: "(tt3 +\<^sub>B Dpt (enat (entry M 1 jp)) (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B),
                    Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
        by (rule MarkedB_addBT_right[OF mbmid]) simp
      have dfall: "dfree_BT (tt3 +\<^sub>B Dpt (enat (entry M 1 jp))
                                    (tt4 +\<^sub>B Dpt (enat ?bv) 0\<^sub>B))"
        using df3 dfsum by (cases tt3) auto
      show ?thesis using x mbout dfall by blast
    qed
  qed
  obtain X2 where c2X: "c2 = Dpt vv X2" and X2df: "dfree_BT X2"
      and X2mb: "(X2, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
    using c2shape by blast
  have c2df: "dfree_BT c2" using c2X X2df wvne vvv by simp
  have iptc2: "isPTB_str (flatBT c2)"
    using c2X by (intro isPTB_str_Dpt[of vv X2, folded c2X])
                 (use wvne vvv X2df in simp_all)
  have c2mb: "(c2, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
  proof -
    have iptb: "isPTB_str (flatBT (Dpt (enat ?bv) 0\<^sub>B))"
      by (rule isPTB_str_Dpt) simp_all
    show ?thesis using MarkedB_Dpt_lift[OF X2mb iptb] c2X by simp
  qed
  obtain pc2 where c2p: "c2 = Trm [pc2]" using c2X by auto
  \<comment> \<open>the replaced \<open>Trans\<close> value\<close>
  have dsome': "scb_decomp ?t1 (fst sb1) (flatBT (Trm [pc])) (snd sb1)"
    using dsome c1p by simp
  have iptc2': "isPTB_str (flatBT (Trm [pc2]))" using iptc2 c2p by simp
  obtain t' where t'f: "flatBT t' = fst sb1 @ flatBT (Trm [pc2]) @ snd sb1"
      and t'd: "scb_decomp t' (fst sb1) (flatBT (Trm [pc2])) (snd sb1)"
    using scb_replace_principal[OF dsome' iptc2'] by blast
  have transM: "Trans M = t'"
    using trans_val t'f c2p unflatBT_flat[of t'] by simp
  \<comment> \<open>dfree and nonzero\<close>
  have sb_sub: "set (fst sb1) \<subseteq> set (flatBT ?t1)"
      and bb_sub: "set (snd sb1) \<subseteq> set (flatBT ?t1)"
    using dsome by (auto simp: scb_decomp_def)
  have t'df: "dfree_BT t'"
  proof -
    have "\<And>v'. Dsym v' \<in> set (flatBT t') \<Longrightarrow> v' \<noteq> \<infinity>"
    proof -
      fix v' assume "Dsym v' \<in> set (flatBT t')"
      hence "Dsym v' \<in> set (flatBT ?t1) \<or> Dsym v' \<in> set (flatBT c2)"
        using t'f c2p sb_sub bb_sub by auto
      thus "v' \<noteq> \<infinity>"
        using IHt1 c2df dfree_flat_BT by blast
    qed
    thus ?thesis using dfree_flat_BT by blast
  qed
  have t'ne: "t' \<noteq> 0\<^sub>B"
  proof
    assume "t' = 0\<^sub>B"
    hence z: "flatBT t' = [Zsym]" by simp
    have pc2v: "pc2 = DB vv X2" using c2p c2X by simp
    have "Dsym vv \<in> set (flatBP pc2)" using pc2v by simp
    hence "Dsym vv \<in> set (flatBT t')" using t'f by simp
    thus False using z by simp
  qed
  \<comment> \<open>the Mark values\<close>
  have markB: "\<And>m. (M, m) \<in> Marked
       \<Longrightarrow> dfree_BT (Mark M m) \<and> (Trans M, Mark M m) \<in> MarkedB"
  proof -
    fix m assume mM: "(M, m) \<in> Marked"
    \<comment> \<open>the fallback value \<open>D\<^bsub>?bv\<^esub> 0\<close> always satisfies both conjuncts\<close>
    have fb_df: "dfree_BT (Dpt (enat ?bv) 0\<^sub>B)" by simp
    have fb_mb: "(Trans M, Dpt (enat ?bv) 0\<^sub>B) \<in> MarkedB"
    proof -
      from c2mb obtain s2x b2x where d2x: "scb_decomp c2 s2x (flatBT (Dpt (enat ?bv) 0\<^sub>B)) b2x"
        by (auto simp: MarkedB_def)
      have "scb_decomp t' (fst sb1 @ s2x) (flatBT (Dpt (enat ?bv) 0\<^sub>B)) (b2x @ snd sb1)"
        by (rule m_7_2_scb_compose[OF _ _ d2x])
           (use c2p t'd in auto)
      thus ?thesis using transM unfolding MarkedB_def by auto
    qed
    show "dfree_BT (Mark M m) \<and> (Trans M, Mark M m) \<in> MarkedB"
    proof (cases "m < Lng M - 1")
      case False
      have "Mark M m = Dpt (enat ?bv) 0\<^sub>B"
        using Mark.psimps[OF domK] MR Lgt1 mono t1ne False
        unfolding Let_def jp_def[symmetric] c1_def[symmetric]
        by simp
      thus ?thesis using fb_df fb_mb by simp
    next
      case mlt: True
      define c0 where "c0 = Mark (Pred M) m"
      define sm1 where "sm1 = (SOME sb. scb_decomp c0 (fst sb) (flatBT c1) (snd sb))"
      have mark_val_raw: "Mark M m = (if (Mark (Pred M) m, c1) \<in> MarkedB
            then unflatBT
                   (fst (SOME sb. scb_decomp (Mark (Pred M) m) (fst sb)
                                    (flatBT c1) (snd sb))
                    @ flatBT c2
                    @ snd (SOME sb. scb_decomp (Mark (Pred M) m) (fst sb)
                                      (flatBT c1) (snd sb)))
            else Dpt (enat ?bv) 0\<^sub>B)"
        using Mark.psimps[OF domK] MR Lgt1 mono t1ne mlt
        unfolding Let_def jp_def[symmetric] c1_def[symmetric] vv_def[symmetric]
                  tt2_def[symmetric] JJ1_def[symmetric] pj_def[symmetric]
                  ldj_def[symmetric] tt3_def[symmetric] tt4_def[symmetric]
                  c2_def[symmetric]
        by simp
      have mark_val: "Mark M m = (if (c0, c1) \<in> MarkedB
            then unflatBT (fst sm1 @ flatBT c2 @ snd sm1)
            else Dpt (enat ?bv) 0\<^sub>B)"
        using mark_val_raw by (simp add: c0_def sm1_def)
      show ?thesis
      proof (cases "(c0, c1) \<in> MarkedB")
        case False
        thus ?thesis using mark_val fb_df fb_mb by simp
      next
        case mbc: True
        have mPred: "(Pred M, m) \<in> Marked"
          by (rule Marked_Pred[OF MT L mM mlt])
        have c0df: "dfree_BT c0" and mb0: "(?t1, c0) \<in> MarkedB"
          using IHmk[OF mPred] c0_def by auto
        \<comment> \<open>\<open>c\<^sub>0\<close> is principal\<close>
        from mb0 obtain s0 b0 where d0: "scb_decomp ?t1 s0 (flatBT c0) b0"
          by (auto simp: MarkedB_def)
        have iptc0: "isPTB_str (flatBT c0)"
          using d0 t1neT by (simp add: scb_decomp_def)
        then obtain pc0 where pc0f: "dfree_BP pc0" and pc0l: "flatBT c0 = flatBP pc0"
          by (auto simp: isPTB_str_def)
        have c0p: "c0 = Trm [pc0]"
        proof -
          have "flatBT c0 = flatBT (Trm [pc0])" using pc0l by simp
          thus ?thesis by (rule m_7_flatBT_inj)
        qed
        \<comment> \<open>the \<open>SOME\<close> for \<open>c\<^sub>0\<close>\<close>
        have exsm: "\<exists>sb. scb_decomp c0 (fst sb) (flatBT c1) (snd sb)"
          using mbc unfolding MarkedB_def by auto
        have dsm: "scb_decomp c0 (fst sm1) (flatBT c1) (snd sm1)"
          unfolding sm1_def by (rule someI_ex[OF exsm])
        have dsm': "scb_decomp (Trm [pc0]) (fst sm1) (flatBT (Trm [pc])) (snd sm1)"
          using dsm c0p c1p by simp
        \<comment> \<open>the replaced \<open>Mark\<close> value (principal)\<close>
        obtain pm where pmf: "flatBP pm = fst sm1 @ flatBT (Trm [pc2]) @ snd sm1"
            and pmd: "scb_decomp (Trm [pm]) (fst sm1) (flatBT (Trm [pc2])) (snd sm1)"
          using scb_replace_principal_BP[OF dsm' iptc2'] by blast
        have markM: "Mark M m = Trm [pm]"
        proof -
          have "flatBT (Trm [pm]) = fst sm1 @ flatBT c2 @ snd sm1"
            using pmf c2p by simp
          thus ?thesis
            using mark_val mbc unflatBT_flat[of "Trm [pm]"] by simp
        qed
        \<comment> \<open>dfree of the replaced value\<close>
        have sm_sub: "set (fst sm1) \<subseteq> set (flatBT c0)"
            and bm_sub: "set (snd sm1) \<subseteq> set (flatBT c0)"
          using dsm by (auto simp: scb_decomp_def)
        have mmdf: "dfree_BT (Trm [pm])"
        proof -
          have "\<And>v'. Dsym v' \<in> set (flatBT (Trm [pm])) \<Longrightarrow> v' \<noteq> \<infinity>"
          proof -
            fix v' assume "Dsym v' \<in> set (flatBT (Trm [pm]))"
            hence "Dsym v' \<in> set (flatBT c0) \<or> Dsym v' \<in> set (flatBT c2)"
              using pmf c2p sm_sub bm_sub by auto
            thus "v' \<noteq> \<infinity>" using c0df c2df dfree_flat_BT by blast
          qed
          thus ?thesis using dfree_flat_BT by blast
        qed
        \<comment> \<open>coherence: the two-step decomposition equals the direct one\<close>
        have comp: "scb_decomp ?t1 (s0 @ fst sm1) (flatBT c1) (snd sm1 @ b0)"
          by (rule m_7_2_scb_compose[OF _ _ dsm]) (use c0p d0 in auto)
        have coh: "fst sb1 = s0 @ fst sm1 \<and> snd sb1 = snd sm1 @ b0"
          by (rule m_7_2_scb_unique_sb[OF dsome comp t1neT])
        have t'flat: "flatBT t' = s0 @ flatBT (Trm [pm]) @ b0"
          using t'f coh pmf c2p by simp
        have b0rp: "\<forall>x \<in> set b0. x = RP"
          using d0 by (simp add: scb_decomp_def)
        have iptm: "isPTB_str (flatBT (Trm [pm]))"
        proof -
          have "dfree_BP pm"
            using mmdf by simp
          thus ?thesis using isPTB_str_def by auto
        qed
        have "scb_decomp t' s0 (flatBT (Trm [pm])) b0"
          unfolding scb_decomp_def using t'flat iptm b0rp by simp
        hence "(Trans M, Mark M m) \<in> MarkedB"
          using transM markM unfolding MarkedB_def by auto
        thus ?thesis using mmdf markM by simp
      qed
    qed
  qed
  show ?thesis using transM t'df t'ne markB by auto
qed


text \<open>The (C) multiT branch of the \<open>Trans\<close>/\<open>Mark\<close> value invariant, as a
  dedicated lemma taking the induction hypotheses for the two smaller
  recursion arguments — the diagonal prefix \<open>take (Pcut M) M\<close> and the last
  \<open>P\<close>-component \<open>drop (Pcut M) M\<close>.  \<open>Trans M = Trans A +\<^sub>B (\<dots>)\<close> appends a
  non-empty right summand, and \<open>MarkedB\<close> reduces to that summand
  (@{thm [source] MarkedB_addBT_right}).\<close>

lemma trans_inv_C:
  assumes MR: "M \<in> RT_PS" and mu: "multiT M"
    and dfTA: "dfree_BT (Trans (take (Pcut M) M))"
    and dfTJ: "dfree_BT (Trans (drop (Pcut M) M))"
    and nzTJ: "\<not> zeroT (drop (Pcut M) M) \<Longrightarrow> Trans (drop (Pcut M) M) \<noteq> 0\<^sub>B"
    and IHmkJ: "\<And>m'. (drop (Pcut M) M, m') \<in> Marked
                 \<Longrightarrow> dfree_BT (Mark (drop (Pcut M) M) m')
                   \<and> (Trans (drop (Pcut M) M), Mark (drop (Pcut M) M) m') \<in> MarkedB"
  shows "dfree_BT (Trans M) \<and> Trans M \<noteq> 0\<^sub>B
       \<and> (\<forall>m. (M, m) \<in> Marked
              \<longrightarrow> dfree_BT (Mark M m) \<and> (Trans M, Mark M m) \<in> MarkedB)"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have L: "1 < Lng M" by (rule multiT_imp_Lng_gt1[OF MT mu])
  have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
  have nmono: "\<not> monoT M" using mu by (simp add: multiT_def)
  have domT: "Trans_Mark_dom (Inl M)" by (rule m_7_3_Trans_welldef[OF MR])
  have domK: "\<And>m. Trans_Mark_dom (Inr (M, m))" by (rule m_7_3_Mark_welldef[OF MR])
  let ?A = "take (Pcut M) M"
  let ?PJ = "drop (Pcut M) M"
  \<comment> \<open>identify the def's PJ / j0 / prefix with their \<open>Pcut\<close>-forms\<close>
  have PJeq: "P M ! (Lng (P M) - 1) = ?PJ"
    by (rule trans_multiT_last_component(1)[OF MT mu])
  have j0eq: "Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1 = Pcut M"
    by (rule trans_multiT_last_component(2)[OF MT mu])
  have cut: "0 < Pcut M \<and> Pcut M \<le> Lng M - 1" using Pcut_le[OF L] by simp
  \<comment> \<open>seg/offset equalities in \<open>drop\<close>-form (so they apply AFTER @{thm PJeq}
     has rewritten \<open>P M ! \<dots>\<close> to \<open>?PJ\<close>, without simp splitting the inner if)\<close>
  have LdJ: "Lng (drop (Pcut M) M) = Lng M - Pcut M" by simp
  have Aeq2: "seg M 0 (Lng M - 1 - Lng (drop (Pcut M) M) + 1 - 1) = ?A"
  proof -
    have "Lng M - 1 - Lng (drop (Pcut M) M) + 1 - 1 = Pcut M - 1"
      using LdJ cut by linarith
    moreover have "seg M 0 (Pcut M - 1) = take (Suc (Pcut M - 1)) M"
      by (rule seg_0_eq_take) (use cut L in linarith)
    moreover have "Suc (Pcut M - 1) = Pcut M" using cut by simp
    ultimately show ?thesis by simp
  qed
  have meq2: "\<And>m. m - (Lng M - 1 - Lng (drop (Pcut M) M) + 1) = m - Pcut M"
  proof -
    fix m
    have "Lng M - 1 - Lng (drop (Pcut M) M) + 1 = Pcut M"
      using LdJ cut by linarith
    thus "m - (Lng M - 1 - Lng (drop (Pcut M) M) + 1) = m - Pcut M" by simp
  qed
  \<comment> \<open>the two recursion values.  Collapse only the OUTER ifs with \<open>simp only\<close>
     (full \<open>simp\<close> pushes the inner if-condition into the branches and rewrites
     \<open>Lng PJ\<close> differently per branch), then rewrite the raw form by \<open>unfolding\<close>
     (no if-splitting) and close with @{thm refl}.\<close>
  have c1: "(M \<notin> RT_PS) = False" using MR by simp
  have c2: "(Lng M - 1 = 0) = False" using L by simp
  have c3: "monoT M = False" using nmono by simp
  have transM: "Trans M = (if ?PJ = [(0, 0)] then Trans ?A +\<^sub>B Dpt 0 0\<^sub>B
                           else Trans ?A +\<^sub>B Trans ?PJ)"
  proof -
    have raw: "Trans M =
        (if P M ! (Lng (P M) - 1) = [(0, 0)]
         then Trans (seg M 0 (Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1 - 1))
                +\<^sub>B Dpt 0 0\<^sub>B
         else Trans (seg M 0 (Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1 - 1))
                +\<^sub>B Trans (P M ! (Lng (P M) - 1)))"
      by (subst Trans.psimps[OF domT]) (simp only: c1 c2 c3 if_False Let_def)
    show ?thesis unfolding raw PJeq Aeq2 ..
  qed
  have markM: "\<And>m. Mark M m = (if ?PJ = [(0, 0)] then Dpt 0 0\<^sub>B
                               else Mark ?PJ (m - Pcut M))"
  proof -
    fix m
    have raw: "Mark M m =
        (if P M ! (Lng (P M) - 1) = [(0, 0)] then Dpt 0 0\<^sub>B
         else Mark (P M ! (Lng (P M) - 1))
                (m - (Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1)))"
      by (subst Mark.psimps[OF domK]) (simp only: c1 c2 c3 if_False Let_def)
    show "Mark M m = (if ?PJ = [(0, 0)] then Dpt 0 0\<^sub>B else Mark ?PJ (m - Pcut M))"
      unfolding raw PJeq meq2 ..
  qed
  \<comment> \<open>dfree / nonzero of the right-appended term\<close>
  have dfadd: "\<And>a b. dfree_BT a \<Longrightarrow> dfree_BT b \<Longrightarrow> dfree_BT (a +\<^sub>B b)"
  proof -
    fix a b assume da: "dfree_BT a" and db: "dfree_BT b"
    obtain as where a: "a = Trm as" by (cases a)
    obtain bs where b: "b = Trm bs" by (cases b)
    show "dfree_BT (a +\<^sub>B b)" using da db a b by auto
  qed
  have nzadd: "\<And>a b. b \<noteq> 0\<^sub>B \<Longrightarrow> a +\<^sub>B b \<noteq> 0\<^sub>B"
  proof -
    fix a b assume bne: "b \<noteq> 0\<^sub>B"
    obtain as where a: "a = Trm as" by (cases a)
    obtain bs where b: "b = Trm bs" by (cases b)
    have "bs \<noteq> []" using bne b by auto
    thus "a +\<^sub>B b \<noteq> 0\<^sub>B" using a b by auto
  qed
  have dfD0: "dfree_BT (Dpt 0 0\<^sub>B)" by (simp add: zero_enat_def)
  have nzD0: "Dpt 0 0\<^sub>B \<noteq> 0\<^sub>B" by simp
  \<comment> \<open>the last component is reduced and (in the else case) non-zero-term\<close>
  have Pne: "P M \<noteq> []" by (rule P_nonempty)
  have J1lt: "Lng (P M) - 1 < Lng (P M)" using Pne by (cases "P M") auto
  have PJRT: "?PJ \<in> RT_PS"
    using m_6_6_P_reduced[OF MT] MR J1lt PJeq by auto
  have PJT: "?PJ \<in> T_PS" using PJRT by (simp add: RT_PS_def)
  have nzPJ: "?PJ \<noteq> [(0, 0)] \<Longrightarrow> \<not> zeroT ?PJ"
  proof
    assume ne: "?PJ \<noteq> [(0, 0)]" and z: "zeroT ?PJ"
    have L1: "Lng ?PJ = 1" using z by (simp add: zeroT_def)
    then obtain v where v: "?PJ = [(v, v)]"
      using m_6_6_oneColumn[OF PJT] PJRT by auto
    have "entry ?PJ 1 0 = 0" using z by (simp add: zeroT_def)
    hence "v = 0" using v by (simp add: entry_def)
    thus False using ne v by simp
  qed
  \<comment> \<open>Trans M dfree and nonzero\<close>
  have dfT_nzT: "dfree_BT (Trans M) \<and> Trans M \<noteq> 0\<^sub>B"
  proof (cases "?PJ = [(0, 0)]")
    case True
    have tv: "Trans M = Trans ?A +\<^sub>B Dpt 0 0\<^sub>B" using transM True by simp
    have "dfree_BT (Trans ?A +\<^sub>B Dpt 0 0\<^sub>B)" by (rule dfadd[OF dfTA dfD0])
    moreover have "Trans ?A +\<^sub>B Dpt 0 0\<^sub>B \<noteq> 0\<^sub>B" by (rule nzadd[OF nzD0])
    ultimately show ?thesis using tv by simp
  next
    case False
    have tv: "Trans M = Trans ?A +\<^sub>B Trans ?PJ" using transM False by simp
    have nz: "Trans ?PJ \<noteq> 0\<^sub>B" using nzTJ[OF nzPJ[OF False]] .
    have "dfree_BT (Trans ?A +\<^sub>B Trans ?PJ)" by (rule dfadd[OF dfTA dfTJ])
    moreover have "Trans ?A +\<^sub>B Trans ?PJ \<noteq> 0\<^sub>B" by (rule nzadd[OF nz])
    ultimately show ?thesis using tv by simp
  qed
  \<comment> \<open>the Mark values and MarkedB membership\<close>
  have markB: "\<And>m. (M, m) \<in> Marked
       \<Longrightarrow> dfree_BT (Mark M m) \<and> (Trans M, Mark M m) \<in> MarkedB"
  proof -
    fix m assume mM: "(M, m) \<in> Marked"
    show "dfree_BT (Mark M m) \<and> (Trans M, Mark M m) \<in> MarkedB"
    proof (cases "?PJ = [(0, 0)]")
      case True
      have kv: "Mark M m = Dpt 0 0\<^sub>B" using markM True by simp
      have tv: "Trans M = Trans ?A +\<^sub>B Dpt 0 0\<^sub>B" using transM True by simp
      have self: "(Dpt 0 0\<^sub>B, Dpt 0 0\<^sub>B) \<in> MarkedB"
      proof -
        have "scb_decomp (Dpt 0 0\<^sub>B) [] (flatBT (Dpt 0 0\<^sub>B)) []"
          by (rule scb_decomp_self) (rule isPTB_str_Dpt, simp_all add: zero_enat_def)
        thus ?thesis unfolding MarkedB_def by auto
      qed
      have "(Trans ?A +\<^sub>B Dpt 0 0\<^sub>B, Dpt 0 0\<^sub>B) \<in> MarkedB"
        by (rule MarkedB_addBT_right[OF self nzD0])
      thus ?thesis using kv tv dfD0 by simp
    next
      case False
      have kv: "Mark M m = Mark ?PJ (m - Pcut M)" using markM False by simp
      have tv: "Trans M = Trans ?A +\<^sub>B Trans ?PJ" using transM False by simp
      have mPJ: "(?PJ, m - Pcut M) \<in> Marked"
        by (rule multi_Marked_last_component(2)[OF MT mu mM])
      have ih: "dfree_BT (Mark ?PJ (m - Pcut M))
                \<and> (Trans ?PJ, Mark ?PJ (m - Pcut M)) \<in> MarkedB"
        by (rule IHmkJ[OF mPJ])
      have nz: "Trans ?PJ \<noteq> 0\<^sub>B" using nzTJ[OF nzPJ[OF False]] .
      have "(Trans ?A +\<^sub>B Trans ?PJ, Mark ?PJ (m - Pcut M)) \<in> MarkedB"
        by (rule MarkedB_addBT_right[OF conjunct2[OF ih] nz])
      thus ?thesis using kv tv ih by simp
    qed
  qed
  show ?thesis using dfT_nzT markB by blast
qed


section \<open>§7.3 命題（\<open>Trans\<close>の well-defined 性）— the VALUE part:
  \<open>(Trans M, Mark M m) \<in> T\<^sub>B\<^sup>Marked\<close> on \<open>RT\<^sub>PS\<close>\<close>

text \<open>The article's well-definedness side condition (content 2044/2182), the
  simultaneous \<open>Lng\<close>-induction invariant.  Carries the auxiliary nonzero-ness
  \<open>\<not> zeroT M \<longrightarrow> Trans M \<noteq> 0\<close> needed by the (C) branch (the right summand of
  \<open>+\<^sub>B\<close> must be nonzero for @{thm [source] MarkedB_addBT_right}).  The three
  productive branches are the dedicated lemmas
  @{thm [source] trans_inv_B_hard} / @{thm [source] trans_inv_C} and the
  inline (A)/(B)\<open>t\<^sub>1=0\<close> base cases.\<close>

lemma Trans_Mark_invariant_aux:
  "M \<in> RT_PS \<longrightarrow> dfree_BT (Trans M)
     \<and> (\<not> zeroT M \<longrightarrow> Trans M \<noteq> 0\<^sub>B)
     \<and> (\<forall>m. (M, m) \<in> Marked
            \<longrightarrow> dfree_BT (Mark M m) \<and> (Trans M, Mark M m) \<in> MarkedB)"
proof (induction M rule: measure_induct_rule[where f=Lng])
  case (less M)
  show ?case
  proof (rule impI)
    assume MR: "M \<in> RT_PS"
    have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
    have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
    have domT: "Trans_Mark_dom (Inl M)" by (rule m_7_3_Trans_welldef[OF MR])
    have domK: "\<And>m. Trans_Mark_dom (Inr (M, m))" by (rule m_7_3_Mark_welldef[OF MR])
    show "dfree_BT (Trans M) \<and> (\<not> zeroT M \<longrightarrow> Trans M \<noteq> 0\<^sub>B)
        \<and> (\<forall>m. (M, m) \<in> Marked
               \<longrightarrow> dfree_BT (Mark M m) \<and> (Trans M, Mark M m) \<in> MarkedB)"
    proof (cases "Lng M = 1")
      case True
      \<comment> \<open>(A) length 1: \<open>M = [(v,v)]\<close>\<close>
      obtain v where Mv: "M = [(v, v)]"
        using m_6_6_oneColumn[OF MT] MR True by auto
      have tv: "Trans M = (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)"
        using Mv Trans_singleton by simp
      have kv: "\<And>m. Mark M m = (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)"
        using Mv Mark_singleton by simp
      have zc: "zeroT M = (v = 0)" using Mv by (simp add: zeroT_def entry_def)
      have df: "dfree_BT (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)" by simp
      have nzc: "\<not> zeroT M \<longrightarrow> Trans M \<noteq> 0\<^sub>B"
        using zc tv by simp
      have mb: "((if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B),
                 (if v = 0 then 0\<^sub>B else Dpt (enat v) 0\<^sub>B)) \<in> MarkedB"
      proof (cases "v = 0")
        case True
        have "scb_decomp 0\<^sub>B [] (flatBT (0\<^sub>B::BT)) []" by (simp add: scb_decomp_def)
        thus ?thesis using True unfolding MarkedB_def by auto
      next
        case False
        have "scb_decomp (Dpt (enat v) 0\<^sub>B) [] (flatBT (Dpt (enat v) 0\<^sub>B)) []"
          by (rule scb_decomp_self) (rule isPTB_str_Dpt, simp_all)
        thus ?thesis using False unfolding MarkedB_def by auto
      qed
      show ?thesis using tv kv df nzc mb by simp
    next
      case notone: False
      have L: "1 < Lng M" using Mne notone by (cases M) auto
      have Lgt1: "\<not> Lng M \<le> Suc 0" using L by simp
      have nzM: "\<not> zeroT M" using notone by (auto simp: zeroT_def)
      show ?thesis
      proof (cases "monoT M")
        case mono: True
        \<comment> \<open>(B) mono branch\<close>
        have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
        have predLng: "Lng (Pred M) < Lng M" using L by (simp add: Pred_def)
        note IHp = less.IH[OF predLng, THEN mp, OF predRT]
        show ?thesis
        proof (cases "Trans (Pred M) = 0\<^sub>B")
          case t1z: True
          \<comment> \<open>(B) \<open>t\<^sub>1 = 0\<close>\<close>
          let ?b = "entry M 1 (Lng M - 1)"
          have tv: "Trans M = Dpt 0 (Dpt (enat ?b) 0\<^sub>B)"
            using Trans.psimps[OF domT] MR Lgt1 mono t1z by (simp add: Let_def)
          have kv: "\<And>m. Mark M m = (if m = 0 then Dpt 0 (Dpt (enat ?b) 0\<^sub>B)
                                    else Dpt (enat ?b) 0\<^sub>B)"
            using Mark.psimps[OF domK] MR Lgt1 mono t1z by (simp add: Let_def)
          have df: "dfree_BT (Dpt 0 (Dpt (enat ?b) 0\<^sub>B))"
               and df2: "dfree_BT (Dpt (enat ?b) 0\<^sub>B)"
            by (simp_all add: zero_enat_def)
          have nzT: "Trans M \<noteq> 0\<^sub>B" using tv by simp
          have mb1: "(Dpt 0 (Dpt (enat ?b) 0\<^sub>B), Dpt 0 (Dpt (enat ?b) 0\<^sub>B)) \<in> MarkedB"
          proof -
            have "scb_decomp (Dpt 0 (Dpt (enat ?b) 0\<^sub>B)) []
                    (flatBT (Dpt 0 (Dpt (enat ?b) 0\<^sub>B))) []"
              by (rule scb_decomp_self)
                 (rule isPTB_str_Dpt, simp_all add: zero_enat_def)
            thus ?thesis unfolding MarkedB_def by auto
          qed
          have mb2: "(Dpt 0 (Dpt (enat ?b) 0\<^sub>B), Dpt (enat ?b) 0\<^sub>B) \<in> MarkedB"
          proof -
            have "flatBT (Dpt 0 (Dpt (enat ?b) 0\<^sub>B))
                  = [Dsym 0] @ flatBT (Dpt (enat ?b) 0\<^sub>B) @ []" by simp
            hence "scb_decomp (Dpt 0 (Dpt (enat ?b) 0\<^sub>B)) [Dsym 0]
                     (flatBT (Dpt (enat ?b) 0\<^sub>B)) []"
              unfolding scb_decomp_def
              using isPTB_str_Dpt[of "enat ?b" "0\<^sub>B"] by simp
            thus ?thesis unfolding MarkedB_def by auto
          qed
          show ?thesis using tv kv df df2 nzT mb1 mb2 nzM by simp
        next
          case t1ne: False
          \<comment> \<open>(B) \<open>t\<^sub>1 \<noteq> 0\<close>: the dedicated hard-branch lemma\<close>
          have IHt1: "dfree_BT (Trans (Pred M))" using IHp by simp
          have IHmk: "\<And>m'. (Pred M, m') \<in> Marked
                       \<Longrightarrow> dfree_BT (Mark (Pred M) m')
                         \<and> (Trans (Pred M), Mark (Pred M) m') \<in> MarkedB"
            using IHp by simp
          have res: "dfree_BT (Trans M) \<and> Trans M \<noteq> 0\<^sub>B
              \<and> (\<forall>m. (M, m) \<in> Marked
                     \<longrightarrow> dfree_BT (Mark M m) \<and> (Trans M, Mark M m) \<in> MarkedB)"
            by (rule trans_inv_B_hard[OF MR mono L t1ne IHt1 IHmk])
          show ?thesis using res by blast
        qed
      next
        case nmono: False
        \<comment> \<open>(C) multiT branch: the dedicated lemma\<close>
        have muM: "multiT M" using nzM nmono by (simp add: multiT_def)
        have cut: "0 < Pcut M \<and> Pcut M \<le> Lng M - 1" using Pcut_le[OF L] by simp
        have Acut_RT: "take (Pcut M) M \<in> RT_PS"
          by (rule trans_multiT_prefix_RT_PS[OF MR muM])
        have LA: "Lng (take (Pcut M) M) < Lng M"
        proof -
          have "Pcut M < Lng M" using cut L by linarith
          thus ?thesis by (simp add: min_def)
        qed
        have PJeq: "P M ! (Lng (P M) - 1) = drop (Pcut M) M"
          by (rule trans_multiT_last_component(1)[OF MT muM])
        have Pne: "P M \<noteq> []" by (rule P_nonempty)
        have J1lt: "Lng (P M) - 1 < Lng (P M)" using Pne by (cases "P M") auto
        have PJ_RT: "drop (Pcut M) M \<in> RT_PS"
          using m_6_6_P_reduced[OF MT] MR J1lt PJeq by auto
        have LPJ: "Lng (drop (Pcut M) M) < Lng M"
        proof -
          have "Lng (drop (Pcut M) M) = Lng M - Pcut M" by simp
          thus ?thesis using cut L by linarith
        qed
        note IHA = less.IH[OF LA, THEN mp, OF Acut_RT]
        note IHJ = less.IH[OF LPJ, THEN mp, OF PJ_RT]
        have dfTA: "dfree_BT (Trans (take (Pcut M) M))" using IHA by simp
        have dfTJ: "dfree_BT (Trans (drop (Pcut M) M))" using IHJ by simp
        have nzTJ: "\<not> zeroT (drop (Pcut M) M) \<Longrightarrow> Trans (drop (Pcut M) M) \<noteq> 0\<^sub>B"
          using IHJ by simp
        have IHmkJ: "\<And>m'. (drop (Pcut M) M, m') \<in> Marked
                     \<Longrightarrow> dfree_BT (Mark (drop (Pcut M) M) m')
                       \<and> (Trans (drop (Pcut M) M), Mark (drop (Pcut M) M) m')
                          \<in> MarkedB"
          using IHJ by simp
        have res: "dfree_BT (Trans M) \<and> Trans M \<noteq> 0\<^sub>B
            \<and> (\<forall>m. (M, m) \<in> Marked
                   \<longrightarrow> dfree_BT (Mark M m) \<and> (Trans M, Mark M m) \<in> MarkedB)"
          by (rule trans_inv_C[OF MR muM dfTA dfTJ nzTJ IHmkJ])
        show ?thesis using res by blast
      qed
    qed
  qed
qed

end
