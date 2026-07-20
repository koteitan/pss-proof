theory Support_7_014
  imports Frontier_7_017
begin

lemma gs_pwsum_Nil[simp]: "gs_pwsum [] = 0"
  by (simp add: gs_pwsum_def)
lemma gs_pwsum_Cons[simp]: "gs_pwsum (x # xs) = gs_pw x + gs_pwsum xs"
  by (simp add: gs_pwsum_def)
lemma gs_pwsum_append[simp]: "gs_pwsum (xs @ ys) = gs_pwsum xs + gs_pwsum ys"
  by (simp add: gs_pwsum_def)

lemma gs_pwsum_concat_CM:
  "(\<forall>r \<in> set zs. gs_pwsum (flatBP r) = 0)
     \<Longrightarrow> gs_pwsum (concat (map (\<lambda>r. CM # flatBP r) zs)) = 0"
  by (induct zs) auto

lemma gs_pwsum_flatBT: "gs_pwsum (flatBT t) = 0"
  and gs_pwsum_flatBP: "gs_pwsum (flatBP p) = 0"
proof (induct t and p rule: flatBT_flatBP.induct)
  case 1 show ?case by simp
next
  case (2 p) thus ?case by simp
next
  case (3 p q ps)
  have seg: "gs_pwsum (concat (map (\<lambda>r. CM # flatBP r) (q # ps))) = 0"
    by (rule gs_pwsum_concat_CM) (use 3(2) in auto)
  have "gs_pwsum (flatBT (Trm (p # q # ps)))
        = gs_pwsum (flatBP p)
        + gs_pwsum (concat (map (\<lambda>r. CM # flatBP r) (q # ps)))"
    by simp
  also have "\<dots> = 0" using 3(1) seg by simp
  finally show ?case .
next
  case (4 u a) thus ?case by simp
qed

lemma gs_pwsum_prefix_concat:
  assumes seg_tot: "\<And>r. r \<in> set zs \<Longrightarrow> gs_pwsum (flatBP r) = 0"
    and seg_pre: "\<And>r as bs. r \<in> set zs \<Longrightarrow> flatBP r = as @ bs \<Longrightarrow> bs \<noteq> []
                    \<Longrightarrow> 0 \<le> gs_pwsum as"
    and split: "concat (map (\<lambda>r. CM # flatBP r) zs) = as @ bs"
  shows "0 \<le> gs_pwsum as"
  using assms
proof (induct zs arbitrary: as bs)
  case Nil thus ?case by simp
next
  case (Cons z zs)
  have whole: "concat (map (\<lambda>r. CM # flatBP r) (z # zs))
               = CM # (flatBP z @ concat (map (\<lambda>r. CM # flatBP r) zs))"
    by simp
  show ?case
  proof (cases as)
    case Nil thus ?thesis by simp
  next
    case (Cons a0 as')
    have a0: "a0 = CM" and rest: "as' @ bs = flatBP z @ concat (map (\<lambda>r. CM # flatBP r) zs)"
      using Cons whole Cons.prems(3) by auto
    have us: "\<exists>us. (as' = flatBP z @ us \<and> us @ bs = concat (map (\<lambda>r. CM # flatBP r) zs))
       \<or> (as' @ us = flatBP z \<and> bs = us @ concat (map (\<lambda>r. CM # flatBP r) zs))"
      using append_eq_append_conv2[THEN iffD1, OF rest] .
    have "0 \<le> gs_pwsum as'"
      using us
    proof (elim exE disjE conjE)
        fix us
        assume A1: "as' = flatBP z @ us"
          and A2: "us @ bs = concat (map (\<lambda>r. CM # flatBP r) zs)"
        have ztot: "gs_pwsum (flatBP z) = 0"
          using Cons.prems(1)[of z] by simp
        have "0 \<le> gs_pwsum us"
          using Cons.hyps[OF _ _ A2[symmetric]] Cons.prems(1) Cons.prems(2) by auto
        thus ?thesis using A1 ztot by simp
      next
        fix us
        assume B1: "as' @ us = flatBP z"
          and B2: "bs = us @ concat (map (\<lambda>r. CM # flatBP r) zs)"
        show ?thesis
        proof (cases "us = []")
          case True
          hence "as' = flatBP z" using B1 by simp
          thus ?thesis using Cons.prems(1)[of z] by simp
        next
          case False
          have "flatBP z = as' @ us" using B1 by simp
          thus ?thesis using Cons.prems(2)[of z as' us] False by simp
        qed
      qed
    thus ?thesis using Cons a0 by simp
  qed
qed

lemma gs_pwsum_prefix_nonneg_BT:
  "flatBT t = as @ bs \<Longrightarrow> bs \<noteq> [] \<Longrightarrow> 0 \<le> gs_pwsum as"
  and gs_pwsum_prefix_nonneg_BP:
  "flatBP p = as @ bs \<Longrightarrow> bs \<noteq> [] \<Longrightarrow> 0 \<le> gs_pwsum as"
proof (induct t and p arbitrary: as bs and as bs rule: flatBT_flatBP.induct)
  case (1 as bs)
  thus ?case by (cases as) auto
next
  case (2 p as bs)
  have "flatBP p = as @ bs" using 2(2) by simp
  thus ?case using 2(1)[of as bs] 2(3) by simp
next
  case (3 p q ps as bs)
  define inner where "inner = flatBP p @ concat (map (\<lambda>r. CM # flatBP r) (q # ps))"
  have flat: "flatBT (Trm (p # q # ps)) = LP # inner @ [RP]"
    unfolding inner_def by simp
  show ?case
  proof (cases as)
    case Nil thus ?thesis by simp
  next
    case (Cons a0 as')
    have a0: "a0 = LP" and rest: "as' @ bs = inner @ [RP]"
      using Cons flat 3(3) by auto
    have key: "-1 \<le> gs_pwsum as'"
    proof (cases "length as' \<le> length inner")
      case True
      from rest True have as'_pre: "as' = take (length as') inner"
        by (metis append_eq_conv_conj append_take_drop_id length_append
                  take_all_iff take_append)
      define cs where "cs = drop (length as') inner"
      have inner_eq: "as' @ cs = flatBP p @ concat (map (\<lambda>r. CM # flatBP r) (q # ps))"
        unfolding cs_def using as'_pre inner_def by (metis append_take_drop_id)
      have us: "\<exists>us. (as' = flatBP p @ us
                      \<and> us @ cs = concat (map (\<lambda>r. CM # flatBP r) (q # ps)))
                   \<or> (as' @ us = flatBP p \<and> cs = us @ concat (map (\<lambda>r. CM # flatBP r) (q # ps)))"
        using append_eq_append_conv2[THEN iffD1, OF inner_eq] .
      show ?thesis
        using us
      proof (elim exE disjE conjE)
        fix us
        assume A1: "as' = flatBP p @ us"
          and A2: "us @ cs = concat (map (\<lambda>r. CM # flatBP r) (q # ps))"
        have ptot: "gs_pwsum (flatBP p) = 0"
          using gs_pwsum_flatBP[of p] .
        have us_nn: "0 \<le> gs_pwsum us"
          by (rule gs_pwsum_prefix_concat[where zs="q # ps" and as=us and bs=cs])
             (use A2[symmetric] gs_pwsum_flatBP 3(2) in auto)
        show ?thesis using A1 ptot us_nn by simp
      next
        fix us
        assume B1: "as' @ us = flatBP p"
          and B2: "cs = us @ concat (map (\<lambda>r. CM # flatBP r) (q # ps))"
        show ?thesis
        proof (cases "us = []")
          case True
          hence "as' = flatBP p" using B1 by simp
          thus ?thesis using gs_pwsum_flatBP[of p] by simp
        next
          case False
          have "flatBP p = as' @ us" using B1 by simp
          thus ?thesis using 3(1)[of as' us] False by simp
        qed
      qed
    next
      case False
      have len_ge: "length as' \<ge> length (inner @ [RP])"
        using False by simp
      have len_eq: "length as' + length bs = length (inner @ [RP])"
        using rest by (metis length_append)
      have "length bs = 0" using len_ge len_eq by linarith
      hence "bs = []" by simp
      thus ?thesis using 3(4) by simp
    qed
    show ?thesis using Cons a0 key by simp
  qed
next
  case (4 u a as bs)
  show ?case
  proof (cases as)
    case Nil thus ?thesis by simp
  next
    case (Cons a0 as')
    have a0: "a0 = Dsym u" and rest: "as' @ bs = flatBT a"
      using Cons 4(2) by auto
    have "0 \<le> gs_pwsum as'"
      using 4(1)[of as' bs] rest 4(3) by simp
    thus ?thesis using Cons a0 by simp
  qed
qed

\<comment> \<open>Prefix of the tuple BODY \<open>flatBP p @ concat ..\<close> is \<open>gs_pwsum\<close>-nonneg.\<close>
lemma gs_pwsum_prefix_body:
  assumes split: "flatBP p @ concat (map (\<lambda>r. CM # flatBP r) zs) = as @ bs"
  shows "0 \<le> gs_pwsum as"
proof -
  have us: "\<exists>us. (flatBP p = as @ us \<and> us @ concat (map (\<lambda>r. CM # flatBP r) zs) = bs)
                \<or> (flatBP p @ us = as \<and> concat (map (\<lambda>r. CM # flatBP r) zs) = us @ bs)"
    using append_eq_append_conv2[THEN iffD1, OF split] by blast
  thus ?thesis
  proof (elim exE disjE conjE)
    \<comment> \<open>\<open>as\<close> is a prefix of \<open>flatBP p\<close>.\<close>
    fix us
    assume A1: "flatBP p = as @ us"
       and A2: "us @ concat (map (\<lambda>r. CM # flatBP r) zs) = bs"
    show ?thesis
    proof (cases "us = []")
      case True hence "as = flatBP p" using A1 by simp
      thus ?thesis using gs_pwsum_flatBP[of p] by simp
    next
      case False
      thus ?thesis using gs_pwsum_prefix_nonneg_BP[of p as us] A1 by simp
    qed
  next
    \<comment> \<open>\<open>flatBP p\<close> is a prefix of \<open>as = flatBP p @ us\<close>; \<open>us\<close> a prefix of the concat.\<close>
    fix us
    assume B1: "flatBP p @ us = as"
       and B2: "concat (map (\<lambda>r. CM # flatBP r) zs) = us @ bs"
    have ptot: "gs_pwsum (flatBP p) = 0" by (rule gs_pwsum_flatBP)
    have "0 \<le> gs_pwsum us"
      by (rule gs_pwsum_prefix_concat[where zs=zs and as=us and bs=bs])
         (use B2 gs_pwsum_flatBP gs_pwsum_prefix_nonneg_BP in auto)
    thus ?thesis using B1[symmetric] ptot by simp
  qed
qed

text \<open>Concat-body helper: locate the \<open>flatBP pr\<close> occurrence within one chunk of
  \<open>concat (map (\<lambda>r. CM # flatBP r) zs)\<close> and replace it by \<open>flatBP pr'\<close>, given a
  per-chunk replacement IH.  \<open>pr\<close>, \<open>pr'\<close> complete principals.\<close>

lemma gensurg_concat:
  assumes seg_repl: "\<forall>r \<in> set zs. \<forall>s b. dfree_BP r \<and> flatBP r = s @ flatBP pr @ b
                       \<longrightarrow> (\<exists>r'. flatBP r' = s @ flatBP pr' @ b \<and> dfree_BP r')"
      and dfz: "\<forall>r \<in> set zs. dfree_BP r"
      and dpr': "dfree_BP pr'"
      and split: "concat (map (\<lambda>r. CM # flatBP r) zs) = s @ flatBP pr @ b"
  shows "\<exists>zs'. concat (map (\<lambda>r. CM # flatBP r) zs') = s @ flatBP pr' @ b
              \<and> (\<forall>r \<in> set zs'. dfree_BP r) \<and> length zs' = length zs"
  using assms
proof (induct zs arbitrary: s b)
  case Nil
  hence "[] = s @ flatBP pr @ b" by simp
  hence "flatBP pr = []" by (cases s) auto
  thus ?case using flatBP_nonempty by simp
next
  case (Cons z zs)
  have whole: "concat (map (\<lambda>r. CM # flatBP r) (z # zs))
                 = CM # (flatBP z @ concat (map (\<lambda>r. CM # flatBP r) zs))"
    by simp
  obtain uu prest where prhd: "flatBP pr = Dsym uu # prest" using flatBP_hd by blast
  obtain s' where s_eq: "s = CM # s'"
    using Cons.prems(4) whole prhd by (cases s) auto
  have body: "flatBP z @ concat (map (\<lambda>r. CM # flatBP r) zs) = s' @ flatBP pr @ b"
    using Cons.prems(4) whole s_eq by simp
  have us: "\<exists>us. (flatBP z = s' @ us \<and> us @ concat (map (\<lambda>r. CM # flatBP r) zs) = flatBP pr @ b)
                \<or> (flatBP z @ us = s' \<and> concat (map (\<lambda>r. CM # flatBP r) zs) = us @ flatBP pr @ b)"
    using append_eq_append_conv2[THEN iffD1, OF body] by blast
  from us obtain us where
    U: "(flatBP z = s' @ us \<and> us @ concat (map (\<lambda>r. CM # flatBP r) zs) = flatBP pr @ b)
       \<or> (flatBP z @ us = s' \<and> concat (map (\<lambda>r. CM # flatBP r) zs) = us @ flatBP pr @ b)"
    by blast
  thus ?case
  proof (elim disjE conjE)
    assume A1: "flatBP z = s' @ us"
       and A2: "us @ concat (map (\<lambda>r. CM # flatBP r) zs) = flatBP pr @ b"
    have us2: "\<exists>ws. (flatBP pr = us @ ws \<and> ws @ b = concat (map (\<lambda>r. CM # flatBP r) zs))
                  \<or> (flatBP pr @ ws = us \<and> b = ws @ concat (map (\<lambda>r. CM # flatBP r) zs))"
      using append_eq_append_conv2[THEN iffD1, OF A2[symmetric]] by blast
    from us2 obtain ws where
      W: "(flatBP pr = us @ ws \<and> ws @ b = concat (map (\<lambda>r. CM # flatBP r) zs))
        \<or> (flatBP pr @ ws = us \<and> b = ws @ concat (map (\<lambda>r. CM # flatBP r) zs))" by blast
    thus ?thesis
    proof (elim disjE conjE)
      assume Ai1: "flatBP pr = us @ ws"
         and Ai2: "ws @ b = concat (map (\<lambda>r. CM # flatBP r) zs)"
      show ?thesis
      proof (cases "ws = []")
        case True
        have fz: "flatBP z = s' @ flatBP pr @ []" using A1 Ai1 True by simp
        have dz: "dfree_BP z" using Cons.prems(2) by simp
        have zmem: "z \<in> set (z # zs)" by simp
        obtain z' where z': "flatBP z' = s' @ flatBP pr' @ [] \<and> dfree_BP z'"
          using Cons.prems(1) zmem dz fz by blast
        have b_tail: "b = concat (map (\<lambda>r. CM # flatBP r) zs)"
          using Ai2 True by simp
        let ?zs' = "z' # zs"
        have "concat (map (\<lambda>r. CM # flatBP r) ?zs')
               = CM # (flatBP z' @ concat (map (\<lambda>r. CM # flatBP r) zs))"
          by simp
        also have "\<dots> = CM # ((s' @ flatBP pr') @ b)" using z' b_tail by simp
        also have "\<dots> = s @ flatBP pr' @ b" using s_eq by simp
        finally have c1: "concat (map (\<lambda>r. CM # flatBP r) ?zs') = s @ flatBP pr' @ b" .
        have c2: "\<forall>r \<in> set ?zs'. dfree_BP r" using z' Cons.prems(2) by simp
        have c3: "length ?zs' = length (z # zs)" by simp
        show ?thesis using c1 c2 c3 by blast
      next
        case False
        show ?thesis
        proof (cases "us = []")
          case usNil: True
          have tail_split: "concat (map (\<lambda>r. CM # flatBP r) zs) = [] @ flatBP pr @ b"
            using Ai1 Ai2 usNil by simp
          have seg_repl': "\<forall>r \<in> set zs. \<forall>s b. dfree_BP r \<and> flatBP r = s @ flatBP pr @ b
                            \<longrightarrow> (\<exists>r'. flatBP r' = s @ flatBP pr' @ b \<and> dfree_BP r')"
            using Cons.prems(1) by (meson list.set_intros(2))
          have dfz': "\<forall>r \<in> set zs. dfree_BP r" using Cons.prems(2) by simp
          from Cons.hyps[OF seg_repl' dfz' Cons.prems(3) tail_split]
          obtain zs' where Z: "concat (map (\<lambda>r. CM # flatBP r) zs') = [] @ flatBP pr' @ b
                                \<and> (\<forall>r \<in> set zs'. dfree_BP r) \<and> length zs' = length zs" by blast
          let ?zs' = "z # zs'"
          have "concat (map (\<lambda>r. CM # flatBP r) ?zs')
                 = CM # (flatBP z @ concat (map (\<lambda>r. CM # flatBP r) zs'))" by simp
          also have "\<dots> = CM # (flatBP z @ flatBP pr' @ b)" using Z by simp
          also have "\<dots> = CM # (s' @ flatBP pr' @ b)" using A1 usNil by simp
          also have "\<dots> = s @ flatBP pr' @ b" using s_eq by simp
          finally have c1: "concat (map (\<lambda>r. CM # flatBP r) ?zs') = s @ flatBP pr' @ b" .
          have c2: "\<forall>r \<in> set ?zs'. dfree_BP r" using Z Cons.prems(2) by simp
          have c3: "length ?zs' = length (z # zs)" using Z by simp
          show ?thesis using c1 c2 c3 by blast
        next
          case usCons: False
          \<comment> \<open>straddle: contradiction by prefix weights.\<close>
          have us_pre_occ: "0 \<le> flatinj_dsum us"
            using flatinj_prefix_nonneg_BP[OF Ai1 False] .
          have fz_tot: "flatinj_dsum (flatBP z) = -1" by (rule flatinj_dsum_flatBP)
          have s'_pre: "0 \<le> flatinj_dsum s'"
            using flatinj_prefix_nonneg_BP[OF A1 usCons] .
          have "flatinj_dsum s' + flatinj_dsum us = -1"
            using A1 fz_tot by (metis flatinj_dsum_append)
          hence "flatinj_dsum us \<le> -1" using s'_pre by simp
          thus ?thesis using us_pre_occ by simp
        qed
      qed
    next
      assume Aii1: "flatBP pr @ ws = us"
         and Aii2: "b = ws @ concat (map (\<lambda>r. CM # flatBP r) zs)"
      have fz: "flatBP z = s' @ flatBP pr @ ws" using A1 Aii1 by simp
      have dz: "dfree_BP z" using Cons.prems(2) by simp
      have zmem: "z \<in> set (z # zs)" by simp
      obtain z' where z': "flatBP z' = s' @ flatBP pr' @ ws \<and> dfree_BP z'"
        using Cons.prems(1) zmem dz fz by blast
      let ?zs' = "z' # zs"
      have "concat (map (\<lambda>r. CM # flatBP r) ?zs')
             = CM # (flatBP z' @ concat (map (\<lambda>r. CM # flatBP r) zs))" by simp
      also have "\<dots> = CM # ((s' @ flatBP pr' @ ws) @ concat (map (\<lambda>r. CM # flatBP r) zs))"
        using z' by simp
      also have "\<dots> = CM # (s' @ flatBP pr' @ b)" using Aii2 by simp
      also have "\<dots> = s @ flatBP pr' @ b" using s_eq by simp
      finally have c1: "concat (map (\<lambda>r. CM # flatBP r) ?zs') = s @ flatBP pr' @ b" .
      have c2: "\<forall>r \<in> set ?zs'. dfree_BP r" using z' Cons.prems(2) by simp
      have c3: "length ?zs' = length (z # zs)" by simp
      show ?thesis using c1 c2 c3 by blast
    qed
  next
    assume B1: "flatBP z @ us = s'"
       and B2: "concat (map (\<lambda>r. CM # flatBP r) zs) = us @ flatBP pr @ b"
    have seg_repl': "\<forall>r \<in> set zs. \<forall>s b. dfree_BP r \<and> flatBP r = s @ flatBP pr @ b
                       \<longrightarrow> (\<exists>r'. flatBP r' = s @ flatBP pr' @ b \<and> dfree_BP r')"
      using Cons.prems(1) by (meson list.set_intros(2))
    have dfz': "\<forall>r \<in> set zs. dfree_BP r" using Cons.prems(2) by simp
    from Cons.hyps[OF seg_repl' dfz' Cons.prems(3) B2]
    obtain zs' where Z: "concat (map (\<lambda>r. CM # flatBP r) zs') = us @ flatBP pr' @ b
                          \<and> (\<forall>r \<in> set zs'. dfree_BP r) \<and> length zs' = length zs" by blast
    let ?zs' = "z # zs'"
    have "concat (map (\<lambda>r. CM # flatBP r) ?zs')
           = CM # (flatBP z @ concat (map (\<lambda>r. CM # flatBP r) zs'))" by simp
    also have "\<dots> = CM # (flatBP z @ us @ flatBP pr' @ b)" using Z by simp
    also have "\<dots> = CM # (s' @ flatBP pr' @ b)" using B1 by simp
    also have "\<dots> = s @ flatBP pr' @ b" using s_eq by simp
    finally have c1: "concat (map (\<lambda>r. CM # flatBP r) ?zs') = s @ flatBP pr' @ b" .
    have c2: "\<forall>r \<in> set ?zs'. dfree_BP r" using Z Cons.prems(2) by simp
    have c3: "length ?zs' = length (z # zs)" using Z by simp
    show ?thesis using c1 c2 c3 by blast
  qed
qed

text \<open>Inner-body helper: occurrence in \<open>flatBP p @ concat (map ... zs)\<close>.\<close>

lemma gensurg_pbody:
  assumes head_repl: "\<forall>s b. dfree_BP p \<and> flatBP p = s @ flatBP pr @ b
                       \<longrightarrow> (\<exists>p'. flatBP p' = s @ flatBP pr' @ b \<and> dfree_BP p')"
      and seg_repl: "\<forall>r \<in> set zs. \<forall>s b. dfree_BP r \<and> flatBP r = s @ flatBP pr @ b
                       \<longrightarrow> (\<exists>r'. flatBP r' = s @ flatBP pr' @ b \<and> dfree_BP r')"
      and dfp: "dfree_BP p" and dfz: "\<forall>r \<in> set zs. dfree_BP r"
      and dpr': "dfree_BP pr'"
      and split: "flatBP p @ concat (map (\<lambda>r. CM # flatBP r) zs) = s @ flatBP pr @ b"
  shows "\<exists>p' zs'. flatBP p' @ concat (map (\<lambda>r. CM # flatBP r) zs') = s @ flatBP pr' @ b
                \<and> dfree_BP p' \<and> (\<forall>r \<in> set zs'. dfree_BP r) \<and> length zs' = length zs"
proof -
  note seg_obj = seg_repl
  have us: "\<exists>us. (flatBP p = s @ us \<and> us @ concat (map (\<lambda>r. CM # flatBP r) zs) = flatBP pr @ b)
                \<or> (flatBP p @ us = s \<and> concat (map (\<lambda>r. CM # flatBP r) zs) = us @ flatBP pr @ b)"
    using append_eq_append_conv2[THEN iffD1, OF split] by blast
  from us obtain us where
    U: "(flatBP p = s @ us \<and> us @ concat (map (\<lambda>r. CM # flatBP r) zs) = flatBP pr @ b)
       \<or> (flatBP p @ us = s \<and> concat (map (\<lambda>r. CM # flatBP r) zs) = us @ flatBP pr @ b)"
    by blast
  thus ?thesis
  proof (elim disjE conjE)
    assume A1: "flatBP p = s @ us"
       and A2: "us @ concat (map (\<lambda>r. CM # flatBP r) zs) = flatBP pr @ b"
    have us2: "\<exists>ws. (flatBP pr = us @ ws \<and> ws @ b = concat (map (\<lambda>r. CM # flatBP r) zs))
                  \<or> (flatBP pr @ ws = us \<and> b = ws @ concat (map (\<lambda>r. CM # flatBP r) zs))"
      using append_eq_append_conv2[THEN iffD1, OF A2[symmetric]] by blast
    from us2 obtain ws where
      W: "(flatBP pr = us @ ws \<and> ws @ b = concat (map (\<lambda>r. CM # flatBP r) zs))
        \<or> (flatBP pr @ ws = us \<and> b = ws @ concat (map (\<lambda>r. CM # flatBP r) zs))" by blast
    thus ?thesis
    proof (elim disjE conjE)
      assume Ai1: "flatBP pr = us @ ws"
         and Ai2: "ws @ b = concat (map (\<lambda>r. CM # flatBP r) zs)"
      show ?thesis
      proof (cases "ws = []")
        case True
        have fz: "flatBP p = s @ flatBP pr @ []" using A1 Ai1 True by simp
        obtain p' where p': "flatBP p' = s @ flatBP pr' @ [] \<and> dfree_BP p'"
          using head_repl dfp fz by blast
        have b_tail: "b = concat (map (\<lambda>r. CM # flatBP r) zs)" using Ai2 True by simp
        have c1: "flatBP p' @ concat (map (\<lambda>r. CM # flatBP r) zs) = s @ flatBP pr' @ b"
          using p' b_tail by simp
        show ?thesis using c1 p' dfz by blast
      next
        case False
        show ?thesis
        proof (cases "us = []")
          case usNil: True
          have tail_split: "concat (map (\<lambda>r. CM # flatBP r) zs) = [] @ flatBP pr @ b"
            using Ai1 Ai2 usNil by simp
          from gensurg_concat[OF seg_obj dfz dpr' tail_split]
          obtain zs' where Z: "concat (map (\<lambda>r. CM # flatBP r) zs') = [] @ flatBP pr' @ b
                                \<and> (\<forall>r \<in> set zs'. dfree_BP r) \<and> length zs' = length zs" by blast
          have s_p: "s = flatBP p" using A1 usNil by simp
          have c1: "flatBP p @ concat (map (\<lambda>r. CM # flatBP r) zs') = s @ flatBP pr' @ b"
            using Z s_p by simp
          show ?thesis using c1 dfp Z by blast
        next
          case usCons: False
          have us_pre_occ: "0 \<le> flatinj_dsum us"
            using flatinj_prefix_nonneg_BP[OF Ai1 False] .
          have fp_tot: "flatinj_dsum (flatBP p) = -1" by (rule flatinj_dsum_flatBP)
          have s_pre: "0 \<le> flatinj_dsum s"
            using flatinj_prefix_nonneg_BP[OF A1 usCons] .
          have "flatinj_dsum s + flatinj_dsum us = -1"
            using A1 fp_tot by (metis flatinj_dsum_append)
          hence "flatinj_dsum us \<le> -1" using s_pre by simp
          thus ?thesis using us_pre_occ by simp
        qed
      qed
    next
      assume Aii1: "flatBP pr @ ws = us"
         and Aii2: "b = ws @ concat (map (\<lambda>r. CM # flatBP r) zs)"
      have fz: "flatBP p = s @ flatBP pr @ ws" using A1 Aii1 by simp
      obtain p' where p': "flatBP p' = s @ flatBP pr' @ ws \<and> dfree_BP p'"
        using head_repl dfp fz by blast
      have c1: "flatBP p' @ concat (map (\<lambda>r. CM # flatBP r) zs) = s @ flatBP pr' @ b"
        using p' Aii2 by simp
      show ?thesis using c1 p' dfz by blast
    qed
  next
    assume B1: "flatBP p @ us = s"
       and B2: "concat (map (\<lambda>r. CM # flatBP r) zs) = us @ flatBP pr @ b"
    from gensurg_concat[OF seg_obj dfz dpr' B2]
    obtain zs' where Z: "concat (map (\<lambda>r. CM # flatBP r) zs') = us @ flatBP pr' @ b
                          \<and> (\<forall>r \<in> set zs'. dfree_BP r) \<and> length zs' = length zs" by blast
    have c1: "flatBP p @ concat (map (\<lambda>r. CM # flatBP r) zs') = s @ flatBP pr' @ b"
      using Z B1 by simp
    show ?thesis using c1 dfp Z by blast
  qed
qed

text \<open>MAIN generalized principal-replacement surgery (BT + BP).\<close>

lemma gensurg_main:
  shows "\<And>s b. flatBT u = s @ flatBP pr @ b \<Longrightarrow> dfree_BT u \<Longrightarrow> dfree_BP pr' \<Longrightarrow>
            (\<exists>u'. flatBT u' = s @ flatBP pr' @ b \<and> dfree_BT u')"
    and "\<And>s b. flatBP p = s @ flatBP pr @ b \<Longrightarrow> dfree_BP p \<Longrightarrow> dfree_BP pr' \<Longrightarrow>
            (\<exists>p'. flatBP p' = s @ flatBP pr' @ b \<and> dfree_BP p')"
proof (induct u and p arbitrary: s b and s b rule: flatBT_flatBP.induct)
  case (1 s b)
  obtain uu prest where prhd: "flatBP pr = Dsym uu # prest" using flatBP_hd by blast
  have "[Zsym] = s @ flatBP pr @ b" using "1.prems"(1) by simp
  thus ?case using prhd by (cases s) auto
next
  case (2 p s b)
  have fp: "flatBP p = s @ flatBP pr @ b" using "2.prems"(1) by simp
  have dfp: "dfree_BP p" using "2.prems"(2) by simp
  from "2.hyps"[OF fp dfp "2.prems"(3)]
  obtain p' where p': "flatBP p' = s @ flatBP pr' @ b \<and> dfree_BP p'" by blast
  have "flatBT (Trm [p']) = s @ flatBP pr' @ b" using p' by simp
  moreover have "dfree_BT (Trm [p'])" using p' by simp
  ultimately show ?case by blast
next
  case (3 p q ps s b)
  note IH3head = "3.hyps"(1)
  note IH3seg = "3.hyps"(2)
  have ft: "flatBT (Trm (p # q # ps))
            = LP # (flatBP p @ concat (map (\<lambda>r. CM # flatBP r) (q # ps))) @ [RP]"
    by simp
  have eq: "LP # (flatBP p @ concat (map (\<lambda>r. CM # flatBP r) (q # ps))) @ [RP]
              = s @ flatBP pr @ b"
    using "3.prems"(1) ft by simp
  obtain uu prest where prhd: "flatBP pr = Dsym uu # prest" using flatBP_hd by blast
  obtain s' where s_eq: "s = LP # s'"
    using eq prhd by (cases s) auto
  define body where "body = flatBP p @ concat (map (\<lambda>r. CM # flatBP r) (q # ps))"
  have body_eq: "body @ [RP] = s' @ flatBP pr @ b"
    using eq s_eq body_def by simp
  \<comment> \<open>\<open>b \<noteq> []\<close>: a complete principal \<open>flatBP pr\<close> cannot end at the wrap RP.\<close>
  have b_ne: "b \<noteq> []"
  proof
    assume bNil: "b = []"
    have e: "body @ [RP] = s' @ flatBP pr" using body_eq bNil by simp
    have occ_ne: "flatBP pr \<noteq> []" using flatBP_nonempty .
    have occ_tot: "gs_pwsum (flatBP pr) = 0" by (rule gs_pwsum_flatBP)
    \<comment> \<open>\<open>flatBP pr\<close> ends in the wrap \<open>RP\<close>: \<open>last (s' @ flatBP pr) = last (body @ [RP]) = RP\<close>.\<close>
    have "last (s' @ flatBP pr) = RP" using e by (metis last_snoc)
    hence last_rp: "last (flatBP pr) = RP" using occ_ne by (simp add: last_append)
    obtain ds where occ_ds: "flatBP pr = ds @ [RP]"
      using occ_ne last_rp by (metis append_butlast_last_id)
    have body2: "body = s' @ ds" using e occ_ds by simp
    have ds_w: "gs_pwsum ds = 1" using occ_ds occ_tot by simp
    have body_tot: "gs_pwsum body = 0"
      using body_def gs_pwsum_flatBP[of p]
            gs_pwsum_concat_CM[of "q # ps"] gs_pwsum_flatBP by simp
    have s'_w: "gs_pwsum s' = -1" using body2 ds_w body_tot by simp
    have s'_pre: "0 \<le> gs_pwsum s'"
      using gs_pwsum_prefix_body[where p=p and zs="q # ps" and as=s' and bs=ds]
            body2[unfolded body_def] by simp
    show False using s'_w s'_pre by simp
  qed
  obtain b' where b_eq: "b = b' @ [RP]" and body_split: "body = s' @ flatBP pr @ b'"
  proof -
    obtain bs bl where bsnoc: "b = bs @ [bl]"
      using b_ne by (meson rev_exhaust)
    have rhs_last: "last (s' @ flatBP pr @ b) = RP" using body_eq by (metis last_snoc)
    have bl_rp: "bl = RP" using body_eq bsnoc rhs_last by simp
    have e: "body @ [RP] = (s' @ flatBP pr @ bs) @ [RP]"
      using body_eq bsnoc bl_rp by simp
    have "body = s' @ flatBP pr @ bs" using e by simp
    thus ?thesis using bsnoc bl_rp that[of bs] by simp
  qed
  have dfp: "dfree_BP p" using "3.prems"(2) by simp
  have dfz: "\<forall>r \<in> set (q # ps). dfree_BP r" using "3.prems"(2) by simp
  have head_repl: "\<forall>s b. dfree_BP p \<and> flatBP p = s @ flatBP pr @ b
                     \<longrightarrow> (\<exists>p'. flatBP p' = s @ flatBP pr' @ b \<and> dfree_BP p')"
    using IH3head "3.prems"(3) by blast
  have seg_repl: "\<forall>r \<in> set (q # ps). \<forall>s b. dfree_BP r \<and> flatBP r = s @ flatBP pr @ b
                     \<longrightarrow> (\<exists>r'. flatBP r' = s @ flatBP pr' @ b \<and> dfree_BP r')"
    using IH3seg "3.prems"(3) by blast
  have split': "flatBP p @ concat (map (\<lambda>r. CM # flatBP r) (q # ps)) = s' @ flatBP pr @ b'"
    using body_split body_def by simp
  from gensurg_pbody[OF head_repl seg_repl dfp dfz "3.prems"(3) split']
  obtain p' zs' where R: "flatBP p' @ concat (map (\<lambda>r. CM # flatBP r) zs') = s' @ flatBP pr' @ b'
                          \<and> dfree_BP p' \<and> (\<forall>r \<in> set zs'. dfree_BP r) \<and> length zs' = length (q # ps)"
    by blast
  have len_zs': "length zs' = Suc (length ps)" using R by simp
  then obtain q' ps' where zs'eq: "zs' = q' # ps'" by (cases zs') auto
  have "flatBT (Trm (p' # q' # ps'))
          = LP # (flatBP p' @ concat (map (\<lambda>r. CM # flatBP r) (q' # ps'))) @ [RP]"
    by simp
  also have "\<dots> = LP # (s' @ flatBP pr' @ b') @ [RP]" using R zs'eq by simp
  also have "\<dots> = (LP # s') @ flatBP pr' @ (b' @ [RP])" by simp
  also have "\<dots> = s @ flatBP pr' @ b" using s_eq b_eq by simp
  finally have c1: "flatBT (Trm (p' # q' # ps')) = s @ flatBP pr' @ b" .
  have c2: "dfree_BT (Trm (p' # q' # ps'))" using R zs'eq by simp
  show ?case using c1 c2 by blast
next
  case (4 w c s b)
  have fp: "Dsym w # flatBT c = s @ flatBP pr @ b" using "4.prems"(1) by simp
  show ?case
  proof (cases s)
    case Nil
    \<comment> \<open>\<open>s = []\<close>: head match; \<open>flatBP pr\<close> is a prefix of \<open>flatBP (DB w c)\<close>.  Both
       complete \<Rightarrow> equal, \<open>b = []\<close>; witness \<open>pr'\<close>.\<close>
    have fp0: "flatBP (DB w c) = flatBP pr @ b" using fp Nil by simp
    have b0: "b = []"
    proof (rule ccontr)
      assume bne: "b \<noteq> []"
      have "0 \<le> flatinj_dsum (flatBP pr)"
        using flatinj_prefix_nonneg_BP[OF fp0 bne] .
      thus False using flatinj_dsum_flatBP[of pr] by simp
    qed
    have "flatBP pr' = s @ flatBP pr' @ b" using Nil b0 by simp
    thus ?thesis using "4.prems"(3) by blast
  next
    case (Cons s0 s')
    have s0w: "s0 = Dsym w" using fp Cons by simp
    have fc: "flatBT c = s' @ flatBP pr @ b" using fp Cons s0w by simp
    have dfc: "dfree_BT c" using "4.prems"(2) by simp
    from "4.hyps"[OF fc dfc "4.prems"(3)]
    obtain c' where c': "flatBT c' = s' @ flatBP pr' @ b \<and> dfree_BT c'" by blast
    have "flatBP (DB w c') = s @ flatBP pr' @ b" using c' Cons s0w by simp
    moreover have "dfree_BP (DB w c')" using "4.prems"(2) c' by simp
    ultimately show ?thesis by blast
  qed
qed

text \<open>BT-level image-membership corollary: an occurrence of a complete principal
  string \<open>flatBP pr\<close> in \<open>flatBT u\<close> (\<open>u \<in> T\<^bsub>B\<^esub>\<close>) can be replaced by \<open>flatBP pr'\<close>
  (\<open>pr' \<in> PT\<^bsub>B\<^esub>\<close>), the spliced string is in the image of \<open>flatBT\<close> over \<open>T\<^bsub>B\<^esub>\<close>.\<close>

lemma gensurg_image_BT:
  assumes uTB: "u \<in> T_B"
      and dpr': "dfree_BP pr'"
      and flat: "flatBT u = s @ flatBP pr @ b"
  shows "\<exists>u'. u' \<in> T_B \<and> flatBT u' = s @ flatBP pr' @ b"
proof -
  have dfu: "dfree_BT u" using uTB by (simp add: T_B_def)
  from gensurg_main(1)[OF flat dfu dpr']
  obtain u' where u': "flatBT u' = s @ flatBP pr' @ b \<and> dfree_BT u'" by blast
  thus ?thesis by (auto simp: T_B_def)
qed

\<comment> \<open>\<open>+\<^sub>B\<close> preserves \<open>T\<^bsub>B\<^esub>\<close> (concatenation of \<open>D\<^sub>\<omega>\<close>-free principal lists).\<close>
lemma gensurg_addBT_TB:
  assumes "t \<in> T_B" and "c \<in> T_B"
  shows "t +\<^sub>B c \<in> T_B"
proof -
  obtain as where t: "t = Trm as" by (cases t)
  obtain bs where c: "c = Trm bs" by (cases c)
  have "\<forall>p \<in> set (as @ bs). dfree_BP p"
    using assms t c by (auto simp: T_B_def)
  thus ?thesis using t c by (simp add: T_B_def)
qed

text \<open>RESIDUAL DISCHARGED (A13 §7.2 系 add_scb (3) image / \<open>scbrepl_image\<close>): given
  \<open>u\<^sub>1 \<in> T\<^bsub>B\<^esub>\<close> with \<open>flatBT u\<^sub>1 = s\<^sub>1 @ (D\<^sub>v # flatBT (t+c)) @ b\<^sub>1\<close>, the spliced string
  \<open>s\<^sub>1 @ (D\<^sub>v # flatBT (t+c')) @ b\<^sub>1\<close> is realised by some \<open>u\<^sub>1' \<in> T\<^bsub>B\<^esub>\<close>.  This is the
  image-existence hypothesis previously ASSUMED in the A13 reduction.\<close>

lemma m_7_2_add_scb_conj3_image:
  fixes v :: nat
  assumes tTB: "t \<in> T_B" and c'TB: "c' \<in> T_B"
      and u1TB: "u\<^sub>1 \<in> T_B"
      and flat: "flatBT u\<^sub>1 = s\<^sub>1 @ (Dsym (enat v) # flatBT (t +\<^sub>B c)) @ b\<^sub>1"
  shows "\<exists>u\<^sub>1'. u\<^sub>1' \<in> T_B
             \<and> flatBT u\<^sub>1' = s\<^sub>1 @ (Dsym (enat v) # flatBT (t +\<^sub>B c')) @ b\<^sub>1"
proof -
  \<comment> \<open>\<open>D\<^sub>v # flatBT (t+c) = flatBP (DB v (t+c))\<close>; replacement \<open>DB v (t+c')\<close>, both
     \<open>D\<^sub>\<omega>\<close>-free since \<open>v\<close> finite and \<open>t+c' \<in> T\<^bsub>B\<^esub>\<close>.\<close>
  have tc'TB: "t +\<^sub>B c' \<in> T_B" by (rule gensurg_addBT_TB[OF tTB c'TB])
  have occ: "Dsym (enat v) # flatBT (t +\<^sub>B c) = flatBP (DB (enat v) (t +\<^sub>B c))" by simp
  have rep: "Dsym (enat v) # flatBT (t +\<^sub>B c') = flatBP (DB (enat v) (t +\<^sub>B c'))" by simp
  have dfbt: "dfree_BT (t +\<^sub>B c')" using tc'TB by (simp add: T_B_def)
  have dpr': "dfree_BP (DB (enat v) (t +\<^sub>B c'))"
    using dfbt by simp
  have flat': "flatBT u\<^sub>1 = s\<^sub>1 @ flatBP (DB (enat v) (t +\<^sub>B c)) @ b\<^sub>1"
    by (subst occ[symmetric]) (rule flat)
  from gensurg_image_BT[OF u1TB dpr' flat']
  obtain u\<^sub>1' where u': "u\<^sub>1' \<in> T_B
                       \<and> flatBT u\<^sub>1' = s\<^sub>1 @ flatBP (DB (enat v) (t +\<^sub>B c')) @ b\<^sub>1" by blast
  have "flatBT u\<^sub>1' = s\<^sub>1 @ (Dsym (enat v) # flatBT (t +\<^sub>B c')) @ b\<^sub>1"
    by (subst rep) (use u' in simp)
  thus ?thesis using u' by blast
qed

text \<open>RESIDUAL DISCHARGED (\<open>m_7_2_scb_replaceable_corr_mod_image\<close>'s \<open>image\<close>): for an
  scb-decomposition \<open>(s, flat c\<^sub>0, b)\<close> of \<open>t\<^sub>0\<close> with \<open>c\<^sub>0 = Trm [p\<^sub>0]\<close> a genuine
  principal and \<open>c\<^sub>1 = Trm [p\<^sub>1] \<in> T\<^bsub>B\<^esub>\<close> another principal, the spliced string
  \<open>s @ flat c\<^sub>1 @ b\<close> is in the image of \<open>flatBT\<close>.  This is exactly the \<open>image\<close>
  hypothesis of \<open>m_7_2_scb_replaceable_corr_mod_image\<close>.\<close>

lemma scbrepl_image_principal:
  assumes t0TB: "t\<^sub>0 \<in> T_B"
      and c0p: "c\<^sub>0 = Trm [p\<^sub>0]"
      and c1TB: "c\<^sub>1 \<in> T_B" and c1p: "c\<^sub>1 = Trm [p\<^sub>1]"
      and d0: "scb_decomp t\<^sub>0 s (flatBT c\<^sub>0) b"
  shows "\<exists>t\<^sub>1. t\<^sub>1 \<in> T_B \<and> flatBT t\<^sub>1 = s @ flatBT c\<^sub>1 @ b"
proof -
  have flat: "flatBT t\<^sub>0 = s @ flatBP p\<^sub>0 @ b"
    using d0 c0p unfolding scb_decomp_def by simp
  have dpr': "dfree_BP p\<^sub>1" using c1TB c1p by (simp add: T_B_def)
  have c1flat: "flatBT c\<^sub>1 = flatBP p\<^sub>1" using c1p by simp
  from gensurg_image_BT[OF t0TB dpr' flat]
  obtain t\<^sub>1 where t1: "t\<^sub>1 \<in> T_B \<and> flatBT t\<^sub>1 = s @ flatBP p\<^sub>1 @ b" by blast
  thus ?thesis using c1flat by auto
qed

end
