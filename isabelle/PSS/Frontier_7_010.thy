theory Frontier_7_010
  imports Support_7_006
begin

text \<open>
  The forward (1\<Rightarrow>2) and (1\<Rightarrow>3) directions of the triviality equivalence — the
  ones that do NOT need \<^const>\<open>flatBT\<close> injectivity — packaged as reusable facts.
  (1\<Rightarrow>2): if \<open>t = c\<close> then any decomposition has empty \<open>s\<close>,\<open>b\<close> by a length count.
\<close>

lemma scbtriv_eq_imp_trivial_decomp:
  assumes "t = c" and "scb_decomp t s (flatBT c) b"
  shows "s = [] \<and> b = []"
proof -
  from assms have eq: "flatBT c = s @ flatBT c @ b"
    unfolding scb_decomp_def by simp
  have "length (flatBT c) = length s + (length (flatBT c) + length b)"
    using eq by (metis length_append)
  hence "length s = 0 \<and> length b = 0" by linarith
  thus ?thesis by simp
qed


subsection \<open>§7 flatBT injectivity — m_7_flatBT_inj\<close>

text \<open>
  \<^const>\<open>flatBT\<close> is injective: the bracket/comma/Dsym/Zsym flattening of a
  \<^typ>\<open>BT\<close> term is uniquely readable.  The engine is a weight function
  \<open>w\<close> on \<open>Sym\<close> for which every complete \<open>flatBT\<close>/\<open>flatBP\<close> string has total
  weight \<open>-1\<close> while every proper (nonempty) prefix has weight \<open>\<ge> 0\<close>.  This makes
  \<^const>\<open>flatBP\<close> prefix-free (no \<open>flatBP\<close> string is a proper prefix of another),
  which lets us cancel a leading \<^const>\<open>flatBP\<close> and recover the term structure.
\<close>

\<comment> \<open>Per-symbol weight: \<open>LP \<mapsto> 1\<close>, \<open>RP \<mapsto> -1\<close>, \<open>Zsym \<mapsto> -1\<close>, \<open>CM \<mapsto> 1\<close>,
   \<open>Dsym \<mapsto> 0\<close>.\<close>
fun flatinj_w :: "Sym \<Rightarrow> int" where
  "flatinj_w LP = 1"
| "flatinj_w RP = -1"
| "flatinj_w CM = 1"
| "flatinj_w Zsym = -1"
| "flatinj_w (Dsym u) = 0"

definition flatinj_dsum :: "Sym list \<Rightarrow> int" where
  "flatinj_dsum xs = sum_list (map flatinj_w xs)"

lemma flatinj_dsum_Nil[simp]: "flatinj_dsum [] = 0"
  by (simp add: flatinj_dsum_def)

lemma flatinj_dsum_Cons[simp]:
  "flatinj_dsum (x # xs) = flatinj_w x + flatinj_dsum xs"
  by (simp add: flatinj_dsum_def)

lemma flatinj_dsum_append[simp]:
  "flatinj_dsum (xs @ ys) = flatinj_dsum xs + flatinj_dsum ys"
  by (simp add: flatinj_dsum_def)

\<comment> \<open>Total weight of a CM-prefixed segment concat is \<open>0\<close>, given each segment is a
   complete \<open>flatBP\<close> (weight \<open>-1\<close>): each \<open>CM # flatBP r\<close> contributes \<open>1 + (-1) = 0\<close>.\<close>
lemma flatinj_dsum_concat_CM:
  "(\<forall>r \<in> set zs. flatinj_dsum (flatBP r) = -1)
     \<Longrightarrow> flatinj_dsum (concat (map (\<lambda>r. CM # flatBP r) zs)) = 0"
  by (induct zs) auto

\<comment> \<open>Total weight of every complete \<open>flatBT\<close>/\<open>flatBP\<close> string is \<open>-1\<close>.\<close>
lemma flatinj_dsum_flatBT: "flatinj_dsum (flatBT t) = -1"
  and flatinj_dsum_flatBP: "flatinj_dsum (flatBP p) = -1"
proof (induct t and p rule: flatBT_flatBP.induct)
  case 1 show ?case by simp
next
  case (2 p) thus ?case by simp
next
  case (3 p q ps)
  have seg: "flatinj_dsum (concat (map (\<lambda>r. CM # flatBP r) (q # ps))) = 0"
    by (rule flatinj_dsum_concat_CM) (use 3(2) in auto)
  have "flatinj_dsum (flatBT (Trm (p # q # ps)))
        = flatinj_dsum (flatBP p)
        + flatinj_dsum (concat (map (\<lambda>r. CM # flatBP r) (q # ps)))"
    by simp
  also have "\<dots> = -1" using 3(1) seg by simp
  finally show ?case .
next
  case (4 u a) thus ?case by simp
qed

text \<open>
  Prefix positivity: every proper nonempty prefix of a complete \<open>flatBT\<close>/\<open>flatBP\<close>
  string has weight \<open>\<ge> 0\<close>.  Stated as: if the flat string is \<open>as @ bs\<close> with
  \<open>bs \<noteq> []\<close> then \<open>flatinj_dsum as \<ge> 0\<close>.
\<close>

\<comment> \<open>Concat helper: in \<open>concat (map (\<lambda>r. CM # flatBP r) zs)\<close> every prefix is
   nonnegative, given each segment is a complete \<open>flatBP\<close> (weight \<open>-1\<close>, proper
   prefixes \<open>\<ge> 0\<close>).  No \<open>bs \<noteq> []\<close> needed: the trailing CM of each unit lifts the
   boundary back to \<open>0\<close>.\<close>
lemma flatinj_prefix_concat:
  assumes seg_tot: "\<And>r. r \<in> set zs \<Longrightarrow> flatinj_dsum (flatBP r) = -1"
    and seg_pre: "\<And>r as bs. r \<in> set zs \<Longrightarrow> flatBP r = as @ bs \<Longrightarrow> bs \<noteq> []
                    \<Longrightarrow> 0 \<le> flatinj_dsum as"
    and split: "concat (map (\<lambda>r. CM # flatBP r) zs) = as @ bs"
  shows "0 \<le> flatinj_dsum as"
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
    \<comment> \<open>\<open>a0 = CM\<close>; \<open>as' @ bs = flatBP z @ concat (\<dots> zs)\<close>.  Show \<open>flatinj_dsum as' \<ge> -1\<close>,
       then the leading CM (\<open>+1\<close>) lifts to \<open>\<ge> 0\<close>.\<close>
    have a0: "a0 = CM" and rest: "as' @ bs = flatBP z @ concat (map (\<lambda>r. CM # flatBP r) zs)"
      using Cons whole Cons.prems(3) by auto
    have us: "\<exists>us. (as' = flatBP z @ us \<and> us @ bs = concat (map (\<lambda>r. CM # flatBP r) zs))
       \<or> (as' @ us = flatBP z \<and> bs = us @ concat (map (\<lambda>r. CM # flatBP r) zs))"
      using append_eq_append_conv2[THEN iffD1, OF rest] .
    have "-1 \<le> flatinj_dsum as'"
      using us
    proof (elim exE disjE conjE)
        \<comment> \<open>Case A: \<open>flatBP z\<close> (weight \<open>-1\<close>) fully consumed, \<open>us\<close> a prefix of the rest.\<close>
        fix us
        assume A1: "as' = flatBP z @ us"
          and A2: "us @ bs = concat (map (\<lambda>r. CM # flatBP r) zs)"
        have ztot: "flatinj_dsum (flatBP z) = -1"
          using Cons.prems(1)[of z] by simp
        have "0 \<le> flatinj_dsum us"
          using Cons.hyps[OF _ _ A2[symmetric]] Cons.prems(1) Cons.prems(2) by auto
        thus ?thesis using A1 ztot by simp
      next
        \<comment> \<open>Case B: \<open>as'\<close> a prefix of \<open>flatBP z\<close>.\<close>
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

lemma flatinj_prefix_nonneg_BT:
  "flatBT t = as @ bs \<Longrightarrow> bs \<noteq> [] \<Longrightarrow> 0 \<le> flatinj_dsum as"
  and flatinj_prefix_nonneg_BP:
  "flatBP p = as @ bs \<Longrightarrow> bs \<noteq> [] \<Longrightarrow> 0 \<le> flatinj_dsum as"
proof (induct t and p arbitrary: as bs and as bs rule: flatBT_flatBP.induct)
  case (1 as bs)
  \<comment> \<open>flatBT (Trm []) = [Zsym]: only proper prefix is \<open>[]\<close>.\<close>
  thus ?case by (cases as) auto
next
  case (2 p as bs)
  \<comment> \<open>flatBT (Trm [p]) = flatBP p: directly the BP prefix property for \<open>p\<close>.\<close>
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
    \<comment> \<open>\<open>as'\<close> sits inside \<open>inner @ [RP]\<close>; show \<open>flatinj_dsum as' \<ge> -1\<close>,
       the leading LP (\<open>+1\<close>) lifts to \<open>\<ge> 0\<close>.\<close>
    have key: "-1 \<le> flatinj_dsum as'"
    proof (cases "length as' \<le> length inner")
      case True
      \<comment> \<open>\<open>as'\<close> is a prefix of \<open>inner = flatBP p @ concat (...)\<close>.\<close>
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
        have ptot: "flatinj_dsum (flatBP p) = -1"
          using flatinj_dsum_flatBP[of p] .
        have us_nn: "0 \<le> flatinj_dsum us"
          by (rule flatinj_prefix_concat[where zs="q # ps" and as=us and bs=cs])
             (use A2[symmetric] flatinj_dsum_flatBP 3(2) in auto)
        show ?thesis using A1 ptot us_nn by simp
      next
        fix us
        assume B1: "as' @ us = flatBP p"
          and B2: "cs = us @ concat (map (\<lambda>r. CM # flatBP r) (q # ps))"
        show ?thesis
        proof (cases "us = []")
          case True
          hence "as' = flatBP p" using B1 by simp
          thus ?thesis using flatinj_dsum_flatBP[of p] by simp
        next
          case False
          have "flatBP p = as' @ us" using B1 by simp
          thus ?thesis using 3(1)[of as' us] False by simp
        qed
      qed
    next
      case False
      \<comment> \<open>\<open>length as' > length inner\<close>: then \<open>as' = inner @ [RP]\<close> and \<open>bs = []\<close>,
         contradicting \<open>bs \<noteq> []\<close>.\<close>
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
  \<comment> \<open>flatBP (DB u a) = Dsym u # flatBT a.\<close>
  show ?case
  proof (cases as)
    case Nil thus ?thesis by simp
  next
    case (Cons a0 as')
    have a0: "a0 = Dsym u" and rest: "as' @ bs = flatBT a"
      using Cons 4(2) by auto
    have "0 \<le> flatinj_dsum as'"
      using 4(1)[of as' bs] rest 4(3) by simp
    thus ?thesis using Cons a0 by simp
  qed
qed

\<comment> \<open>Prefix-freeness / cancellation: a leading \<^const>\<open>flatBP\<close> cancels uniquely.
   Concludes equality of the flat strings (not yet of the \<^typ>\<open>BP\<close> terms — that
   needs injectivity, proved afterwards) and of the tails.\<close>
lemma flatinj_flatBP_cancel:
  assumes "flatBP p @ xs = flatBP q @ ys"
  shows "flatBP p = flatBP q \<and> xs = ys"
proof -
  have us: "\<exists>us. (flatBP p = flatBP q @ us \<and> us @ xs = ys)
               \<or> (flatBP p @ us = flatBP q \<and> xs = us @ ys)"
    using append_eq_append_conv2[THEN iffD1, OF assms] .
  have "flatBP p = flatBP q"
    using us
  proof (elim exE disjE conjE)
      fix us
      assume A: "flatBP p = flatBP q @ us"
      show ?thesis
      proof (cases "us = []")
        case True thus ?thesis using A by simp
      next
        case False
        \<comment> \<open>\<open>flatBP q\<close> is a proper prefix of \<open>flatBP p\<close>: weight \<open>\<ge> 0\<close>, but \<open>= -1\<close>.\<close>
        have "0 \<le> flatinj_dsum (flatBP q)"
          using flatinj_prefix_nonneg_BP[OF A False] .
        thus ?thesis using flatinj_dsum_flatBP[of q] by simp
      qed
    next
      fix us
      assume B: "flatBP p @ us = flatBP q"
      show ?thesis
      proof (cases "us = []")
        case True thus ?thesis using B by simp
      next
        case False
        have "flatBP q = flatBP p @ us" using B by simp
        have "0 \<le> flatinj_dsum (flatBP p)"
          using flatinj_prefix_nonneg_BP[OF \<open>flatBP q = flatBP p @ us\<close> False] .
        thus ?thesis using flatinj_dsum_flatBP[of p] by simp
      qed
    qed
  thus ?thesis using assms by simp
qed

text \<open>
  Injectivity of the comma-separated principal list inside a tuple: if two
  \<open>concat (map (\<lambda>r. CM # flatBP r) \<dots>)\<close> strings agree then the underlying
  \<^typ>\<open>BP\<close> lists agree.  The cancellation lemma peels off matching prefixes
  \<open>flatBP x = flatBP y\<close>; turning that into \<open>x = y\<close> needs \<^const>\<open>flatBP\<close>
  injectivity, which is supplied as the segment-wise hypothesis \<open>inj_seg\<close>
  (discharged from the per-component induction hypothesis at the call site, so
  the development stays non-circular).
\<close>

lemma flatinj_concat_inj:
  assumes inj_seg: "\<And>a b. a \<in> set xs \<Longrightarrow> flatBP a = flatBP b \<Longrightarrow> a = b"
    and eq: "concat (map (\<lambda>r. CM # flatBP r) xs) = concat (map (\<lambda>r. CM # flatBP r) ys)"
  shows "xs = ys"
  using assms
proof (induct xs arbitrary: ys)
  case Nil thus ?case by (cases ys) auto
next
  case (Cons x xs)
  show ?case
  proof (cases ys)
    case Nil thus ?thesis using Cons.prems(2) by simp
  next
    case (Cons y ys')
    have "CM # flatBP x @ concat (map (\<lambda>r. CM # flatBP r) xs)
          = CM # flatBP y @ concat (map (\<lambda>r. CM # flatBP r) ys')"
      using Cons.prems(2) Cons by simp
    hence eqc: "flatBP x @ concat (map (\<lambda>r. CM # flatBP r) xs)
          = flatBP y @ concat (map (\<lambda>r. CM # flatBP r) ys')"
      by simp
    have fxy: "flatBP x = flatBP y"
      and tl: "concat (map (\<lambda>r. CM # flatBP r) xs)
               = concat (map (\<lambda>r. CM # flatBP r) ys')"
      using flatinj_flatBP_cancel[OF eqc] by simp_all
    have xy: "x = y" using Cons.prems(1)[of x y] fxy by simp
    have "xs = ys'"
      by (rule Cons.hyps) (use Cons.prems(1) tl in auto)
    thus ?thesis using xy Cons by simp
  qed
qed

\<comment> \<open>Case split on a list into the three \<^typ>\<open>BT\<close>-relevant shapes:
   empty, singleton, or two-or-more.\<close>
lemma list_321_cases:
  obtains (Nil) "xs = []"
        | (single) x where "xs = [x]"
        | (multi) x y zs where "xs = x # y # zs"
  by (metis list.exhaust)

text \<open>
  Main: \<^const>\<open>flatBT\<close> and \<^const>\<open>flatBP\<close> injectivity, proved together by the
  mutual function-induction rule \<open>flatBT_flatBP.induct\<close>.  The first symbol of a
  flat string distinguishes the three [Buc1] term shapes (\<open>Zsym\<close>: \<open>0\<close>;
  \<open>Dsym\<close>: single principal; \<open>LP\<close>: tuple), and within each shape the cancellation
  lemma + \<open>flatinj_concat_inj\<close> recover the components.
\<close>

lemma flatinj_flat_inj:
  "flatBT t = flatBT c \<Longrightarrow> t = c"
  and "flatBP p = flatBP d \<Longrightarrow> p = d"
proof (induct t and p arbitrary: c and d rule: flatBT_flatBP.induct)
  case 1
  \<comment> \<open>t = Trm []: flat = [Zsym]; c must also be Trm [].\<close>
  have "flatBT c = [Zsym]" using "1.prems" by simp
  thus ?case using rnsub_flat_hd[of c "[]"] by auto
next
  case (2 p)
  \<comment> \<open>t = Trm [p]: flat = flatBP p, head Dsym; c is a single principal.\<close>
  note IH2 = "2.hyps"
  note prem2 = "2.prems"
  obtain u a where p: "p = DB u a" by (cases p)
  have head: "flatBT c = Dsym u # flatBT a"
    using prem2 p by simp
  obtain cs where c: "c = Trm cs" by (cases c)
  show ?case
  proof (cases cs rule: list_321_cases)
    case Nil
    \<comment> \<open>c = Trm []: flat = [Zsym], contradicts the Dsym head.\<close>
    have "flatBT c = [Zsym]" using c Nil by simp
    thus ?thesis using head by simp
  next
    case (single p')
    \<comment> \<open>c = Trm [p']: flat = flatBP p', cancel against flatBP p.\<close>
    have "flatBP p = flatBP p'" using prem2 c single by simp
    hence "p = p'" using IH2[of p'] by simp
    thus ?thesis using c single by simp
  next
    case (multi p' q' ps')
    \<comment> \<open>c = Trm (p'#q'#ps'): flat starts with LP, contradicts the Dsym head.\<close>
    have "flatBT c = LP # (flatBP p' @ concat (map (\<lambda>r. CM # flatBP r) (q' # ps'))) @ [RP]"
      using c multi by simp
    thus ?thesis using head by simp
  qed
next
  case (3 p q ps)
  \<comment> \<open>t = Trm (p#q#ps): flat = LP # inner @ [RP], head LP.\<close>
  note prem3 = "3.prems"
  \<comment> \<open>component injectivity IHs: \<open>IH3head\<close> for the leading principal \<open>p\<close>,
     \<open>IH3seg\<close> for each principal in \<open>q#ps\<close>.\<close>
  note IH3head = "3.hyps"(1)
  note IH3seg = "3.hyps"(2)
  have ft: "flatBT (Trm (p # q # ps))
            = LP # (flatBP p @ concat (map (\<lambda>r. CM # flatBP r) (q # ps))) @ [RP]"
    by simp
  obtain cs where c: "c = Trm cs" by (cases c)
  show ?case
  proof (cases cs rule: list_321_cases)
    case Nil
    \<comment> \<open>c = Trm []: flat = [Zsym], contradicts the LP head.\<close>
    have "flatBT c = [Zsym]" using c Nil by simp
    thus ?thesis using prem3 ft by simp
  next
    case (single p')
    \<comment> \<open>c = Trm [p']: flat starts with Dsym, contradicts the LP head.\<close>
    obtain u' a' where p': "p' = DB u' a'" by (cases p')
    have "flatBT c = Dsym u' # flatBT a'" using c single p' by simp
    thus ?thesis using prem3 ft by simp
  next
    case (multi p' q' ps')
    have fc: "flatBT c
              = LP # (flatBP p' @ concat (map (\<lambda>r. CM # flatBP r) (q' # ps'))) @ [RP]"
      using c multi by simp
    have inner_eq: "flatBP p @ concat (map (\<lambda>r. CM # flatBP r) (q # ps))
                  = flatBP p' @ concat (map (\<lambda>r. CM # flatBP r) (q' # ps'))"
      using prem3 ft fc by simp
    have fpp: "flatBP p = flatBP p'"
      and cc: "concat (map (\<lambda>r. CM # flatBP r) (q # ps))
               = concat (map (\<lambda>r. CM # flatBP r) (q' # ps'))"
      using flatinj_flatBP_cancel[OF inner_eq] by simp_all
    \<comment> \<open>\<open>p = p'\<close> from the head IH; the list \<open>q#ps = q'#ps'\<close> from \<open>flatinj_concat_inj\<close>,
       its segment-injectivity hypothesis discharged by the component IH \<open>IH3seg\<close>.\<close>
    have pp: "p = p'" using IH3head fpp by simp
    have "q # ps = q' # ps'"
      by (rule flatinj_concat_inj[OF _ cc]) (use IH3seg in blast)
    thus ?thesis using pp c multi by simp
  qed
next
  case (4 u a)
  \<comment> \<open>p = DB u a: flat = Dsym u # flatBT a; d must be DB u a'.\<close>
  obtain v b where d: "d = DB v b" by (cases d)
  have "Dsym u # flatBT a = Dsym v # flatBT b"
    using "4.prems" d by simp
  hence uv: "u = v" and ab: "flatBT a = flatBT b" by simp_all
  have "a = b" using "4.hyps"[of b] ab by simp
  thus ?case using uv d by simp
qed

end
