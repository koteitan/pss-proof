theory Frontier_6_029
  imports Support_6_011
begin

lemma descending_shift_append:
  assumes dQ: "descending Q" and Qne: "Q \<noteq> []"
    and lenPRE: "length PRE = Lng Q - 1"
    and pre0: "\<And>J. J < length PRE \<Longrightarrow> entry (PRE ! J) 0 0 = entry (Q ! J) 0 0 + c"
    and pre1: "\<And>J. J < length PRE \<Longrightarrow> entry (PRE ! J) 1 0 = entry (Q ! J) 1 0"
    and tl0: "entry TL 0 0 = entry (Q ! (Lng Q - 1)) 0 0 + c"
    and tl1: "entry TL 1 0 \<le> entry (Q ! (Lng Q - 1)) 1 0"
  shows "descending (PRE @ [TL])"
proof (rule descending_append)
  \<comment> \<open>\<open>PRE\<close> descending: each \<open>cdom (PRE!J0)(PRE!J1)\<close> is the \<open>+c\<close>-shift of
     \<open>cdom (Q!J0)(Q!J1)\<close>, which holds since \<open>J0\<le>J1\<le>J\<^sub>1-1<Lng Q-1\<close>.\<close>
  show "descending PRE"
  proof (rule descendingI_cdom)
    fix J0 J1 assume le: "J0 \<le> J1" and j1: "J1 < Lng PRE"
    have j1p: "J1 < length PRE" using j1 by simp
    have j0p: "J0 < length PRE" using le j1p by linarith
    have j1Q: "J1 < Lng Q" using j1p lenPRE by simp
    have cdomQ: "cdom (Q ! J0) (Q ! J1)" using descending_cdomD[OF dQ le j1Q] .
    show "cdom (PRE ! J0) (PRE ! J1)"
      unfolding cdom_def
    proof (intro conjI impI)
      have e0J0: "entry (PRE ! J0) 0 0 = entry (Q ! J0) 0 0 + c" using pre0[OF j0p] .
      have e0J1: "entry (PRE ! J1) 0 0 = entry (Q ! J1) 0 0 + c" using pre0[OF j1p] .
      have e1J0: "entry (PRE ! J0) 1 0 = entry (Q ! J0) 1 0" using pre1[OF j0p] .
      have e1J1: "entry (PRE ! J1) 1 0 = entry (Q ! J1) 1 0" using pre1[OF j1p] .
      from cdomQ have r0: "entry (Q ! J1) 0 0 \<le> entry (Q ! J0) 0 0"
        and r1: "entry (Q ! J0) 0 0 = entry (Q ! J1) 0 0
                  \<longrightarrow> entry (Q ! J1) 1 0 \<le> entry (Q ! J0) 1 0"
        by (auto simp: cdom_def)
      show "entry (PRE ! J1) 0 0 \<le> entry (PRE ! J0) 0 0"
        using r0 e0J0 e0J1 by simp
      assume "entry (PRE ! J0) 0 0 = entry (PRE ! J1) 0 0"
      hence "entry (Q ! J0) 0 0 = entry (Q ! J1) 0 0" using e0J0 e0J1 by simp
      thus "entry (PRE ! J1) 1 0 \<le> entry (PRE ! J0) 1 0"
        using r1 e1J0 e1J1 by simp
    qed
  qed
next
  show "descending [TL]" by (simp add: descending_def)
next
  \<comment> \<open>junction \<open>cdom (last PRE) TL\<close>: \<open>last PRE = PRE!(J\<^sub>1-1)\<close>, and
     \<open>cdom (Q!(J\<^sub>1-1)) (Q!J\<^sub>1)\<close> with \<open>J\<^sub>1 = Lng Q - 1\<close> shifts to it.\<close>
  assume PREne: "PRE \<noteq> []" and "[TL] \<noteq> []"
  let ?J1 = "Lng Q - 1"
  have lenpos: "0 < length PRE" using PREne by simp
  have J1pos: "0 < ?J1" using lenpos lenPRE by simp
  have idxlt: "?J1 - 1 < length PRE" using lenPRE J1pos by linarith
  have lastPRE: "last PRE = PRE ! (?J1 - 1)"
    using PREne lenPRE by (simp add: last_conv_nth)
  have cdomQ: "cdom (Q ! (?J1 - 1)) (Q ! ?J1)"
    by (rule descending_cdomD[OF dQ diff_le_self]) (use Qne in simp)
  from cdomQ have r0: "entry (Q ! ?J1) 0 0 \<le> entry (Q ! (?J1 - 1)) 0 0"
    and r1: "entry (Q ! (?J1 - 1)) 0 0 = entry (Q ! ?J1) 0 0
              \<longrightarrow> entry (Q ! ?J1) 1 0 \<le> entry (Q ! (?J1 - 1)) 1 0"
    by (auto simp: cdom_def)
  have pe0: "entry (last PRE) 0 0 = entry (Q ! (?J1 - 1)) 0 0 + c"
    using pre0[OF idxlt] lastPRE by simp
  have pe1: "entry (last PRE) 1 0 = entry (Q ! (?J1 - 1)) 1 0"
    using pre1[OF idxlt] lastPRE by simp
  show "cdom (last PRE) ([TL] ! 0)"
    unfolding cdom_def
  proof (intro conjI impI)
    show "entry ([TL] ! 0) 0 0 \<le> entry (last PRE) 0 0"
      using tl0 r0 pe0 by simp
    assume "entry (last PRE) 0 0 = entry ([TL] ! 0) 0 0"
    hence "entry (Q ! (?J1 - 1)) 0 0 = entry (Q ! ?J1) 0 0" using pe0 tl0 by simp
    hence "entry (Q ! ?J1) 1 0 \<le> entry (Q ! (?J1 - 1)) 1 0" using r1 by simp
    thus "entry ([TL] ! 0) 1 0 \<le> entry (last PRE) 1 0"
      using tl1 pe1 by simp
  qed
qed

text \<open>Block periodicity of the \<open>i\<^sub>1 = 0\<close> oper (article 1462).  With \<open>i\<^sub>1 = 0\<close> the
  row shifts \<open>d\<^sub>0, d\<^sub>1\<close> both vanish, so each of the \<open>n\<close> blocks is the verbatim
  copy \<open>(M\<^sub>j)\<^bsub>j=j\<^sub>0\<^esub>\<^bsup>j\<^sub>1-1\<^esup> = seg M j\<^sub>0 (j\<^sub>1-1)\<close>; hence \<open>M[n]\<close> is \<open>take j\<^sub>0 M\<close>
  followed by \<open>n\<close> identical such blocks.\<close>

lemma nth_concat_replicate:
  "s < length B \<Longrightarrow> q < n \<Longrightarrow> concat (replicate n B) ! (q * length B + s) = B ! s"
proof (induction n arbitrary: q)
  case 0 thus ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases q)
    case 0
    have "concat (replicate (Suc n) B) = B @ concat (replicate n B)" by simp
    thus ?thesis using Suc.prems 0 by (simp add: nth_append)
  next
    case (Suc q')
    have eq: "concat (replicate (Suc n) B) = B @ concat (replicate n B)" by simp
    have idx: "q * length B + s = length B + (q' * length B + s)"
      using Suc by (simp add: algebra_simps)
    have qn: "q' < n" using Suc.prems Suc by simp
    show ?thesis using eq idx Suc.IH[OF Suc.prems(1) qn] by (simp add: nth_append)
  qed
qed

lemma oper_d0zero_expand:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 0"
  shows "M[n] = take (parent M 0 (Lng M - 1)) M
              @ concat (replicate n (map ((!) M) [parent M 0 (Lng M - 1)..<Lng M - 1]))"
proof -
  let ?j1 = "Lng M - 1"  let ?i1 = "idx1 M ?j1"  let ?j0 = "parent M ?i1 ?j1"
  let ?d0 = "if 0 < ?i1 then entry M 0 ?j1 - entry M 0 ?j0 else 0"
  let ?d1 = "if 1 < ?i1 then entry M 1 ?j1 - entry M 1 ?j0 else 0"
  \<comment> \<open>unfold the oper Let by pure rewriting (no \<open>1\<close>-normalisation)\<close>
  have raw: "M[n] = take ?j0 M @
       concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * ?d0, entry M 1 j + k * ?d1))
                            [?j0..<?j1]) [0..<n])"
    by (rule poper_oper_expand[OF L notzero hp, of n, unfolded Let_def])
  \<comment> \<open>\<open>i\<^sub>1 = 0\<close> collapses parent index and both shifts (via \<open>subst\<close>, no normalisation)\<close>
  have d0z: "?d0 = 0" by (subst i1z) simp
  have d1z: "?d1 = 0" by (subst i1z) simp
  have pj0: "?j0 = parent M 0 ?j1" by (subst i1z) (rule refl)
  have "M[n] = take ?j0 M @ concat (map (\<lambda>k. map ((!) M) [?j0..<?j1]) [0..<n])"
    using raw by (simp add: d0z d1z entry_def del: One_nat_def)
  also have "\<dots> = take ?j0 M @ concat (replicate n (map ((!) M) [?j0..<?j1]))"
    by (simp add: map_replicate_const)
  finally have key: "M[n] = take ?j0 M @ concat (replicate n (map ((!) M) [?j0..<?j1]))" .
  show ?thesis using key[unfolded pj0] .
qed

text \<open>§6.8 d0pos analog of @{thm [source] oper_d0zero_expand}: when the row-1
  index of the last node is \<open>i\<^sub>1 = 1\<close>, the fundamental sequence repeats the slice
  \<open>seg M j\<^sub>0 (Lng M-1)\<close> with each block's row-0 entries shifted by \<open>k\<cdot>\<delta>\<close>, where
  \<open>\<delta> = entry M 0 (Lng M-1) - entry M 0 j\<^sub>0\<close> and \<open>j\<^sub>0 = parent M 1 (Lng M-1)\<close>.
  Row 1 is unchanged (\<open>d\<^sub>1 = 0\<close> because \<open>1 < i\<^sub>1\<close> fails).\<close>

lemma oper_d1pos_expand:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
  shows "M[n] = take (parent M 1 (Lng M - 1)) M
              @ concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j
                          + k * (entry M 0 (Lng M - 1) - entry M 0 (parent M 1 (Lng M - 1))),
                          entry M 1 j))
                        [parent M 1 (Lng M - 1)..<Lng M - 1]) [0..<n])"
proof -
  let ?j1 = "Lng M - 1"  let ?i1 = "idx1 M ?j1"  let ?j0 = "parent M ?i1 ?j1"
  let ?d0 = "if 0 < ?i1 then entry M 0 ?j1 - entry M 0 ?j0 else 0"
  let ?d1 = "if 1 < ?i1 then entry M 1 ?j1 - entry M 1 ?j0 else 0"
  \<comment> \<open>unfold the oper Let by pure rewriting (no \<open>1\<close>-normalisation)\<close>
  have raw: "M[n] = take ?j0 M @
       concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * ?d0, entry M 1 j + k * ?d1))
                            [?j0..<?j1]) [0..<n])"
    by (rule poper_oper_expand[OF L notzero hp, of n, unfolded Let_def])
  \<comment> \<open>\<open>i\<^sub>1 = 1\<close>: \<open>0 < i\<^sub>1\<close> holds (row-0 shift live), \<open>1 < i\<^sub>1\<close> fails (\<open>d\<^sub>1 = 0\<close>)\<close>
  let ?delta = "entry M 0 ?j1 - entry M 0 ?j0"
  have d0v: "?d0 = ?delta" by (subst i1z) simp
  have d1z: "?d1 = 0" by (subst i1z) simp
  have pj0: "?j0 = parent M 1 ?j1" by (subst i1z) (rule refl)
  have key: "M[n] = take ?j0 M @
       concat (map (\<lambda>k. map (\<lambda>j. (entry M 0 j + k * ?delta, entry M 1 j))
                            [?j0..<?j1]) [0..<n])"
    using raw by (simp add: d0v d1z del: One_nat_def)
  show ?thesis using key unfolding pj0 .
qed

text \<open>Length of the §6.8 d0pos fundamental-sequence term: \<open>j\<^sub>0 + n\<cdot>w\<close> with
  \<open>w = Lng M - 1 - j\<^sub>0\<close>, equivalently (the form requested by the article)
  \<open>parent M 1 (Lng M-1) + n\<cdot>(Lng M - parent M 1 (Lng M-1))\<close> once \<open>w\<close> is unfolded;
  here stated in the exact \<open>Lng M - 1\<close> form that the \<open>oper\<close> definition produces.\<close>

lemma oper_d1pos_LngM:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
  shows "Lng (M[n]) = parent M 1 (Lng M - 1)
                    + n * (Lng M - 1 - parent M 1 (Lng M - 1))"
proof -
  let ?j0 = "parent M 1 (Lng M - 1)"  let ?w = "Lng M - 1 - ?j0"
  let ?B = "\<lambda>k. map (\<lambda>j. (entry M 0 j
              + k * (entry M 0 (Lng M - 1) - entry M 0 ?j0), entry M 1 j))
            [?j0..<Lng M - 1]"
  have expand: "M[n] = take ?j0 M @ concat (map ?B [0..<n])"
    using oper_d1pos_expand[OF L notzero hp i1z] by simp
  have t: "length (take ?j0 M) = ?j0" using j0lt L by simp
  have lmap: "map Lng (map ?B [0..<n]) = replicate n ?w"
  proof -
    have "map Lng (map ?B [0..<n]) = map (\<lambda>k. ?w) [0..<n]" by simp
    thus ?thesis by (simp add: map_replicate_const)
  qed
  have lc: "length (concat (map ?B [0..<n])) = n * ?w"
    by (subst length_concat, subst lmap) (simp add: sum_list_replicate)
  show ?thesis using expand t lc by simp
qed

text \<open>§6.8 d0pos block index helper: for distinct but equal-length blocks
  \<open>B 0, \<dots>, B (n-1)\<close> (each of length \<open>w\<close>), the \<open>(q\<cdot>w+s)\<close>-th element of their
  concatenation is the \<open>s\<close>-th element of block \<open>B q\<close>.  Analog of
  @{thm [source] nth_concat_replicate} for non-identical blocks.\<close>

lemma nth_concat_map_const_len:
  assumes lenB: "\<And>k. k < n \<Longrightarrow> length (B k) = w"
    and s: "s < w" and q: "q < n"
  shows "concat (map B [0..<n]) ! (q * w + s) = (B q) ! s"
  using assms
proof (induction n arbitrary: q B)
  case 0 thus ?case by simp
next
  case (Suc n)
  have split: "concat (map B [0..<Suc n]) = B 0 @ concat (map (\<lambda>k. B (Suc k)) [0..<n])"
  proof -
    have c: "[0..<Suc n] = 0 # [Suc 0..<Suc n]"
      by (rule upt_conv_Cons) simp
    have m: "[Suc 0..<Suc n] = map Suc [0..<n]"
      by (rule map_Suc_upt[symmetric])
    have "map B [0..<Suc n] = B 0 # map (\<lambda>k. B (Suc k)) [0..<n]"
      by (subst c, subst m) simp
    thus ?thesis by simp
  qed
  show ?case
  proof (cases q)
    case 0
    have "concat (map B [0..<Suc n]) ! (q * w + s) = (B 0 @ concat (map (\<lambda>k. B (Suc k)) [0..<n])) ! s"
      using split 0 by simp
    also have "\<dots> = (B 0) ! s"
      using Suc.prems(1)[of 0] s by (simp add: nth_append)
    finally show ?thesis using 0 by simp
  next
    case (Suc q')
    have qn: "q' < n" using Suc.prems(3) Suc by simp
    have lenB0: "length (B 0) = w" using Suc.prems(1)[of 0] by simp
    have lenSuc: "\<And>k. k < n \<Longrightarrow> length (B (Suc k)) = w"
      using Suc.prems(1) by simp
    have ih: "concat (map (\<lambda>k. B (Suc k)) [0..<n]) ! (q' * w + s) = B (Suc q') ! s"
      using Suc.IH[where B="\<lambda>k. B (Suc k)" and q=q', OF lenSuc s qn] by simp
    have idx: "q * w + s = w + (q' * w + s)"
      using Suc by (simp add: algebra_simps)
    have qwsge: "w \<le> q * w + s" using idx by simp
    have "concat (map B [0..<Suc n]) ! (q * w + s)
            = concat (map (\<lambda>k. B (Suc k)) [0..<n]) ! (q' * w + s)"
      using split idx lenB0 qwsge by (simp add: nth_append)
    also have "\<dots> = B (Suc q') ! s" using ih .
    finally show ?thesis using Suc by simp
  qed
qed

text \<open>Periodicity in index form (d0pos / \<open>i\<^sub>1=1\<close>): inside block \<open>q < n\<close> at offset
  \<open>s\<close>, \<open>M[n]\<close> reads off the slice node \<open>j\<^sub>0+s\<close> of \<open>M\<close> with its row-0 entry shifted
  by \<open>q\<cdot>\<delta>\<close> (\<open>\<delta> = entry M 0 (Lng M-1) - entry M 0 j\<^sub>0\<close>); row 1 is unshifted.\<close>

lemma oper_d1pos_nth:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and q: "q < n"
    and s: "s < Lng M - 1 - parent M 1 (Lng M - 1)"
  shows "(M[n]) ! (parent M 1 (Lng M - 1)
                   + q * (Lng M - 1 - parent M 1 (Lng M - 1)) + s)
       = (entry M 0 (parent M 1 (Lng M - 1) + s)
            + q * (entry M 0 (Lng M - 1) - entry M 0 (parent M 1 (Lng M - 1))),
          entry M 1 (parent M 1 (Lng M - 1) + s))"
proof -
  let ?j1 = "Lng M - 1"  let ?j0 = "parent M 1 ?j1"  let ?w = "?j1 - ?j0"
  let ?delta = "entry M 0 ?j1 - entry M 0 ?j0"
  let ?B = "\<lambda>k. map (\<lambda>j. (entry M 0 j + k * ?delta, entry M 1 j)) [?j0..<?j1]"
  have lenB: "\<And>k. length (?B k) = ?w" by simp
  have j0le: "?j0 \<le> Lng M" using j0lt by linarith
  have lentake: "length (take ?j0 M) = ?j0" using j0le by simp
  have idxge: "?j0 \<le> ?j0 + q * ?w + s" by simp
  have expand: "M[n] = take ?j0 M @ concat (map ?B [0..<n])"
    using oper_d1pos_expand[OF L notzero hp i1z] by simp
  have "(M[n]) ! (?j0 + q * ?w + s) = concat (map ?B [0..<n]) ! (q * ?w + s)"
    using expand lentake idxge by (simp add: nth_append)
  also have "\<dots> = (?B q) ! s"
    by (rule nth_concat_map_const_len[OF _ s q]) (simp add: lenB)
  also have "\<dots> = (entry M 0 (?j0 + s) + q * ?delta, entry M 1 (?j0 + s))"
    using s by (simp add: nth_upt)
  finally show ?thesis .
qed

text \<open>Row-0 value of the \<open>i\<^sub>1=1\<close> oper inside block \<open>q\<close> at offset \<open>s\<close>: the slice
  value \<open>entry M 0 (j\<^sub>0+s)\<close> plus the per-block shift \<open>q\<cdot>\<delta>\<close>.\<close>

lemma oper_d1pos_entry0:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and q: "q < n"
    and s: "s < Lng M - 1 - parent M 1 (Lng M - 1)"
  shows "entry (M[n]) 0 (parent M 1 (Lng M - 1)
                   + q * (Lng M - 1 - parent M 1 (Lng M - 1)) + s)
       = entry M 0 (parent M 1 (Lng M - 1) + s)
            + q * (entry M 0 (Lng M - 1) - entry M 0 (parent M 1 (Lng M - 1)))"
proof -
  have "(M[n]) ! (parent M 1 (Lng M - 1)
                   + q * (Lng M - 1 - parent M 1 (Lng M - 1)) + s)
       = (entry M 0 (parent M 1 (Lng M - 1) + s)
            + q * (entry M 0 (Lng M - 1) - entry M 0 (parent M 1 (Lng M - 1))),
          entry M 1 (parent M 1 (Lng M - 1) + s))"
    by (rule oper_d1pos_nth[OF L notzero hp i1z j0lt q s])
  thus ?thesis by (simp add: entry_def)
qed

text \<open>Row-1 value of the \<open>i\<^sub>1=1\<close> oper inside block \<open>q\<close> at offset \<open>s\<close>: equals the
  slice value \<open>entry M 1 (j\<^sub>0+s)\<close> with NO per-block shift (the key d0pos-vs-d0zero
  difference: \<open>d\<^sub>1 = 0\<close> because \<open>1 < i\<^sub>1\<close> fails when \<open>i\<^sub>1 = 1\<close>).\<close>

lemma oper_d1pos_entry1:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and q: "q < n"
    and s: "s < Lng M - 1 - parent M 1 (Lng M - 1)"
  shows "entry (M[n]) 1 (parent M 1 (Lng M - 1)
                   + q * (Lng M - 1 - parent M 1 (Lng M - 1)) + s)
       = entry M 1 (parent M 1 (Lng M - 1) + s)"
proof -
  have "(M[n]) ! (parent M 1 (Lng M - 1)
                   + q * (Lng M - 1 - parent M 1 (Lng M - 1)) + s)
       = (entry M 0 (parent M 1 (Lng M - 1) + s)
            + q * (entry M 0 (Lng M - 1) - entry M 0 (parent M 1 (Lng M - 1))),
          entry M 1 (parent M 1 (Lng M - 1) + s))"
    by (rule oper_d1pos_nth[OF L notzero hp i1z j0lt q s])
  thus ?thesis by (simp add: entry_def)
qed

text \<open>§6.8 d0pos analog of \<open>oper_d0zero_nth_prefix\<close>: prefix indices
  (\<open>x < j\<^sub>0\<close>) of the \<open>i\<^sub>1=1\<close> oper read straight off \<open>M\<close> (the prefix \<open>take j\<^sub>0 M\<close>
  is verbatim, independent of \<open>n\<close>).\<close>

lemma oper_d1pos_nth_prefix:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and x: "x < parent M 1 (Lng M - 1)"
  shows "((M::pairseq)[n]) ! x = M ! x"
proof -
  let ?j0 = "parent M 1 (Lng M - 1)"
  let ?B = "\<lambda>k. map (\<lambda>j. (entry M 0 j
              + k * (entry M 0 (Lng M - 1) - entry M 0 ?j0), entry M 1 j))
            [?j0..<Lng M - 1]"
  have hp1: "hasParent M 1 (Lng M - 1)" using hp i1z by simp
  have parR: "nextR M 1 ?j0 (Lng M - 1)"
    using hp1 unfolding hasParent_def parent_def by (rule theI')
  have j0lt: "?j0 < Lng M - 1" using poper_nextR_imp_le0[OF parR] by simp
  have j0le: "?j0 \<le> Lng M" using j0lt by linarith
  have e: "(M::pairseq)[n] = take ?j0 M @ concat (map ?B [0..<n])"
    using oper_d1pos_expand[OF L notzero hp i1z] by simp
  have "x < length (take ?j0 M)" using x j0le by simp
  thus ?thesis using e by (simp add: nth_append nth_take x)
qed

end
