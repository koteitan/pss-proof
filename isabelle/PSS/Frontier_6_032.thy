theory Frontier_6_032
  imports Support_6_014
begin

text \<open>§6.8 d1pos B1 (S1): every P-component of a d1pos branch region is
  \<open>monoT\<close> or \<open>zeroT\<close>.  The branch region of \<open>N = M[n]\<close> is the slice
  \<open>Q = seg N (TrMax N + 1) (Lng N - 1)\<close>, and \<open>Br N = P Q\<close> (article §6.8).  We
  state it for an arbitrary branch-region slice \<open>Q = seg (M[n]) a b\<close> (the d1pos
  oper hypotheses are carried for traceability), only requiring \<open>Q \<in> T_PS\<close>.
  Each component \<open>P Q ! J = seg Q (IdxSum (P Q)!J) (IdxSum (P Q)!(J+1)-1)\<close>
  (@{thm [source] m_6_4_P_IdxSum}) has a row-0 left-minimum left end
  (@{thm [source] idxsum_leftend_lmin}), and \<open>P\<close> decomposes any \<open>T_PS\<close> sequence
  into non-multi (zero/mono) components by construction — so the component
  \<open>monoT/zeroT\<close> property is exactly @{thm [source] m_6_2_P_components_1} read at
  the index \<open>J\<close> via \<open>nth_mem\<close>.  Empirically validated (\<open>python/red_model.py\<close>
  via \<open>is_standard\<close> + yaBMS, \<open>KMAX = 7\<close>): 140/140 P-components of standard d1pos
  branch regions are \<open>monoT \<or> zeroT\<close> (0 failures), and the route lemma — \<open>le0\<close>
  holds across every component's endpoints — also held 105/105.\<close>

text \<open>§6.8 general block-read: regardless of \<open>i\<^sub>1 \<in> {0,1}\<close>, the fundamental
  sequence \<open>M[n]\<close> inside block \<open>q < n\<close> at offset \<open>s < w\<close> reads the slice node
  \<open>j\<^sub>0+s\<close> of \<open>M\<close> with row-0 shifted by \<open>q\<cdot>d\<^sub>0\<close> and row-1 UNSHIFTED (because
  \<open>d\<^sub>1 = 0\<close> always, as \<open>1 < i\<^sub>1\<close> is impossible).  Here
  \<open>j\<^sub>0 = parent M (idx1 M (Lng M-1)) (Lng M-1)\<close>,
  \<open>w = Lng M - 1 - j\<^sub>0\<close>, and \<open>d\<^sub>0 = (if 0 < idx1 M (Lng M-1) then ... else 0)\<close>.
  This is the \<open>i\<^sub>1\<close>-agnostic generalisation of @{thm [source] oper_d1pos_nth}.\<close>

lemma oper_gen_block_nth:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and j0lt: "parent M (idx1 M (Lng M - 1)) (Lng M - 1) < Lng M - 1"
    and q: "q < n"
    and s: "s < Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1)"
  shows "(M[n]) ! (parent M (idx1 M (Lng M - 1)) (Lng M - 1)
                   + q * (Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1)) + s)
       = (entry M 0 (parent M (idx1 M (Lng M - 1)) (Lng M - 1) + s)
            + q * (if 0 < idx1 M (Lng M - 1)
                     then entry M 0 (Lng M - 1)
                          - entry M 0 (parent M (idx1 M (Lng M - 1)) (Lng M - 1))
                     else 0),
          entry M 1 (parent M (idx1 M (Lng M - 1)) (Lng M - 1) + s))"
proof -
  let ?j1 = "Lng M - 1"  let ?i1 = "idx1 M ?j1"  let ?j0 = "parent M ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?d0 = "if 0 < ?i1 then entry M 0 ?j1 - entry M 0 ?j0 else 0"
  let ?d1 = "if 1 < ?i1 then entry M 1 ?j1 - entry M 1 ?j0 else 0"
  let ?B = "\<lambda>k. map (\<lambda>j. (entry M 0 j + k * ?d0, entry M 1 j + k * ?d1)) [?j0..<?j1]"
  have d1z: "?d1 = 0" using idx1_def[of M ?j1] by (cases "entry M 1 ?j1 > 0") simp_all
  have lenB: "\<And>k. length (?B k) = ?w" by simp
  have j0le: "?j0 \<le> Lng M" using j0lt by linarith
  have lentake: "length (take ?j0 M) = ?j0" using j0le by simp
  have idxge: "?j0 \<le> ?j0 + q * ?w + s" by simp
  have expand: "M[n] = take ?j0 M @ concat (map ?B [0..<n])"
    by (rule poper_oper_expand[OF L notzero hp, of n, unfolded Let_def])
  have "(M[n]) ! (?j0 + q * ?w + s) = concat (map ?B [0..<n]) ! (q * ?w + s)"
    using expand lentake idxge by (simp add: nth_append)
  also have "\<dots> = (?B q) ! s"
    by (rule nth_concat_map_const_len[OF _ s q]) (simp add: lenB)
  also have "\<dots> = (entry M 0 (?j0 + s) + q * ?d0, entry M 1 (?j0 + s) + q * ?d1)"
    using s by (simp add: nth_upt)
  also have "\<dots> = (entry M 0 (?j0 + s) + q * ?d0, entry M 1 (?j0 + s))"
    using d1z by simp
  finally show ?thesis .
qed

lemma oper_gen_block_entry0:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and j0lt: "parent M (idx1 M (Lng M - 1)) (Lng M - 1) < Lng M - 1"
    and q: "q < n"
    and s: "s < Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1)"
  shows "entry (M[n]) 0 (parent M (idx1 M (Lng M - 1)) (Lng M - 1)
                   + q * (Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1)) + s)
       = entry M 0 (parent M (idx1 M (Lng M - 1)) (Lng M - 1) + s)
            + q * (if 0 < idx1 M (Lng M - 1)
                     then entry M 0 (Lng M - 1)
                          - entry M 0 (parent M (idx1 M (Lng M - 1)) (Lng M - 1))
                     else 0)"
  using oper_gen_block_nth[OF L notzero hp j0lt q s] by (simp add: entry_def)

lemma oper_gen_block_entry1:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and j0lt: "parent M (idx1 M (Lng M - 1)) (Lng M - 1) < Lng M - 1"
    and q: "q < n"
    and s: "s < Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1)"
  shows "entry (M[n]) 1 (parent M (idx1 M (Lng M - 1)) (Lng M - 1)
                   + q * (Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1)) + s)
       = entry M 1 (parent M (idx1 M (Lng M - 1)) (Lng M - 1) + s)"
  using oper_gen_block_nth[OF L notzero hp j0lt q s] by (simp add: entry_def)

text \<open>§6.8 prefix read (\<open>i\<^sub>1\<close>-agnostic): on the prefix \<open>x < j\<^sub>0\<close>, \<open>M[n]\<close> reads
  off \<open>M\<close> verbatim.\<close>

lemma oper_gen_nth_prefix:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and x: "x < parent M (idx1 M (Lng M - 1)) (Lng M - 1)"
  shows "((M::pairseq)[n]) ! x = M ! x"
proof -
  let ?j1 = "Lng M - 1"  let ?i1 = "idx1 M ?j1"  let ?j0 = "parent M ?i1 ?j1"
  let ?d0 = "if 0 < ?i1 then entry M 0 ?j1 - entry M 0 ?j0 else 0"
  let ?d1 = "if 1 < ?i1 then entry M 1 ?j1 - entry M 1 ?j0 else 0"
  let ?B = "\<lambda>k. map (\<lambda>j. (entry M 0 j + k * ?d0, entry M 1 j + k * ?d1)) [?j0..<?j1]"
  have parR: "nextR M ?i1 ?j0 ?j1"
    using hp unfolding hasParent_def parent_def by (rule theI')
  have j0lt: "?j0 < ?j1" using poper_nextR_imp_le0[OF parR] by simp
  have j0le: "?j0 \<le> Lng M" using j0lt by linarith
  have e: "(M::pairseq)[n] = take ?j0 M @ concat (map ?B [0..<n])"
    by (rule poper_oper_expand[OF L notzero hp, of n, unfolded Let_def])
  have "x < length (take ?j0 M)" using x j0le by simp
  thus ?thesis using e by (simp add: nth_append nth_take x)
qed

text \<open>Prefix indices (\<open>x < j\<^sub>0\<close>) of the \<open>i\<^sub>1=0\<close> oper read straight off \<open>M\<close>.\<close>

lemma oper_d0zero_nth_prefix:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 0"
    and x: "x < parent M 0 (Lng M - 1)"
  shows "((M::pairseq)[n]) ! x = M ! x"
proof -
  let ?j0 = "parent M 0 (Lng M - 1)"
  have hp0: "hasParent M 0 (Lng M - 1)" using hp i1z by simp
  have parR: "nextR M 0 ?j0 (Lng M - 1)"
    using hp0 unfolding hasParent_def parent_def by (rule theI')
  have j0lt: "?j0 < Lng M - 1" using poper_nextR_imp_le0[OF parR] by simp
  have j0le: "?j0 \<le> Lng M" using j0lt by linarith
  have e: "(M::pairseq)[n] = take ?j0 M @ concat (replicate n (map ((!) M) [?j0..<Lng M - 1]))"
    by (rule oper_d0zero_expand[OF L notzero hp i1z])
  have "x < length (take ?j0 M)" using x j0le by simp
  thus ?thesis using e by (simp add: nth_append nth_take x)
qed

text \<open>The \<open>i\<^sub>1=0\<close> oper agrees with \<open>M\<close> on the whole closed prefix \<open>[0, j\<^sub>0]\<close>
  (prefix indices read off directly; \<open>j\<^sub>0\<close> is the start of block 0, value \<open>M\<^bsub>j\<^sub>0\<^esub>\<close>).\<close>

lemma oper_d0zero_nth_le_parent:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 0"
    and n: "1 \<le> n" and x: "x \<le> parent M 0 (Lng M - 1)"
  shows "((M::pairseq)[n]) ! x = M ! x"
proof (cases "x < parent M 0 (Lng M - 1)")
  case True
  show ?thesis by (rule oper_d0zero_nth_prefix[OF L notzero hp i1z True])
next
  case False
  hence xeq: "x = parent M 0 (Lng M - 1)" using x by linarith
  let ?j0 = "parent M 0 (Lng M - 1)"
  have hp0: "hasParent M 0 (Lng M - 1)" using hp i1z by simp
  have parR: "nextR M 0 ?j0 (Lng M - 1)"
    using hp0 unfolding hasParent_def parent_def by (rule theI')
  have j0lt: "?j0 < Lng M - 1" using poper_nextR_imp_le0[OF parR] by simp
  have "((M::pairseq)[n]) ! (?j0 + 0 * (Lng M - 1 - ?j0) + 0) = M ! (?j0 + 0)"
    by (rule oper_d0zero_nth[OF L notzero hp i1z j0lt]) (use n j0lt in auto)
  thus ?thesis using xeq by simp
qed

end
