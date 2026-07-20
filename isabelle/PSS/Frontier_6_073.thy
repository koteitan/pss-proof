theory Frontier_6_073
  imports Support_6_052
begin

text \<open>§6.7 oper-tiling brick (Front B): general length of the tiling \<open>oper\<close>
  (\<open>i\<^sub>1\<close>-agnostic), \<open>Lng (M[n]) = j\<^sub>0 + n\<cdot>w\<close> with \<open>w = Lng M - 1 - j\<^sub>0\<close>.  Mirror of
  the \<open>i\<^sub>1=1\<close>-only @{thm [source] oper_d1pos_LngM}, derived from
  @{thm [source] poper_oper_expand}.\<close>

lemma operB_gen_LngM:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and j0lt: "parent M (idx1 M (Lng M - 1)) (Lng M - 1) < Lng M - 1"
  shows "Lng ((M::pairseq)[n]) = parent M (idx1 M (Lng M - 1)) (Lng M - 1)
                    + n * (Lng M - 1 - parent M (idx1 M (Lng M - 1)) (Lng M - 1))"
proof -
  let ?j1 = "Lng M - 1"  let ?i1 = "idx1 M ?j1"  let ?j0 = "parent M ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?d0 = "if 0 < ?i1 then entry M 0 ?j1 - entry M 0 ?j0 else 0"
  let ?d1 = "if 1 < ?i1 then entry M 1 ?j1 - entry M 1 ?j0 else 0"
  let ?B = "\<lambda>k. map (\<lambda>j. (entry M 0 j + k * ?d0, entry M 1 j + k * ?d1)) [?j0..<?j1]"
  have expand: "(M::pairseq)[n] = take ?j0 M @ concat (map ?B [0..<n])"
    by (rule poper_oper_expand[OF L notzero hp, of n, unfolded Let_def])
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

text \<open>§6.7 oper-tiling brick (Front B): entry prefix read in entry form
  (\<open>i\<^sub>1\<close>-agnostic), from @{thm [source] oper_gen_nth_prefix}.\<close>

lemma operB_gen_entry_prefix:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and x: "x < parent M (idx1 M (Lng M - 1)) (Lng M - 1)"
  shows "entry ((M::pairseq)[n]) i x = entry M i x"
  using oper_gen_nth_prefix[OF L notzero hp x, of n] by (simp add: entry_def)

text \<open>§6.7 oper-tiling brick (Front B): the genuine TILING branch of \<open>RedCondB\<close>.
  Discharges the \<open>operCB\<close> residual of @{thm [source] m_6_7_standard_RedCondAB}
  (and hence @{thm [source] m_6_7_standard_reduced} / @{thm [source] m_6_5_ST_PS_imp_RedCondA}).

  Structure of \<open>N[n]\<close> (\<open>j\<^sub>1 = Lng N-1\<close>, \<open>i\<^sub>1 = idx1 N j\<^sub>1\<close>, \<open>j\<^sub>0 = parent N i\<^sub>1 j\<^sub>1\<close>,
  \<open>w = j\<^sub>1 - j\<^sub>0\<close>, \<open>d\<^sub>0 = (if 0<i\<^sub>1 then e\<^sub>0 j\<^sub>1 - e\<^sub>0 j\<^sub>0 else 0)\<close>): a verbatim prefix
  \<open>[0,j\<^sub>0)\<close> of \<open>N\<close>, then \<open>n\<close> copies of the active slice \<open>[j\<^sub>0,j\<^sub>1)\<close>, copy \<open>q\<close>
  row-0-shifted by \<open>q\<cdot>d\<^sub>0\<close>, row 1 unshifted.

  Take a row-0-parentless column \<open>x\<close> of \<open>N[n]\<close> (running-min of row 0, by
  @{thm [source] idxsum_no_parent0_iff}).  Two regions:
  \<^item> \<open>x < j\<^sub>0\<close> (prefix): \<open>x\<close> is the same running-min in \<open>N\<close> (prefix verbatim), so
    row-0-parentless in \<open>N\<close>; \<open>RedCondB N\<close> + verbatim entries give the equality.
  \<^item> \<open>x \<ge> j\<^sub>0\<close>: \<open>x = j\<^sub>0 + q\<cdot>w + s\<close>; the block-0 witness \<open>u = j\<^sub>0+s \<le> x\<close> reads
    \<open>e\<^sub>0 u\<close> in \<open>N[n]\<close> (shift \<open>0\<cdot>d\<^sub>0\<close>), so the running-min at \<open>x\<close> forces
    \<open>e\<^sub>0 u \<ge> e\<^sub>0 u + q\<cdot>d\<^sub>0\<close>, i.e. \<open>q\<cdot>d\<^sub>0 = 0\<close>; then \<open>e\<^sub>0(N[n],x) = e\<^sub>0(N,u)\<close>,
    \<open>e\<^sub>1(N[n],x) = e\<^sub>1(N,u)\<close> (row 1 always unshifted), and \<open>u\<close> is itself a
    row-0 running-min in \<open>N\<close> (every \<open>y<u\<close> lies in the verbatim region), so
    \<open>RedCondB N\<close> gives \<open>e\<^sub>0(N,u)=e\<^sub>1(N,u)\<close>.  Empirically 0-fail (red_model.py).\<close>

lemma operCB_tiling_T:
  assumes NT: "N \<in> T_PS" and condB: "RedCondB N"
    and n1: "1 \<le> n"
    and tile: "\<not> (Lng N - 1 = 0
                  \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                  \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1))"
  shows "RedCondB ((N::pairseq)[n])"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "Lng N - 1 - ?j0"
  let ?d0 = "if 0 < ?i1 then entry N 0 ?j1 - entry N 0 ?j0 else 0"
  let ?Nn = "(N::pairseq)[n]"
  have L: "1 < Lng N" using tile by (cases "Lng N - 1 = 0") auto
  have notzero: "\<not> (entry N 0 ?j1 = 0 \<and> entry N 1 ?j1 = 0)" using tile by blast
  have hp: "hasParent N ?i1 ?j1" using tile by blast
  have parR: "nextR N ?i1 ?j0 ?j1"
    using hp unfolding hasParent_def parent_def by (rule theI')
  have j0lt: "?j0 < ?j1" using poper_nextR_imp_le0[OF parR] by simp
  have w0: "0 < ?w" using j0lt by linarith
  have LngNn: "Lng ?Nn = ?j0 + n * ?w"
    by (rule operB_gen_LngM[OF L notzero hp j0lt])
  have NnT: "?Nn \<in> T_PS"
  proof -
    have "0 < n * ?w" using w0 n1 by simp
    hence "0 < Lng ?Nn" using LngNn by simp
    hence "?Nn \<noteq> []" using length_greater_0_conv by blast
    thus ?thesis by (simp add: T_PS_def)
  qed
  \<comment> \<open>prefix-region entries of \<open>N[n]\<close> are verbatim, on both rows\<close>
  have pref0: "\<And>y i. y < ?j0 \<Longrightarrow> entry ?Nn i y = entry N i y"
    using operB_gen_entry_prefix[OF L notzero hp] by blast
  \<comment> \<open>block-region entries of \<open>N[n]\<close>: at \<open>j\<^sub>0+q\<cdot>w+s\<close>, row 0 is shifted by \<open>q\<cdot>d\<^sub>0\<close>,
     row 1 is verbatim at \<open>j\<^sub>0+s\<close>\<close>
  have blk0: "\<And>q s. q < n \<Longrightarrow> s < ?w \<Longrightarrow>
       entry ?Nn 0 (?j0 + q * ?w + s) = entry N 0 (?j0 + s) + q * ?d0"
    using oper_gen_block_entry0[OF L notzero hp j0lt] by blast
  have blk1: "\<And>q s. q < n \<Longrightarrow> s < ?w \<Longrightarrow>
       entry ?Nn 1 (?j0 + q * ?w + s) = entry N 1 (?j0 + s)"
    using oper_gen_block_entry1[OF L notzero hp j0lt] by blast
  show ?thesis
    unfolding RedCondB_def
  proof (intro allI impI)
    fix x assume Hx: "\<not> hasParent ?Nn 0 x \<and> x \<le> Lng ?Nn - 1"
    hence noP: "\<not> hasParent ?Nn 0 x" and xle: "x \<le> Lng ?Nn - 1" by simp_all
    have nwpos: "0 < n * ?w" using w0 n1 by simp
    have lpos: "0 < Lng ?Nn" using LngNn nwpos by simp
    have xlt: "x < Lng ?Nn" using xle lpos by linarith
    \<comment> \<open>running-minimum characterization of the row-0-parentless column \<open>x\<close>\<close>
    have rmin: "\<forall>y<x. entry ?Nn 0 y \<ge> entry ?Nn 0 x"
      using idxsum_no_parent0_iff[OF NnT xlt] noP unfolding hasParent_def by blast
    show "entry ?Nn 0 x = entry ?Nn 1 x"
    proof (cases "x < ?j0")
      case True
      \<comment> \<open>prefix: \<open>x\<close> is the same running-min in \<open>N\<close>, hence row-0-parentless in \<open>N\<close>\<close>
      have xltN: "x < Lng N" using True j0lt by linarith
      have eq0: "entry ?Nn 0 x = entry N 0 x" using pref0[OF True] .
      have eq1: "entry ?Nn 1 x = entry N 1 x" using pref0[OF True] .
      have rminN: "\<forall>y<x. entry N 0 y \<ge> entry N 0 x"
      proof (intro allI impI)
        fix y assume yx: "y < x"
        have yj0: "y < ?j0" using yx True by linarith
        have "entry N 0 y = entry ?Nn 0 y" using pref0[OF yj0] by simp
        also have "\<dots> \<ge> entry ?Nn 0 x" using rmin yx by blast
        finally show "entry N 0 y \<ge> entry N 0 x" using eq0 by simp
      qed
      have noPN: "\<not> hasParent N 0 x"
        using idxsum_no_parent0_iff[OF NT xltN] rminN unfolding hasParent_def by blast
      have "entry N 0 x = entry N 1 x"
        using condB noPN xltN unfolding RedCondB_def by simp
      thus ?thesis using eq0 eq1 by simp
    next
      case False
      hence ge: "?j0 \<le> x" by simp
      let ?q = "(x - ?j0) div ?w"  let ?s = "(x - ?j0) mod ?w"
      have sw: "?s < ?w" using w0 by simp
      have xmj: "x - ?j0 < n * ?w" using xlt ge LngNn by linarith
      have qn: "?q < n" using less_mult_imp_div_less[OF xmj] .
      have dm: "?q * ?w + ?s = x - ?j0"
        using div_mult_mod_eq[of "x - ?j0" ?w] by (simp add: mult.commute)
      have xsplit: "x = ?j0 + ?q * ?w + ?s" using dm ge by linarith
      let ?u = "?j0 + ?s"
      \<comment> \<open>block-0 witness \<open>u = j\<^sub>0+s \<le> x\<close>: same row-0 base value, no \<open>q\<cdot>d\<^sub>0\<close> shift\<close>
      have uleX: "?u \<le> x" using xsplit by simp
      have ex0: "entry ?Nn 0 x = entry N 0 ?u + ?q * ?d0"
        using blk0[OF qn sw] xsplit by simp
      have ex1: "entry ?Nn 1 x = entry N 1 ?u"
        using blk1[OF qn sw] xsplit by simp
      have eu0: "entry ?Nn 0 ?u = entry N 0 ?u"
        using blk0[of 0 ?s] qn sw by simp
      \<comment> \<open>running-min at \<open>x\<close> forces the per-block shift \<open>q\<cdot>d\<^sub>0\<close> to vanish\<close>
      have qd0z: "?q * ?d0 = 0"
      proof (cases "?u < x")
        case True
        have "entry N 0 ?u = entry ?Nn 0 ?u" using eu0 by simp
        also have "\<dots> \<ge> entry ?Nn 0 x" using rmin True by blast
        finally have "entry N 0 ?u \<ge> entry N 0 ?u + ?q * ?d0" using ex0 by simp
        thus ?thesis by simp
      next
        case False
        hence ueqx: "?u = x" using uleX by simp
        have "?j0 + ?s = ?j0 + ?q * ?w + ?s" using ueqx xsplit by simp
        hence qw0: "?q * ?w = 0" by simp
        have "?q = 0" using qw0 w0 by (metis mult_is_0 less_numeral_extra(3))
        thus ?thesis by simp
      qed
      have ex0': "entry ?Nn 0 x = entry N 0 ?u" using ex0 qd0z by simp
      \<comment> \<open>\<open>u\<close> is a row-0 running-min in \<open>N\<close>: every \<open>y<u\<close> reads verbatim in \<open>N[n]\<close>
         (prefix, or block-0 with no shift), and \<open>e\<^sub>0(N[n],x) = e\<^sub>0(N,u)\<close>\<close>
      have ult: "?u < Lng N" using sw j0lt by linarith
      have rminU: "\<forall>y<?u. entry N 0 y \<ge> entry N 0 ?u"
      proof (intro allI impI)
        fix y assume yu: "y < ?u"
        have yltX: "y < x" using yu uleX by linarith
        have e_y: "entry ?Nn 0 y = entry N 0 y"
        proof (cases "y < ?j0")
          case True thus ?thesis using pref0[OF True] by simp
        next
          case False
          hence yge: "?j0 \<le> y" by simp
          have ysw: "y - ?j0 < ?w" using yu yge sw by linarith
          have ysplit: "y = ?j0 + 0 * ?w + (y - ?j0)" using yge by simp
          have "entry ?Nn 0 y = entry N 0 (?j0 + (y - ?j0)) + 0 * ?d0"
            using blk0[of 0 "y - ?j0"] n1 ysw ysplit by simp
          thus ?thesis using yge by simp
        qed
        have rm: "entry ?Nn 0 x \<le> entry ?Nn 0 y" using rmin yltX by blast
        have "entry N 0 ?u = entry ?Nn 0 x" using ex0' by simp
        also have "\<dots> \<le> entry ?Nn 0 y" using rm by simp
        also have "\<dots> = entry N 0 y" using e_y by simp
        finally show "entry N 0 y \<ge> entry N 0 ?u" by simp
      qed
      have noPU: "\<not> hasParent N 0 ?u"
        using idxsum_no_parent0_iff[OF NT ult] rminU unfolding hasParent_def by blast
      have uleN: "?u \<le> Lng N - 1" using ult by linarith
      have "entry N 0 ?u = entry N 1 ?u"
        using condB[unfolded RedCondB_def, rule_format, of ?u] noPU uleN by simp
      thus ?thesis using ex0' ex1 by simp
    qed
  qed
qed

text \<open>The original \<open>ST\<^sub>PS\<close>-interface form (kept for the
  @{thm [source] m_6_7_standard_reduced} plumbing); the standardness and
  \<open>RedCondA\<close> hypotheses are not actually needed
  (@{thm [source] operCB_tiling_T}).\<close>

lemma operCB_tiling:
  assumes Nst: "N \<in> ST_PS" and condA: "RedCondA N" and condB: "RedCondB N"
    and n1: "1 \<le> n"
    and tile: "\<not> (Lng N - 1 = 0
                  \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                  \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1))"
  shows "RedCondB ((N::pairseq)[n])"
  by (rule operCB_tiling_T[OF ST_PS_T_PS[OF Nst] condB n1 tile])


text \<open>§6.7 oper-tiling brick (Front A): \<open>i\<^sub>1\<close>-AGNOSTIC within-block \<open>nextrel0\<close>
  transfer.  A base row-0 step \<open>nextrel0 N x y\<close> with \<open>j\<^sub>0 \<le> x\<close> and \<open>y < j\<^sub>1\<close>
  (both endpoints strictly inside one period \<open>[j\<^sub>0,j\<^sub>1)\<close>) lifts verbatim into
  block \<open>q\<close> of \<open>N[n]\<close>, translated by the block start \<open>j\<^sub>0+q\<cdot>w\<close>.  Inside one
  block \<open>N[n]\<close>'s row 0 is \<open>N\<close>'s row 0 shifted by the constant \<open>q\<cdot>d\<^sub>0\<close>
  (@{thm [source] oper_gen_block_entry0}, valid for \<open>i\<^sub>1\<in>{0,1}\<close>), and the
  strict-increase + valley conditions of \<open>nextrel0\<close> are invariant under a uniform
  additive shift.  Mirrors @{thm [source] oper_d1pos_nextrel0_within} but drops the
  \<open>idx1 = 1\<close> assumption (so it also covers the \<open>d\<^sub>0 = 0\<close> case).\<close>

lemma oper_gen_nextrel0_within:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and qn: "q < n"
    and xge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> x"
    and ylt: "y < Lng N - 1"
    and step: "nextrel0 N x y"
  shows "nextrel0 ((N::pairseq)[n])
            (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
               + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
               + (x - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
            (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
               + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
               + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?d0 = "if 0 < ?i1 then entry N 0 ?j1 - entry N 0 ?j0 else 0"
  let ?base = "?j0 + q * ?w"
  let ?tx = "?base + (x - ?j0)"  let ?ty = "?base + (y - ?j0)"
  have w0: "0 < ?w" using j0lt by linarith
  from step have sx: "x < y" and sm: "x < Lng N" "y < Lng N"
    and sv: "entry N 0 x < entry N 0 y"
    and smid: "\<And>j. x < j \<Longrightarrow> j < y \<Longrightarrow> entry N 0 y \<le> entry N 0 j"
    by (auto simp: nextrel0_def)
  have x0: "?j0 \<le> x" using xge .
  have xle: "x \<le> y" using sx by simp
  have yle: "y \<le> ?j1" using ylt by linarith
  have ox: "x - ?j0 < ?w" using x0 sx ylt by linarith
  have oy: "y - ?j0 < ?w" using x0 xle ylt by linarith
  have LngNn: "Lng (N[n]) = ?j0 + n * ?w"
    by (rule operB_gen_LngM[OF L notzero hp j0lt])
  \<comment> \<open>block-\<open>q\<close> row-0 reading at offsets \<open>x-j\<^sub>0\<close>, \<open>y-j\<^sub>0\<close>, and any interior \<open>t\<close>\<close>
  have e_tx: "entry (N[n]) 0 ?tx = entry N 0 x + q * ?d0"
  proof -
    have "entry (N[n]) 0 (?j0 + q * ?w + (x - ?j0)) = entry N 0 (?j0 + (x - ?j0)) + q * ?d0"
      by (rule oper_gen_block_entry0[OF L notzero hp j0lt qn ox])
    thus ?thesis using x0 by simp
  qed
  have e_ty: "entry (N[n]) 0 ?ty = entry N 0 y + q * ?d0"
  proof -
    have "entry (N[n]) 0 (?j0 + q * ?w + (y - ?j0)) = entry N 0 (?j0 + (y - ?j0)) + q * ?d0"
      by (rule oper_gen_block_entry0[OF L notzero hp j0lt qn oy])
    thus ?thesis using x0 xle yle by simp
  qed
  obtain w where wdef: "?w = w" by blast
  have klt: "?j0 + q * w + w \<le> ?j0 + n * w"
  proof -
    have "?j0 + q * w + w = ?j0 + (q + 1) * w" by simp
    also have "\<dots> \<le> ?j0 + n * w" using mult_le_mono1[of "q+1" n w] qn by simp
    finally show ?thesis .
  qed
  have oxw: "x - ?j0 < w" using ox wdef by simp
  have oyw: "y - ?j0 < w" using oy wdef by simp
  have txw: "?tx = ?j0 + q * w + (x - ?j0)" using wdef by simp
  have tyw: "?ty = ?j0 + q * w + (y - ?j0)" using wdef by simp
  have LngNnw: "Lng (N[n]) = ?j0 + n * w" using LngNn wdef by simp
  have txlt: "?tx < Lng (N[n])"
  proof -
    have "?tx < ?j0 + q * w + w" using txw oxw by linarith
    thus ?thesis using klt LngNnw by linarith
  qed
  have tylt: "?ty < Lng (N[n])"
  proof -
    have "?ty < ?j0 + q * w + w" using tyw oyw by linarith
    thus ?thesis using klt LngNnw by linarith
  qed
  have txty: "?tx < ?ty" using sx x0 by linarith
  have ev: "entry (N[n]) 0 ?tx < entry (N[n]) 0 ?ty"
    using e_tx e_ty sv by simp
  have valley: "\<And>z. ?tx < z \<Longrightarrow> z < ?ty \<Longrightarrow> entry (N[n]) 0 ?ty \<le> entry (N[n]) 0 z"
  proof -
    fix z assume zlo: "?tx < z" and zhi: "z < ?ty"
    have zge: "?base \<le> z" using zlo x0 by linarith
    let ?t = "z - ?base"
    have ztw: "?t < ?w" using zhi zge oy by linarith
    have zsplit: "z = ?j0 + q * ?w + ?t" using zge by simp
    have e_z: "entry (N[n]) 0 z = entry N 0 (?j0 + ?t) + q * ?d0"
    proof -
      have "entry (N[n]) 0 (?j0 + q * ?w + ?t) = entry N 0 (?j0 + ?t) + q * ?d0"
        by (rule oper_gen_block_entry0[OF L notzero hp j0lt qn ztw])
      thus ?thesis using zsplit by simp
    qed
    have jlo: "x < ?j0 + ?t" using zlo zge x0 by linarith
    have jhi: "?j0 + ?t < y" using zhi zge x0 xle yle by linarith
    have "entry N 0 y \<le> entry N 0 (?j0 + ?t)" using smid[OF jlo jhi] .
    thus "entry (N[n]) 0 ?ty \<le> entry (N[n]) 0 z"
      using e_z e_ty by simp
  qed
  show ?thesis
    unfolding nextrel0_def
    using txlt tylt txty ev valley by blast
qed


text \<open>§6.7 oper-tiling brick (Front A): row-0 RedCondA on the verbatim PREFIX.
  For a column \<open>jl < j\<^sub>0\<close> of \<open>N[n]\<close> that HAS a row-0 parent, the parent edge is
  read verbatim off the prefix of \<open>N\<close> (@{thm [source] operB_gen_entry_prefix}),
  so \<open>RedCondA N\<close> gives the \<open>+1\<close> step.  The parent \<open>p < jl < j\<^sub>0\<close>, hence both
  endpoints (and the whole valley window) lie in the verbatim prefix; the
  \<open>nextrel0\<close> step therefore agrees between \<open>N[n]\<close> and \<open>N\<close>.\<close>

lemma oper_tiling_row0_prefix:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and condA: "RedCondA N"
    and jl: "jl < parent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and hpn: "hasParent ((N::pairseq)[n]) 0 jl"
  shows "entry ((N::pairseq)[n]) 0 (parent ((N::pairseq)[n]) 0 jl) + 1
       = entry ((N::pairseq)[n]) 0 jl"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?Nn = "(N::pairseq)[n]"
  \<comment> \<open>verbatim prefix entries on row 0 for every \<open>x \<le> jl < j\<^sub>0\<close>\<close>
  have pref: "\<And>x. x < ?j0 \<Longrightarrow> entry ?Nn 0 x = entry N 0 x"
    using operB_gen_entry_prefix[OF L notzero hp] by blast
  \<comment> \<open>obtain the unique \<open>N[n]\<close>-parent \<open>p\<close>\<close>
  have exu: "\<exists>!q. nextrel0 ?Nn q jl"
    using hpn unfolding hasParent_def nextR_def by simp
  obtain p where pP: "nextrel0 ?Nn p jl"
    and pU: "\<And>p'. nextrel0 ?Nn p' jl \<Longrightarrow> p' = p"
    using exu by blast
  have pjl: "p < jl" using pP by (simp add: nextrel0_def)
  have pj0: "p < ?j0" using pjl jl by linarith
  have jlj0: "jl < ?j0" using jl by simp
  \<comment> \<open>both length bounds: \<open>jl < Lng N\<close> and \<open>jl < Lng (N[n])\<close>\<close>
  have jlLN: "jl < Lng N" using jlj0 j0lt by linarith
  have jlLNn: "jl < Lng ?Nn" using pP by (simp add: nextrel0_def)
  \<comment> \<open>the step transfers to \<open>N\<close>: same entries, same valley window (all \<open>< j\<^sub>0\<close>)\<close>
  have stepN: "nextrel0 N p jl"
    unfolding nextrel0_def
  proof (intro conjI allI impI)
    show "p < Lng N" using pj0 j0lt by linarith
    show "jl < Lng N" by (rule jlLN)
    show "p < jl" by (rule pjl)
    have "entry ?Nn 0 p < entry ?Nn 0 jl" using pP by (simp add: nextrel0_def)
    thus "entry N 0 p < entry N 0 jl" using pref[OF pj0] pref[OF jlj0] by simp
  next
    fix j assume jj: "p < j \<and> j < jl"
    hence jp: "p < j" and jjl: "j < jl" by simp_all
    have jj0: "j < ?j0" using jjl jlj0 by linarith
    have "entry ?Nn 0 jl \<le> entry ?Nn 0 j" using pP jp jjl by (simp add: nextrel0_def)
    thus "entry N 0 jl \<le> entry N 0 j" using pref[OF jj0] pref[OF jlj0] by simp
  qed
  \<comment> \<open>uniqueness of the \<open>N\<close>-parent transfers back, so \<open>parent N 0 jl = p\<close>\<close>
  have uniqN: "\<And>p'. nextrel0 N p' jl \<Longrightarrow> p' = p"
  proof -
    fix p' assume Hp': "nextrel0 N p' jl"
    have p'jl: "p' < jl" using Hp' by (simp add: nextrel0_def)
    have p'j0: "p' < ?j0" using p'jl jlj0 by linarith
    have stepNn: "nextrel0 ?Nn p' jl"
      unfolding nextrel0_def
    proof (intro conjI allI impI)
      show "p' < Lng ?Nn" using p'jl jlLNn by linarith
      show "jl < Lng ?Nn" by (rule jlLNn)
      show "p' < jl" by (rule p'jl)
      have "entry N 0 p' < entry N 0 jl" using Hp' by (simp add: nextrel0_def)
      thus "entry ?Nn 0 p' < entry ?Nn 0 jl" using pref[OF p'j0] pref[OF jlj0] by simp
    next
      fix j assume jj: "p' < j \<and> j < jl"
      hence jjl: "j < jl" by simp
      have jj0: "j < ?j0" using jjl jlj0 by linarith
      have "entry N 0 jl \<le> entry N 0 j" using Hp' jj by (simp add: nextrel0_def)
      thus "entry ?Nn 0 jl \<le> entry ?Nn 0 j" using pref[OF jj0] pref[OF jlj0] by simp
    qed
    show "p' = p" using pU[OF stepNn] .
  qed
  \<comment> \<open>recast the steps and uniqueness in \<open>nextR \<cdot> 0\<close> form (matches \<open>parent_def\<close>)\<close>
  have stepNR: "nextR N 0 p jl" using stepN by (simp add: nextR_def)
  have uniqNR: "\<And>p'. nextR N 0 p' jl \<Longrightarrow> p' = p"
    using uniqN by (simp add: nextR_def)
  have pPR: "nextR ?Nn 0 p jl" using pP by (simp add: nextR_def)
  have pUR: "\<And>p'. nextR ?Nn 0 p' jl \<Longrightarrow> p' = p"
    using pU by (simp add: nextR_def)
  have hpN: "hasParent N 0 jl"
    unfolding hasParent_def using stepNR uniqNR by blast
  have parN: "parent N 0 jl = p"
    unfolding parent_def
    by (rule the_equality[where P="\<lambda>q. nextR N 0 q jl", OF stepNR uniqNR])
  have parNn: "parent ?Nn 0 jl = p"
    unfolding parent_def
    by (rule the_equality[where P="\<lambda>q. nextR ?Nn 0 q jl", OF pPR pUR])
  \<comment> \<open>RedCondA N closes the \<open>+1\<close> step\<close>
  have baseN: "entry N 0 (parent N 0 jl) + 1 = entry N 0 jl"
    using condA[unfolded RedCondA_def, rule_format, of 0 jl] hpN by simp
  show ?thesis
    using baseN parN parNn pref[OF pj0] pref[OF jlj0] by simp
qed

end
