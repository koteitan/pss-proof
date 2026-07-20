theory Support_6_057
  imports Frontier_6_077
begin

text \<open>§6.7 oper-tiling ROW-1 parent CHARACTERIZATION (Front A, \<open>i\<^sub>1 = 0\<close> case) — the
  LAST brick, \<open>i\<^sub>1 = 0\<close> half.  For the tiling branch with \<open>i\<^sub>1 = 0\<close> and a within-
  block column \<open>j\<^sub>0 \<le> x < Lng (N[n])\<close> that has a row-1 parent \<open>p = parent (N[n]) 1 x\<close>,
  its period base \<open>x' = j\<^sub>0 + (x-j\<^sub>0) mod w\<close> has a row-1 parent in \<open>N\<close> whose row-1
  \<open>N\<close>-entry matches that of \<open>base p\<close>.  Assembled by REFLECTING \<open>nextrel1 (N[n]) p x\<close>
  to \<open>nextrel1 N (base p) x'\<close>: the row-1 entries transfer verbatim
  (@{thm [source] oper_d0zero_entryi_base}), \<open>le0\<close> transfers BOTH ways
  (@{thm [source] oper_d0zero_le0_base_fwd} / @{thm [source] oper_d0zero_le0_lift}),
  and the row-1 argmin over \<open>le0\<close>-predecessors carries across by lifting any
  \<open>N\<close>-competitor into block \<open>q\<close>.  \<open>THE\<close>-uniqueness then yields
  \<open>hasParent N 1 x'\<close> and \<open>parent N 1 x' = base p\<close>; the \<open>+1\<close> step follows from
  @{thm [source] operCA_tiling_within1_via_pbase}.  Empirically 0-fail
  (/tmp/charac_i0_check.py: 1758/1758; le0 base-correspondence 17604/17604).\<close>

lemma operCA_tiling_row1_charac_i0:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 0"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and condA: "RedCondA N"
    and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> x"
    and hpn: "hasParent ((N::pairseq)[n]) 1 x"
  shows "entry ((N::pairseq)[n]) 1 (parent ((N::pairseq)[n]) 1 x) + 1
       = entry ((N::pairseq)[n]) 1 x"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?Nn = "(N::pairseq)[n]"
  let ?p = "parent ?Nn 1 x"
  let ?sx = "(x - ?j0) mod ?w"  let ?qx = "(x - ?j0) div ?w"
  let ?xp = "?j0 + ?sx"
  let ?base = "\<lambda>z. if z < ?j0 then z else ?j0 + (z - ?j0) mod ?w"
  have w0: "0 < ?w" using j0lt by linarith
  have j0le1: "?j0 \<le> ?j1" using j0lt by linarith
  have j0w1: "?j0 + ?w = ?j1" using j0le1 by simp
  have lenNn: "Lng ?Nn = ?j0 + n * ?w"
    by (rule operB_gen_LngM[OF L notzero hp j0lt])
  \<comment> \<open>decode \<open>x\<close> as block \<open>q\<^sub>x\<close>, offset \<open>s\<^sub>x\<close>\<close>
  have xge: "?j0 \<le> x" using ge by simp
  have nrel: "nextrel1 ?Nn ?p x"
  proof -
    have "\<exists>!j0. nextR ?Nn 1 j0 x" using hpn unfolding hasParent_def by simp
    hence "nextR ?Nn 1 ?p x" unfolding parent_def by (rule theI')
    thus ?thesis by (simp add: nextR_def)
  qed
  from nrel have px: "?p < x" and pNn: "?p < Lng ?Nn" and xNn: "x < Lng ?Nn"
    and e1px: "entry ?Nn 1 ?p < entry ?Nn 1 x"
    and le0px: "le0 ?Nn ?p x"
    and argmin: "\<And>j. ?p < j \<Longrightarrow> le0 ?Nn j x \<Longrightarrow> entry ?Nn 1 x \<le> entry ?Nn 1 j"
    by (auto simp: nextrel1_def)
  have sxw: "?sx < ?w" using w0 by simp
  have xmj: "x - ?j0 < n * ?w" using xNn lenNn xge by linarith
  have qxn: "?qx < n" using less_mult_imp_div_less[OF xmj] .
  have xsplit: "x = ?j0 + ?qx * ?w + ?sx"
  proof -
    have "?qx * ?w + ?sx = x - ?j0"
      using div_mult_mod_eq[of "x - ?j0" ?w] by (simp add: mult.commute)
    thus ?thesis using xge by linarith
  qed
  have xpj1: "?xp < ?j1"
  proof -
    have "?xp < ?j0 + ?w" using sxw by simp
    thus ?thesis using j0w1 by simp
  qed
  have xpN: "?xp < Lng N" using xpj1 L by linarith
  \<comment> \<open>row-1 entry readings (verbatim periodicity, \<open>d\<^sub>1 = 0\<close>)\<close>
  have e1x: "entry ?Nn 1 x = entry N 1 ?xp"
    using oper_d0zero_entryi_base[OF L notzero hp i1z j0lt xNn, of 1] xge by simp
  have e1p: "entry ?Nn 1 ?p = entry N 1 (?base ?p)"
    using oper_d0zero_entryi_base[OF L notzero hp i1z j0lt pNn, of 1] by simp
  \<comment> \<open>(3) \<open>le0 N (base p) x'\<close> via FORWARD base-correspondence\<close>
  have le0N: "le0 N (?base ?p) ?xp"
  proof -
    have "le0 ?Nn ?p (?j0 + ?qx * ?w + ?sx)" using le0px xsplit by simp
    thus ?thesis
      using oper_d0zero_le0_base_fwd[OF L notzero hp i1z j0lt qxn sxw, of ?p] by simp
  qed
  \<comment> \<open>(2) row-1 strict increase; (1) \<open>base p < x'\<close> (\<open>\<le>\<close> from mono, \<open>\<noteq>\<close> from entries)\<close>
  have e1lt: "entry N 1 (?base ?p) < entry N 1 ?xp" using e1px e1p e1x by simp
  have bple: "?base ?p \<le> ?xp"
  proof -
    have "(nextrel0 N)\<^sup>*\<^sup>* (?base ?p) ?xp" using le0N by (simp add: le0_def)
    thus ?thesis by (rule nextrel0_rtrancl_mono)
  qed
  have bpxneq: "?base ?p \<noteq> ?xp" using e1lt by force
  have bpx: "?base ?p < ?xp" using bple bpxneq by linarith
  \<comment> \<open>(4) the row-1 argmin in \<open>N\<close>: lift any competitor into block \<open>q\<^sub>x\<close>\<close>
  have argminN: "\<And>j. ?base ?p < j \<Longrightarrow> le0 N j ?xp \<Longrightarrow> entry N 1 ?xp \<le> entry N 1 j"
  proof -
    fix j assume jgt: "?base ?p < j" and jle0: "le0 N j ?xp"
    \<comment> \<open>\<open>j \<le> x' < j\<^sub>1\<close>; lift \<open>j\<close> to \<open>lift j\<close> in block \<open>q\<^sub>x\<close>\<close>
    have jxp: "j \<le> ?xp" using jle0 nextrel0_rtrancl_mono[of N j ?xp] by (simp add: le0_def)
    have jj1: "j < ?j1" using jxp xpj1 by (rule le_less_trans)
    let ?lj = "if j < ?j0 then j else ?j0 + ?qx * ?w + (j - ?j0)"
    have liftj: "le0 ?Nn ?lj (?j0 + ?qx * ?w + ?sx)"
      using oper_d0zero_le0_lift[OF L notzero hp i1z j0lt qxn sxw, of j] jle0 by simp
    have liftjx: "le0 ?Nn ?lj x" using liftj xsplit by simp
    \<comment> \<open>\<open>p < lift j\<close>: from \<open>base p < j\<close> and the block/prefix position of \<open>lift j\<close>\<close>
    have p_lt_lj: "?p < ?lj"
    proof (cases "?p < ?j0")
      case True \<comment> \<open>\<open>p\<close> in prefix; \<open>lift j \<ge> j > base p = p\<close> if \<open>j\<close> prefix, else \<open>\<ge> j\<^sub>0 > p\<close>\<close>
      have bpeq: "?base ?p = ?p" using True by simp
      show ?thesis
      proof (cases "j < ?j0")
        case True thus ?thesis using jgt bpeq by simp
      next
        case False thus ?thesis using True by simp
      qed
    next
      case False \<comment> \<open>\<open>p\<close> in a block (\<open>p \<ge> j\<^sub>0\<close>); by confinement it is block \<open>q\<^sub>x\<close> (\<open>p \<le> x\<close>)\<close>
      hence pge: "?j0 \<le> ?p" by simp
      \<comment> \<open>\<open>j \<ge> j\<^sub>0\<close>: else \<open>base p \<ge> j\<^sub>0 > j\<close> contradicts \<open>base p < j\<close>\<close>
      have jge: "?j0 \<le> j"
      proof (rule ccontr)
        assume "\<not> ?j0 \<le> j"
        hence "j < ?j0" by simp
        moreover have "?j0 \<le> ?base ?p" using False by simp
        ultimately show False using jgt by linarith
      qed
      \<comment> \<open>\<open>p\<close> is in block \<open>q\<^sub>x\<close>: \<open>p \<le> x = j\<^sub>0+q\<^sub>x\<cdot>w+s\<^sub>x < j\<^sub>0+(q\<^sub>x+1)\<cdot>w\<close>, and \<open>p \<ge> j\<^sub>0+q\<^sub>x\<cdot>w\<close>
         by the block-start barrier of @{thm [source] oper_d0zero_le0_confined}\<close>
      let ?sp = "(?p - ?j0) mod ?w"  let ?qp = "(?p - ?j0) div ?w"
      have spw: "?sp < ?w" using w0 by simp
      have psplit: "?p = ?j0 + ?qp * ?w + ?sp"
      proof -
        have "?qp * ?w + ?sp = ?p - ?j0"
          using div_mult_mod_eq[of "?p - ?j0" ?w] by (simp add: mult.commute)
        thus ?thesis using pge by linarith
      qed
      have basep_eq: "?base ?p = ?j0 + ?sp" using False by simp
      have qpqx: "?qp = ?qx"
      proof -
        have ple: "?p \<le> x" using px by simp
        have pxblk: "?p < ?j0 + (?qx + 1) * ?w"
        proof -
          have "x < ?j0 + (?qx + 1) * ?w" using xsplit sxw by simp
          thus ?thesis using ple by linarith
        qed
        \<comment> \<open>so \<open>qp \<le> qx\<close>; and \<open>qp \<ge> qx\<close> would need a lower block-start barrier — both give \<open>=\<close>\<close>
        have qple: "?qp \<le> ?qx"
        proof (rule ccontr)
          assume "\<not> ?qp \<le> ?qx"
          hence "?qx + 1 \<le> ?qp" by simp
          hence "(?qx + 1) * ?w \<le> ?qp * ?w" using mult_le_mono1 by blast
          hence "?j0 + (?qx + 1) * ?w \<le> ?p" using psplit by linarith
          thus False using pxblk by linarith
        qed
        have qpge: "?qx \<le> ?qp"
        proof (rule ccontr)
          assume "\<not> ?qx \<le> ?qp"
          hence qplt: "?qp < ?qx" by simp
          \<comment> \<open>the block-start \<open>j\<^sub>0+q\<^sub>x\<cdot>w\<close> lies in \<open>(p, x]\<close>, carries the row-0 minimum,
             but \<open>le0 (N[n]) p x\<close> can't cross a block-start lower than \<open>x\<close>'s\<close>
          have pstart: "?p < ?j0 + ?qx * ?w"
          proof -
            have "(?qp + 1) * ?w \<le> ?qx * ?w" using qplt mult_le_mono1[of "?qp+1" ?qx ?w] by simp
            hence "?j0 + ?qp * ?w + ?w \<le> ?j0 + ?qx * ?w" by (simp add: algebra_simps)
            thus ?thesis using psplit spw by linarith
          qed
          have j0eq: "parent N 0 ?j1 = ?j0" using i1z by simp
          have p0ge: "parent N 0 ?j1 \<le> ?p" using pge j0eq by simp
          have chPx: "(nextrel0 ?Nn)\<^sup>*\<^sup>* ?p x" using le0px by (simp add: le0_def)
          have conf: "x < parent N 0 ?j1
                        + ((?p - parent N 0 ?j1) div (?j1 - parent N 0 ?j1) + 1)
                           * (?j1 - parent N 0 ?j1)"
            by (rule oper_d0zero_le0_confined[OF L notzero hp i1z p0ge pNn chPx])
          \<comment> \<open>rewrite \<open>conf\<close> into the abstract \<open>j\<^sub>0, w, q\<^sub>p\<close> form by \<open>simp only\<close> on the two
             defining equalities (NOT full \<open>simp\<close>, which loops on the nested nat-
             subtraction — CLAUDE.md gotcha)\<close>
          have weq: "?j1 - parent N 0 ?j1 = ?w" using j0eq by simp
          have qpeq: "(?p - parent N 0 ?j1) div (?j1 - parent N 0 ?j1) = ?qp"
            using j0eq weq by simp
          have conf2: "x < ?j0 + (?qp + 1) * ?w"
            using conf by (simp only: j0eq weq qpeq)
          have step_le: "?j0 + (?qp + 1) * ?w \<le> ?j0 + ?qx * ?w"
          proof -
            have "(?qp + 1) * ?w \<le> ?qx * ?w" using qplt mult_le_mono1[of "?qp+1" ?qx ?w] by simp
            thus ?thesis by simp
          qed
          have "x < ?j0 + ?qx * ?w" using conf2 step_le by linarith
          thus False using xsplit by linarith
        qed
        show ?thesis using qple qpge by simp
      qed
      have psplit': "?p = ?j0 + ?qx * ?w + ?sp" using psplit qpqx by simp
      \<comment> \<open>\<open>base p < j\<close> gives \<open>s\<^sub>p < j - j\<^sub>0\<close>, hence \<open>p < lift j\<close>\<close>
      have spj: "?sp < j - ?j0" using jgt basep_eq jge by linarith
      have ljeq: "?lj = ?j0 + ?qx * ?w + (j - ?j0)" using jge by simp
      show ?thesis using psplit' ljeq spj by linarith
    qed
    have e1lj: "entry ?Nn 1 ?lj = entry N 1 j"
    proof (cases "j < ?j0")
      case True thus ?thesis
        using operB_gen_entry_prefix[OF L notzero hp True, of n 1] by simp
    next
      case False
      hence jge: "?j0 \<le> j" by simp
      have ojw: "j - ?j0 < ?w"
      proof -
        have "j < ?j0 + ?w" using jj1 j0w1 by simp
        thus ?thesis using jge by linarith
      qed
      have "entry ?Nn 1 (?j0 + ?qx * ?w + (j - ?j0)) = entry N 1 (?j0 + (j - ?j0))"
        using oper_gen_block_entry1[OF L notzero hp j0lt qxn ojw] by simp
      thus ?thesis using False jge by simp
    qed
    have "entry ?Nn 1 x \<le> entry ?Nn 1 ?lj" using argmin[OF p_lt_lj liftjx] .
    thus "entry N 1 ?xp \<le> entry N 1 j" using e1x e1lj by simp
  qed
  \<comment> \<open>assemble \<open>nextrel1 N (base p) x'\<close>\<close>
  have bpN: "?base ?p < Lng N" using bpx xpN by linarith
  have nrelN: "nextrel1 N (?base ?p) ?xp"
    unfolding nextrel1_def
    by (intro conjI bpN xpN bpx e1lt le0N) (use argminN in blast)
  \<comment> \<open>uniqueness: \<open>base p\<close> is THE row-1 parent of \<open>x'\<close>\<close>
  have nextRN: "nextR N 1 (?base ?p) ?xp" using nrelN by (simp add: nextR_def)
  have hpNx: "hasParent N 1 ?xp"
  proof -
    have "\<exists>!a. nextR N 1 a ?xp"
    proof (rule ex1I)
      show "nextR N 1 (?base ?p) ?xp" by (rule nextRN)
    next
      fix a assume "nextR N 1 a ?xp"
      thus "a = ?base ?p" using nextRN by (rule nextR1_unique)
    qed
    thus ?thesis unfolding hasParent_def by simp
  qed
  have parNx: "parent N 1 ?xp = ?base ?p"
  proof -
    have "(THE a. nextR N 1 a ?xp) = ?base ?p"
    proof (rule the_equality)
      show "nextR N 1 (?base ?p) ?xp" by (rule nextRN)
    next
      fix a assume "nextR N 1 a ?xp"
      thus "a = ?base ?p" using nextRN by (rule nextR1_unique)
    qed
    thus ?thesis unfolding parent_def .
  qed
  \<comment> \<open>feed the glue: \<open>hpN\<close> and \<open>pbase\<close> (entry equality) for
     @{thm [source] operCA_tiling_within1_via_pbase}\<close>
  have hpN: "hasParent N 1 (?j0 + (x - ?j0) mod ?w)" using hpNx by simp
  have plt: "?p < Lng ?Nn" by (rule pNn)
  have pbase: "entry N 1 (if ?p < ?j0 then ?p else ?j0 + (?p - ?j0) mod ?w)
               = entry N 1 (parent N 1 ?xp)"
    using parNx by simp
  show ?thesis
    by (rule operCA_tiling_within1_via_pbase[OF L notzero hp j0lt condA ge xNn plt hpN pbase])
qed

end
