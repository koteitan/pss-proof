theory Frontier_6_082
  imports Support_6_061
begin

lemma oper_parent1_readback_interior:
  fixes M :: pairseq
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and qn: "q < n"
    and s0: "0 < s"
    and sw: "s < Lng M - 1 - parent M 1 (Lng M - 1)"
    and hpMs: "hasParent M 1 (parent M 1 (Lng M - 1) + s)"
    and pMge: "parent M 1 (parent M 1 (Lng M - 1) + s) \<ge> parent M 1 (Lng M - 1)"
    \<comment> \<open>the ONE residual: the cross-block VALLEY clause of the readback edge\<close>
    and valley: "\<And>j'. parent M 1 (parent M 1 (Lng M - 1) + s)
                        + q * (Lng M - 1 - parent M 1 (Lng M - 1)) < j'
                  \<Longrightarrow> le0 ((M::pairseq)[n]) j'
                          (parent M 1 (Lng M - 1)
                             + q * (Lng M - 1 - parent M 1 (Lng M - 1)) + s)
                  \<Longrightarrow> entry ((M::pairseq)[n]) 1 j'
                        \<ge> entry ((M::pairseq)[n]) 1
                              (parent M 1 (Lng M - 1)
                                 + q * (Lng M - 1 - parent M 1 (Lng M - 1)) + s)"
  shows "parent ((M::pairseq)[n]) 1
            (parent M 1 (Lng M - 1)
               + q * (Lng M - 1 - parent M 1 (Lng M - 1)) + s)
       = parent M 1 (parent M 1 (Lng M - 1) + s)
           + q * (Lng M - 1 - parent M 1 (Lng M - 1))"
proof -
  let ?j1 = "Lng M - 1"  let ?j0 = "parent M 1 ?j1"  let ?w = "?j1 - ?j0"
  let ?Mn = "(M::pairseq)[n]"
  let ?u = "?j0 + s"           \<comment> \<open>the M-side child (offset \<open>s\<close>)\<close>
  let ?pM = "parent M 1 ?u"    \<comment> \<open>the M-side row-1 parent of \<open>?u\<close>\<close>
  let ?y = "?j0 + q * ?w + s"  \<comment> \<open>the N-side interior column\<close>
  let ?c = "?pM + q * ?w"      \<comment> \<open>the candidate N-side parent\<close>
  let ?sp = "?pM - ?j0"        \<comment> \<open>offset of \<open>?c\<close> in block \<open>q\<close>\<close>
  have w0: "0 < ?w" using j0lt by linarith
  have hpidx: "hasParent M (idx1 M ?j1) ?j1" using hp .
  \<comment> \<open>the \<open>idx1\<close>-form of \<open>j0lt\<close> required by the block bricks, and the \<open>j\<^sub>0\<close> rewrite\<close>
  have pj0eq: "parent M (idx1 M ?j1) ?j1 = ?j0" using i1z by simp
  have j0lt': "parent M (idx1 M ?j1) ?j1 < ?j1" using j0lt pj0eq by simp
  \<comment> \<open>the M-side row-1 parent edge \<open>nextrel1 M p\<^sub>M ?u\<close>\<close>
  have parRMu: "nextR M 1 ?pM ?u"
    using hpMs unfolding hasParent_def parent_def by (rule theI')
  have nr1Mu: "nextrel1 M ?pM ?u" using parRMu by (simp add: nextR_def)
  have eMlt: "entry M 1 ?pM < entry M 1 ?u" using nr1Mu by (simp add: nextrel1_def)
  have le0Mu: "le0 M ?pM ?u" using nr1Mu by (simp add: nextrel1_def)
  have pMlt: "?pM < ?u" using nr1Mu by (simp add: nextrel1_def)
  \<comment> \<open>\<open>?pM\<close> lies in \<open>[j\<^sub>0, ?u)\<close>: offset \<open>?sp < s < w\<close>\<close>
  have pMge': "?j0 \<le> ?pM" using pMge .
  have spv: "?sp = ?pM - ?j0" by simp
  have splt_s: "?sp < s" using pMlt pMge' by linarith
  have spw: "?sp < ?w" using splt_s sw by linarith
  have pM_eq: "?pM = ?j0 + ?sp" using pMge' by simp
  \<comment> \<open>idx1-form offset bounds required by the block bricks (denominator via \<open>pj0eq\<close>)\<close>
  have spw': "?sp < ?j1 - parent M (idx1 M ?j1) ?j1" using spw pj0eq by simp
  have sw': "s < ?j1 - parent M (idx1 M ?j1) ?j1" using sw pj0eq by simp
  \<comment> \<open>index identities reconciling the brick's \<open>idx1\<close>-form with \<open>?c, ?y, ?pM, ?u\<close>\<close>
  have idxC: "parent M (idx1 M ?j1) ?j1
                + q * (?j1 - parent M (idx1 M ?j1) ?j1) + ?sp = ?c"
    using pj0eq pM_eq by (simp add: ac_simps)
  have idxCr: "parent M (idx1 M ?j1) ?j1 + ?sp = ?pM"
    using pj0eq pM_eq by simp
  have idxY: "parent M (idx1 M ?j1) ?j1
                + q * (?j1 - parent M (idx1 M ?j1) ?j1) + s = ?y"
    using pj0eq by (simp add: ac_simps)
  have idxYr: "parent M (idx1 M ?j1) ?j1 + s = ?u"
    using pj0eq by simp
  \<comment> \<open>(1) ENTRIES read back unshifted (\<open>d\<^sub>1 = 0\<close>)\<close>
  have eC: "entry ?Mn 1 ?c = entry M 1 ?pM"
  proof -
    have raw: "entry ?Mn 1 (parent M (idx1 M ?j1) ?j1
                 + q * (?j1 - parent M (idx1 M ?j1) ?j1) + ?sp)
             = entry M 1 (parent M (idx1 M ?j1) ?j1 + ?sp)"
      by (rule oper_gen_block_entry1[OF L notzero hpidx j0lt' qn spw'])
    show ?thesis using raw idxC idxCr by simp
  qed
  have eY: "entry ?Mn 1 ?y = entry M 1 ?u"
  proof -
    have raw: "entry ?Mn 1 (parent M (idx1 M ?j1) ?j1
                 + q * (?j1 - parent M (idx1 M ?j1) ?j1) + s)
             = entry M 1 (parent M (idx1 M ?j1) ?j1 + s)"
      by (rule oper_gen_block_entry1[OF L notzero hpidx j0lt' qn sw'])
    show ?thesis using raw idxY idxYr by simp
  qed
  have elt: "entry ?Mn 1 ?c < entry ?Mn 1 ?y" using eC eY eMlt by simp
  \<comment> \<open>(2) the row-0 \<open>le0\<close> edge \<open>le0 (M[n]) c y\<close> via the within-one-block brick\<close>
  have basepath: "(nextrel0 M)\<^sup>*\<^sup>* (?j0 + ?sp) (?j0 + s)"
    using le0Mu pM_eq by (simp add: le0_def)
  have basepath': "(nextrel0 M)\<^sup>*\<^sup>* (parent M (idx1 M ?j1) ?j1 + ?sp)
                                   (parent M (idx1 M ?j1) ?j1 + s)"
    using basepath pj0eq by simp
  have le0CY: "le0 ?Mn ?c ?y"
  proof -
    have raw: "le0 ?Mn (parent M (idx1 M ?j1) ?j1
                  + q * (?j1 - parent M (idx1 M ?j1) ?j1) + ?sp)
                 (parent M (idx1 M ?j1) ?j1
                  + q * (?j1 - parent M (idx1 M ?j1) ?j1) + s)"
      by (rule oper_d1pos_le0_offset_within
            [OF L notzero hpidx j0lt' qn sw' basepath'])
    from raw show ?thesis by (simp only: idxC idxY)
  qed
  have cltY: "?c < ?y"
  proof -
    have e1: "?c = ?j0 + q * ?w + ?sp" using pM_eq by (simp add: ac_simps)
    have e2: "?y = ?j0 + q * ?w + s" by simp
    show ?thesis using e1 e2 splt_s by simp
  qed
  \<comment> \<open>bounds: \<open>c, y < Lng (M[n])\<close> from \<open>le0CY\<close>\<close>
  have cL: "?c < Lng ?Mn" using le0CY by (simp add: le0_def)
  have yL: "?y < Lng ?Mn" using le0CY by (simp add: le0_def)
  \<comment> \<open>(3) assemble the readback edge \<open>nextrel1 (M[n]) c y\<close> with the valley hypothesis\<close>
  have nrCY: "nextrel1 ?Mn ?c ?y"
    unfolding nextrel1_def
  proof (intro conjI allI impI)
    show "?c < Lng ?Mn" using cL .
    show "?y < Lng ?Mn" using yL .
    show "?c < ?y" using cltY .
    show "entry ?Mn 1 ?c < entry ?Mn 1 ?y" using elt .
    show "le0 ?Mn ?c ?y" using le0CY .
  next
    fix j' assume a: "?c < j' \<and> le0 ?Mn j' ?y"
    have a1: "?c < j'" using a by simp
    have a2: "le0 ?Mn j' ?y" using a by simp
    show "entry ?Mn 1 ?y \<le> entry ?Mn 1 j'"
      using valley[OF a1 a2] by simp
  qed
  \<comment> \<open>\<open>c\<close> IS the (unique) row-1 parent of \<open>y\<close> in \<open>M[n]\<close>\<close>
  have hpY: "hasParent ?Mn 1 ?y"
    unfolding hasParent_def
  proof (rule ex_ex1I)
    show "\<exists>a. nextR ?Mn 1 a ?y" using nrCY by (auto simp: nextR_def)
  next
    fix a b assume "nextR ?Mn 1 a ?y" "nextR ?Mn 1 b ?y"
    thus "a = b" by (rule nextR1_unique)
  qed
  have "(THE a. nextR ?Mn 1 a ?y) = ?c"
  proof (rule the1_equality)
    show "\<exists>!a. nextR ?Mn 1 a ?y" using hpY unfolding hasParent_def .
    show "nextR ?Mn 1 ?c ?y" using nrCY by (simp add: nextR_def)
  qed
  thus ?thesis unfolding parent_def .
qed


text \<open>§6.7 INTERIOR row-1 parent READBACK, UNCONDITIONAL.  Discharges the
  cross-block VALLEY hypothesis of @{thm [source] oper_parent1_readback_interior}.

  KEY STRUCTURAL FACT (empirically 18425/0 on the broad ST\_PS closure, depth 4,
  base \<open>u 0..3 v u..6\<close>, maxlen 12, NOT is\_standard;
  see python/_valley_check5.py): every \<open>le0\<close>-predecessor \<open>j'\<close> of the
  interior column \<open>?y = j\<^sub>0+q\<cdot>w+s\<close> with \<open>?c = ?pM+q\<cdot>w < j'\<close> lies in the SAME
  block \<open>q\<close> (offset \<open>sp'\<close> with \<open>?sp < sp' \<le> s\<close>).  This is forced arithmetically:
  \<open>le0\<close> gives \<open>j' \<le> ?y\<close>, and \<open>?c < j'\<close> with \<open>?c, ?y\<close> both in block \<open>q\<close>
  (offsets \<open>?sp < s\<close>) confines \<open>j'\<close> to block \<open>q\<close> -- the ``2360 cross-block
  cases'' are VACUOUS under the lower bound \<open>?c < j'\<close>.  The valley then reduces
  to the M-side maximality:
  \<^item> N\<rightarrow>M le0 reflection (SAME block) via @{thm [source] oper_d1pos_le0_base_back}:
    \<open>le0 (M[n]) j' ?y \<Longrightarrow> le0 M (j\<^sub>0+sp') ?u\<close> (offsets \<open>sp' < s\<close>);
  \<^item> M parent maximality (the valley clause of \<open>nextrel1 M ?pM ?u\<close>): since
    \<open>?pM < j\<^sub>0+sp'\<close> and \<open>le0 M (j\<^sub>0+sp') ?u\<close>, \<open>entry M 1 ?u \<le> entry M 1 (j\<^sub>0+sp')\<close>;
  \<^item> periodic ROW-1 readback @{thm [source] oper_gen_block_entry1}:
    \<open>entry (M[n]) 1 j' = entry M 1 (j\<^sub>0+sp')\<close> and \<open>entry (M[n]) 1 ?y = entry M 1 ?u\<close>.
  Cites only already-GREEN RedCondA-free bricks (oper block entry, base_back le0
  reflection, nextrel1 M parent edge); no spsy / sblk / RedCond / tail_affine.\<close>

lemma oper_parent1_readback:
  fixes M :: pairseq
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and qn: "q < n"
    and s0: "0 < s"
    and sw: "s < Lng M - 1 - parent M 1 (Lng M - 1)"
    and hpMs: "hasParent M 1 (parent M 1 (Lng M - 1) + s)"
    and pMge: "parent M 1 (parent M 1 (Lng M - 1) + s) \<ge> parent M 1 (Lng M - 1)"
  shows "parent ((M::pairseq)[n]) 1
            (parent M 1 (Lng M - 1)
               + q * (Lng M - 1 - parent M 1 (Lng M - 1)) + s)
       = parent M 1 (parent M 1 (Lng M - 1) + s)
           + q * (Lng M - 1 - parent M 1 (Lng M - 1))"
proof -
  let ?j1 = "Lng M - 1"  let ?j0 = "parent M 1 ?j1"  let ?w = "?j1 - ?j0"
  let ?Mn = "(M::pairseq)[n]"
  let ?u = "?j0 + s"           \<comment> \<open>the M-side child (offset \<open>s\<close>)\<close>
  let ?pM = "parent M 1 ?u"    \<comment> \<open>the M-side row-1 parent of \<open>?u\<close>\<close>
  let ?y = "?j0 + q * ?w + s"  \<comment> \<open>the N-side interior column\<close>
  let ?c = "?pM + q * ?w"      \<comment> \<open>the candidate N-side parent\<close>
  let ?sp = "?pM - ?j0"        \<comment> \<open>offset of \<open>?c\<close> in block \<open>q\<close>\<close>
  have w0: "0 < ?w" using j0lt by linarith
  have hpidx: "hasParent M (idx1 M ?j1) ?j1" using hp .
  have pj0eq: "parent M (idx1 M ?j1) ?j1 = ?j0" using i1z by simp
  have j0lt': "parent M (idx1 M ?j1) ?j1 < ?j1" using j0lt pj0eq by simp
  \<comment> \<open>the M-side row-1 parent edge \<open>nextrel1 M p\<^sub>M ?u\<close> and its VALLEY clause\<close>
  have parRMu: "nextR M 1 ?pM ?u"
    using hpMs unfolding hasParent_def parent_def by (rule theI')
  have nr1Mu: "nextrel1 M ?pM ?u" using parRMu by (simp add: nextR_def)
  have pMlt: "?pM < ?u" using nr1Mu by (simp add: nextrel1_def)
  have pMge': "?j0 \<le> ?pM" using pMge .
  have splt_s: "?sp < s" using pMlt pMge' by linarith
  have spw: "?sp < ?w" using splt_s sw by linarith
  have pM_eq: "?pM = ?j0 + ?sp" using pMge' by simp
  \<comment> \<open>the M parent maximality clause, extracted from \<open>nextrel1 M ?pM ?u\<close>\<close>
  have Mvalley: "\<And>j. ?pM < j \<Longrightarrow> le0 M j ?u \<Longrightarrow> entry M 1 ?u \<le> entry M 1 j"
    using nr1Mu unfolding nextrel1_def by blast
  \<comment> \<open>DISCHARGE THE VALLEY: every \<open>le0\<close>-predecessor of \<open>?y\<close> above \<open>?c\<close> is in block \<open>q\<close>\<close>
  have valley: "\<And>j'. ?c < j' \<Longrightarrow> le0 ?Mn j' ?y
                  \<Longrightarrow> entry ?Mn 1 j' \<ge> entry ?Mn 1 ?y"
  proof -
    fix j' assume cj': "?c < j'" and le0j': "le0 ?Mn j' ?y"
    \<comment> \<open>\<open>j' \<le> ?y\<close> from the row-0 reach\<close>
    have jy: "j' \<le> ?y"
    proof -
      have "(nextrel0 ?Mn)\<^sup>*\<^sup>* j' ?y" using le0j' by (simp add: le0_def)
      thus ?thesis by (rule nextrel0_rtrancl_mono)
    qed
    \<comment> \<open>\<open>?c = ?j0 + q\<cdot>w + ?sp\<close>, so \<open>j'\<close> has block offset \<open>sp'\<close> with \<open>?sp < sp' \<le> s\<close>\<close>
    have cform: "?c = ?j0 + q * ?w + ?sp" using pM_eq by (simp add: ac_simps)
    have lo: "?j0 + q * ?w + ?sp < j'" using cj' cform by simp
    have hi: "j' \<le> ?j0 + q * ?w + s" using jy by simp
    \<comment> \<open>explicit block offset \<open>sp' = j' - (j\<^sub>0 + q\<cdot>w)\<close> (deterministic; avoids slow metis)\<close>
    define sp' where "sp' = j' - (?j0 + q * ?w)"
    have ge_base: "?j0 + q * ?w \<le> j'" using lo by linarith
    have spp: "j' = ?j0 + q * ?w + sp'" using sp'_def ge_base by simp
    have spp_lo: "?sp < sp'" using lo spp by linarith
    have spp_hi: "sp' \<le> s" using hi spp by linarith
    show "entry ?Mn 1 j' \<ge> entry ?Mn 1 ?y"
    proof (cases "sp' = s")
      case True
      \<comment> \<open>\<open>j' = ?y\<close>: trivial\<close>
      have "j' = ?y" using spp True by simp
      thus ?thesis by simp
    next
      case False
      have spps: "sp' < s" using spp_hi False by simp
      have spw': "s < ?w" using sw by simp
      \<comment> \<open>N\<rightarrow>M le0 reflection (same block \<open>q\<close>): \<open>le0 M (?j0+sp') ?u\<close>\<close>
      have reachN: "le0 ?Mn (?j0 + q * ?w + sp') (?j0 + q * ?w + s)"
        using le0j' spp by simp
      have le0Msp: "le0 M (?j0 + sp') (?j0 + s)"
        by (rule oper_d1pos_le0_base_back
              [OF L notzero hpidx i1z j0lt qn spps spw' reachN])
      have le0Msp': "le0 M (?j0 + sp') ?u" using le0Msp by simp
      \<comment> \<open>\<open>?pM < ?j0+sp'\<close> from \<open>?sp < sp'\<close>, so the M valley applies\<close>
      have pMlt': "?pM < ?j0 + sp'" using pM_eq spp_lo by simp
      have eM: "entry M 1 ?u \<le> entry M 1 (?j0 + sp')"
        by (rule Mvalley[OF pMlt' le0Msp'])
      \<comment> \<open>periodic ROW-1 readback at both columns\<close>
      have spw'': "sp' < ?w" using spps spw' by linarith
      have rb_j': "entry ?Mn 1 (?j0 + q * ?w + sp') = entry M 1 (?j0 + sp')"
      proof -
        have raw: "entry ?Mn 1 (parent M (idx1 M ?j1) ?j1
                     + q * (?j1 - parent M (idx1 M ?j1) ?j1) + sp')
                 = entry M 1 (parent M (idx1 M ?j1) ?j1 + sp')"
          by (rule oper_gen_block_entry1[OF L notzero hpidx j0lt' qn]) (use spw'' i1z in simp)
        show ?thesis using raw i1z by simp
      qed
      have rb_y: "entry ?Mn 1 ?y = entry M 1 ?u"
      proof -
        have raw: "entry ?Mn 1 (parent M (idx1 M ?j1) ?j1
                     + q * (?j1 - parent M (idx1 M ?j1) ?j1) + s)
                 = entry M 1 (parent M (idx1 M ?j1) ?j1 + s)"
          by (rule oper_gen_block_entry1[OF L notzero hpidx j0lt' qn]) (use sw i1z in simp)
        show ?thesis using raw i1z by simp
      qed
      have "entry ?Mn 1 ?y = entry M 1 ?u" using rb_y .
      also have "\<dots> \<le> entry M 1 (?j0 + sp')" using eM .
      also have "\<dots> = entry ?Mn 1 j'" using rb_j' spp by simp
      finally show ?thesis .
    qed
  qed
  show ?thesis
    by (rule oper_parent1_readback_interior
          [OF L notzero hp i1z j0lt qn s0 sw hpMs pMge valley])
qed


text \<open>§6.7 BOUNDARY (\<open>s = 0\<close>) row-1 parent READBACK (attempt Z), CONDITIONAL.
  For a BLOCK-START column \<open>z = j\<^sub>0 + q\<cdot>w\<close> of \<open>M[n]\<close> (offset \<open>s = 0\<close>) the row-1
  parent lands in the verbatim PREFIX \<open>x < j\<^sub>0\<close>, at the FIXED node
  \<open>p\<^sub>j = parent M 1 j\<^sub>0\<close> --- INDEPENDENTLY of the block index \<open>q\<close>:
  \<open>parent (M[n]) 1 (j\<^sub>0 + q\<cdot>w) = parent M 1 j\<^sub>0\<close>.  This is the clean closed form
  pinned EMPIRICALLY (0-fail on the broad ST\_PS closure, depth\<ge>5, base \<open>u 0..3
  v u..6\<close>, maxlen 16, NOT is\_standard; python/_Z_main.py: q=0 3870/0,
  q\<ge>1 7740/0; ingredients 11610/11610).  The candidate-edge ingredients are all
  GREEN/RedCondA-free:
  \<^item> the prefix-to-block-start row-0 reach \<open>le0 (M[n]) p\<^sub>j (j\<^sub>0+q\<cdot>w)\<close> assembled
    from the M-side parent edge \<open>nextrel1 M p\<^sub>j j\<^sub>0\<close> lifted over the verbatim
    prefix \<open>[0,j\<^sub>0]\<close> (@{thm [source] le0_prefix_agree}, using \<open>(M[n]) ! j\<^sub>0 = M ! j\<^sub>0\<close>
    via @{thm [source] oper_gen_block_nth} at \<open>q=0,s=0\<close>) chained
    (@{thm [source] le0_trans}) with the block-start reach
    @{thm [source] oper_d1pos_le0_blockstarts};
  \<^item> the periodic ROW-1 readback @{thm [source] oper_gen_block_entry1} (block-start,
    \<open>s=0\<close>: \<open>entry (M[n]) 1 (j\<^sub>0+q\<cdot>w) = entry M 1 j\<^sub>0\<close>) and the verbatim prefix read
    @{thm [source] operB_gen_entry_prefix} (\<open>entry (M[n]) 1 p\<^sub>j = entry M 1 p\<^sub>j\<close>).
  The SINGLE residual is the BOUNDARY VALLEY clause: unlike the interior case the
  lower cut \<open>p\<^sub>j\<close> sits in the prefix, so the valley predecessors are GENUINELY
  cross-block (prefix 21075, same-block 6450, cross-block 26172 on the closure;
  python/_Z_readback.py) and the vacuity argument of
  @{thm [source] oper_parent1_readback} does NOT apply.  We therefore take the
  boundary maximality as the ONE hypothesis, mirroring the shape of
  @{thm [source] oper_parent1_readback_interior}.  Cites only already-GREEN
  RedCondA-free bricks; no spsy / sblk / RedCond / oper-tiling / tail_affine.\<close>

lemma oper_parent1_readback_boundary:
  fixes M :: pairseq
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and qn: "q < n"
    and hpMj0: "hasParent M 1 (parent M 1 (Lng M - 1))"
    and pjlt: "parent M 1 (parent M 1 (Lng M - 1)) < parent M 1 (Lng M - 1)"
    \<comment> \<open>the ONE residual: the boundary (cross-block) VALLEY clause of the readback edge\<close>
    and valley: "\<And>j'. parent M 1 (parent M 1 (Lng M - 1)) < j'
                  \<Longrightarrow> le0 ((M::pairseq)[n]) j'
                          (parent M 1 (Lng M - 1)
                             + q * (Lng M - 1 - parent M 1 (Lng M - 1)))
                  \<Longrightarrow> entry ((M::pairseq)[n]) 1 j'
                        \<ge> entry ((M::pairseq)[n]) 1
                              (parent M 1 (Lng M - 1)
                                 + q * (Lng M - 1 - parent M 1 (Lng M - 1)))"
  shows "parent ((M::pairseq)[n]) 1
            (parent M 1 (Lng M - 1)
               + q * (Lng M - 1 - parent M 1 (Lng M - 1)))
       = parent M 1 (parent M 1 (Lng M - 1))"
proof -
  let ?j1 = "Lng M - 1"  let ?j0 = "parent M 1 ?j1"  let ?w = "?j1 - ?j0"
  let ?Mn = "(M::pairseq)[n]"
  let ?pj = "parent M 1 ?j0"   \<comment> \<open>the M-side row-1 parent of the block start \<open>j\<^sub>0\<close>\<close>
  let ?z = "?j0 + q * ?w"      \<comment> \<open>the N-side block-start column (offset \<open>0\<close>)\<close>
  have w0: "0 < ?w" using j0lt by linarith
  have hpidx: "hasParent M (idx1 M ?j1) ?j1" using hp .
  have pj0eq: "parent M (idx1 M ?j1) ?j1 = ?j0" using i1z by simp
  have j0lt': "parent M (idx1 M ?j1) ?j1 < ?j1" using j0lt pj0eq by simp
  \<comment> \<open>the M-side row-1 parent edge \<open>nextrel1 M ?pj j\<^sub>0\<close>\<close>
  have parRMj0: "nextR M 1 ?pj ?j0"
    using hpMj0 unfolding hasParent_def parent_def by (rule theI')
  have nr1Mj0: "nextrel1 M ?pj ?j0" using parRMj0 by (simp add: nextR_def)
  have eMlt: "entry M 1 ?pj < entry M 1 ?j0" using nr1Mj0 by (simp add: nextrel1_def)
  have le0Mj0: "le0 M ?pj ?j0" using nr1Mj0 by (simp add: nextrel1_def)
  have pjlt': "?pj < ?j0" using pjlt .
  \<comment> \<open>\<open>j\<^sub>0 < Lng M\<close>\<close>
  have j0L: "?j0 < Lng M" using j0lt by linarith
  have n0: "0 < n" using qn by simp
  \<comment> \<open>VERBATIM PREFIX \<open>[0, j\<^sub>0]\<close>: \<open>M[n] ! x = M ! x\<close> for \<open>x \<le> j\<^sub>0\<close>\<close>
  have nthj0: "?Mn ! ?j0 = M ! ?j0"
  proof -
    have raw: "?Mn ! (parent M (idx1 M ?j1) ?j1
                 + 0 * (?j1 - parent M (idx1 M ?j1) ?j1) + 0)
             = (entry M 0 (parent M (idx1 M ?j1) ?j1 + 0)
                  + 0 * (if 0 < idx1 M ?j1 then entry M 0 ?j1
                           - entry M 0 (parent M (idx1 M ?j1) ?j1) else 0),
                entry M 1 (parent M (idx1 M ?j1) ?j1 + 0))"
      by (rule oper_gen_block_nth[OF L notzero hpidx j0lt' n0, where s=0])
         (use j0lt' in linarith)
    have lhs: "?Mn ! (parent M (idx1 M ?j1) ?j1
                 + 0 * (?j1 - parent M (idx1 M ?j1) ?j1) + 0) = ?Mn ! ?j0"
      using pj0eq by simp
    have rhs: "(entry M 0 (parent M (idx1 M ?j1) ?j1 + 0)
                  + 0 * (if 0 < idx1 M ?j1 then entry M 0 ?j1
                           - entry M 0 (parent M (idx1 M ?j1) ?j1) else 0),
                entry M 1 (parent M (idx1 M ?j1) ?j1 + 0))
             = (entry M 0 ?j0, entry M 1 ?j0)" using pj0eq by simp
    have mj0: "M ! ?j0 = (entry M 0 ?j0, entry M 1 ?j0)"
      by (simp add: entry_def)
    show ?thesis using raw lhs rhs mj0 by simp
  qed
  have agree: "\<And>x. x \<le> ?j0 \<Longrightarrow> ?Mn ! x = M ! x"
  proof -
    fix x assume xj0: "x \<le> ?j0"
    show "?Mn ! x = M ! x"
    proof (cases "x = ?j0")
      case True thus ?thesis using nthj0 by simp
    next
      case False
      have xlt: "x < ?j0" using xj0 False by simp
      show ?thesis by (rule oper_gen_nth_prefix[OF L notzero hpidx]) (use xlt pj0eq in simp)
    qed
  qed
  \<comment> \<open>\<open>Lng (M[n]) = j\<^sub>0 + n\<cdot>w\<close>, hence \<open>z, j\<^sub>0 < Lng (M[n])\<close>\<close>
  have lenMn: "Lng ?Mn = ?j0 + n * ?w"
    using oper_d1pos_LngM[OF L notzero hp i1z j0lt] by simp
  have zlt: "?z < Lng ?Mn"
  proof -
    have "?z < ?j0 + q * ?w + ?w" using w0 by simp
    also have "\<dots> = ?j0 + (q + 1) * ?w" by simp
    also have "\<dots> \<le> ?j0 + n * ?w" using mult_le_mono1[of "q+1" n ?w] qn by simp
    finally show ?thesis using lenMn by simp
  qed
  have j0ltMn: "?j0 < Lng ?Mn"
  proof -
    have "?j0 \<le> ?z" by simp
    thus ?thesis using zlt by linarith
  qed
  \<comment> \<open>(A) row-0 REACH \<open>le0 (M[n]) ?pj ?z\<close>: prefix lift \<open>?pj \<rightarrow> j\<^sub>0\<close> chained with block-start reach\<close>
  have le0_pj_j0: "le0 ?Mn ?pj ?j0"
  proof (rule le0_prefix_agree[where c="?j0" and M=M])
    show "\<And>j. j \<le> ?j0 \<Longrightarrow> M ! j = ?Mn ! j" using agree by simp
    show "?j0 < Lng M" using j0L .
    show "?j0 < Lng ?Mn" using j0ltMn .
    show "?pj \<le> ?j0" using pjlt' by simp
    show "?j0 \<le> ?j0" by simp
    show "le0 M ?pj ?j0" using le0Mj0 .
  qed
  have le0_j0_z: "le0 ?Mn ?j0 ?z"
    by (rule oper_d1pos_le0_blockstarts[OF L notzero hp i1z j0lt qn])
  have le0_pj_z: "le0 ?Mn ?pj ?z" using le0_trans[OF le0_pj_j0 le0_j0_z] .
  have zL: "?z < Lng ?Mn" using zlt .
  have pjL: "?pj < Lng ?Mn" using le0_pj_z by (simp add: le0_def)
  have pjltz: "?pj < ?z"
  proof -
    have "?pj < ?j0" using pjlt' .
    also have "?j0 \<le> ?z" by simp
    finally show ?thesis .
  qed
  \<comment> \<open>(B) ENTRIES: prefix read at \<open>?pj\<close>, block-start read at \<open>?z\<close>\<close>
  have e_pj: "entry ?Mn 1 ?pj = entry M 1 ?pj"
    by (rule operB_gen_entry_prefix[OF L notzero hpidx]) (use pjlt' pj0eq in simp)
  have e_z: "entry ?Mn 1 ?z = entry M 1 ?j0"
  proof -
    have raw: "entry ?Mn 1 (parent M (idx1 M ?j1) ?j1
                 + q * (?j1 - parent M (idx1 M ?j1) ?j1) + 0)
             = entry M 1 (parent M (idx1 M ?j1) ?j1 + 0)"
      by (rule oper_gen_block_entry1[OF L notzero hpidx j0lt' qn, where s=0])
         (use j0lt' in linarith)
    show ?thesis using raw pj0eq by simp
  qed
  have elt: "entry ?Mn 1 ?pj < entry ?Mn 1 ?z" using e_pj e_z eMlt by simp
  \<comment> \<open>(C) assemble the readback edge \<open>nextrel1 (M[n]) ?pj ?z\<close> with the boundary valley\<close>
  have nrPZ: "nextrel1 ?Mn ?pj ?z"
    unfolding nextrel1_def
  proof (intro conjI allI impI)
    show "?pj < Lng ?Mn" using pjL .
    show "?z < Lng ?Mn" using zL .
    show "?pj < ?z" using pjltz .
    show "entry ?Mn 1 ?pj < entry ?Mn 1 ?z" using elt .
    show "le0 ?Mn ?pj ?z" using le0_pj_z .
  next
    fix j' assume a: "?pj < j' \<and> le0 ?Mn j' ?z"
    have a1: "?pj < j'" using a by simp
    have a2: "le0 ?Mn j' ?z" using a by simp
    show "entry ?Mn 1 ?z \<le> entry ?Mn 1 j'"
      using valley[OF a1 a2] by simp
  qed
  \<comment> \<open>\<open>?pj\<close> IS the (unique) row-1 parent of \<open>?z\<close> in \<open>M[n]\<close>\<close>
  have hpZ: "hasParent ?Mn 1 ?z"
    unfolding hasParent_def
  proof (rule ex_ex1I)
    show "\<exists>a. nextR ?Mn 1 a ?z" using nrPZ by (auto simp: nextR_def)
  next
    fix a b assume "nextR ?Mn 1 a ?z" "nextR ?Mn 1 b ?z"
    thus "a = b" by (rule nextR1_unique)
  qed
  have "(THE a. nextR ?Mn 1 a ?z) = ?pj"
  proof (rule the1_equality)
    show "\<exists>!a. nextR ?Mn 1 a ?z" using hpZ unfolding hasParent_def .
    show "nextR ?Mn 1 ?pj ?z" using nrPZ by (simp add: nextR_def)
  qed
  thus ?thesis unfolding parent_def .
qed


text \<open>From the FULLRAMP invariant the tree well-formedness clause follows at any
  gated interior \<open>z\<close> with \<open>parent N 1 z > j\<^sub>0\<close>: restrict the whole-tail ramp to
  \<open>[parent N 1 z, j\<^sub>1)\<close> (\<open>parent N 1 z \<ge> j\<^sub>0\<close> by \<open>pge\<close>) and feed
  @{thm [source] m_6_7_tree_wellformed_via_subramp}.\<close>

lemma tree_from_fullramp:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and hp1: "hasParent N 1 (Lng N - 1)"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and zlo: "parent N 1 (Lng N - 1) < z"
    and zhi: "z < Lng N - 1"
    and hpz: "hasParent N 1 z"
    and pge: "parent N 1 z \<ge> parent N 1 (Lng N - 1)"
    and pgt: "parent N 1 z > parent N 1 (Lng N - 1)"
    and ramp: "\<And>x. parent N 1 (Lng N - 1) \<le> x \<Longrightarrow> x < Lng N - 1
                 \<Longrightarrow> entry N 0 (Suc x) = Suc (entry N 0 x)"
  shows "hasParent N 1 (parent N 1 z)
         \<and> parent N 1 (parent N 1 z) \<ge> parent N 1 (Lng N - 1)"
proof -
  \<comment> \<open>the sub-range ramp on \<open>[parent N 1 z, j\<^sub>1)\<close> from the whole-tail ramp\<close>
  have rampP: "\<And>x. parent N 1 z \<le> x \<Longrightarrow> x < Lng N - 1
                 \<Longrightarrow> entry N 0 (Suc x) = Suc (entry N 0 x)"
  proof -
    fix x assume xlo: "parent N 1 z \<le> x" and xhi: "x < Lng N - 1"
    have "parent N 1 (Lng N - 1) \<le> x" using pge xlo by simp
    thus "entry N 0 (Suc x) = Suc (entry N 0 x)" using ramp xhi by simp
  qed
  show ?thesis
    by (rule m_6_7_tree_wellformed_via_subramp
          [OF L hp1 j0lt zlo zhi hpz pge pgt rampP])
qed





text \<open>§6.7 GS STEP B (assembly), CORE.  From the GLOBAL row-0 \<open>+1\<close> ramp
  \<open>gstrict_full(N)\<close> (every step on \<open>[0, j\<^sub>1)\<close> is \<open>+1\<close>) the spsy TREE clause at any
  gated interior \<open>z\<close> follows: restrict the global ramp to the tail \<open>[j\<^sub>0, j\<^sub>1)\<close> and
  feed @{thm [source] tree_from_fullramp}.  Cites only the already-GREEN
  @{thm [source] tree_from_fullramp}; no spsy / sblk / RedCond / tail_affine.\<close>

lemma gs_tree_from_gstrict:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and hp1: "hasParent N 1 (Lng N - 1)"
    and j0lt: "parent N 1 (Lng N - 1) < Lng N - 1"
    and zlo: "parent N 1 (Lng N - 1) < z"
    and zhi: "z < Lng N - 1"
    and hpz: "hasParent N 1 z"
    and pge: "parent N 1 z \<ge> parent N 1 (Lng N - 1)"
    and pgt: "parent N 1 z > parent N 1 (Lng N - 1)"
    and gstrict: "\<And>y. y < Lng N - 1 \<Longrightarrow> entry N 0 (Suc y) = Suc (entry N 0 y)"
  shows "hasParent N 1 (parent N 1 z)
         \<and> parent N 1 (parent N 1 z) \<ge> parent N 1 (Lng N - 1)"
proof -
  have ramp: "\<And>x. parent N 1 (Lng N - 1) \<le> x \<Longrightarrow> x < Lng N - 1
                 \<Longrightarrow> entry N 0 (Suc x) = Suc (entry N 0 x)"
    using gstrict by simp
  show ?thesis
    by (rule tree_from_fullramp[OF L hp1 j0lt zlo zhi hpz pge pgt ramp])
qed

end
