theory Support_6_060
  imports Frontier_6_080
begin

text \<open>§6.7 hpN SAME-BLOCK residual \<open>sblk\<close> (Front B, \<open>i\<^sub>1=1\<close>): the ARGMIN coincidence
  \<open>q\<^sub>p = q\<^sub>y\<close> for the non-prefix \<open>N[n]\<close>-parent \<open>p = parent (N[n]) 1 y\<close> (\<open>j\<^sub>0 \<le> p\<close>),
  i.e. \<open>(p-j\<^sub>0) div w = (y-j\<^sub>0) div w\<close>.  From \<open>p < y\<close> we get \<open>q\<^sub>p \<le> q\<^sub>y\<close> for free.
  If \<open>q\<^sub>p < q\<^sub>y\<close>, the SAME-OFFSET column in \<open>y\<close>'s own block, \<open>c\<^sub>0 = j\<^sub>0 + q\<^sub>y\<cdot>w + s\<^sub>p\<close>
  (\<open>s\<^sub>p = (p-j\<^sub>0) mod w\<close>), is (i) strictly past \<open>p\<close> (\<open>p < c\<^sub>0\<close>, since \<open>q\<^sub>p < q\<^sub>y\<close>);
  (ii) \<open>le0 (N[n])\<close>-reachable to \<open>y\<close> within block \<open>q\<^sub>y\<close> by the offset-within brick
  \<open>owithin\<close> (needs \<open>s\<^sub>p \<le> s\<^sub>y\<close>, the offset-monotonicity \<open>spsy\<close>); (iii) has the SAME
  row-1 value as \<open>p\<close> by periodicity (@{thm [source] operCA_tiling_entry1_base'},
  both at offset \<open>s\<^sub>p\<close>), hence \<open>entry (N[n]) 1 c\<^sub>0 < entry (N[n]) 1 y\<close>.  But the
  VALLEY clause of \<open>nextrel1 (N[n]) p y\<close> (\<open>p\<close> IS the parent) forces
  \<open>entry (N[n]) 1 c\<^sub>0 \<ge> entry (N[n]) 1 y\<close> — contradiction.  Conditional on the two
  Front-A offset residuals \<open>owithin\<close> (offset-to-offset within ONE block) and
  \<open>spsy\<close> (\<open>s\<^sub>p \<le> s\<^sub>y\<close>), both empirically 1212/1212 (/tmp/_fb_sblk_route.py,
  /tmp/_fb_sp_sy.py).\<close>

lemma operCA_tiling_sblk_via_owithin:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y"
    and hpny: "hasParent ((N::pairseq)[n]) 1 y"
    and pge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> parent ((N::pairseq)[n]) 1 y"
    and spsy: "(parent ((N::pairseq)[n]) 1 y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                  mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
               \<le> (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                  mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
    and owithin: "\<And>q sp sx. sp \<le> sx
                   \<Longrightarrow> sx < Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                   \<Longrightarrow> q < n
                   \<Longrightarrow> le0 ((N::pairseq)[n])
                          (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                             + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)) + sp)
                          (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                             + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)) + sx)"
  shows "(parent ((N::pairseq)[n]) 1 y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
           div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
         = (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
           div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?Nn = "(N::pairseq)[n]"
  let ?p = "parent ?Nn 1 y"
  let ?sy = "(y - ?j0) mod ?w"  let ?qy = "(y - ?j0) div ?w"
  let ?sp = "(?p - ?j0) mod ?w"  let ?qp = "(?p - ?j0) div ?w"
  let ?c0 = "?j0 + ?qy * ?w + ?sp"
  have w0: "0 < ?w" using j0lt by linarith
  have j0w1: "?j0 + ?w = ?j1" using j0lt by simp
  have lenNn: "Lng ?Nn = ?j0 + n * ?w"
    by (rule operB_gen_LngM[OF L notzero hp j0lt])
  \<comment> \<open>parent edge of \<open>y\<close>\<close>
  have nrely: "nextrel1 ?Nn ?p y"
  proof -
    have "\<exists>!a. nextR ?Nn 1 a y" using hpny unfolding hasParent_def by simp
    hence "nextR ?Nn 1 ?p y" unfolding parent_def by (rule theI')
    thus ?thesis by (simp add: nextR_def)
  qed
  from nrely have py: "?p < y" and yNn: "y < Lng ?Nn"
    and e1py: "entry ?Nn 1 ?p < entry ?Nn 1 y"
    and valley: "\<forall>x. ?p < x \<and> le0 ?Nn x y \<longrightarrow> entry ?Nn 1 x \<ge> entry ?Nn 1 y"
    by (auto simp: nextrel1_def)
  \<comment> \<open>decode \<open>p\<close>, \<open>y\<close>\<close>
  have syw: "?sy < ?w" using w0 by simp
  have spw: "?sp < ?w" using w0 by simp
  have ymj: "y - ?j0 < n * ?w" using yNn lenNn ge by linarith
  have qyn: "?qy < n" using less_mult_imp_div_less[OF ymj] .
  have psplit: "?p = ?j0 + ?qp * ?w + ?sp"
  proof -
    have "?qp * ?w + ?sp = ?p - ?j0"
      using div_mult_mod_eq[of "?p - ?j0" ?w] by (simp add: mult.commute)
    thus ?thesis using pge by linarith
  qed
  have ysplit: "y = ?j0 + ?qy * ?w + ?sy"
  proof -
    have "?qy * ?w + ?sy = y - ?j0"
      using div_mult_mod_eq[of "y - ?j0" ?w] by (simp add: mult.commute)
    thus ?thesis using ge by linarith
  qed
  \<comment> \<open>\<open>q\<^sub>p \<le> q\<^sub>y\<close> for free from \<open>p < y\<close>\<close>
  have pmj: "?p - ?j0 \<le> y - ?j0" using py pge by linarith
  have qpqy: "?qp \<le> ?qy" using div_le_mono[OF pmj] .
  \<comment> \<open>\<open>s\<^sub>p \<le> s\<^sub>y\<close> from the supplied offset-monotonicity\<close>
  have spsy': "?sp \<le> ?sy" using spsy by simp
  show ?thesis
  proof (rule ccontr)
    assume "?qp \<noteq> ?qy"
    hence qplt: "?qp < ?qy" using qpqy by linarith
    \<comment> \<open>the same-offset witness \<open>c\<^sub>0 = j\<^sub>0 + q\<^sub>y\<cdot>w + s\<^sub>p\<close> sits strictly past \<open>p\<close>\<close>
    have pc0: "?p < ?c0"
    proof -
      have "?p = ?j0 + ?qp * ?w + ?sp" using psplit .
      also have "\<dots> < ?j0 + ?qy * ?w + ?sp"
        using qplt w0 by simp
      finally show ?thesis .
    qed
    \<comment> \<open>\<open>c\<^sub>0\<close> reaches \<open>y\<close> within block \<open>q\<^sub>y\<close> (offsets \<open>s\<^sub>p \<le> s\<^sub>y\<close>)\<close>
    have reachc0: "le0 ?Nn ?c0 (?j0 + ?qy * ?w + ?sy)"
      by (rule owithin[OF spsy' syw qyn])
    have reachc0': "le0 ?Nn ?c0 y" using reachc0 ysplit by simp
    \<comment> \<open>periodicity: \<open>c\<^sub>0\<close> and \<open>p\<close> have the same row-1 reading \<open>entry N 1 (j\<^sub>0 + s\<^sub>p)\<close>\<close>
    have c0Nn: "?c0 < Lng ?Nn" using reachc0' by (simp add: le0_def)
    have base_c0: "(if ?c0 < ?j0 then ?c0 else ?j0 + (?c0 - ?j0) mod ?w) = ?j0 + ?sp"
    proof -
      have nge: "\<not> ?c0 < ?j0" by simp
      have "(?c0 - ?j0) mod ?w = ?sp"
      proof -
        have "?c0 - ?j0 = ?qy * ?w + ?sp" by simp
        thus ?thesis by simp
      qed
      thus ?thesis using nge by simp
    qed
    have e1c0: "entry ?Nn 1 ?c0 = entry N 1 (?j0 + ?sp)"
    proof -
      have "entry ?Nn 1 ?c0
              = entry N 1 (if ?c0 < ?j0 then ?c0 else ?j0 + (?c0 - ?j0) mod ?w)"
        by (rule operCA_tiling_entry1_base'[OF L notzero hp j0lt c0Nn])
      thus ?thesis using base_c0 by simp
    qed
    have pNn: "?p < Lng ?Nn" using py yNn by linarith
    have base_p: "(if ?p < ?j0 then ?p else ?j0 + (?p - ?j0) mod ?w) = ?j0 + ?sp"
      using pge by simp
    have e1p: "entry ?Nn 1 ?p = entry N 1 (?j0 + ?sp)"
    proof -
      have "entry ?Nn 1 ?p
              = entry N 1 (if ?p < ?j0 then ?p else ?j0 + (?p - ?j0) mod ?w)"
        by (rule operCA_tiling_entry1_base'[OF L notzero hp j0lt pNn])
      thus ?thesis using base_p by simp
    qed
    have e1eq: "entry ?Nn 1 ?c0 = entry ?Nn 1 ?p" using e1c0 e1p by simp
    \<comment> \<open>\<open>c\<^sub>0\<close> beats the strict-decrease but obeys the valley: contradiction\<close>
    have lt: "entry ?Nn 1 ?c0 < entry ?Nn 1 y" using e1eq e1py by simp
    have ge': "entry ?Nn 1 y \<le> entry ?Nn 1 ?c0" using valley pc0 reachc0' by blast
    show False using lt ge' by simp
  qed
qed


text \<open>§6.7 hpN UNCONDITIONAL on the argmin offset residuals (Front B, \<open>i\<^sub>1=1\<close>):
  the period-base row-1 parent existence \<open>hasParent N 1 (base y)\<close>, with the
  same-block residual \<open>sblk\<close> of @{thm [source] operCA_tiling_hpN_via_sblk}
  discharged by @{thm [source] operCA_tiling_sblk_via_owithin}.  The PREFIX branch
  (\<open>p < j\<^sub>0\<close>) is already unconditional; the non-prefix branch needs only the two
  Front-A offset residuals \<open>owithin\<close> (offset-to-offset within ONE block) and
  \<open>spsy\<close> (\<open>s\<^sub>p \<le> s\<^sub>y\<close>).\<close>

lemma operCA_tiling_hpN_via_owithin:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and n1: "1 \<le> n"
    and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y"
    and hpny: "hasParent ((N::pairseq)[n]) 1 y"
    and spsy: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> parent ((N::pairseq)[n]) 1 y
               \<Longrightarrow> (parent ((N::pairseq)[n]) 1 y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                     mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                   \<le> (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                     mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
    and owithin: "\<And>q sp sx. sp \<le> sx
                   \<Longrightarrow> sx < Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                   \<Longrightarrow> q < n
                   \<Longrightarrow> le0 ((N::pairseq)[n])
                          (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                             + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)) + sp)
                          (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                             + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)) + sx)"
  shows "hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                   mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
proof -
  have sblk: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> parent ((N::pairseq)[n]) 1 y
               \<Longrightarrow> (parent ((N::pairseq)[n]) 1 y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                     div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                   = (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                     div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
  proof -
    assume pge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> parent ((N::pairseq)[n]) 1 y"
    show "(parent ((N::pairseq)[n]) 1 y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
            div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
          = (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
            div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
      by (rule operCA_tiling_sblk_via_owithin[OF L notzero hp i1z j0lt ge hpny pge
            spsy[OF pge] owithin])
  qed
  show ?thesis
    by (rule operCA_tiling_hpN_via_sblk[OF L notzero hp i1z j0lt n1 ge hpny sblk])
qed


text \<open>§6.7/§6.5 FINAL DISCHARGE conditional on the Front-A offset residuals only.
  The hpN meta-assumption of @{thm [source] m_6_7_standard_reduced_hpN_valley} /
  @{thm [source] m_6_5_ST_PS_imp_RedCondA_hpN_valley} is discharged by
  @{thm [source] operCA_tiling_hpN_via_owithin}; the valley meta-assumption is
  carried through verbatim (Front A).  The remaining hypotheses are the two
  Front-A offset bricks \<open>owithin\<close> (offset-to-offset within one tiling block) and
  \<open>spsy\<close> (\<open>s\<^sub>p \<le> s\<^sub>y\<close>, offset monotonicity) and Front A's per-competitor row-1
  minimality \<open>valley\<close>.\<close>

lemma m_6_7_standard_reduced_via_owithin_valleyA:
  assumes owithin: "\<And>N n q sp sx. \<lbrakk>N \<in> ST_PS;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1));
                   idx1 N (Lng N - 1) = 1;
                   sp \<le> sx;
                   sx < Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1);
                   q < n\<rbrakk>
                 \<Longrightarrow> le0 ((N::pairseq)[n])
                        (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                           + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)) + sp)
                        (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                           + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)) + sx)"
    and spsy: "\<And>N n y. \<lbrakk>N \<in> ST_PS;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1));
                   parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y;
                   hasParent ((N::pairseq)[n]) 1 y;
                   idx1 N (Lng N - 1) = 1;
                   parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> parent ((N::pairseq)[n]) 1 y\<rbrakk>
                 \<Longrightarrow> (parent ((N::pairseq)[n]) 1 y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                       mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                     \<le> (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                       mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
    and valley: "\<And>N n y j. \<lbrakk>N \<in> ST_PS;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1));
                   parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y;
                   hasParent ((N::pairseq)[n]) 1 y;
                   idx1 N (Lng N - 1) = 1;
                   (if parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                              + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                                 mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                          < parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                       then parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                              + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                                 mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                       else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                              + ((y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                                 div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                                * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                              + (parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                                    + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                                       mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                                 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                        < j;
                   le0 ((N::pairseq)[n]) j y\<rbrakk>
                   \<Longrightarrow> entry ((N::pairseq)[n]) 1 y \<le> entry ((N::pairseq)[n]) 1 j"
  shows "ST_PS \<subseteq> RT_PS"
proof -
  have hpN: "\<And>N n y. \<lbrakk>N \<in> ST_PS;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1));
                   parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y;
                   hasParent ((N::pairseq)[n]) 1 y;
                   idx1 N (Lng N - 1) = 1\<rbrakk>
                 \<Longrightarrow> hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                        + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                           mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
  proof -
    fix N n y
    assume Nst: "N \<in> ST_PS"
      and tile: "\<not> (Lng N - 1 = 0
                    \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                    \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1))"
      and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y"
      and hpny: "hasParent ((N::pairseq)[n]) 1 y"
      and i1z: "idx1 N (Lng N - 1) = 1"
    have L: "1 < Lng N" using tile by (cases "Lng N - 1 = 0") auto
    have notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
      using tile by blast
    have hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)" using tile by blast
    have parR: "nextR N (idx1 N (Lng N - 1)) (parent N (idx1 N (Lng N - 1)) (Lng N - 1)) (Lng N - 1)"
      using hp unfolding hasParent_def parent_def by (rule theI')
    have j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
      using poper_nextR_imp_le0[OF parR] by simp
    \<comment> \<open>\<open>n \<ge> 1\<close> is forced by \<open>y\<close>'s existence in \<open>N[n]\<close>\<close>
    have nrely: "nextrel1 ((N::pairseq)[n]) (parent ((N::pairseq)[n]) 1 y) y"
    proof -
      have "\<exists>!a. nextR ((N::pairseq)[n]) 1 a y" using hpny unfolding hasParent_def by simp
      hence "nextR ((N::pairseq)[n]) 1 (parent ((N::pairseq)[n]) 1 y) y"
        unfolding parent_def by (rule theI')
      thus ?thesis by (simp add: nextR_def)
    qed
    from nrely have yNn: "y < Lng ((N::pairseq)[n])" by (simp add: nextrel1_def)
    have lenNn: "Lng ((N::pairseq)[n]) = parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                   + n * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
      by (rule operB_gen_LngM[OF L notzero hp j0lt])
    have nw0: "0 < n * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
      using ge yNn lenNn by linarith
    have n1: "1 \<le> n" using nw0 by (cases n) auto
    show "hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
            + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
               mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
      by (rule operCA_tiling_hpN_via_owithin[OF L notzero hp i1z j0lt n1 ge hpny
            spsy[OF Nst tile ge hpny i1z] owithin[OF Nst tile i1z]])
  qed
  show ?thesis by (rule m_6_7_standard_reduced_hpN_valley[OF hpN valley])
qed


text \<open>§6.5 \<open>stdCA\<close> residual \<open>M \<in> ST_PS \<Longrightarrow> RedCondA M\<close> conditional on the same
  Front-A offset residuals \<open>owithin\<close>/\<open>spsy\<close> + \<open>valley\<close> only, mirroring
  @{thm [source] m_6_7_standard_reduced_via_owithin_valleyA} into
  @{thm [source] m_6_5_ST_PS_imp_RedCondA_hpN_valley}.\<close>

lemma m_6_5_ST_PS_imp_RedCondA_via_owithin_valleyA:
  assumes owithin: "\<And>N n q sp sx. \<lbrakk>N \<in> ST_PS;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1));
                   idx1 N (Lng N - 1) = 1;
                   sp \<le> sx;
                   sx < Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1);
                   q < n\<rbrakk>
                 \<Longrightarrow> le0 ((N::pairseq)[n])
                        (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                           + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)) + sp)
                        (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                           + q * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)) + sx)"
    and spsy: "\<And>N n y. \<lbrakk>N \<in> ST_PS;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1));
                   parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y;
                   hasParent ((N::pairseq)[n]) 1 y;
                   idx1 N (Lng N - 1) = 1;
                   parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> parent ((N::pairseq)[n]) 1 y\<rbrakk>
                 \<Longrightarrow> (parent ((N::pairseq)[n]) 1 y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                       mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                     \<le> (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                       mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
    and valley: "\<And>N n y j. \<lbrakk>N \<in> ST_PS;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1));
                   parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y;
                   hasParent ((N::pairseq)[n]) 1 y;
                   idx1 N (Lng N - 1) = 1;
                   (if parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                              + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                                 mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                          < parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                       then parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                              + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                                 mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                       else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                              + ((y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                                 div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                                * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                              + (parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                                    + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                                       mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                                 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                        < j;
                   le0 ((N::pairseq)[n]) j y\<rbrakk>
                   \<Longrightarrow> entry ((N::pairseq)[n]) 1 y \<le> entry ((N::pairseq)[n]) 1 j"
    and M: "M \<in> ST_PS"
  shows "RedCondA M"
proof -
  have hpN: "\<And>N n y. \<lbrakk>N \<in> ST_PS;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1));
                   parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y;
                   hasParent ((N::pairseq)[n]) 1 y;
                   idx1 N (Lng N - 1) = 1\<rbrakk>
                 \<Longrightarrow> hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                        + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                           mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
  proof -
    fix N n y
    assume Nst: "N \<in> ST_PS"
      and tile: "\<not> (Lng N - 1 = 0
                    \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                    \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1))"
      and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y"
      and hpny: "hasParent ((N::pairseq)[n]) 1 y"
      and i1z: "idx1 N (Lng N - 1) = 1"
    have L: "1 < Lng N" using tile by (cases "Lng N - 1 = 0") auto
    have notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
      using tile by blast
    have hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)" using tile by blast
    have parR: "nextR N (idx1 N (Lng N - 1)) (parent N (idx1 N (Lng N - 1)) (Lng N - 1)) (Lng N - 1)"
      using hp unfolding hasParent_def parent_def by (rule theI')
    have j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
      using poper_nextR_imp_le0[OF parR] by simp
    have nrely: "nextrel1 ((N::pairseq)[n]) (parent ((N::pairseq)[n]) 1 y) y"
    proof -
      have "\<exists>!a. nextR ((N::pairseq)[n]) 1 a y" using hpny unfolding hasParent_def by simp
      hence "nextR ((N::pairseq)[n]) 1 (parent ((N::pairseq)[n]) 1 y) y"
        unfolding parent_def by (rule theI')
      thus ?thesis by (simp add: nextR_def)
    qed
    from nrely have yNn: "y < Lng ((N::pairseq)[n])" by (simp add: nextrel1_def)
    have lenNn: "Lng ((N::pairseq)[n]) = parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                   + n * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
      by (rule operB_gen_LngM[OF L notzero hp j0lt])
    have nw0: "0 < n * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
      using ge yNn lenNn by linarith
    have n1: "1 \<le> n" using nw0 by (cases n) auto
    show "hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
            + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
               mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
      by (rule operCA_tiling_hpN_via_owithin[OF L notzero hp i1z j0lt n1 ge hpny
            spsy[OF Nst tile ge hpny i1z] owithin[OF Nst tile i1z]])
  qed
  show ?thesis by (rule m_6_5_ST_PS_imp_RedCondA_hpN_valley[OF hpN valley M])
qed


text \<open>§6.7 hpN SAME-BLOCK residual \<open>sblk\<close> (Front B, \<open>i\<^sub>1=1\<close>) UNCONDITIONAL on
  \<open>owithin\<close>: the argmin coincidence \<open>q\<^sub>p = q\<^sub>y\<close> proven from \<open>spsy\<close> only.  Replaces
  the abstract \<open>owithin\<close> hypothesis of @{thm [source] operCA_tiling_sblk_via_owithin}
  by an IN-PLACE construction of the contradiction witness \<open>le0 (N[n]) c\<^sub>0 y\<close>:
  in the \<open>q\<^sub>p < q\<^sub>y\<close> ccontr branch the BASE path \<open>le0 N (j\<^sub>0+s\<^sub>p) (j\<^sub>0+s\<^sub>y)\<close> (\<open>s\<^sub>p \<le> s\<^sub>y\<close>)
  is reflected out of \<open>le0 (N[n]) p y\<close> by the period backward reflection
  @{thm [source] oper_d1pos_ctx_period_le0Np} (cross/same-block, \<open>q\<^sub>p \<le> q\<^sub>y\<close> span),
  then lifted into block \<open>q\<^sub>y\<close> by the GREEN offset-within brick
  @{thm [source] oper_d1pos_le0_offset_within} — yielding \<open>le0 (N[n]) c\<^sub>0 y\<close> with
  \<open>c\<^sub>0 = j\<^sub>0 + q\<^sub>y\<cdot>w + s\<^sub>p\<close>, which violates the parent valley clause (\<open>c\<^sub>0 > p\<close>,
  same row-1 reading as \<open>p\<close> by periodicity).  Conditional now ONLY on \<open>spsy\<close>.\<close>

lemma operCA_tiling_sblk_via_spsy:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y"
    and hpny: "hasParent ((N::pairseq)[n]) 1 y"
    and pge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> parent ((N::pairseq)[n]) 1 y"
    and spsy: "(parent ((N::pairseq)[n]) 1 y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                  mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
               \<le> (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                  mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
  shows "(parent ((N::pairseq)[n]) 1 y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
           div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
         = (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
           div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?Nn = "(N::pairseq)[n]"
  let ?p = "parent ?Nn 1 y"
  let ?sy = "(y - ?j0) mod ?w"  let ?qy = "(y - ?j0) div ?w"
  let ?sp = "(?p - ?j0) mod ?w"  let ?qp = "(?p - ?j0) div ?w"
  let ?c0 = "?j0 + ?qy * ?w + ?sp"
  have j0eq1: "?j0 = parent N 1 ?j1" using i1z by simp
  have j0lt1: "parent N 1 ?j1 < ?j1" using j0lt j0eq1 by simp
  have w0: "0 < ?w" using j0lt by linarith
  have j0w1: "?j0 + ?w = ?j1" using j0lt by simp
  have lenNn: "Lng ?Nn = ?j0 + n * ?w"
    by (rule operB_gen_LngM[OF L notzero hp j0lt])
  \<comment> \<open>parent edge of \<open>y\<close>\<close>
  have nrely: "nextrel1 ?Nn ?p y"
  proof -
    have "\<exists>!a. nextR ?Nn 1 a y" using hpny unfolding hasParent_def by simp
    hence "nextR ?Nn 1 ?p y" unfolding parent_def by (rule theI')
    thus ?thesis by (simp add: nextR_def)
  qed
  from nrely have py: "?p < y" and yNn: "y < Lng ?Nn"
    and e1py: "entry ?Nn 1 ?p < entry ?Nn 1 y"
    and le0py: "le0 ?Nn ?p y"
    and valley: "\<forall>x. ?p < x \<and> le0 ?Nn x y \<longrightarrow> entry ?Nn 1 x \<ge> entry ?Nn 1 y"
    by (auto simp: nextrel1_def)
  \<comment> \<open>decode \<open>p\<close>, \<open>y\<close>\<close>
  have syw: "?sy < ?w" using w0 by simp
  have spw: "?sp < ?w" using w0 by simp
  have ymj: "y - ?j0 < n * ?w" using yNn lenNn ge by linarith
  have qyn: "?qy < n" using less_mult_imp_div_less[OF ymj] .
  have psplit: "?p = ?j0 + ?qp * ?w + ?sp"
  proof -
    have "?qp * ?w + ?sp = ?p - ?j0"
      using div_mult_mod_eq[of "?p - ?j0" ?w] by (simp add: mult.commute)
    thus ?thesis using pge by linarith
  qed
  have ysplit: "y = ?j0 + ?qy * ?w + ?sy"
  proof -
    have "?qy * ?w + ?sy = y - ?j0"
      using div_mult_mod_eq[of "y - ?j0" ?w] by (simp add: mult.commute)
    thus ?thesis using ge by linarith
  qed
  \<comment> \<open>\<open>q\<^sub>p \<le> q\<^sub>y\<close> for free from \<open>p < y\<close>\<close>
  have pmj: "?p - ?j0 \<le> y - ?j0" using py pge by linarith
  have qpqy: "?qp \<le> ?qy" using div_le_mono[OF pmj] .
  \<comment> \<open>\<open>s\<^sub>p \<le> s\<^sub>y\<close> from the supplied offset-monotonicity\<close>
  have spsy': "?sp \<le> ?sy" using spsy by simp
  show ?thesis
  proof (rule ccontr)
    assume "?qp \<noteq> ?qy"
    hence qplt: "?qp < ?qy" using qpqy by linarith
    \<comment> \<open>the same-offset witness \<open>c\<^sub>0 = j\<^sub>0 + q\<^sub>y\<cdot>w + s\<^sub>p\<close> sits strictly past \<open>p\<close>\<close>
    have pc0: "?p < ?c0"
    proof -
      have "?p = ?j0 + ?qp * ?w + ?sp" using psplit .
      also have "\<dots> < ?j0 + ?qy * ?w + ?sp"
        using qplt w0 by simp
      finally show ?thesis .
    qed
    \<comment> \<open>BASE path \<open>le0 N (j\<^sub>0+s\<^sub>p) (j\<^sub>0+s\<^sub>y)\<close> reflected out of \<open>le0 (N[n]) p y\<close>\<close>
    have basepath: "(nextrel0 N)\<^sup>*\<^sup>* (?j0 + ?sp) (?j0 + ?sy)"
    proof (cases "?sp = ?sy")
      case True
      have "?j0 + ?sp < Lng N" using spw L j0lt by linarith
      thus ?thesis using True by simp
    next
      case False
      hence spsylt: "?sp < ?sy" using spsy' by linarith
      \<comment> \<open>instantiate the period backward reflection at \<open>p\<close>'s block-\<open>q\<^sub>p\<close>, offset \<open>s\<^sub>p\<close>\<close>
      have qpn: "?qp < n" using qpqy qyn by linarith
      have s0lt: "?sp < Lng N - 1 - parent N 1 ?j1" using spw j0eq1 by simp
      have j0reds: "?j0 + ?sp = parent N 1 ?j1 + ?sp" using j0eq1 by simp
      have j0'eq: "?p = parent N 1 ?j1
                     + ?qp * (Lng N - 1 - parent N 1 ?j1) + ?sp"
        using psplit j0eq1 by simp
      have shamteq: "?qp * (entry N 0 ?j1 - entry N 0 (parent N 1 ?j1))
                       = ?qp * (entry N 0 ?j1 - entry N 0 (parent N 1 ?j1))" by simp
      have j1redle: "?j0 + ?sy \<le> ?j1" using syw j0w1 by linarith
      have j0j1red: "?j0 + ?sp < ?j0 + ?sy" using spsylt by simp
      have j1redspan: "?j0 + ?sy \<le> (?j0 + ?sp) + (y - ?p)"
      proof -
        have qpw: "?qp * ?w \<le> ?qy * ?w" using qpqy by (rule mult_le_mono1)
        have ypeq: "y - ?p = (?qy * ?w - ?qp * ?w) + (?sy - ?sp)"
        proof -
          have "y - ?p = (?j0 + ?qy * ?w + ?sy) - (?j0 + ?qp * ?w + ?sp)"
            using ysplit psplit by simp
          also have "\<dots> = (?qy * ?w + ?sy) - (?qp * ?w + ?sp)" by simp
          also have "\<dots> = (?qy * ?w - ?qp * ?w) + (?sy - ?sp)"
            using qpw spsy' by simp
          finally show ?thesis .
        qed
        have "(?j0 + ?sp) + (y - ?p)
                = (?j0 + ?sp) + ((?qy * ?w - ?qp * ?w) + (?sy - ?sp))"
          using ypeq by simp
        also have "\<dots> = ?j0 + ?sy + (?qy * ?w - ?qp * ?w)"
          using spsy' by simp
        finally show ?thesis by linarith
      qed
      have le0base: "le0 N (?j0 + ?sp) (?j0 + ?sy)"
        by (rule oper_d1pos_ctx_period_le0Np[OF L notzero hp i1z j0lt1 refl le0py py yNn
              qpn s0lt j0reds j0'eq shamteq j1redle j0j1red j1redspan])
      thus ?thesis by (simp add: le0_def)
    qed
    \<comment> \<open>lift the base path into block \<open>q\<^sub>y\<close>: \<open>le0 (N[n]) c\<^sub>0 (j\<^sub>0+q\<^sub>y\<cdot>w+s\<^sub>y)\<close>\<close>
    have reachc0: "le0 ?Nn (?j0 + ?qy * ?w + ?sp) (?j0 + ?qy * ?w + ?sy)"
      by (rule oper_d1pos_le0_offset_within[OF L notzero hp j0lt qyn syw basepath])
    have reachc0': "le0 ?Nn ?c0 y" using reachc0 ysplit by simp
    \<comment> \<open>periodicity: \<open>c\<^sub>0\<close> and \<open>p\<close> have the same row-1 reading \<open>entry N 1 (j\<^sub>0 + s\<^sub>p)\<close>\<close>
    have c0Nn: "?c0 < Lng ?Nn" using reachc0' by (simp add: le0_def)
    have base_c0: "(if ?c0 < ?j0 then ?c0 else ?j0 + (?c0 - ?j0) mod ?w) = ?j0 + ?sp"
    proof -
      have nge: "\<not> ?c0 < ?j0" by simp
      have "(?c0 - ?j0) mod ?w = ?sp"
      proof -
        have "?c0 - ?j0 = ?qy * ?w + ?sp" by simp
        thus ?thesis by simp
      qed
      thus ?thesis using nge by simp
    qed
    have e1c0: "entry ?Nn 1 ?c0 = entry N 1 (?j0 + ?sp)"
    proof -
      have "entry ?Nn 1 ?c0
              = entry N 1 (if ?c0 < ?j0 then ?c0 else ?j0 + (?c0 - ?j0) mod ?w)"
        by (rule operCA_tiling_entry1_base'[OF L notzero hp j0lt c0Nn])
      thus ?thesis using base_c0 by simp
    qed
    have pNn: "?p < Lng ?Nn" using py yNn by linarith
    have base_p: "(if ?p < ?j0 then ?p else ?j0 + (?p - ?j0) mod ?w) = ?j0 + ?sp"
      using pge by simp
    have e1p: "entry ?Nn 1 ?p = entry N 1 (?j0 + ?sp)"
    proof -
      have "entry ?Nn 1 ?p
              = entry N 1 (if ?p < ?j0 then ?p else ?j0 + (?p - ?j0) mod ?w)"
        by (rule operCA_tiling_entry1_base'[OF L notzero hp j0lt pNn])
      thus ?thesis using base_p by simp
    qed
    have e1eq: "entry ?Nn 1 ?c0 = entry ?Nn 1 ?p" using e1c0 e1p by simp
    \<comment> \<open>\<open>c\<^sub>0\<close> beats the strict-decrease but obeys the valley: contradiction\<close>
    have lt: "entry ?Nn 1 ?c0 < entry ?Nn 1 y" using e1eq e1py by simp
    have ge': "entry ?Nn 1 y \<le> entry ?Nn 1 ?c0" using valley pc0 reachc0' by blast
    show False using lt ge' by simp
  qed
qed


text \<open>§6.7 hpN UNCONDITIONAL on \<open>owithin\<close> (Front B, \<open>i\<^sub>1=1\<close>): the period-base
  row-1 parent existence \<open>hasParent N 1 (base y)\<close>, with the same-block residual
  \<open>sblk\<close> discharged by @{thm [source] operCA_tiling_sblk_via_spsy} (the GREEN
  offset-within brick replaces the old abstract \<open>owithin\<close> hypothesis).  Conditional
  now ONLY on the single Front-A offset residual \<open>spsy\<close> (\<open>s\<^sub>p \<le> s\<^sub>y\<close>).\<close>

lemma operCA_tiling_hpN_via_spsy:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and n1: "1 \<le> n"
    and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y"
    and hpny: "hasParent ((N::pairseq)[n]) 1 y"
    and spsy: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> parent ((N::pairseq)[n]) 1 y
               \<Longrightarrow> (parent ((N::pairseq)[n]) 1 y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                     mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                   \<le> (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                     mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
  shows "hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                   mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
proof -
  have sblk: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> parent ((N::pairseq)[n]) 1 y
               \<Longrightarrow> (parent ((N::pairseq)[n]) 1 y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                     div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                   = (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                     div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
  proof -
    assume pge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> parent ((N::pairseq)[n]) 1 y"
    show "(parent ((N::pairseq)[n]) 1 y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
            div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
          = (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
            div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
      by (rule operCA_tiling_sblk_via_spsy[OF L notzero hp i1z j0lt ge hpny pge spsy[OF pge]])
  qed
  show ?thesis
    by (rule operCA_tiling_hpN_via_sblk[OF L notzero hp i1z j0lt n1 ge hpny sblk])
qed


text \<open>§6.7/§6.5 FINAL DISCHARGE conditional on \<open>spsy\<close> + \<open>valley\<close> only.  Instantiates
  the \<open>owithin\<close> meta-assumption of @{thm [source] m_6_7_standard_reduced_via_owithin_valleyA}
  with the GREEN offset-within brick (folded inside @{thm [source] operCA_tiling_hpN_via_spsy}),
  so the only remaining hypotheses are the offset monotonicity \<open>spsy\<close> and the
  per-competitor row-1 minimality \<open>valley\<close>.\<close>

lemma m_6_7_standard_reduced_via_spsy_valley:
  assumes spsy: "\<And>N n y. \<lbrakk>N \<in> ST_PS;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1));
                   parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y;
                   hasParent ((N::pairseq)[n]) 1 y;
                   idx1 N (Lng N - 1) = 1;
                   parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> parent ((N::pairseq)[n]) 1 y\<rbrakk>
                 \<Longrightarrow> (parent ((N::pairseq)[n]) 1 y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                       mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                     \<le> (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                       mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
    and valley: "\<And>N n y j. \<lbrakk>N \<in> ST_PS;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1));
                   parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y;
                   hasParent ((N::pairseq)[n]) 1 y;
                   idx1 N (Lng N - 1) = 1;
                   (if parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                              + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                                 mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                          < parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                       then parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                              + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                                 mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                       else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                              + ((y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                                 div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                                * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                              + (parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                                    + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                                       mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                                 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                        < j;
                   le0 ((N::pairseq)[n]) j y\<rbrakk>
                   \<Longrightarrow> entry ((N::pairseq)[n]) 1 y \<le> entry ((N::pairseq)[n]) 1 j"
  shows "ST_PS \<subseteq> RT_PS"
proof -
  have hpN: "\<And>N n y. \<lbrakk>N \<in> ST_PS;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1));
                   parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y;
                   hasParent ((N::pairseq)[n]) 1 y;
                   idx1 N (Lng N - 1) = 1\<rbrakk>
                 \<Longrightarrow> hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                        + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                           mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
  proof -
    fix N n y
    assume Nst: "N \<in> ST_PS"
      and tile: "\<not> (Lng N - 1 = 0
                    \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                    \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1))"
      and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y"
      and hpny: "hasParent ((N::pairseq)[n]) 1 y"
      and i1z: "idx1 N (Lng N - 1) = 1"
    have L: "1 < Lng N" using tile by (cases "Lng N - 1 = 0") auto
    have notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
      using tile by blast
    have hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)" using tile by blast
    have parR: "nextR N (idx1 N (Lng N - 1)) (parent N (idx1 N (Lng N - 1)) (Lng N - 1)) (Lng N - 1)"
      using hp unfolding hasParent_def parent_def by (rule theI')
    have j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
      using poper_nextR_imp_le0[OF parR] by simp
    have nrely: "nextrel1 ((N::pairseq)[n]) (parent ((N::pairseq)[n]) 1 y) y"
    proof -
      have "\<exists>!a. nextR ((N::pairseq)[n]) 1 a y" using hpny unfolding hasParent_def by simp
      hence "nextR ((N::pairseq)[n]) 1 (parent ((N::pairseq)[n]) 1 y) y"
        unfolding parent_def by (rule theI')
      thus ?thesis by (simp add: nextR_def)
    qed
    from nrely have yNn: "y < Lng ((N::pairseq)[n])" by (simp add: nextrel1_def)
    have lenNn: "Lng ((N::pairseq)[n]) = parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                   + n * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
      by (rule operB_gen_LngM[OF L notzero hp j0lt])
    have nw0: "0 < n * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
      using ge yNn lenNn by linarith
    have n1: "1 \<le> n" using nw0 by (cases n) auto
    show "hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
            + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
               mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
      by (rule operCA_tiling_hpN_via_spsy[OF L notzero hp i1z j0lt n1 ge hpny
            spsy[OF Nst tile ge hpny i1z]])
  qed
  show ?thesis by (rule m_6_7_standard_reduced_hpN_valley[OF hpN valley])
qed


text \<open>§6.5 \<open>stdCA\<close> residual \<open>M \<in> ST_PS \<Longrightarrow> RedCondA M\<close> conditional on \<open>spsy\<close> + \<open>valley\<close>
  only, mirroring @{thm [source] m_6_7_standard_reduced_via_spsy_valley} into
  @{thm [source] m_6_5_ST_PS_imp_RedCondA_hpN_valley}.\<close>

lemma m_6_5_ST_PS_imp_RedCondA_via_spsy_valley:
  assumes spsy: "\<And>N n y. \<lbrakk>N \<in> ST_PS;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1));
                   parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y;
                   hasParent ((N::pairseq)[n]) 1 y;
                   idx1 N (Lng N - 1) = 1;
                   parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> parent ((N::pairseq)[n]) 1 y\<rbrakk>
                 \<Longrightarrow> (parent ((N::pairseq)[n]) 1 y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                       mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                     \<le> (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                       mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
    and valley: "\<And>N n y j. \<lbrakk>N \<in> ST_PS;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1));
                   parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y;
                   hasParent ((N::pairseq)[n]) 1 y;
                   idx1 N (Lng N - 1) = 1;
                   (if parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                              + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                                 mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                          < parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                       then parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                              + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                                 mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                       else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                              + ((y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                                 div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                                * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                              + (parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                                    + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                                       mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                                 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                        < j;
                   le0 ((N::pairseq)[n]) j y\<rbrakk>
                   \<Longrightarrow> entry ((N::pairseq)[n]) 1 y \<le> entry ((N::pairseq)[n]) 1 j"
    and M: "M \<in> ST_PS"
  shows "RedCondA M"
proof -
  have hpN: "\<And>N n y. \<lbrakk>N \<in> ST_PS;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1));
                   parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y;
                   hasParent ((N::pairseq)[n]) 1 y;
                   idx1 N (Lng N - 1) = 1\<rbrakk>
                 \<Longrightarrow> hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                        + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                           mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
  proof -
    fix N n y
    assume Nst: "N \<in> ST_PS"
      and tile: "\<not> (Lng N - 1 = 0
                    \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                    \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1))"
      and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y"
      and hpny: "hasParent ((N::pairseq)[n]) 1 y"
      and i1z: "idx1 N (Lng N - 1) = 1"
    have L: "1 < Lng N" using tile by (cases "Lng N - 1 = 0") auto
    have notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
      using tile by blast
    have hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)" using tile by blast
    have parR: "nextR N (idx1 N (Lng N - 1)) (parent N (idx1 N (Lng N - 1)) (Lng N - 1)) (Lng N - 1)"
      using hp unfolding hasParent_def parent_def by (rule theI')
    have j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
      using poper_nextR_imp_le0[OF parR] by simp
    have nrely: "nextrel1 ((N::pairseq)[n]) (parent ((N::pairseq)[n]) 1 y) y"
    proof -
      have "\<exists>!a. nextR ((N::pairseq)[n]) 1 a y" using hpny unfolding hasParent_def by simp
      hence "nextR ((N::pairseq)[n]) 1 (parent ((N::pairseq)[n]) 1 y) y"
        unfolding parent_def by (rule theI')
      thus ?thesis by (simp add: nextR_def)
    qed
    from nrely have yNn: "y < Lng ((N::pairseq)[n])" by (simp add: nextrel1_def)
    have lenNn: "Lng ((N::pairseq)[n]) = parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                   + n * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
      by (rule operB_gen_LngM[OF L notzero hp j0lt])
    have nw0: "0 < n * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
      using ge yNn lenNn by linarith
    have n1: "1 \<le> n" using nw0 by (cases n) auto
    show "hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
            + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
               mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
      by (rule operCA_tiling_hpN_via_spsy[OF L notzero hp i1z j0lt n1 ge hpny
            spsy[OF Nst tile ge hpny i1z]])
  qed
  show ?thesis by (rule m_6_5_ST_PS_imp_RedCondA_hpN_valley[OF hpN valley M])
qed

end
