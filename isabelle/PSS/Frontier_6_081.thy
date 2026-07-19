theory Frontier_6_081
  imports Support_6_060
begin

text \<open>§6.7 spsy keystone — STRICT-at-blockstart branch (non-circular core).
  Front B.  Under the spsy domain with \<open>p \<ge> j\<^sub>0\<close>, if the block-start \<open>bs = j\<^sub>0 + q\<^sub>y\<cdot>w\<close>
  of \<open>y\<close>'s tiling block has strictly smaller row-1 entry than \<open>y\<close> (the generic case,
  18945/19020 empirically), then \<open>bs\<close> is a strict row-0 ancestor of \<open>y\<close> inside \<open>N[n]\<close>
  (lifted from the always-true base path \<open>j\<^sub>0 \<rightarrow>\<^sup>* base y\<close> by @{thm [source]
  oper_d1pos_le0_within}); applying @{thm [source] m_5_1_parent_exists_2} INSIDE \<open>N[n]\<close>
  rooted at \<open>bs\<close> yields a row-1 parent of \<open>y\<close> in \<open>[bs, y)\<close>, which by
  @{thm [source] nextR1_unique} is \<open>p\<close> itself, forcing \<open>p \<ge> bs\<close>, i.e. \<open>q\<^sub>p = q\<^sub>y\<close>, whence
  \<open>s\<^sub>p < s\<^sub>y\<close>.  This branch needs NO base reflection \<open>le0 N (j\<^sub>0+s\<^sub>p) (base y)\<close> and is
  therefore free of the spsy/sblk circularity.\<close>

lemma spsy_keystone_strict_blockstart:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y"
    and hpny: "hasParent ((N::pairseq)[n]) 1 y"
    and pge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> parent ((N::pairseq)[n]) 1 y"
    and strict: "entry ((N::pairseq)[n]) 1
                   (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                    + ((y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                        div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                      * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                 < entry ((N::pairseq)[n]) 1 y"
  shows "(parent ((N::pairseq)[n]) 1 y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
            mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
        \<le> (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
            mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?Nn = "(N::pairseq)[n]"
  let ?p = "parent ?Nn 1 y"
  let ?sy = "(y - ?j0) mod ?w"  let ?qy = "(y - ?j0) div ?w"
  let ?sp = "(?p - ?j0) mod ?w"  let ?qp = "(?p - ?j0) div ?w"
  let ?bs = "?j0 + ?qy * ?w"
  have j0eq1: "?j0 = parent N 1 ?j1" using i1z by simp
  have w0: "0 < ?w" using j0lt by linarith
  have j0w1: "?j0 + ?w = ?j1" using j0lt by simp
  have NT: "N \<in> T_PS" using L by (cases N) (auto simp: T_PS_def)
  have lenNn: "Lng ?Nn = ?j0 + n * ?w"
    by (rule operB_gen_LngM[OF L notzero hp j0lt])
  have nrely: "nextrel1 ?Nn ?p y"
  proof -
    have "\<exists>!a. nextR ?Nn 1 a y" using hpny unfolding hasParent_def by simp
    hence "nextR ?Nn 1 ?p y" unfolding parent_def by (rule theI')
    thus ?thesis by (simp add: nextR_def)
  qed
  from nrely have py: "?p < y" and yNn: "y < Lng ?Nn" and le0py: "le0 ?Nn ?p y"
    by (auto simp: nextrel1_def)
  have syw: "?sy < ?w" using w0 by simp
  have ymj: "y - ?j0 < n * ?w" using yNn lenNn ge by linarith
  have qyn: "?qy < n" using less_mult_imp_div_less[OF ymj] .
  have ysplit: "y = ?bs + ?sy"
  proof -
    have a: "?qy * ?w + ?sy = y - ?j0"
      using div_mult_mod_eq[of "y - ?j0" ?w] by (simp add: mult.commute)
    have "?bs + ?sy = ?j0 + (?qy * ?w + ?sy)" by simp
    also have "\<dots> = ?j0 + (y - ?j0)" using a by simp
    also have "\<dots> = y" using ge by simp
    finally show ?thesis by simp
  qed
  have pmj: "?p - ?j0 \<le> y - ?j0" using py pge by linarith
  have qpqy: "?qp \<le> ?qy" using div_le_mono[OF pmj] .
  have j0lt1: "parent N 1 ?j1 < ?j1" using j0lt j0eq1 by simp
  have NnT: "?Nn \<in> T_PS" using yNn unfolding T_PS_def by (cases ?Nn) auto
  have syw': "?sy < Lng N - 1 - parent N 1 ?j1" using syw j0eq1 by simp
  have le0bsy: "le0 ?Nn ?bs y"
  proof -
    have "le0 ?Nn (parent N 1 ?j1 + ?qy * (Lng N - 1 - parent N 1 ?j1))
                  (parent N 1 ?j1 + ?qy * (Lng N - 1 - parent N 1 ?j1) + ?sy)"
      by (rule oper_d1pos_le0_within[OF NT L notzero hp i1z j0lt1 qyn syw'])
    thus ?thesis using ysplit j0eq1 by simp
  qed
  have bsley: "?bs \<le> y"
  proof -
    have "(nextrel0 ?Nn)\<^sup>*\<^sup>* ?bs y" using le0bsy by (simp add: le0_def)
    thus ?thesis by (rule nextrel0_rtrancl_mono)
  qed
  have bsneq: "?bs \<noteq> y" using strict by force
  have bsy: "?bs < y" using bsley bsneq by linarith
  have leR0: "leR ?Nn 0 ?bs y" using le0bsy by (simp add: leR_def)
  obtain j' where bsj': "?bs \<le> j'" and j'y: "j' < y" and j'par: "nextR ?Nn 1 j' y"
    using m_5_1_parent_exists_2[OF NnT bsy yNn strict leR0] by blast
  have pj'eq: "?p = j'"
  proof -
    have "nextR ?Nn 1 ?p y" using nrely by (simp add: nextR_def)
    thus ?thesis using j'par by (rule nextR1_unique)
  qed
  have pbs: "?bs \<le> ?p" using bsj' pj'eq by simp
  have qpge: "?qy \<le> ?qp"
  proof -
    have "?j0 + ?qy * ?w \<le> ?p" using pbs by simp
    hence "?qy * ?w \<le> ?p - ?j0" using pge by linarith
    hence "(?qy * ?w) div ?w \<le> (?p - ?j0) div ?w" by (rule div_le_mono)
    thus ?thesis using w0 by simp
  qed
  have qpeq: "?qp = ?qy" using qpqy qpge by linarith
  have psplit: "?p = ?bs + ?sp"
  proof -
    have a: "?qp * ?w + ?sp = ?p - ?j0"
      using div_mult_mod_eq[of "?p - ?j0" ?w] by (simp add: mult.commute)
    have "?bs + ?sp = ?j0 + (?qp * ?w + ?sp)" using qpeq by simp
    also have "\<dots> = ?j0 + (?p - ?j0)" using a by simp
    also have "\<dots> = ?p" using pge by simp
    finally show ?thesis by simp
  qed
  have spsy: "?sp < ?sy"
  proof -
    have "?bs + ?sp < ?bs + ?sy" using py psplit ysplit by simp
    thus ?thesis by simp
  qed
  show ?thesis using spsy by simp
qed


text \<open>6.7 spsy keystone -- CLEAN REDUCTION to the pure base-sequence fact Q.
  This isolates the single open crux of the whole 6.5/6.7 cascade.  Under the
  spsy arising domain (N tiling, i1=1, a real y with hasParent (N[n]) 1 y and
  j0 le p := parent (N[n]) 1 y), the FULL spsy mod-inequality
  (p-j0) mod w le (y-j0) mod w (w = Lng N-1-j0) follows from the single
  base-sequence fact Q:  w = 1  or  entry N 1 j0 < entry N 1 (j0 + (y-j0) mod w).
  The w = 1 branch is trivial (both sides mod 1 = 0).  For w > 1, Q's strict
  inequality is exactly the strict hypothesis of the GREEN
  spsy_keystone_strict_blockstart, AFTER moving it through the periodic row-1
  reading oper_d1pos_entry1: the block start bs = j0 + qy*w (offset 0) reads
  entry N 1 j0; y = bs + sy (offset sy) reads entry N 1 (j0 + sy).  So
  entry (N[n]) 1 bs < entry (N[n]) 1 y  iff  entry N 1 j0 < entry N 1 (j0+sy).
  CITES ONLY already-GREEN facts: oper_d1pos_entry1, operB_gen_LngM,
  spsy_keystone_strict_blockstart.  No via_spsy, no spsy goal, no
  RedCondA/RedCondB N, no p_ stub.\<close>

lemma spsy_keystone_via_Q:
  fixes N :: pairseq
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y"
    and hpny: "hasParent ((N::pairseq)[n]) 1 y"
    and pge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> parent ((N::pairseq)[n]) 1 y"
    and Q: "Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1) = 1
            \<or> entry N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                 < entry N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                      + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                          mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
  shows "(parent ((N::pairseq)[n]) 1 y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
            mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
        \<le> (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
            mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?Nn = "(N::pairseq)[n]"
  let ?p = "parent ?Nn 1 y"
  let ?sy = "(y - ?j0) mod ?w"  let ?qy = "(y - ?j0) div ?w"
  let ?bs = "?j0 + ?qy * ?w"
  have j0eq1: "?j0 = parent N 1 ?j1" using i1z by simp
  have j0lt1: "parent N 1 ?j1 < ?j1" using j0lt j0eq1 by simp
  show ?thesis
  proof (cases "?w = 1")
    case True
    \<comment> \<open>both residues are \<open>mod 1 = 0\<close>\<close>
    show ?thesis using True by simp
  next
    case False
    hence w0: "0 < ?w" and w1: "1 < ?w" using j0lt by linarith+
    \<comment> \<open>the arising structure decodes \<open>y\<close> inside block \<open>q\<^sub>y < n\<close>\<close>
    have lenNn: "Lng ?Nn = ?j0 + n * ?w"
      by (rule operB_gen_LngM[OF L notzero hp j0lt])
    have nrely: "nextrel1 ?Nn ?p y"
    proof -
      have "\<exists>!a. nextR ?Nn 1 a y" using hpny unfolding hasParent_def by simp
      hence "nextR ?Nn 1 ?p y" unfolding parent_def by (rule theI')
      thus ?thesis by (simp add: nextR_def)
    qed
    from nrely have yNn: "y < Lng ?Nn" by (simp add: nextrel1_def)
    have ymj: "y - ?j0 < n * ?w" using yNn lenNn ge by linarith
    have qyn: "?qy < n" using less_mult_imp_div_less[OF ymj] .
    have syw: "?sy < ?w" using w0 by simp
    have syw': "?sy < Lng N - 1 - parent N 1 ?j1" using syw j0eq1 by simp
    have zw': "(0::nat) < Lng N - 1 - parent N 1 ?j1" using w0 j0eq1 by simp
    have ysplit: "y = ?j0 + ?qy * ?w + ?sy"
    proof -
      have "?qy * ?w + ?sy = y - ?j0"
        using div_mult_mod_eq[of "y - ?j0" ?w] by (simp add: mult.commute)
      thus ?thesis using ge by linarith
    qed
    \<comment> \<open>the two periodic row-1 readings (offset \<open>0\<close> at \<open>bs\<close>, offset \<open>s\<^sub>y\<close> at \<open>y\<close>)\<close>
    have e1bs: "entry ?Nn 1 ?bs = entry N 1 ?j0"
    proof -
      have "entry ?Nn 1 (parent N 1 ?j1 + ?qy * (Lng N - 1 - parent N 1 ?j1) + 0)
              = entry N 1 (parent N 1 ?j1 + 0)"
        by (rule oper_d1pos_entry1[OF L notzero hp i1z j0lt1 qyn zw'])
      thus ?thesis using j0eq1 by simp
    qed
    have e1y: "entry ?Nn 1 y = entry N 1 (?j0 + ?sy)"
    proof -
      have "entry ?Nn 1 (parent N 1 ?j1 + ?qy * (Lng N - 1 - parent N 1 ?j1) + ?sy)
              = entry N 1 (parent N 1 ?j1 + ?sy)"
        by (rule oper_d1pos_entry1[OF L notzero hp i1z j0lt1 qyn syw'])
      thus ?thesis using ysplit j0eq1 by simp
    qed
    \<comment> \<open>move \<open>Q\<close> (with \<open>w>1\<close>) to the \<open>strict\<close> hypothesis of the GREEN keystone\<close>
    have Qstrict: "entry N 1 ?j0 < entry N 1 (?j0 + ?sy)"
      using Q w1 by linarith
    have strict: "entry ?Nn 1 ?bs < entry ?Nn 1 y"
      using e1bs e1y Qstrict by simp
    show ?thesis
      by (rule spsy_keystone_strict_blockstart[OF L notzero hp i1z j0lt ge hpny pge strict])
  qed
qed

end
