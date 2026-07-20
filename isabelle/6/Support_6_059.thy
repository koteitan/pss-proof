theory Support_6_059
  imports Frontier_6_079
begin

text \<open>§6.7 oper-tiling ROW-1 base-parent CORRESPONDENCE (Front B, \<open>i\<^sub>1=1\<close>), reduced
  to the two empirically-verified residuals \<open>le0pstar\<close> (piece W1(c)) and \<open>valley\<close>
  (piece W1(d)).  With the period base \<open>y' = base y\<close> having a row-1 parent in \<open>N\<close>
  (\<open>hpN\<close>), the lifted witness \<open>pstar = lift (parent N 1 y')\<close> is a row-1
  nearest-ancestor witness of \<open>y\<close> in \<open>N[n]\<close>; uniqueness @{thm [source] nextR1_unique}
  pins \<open>parent (N[n]) 1 y = pstar\<close>, whose base is exactly \<open>parent N 1 y'\<close>
  (empirically 1512/1512).  Pieces (a) \<open>pstar < y\<close> and (b) the strict row-1 increase
  are DERIVED here from \<open>hpN\<close>'s \<open>nextrel1 N (parent N 1 y') y'\<close> via the periodic
  row-1 reading @{thm [source] operCA_tiling_entry1_base'}.  This banks all of bcorr
  except the d1pos forward-lift (c, slice case via
  @{thm [source] oper_d0zero_le0_slice_lift}, prefix case via the cross argument) and
  the d1pos row-1 minimality (d).\<close>

lemma operCA_tiling_bcorr_reduced:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and n1: "1 \<le> n"
    and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y"
    and hpny: "hasParent ((N::pairseq)[n]) 1 y"
    and hpN: "hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                   mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
    and le0pstar: "le0 ((N::pairseq)[n])
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
                      y"
    and valley: "\<And>j. (if parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
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
                        < j
                   \<Longrightarrow> le0 ((N::pairseq)[n]) j y
                   \<Longrightarrow> entry ((N::pairseq)[n]) 1 y \<le> entry ((N::pairseq)[n]) 1 j"
  shows "hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                   mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
         \<and> entry N 1 (if parent ((N::pairseq)[n]) 1 y
                        < parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                      then parent ((N::pairseq)[n]) 1 y
                      else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                        + (parent ((N::pairseq)[n]) 1 y
                           - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                          mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
             = entry N 1 (parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                   mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))))"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?Nn = "(N::pairseq)[n]"
  let ?qy = "(y - ?j0) div ?w"  let ?sy = "(y - ?j0) mod ?w"
  let ?yp = "?j0 + ?sy"
  let ?pN = "parent N 1 ?yp"
  let ?pstar = "if ?pN < ?j0 then ?pN else ?j0 + ?qy * ?w + (?pN - ?j0)"
  let ?p = "parent ?Nn 1 y"
  let ?base = "\<lambda>z. if z < ?j0 then z else ?j0 + (z - ?j0) mod ?w"
  have w0: "0 < ?w" using j0lt by linarith
  have j0w1: "?j0 + ?w = ?j1" using j0lt by simp
  have lenNn: "Lng ?Nn = ?j0 + n * ?w"
    by (rule operB_gen_LngM[OF L notzero hp j0lt])
  \<comment> \<open>decode \<open>y\<close>\<close>
  have yge: "?j0 \<le> y" using ge by simp
  have nrely: "nextrel1 ?Nn ?p y"
  proof -
    have "\<exists>!a. nextR ?Nn 1 a y" using hpny unfolding hasParent_def by simp
    hence "nextR ?Nn 1 ?p y" unfolding parent_def by (rule theI')
    thus ?thesis by (simp add: nextR_def)
  qed
  from nrely have yNn: "y < Lng ?Nn" by (simp add: nextrel1_def)
  have syw: "?sy < ?w" using w0 by simp
  have ymj: "y - ?j0 < n * ?w" using yNn lenNn yge by linarith
  have qyn: "?qy < n" using less_mult_imp_div_less[OF ymj] .
  have ysplit: "y = ?j0 + ?qy * ?w + ?sy"
  proof -
    have "?qy * ?w + ?sy = y - ?j0"
      using div_mult_mod_eq[of "y - ?j0" ?w] by (simp add: mult.commute)
    thus ?thesis using yge by linarith
  qed
  have ypj1: "?yp < ?j1" using syw j0w1 by linarith
  have ypN: "?yp < Lng N" using ypj1 L by linarith
  \<comment> \<open>\<open>hpN\<close> on the period base \<open>y'\<close>: extract \<open>nextrel1 N pN y'\<close>\<close>
  have hpN': "hasParent N 1 ?yp" using hpN by simp
  have nrelN: "nextrel1 N ?pN ?yp"
  proof -
    have "\<exists>!a. nextR N 1 a ?yp" using hpN' unfolding hasParent_def by simp
    hence "nextR N 1 ?pN ?yp" unfolding parent_def by (rule theI')
    thus ?thesis by (simp add: nextR_def)
  qed
  from nrelN have pNlt: "?pN < ?yp" and pNN: "?pN < Lng N"
    and e1pNyp: "entry N 1 ?pN < entry N 1 ?yp"
    by (auto simp: nextrel1_def)
  have pNw: "?pN < ?j1" using pNlt ypj1 by linarith
  \<comment> \<open>base of pstar is \<open>pN\<close>\<close>
  have basepstar: "?base ?pstar = ?pN"
  proof (cases "?pN < ?j0")
    case True thus ?thesis by simp
  next
    case False
    hence pNge: "?j0 \<le> ?pN" by simp
    have pstar_eq: "?pstar = ?j0 + ?qy * ?w + (?pN - ?j0)" using False by simp
    have rw: "?pN - ?j0 < ?w" using pNw pNge j0w1 by linarith
    have pmj: "?pstar - ?j0 = ?qy * ?w + (?pN - ?j0)" using pstar_eq by simp
    have o: "(?pstar - ?j0) mod ?w = ?pN - ?j0"
      using pmj rw by simp
    have nlt: "\<not> ?pstar < ?j0" using pstar_eq by simp
    have "?base ?pstar = ?j0 + (?pN - ?j0)" using nlt o by simp
    thus ?thesis using pNge by simp
  qed
  \<comment> \<open>(a) \<open>pstar < y\<close>\<close>
  have pstar_y: "?pstar < y"
  proof (cases "?pN < ?j0")
    case True
    have "?pN < ?j0 + ?qy * ?w + ?sy" using True by linarith
    thus ?thesis using True ysplit by simp
  next
    case False
    hence pst: "?pstar = ?j0 + ?qy * ?w + (?pN - ?j0)" by simp
    have "?pN - ?j0 < ?yp - ?j0" using pNlt False by linarith
    hence "?pN - ?j0 < ?sy" by simp
    thus ?thesis using ysplit pst by linarith
  qed
  \<comment> \<open>(b) row-1 readings\<close>
  have e1y: "entry ?Nn 1 y = entry N 1 ?yp"
  proof -
    have nge: "\<not> y < ?j0" using ge by simp
    have "entry ?Nn 1 y = entry N 1 (if y < ?j0 then y else ?j0 + (y - ?j0) mod ?w)"
      by (rule operCA_tiling_entry1_base'[OF L notzero hp j0lt yNn])
    thus ?thesis using nge by simp
  qed
  have pstarNn: "?pstar < Lng ?Nn"
  proof (cases "?pN < ?j0")
    case True thus ?thesis using lenNn w0 n1 j0lt by simp
  next
    case False
    have "?pstar = ?j0 + ?qy * ?w + (?pN - ?j0)" using False by simp
    also have "\<dots> < ?j0 + ?qy * ?w + ?w" using pNw False j0w1 by linarith
    also have "\<dots> = ?j0 + (?qy + 1) * ?w" by simp
    also have "\<dots> \<le> ?j0 + n * ?w" using mult_le_mono1[of "?qy+1" n ?w] qyn by simp
    finally show ?thesis using lenNn by simp
  qed
  have e1pstar: "entry ?Nn 1 ?pstar = entry N 1 ?pN"
  proof -
    have "entry ?Nn 1 ?pstar = entry N 1 (?base ?pstar)"
      by (rule operCA_tiling_entry1_base'[OF L notzero hp j0lt pstarNn])
    thus ?thesis using basepstar by simp
  qed
  have e1lt: "entry ?Nn 1 ?pstar < entry ?Nn 1 y"
    using e1pstar e1y e1pNyp by simp
  \<comment> \<open>(c) le0 from hypothesis \<open>le0pstar\<close> (rewritten to the \<open>?pstar\<close> form)\<close>
  have le0ps: "le0 ?Nn ?pstar y"
  proof (cases "?pN < ?j0")
    case True thus ?thesis using le0pstar by simp
  next
    case False thus ?thesis using le0pstar by simp
  qed
  \<comment> \<open>assemble \<open>nextrel1 (N[n]) pstar y\<close>\<close>
  have nrelps: "nextrel1 ?Nn ?pstar y"
    unfolding nextrel1_def
  proof (intro conjI)
    show "?pstar < Lng ?Nn" by (rule pstarNn)
    show "y < Lng ?Nn" by (rule yNn)
    show "?pstar < y" by (rule pstar_y)
    show "entry ?Nn 1 ?pstar < entry ?Nn 1 y" by (rule e1lt)
    show "le0 ?Nn ?pstar y" by (rule le0ps)
    show "\<forall>j. ?pstar < j \<and> le0 ?Nn j y \<longrightarrow> entry ?Nn 1 y \<le> entry ?Nn 1 j"
    proof (intro allI impI)
      fix j assume "?pstar < j \<and> le0 ?Nn j y"
      thus "entry ?Nn 1 y \<le> entry ?Nn 1 j" using valley by blast
    qed
  qed
  \<comment> \<open>uniqueness pins \<open>parent (N[n]) 1 y = pstar\<close>\<close>
  have nextRps: "nextR ?Nn 1 ?pstar y" using nrelps by (simp add: nextR_def)
  have par_eq: "?p = ?pstar"
  proof -
    have "nextR ?Nn 1 ?p y"
      using nrely by (simp add: nextR_def)
    thus ?thesis using nextRps by (rule nextR1_unique)
  qed
  \<comment> \<open>conjunct1: \<open>hpN\<close> directly; conjunct2: base of \<open>?p = ?pstar\<close> is \<open>pN = parent N 1 y'\<close>\<close>
  have base_p: "(if ?p < ?j0 then ?p else ?j0 + (?p - ?j0) mod ?w) = ?pN"
  proof -
    have step: "(if ?p < ?j0 then ?p else ?j0 + (?p - ?j0) mod ?w)
                  = (if ?pstar < ?j0 then ?pstar else ?j0 + (?pstar - ?j0) mod ?w)"
      by (simp only: par_eq)
    have "(if ?pstar < ?j0 then ?pstar else ?j0 + (?pstar - ?j0) mod ?w) = ?pN"
      using basepstar by simp
    thus ?thesis using step by simp
  qed
  show ?thesis
  proof (intro conjI)
    show "hasParent N 1 ?yp" by (rule hpN')
    show "entry N 1 (if ?p < ?j0 then ?p else ?j0 + (?p - ?j0) mod ?w)
            = entry N 1 (parent N 1 ?yp)" using base_p by simp
  qed
qed


text \<open>§6.7 oper-tiling ROW-1 piece W1(c) (Front B), the FORWARD lift discharging
  \<open>le0pstar\<close> when the \<open>N\<close>-parent \<open>pN = parent N 1 y'\<close> of the period base sits in
  the active slice (\<open>j\<^sub>0 \<le> pN\<close>).  The slice chain \<open>le0 N pN y'\<close> (from \<open>hpN\<close>'s
  \<open>nextrel1\<close>) lifts verbatim into block \<open>q\<^sub>y\<close> via @{thm [source]
  oper_d0zero_le0_slice_lift}, landing \<open>le0 (N[n]) pstar y\<close> with
  \<open>pstar = j\<^sub>0 + q\<^sub>y\<cdot>w + (pN - j\<^sub>0)\<close>.  (Prefix start \<open>pN < j\<^sub>0\<close> is the residual cross
  case.)  Empirically 1212/1212 slice subcases.\<close>

lemma operCA_tiling_bcorr_le0pstar_slice:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y"
    and hpny: "hasParent ((N::pairseq)[n]) 1 y"
    and hpN: "hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                   mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
    and pNge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                 \<le> parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                      + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                         mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
  shows "le0 ((N::pairseq)[n])
            (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
               + ((y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                  div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                 * (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
               + (parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                     + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                        mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                  - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
            y"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?Nn = "(N::pairseq)[n]"
  let ?qy = "(y - ?j0) div ?w"  let ?sy = "(y - ?j0) mod ?w"
  let ?yp = "?j0 + ?sy"
  let ?pN = "parent N 1 ?yp"
  have w0: "0 < ?w" using j0lt by linarith
  have j0w1: "?j0 + ?w = ?j1" using j0lt by simp
  have lenNn: "Lng ?Nn = ?j0 + n * ?w"
    by (rule operB_gen_LngM[OF L notzero hp j0lt])
  have yge: "?j0 \<le> y" using ge by simp
  have nrely: "nextrel1 ?Nn (parent ?Nn 1 y) y"
  proof -
    have "\<exists>!a. nextR ?Nn 1 a y" using hpny unfolding hasParent_def by simp
    hence "nextR ?Nn 1 (parent ?Nn 1 y) y" unfolding parent_def by (rule theI')
    thus ?thesis by (simp add: nextR_def)
  qed
  from nrely have yNn: "y < Lng ?Nn" by (simp add: nextrel1_def)
  have syw: "?sy < ?w" using w0 by simp
  have ymj: "y - ?j0 < n * ?w" using yNn lenNn yge by linarith
  have qyn: "?qy < n" using less_mult_imp_div_less[OF ymj] .
  have ysplit: "y = ?j0 + ?qy * ?w + ?sy"
  proof -
    have "?qy * ?w + ?sy = y - ?j0"
      using div_mult_mod_eq[of "y - ?j0" ?w] by (simp add: mult.commute)
    thus ?thesis using yge by linarith
  qed
  have ypj1: "?yp < ?j1" using syw j0w1 by linarith
  \<comment> \<open>extract \<open>le0 N pN y'\<close> from \<open>hpN\<close>'s \<open>nextrel1\<close>\<close>
  have hpN': "hasParent N 1 ?yp" using hpN by simp
  have nrelN: "nextrel1 N ?pN ?yp"
  proof -
    have "\<exists>!a. nextR N 1 a ?yp" using hpN' unfolding hasParent_def by simp
    hence "nextR N 1 ?pN ?yp" unfolding parent_def by (rule theI')
    thus ?thesis by (simp add: nextR_def)
  qed
  from nrelN have le0pNyp: "le0 N ?pN ?yp" by (simp add: nextrel1_def)
  \<comment> \<open>lift the slice chain into block \<open>q\<^sub>y\<close>\<close>
  have lifted: "le0 ?Nn (?j0 + ?qy * ?w + (?pN - ?j0)) (?j0 + ?qy * ?w + (?yp - ?j0))"
    by (rule oper_d0zero_le0_slice_lift[OF L notzero hp j0lt qyn pNge ypj1 le0pNyp])
  have ypoff: "?yp - ?j0 = ?sy" by simp
  have target_eq: "?j0 + ?qy * ?w + (?yp - ?j0) = y" using ysplit ypoff by simp
  show ?thesis using lifted target_eq by simp
qed



text \<open>§6.7 oper-tiling ROW-1 (Front B): the FULL \<open>le0pstar\<close> input of
  @{thm [source] operCA_tiling_bcorr_reduced}, by case split on whether the
  period-base row-1 parent \<open>pN = parent N 1 y'\<close> lands in the active slice
  (\<open>j\<^sub>0 \<le> pN\<close>, slice case via @{thm [source] operCA_tiling_bcorr_le0pstar_slice}) or
  in the prefix (\<open>pN < j\<^sub>0\<close>, cross case via
  @{thm [source] oper_d1pos_le0_prefix_lift_fwd}).  Both land
  \<open>le0 (N[n]) pstar y\<close>.  Empirically the two subcases together are 1512/1512.\<close>

lemma operCA_tiling_bcorr_le0pstar:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and n1: "1 \<le> n"
    and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y"
    and hpny: "hasParent ((N::pairseq)[n]) 1 y"
    and hpN: "hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                   mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
  shows "le0 ((N::pairseq)[n])
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
            y"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?Nn = "(N::pairseq)[n]"
  let ?qy = "(y - ?j0) div ?w"  let ?sy = "(y - ?j0) mod ?w"
  let ?yp = "?j0 + ?sy"
  let ?pN = "parent N 1 ?yp"
  have w0: "0 < ?w" using j0lt by linarith
  have j0w1: "?j0 + ?w = ?j1" using j0lt by simp
  have lenNn: "Lng ?Nn = ?j0 + n * ?w"
    by (rule operB_gen_LngM[OF L notzero hp j0lt])
  have yge: "?j0 \<le> y" using ge by simp
  \<comment> \<open>decode \<open>y\<close> for ranges\<close>
  have nrely: "nextrel1 ?Nn (parent ?Nn 1 y) y"
  proof -
    have "\<exists>!a. nextR ?Nn 1 a y" using hpny unfolding hasParent_def by simp
    hence "nextR ?Nn 1 (parent ?Nn 1 y) y" unfolding parent_def by (rule theI')
    thus ?thesis by (simp add: nextR_def)
  qed
  from nrely have yNn: "y < Lng ?Nn" by (simp add: nextrel1_def)
  have syw: "?sy < ?w" using w0 by simp
  have ymj: "y - ?j0 < n * ?w" using yNn lenNn yge by linarith
  have qyn: "?qy < n" using less_mult_imp_div_less[OF ymj] .
  have ysplit: "y = ?j0 + ?qy * ?w + ?sy"
  proof -
    have "?qy * ?w + ?sy = y - ?j0"
      using div_mult_mod_eq[of "y - ?j0" ?w] by (simp add: mult.commute)
    thus ?thesis using yge by linarith
  qed
  have ypj1: "?yp < ?j1" using syw j0w1 by linarith
  \<comment> \<open>extract \<open>nextrel1 N pN y'\<close> from \<open>hpN\<close>\<close>
  have hpN': "hasParent N 1 ?yp" using hpN by simp
  have nrelN: "nextrel1 N ?pN ?yp"
  proof -
    have "\<exists>!a. nextR N 1 a ?yp" using hpN' unfolding hasParent_def by simp
    hence "nextR N 1 ?pN ?yp" unfolding parent_def by (rule theI')
    thus ?thesis by (simp add: nextR_def)
  qed
  from nrelN have pNlt: "?pN < ?yp" and le0pNyp: "le0 N ?pN ?yp"
    by (auto simp: nextrel1_def)
  show ?thesis
  proof (cases "?pN < ?j0")
    case True
    \<comment> \<open>PREFIX cross case: witness is \<open>pN\<close> itself, target \<open>le0 (N[n]) pN y\<close>\<close>
    have j0eq: "parent N 1 ?j1 = ?j0" using i1z by simp
    have jpre: "?pN < parent N 1 ?j1" using True j0eq by simp
    have j0lt': "parent N 1 ?j1 < ?j1" using j0lt j0eq by simp
    have xpge: "parent N 1 ?j1 \<le> ?yp" using yge j0eq ypj1 by simp
    have xge: "parent N 1 ?j1 \<le> y" using yge j0eq by simp
    have lift: "le0 ?Nn ?pN y"
      by (rule oper_d1pos_le0_prefix_lift_fwd[OF L notzero hp i1z j0lt' n1
            jpre xpge ypj1 le0pNyp xge yNn])
    show ?thesis using True lift by simp
  next
    case False
    hence pNge: "?j0 \<le> ?pN" by simp
    have lift: "le0 ?Nn (?j0 + ?qy * ?w + (?pN - ?j0)) y"
      by (rule operCA_tiling_bcorr_le0pstar_slice[OF L notzero hp i1z j0lt ge hpny hpN pNge])
    show ?thesis using False lift by simp
  qed
qed


text \<open>§6.7 oper-tiling \<open>RedCondA (N[n])\<close> for the genuine TILING branch, reduced to
  the two SOUNDLY-CARRIED residuals \<open>hpN\<close> (the period-base row-1 parent existence,
  empirically 3710/0 / 1512/1512) and \<open>valley\<close> (the row-1 nearest-ancestor
  minimality of the lifted witness, Front A; empirically 0 bad).  Assembles
  \<open>bcorr\<close> from @{thm [source] operCA_tiling_bcorr_reduced} (fed \<open>le0pstar\<close> via
  @{thm [source] operCA_tiling_bcorr_le0pstar} and \<open>valley\<close>) and discharges
  @{thm [source] operCA_tiling_via_bcorr}.  This is the FULL \<open>operCA\<close> brick of
  @{thm [source] m_6_7_standard_RedCondAB} modulo \<open>hpN\<close> + \<open>valley\<close>.\<close>

lemma operCA_tiling_cond_hpN_valley:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and condA: "RedCondA N"
    and n1: "1 \<le> n"
    and hpN: "\<And>y. parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y
                 \<Longrightarrow> hasParent ((N::pairseq)[n]) 1 y
                 \<Longrightarrow> idx1 N (Lng N - 1) = 1
                 \<Longrightarrow> hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                        + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                           mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
    and valley: "\<And>y j. parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y
                 \<Longrightarrow> hasParent ((N::pairseq)[n]) 1 y
                 \<Longrightarrow> idx1 N (Lng N - 1) = 1
                 \<Longrightarrow> (if parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
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
                        < j
                   \<Longrightarrow> le0 ((N::pairseq)[n]) j y
                   \<Longrightarrow> entry ((N::pairseq)[n]) 1 y \<le> entry ((N::pairseq)[n]) 1 j"
  shows "RedCondA ((N::pairseq)[n])"
proof -
  have bcorr: "\<And>y. parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y
                 \<Longrightarrow> hasParent ((N::pairseq)[n]) 1 y
                 \<Longrightarrow> idx1 N (Lng N - 1) = 1
                 \<Longrightarrow> hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                        + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                           mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                   \<and> entry N 1 (if parent ((N::pairseq)[n]) 1 y
                                  < parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                                then parent ((N::pairseq)[n]) 1 y
                                else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                                  + (parent ((N::pairseq)[n]) 1 y
                                     - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                                    mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                       = entry N 1 (parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                          + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                             mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))))"
  proof -
    fix y
    assume ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y"
       and hpny: "hasParent ((N::pairseq)[n]) 1 y"
       and i1z: "idx1 N (Lng N - 1) = 1"
    have hpNy: "hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                  + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                     mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
      by (rule hpN[OF ge hpny i1z])
    have le0ps: "le0 ((N::pairseq)[n])
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
            y"
      by (rule operCA_tiling_bcorr_le0pstar[OF L notzero hp i1z j0lt n1 ge hpny hpNy])
    show "hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                  + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                     mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
            \<and> entry N 1 (if parent ((N::pairseq)[n]) 1 y
                          < parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                        then parent ((N::pairseq)[n]) 1 y
                        else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                          + (parent ((N::pairseq)[n]) 1 y
                             - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                            mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
               = entry N 1 (parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                  + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                     mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))))"
      by (rule operCA_tiling_bcorr_reduced[OF L notzero hp i1z j0lt n1 ge hpny hpNy le0ps
            valley[OF ge hpny i1z]])
  qed
  show ?thesis
    by (rule operCA_tiling_via_bcorr[OF L notzero hp j0lt condA n1 bcorr])
qed


text \<open>§6.7 oper-tiling \<open>operCA\<close> brick in the EXACT shape of
  @{thm [source] m_6_7_standard_RedCondAB}'s \<open>operCA\<close> hypothesis, with the tiling
  side conditions \<open>L\<close>/\<open>notzero\<close>/\<open>hp\<close>/\<open>j0lt\<close> extracted from \<open>N \<in> ST_PS\<close> and the
  non-degeneracy \<open>\<not> nontile\<close> (\<open>j0lt = parent < j\<^sub>1\<close> via @{thm [source]
  poper_nextR_imp_le0}).  Conditional only on the two soundly-carried residuals
  \<open>hpN\<close> (period-base row-1 parent existence) and \<open>valley\<close> (lifted row-1 minimality).\<close>

lemma operCA_tiling_hpN_valley:
  assumes hpN: "\<And>N n y. \<lbrakk>N \<in> ST_PS;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1));
                   parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y;
                   hasParent ((N::pairseq)[n]) 1 y;
                   idx1 N (Lng N - 1) = 1\<rbrakk>
                 \<Longrightarrow> hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                        + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                           mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
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
    and Nst: "N \<in> ST_PS" and condA: "RedCondA N" and condB: "RedCondB N"
    and n1: "1 \<le> n"
    and tile: "\<not> (Lng N - 1 = 0
                  \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                  \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1))"
  shows "RedCondA ((N::pairseq)[n])"
proof -
  have NT: "N \<in> T_PS" by (rule ST_PS_T_PS[OF Nst])
  have L: "1 < Lng N" using tile by (cases "Lng N - 1 = 0") auto
  have notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    using tile by blast
  have hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)" using tile by blast
  have parR: "nextR N (idx1 N (Lng N - 1)) (parent N (idx1 N (Lng N - 1)) (Lng N - 1)) (Lng N - 1)"
    using hp unfolding hasParent_def parent_def by (rule theI')
  have j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    using poper_nextR_imp_le0[OF parR] by simp
  show ?thesis
  proof (rule operCA_tiling_cond_hpN_valley[OF L notzero hp j0lt condA n1])
    fix y assume "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y"
      and "hasParent ((N::pairseq)[n]) 1 y" and "idx1 N (Lng N - 1) = 1"
    thus "hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
            + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
               mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
      by (rule hpN[OF Nst tile])
  next
    fix y j
    assume gy: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y"
      and hpny: "hasParent ((N::pairseq)[n]) 1 y"
      and i1z: "idx1 N (Lng N - 1) = 1"
      and jbig: "(if parent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
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
                        < j"
      and lej: "le0 ((N::pairseq)[n]) j y"
    show "entry ((N::pairseq)[n]) 1 y \<le> entry ((N::pairseq)[n]) 1 j"
      by (rule valley[OF Nst tile gy hpny i1z jbig lej])
  qed
qed


text \<open>§6.7 \<open>ST\<^sub>PS \<subseteq> RT\<^sub>PS\<close> conditional on the two operCA residuals \<open>hpN\<close>/\<open>valley\<close>
  only (\<open>operCB\<close> is the GREEN @{thm [source] operCB_tiling}).  Feeds
  @{thm [source] m_6_7_standard_reduced} with \<open>operCA = operCA_tiling_hpN_valley\<close>
  and \<open>operCB = operCB_tiling\<close>.\<close>

lemma m_6_7_standard_reduced_hpN_valley:
  assumes hpN: "\<And>N n y. \<lbrakk>N \<in> ST_PS;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1));
                   parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y;
                   hasParent ((N::pairseq)[n]) 1 y;
                   idx1 N (Lng N - 1) = 1\<rbrakk>
                 \<Longrightarrow> hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                        + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                           mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
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
  have operCA: "\<And>N n. \<lbrakk>N \<in> ST_PS; RedCondA N; RedCondB N; 1 \<le> n;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1))\<rbrakk>
                  \<Longrightarrow> RedCondA ((N::pairseq)[n])"
    by (rule operCA_tiling_hpN_valley[OF hpN valley])
  have operCB: "\<And>N n. \<lbrakk>N \<in> ST_PS; RedCondA N; RedCondB N; 1 \<le> n;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1))\<rbrakk>
                  \<Longrightarrow> RedCondB ((N::pairseq)[n])"
    by (rule operCB_tiling)
  show ?thesis by (rule m_6_7_standard_reduced[OF operCA operCB])
qed


text \<open>§6.5 \<open>stdCA\<close> residual \<open>M \<in> ST_PS \<Longrightarrow> RedCondA M\<close> conditional on \<open>hpN\<close>/\<open>valley\<close>
  only, via @{thm [source] m_6_5_ST_PS_imp_RedCondA} with \<open>operCB = operCB_tiling\<close>.\<close>

lemma m_6_5_ST_PS_imp_RedCondA_hpN_valley:
  assumes hpN: "\<And>N n y. \<lbrakk>N \<in> ST_PS;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1));
                   parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y;
                   hasParent ((N::pairseq)[n]) 1 y;
                   idx1 N (Lng N - 1) = 1\<rbrakk>
                 \<Longrightarrow> hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                        + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                           mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
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
  have operCA: "\<And>N n. \<lbrakk>N \<in> ST_PS; RedCondA N; RedCondB N; 1 \<le> n;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1))\<rbrakk>
                  \<Longrightarrow> RedCondA ((N::pairseq)[n])"
    by (rule operCA_tiling_hpN_valley[OF hpN valley])
  have operCB: "\<And>N n. \<lbrakk>N \<in> ST_PS; RedCondA N; RedCondB N; 1 \<le> n;
                   \<not> (Lng N - 1 = 0
                      \<or> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)
                      \<or> \<not> hasParent N (idx1 N (Lng N - 1)) (Lng N - 1))\<rbrakk>
                  \<Longrightarrow> RedCondB ((N::pairseq)[n])"
    by (rule operCB_tiling)
  show ?thesis by (rule m_6_5_ST_PS_imp_RedCondA[OF M operCA operCB])
qed



text \<open>§6.7 hpN ASSEMBLY (Front B, \<open>i\<^sub>1=1\<close>): the period-base row-1 parent existence
  \<open>hasParent N 1 (base y)\<close>, REDUCED to the single row-0 base-correspondence
  hypothesis \<open>le0baseN : le0 N (base p) (base y)\<close> (\<open>p = parent (N[n]) 1 y\<close>).
  The witness \<open>base p\<close> is the row-1 parent of \<open>base y\<close>: its row-1 \<open>N\<close>-entry equals
  \<open>entry (N[n]) 1 p < entry (N[n]) 1 y = entry N 1 (base y)\<close> (period reading
  @{thm [source] operCA_tiling_entry1_base'}), so it is a STRICTLY-smaller row-1
  \<open>le0\<close>-predecessor; @{thm [source] m_5_1_parent_exists_2} then builds the
  nearest-ancestor row-1 parent and @{thm [source] nextR1_unique} pins existence.
  Empirically: witness 13062/13062, the three @{thm [source] m_5_1_parent_exists_2}
  inputs 0-fail (/tmp/hpN_3props.py, /tmp/hpN_basep_check.py).  The remaining
  \<open>le0baseN\<close> is the row-0 base-back: GREEN same-block (@{thm [source]
  oper_d1pos_le0_base_back}), prefix-cross-block PENDING.\<close>

lemma operCA_tiling_hpN_via_le0baseN:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y"
    and hpny: "hasParent ((N::pairseq)[n]) 1 y"
    and le0baseN: "le0 N (if parent ((N::pairseq)[n]) 1 y < parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                         then parent ((N::pairseq)[n]) 1 y
                         else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                           + (parent ((N::pairseq)[n]) 1 y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                              mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
                        (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                           + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                              mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
  shows "hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                   mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?Nn = "(N::pairseq)[n]"
  let ?p = "parent ?Nn 1 y"
  let ?sy = "(y - ?j0) mod ?w"
  let ?yp = "?j0 + ?sy"
  let ?bp = "if ?p < ?j0 then ?p else ?j0 + (?p - ?j0) mod ?w"
  have NT: "N \<in> T_PS" using L by (cases N) (auto simp: T_PS_def)
  have w0: "0 < ?w" using j0lt by linarith
  have j0w1: "?j0 + ?w = ?j1" using j0lt by simp
  have lenNn: "Lng ?Nn = ?j0 + n * ?w"
    by (rule operB_gen_LngM[OF L notzero hp j0lt])
  \<comment> \<open>parent edge of \<open>y\<close> in \<open>N[n]\<close>\<close>
  have nrely: "nextrel1 ?Nn ?p y"
  proof -
    have "\<exists>!a. nextR ?Nn 1 a y" using hpny unfolding hasParent_def by simp
    hence "nextR ?Nn 1 ?p y" unfolding parent_def by (rule theI')
    thus ?thesis by (simp add: nextR_def)
  qed
  from nrely have py: "?p < y" and pNn: "?p < Lng ?Nn" and yNn: "y < Lng ?Nn"
    and e1py: "entry ?Nn 1 ?p < entry ?Nn 1 y"
    by (auto simp: nextrel1_def)
  have syw: "?sy < ?w" using w0 by simp
  have ypj1: "?yp < ?j1" using syw j0w1 by linarith
  have ypN: "?yp < Lng N" using ypj1 L by linarith
  \<comment> \<open>row-1 entry readings: \<open>y\<close> reads base \<open>y'\<close>, \<open>p\<close> reads its base \<open>base p\<close>\<close>
  have e1y: "entry ?Nn 1 y = entry N 1 ?yp"
  proof -
    have nge: "\<not> y < ?j0" using ge by simp
    have "entry ?Nn 1 y = entry N 1 (if y < ?j0 then y else ?j0 + (y - ?j0) mod ?w)"
      by (rule operCA_tiling_entry1_base'[OF L notzero hp j0lt yNn])
    thus ?thesis using nge by simp
  qed
  have e1p: "entry ?Nn 1 ?p = entry N 1 ?bp"
    by (rule operCA_tiling_entry1_base'[OF L notzero hp j0lt pNn])
  \<comment> \<open>(1) strict row-1 increase at the bases\<close>
  have e1lt: "entry N 1 ?bp < entry N 1 ?yp" using e1py e1p e1y by simp
  \<comment> \<open>(2) \<open>base p < base y\<close> (\<open>\<le>\<close> from le0 mono, \<open>\<noteq>\<close> from the strict entries)\<close>
  have bple: "?bp \<le> ?yp"
  proof -
    have "(nextrel0 N)\<^sup>*\<^sup>* ?bp ?yp" using le0baseN by (simp add: le0_def)
    thus ?thesis by (rule nextrel0_rtrancl_mono)
  qed
  have bpneq: "?bp \<noteq> ?yp" using e1lt by force
  have bplt: "?bp < ?yp" using bple bpneq by linarith
  \<comment> \<open>(3) \<open>leR N 0 (base p) (base y)\<close> from the supplied \<open>le0baseN\<close>\<close>
  have leR0: "leR N 0 ?bp ?yp" using le0baseN by (simp add: leR_def)
  \<comment> \<open>build the nearest row-1 ancestor; uniqueness gives \<open>hasParent\<close>\<close>
  obtain j' where "?bp \<le> j'" "j' < ?yp" and j'par: "nextR N 1 j' ?yp"
    using m_5_1_parent_exists_2[OF NT bplt ypN e1lt leR0] by blast
  have "hasParent N 1 ?yp"
    unfolding hasParent_def
  proof (rule ex_ex1I)
    show "\<exists>j0. nextR N 1 j0 ?yp" using j'par by blast
  next
    fix a b assume "nextR N 1 a ?yp" "nextR N 1 b ?yp"
    thus "a = b" using nextR1_unique by blast
  qed
  thus ?thesis by simp
qed


text \<open>§6.7 hpN \<open>le0baseN\<close> SAME-BLOCK discharge (Front B, \<open>i\<^sub>1=1\<close>): when the
  \<open>N[n]\<close>-parent \<open>p = parent (N[n]) 1 y\<close> sits in the SAME period block \<open>q\<^sub>y\<close> as \<open>y\<close>
  (i.e. \<open>j\<^sub>0 \<le> p\<close>; empirically 12426/12426 of the non-prefix cases), the row-0
  reachability \<open>le0 (N[n]) p y\<close> projects to \<open>le0 N (base p) (base y)\<close> by the d1pos
  base-back @{thm [source] oper_d1pos_le0_base_back} (offsets \<open>s\<^sub>p = (p-j\<^sub>0) mod w
  < s\<^sub>y = (y-j\<^sub>0) mod w\<close>; the same-block offset-strictness holds since
  \<open>p < y\<close>).\<close>

lemma operCA_tiling_hpN_le0baseN_sameblock:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y"
    and hpny: "hasParent ((N::pairseq)[n]) 1 y"
    and pge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> parent ((N::pairseq)[n]) 1 y"
    and sblk: "(parent ((N::pairseq)[n]) 1 y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                 div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
               = (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                 div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
  shows "le0 N (if parent ((N::pairseq)[n]) 1 y < parent N (idx1 N (Lng N - 1)) (Lng N - 1)
               then parent ((N::pairseq)[n]) 1 y
               else parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                 + (parent ((N::pairseq)[n]) 1 y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                    mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))
              (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                 + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                    mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?Nn = "(N::pairseq)[n]"
  let ?p = "parent ?Nn 1 y"
  let ?sy = "(y - ?j0) mod ?w"  let ?qy = "(y - ?j0) div ?w"
  let ?sp = "(?p - ?j0) mod ?w"  let ?qp = "(?p - ?j0) div ?w"
  have j0eq1: "?j0 = parent N 1 ?j1" using i1z by simp
  have j0lt1: "parent N 1 ?j1 < ?j1" using j0lt j0eq1 by simp
  have w0: "0 < ?w" using j0lt by linarith
  have j0w1: "?j0 + ?w = ?j1" using j0lt by simp
  have lenNn: "Lng ?Nn = ?j0 + n * ?w"
    by (rule operB_gen_LngM[OF L notzero hp j0lt])
  \<comment> \<open>parent edge\<close>
  have nrely: "nextrel1 ?Nn ?p y"
  proof -
    have "\<exists>!a. nextR ?Nn 1 a y" using hpny unfolding hasParent_def by simp
    hence "nextR ?Nn 1 ?p y" unfolding parent_def by (rule theI')
    thus ?thesis by (simp add: nextR_def)
  qed
  from nrely have py: "?p < y" and yNn: "y < Lng ?Nn"
    and le0py: "le0 ?Nn ?p y"
    by (auto simp: nextrel1_def)
  have syw: "?sy < ?w" using w0 by simp
  have spw: "?sp < ?w" using w0 by simp
  have ymj: "y - ?j0 < n * ?w" using yNn lenNn ge by linarith
  have qyn: "?qy < n" using less_mult_imp_div_less[OF ymj] .
  \<comment> \<open>decode \<open>p\<close>, \<open>y\<close> in the SAME block \<open>q\<^sub>y\<close>\<close>
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
  have qpeq: "?qp = ?qy" using sblk by simp
  have psplit': "?p = ?j0 + ?qy * ?w + ?sp" using psplit qpeq by simp
  \<comment> \<open>offset strictness \<open>s\<^sub>p < s\<^sub>y\<close> from \<open>p < y\<close> in the same block\<close>
  have spsy: "?sp < ?sy"
  proof -
    have "?j0 + ?qy * ?w + ?sp < ?j0 + ?qy * ?w + ?sy" using py psplit' ysplit by simp
    thus ?thesis by simp
  qed
  \<comment> \<open>rewrite \<open>le0 (N[n]) p y\<close> into the block-\<open>q\<^sub>y\<close> offset form and apply base-back\<close>
  have reach: "le0 ?Nn (parent N 1 ?j1 + ?qy * (?j1 - parent N 1 ?j1) + ?sp)
                       (parent N 1 ?j1 + ?qy * (?j1 - parent N 1 ?j1) + ?sy)"
  proof -
    have e1: "parent N 1 ?j1 + ?qy * (?j1 - parent N 1 ?j1) + ?sp = ?p"
      using psplit' j0eq1 by simp
    have e2: "parent N 1 ?j1 + ?qy * (?j1 - parent N 1 ?j1) + ?sy = y"
      using ysplit j0eq1 by simp
    show ?thesis using le0py e1 e2 by simp
  qed
  have syw': "?sy < ?j1 - parent N 1 ?j1" using syw j0eq1 by simp
  have baseback: "le0 N (parent N 1 ?j1 + ?sp) (parent N 1 ?j1 + ?sy)"
    by (rule oper_d1pos_le0_base_back[OF L notzero hp i1z j0lt1 qyn spsy syw' reach])
  \<comment> \<open>identify the abstract base columns: \<open>base p = j\<^sub>0 + s\<^sub>p\<close> (since \<open>p \<ge> j\<^sub>0\<close>),
     \<open>base y = j\<^sub>0 + s\<^sub>y\<close>\<close>
  have pnlt: "\<not> ?p < ?j0" using pge by simp
  have basep_eq: "(if ?p < ?j0 then ?p else ?j0 + (?p - ?j0) mod ?w) = ?j0 + ?sp"
    using pnlt by simp
  show ?thesis using baseback basep_eq j0eq1 by simp
qed


text \<open>§6.7 PREFIX ROW-0 PROJECTION (Front A, \<open>i\<^sub>1=1\<close>): a row-0 \<open>N[n]\<close>-chain from a
  PREFIX source \<open>j < j\<^sub>0\<close> that reaches an active-slice target \<open>y \<ge> j\<^sub>0\<close> projects to a
  row-0 \<open>N\<close>-chain from \<open>j\<close> to the period base \<open>y' = j\<^sub>0 + (y-j\<^sub>0) mod w\<close>.  Restrict the
  ancestor path down to \<open>y'\<close> (\<open>m_5_1_ancestor_tree_1\<close>, \<open>j \<le> y' \<le> y\<close>), then transfer the
  row-0 chain \<open>N[n] \<to> N\<close> on \<open>[0, y']\<close> where \<open>N[n]\<close> reads \<open>N\<close> verbatim (prefix
  \<open>[0,j\<^sub>0)\<close> via @{thm [source] operB_gen_entry_prefix}; first active block \<open>[j\<^sub>0,j\<^sub>1)\<close>,
  \<open>q=0\<close>, shift \<open>0\<close>, via @{thm [source] oper_gen_block_entry0}) — @{thm [source]
  le0_prefix_row0}.  Empirically 558/558 (/tmp/fa_prefix_proj.py).  This is exactly the
  prefix-cross residual of \<open>le0baseN\<close> (with \<open>j = parent (N[n]) 1 y < j\<^sub>0\<close>), unblocking
  @{thm [source] operCA_tiling_hpN_via_le0baseN}.\<close>

lemma operCA_tiling_le0_prefix_proj:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and n1: "1 \<le> n"
    and jpre: "j < parent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y"
    and reach: "le0 ((N::pairseq)[n]) j y"
  shows "le0 N j (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
            + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
               mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?Nn = "(N::pairseq)[n]"
  let ?sy = "(y - ?j0) mod ?w"
  let ?yp = "?j0 + ?sy"
  have w0: "0 < ?w" using j0lt by linarith
  have j0w1: "?j0 + ?w = ?j1" using j0lt by simp
  have NT: "N \<in> T_PS" using L by (cases N) (auto simp: T_PS_def)
  have NnT: "?Nn \<in> T_PS"
    using poper_oper_nth0[OF NT L n1] by (cases ?Nn) (auto simp: T_PS_def)
  \<comment> \<open>length and bounds\<close>
  have lenNn: "Lng ?Nn = ?j0 + n * ?w"
    by (rule operB_gen_LngM[OF L notzero hp j0lt])
  from reach have jLNn: "j < Lng ?Nn" and yLNn: "y < Lng ?Nn" and jley: "j \<le> y"
    by (auto simp: le0_def nextrel0_rtrancl_mono)
  have syw: "?sy < ?w" using w0 by simp
  have ypj1: "?yp < ?j1" using syw j0w1 by linarith
  have ypN: "?yp < Lng N" using ypj1 L by linarith
  have jyp: "j \<le> ?yp" using jpre by simp
  have ypy: "?yp \<le> y"
  proof -
    have "?yp = ?j0 + ?sy" by simp
    moreover have "?j0 + ?sy \<le> y"
      using ge div_mult_mod_eq[of "y - ?j0" ?w] by linarith
    ultimately show ?thesis by simp
  qed
  have ypLNn: "?yp < Lng ?Nn" using ypy yLNn by linarith
  \<comment> \<open>(1) restrict the ancestor path \<open>j \<rightsquigarrow> y\<close> down to \<open>y'\<close>\<close>
  have leRjy: "leR ?Nn 0 j y" using reach by (simp add: leR_def)
  have leRjyp: "leR ?Nn 0 j ?yp"
    by (rule m_5_1_ancestor_tree_1[OF NnT leRjy jyp ypy])
  have le0Nnjyp: "le0 ?Nn j ?yp" using leRjyp by (simp add: leR_def)
  \<comment> \<open>(2) row-0 agreement \<open>N[n] = N\<close> on \<open>[0, y']\<close>\<close>
  have agree: "\<And>z. z \<le> ?yp \<Longrightarrow> entry ?Nn 0 z = entry N 0 z"
  proof -
    fix z assume zyp: "z \<le> ?yp"
    show "entry ?Nn 0 z = entry N 0 z"
    proof (cases "z < ?j0")
      case True
      show ?thesis by (rule operB_gen_entry_prefix[OF L notzero hp True])
    next
      case False
      hence zj0: "?j0 \<le> z" by simp
      have zlt: "z - ?j0 < ?w" using zyp zj0 syw by linarith
      have n0: "0 < n" using n1 by simp
      have "entry ?Nn 0 (?j0 + 0 * ?w + (z - ?j0))
              = entry N 0 (?j0 + (z - ?j0))
                + 0 * (if 0 < ?i1 then entry N 0 ?j1 - entry N 0 ?j0 else 0)"
        by (rule oper_gen_block_entry0[OF L notzero hp j0lt n0 zlt])
      hence "entry ?Nn 0 (?j0 + (z - ?j0)) = entry N 0 (?j0 + (z - ?j0))" by simp
      thus ?thesis using zj0 by simp
    qed
  qed
  \<comment> \<open>(3) transfer the chain \<open>N[n] \<to> N\<close>\<close>
  show ?thesis
    by (rule le0_prefix_row0[OF agree ypLNn ypN jyp order.refl le0Nnjyp])
qed


text \<open>§6.7 hpN PREFIX sub-case (Front A, \<open>i\<^sub>1=1\<close>): the period-base row-1 parent
  existence \<open>hasParent N 1 (base y)\<close> when the \<open>N[n]\<close>-parent \<open>p = parent (N[n]) 1 y\<close>
  sits in the verbatim PREFIX \<open>p < j\<^sub>0\<close>.  The \<open>le0baseN\<close> input of @{thm [source]
  operCA_tiling_hpN_via_le0baseN} is then \<open>le0 N p (base y)\<close>, the row-0 prefix
  projection @{thm [source] operCA_tiling_le0_prefix_proj} of the row-1 parent edge
  \<open>le0 (N[n]) p y\<close>.  This discharges the prefix-cross-block residual that was PENDING
  in @{thm [source] operCA_tiling_hpN_le0baseN_sameblock}'s comment.\<close>

lemma operCA_tiling_hpN_prefix:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and n1: "1 \<le> n"
    and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y"
    and hpny: "hasParent ((N::pairseq)[n]) 1 y"
    and ppre: "parent ((N::pairseq)[n]) 1 y < parent N (idx1 N (Lng N - 1)) (Lng N - 1)"
  shows "hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                   mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?Nn = "(N::pairseq)[n]"
  let ?p = "parent ?Nn 1 y"
  \<comment> \<open>row-1 parent edge of \<open>y\<close> in \<open>N[n]\<close> gives row-0 reachability \<open>le0 (N[n]) p y\<close>\<close>
  have nrely: "nextrel1 ?Nn ?p y"
  proof -
    have "\<exists>!a. nextR ?Nn 1 a y" using hpny unfolding hasParent_def by simp
    hence "nextR ?Nn 1 ?p y" unfolding parent_def by (rule theI')
    thus ?thesis by (simp add: nextR_def)
  qed
  have le0py: "le0 ?Nn ?p y" using nrely by (simp add: nextrel1_def)
  \<comment> \<open>prefix projection: \<open>le0 N p (base y)\<close>\<close>
  have le0Npyp: "le0 N ?p (?j0 + (y - ?j0) mod ?w)"
    by (rule operCA_tiling_le0_prefix_proj[OF L notzero hp i1z j0lt n1 ppre ge le0py])
  \<comment> \<open>the \<open>le0baseN\<close> if-branch collapses to \<open>p\<close> since \<open>p < j\<^sub>0\<close>\<close>
  have le0baseN: "le0 N (if ?p < ?j0 then ?p else ?j0 + (?p - ?j0) mod ?w)
                       (?j0 + (y - ?j0) mod ?w)"
    using le0Npyp ppre by simp
  show ?thesis
    by (rule operCA_tiling_hpN_via_le0baseN[OF L notzero hp i1z j0lt ge hpny le0baseN])
qed


text \<open>§6.7 hpN FULL assembly (Front A, \<open>i\<^sub>1=1\<close>), reduced to the SINGLE same-block
  residual \<open>sblk\<close>.  Splits on where the \<open>N[n]\<close>-parent \<open>p = parent (N[n]) 1 y\<close> lands:
  \<^item> PREFIX \<open>p < j\<^sub>0\<close>: @{thm [source] operCA_tiling_hpN_prefix} (now GREEN via the row-0
    prefix projection).
  \<^item> ACTIVE \<open>j\<^sub>0 \<le> p\<close>: @{thm [source] operCA_tiling_hpN_le0baseN_sameblock} then
    @{thm [source] operCA_tiling_hpN_via_le0baseN}; the only obligation is \<open>sblk\<close>
    (\<open>p\<close> sits in \<open>y\<close>'s period block, \<open>(p-j\<^sub>0) div w = (y-j\<^sub>0) div w\<close>) — empirically
    13062/13062 the active case is same-block (/tmp/hpN_cases.py: 0 active cross-block).
  Thus the whole \<open>hpN\<close> residual is exactly \<open>sblk\<close>.\<close>

lemma operCA_tiling_hpN_via_sblk:
  assumes L: "1 < Lng N"
    and notzero: "\<not> (entry N 0 (Lng N - 1) = 0 \<and> entry N 1 (Lng N - 1) = 0)"
    and hp: "hasParent N (idx1 N (Lng N - 1)) (Lng N - 1)"
    and i1z: "idx1 N (Lng N - 1) = 1"
    and j0lt: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) < Lng N - 1"
    and n1: "1 \<le> n"
    and ge: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> y"
    and hpny: "hasParent ((N::pairseq)[n]) 1 y"
    and sblk: "parent N (idx1 N (Lng N - 1)) (Lng N - 1) \<le> parent ((N::pairseq)[n]) 1 y
               \<Longrightarrow> (parent ((N::pairseq)[n]) 1 y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                     div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                   = (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                     div (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1))"
  shows "hasParent N 1 (parent N (idx1 N (Lng N - 1)) (Lng N - 1)
                + (y - parent N (idx1 N (Lng N - 1)) (Lng N - 1))
                   mod (Lng N - 1 - parent N (idx1 N (Lng N - 1)) (Lng N - 1)))"
proof -
  let ?j1 = "Lng N - 1"  let ?i1 = "idx1 N ?j1"  let ?j0 = "parent N ?i1 ?j1"
  let ?w = "?j1 - ?j0"
  let ?Nn = "(N::pairseq)[n]"
  let ?p = "parent ?Nn 1 y"
  show ?thesis
  proof (cases "?p < ?j0")
    case True
    show ?thesis
      by (rule operCA_tiling_hpN_prefix[OF L notzero hp i1z j0lt n1 ge hpny True])
  next
    case False
    hence pge: "?j0 \<le> ?p" by simp
    have sb: "(?p - ?j0) div ?w = (y - ?j0) div ?w" by (rule sblk[OF pge])
    have le0baseN: "le0 N (if ?p < ?j0 then ?p else ?j0 + (?p - ?j0) mod ?w)
                         (?j0 + (y - ?j0) mod ?w)"
      by (rule operCA_tiling_hpN_le0baseN_sameblock[OF L notzero hp i1z j0lt ge hpny pge sb])
    show ?thesis
      by (rule operCA_tiling_hpN_via_le0baseN[OF L notzero hp i1z j0lt ge hpny le0baseN])
  qed
qed

end
