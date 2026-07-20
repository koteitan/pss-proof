theory Frontier_6_045
  imports P_6_6_Red_leftend_2
begin

(* ===== Red_Pred helper block from workflow predh-T1 ===== *)
text \<open>
  T1 helper (\<open>pred_P_decomp\<close>): for a multi-term \<open>M \<in> T_PS\<close>, the predecessor
  acts on the LAST \<open>P\<close>-block.  Concretely \<open>Pred = butlast M\<close>, and the cut
  \<open>c = Pcut M\<close> sits at \<open>c \<le> Lng M - 1\<close>, so \<open>P M = P (take c M) @ [drop c M]\<close>
  has \<open>last (P M) = drop c M\<close> and \<open>butlast (P M) = P (take c M)\<close>.  Dropping the
  final pair either deletes a singleton last block (\<open>c = Lng M - 1\<close>, the
  multiT\<rightarrow>non-multiT class-change case) or predecessors it (\<open>c < Lng M - 1\<close>,
  where \<open>butlast M\<close> is again multiT with the same cut \<open>c\<close>, by additivity).
  Empirically verified 6480/0 (and the class-change subcase 648/648).
\<close>

lemma pred_P_decomp:
  assumes M: "M \<in> T_PS" and multi: "multiT M"
  shows "P (Pred M) =
           (if Lng (last (P M)) = 1
            then butlast (P M)
            else butlast (P M) @ [Pred (last (P M))])"
proof -
  have L: "1 < Lng M" by (rule multiT_imp_Lng_gt1[OF M multi])
  let ?c = "Pcut M"
  let ?j1 = "Lng M - 1"
  from P_add_Pcut_props[OF L] have c0: "0 < ?c" and cj1: "?c \<le> ?j1"
    and lec: "leR M 0 ?c ?j1" by auto
  have cL: "?c < Lng M" using cj1 L by simp
  have cond: "multiT M \<and> 1 < Lng M" using multi L by simp
  \<comment> \<open>One unfold of \<open>P.simps\<close>: the last block is \<open>drop ?c M\<close>, the rest \<open>P (take ?c M)\<close>.\<close>
  have Pstep: "P M = P (take ?c M) @ [drop ?c M]"
    by (subst P.simps) (simp only: cond if_True simp_thms)
  have lastPM: "last (P M) = drop ?c M" using Pstep by simp
  have butlastPM: "butlast (P M) = P (take ?c M)"
    using Pstep P_nonempty[of "take ?c M"] by simp
  \<comment> \<open>\<open>Pred M = butlast M\<close> since \<open>Lng M > 1\<close>.\<close>
  have predM: "Pred M = butlast M" using L by (simp add: Pred_def)
  have Lbl: "Lng (butlast M) = Lng M - 1" by simp
  \<comment> \<open>\<open>Lng (drop ?c M) = Lng M - ?c\<close>; it is \<open>1\<close> iff \<open>?c = Lng M - 1\<close>.\<close>
  have Ldrop: "Lng (drop ?c M) = Lng M - ?c" by simp
  show ?thesis
  proof (cases "?c = ?j1")
    case True
    \<comment> \<open>Singleton last block: \<open>drop ?c M\<close> has length 1; \<open>butlast M = take ?c M\<close>.\<close>
    have len1: "Lng (last (P M)) = 1" using lastPM True L by simp
    have "butlast M = take ?j1 M" by (simp add: butlast_conv_take)
    hence "Pred M = take ?c M" using predM True by simp
    hence "P (Pred M) = P (take ?c M)" by simp
    also have "\<dots> = butlast (P M)" using butlastPM by simp
    finally show ?thesis using len1 by simp
  next
    case False
    with cj1 have ltc: "?c < ?j1" by simp
    \<comment> \<open>Last block has length \<open>> 1\<close>.\<close>
    have lenN: "Lng (last (P M)) = Lng M - ?c" using lastPM Ldrop by simp
    have lenNgt1: "1 < Lng (last (P M))" using lenN ltc L by simp
    \<comment> \<open>\<open>butlast M \<in> T_PS\<close> and is again multi-term, with cut \<open>?c\<close> by additivity.\<close>
    have blT: "butlast M \<in> T_PS"
    proof -
      have "Lng (butlast M) = Lng M - 1" by simp
      hence "butlast M \<noteq> []" using L by (cases "butlast M") auto
      thus ?thesis by (simp add: T_PS_def)
    qed
    \<comment> \<open>\<open>?c \<le> Lng (butlast M) - 1\<close> since \<open>?c < Lng M - 1\<close>.\<close>
    have c_bl: "?c \<le> Lng (butlast M) - 1" using ltc Lbl by simp
    \<comment> \<open>Entries below \<open>Lng M - 1\<close> agree on \<open>M\<close> and \<open>butlast M\<close>; transfer left-minimality.\<close>
    have lmin: "\<And>j. j < ?c \<Longrightarrow> entry (butlast M) 0 j \<ge> entry (butlast M) 0 ?c"
    proof -
      fix j assume jc: "j < ?c"
      have jj1: "j < Lng M - 1" using jc ltc by simp
      have cj1': "?c < Lng M - 1" using ltc by simp
      have ej: "entry (butlast M) 0 j = entry M 0 j"
        using jj1 by (simp add: entry_def nth_butlast)
      have ec: "entry (butlast M) 0 ?c = entry M 0 ?c"
        using cj1' by (simp add: entry_def nth_butlast)
      have "entry M 0 j \<ge> entry M 0 ?c"
        using P_add_Pcut_left_min[OF M multi L] jc by simp
      thus "entry (butlast M) 0 j \<ge> entry (butlast M) 0 ?c" using ej ec by simp
    qed
    \<comment> \<open>Apply \<open>P\<close>-additivity to \<open>butlast M\<close> at the cut \<open>?c\<close>.\<close>
    have add: "P (butlast M) = P (take ?c (butlast M)) @ P (drop ?c (butlast M))"
    proof -
      have "P (butlast M) =
              P (seg (butlast M) 0 (?c - 1)) @ P (seg (butlast M) ?c (Lng (butlast M) - 1))"
        by (rule m_6_2_P_additive[OF blT c0 c_bl lmin])
      moreover have "seg (butlast M) 0 (?c - 1) = take ?c (butlast M)"
        using c0 c_bl by (subst P_add_seg_0_eq_take) auto
      moreover have "seg (butlast M) ?c (Lng (butlast M) - 1) = drop ?c (butlast M)"
        using c0 c_bl by (subst P_add_seg_to_last_eq_drop) auto
      ultimately show ?thesis by simp
    qed
    \<comment> \<open>\<open>take ?c (butlast M) = take ?c M\<close> and \<open>drop ?c (butlast M) = butlast (drop ?c M)\<close>.\<close>
    have minc: "min ?c (Lng M - Suc 0) = ?c" using cj1 by simp
    have tk: "take ?c (butlast M) = take ?c M"
      by (simp add: butlast_conv_take take_take minc)
    have dr: "drop ?c (butlast M) = butlast (drop ?c M)"
      by (simp add: butlast_drop)
    \<comment> \<open>\<open>drop ?c M\<close> is mono; its \<open>butlast\<close> is non-multi, so \<open>P\<close> of it is the singleton.\<close>
    have monoN: "monoT (drop ?c M)"
    proof -
      have "monoT (seg M ?c ?j1)" by (rule m_6_2_mono_ancestor_slice[OF M ltc lec])
      thus ?thesis using drop_eq_seg[OF cL] by simp
    qed
    have Pbl_drop: "P (butlast (drop ?c M)) = [butlast (drop ?c M)]"
    proof (cases "1 < Lng (drop ?c M) - 1")
      case True
      \<comment> \<open>\<open>butlast (drop ?c M) = seg (drop ?c M) 0 (Lng (drop ?c M) - 2)\<close> is mono.\<close>
      have NT: "drop ?c M \<in> PT_PS"
      proof -
        have "drop ?c M \<noteq> []" using cL by (cases "drop ?c M") auto
        thus ?thesis using monoN by (simp add: PT_PS_def T_PS_def)
      qed
      have Lge2: "2 \<le> Lng (drop ?c M)" using True by simp
      have j0lt: "Lng (drop ?c M) - 2 < Lng (drop ?c M)" using True by simp
      have j0pos: "0 < Lng (drop ?c M) - 2" using True by simp
      have "monoT (seg (drop ?c M) 0 (Lng (drop ?c M) - 2))"
        by (rule m_6_2_mono_prefix[OF NT j0pos j0lt])
      moreover have "seg (drop ?c M) 0 (Lng (drop ?c M) - 2) = butlast (drop ?c M)"
      proof -
        have suc: "Suc (Lng (drop ?c M) - 2) \<le> Lng (drop ?c M)" using Lge2 by simp
        have "seg (drop ?c M) 0 (Lng (drop ?c M) - 2)
                = take (Suc (Lng (drop ?c M) - 2)) (drop ?c M)"
          by (rule seg_0_eq_take[OF suc])
        also have "Suc (Lng (drop ?c M) - 2) = Lng (drop ?c M) - 1" using Lge2 by simp
        also have "take (Lng (drop ?c M) - 1) (drop ?c M) = butlast (drop ?c M)"
          by (simp add: butlast_conv_take)
        finally show ?thesis .
      qed
      ultimately have "monoT (butlast (drop ?c M))" by simp
      hence "\<not> multiT (butlast (drop ?c M))" by (simp add: multiT_def)
      thus ?thesis by (subst P.simps) simp
    next
      case False
      \<comment> \<open>\<open>Lng (drop ?c M) = 2\<close>, so \<open>butlast (drop ?c M)\<close> has length 1: non-multi.\<close>
      have "2 \<le> Lng (drop ?c M)" using lenNgt1 lastPM by simp
      hence Lbn: "Lng (butlast (drop ?c M)) = 1" using False by simp
      have "\<not> multiT (butlast (drop ?c M))"
      proof (cases "zeroT (butlast (drop ?c M))")
        case True thus ?thesis by (simp add: multiT_def)
      next
        case False
        have "monoT (butlast (drop ?c M))"
          using Lbn False by (simp add: monoT_def leR_def le0_def)
        thus ?thesis by (simp add: multiT_def)
      qed
      thus ?thesis by (subst P.simps) simp
    qed
    \<comment> \<open>Assemble.\<close>
    have "P (Pred M) = P (butlast M)" using predM by simp
    also have "\<dots> = P (take ?c M) @ P (butlast (drop ?c M))"
      using add tk dr by simp
    also have "\<dots> = butlast (P M) @ [butlast (drop ?c M)]"
      using butlastPM Pbl_drop by simp
    also have "\<dots> = butlast (P M) @ [Pred (last (P M))]"
    proof -
      have "Pred (last (P M)) = butlast (drop ?c M)"
        using lastPM lenNgt1 lenN by (simp add: Pred_def)
      thus ?thesis by simp
    qed
    finally show ?thesis using lenNgt1 by simp
  qed
qed



(* ===== Red_Pred helper block from workflow predh-T2 ===== *)
subsection \<open>T2: \<open>diagSeq\<close> butlast arithmetic and \<open>Red\<close> of a core diagonal\<close>

text \<open>T2(i): the last pair of a diagonal segment is just the top of the range, so
  \<open>butlast (diagSeq a b) = diagSeq a (b - 1)\<close> for \<open>a \<le> b\<close> and \<open>0 < b\<close>.  (The
  positivity is essential: at \<open>b = 0\<close> the nat-subtraction \<open>0 - 1 = 0\<close> would make
  the RHS \<open>diagSeq a 0 = [(a,a)]\<close> while the LHS is \<open>[]\<close>.)  Generalizes
  @{thm [source] diagSeq_Suc_snoc}/@{thm [source] Pred_diagSeq_Suc} to a plain
  predecessor of the upper bound.\<close>

lemma butlast_diagSeq:
  assumes ab: "a \<le> b" and bpos: "0 < b"
  shows "butlast (diagSeq a b) = diagSeq a (b - 1)"
proof -
  obtain c where bc: "b = Suc c" using bpos by (cases b) auto
  \<comment> \<open>\<open>butlast\<close> commutes with \<open>map\<close>; \<open>[a..<Suc b] = [a..<b] @ [b]\<close> (as \<open>a \<le> b\<close>),
     so its \<open>butlast\<close> is \<open>[a..<b]\<close>.\<close>
  have "butlast (diagSeq a b) = map (\<lambda>j. (j, j)) (butlast [a..<Suc b])"
    by (simp add: diagSeq_def map_butlast)
  also have "butlast [a..<Suc b] = butlast ([a..<b] @ [b])"
    by (simp only: upt_Suc_append[OF ab])
  also have "\<dots> = [a..<b]" by simp
  finally show ?thesis using bc by (simp add: diagSeq_def del: upt_Suc)
qed

text \<open>A core diagonal \<open>diagSeq 0 v\<close> is in \<open>T\<^sub>PS\<close> (it is a nonempty pair sequence).\<close>

lemma diagSeq_in_T_PS:
  assumes uv: "u \<le> v"
  shows "diagSeq u v \<in> T_PS"
  using uv by (simp add: T_PS_def diagSeq_def del: upt_Suc)

text \<open>T2 core: \<open>Red\<close> fixes a core diagonal: \<open>Red (diagSeq 0 v) = diagSeq 0 v\<close>.
  The \<open>v = 0\<close> case is the zero term (\<open>Red = [(0,0)] = diagSeq 0 0\<close>); for \<open>v > 0\<close>
  the sequence is mono, non-multi, core (\<open>m\<^sub>0\<^sub>0 = m\<^sub>1\<^sub>0 = 0\<close>), with
  \<open>TrMax = Lng - 1\<close>, hitting branch 3a of @{const Red}, which returns
  \<open>diagSeq m\<^sub>1\<^sub>0 (m\<^sub>1\<^sub>0 + (Lng-1)) = diagSeq 0 v\<close>.\<close>

lemma Red_core_diagSeq:
  shows "Red (diagSeq 0 v) = diagSeq 0 v"
proof -
  let ?M = "diagSeq 0 v"
  have MT: "?M \<in> T_PS" by (rule diagSeq_in_T_PS) simp
  have dom: "Red_dom ?M" by (rule m_6_5_Red_welldef[OF MT])
  have LM: "Lng ?M = Suc v" by simp
  have m00: "entry ?M 0 0 = 0" by (simp add: entry_diagSeq)
  have m10: "entry ?M 1 0 = 0" by (simp add: entry_diagSeq)
  show ?thesis
  proof (cases v)
    case 0
    \<comment> \<open>\<open>diagSeq 0 0 = [(0,0)]\<close> is a zero term.\<close>
    have z: "zeroT ?M" using 0 m10 by (simp add: zeroT_def)
    have "Red ?M = [(0, 0)]" using Red.psimps[OF dom] z by simp
    also have "\<dots> = diagSeq 0 v" using 0 by (simp add: diagSeq_def)
    finally show ?thesis .
  next
    case (Suc w)
    have vpos: "0 < v" using Suc by simp
    have Lgt1: "1 < Lng ?M" using LM Suc by simp
    have nz: "\<not> zeroT ?M" using Lgt1 by (simp add: zeroT_def)
    have zv: "(0::nat) \<le> v" by simp
    have nmu: "\<not> multiT ?M" by (rule not_multiT_diagSeq[OF zv])
    \<comment> \<open>\<open>TrMax = v = Lng - 1\<close> (branch 3a guard \<open>j\<^sub>1' = j\<^sub>1\<close>).\<close>
    have tr: "TrMax ?M = Lng ?M - 1"
      using TrMax_diagSeq[OF zv] LM by simp
    have c0: "entry ?M 0 0 = 0" by (rule m00)
    have c1: "entry ?M 1 0 = 0" by (rule m10)
    have rM: "Red ?M = diagSeq (entry ?M 1 0) (entry ?M 1 0 + (Lng ?M - 1))"
      using Red.psimps[OF dom] nz nmu c0 c1 tr by (simp add: Let_def)
    also have "\<dots> = diagSeq 0 v" using c1 LM by simp
    finally show ?thesis .
  qed
qed

end
