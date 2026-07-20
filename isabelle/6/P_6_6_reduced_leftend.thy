theory P_6_6_reduced_leftend
  imports Frontier_6_061
begin

text \<open>補題（簡約性と左端の関係） — prepending a diagonal to a reduced mono sequence
  keeps it reduced and mono.\<close>

text \<open>(e) 補題（簡約性と左端の関係） — discharges \<open>p_6_6_reduced_leftend\<close>.
  Prepending a leading diagonal \<open>diagSeq u (m\<^sub>1\<^sub>0-1)\<close> (guarded: empty when
  \<open>u = m\<^sub>1\<^sub>0\<close>) to a reduced mono \<open>M\<close> keeps it reduced and mono.

  The literal article form \<open>diagSeq u (entry M 1 0 - 1) @ M\<close> degenerates to a
  spurious singleton at \<open>u = entry M 1 0\<close> with \<open>m\<^sub>1\<^sub>0 = 0\<close> (nat subtraction); the
  guarded form below is the correct/usable one and matches the green mono-half
  @{thm [source] elead_monoT_N}.

  Reduced half via @{thm [source] m_6_6_Red_diag_prefix}
  (\<open>Red(diagSeq 0 (m\<^sub>1\<^sub>0-1) @ M') = diagSeq 0 (m\<^sub>1\<^sub>0-1) @ Red M'\<close> for mono \<open>M'\<close> with
  \<open>0 < m\<^sub>1\<^sub>0 \<le> m\<^sub>0\<^sub>0\<close>), @{thm [source] ecrux_diagSeq_split} and
  \<open>Red M = M\<close>.  Mono half via @{thm [source] elead_monoT_N}.\<close>

lemma m_6_6_reduced_leftend:
  assumes M: "M \<in> RT_PS" "M \<in> PT_PS" and ule: "u \<le> entry M 1 0"
  defines "N \<equiv> (if u < entry M 1 0 then diagSeq u (entry M 1 0 - 1) else []) @ M"
  shows "Red N = N \<and> monoT N"
proof -
  let ?m10 = "entry M 1 0"
  let ?m00 = "entry M 0 0"
  let ?k = "?m10 - 1"
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have mono: "monoT M" using M by (simp add: PT_PS_def)
  have redM: "Red M = M" using M by (simp add: RT_PS_def)
  have dom: "?m10 \<le> ?m00" by (rule kst_reduced_row1_le_row0[OF M(1) mono])
  \<comment> \<open>Mono half (green brick @{thm [source] elead_monoT_N}).\<close>
  have monoN: "monoT N"
    unfolding N_def by (rule elead_monoT_N[OF MT mono dom ule])
  \<comment> \<open>Reduced half.\<close>
  have redN: "Red N = N"
  proof (cases "0 < ?m10")
    case False
    \<comment> \<open>\<open>m\<^sub>1\<^sub>0 = 0\<close>: then \<open>u \<le> 0\<close> so \<open>\<not> (u < m\<^sub>1\<^sub>0)\<close>, the guard makes \<open>N = M\<close>.\<close>
    hence m10z: "?m10 = 0" by simp
    hence "\<not> (u < ?m10)" using ule by simp
    hence NM: "N = M" unfolding N_def by simp
    show ?thesis using NM redM by simp
  next
    case True
    hence m10pos: "0 < ?m10" .
    \<comment> \<open>Auxiliary diagonal/CRUX facts shared by the two subcases.\<close>
    have AeqRedA: "Red (diagSeq 0 ?k @ M) = diagSeq 0 ?k @ M"
    proof -
      have "Red (diagSeq 0 ?k @ M) = diagSeq 0 ?k @ Red M"
        by (rule m_6_6_Red_diag_prefix[OF mono m10pos dom])
      thus ?thesis using redM by simp
    qed
    show ?thesis
    proof (cases "u < ?m10")
      case False
      \<comment> \<open>\<open>u = m\<^sub>1\<^sub>0\<close>: guard makes \<open>N = M\<close>.\<close>
      hence NM: "N = M" unfolding N_def by simp
      show ?thesis using NM redM by simp
    next
      case True
      hence upos_lt: "u < ?m10" .
      have NeqU: "N = diagSeq u ?k @ M" unfolding N_def using upos_lt by simp
      show ?thesis
      proof (cases "u = 0")
        case True
        \<comment> \<open>\<open>u = 0\<close>: \<open>N = diagSeq 0 (m\<^sub>1\<^sub>0-1) @ M\<close>; CRUX directly.\<close>
        have "N = diagSeq 0 ?k @ M" using NeqU True by simp
        thus ?thesis using AeqRedA by simp
      next
        case False
        hence upos: "0 < u" by simp
        \<comment> \<open>\<open>u > 0\<close>: prepend \<open>diagSeq 0 (u-1)\<close>; \<open>diagSeq 0 (u-1) @ N = diagSeq 0 (m\<^sub>1\<^sub>0-1) @ M = A\<close>.\<close>
        let ?A = "diagSeq 0 ?k @ M"
        have split: "diagSeq 0 (u - 1) @ diagSeq u ?k = diagSeq 0 ?k"
        proof -
          have alm: "(0::nat) \<le> u - 1" by simp
          have mb: "u - 1 < ?k" using upos upos_lt m10pos by simp
          have su: "Suc (u - 1) = u" using upos by simp
          have "diagSeq 0 (u - 1) @ diagSeq (Suc (u - 1)) ?k = diagSeq 0 ?k"
            by (rule ecrux_diagSeq_split[OF alm mb])
          thus ?thesis using su by simp
        qed
        have preNeqA: "diagSeq 0 (u - 1) @ N = ?A"
        proof -
          have "diagSeq 0 (u - 1) @ N = diagSeq 0 (u - 1) @ (diagSeq u ?k @ M)"
            using NeqU by simp
          also have "\<dots> = (diagSeq 0 (u - 1) @ diagSeq u ?k) @ M" by simp
          also have "\<dots> = diagSeq 0 ?k @ M" using split by simp
          finally show ?thesis .
        qed
        \<comment> \<open>\<open>N\<close> is mono with \<open>entry N 1 0 = u > 0\<close> and \<open>entry N 1 0 \<le> entry N 0 0\<close>; CRUX on \<open>N\<close>.\<close>
        have Nne: "N \<noteq> []"
        proof -
          have "M \<noteq> []" using MT by (simp add: T_PS_def)
          thus ?thesis using NeqU by simp
        qed
        have NT: "N \<in> T_PS" using Nne by (simp add: T_PS_def)
        have eN10: "entry N 1 0 = u"
        proof -
          have lt: "0 < Suc ?k - u" using upos_lt by simp
          have "entry (diagSeq u ?k @ M) 1 0 = u + 0"
            by (rule elead_entry_diag_append_lo[OF lt])
          thus ?thesis using NeqU by simp
        qed
        have eN00: "entry N 0 0 = u"
        proof -
          have lt: "0 < Suc ?k - u" using upos_lt by simp
          have "entry (diagSeq u ?k @ M) 0 0 = u + 0"
            by (rule elead_entry_diag_append_lo[OF lt])
          thus ?thesis using NeqU by simp
        qed
        have N10pos: "0 < entry N 1 0" using eN10 upos by simp
        have N_dom: "entry N 1 0 \<le> entry N 0 0" using eN10 eN00 by simp
        \<comment> \<open>CRUX on \<open>N\<close>: \<open>Red(diagSeq 0 (u-1) @ N) = diagSeq 0 (u-1) @ Red N\<close>.\<close>
        have cruxN: "Red (diagSeq 0 (entry N 1 0 - 1) @ N)
                       = diagSeq 0 (entry N 1 0 - 1) @ Red N"
          by (rule m_6_6_Red_diag_prefix[OF monoN N10pos N_dom])
        have crux: "Red (diagSeq 0 (u - 1) @ N) = diagSeq 0 (u - 1) @ Red N"
          using cruxN eN10 by simp
        \<comment> \<open>LHS = Red A = A = diagSeq 0 (u-1) @ N.\<close>
        have lhs: "Red (diagSeq 0 (u - 1) @ N) = diagSeq 0 (u - 1) @ N"
          using preNeqA AeqRedA by simp
        \<comment> \<open>cancel the common prefix \<open>diagSeq 0 (u-1)\<close>.\<close>
        have "diagSeq 0 (u - 1) @ Red N = diagSeq 0 (u - 1) @ N"
          using crux lhs by simp
        thus ?thesis by simp
      qed
    qed
  qed
  show ?thesis using redN monoN by simp
qed


lemma p_6_6_reduced_leftend:
  assumes "M \<in> RT_PS" "M \<in> PT_PS" "u \<le> entry M 1 0"
  defines "N \<equiv> (if u < entry M 1 0 then diagSeq u (entry M 1 0 - 1) else []) @ M"
  shows "Red N = N \<and> monoT N"
  unfolding N_def
  by (rule m_6_6_reduced_leftend[OF assms(1) assms(2) assms(3)])

end
