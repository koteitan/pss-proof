theory Frontier_7_032
  imports Support_7_026
begin

text \<open>The marked image at a positive column \<open>m > 0\<close> differs from the marked image
  at column \<open>0\<close> (which is \<open>Trans M\<close>, @{thm [source] ra_Mark0_eq_Trans}).  At
  column \<open>0\<close> the sequence is \<open>monoT\<close>, so \<open>RightNodes (Trans M)\<close> has length \<open>\<ge> 2\<close>
  (@{thm [source] Trans_mono_RN_ge2}); for \<open>0 < m\<close> the interior case strictly
  shrinks the right-spine and the rightmost case has length \<open>1\<close>, so they cannot
  coincide.\<close>

lemma Mark0_ne_Mark:
  assumes MR: "M \<in> RT_PS" and m0M: "(M, 0) \<in> Marked" and mM: "(M, m) \<in> Marked"
    and pos: "0 < m"
  shows "Mark M m \<noteq> Trans M"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have le00: "leR M 0 0 (Lng M - 1)" using m0M by (simp add: Marked_def)
  have lem: "leR M 0 m (Lng M - 1)" using mM by (simp add: Marked_def)
  have mlt: "m < Lng M" using lem by (simp add: leR_def le0_def)
  have mle: "m \<le> Lng M - 1" using mlt by linarith
  have L: "1 < Lng M" using pos mlt by linarith
  have nzM: "\<not> zeroT M" using L by (auto simp: zeroT_def)
  have monoM: "monoT M" using nzM le00 by (simp add: monoT_def)
  \<comment> \<open>\<open>Mark M 0 = Trans M\<close>\<close>
  have mk0: "Mark M 0 = Trans M"
    using ra_Mark0_eq_Trans[THEN mp, THEN mp, OF m0M MR] .
  have rnTM: "2 \<le> length (RightNodes (Trans M))"
    by (rule Trans_mono_RN_ge2[OF MR monoM L])
  show ?thesis
  proof (cases "m < Lng M - 1")
    case True
    \<comment> \<open>interior: \<open>RightNodes (Mark M m)\<close> shorter than \<open>RightNodes (Trans M)\<close>\<close>
    obtain a0 a1 where
          RT: "RightNodes (Trans M) = a0 @ [entry M 1 m] @ a1"
      and Sseg: "RightNodes (Trans (seg M 0 m)) = a0 @ [entry M 1 m]"
      and RMark: "RightNodes (Mark M m) = [entry M 1 m] @ a1"
      using m_7_4_RightNodes_Mark[OF mM MR pos True] by blast
    \<comment> \<open>\<open>seg M 0 m\<close> is mono reduced of length \<open>m+1 \<ge> 2\<close>, so its \<open>Trans\<close> has \<open>RightNodes \<ge> 2\<close>\<close>
    have segRT: "seg M 0 m \<in> RT_PS" by (rule seg_0_RT_PS[OF MR mle])
    have segm0: "(seg M 0 m, 0) \<in> Marked"
    proof -
      have "(seg M 0 m, (0::nat) - 0) \<in> Marked"
        by (rule m_6_3_marked_slice[OF m0M]) (use pos mle in auto)
      thus ?thesis by simp
    qed
    have Lseg: "Lng (seg M 0 m) = Suc m" using mlt by simp
    have segL: "1 < Lng (seg M 0 m)" using pos Lseg by simp
    have segnz: "\<not> zeroT (seg M 0 m)" using segL by (auto simp: zeroT_def)
    have segle00: "leR (seg M 0 m) 0 0 (Lng (seg M 0 m) - 1)"
      using segm0 by (simp add: Marked_def)
    have segmono: "monoT (seg M 0 m)" using segnz segle00 by (simp add: monoT_def)
    have rnseg: "2 \<le> length (RightNodes (Trans (seg M 0 m)))"
      by (rule Trans_mono_RN_ge2[OF segRT segmono segL])
    \<comment> \<open>\<open>RightNodes (Trans (seg M 0 m)) = a0 @ [entry M 1 m]\<close>, so \<open>a0 \<noteq> []\<close>\<close>
    have a0ne: "a0 \<noteq> []"
    proof
      assume "a0 = []"
      hence "RightNodes (Trans (seg M 0 m)) = [entry M 1 m]" using Sseg by simp
      thus False using rnseg by simp
    qed
    have lenTM: "length (RightNodes (Trans M)) = length a0 + 1 + length a1"
      using RT by simp
    have lenMark: "length (RightNodes (Mark M m)) = 1 + length a1"
      using RMark by simp
    have "length (RightNodes (Mark M m)) < length (RightNodes (Trans M))"
      using lenTM lenMark a0ne by (cases a0) auto
    thus ?thesis by auto
  next
    case False
    hence meq: "m = Lng M - 1" using mle by simp
    have "Mark M m = Dpt (enat (entry M 1 m)) 0\<^sub>B"
      using m_7_3_Mark_rightmost1[OF mM MR nzM] meq by simp
    hence "length (RightNodes (Mark M m)) = 1" by (simp add: rnsub_RightNodes_Dpt)
    thus ?thesis using rnTM by auto
  qed
qed

end
