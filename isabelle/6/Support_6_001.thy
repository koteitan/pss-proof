theory Support_6_001
  imports Frontier_6_002
begin

text \<open>\<open>\<not> multiT\<close> coincides with \<open>(0,0) \<le>\<^sub>M (0, Lng M - 1)\<close> (criterion (1) = (3)).\<close>

lemma m_6_2_not_multi_iff_le:
  assumes "M \<in> T_PS"
  shows "(\<not> multiT M) = leR M 0 0 (Lng M - 1)"
proof
  assume "\<not> multiT M"
  hence "zeroT M \<or> monoT M" by (simp add: multiT_def)
  thus "leR M 0 0 (Lng M - 1)"
  proof
    assume "zeroT M"
    hence "Lng M = 1" by (simp add: zeroT_def)
    thus ?thesis by (simp add: leR_def le0_def)
  next
    assume "monoT M"
    thus ?thesis by (simp add: monoT_def)
  qed
next
  assume le: "leR M 0 0 (Lng M - 1)"
  show "\<not> multiT M"
  proof (cases "zeroT M")
    case True thus ?thesis by (simp add: multiT_def)
  next
    case False
    hence "monoT M" using le by (simp add: monoT_def)
    thus ?thesis by (simp add: multiT_def)
  qed
qed

end
