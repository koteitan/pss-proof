theory Support_6_008
  imports Frontier_6_025
begin

lemma ST_PS_seg_0_aux:
  assumes MST: "M \<in> ST_PS" and j1'le: "j1' \<le> Lng M - 1"
  shows "seg M 0 j1' \<in> ST_PS"
proof -
  have h: "\<forall>M' j1''. M' \<in> ST_PS \<longrightarrow> j1'' \<le> Lng M' - 1 \<longrightarrow>
                Lng M' - 1 - j1'' = Lng M - 1 - j1' \<longrightarrow> seg M' 0 j1'' \<in> ST_PS"
    using ST_PS_seg_0_inner by blast
  have deq: "Lng M - 1 - j1' = Lng M - 1 - j1'" by simp
  show ?thesis using h[rule_format, OF MST j1'le deq] .
qed

end
