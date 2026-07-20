theory Support_7_007
  imports Frontier_7_010
begin

theorem m_7_flatBT_inj:
  "flatBT t = flatBT c \<Longrightarrow> t = c"
  using flatinj_flat_inj(1) by blast

end
