theory Support_6_069
  imports Frontier_6_090
begin

lemma m_6_5_congR_self_Red_monoT:
  assumes MT: "M \<in> T_PS" and condA: "RedCondA M" and mono: "monoT M"
  shows "congR M (Red M)"
proof -
  let ?m = "entry M 1 0"  let ?c0 = "entry M 0 0"
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  have red: "Red M = map (\<lambda>j. (entry M 0 j - ?c0 + ?m, entry M 1 j)) [0..<Lng M]"
    by (rule m_6_5_Red_rebase[OF MT condA nmu])
  have redmap: "Red M = map (\<lambda>p. (fst p - ?c0 + ?m, snd p)) M"
    using red rebase_as_pair_map by simp
  have fcomp: "map (\<lambda>p. (fst p - ?c0 + ?m, snd p)) M = (IncrFirst ^^ ?m) (shiftRow0 M)"
  proof -
    have sh: "shiftRow0 M = map (\<lambda>p. (fst p - ?c0, snd p)) M"
      using rebase_as_pair_map[of M ?c0 0] by (simp add: shiftRow0_def)
    have "(IncrFirst ^^ ?m) (shiftRow0 M)
          = map (\<lambda>p. (fst p + ?m, snd p)) (map (\<lambda>p. (fst p - ?c0, snd p)) M)"
      using sh funpow_IncrFirst_as_map by simp
    also have "\<dots> = map (\<lambda>p. (fst p - ?c0 + ?m, snd p)) M" by simp
    finally show ?thesis by simp
  qed
  have c1: "congR M (shiftRow0 M)" by (rule congR_self_shiftRow0[OF MT mono])
  have c2: "congR (shiftRow0 M) ((IncrFirst ^^ ?m) (shiftRow0 M))"
    by (rule congR_self_funpow_IncrFirst)
  have "congR M ((IncrFirst ^^ ?m) (shiftRow0 M))" by (rule congR_trans[OF c1 c2])
  thus ?thesis using redmap fcomp by simp
qed

end
