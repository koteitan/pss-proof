theory Frontier_7_037
  imports Support_7_031
begin

\<comment> \<open>§7.4 monoT interior core (Step 3) green; takes ihPred + markShift (IH-ready).\<close>


section \<open>§7.4 keystone, monoT-interior markShift discharge (Step 2)\<close>

text \<open>\<open>IncrFirst\<close> is a \<open>map\<close>, so \<open>(IncrFirst^^k) M\<close> is the map that adds \<open>k\<close> to
  every top-row entry.\<close>

lemma funpow_IncrFirst_map:
  "(IncrFirst ^^ k) M = map (\<lambda>p. (k + fst p, snd p)) M"
proof (induction k)
  case 0 thus ?case by (simp add: map_idI)
next
  case (Suc k)
  have "(IncrFirst ^^ Suc k) M = IncrFirst ((IncrFirst ^^ k) M)" by simp
  also have "\<dots> = IncrFirst (map (\<lambda>p. (k + fst p, snd p)) M)" using Suc by simp
  also have "\<dots> = map (\<lambda>p. (Suc (fst p), snd p)) (map (\<lambda>p. (k + fst p, snd p)) M)"
    by (simp add: IncrFirst_def)
  also have "\<dots> = map (\<lambda>p. (Suc k + fst p, snd p)) M" by (simp add: o_def)
  finally show ?case .
qed

text \<open>\<open>seg\<close> commutes with \<open>(IncrFirst^^k)\<close> when the endpoint is in range
  (both are maps over the index slice).\<close>

lemma seg_funpow_IncrFirst:
  assumes "b < Lng M"
  shows "seg ((IncrFirst ^^ k) M) a b = (IncrFirst ^^ k) (seg M a b)"
proof -
  let ?f = "\<lambda>p. (k + fst p, snd p)"
  have IM: "(IncrFirst ^^ k) M = map ?f M" by (rule funpow_IncrFirst_map)
  have IS: "(IncrFirst ^^ k) (seg M a b) = map ?f (seg M a b)" by (rule funpow_IncrFirst_map)
  have "seg ((IncrFirst ^^ k) M) a b = map (\<lambda>j. ((IncrFirst ^^ k) M) ! j) [a..<Suc b]"
    by (simp add: seg_def)
  also have "\<dots> = map (\<lambda>j. ?f (M ! j)) [a..<Suc b]"
  proof (rule map_cong[OF refl])
    fix j assume "j \<in> set [a..<Suc b]"
    hence "j < Suc b" by auto
    hence "j < Lng M" using assms by simp
    thus "((IncrFirst ^^ k) M) ! j = ?f (M ! j)" using IM by simp
  qed
  also have "\<dots> = map ?f (map (\<lambda>j. M ! j) [a..<Suc b])" by simp
  also have "\<dots> = map ?f (seg M a b)" by (simp add: seg_def)
  also have "\<dots> = (IncrFirst ^^ k) (seg M a b)" using IS by simp
  finally show ?thesis .
qed

end
