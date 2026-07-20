theory Frontier_7_038
  imports Support_7_032
begin

text \<open>Generic row-1 entry shift on a reduced backward slice ending at \<open>b\<close>:
  \<open>entry (Red (seg M m b)) 1 i = entry M 1 (m + i)\<close> for in-range \<open>i\<close>.
  (Same proof shape as @{thm [source] repr_entry1_shift}, but with an arbitrary
  endpoint \<open>b\<close>.)\<close>

lemma repr_entry1_shift_gen:
  assumes MR: "M \<in> RT_PS" and mb: "m < b" and bL: "b \<le> Lng M - 1"
    and leM: "leR M 0 m b"
    and il: "i < Lng (Red (seg M m b))"
  shows "entry (Red (seg M m b)) 1 i = entry M 1 (m + i)"
proof -
  let ?S = "seg M m b"  let ?N = "Red ?S"
  define k where "k = entry M 0 m - entry M 1 m"
  have segeq: "?S = (IncrFirst ^^ k) ?N"
    using m_6_6_ancestor_slice_Red_IncrFirst[OF MR mb bL leM] k_def by simp
  have LNS: "Lng ?N = Lng ?S"
    using arg_cong[OF segeq, of Lng] by (simp add: Lng_funpow_IncrFirst)
  have iN: "i < Lng ?N" using il by simp
  have iS: "i < Lng ?S" using iN LNS by simp
  have eN: "entry ?S 1 i = entry ?N 1 i"
    using segeq entry_funpow_IncrFirst1[OF iN, of k] by simp
  have eM: "entry ?S 1 i = entry M 1 (m + i)" using iS by (simp add: entry_seg)
  show ?thesis using eN eM by simp
qed

end
