theory Frontier_6_027
  imports P_6_8_standard_P_descending
begin

text \<open>§6.8 prop1 build-up.  Row-generic version of
  @{thm [source] entry_FirstNodes_eq_component}: the \<open>(i,0)\<close> entry of the \<open>J\<close>-th
  branch component equals \<open>M\<close>'s \<open>(i, FirstNodes M ! J)\<close> entry (same proof, since
  @{thm [source] entry_seg} is row-generic).  Needed for the row-1 tie-break of
  \<open>Br\<close> components.\<close>

lemma entry_FirstNodes_eq_component_gen:
  assumes M: "M \<in> PT_PS" and J: "J < length (Br M)"
  shows "entry M i (FirstNodes M ! J) = entry (Br M ! J) i 0"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
  have trne: "TrMax M \<noteq> Lng M - 1"
  proof
    assume "TrMax M = Lng M - 1"
    hence "Br M = []" by (simp add: Br_def)
    with J show False by simp
  qed
  with tb have trlt: "TrMax M < Lng M - 1" by linarith
  let ?N = "seg M (TrMax M + 1) (Lng M - 1)"
  have brQ: "Br M = P ?N" using trne by (simp add: Br_def)
  have NLpos: "Lng ?N > 0" using trlt by simp
  have Nne: "?N \<noteq> []" using NLpos length_greater_0_conv by blast
  have NT: "?N \<in> T_PS" using Nne by (simp add: T_PS_def)
  have JN: "J < length (P ?N)" using J brQ by simp
  have Jle: "J \<le> Lng (P ?N) - 1" using JN by (cases "P ?N") auto
  have comp: "(P ?N) ! J = seg ?N (IdxSum (P ?N) ! J) (IdxSum (P ?N) ! (J + 1) - 1)"
    by (rule m_6_4_P_IdxSum[OF NT Jle])
  have lenpos: "0 < Lng ((P ?N) ! J)"
    by (rule idxsum_P_component_nonempty[OF NT JN])
  have e_comp: "entry ((P ?N) ! J) i 0 = entry ?N i (IdxSum (P ?N) ! J)"
  proof -
    have lp: "0 < Lng (seg ?N (IdxSum (P ?N) ! J) (IdxSum (P ?N) ! (J + 1) - 1))"
      using lenpos by (simp only: comp[symmetric])
    have "entry (seg ?N (IdxSum (P ?N) ! J) (IdxSum (P ?N) ! (J + 1) - 1)) i 0
         = entry ?N i ((IdxSum (P ?N) ! J) + 0)"
      by (rule entry_seg[OF lp])
    thus ?thesis using comp by simp
  qed
  have idxbound: "IdxSum (P ?N) ! J \<le> Lng ?N - 1"
    using idxsum_leftend_lmin[OF NT JN] by blast
  hence idxlt: "IdxSum (P ?N) ! J < Lng ?N" using NLpos by simp
  have e_N: "entry ?N i (IdxSum (P ?N) ! J)
           = entry M i (TrMax M + 1 + IdxSum (P ?N) ! J)"
    using idxlt by (simp add: entry_seg)
  have fn: "FirstNodes M ! J = TrMax M + 1 + IdxSum (Br M) ! J"
    by (rule FirstNodes_nth[OF J])
  show ?thesis using e_comp e_N fn brQ by simp
qed

text \<open>A slice of a slice is a slice: \<open>seg (seg M a b) c d = seg M (a+c) (a+d)\<close>
  when \<open>d \<le> b - a\<close> (so the inner indices stay in range).  Lets the branch
  segment of a slice be viewed as a slice of the ambient \<open>M\<close>.\<close>

lemma seg_nth_eq:
  assumes k: "k < Suc y - x"
  shows "seg M x y ! k = M ! (x + k)"
  unfolding seg_def by (rule nth_map_upt[OF k])

lemma seg_of_seg:
  assumes ab: "a \<le> b" and db: "d \<le> b - a"
  shows "seg (seg M a b) c d = seg M (a + c) (a + d)"
proof (rule nth_equalityI)
  have l1: "length (seg (seg M a b) c d) = Suc d - c" by simp
  have l2: "length (seg M (a + c) (a + d)) = Suc (a + d) - (a + c)" by simp
  show leq: "length (seg (seg M a b) c d) = length (seg M (a + c) (a + d))"
    using l1 l2 by presburger
  fix i assume "i < length (seg (seg M a b) c d)"
  hence ic: "i < Suc d - c" by simp
  have ciba: "c + i < Suc b - a" using ic db ab by presburger
  have icd: "i < Suc (a + d) - (a + c)" using ic by presburger
  have "seg (seg M a b) c d ! i = seg M a b ! (c + i)" using ic by (rule seg_nth_eq)
  also have "\<dots> = M ! (a + (c + i))" using ciba by (rule seg_nth_eq)
  also have "a + (c + i) = (a + c) + i" by simp
  finally have lhs: "seg (seg M a b) c d ! i = M ! ((a + c) + i)" .
  have "seg M (a + c) (a + d) ! i = M ! ((a + c) + i)" using icd by (rule seg_nth_eq)
  thus "seg (seg M a b) c d ! i = seg M (a + c) (a + d) ! i" using lhs by simp
qed

end
