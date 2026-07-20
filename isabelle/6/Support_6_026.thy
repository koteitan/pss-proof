theory Support_6_026
  imports Frontier_6_043
begin

text \<open>(2) @{const Br} is the @{const IncrFirst}-image of \<open>crM\<close>'s branches;
  in particular it has the same length and per-block lengths.\<close>

lemma njA_Br_eq:
  assumes T: "M \<in> T_PS" and mono: "monoT M" and pos: "0 < entry M 1 0"
  shows "Br (coreReduce (IncrFirst M)) = map IncrFirst (Br (coreReduce M))"
proof -
  let ?A = "coreReduce (IncrFirst M)"
  let ?X = "coreReduce M"
  have trEq: "TrMax ?A = TrMax ?X" by (rule njA_TrMax_eq[OF T pos])
  have lenEq: "Lng ?A = Lng ?X"
    using tail_bump.len_eq[OF tail_bump_coreReduce[OF T pos]] .
  show ?thesis
  proof (cases "TrMax ?X = Lng ?X - 1")
    case True
    hence "Br ?A = []" "Br ?X = []" using trEq lenEq by (simp_all add: Br_def)
    thus ?thesis by simp
  next
    case False
    have ag: "entry M 1 0 \<le> TrMax ?X" by (rule njA_TrMax_ge_m10[OF T pos])
    have age: "entry M 1 0 \<le> TrMax ?X + 1" using ag by simp
    have Lpos: "0 < Lng ?X"
    proof -
      have "coreReduce M = diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ (entry M 1 0)) M"
        by (rule coreReduce_m10pos_form[OF pos])
      thus ?thesis using pos by simp
    qed
    have bb: "Lng ?X - 1 < Lng ?X" using Lpos by simp
    have segEq: "seg ?A (TrMax ?X + 1) (Lng ?X - 1)
               = IncrFirst (seg ?X (TrMax ?X + 1) (Lng ?X - 1))"
      by (rule njA_seg_IncrFirst[OF T pos age bb])
    have "Br ?A = P (seg ?A (TrMax ?A + 1) (Lng ?A - 1))"
      using False trEq lenEq by (simp add: Br_def)
    also have "\<dots> = P (seg ?A (TrMax ?X + 1) (Lng ?X - 1))" using trEq lenEq by simp
    also have "\<dots> = P (IncrFirst (seg ?X (TrMax ?X + 1) (Lng ?X - 1)))" using segEq by simp
    also have "\<dots> = map IncrFirst (P (seg ?X (TrMax ?X + 1) (Lng ?X - 1)))"
      by (rule m_6_2_P_IncrFirst)
    also have "\<dots> = map IncrFirst (Br ?X)" using False by (simp add: Br_def)
    finally show ?thesis .
  qed
qed

end
