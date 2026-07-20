theory Support_6_067
  imports Frontier_6_088
begin

lemma coreReduce_trunk_e1:
  assumes MT: "M \<in> T_PS" and condA: "RedCondA M" and mono: "monoT M"
    and pos: "0 < entry M 1 0"
    and ple: "p \<le> TrMax (diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ entry M 1 0) M)"
  shows "entry (diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ entry M 1 0) M) 1 p = p"
proof -
  let ?m = "entry M 1 0"
  let ?A = "diagSeq 0 (?m - 1) @ (IncrFirst ^^ ?m) M"
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have LMpos: "0 < Lng M" using Mne by (cases M) auto
  have Ld: "Lng (diagSeq 0 (?m - 1)) = ?m" using pos by (simp del: upt_Suc)
  have trA: "TrMax ?A = ?m + TrMax M" by (rule TrMax_coreReduce[OF MT condA mono pos])
  show ?thesis
  proof (cases "p < ?m")
    case True
    have "?A ! p = diagSeq 0 (?m - 1) ! p" using True Ld by (simp add: nth_append)
    also have "\<dots> = (p, p)" using True pos by (simp add: diagSeq_def del: upt_Suc)
    finally show ?thesis by (simp add: entry_def)
  next
    case False
    define k where "k = p - ?m"
    have pk: "p = ?m + k" using False k_def by simp
    have kTr: "k \<le> TrMax M" using ple trA pk by simp
    have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
    have kM: "k < Lng M" using kTr tb LMpos by linarith
    have "?A ! p = ((IncrFirst ^^ ?m) M) ! k" using pk Ld by (simp add: nth_append)
    hence "entry ?A 1 p = entry ((IncrFirst ^^ ?m) M) 1 k" by (simp add: entry_def)
    also have "\<dots> = entry M 1 k" by (rule entry_funpow_IncrFirst1[OF kM])
    also have "\<dots> = ?m + k"
      using trunk_entries_offset[OF MT condA kTr] by simp
    finally show ?thesis using pk by simp
  qed
qed

end
