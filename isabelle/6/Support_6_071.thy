theory Support_6_071
  imports P_6_5_P_Red
begin

section \<open>§6.5 命題（\<open>Red\<close>が許容性を保つこと）/ 系（許容化の\<open>Red\<close>不変性）/
  系（\<open>Red\<close>が基点を保つこと） — A4 final forms\<close>

text \<open>The unified anchored self-congruence: \<open>congR M (Red M)\<close> for any anchored
  slice (the \<open>zeroT\<close> branch is immediate from \<open>Red M = [(0,0)]\<close>; the \<open>monoT\<close>
  branch is @{thm [source] m_6_5_congR_self_Red_monoT} with \<open>RedCondA\<close> supplied
  by the anchored characterization).  Since \<open>nadm\<close>/\<open>adm\<close>/\<open>AdmSet\<close>/\<open>Adm\<close> depend
  only on \<open>Lng\<close> and \<open>nextR\<close>, all admissibility notions transfer along \<open>congR\<close>.
  Empirically: AdmSet equality + Marked transfer 0/432 anchored slices.\<close>

lemma m_6_5_congR_self_Red_anchored:
  assumes M: "M \<in> anchored_slice"
  shows "congR M (Red M)"
proof -
  have MT: "M \<in> T_PS" by (rule anchored_slice_imp_T_PS[OF M])
  show ?thesis
  proof (cases "zeroT M")
    case True
    have domM: "Red_dom M" by (rule m_6_5_Red_welldef[OF MT])
    have rM: "Red M = [(0, 0)]" using Red.psimps[OF domM] True by simp
    have L1: "Lng M = 1" using True by (simp add: zeroT_def)
    have e1: "entry M 1 0 = 0" using True by (simp add: zeroT_def)
    have n0: "nextrel0 M = nextrel0 [(0, 0)]"
      by (rule ext, rule ext) (auto simp: nextrel0_def L1)
    show ?thesis using L1 e1 n0 by (simp add: rM congR_def entry_def)
  next
    case False
    hence mono: "monoT M" using m_6_5_anchored_zeroT_or_monoT[OF M] by simp
    have condA: "RedCondA M"
      by (rule m_6_5_anchored_imp_RedCondA[OF M stdCA_ST_PS])
    show ?thesis by (rule m_6_5_congR_self_Red_monoT[OF MT condA mono])
  qed
qed

lemma m_6_5_adm_Red_eq:
  assumes M: "M \<in> anchored_slice"
  shows "adm M = adm (Red M)"
proof -
  have c: "congR M (Red M)" by (rule m_6_5_congR_self_Red_anchored[OF M])
  have L: "Lng M = Lng (Red M)" by (rule congR_Lng[OF c])
  have n: "nextR M = nextR (Red M)" by (rule congR_nextR[OF c])
  show ?thesis by (rule ext) (simp add: adm_def nadm_def L n)
qed

end
