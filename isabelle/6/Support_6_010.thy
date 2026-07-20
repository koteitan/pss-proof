theory Support_6_010
  imports Frontier_6_027
begin

text \<open>§6.8 prop1 — reduction of the hard core to a single-index «suffix» form.
  Any slice \<open>seg M a b\<close> of a standard \<open>M\<close> is the suffix \<open>drop a N\<close> of the
  standard prefix \<open>N = seg M 0 b\<close> (@{thm [source] m_6_7_standard_prefix}).  Hence
  the slice statement \<open>slice_P_descending\<close> (\<open>descending (P (seg M a b))\<close> for all
  \<open>a \<le> b \<le> Lng M - 1\<close>) follows from the cleaner single-index statement
  \<open>descending (P (drop j N))\<close> for every standard \<open>N\<close> and every \<open>j\<close>.  This is the
  remaining hard core; see \<open>docs/slice-Br-descending.md\<close>.\<close>

lemma slice_P_descending_of_drop:
  assumes core: "\<And>N j. N \<in> ST_PS \<Longrightarrow> descending (P (drop j N))"
    and M: "M \<in> ST_PS" and ab: "a \<le> b" and bM: "b \<le> Lng M - 1"
  shows "descending (P (seg M a b))"
proof -
  let ?N = "seg M 0 b"
  have N: "?N \<in> ST_PS" by (rule m_6_7_standard_prefix[OF M bM])
  have lenN: "Lng ?N = Suc b" by simp
  have NLpos: "Lng ?N > 0" by simp
  have sl: "seg ?N a b = seg M a b"
    using seg_of_seg[where M=M and a=0 and b=b and c=a and d=b] by simp
  have "seg M a b = seg ?N a (Lng ?N - 1)" using sl lenN by simp
  also have "\<dots> = drop a ?N" by (rule seg_to_last_eq_drop[OF NLpos])
  finally have eq: "seg M a b = drop a ?N" .
  show ?thesis using core[OF N, of a] eq by simp
qed

text \<open>§6.8 prop1 assembly.  Given the core \<open>descending (P (drop j N))\<close> for all
  standard \<open>N\<close>, the full proposition \<open>p_6_8_standard_slice_Br_descending\<close>
  follows: the \<open>monoT\<close> part is @{thm [source] m_6_2_mono_ancestor_slice} (free),
  and \<open>descending (Br (seg M j0' j1'))\<close> reduces — via the branch segment being a
  further slice of \<open>M\<close> (@{thm [source] seg_of_seg}) — to
  @{thm [source] slice_P_descending_of_drop}.\<close>

lemma m_6_8_standard_slice_Br_descending_of_drop:
  assumes core: "\<And>N j. N \<in> ST_PS \<Longrightarrow> descending (P (drop j N))"
    and M: "M \<in> ST_PS" and lt: "j0' < j1'" and j1: "j1' \<le> Lng M - 1"
    and leR: "leR M 0 j0' j1'"
  shows "monoT (seg M j0' j1') \<and> descending (Br (seg M j0' j1'))"
proof
  have MT: "M \<in> T_PS" using M ST_PS_T_PS by blast
  show mono: "monoT (seg M j0' j1')"
    by (rule m_6_2_mono_ancestor_slice[OF MT lt leR])
  let ?M' = "seg M j0' j1'"
  have lenM': "Lng ?M' = Suc j1' - j0'" by (rule Lng_seg)
  show "descending (Br ?M')"
  proof (cases "Br ?M' = []")
    case True thus ?thesis by (simp add: descending_def)
  next
    case False
    have M'T: "?M' \<in> T_PS"
    proof -
      have "Lng ?M' > 0" using lt by simp
      thus ?thesis by (cases ?M') (auto simp: T_PS_def)
    qed
    have tb: "TrMax ?M' \<le> Lng ?M' - 1" by (rule TrMax_bound[OF M'T])
    have trne: "TrMax ?M' \<noteq> Lng ?M' - 1"
    proof
      assume "TrMax ?M' = Lng ?M' - 1"
      hence "Br ?M' = []" by (simp add: Br_def)
      with False show False by simp
    qed
    from trne tb have trlt: "TrMax ?M' < Lng ?M' - 1" by linarith
    let ?c = "TrMax ?M' + 1" and ?e = "Lng ?M' - 1"
    have brQ: "Br ?M' = P (seg ?M' ?c ?e)" using trne by (simp add: Br_def)
    \<comment> \<open>the branch segment is itself a slice of the ambient \<open>M\<close>\<close>
    have dle: "?e \<le> j1' - j0'" using lenM' lt by linarith
    have seg2: "seg ?M' ?c ?e = seg M (j0' + ?c) (j0' + ?e)"
      using seg_of_seg[where M=M and a=j0' and b=j1' and c="?c" and d="?e"] lt dle
      by simp
    have aleb: "j0' + ?c \<le> j0' + ?e" using trlt by linarith
    have bleM: "j0' + ?e \<le> Lng M - 1" using lenM' lt j1 by linarith
    have "descending (P (seg M (j0' + ?c) (j0' + ?e)))"
      by (rule slice_P_descending_of_drop[OF core M aleb bleM])
    thus ?thesis using brQ seg2 by simp
  qed
qed

end
