theory Frontier_6_056
  imports P_6_5_Red_idem
begin

(* ===== Red_Pred (5/6 branches, conditional) from tf-a3 ===== *)

(* ===== Red_Pred assembly (workflow tf-a3) ===== *)
subsection \<open>§6.5 命題（\<open>Red\<close>と\<open>Pred\<close>の可換性）の組立て \<open>m_6_5_Red_Pred\<close>\<close>

text \<open>a3 helper: \<open>butlast\<close> of a concatenation acts on the last block.  If the
  last element of a list \<open>L\<close> of pair-sequences is non-empty, then
  \<open>butlast (concat L) = concat (butlast L) @ butlast (last L)\<close>.  This matches the
  \<open>pred_P_decomp\<close> split: when the last block has length \<open>1\<close> the trailing
  \<open>butlast (last L) = []\<close> drops the whole block; when \<open>> 1\<close> it predecessors it.\<close>

lemma a3_butlast_concat:
  assumes ne: "L \<noteq> []" and lastne: "last L \<noteq> []"
  shows "butlast (concat L) = concat (butlast L) @ butlast (last L)"
proof -
  obtain Ls lst where Lsplit: "L = Ls @ [lst]" using ne
    by (metis append_butlast_last_id)
  have lst: "lst = last L" using Lsplit by simp
  have lstne: "lst \<noteq> []" using lst lastne by simp
  have but: "butlast L = Ls" using Lsplit by simp
  have cc: "concat L = concat Ls @ lst" using Lsplit by simp
  have "butlast (concat L) = concat Ls @ butlast lst"
    using lstne cc by (simp add: butlast_append)
  thus ?thesis using but lst by simp
qed

text \<open>a3 helper: \<open>map\<close> commutes with \<open>butlast\<close> for \<open>P\<close>-blocks (just \<open>map_butlast\<close>).\<close>

lemma a3_map_butlast: "map f (butlast xs) = butlast (map f xs)"
  by (simp add: map_butlast)

text \<open>a3 helper: \<open>Pred\<close> of a length-1 reduced last block contributes nothing.  If
  \<open>Lng (last (P M)) = 1\<close> then \<open>Red (last (P M))\<close> has length 1, so its \<open>butlast\<close>
  is \<open>[]\<close>.\<close>

lemma a3_butlast_Red_len1:
  assumes "B \<in> T_PS" and "Lng B = 1"
  shows "butlast (Red B) = []"
proof -
  have "Lng (Red B) = 1" using m_6_5_Lng_Red[OF assms(1)] assms(2) by simp
  thus ?thesis by (cases "Red B") auto
qed

text \<open>a3 helper: \<open>shiftRow0\<close> commutes with \<open>Pred\<close> when \<open>Lng M > 1\<close>.  Both
  \<open>shiftRow0\<close> and \<open>Pred = butlast\<close> are per-column operations; the row-0 anchor
  \<open>entry M 0 0\<close> is unchanged by dropping the last column.\<close>

lemma a3_shiftRow0_Pred:
  assumes L: "1 < Lng M"
  shows "Pred (shiftRow0 M) = shiftRow0 (Pred M)"
proof -
  have Mne: "M \<noteq> []" using L by (cases M) auto
  have predbl: "Pred M = butlast M" using L by (simp add: Pred_def)
  have anchor: "entry (butlast M) 0 0 = entry M 0 0"
    using L by (simp add: entry_def nth_butlast)
  have LshM: "Lng (shiftRow0 M) = Lng M" by simp
  have Lsh1: "1 < Lng (shiftRow0 M)" using L LshM by simp
  have predsh: "Pred (shiftRow0 M) = butlast (shiftRow0 M)"
    using Lsh1 by (simp add: Pred_def)
  show ?thesis
  proof (rule nth_equalityI)
    have Lbut: "Lng (butlast (shiftRow0 M)) = Lng M - 1" using LshM by simp
    have Lrhs: "Lng (shiftRow0 (Pred M)) = Lng M - 1"
      by (simp add: predbl)
    show "length (Pred (shiftRow0 M)) = length (shiftRow0 (Pred M))"
      using predsh Lbut Lrhs by simp
    fix i assume "i < length (Pred (shiftRow0 M))"
    hence iL: "i < Lng M - 1" using predsh Lbut by simp
    hence iLM: "i < Lng M" by simp
    have lhs: "Pred (shiftRow0 M) ! i = (entry M 0 i - entry M 0 0, entry M 1 i)"
    proof -
      have "Pred (shiftRow0 M) ! i = shiftRow0 M ! i"
        using predsh iL by (simp add: nth_butlast LshM)
      thus ?thesis using iLM by (simp add: shiftRow0_def)
    qed
    have rhs: "shiftRow0 (Pred M) ! i = (entry M 0 i - entry M 0 0, entry M 1 i)"
    proof -
      have iLP: "i < Lng (Pred M)" using iL by (simp add: predbl)
      have "shiftRow0 (Pred M) ! i
              = (entry (Pred M) 0 i - entry (Pred M) 0 0, entry (Pred M) 1 i)"
        using iLP by (simp add: shiftRow0_def)
      moreover have "entry (Pred M) 0 i = entry M 0 i"
        using iL predbl by (simp add: entry_def nth_butlast)
      moreover have "entry (Pred M) 1 i = entry M 1 i"
        using iL predbl by (simp add: entry_def nth_butlast)
      moreover have "entry (Pred M) 0 0 = entry M 0 0" using predbl anchor by simp
      ultimately show ?thesis by simp
    qed
    show "Pred (shiftRow0 M) ! i = shiftRow0 (Pred M) ! i" using lhs rhs by simp
  qed
qed

text \<open>a3 helper: \<open>Red (Pred M) = Red (shiftRow0 (Pred M))\<close> on the shift branch
  (\<open>monoT M\<close>, \<open>m\<^sub>1\<^sub>0 = 0\<close>, \<open>Lng M > 1\<close>).  When \<open>Pred M\<close> is again mono this is
  @{thm [source] cdn_Red_shiftRow0_m10z}; when \<open>Lng M = 2\<close> the predecessor is the
  single column \<open>[(m\<^sub>0\<^sub>0, 0)]\<close>, which is \<open>zeroT\<close> and whose \<open>shiftRow0\<close> is \<open>[(0,0)]\<close>,
  both reducing to \<open>[(0,0)]\<close>.\<close>

lemma a3_Red_shiftRow0_Pred_m10z:
  assumes MT: "M \<in> T_PS" and mono: "monoT M" and c1: "entry M 1 0 = 0" and L: "1 < Lng M"
  shows "Red (Pred M) = Red (shiftRow0 (Pred M))"
proof -
  have predbl: "Pred M = butlast M" using L by (simp add: Pred_def)
  have predT: "Pred M \<in> T_PS" by (rule Pred_preserves_T_PS[OF MT])
  have LP: "Lng (Pred M) = Lng M - 1" using L by (simp add: predbl)
  have e1P: "entry (Pred M) 1 0 = 0"
    using L predbl c1 by (simp add: entry_def nth_butlast)
  show ?thesis
  proof (cases "zeroT (Pred M)")
    case True
    \<comment> \<open>\<open>Pred M\<close> is a zero term: \<open>Lng (Pred M) = 1\<close> and \<open>entry (Pred M) 1 0 = 0\<close>.\<close>
    have L1P: "Lng (Pred M) = 1" using True by (simp add: zeroT_def)
    have domP: "Red_dom (Pred M)" by (rule m_6_5_Red_welldef[OF predT])
    have rP: "Red (Pred M) = [(0,0)]" using Red.psimps[OF domP] True by simp
    \<comment> \<open>\<open>shiftRow0 (Pred M)\<close> is also a single zero column.\<close>
    have shne: "shiftRow0 (Pred M) \<noteq> []"
      using L1P by (simp add: shiftRow0_def)
    have shT: "shiftRow0 (Pred M) \<in> T_PS" using shne by (simp add: T_PS_def)
    have Lsh: "Lng (shiftRow0 (Pred M)) = 1" using L1P by simp
    have e1sh: "entry (shiftRow0 (Pred M)) 1 0 = 0"
      using L1P e1P by (simp add: shiftRow0_def entry_def)
    have zsh: "zeroT (shiftRow0 (Pred M))" using Lsh e1sh by (simp add: zeroT_def)
    have domsh: "Red_dom (shiftRow0 (Pred M))" by (rule m_6_5_Red_welldef[OF shT])
    have rsh: "Red (shiftRow0 (Pred M)) = [(0,0)]" using Red.psimps[OF domsh] zsh by simp
    show ?thesis using rP rsh by simp
  next
    case False
    \<comment> \<open>\<open>Pred M\<close> is mono (prefix of mono), so \<open>cdn_Red_shiftRow0_m10z\<close> applies.\<close>
    have nmuP: "\<not> multiT (Pred M)"
    proof -
      have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
      show ?thesis by (rule nonmulti_Pred[OF MT nmu L])
    qed
    have monoP: "monoT (Pred M)" using False nmuP by (simp add: multiT_def)
    show ?thesis by (rule cdn_Red_shiftRow0_m10z[OF predT monoP e1P])
  qed
qed

text \<open>a3 helper: for a core-trunk \<open>M\<close> (\<open>TrMax M = Lng M - 1\<close>), the predecessor is
  again core-trunk: \<open>TrMax (Pred M) = Lng (Pred M) - 1\<close>.  Every below-trunk row-1
  step of \<open>M\<close> (and \<open>M\<close>'s trunk is full) transfers to \<open>Pred M = butlast M\<close>, which
  shares the prefix \<open>[0, Lng M - 2]\<close>; the boundary step out of \<open>Pred M\<close> is
  vacuously absent (out of range).\<close>

lemma a3_TrMax_Pred_trunk:
  assumes M: "M \<in> T_PS" and trunk: "TrMax M = Lng M - 1" and L: "1 < Lng M"
  shows "TrMax (Pred M) = Lng (Pred M) - 1"
proof -
  have predT: "Pred M \<in> T_PS" by (rule Pred_preserves_T_PS[OF M])
  have predbl: "Pred M = butlast M" using L by (simp add: Pred_def)
  have LP: "Lng (Pred M) = Lng M - 1" using L by (simp add: predbl)
  let ?j = "Lng (Pred M) - 1"
  have agree: "\<And>j. j \<le> ?j \<Longrightarrow> M ! j = Pred M ! j"
  proof -
    fix j assume "j \<le> ?j"
    hence jlt: "j < Lng (Pred M)" using L LP by linarith
    thus "M ! j = Pred M ! j" by (simp add: predbl nth_butlast)
  qed
  have cM: "?j < Lng M" using LP L by linarith
  have cP: "?j < Lng (Pred M)" using LP L by linarith
  show ?thesis
  proof (rule TrMax_eqI[OF predT])
    fix j' assume j': "j' < ?j"
    \<comment> \<open>\<open>j' < Lng M - 2 < TrMax M\<close>, so \<open>M\<close> has the trunk step; transfer to \<open>Pred M\<close>.\<close>
    have j'tr: "j' < TrMax M" using j' trunk LP by linarith
    have stepM: "nextrel1 M j' (j' + 1)"
      using TrMax_trunk_step[OF M j'tr] by (simp add: nextR_def)
    have y_le: "j' + 1 \<le> ?j" using j' by linarith
    have x_le: "j' \<le> ?j" using j' by linarith
    have "nextrel1 (Pred M) j' (j' + 1)"
      by (rule nextrel1_prefix_imp[OF agree cM cP x_le y_le stepM])
    thus "nextR (Pred M) 1 j' (j' + 1)" by (simp add: nextR_def)
  next
    \<comment> \<open>boundary step out of \<open>Pred M\<close> is out of range.\<close>
    show "\<not> nextR (Pred M) 1 ?j (?j + 1)"
    proof
      assume "nextR (Pred M) 1 ?j (?j + 1)"
      hence "?j + 1 < Lng (Pred M)" by (simp add: nextR_def nextrel1_def)
      thus False using cP by linarith
    qed
  qed
qed

end
