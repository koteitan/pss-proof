theory P_6_5_Red_welldef
  imports Frontier_6_021
begin

subsection \<open>§6.5 簡約化\<close>

text \<open>
  CAUTION (correction A4 — see corrections.md and docs/red-le-domain.md).
  The eight §6.5 corollaries p_6_5_Red_le, p_6_5_Red_monoT, p_6_5_P_Red,
  p_6_5_Red_idem, p_6_5_Red_oper, p_6_5_Red_adm, p_6_5_admof_Red and
  p_6_5_Red_marked are FALSE as the article states them for all M : T_PS —
  counterexample Red ((0,0)(0,1)) = (0,0)(1,1), which changes the ancestor tree
  (checked empirically with python/ + yaBMS).  They DO hold on the restricted
  domain of ANCESTOR-ANCHORED SLICES of standard / reduced+mono sequences, i.e.
  the actual §7 use-sites.  Their premise is therefore corrected here from
  \<open>M \<in> T_PS\<close> to \<open>M \<in> anchored_slice\<close> (pss_defs.thy), so the sorry below is
  no longer a false axiom — the statements are now true but UNPROVEN, and the
  domain \<open>anchored_slice\<close> is PROVISIONAL (a simpler intrinsic characterization
  and the proof are pending).  The remaining §6.5 facts (Lng_Red, Red_zeroT,
  Red_Pred, Red_IncrFirst) hold on all of T_PS and keep that premise.
\<close>

text \<open>命題（\<open>Red\<close>のwell-defined性） — the recursion defining \<open>Red\<close> terminates on
  every \<open>M \<in> T\<^sub>PS\<close> (the article: 上の条件を全て満たす写像 \<open>Red\<close> が一意に存在する).
  Encoded as totality of the \<open>function\<close>-domain predicate \<open>Red_dom\<close>.\<close>

text \<open>m: 命題（\<open>Red\<close> の well-defined 性） — discharges
  @{text p_6_5_Red_welldef}.  \<open>Red\<close> terminates on \<open>T\<^sub>PS\<close> by well-founded
  induction on the measure @{const nu}; each of the five @{thm [source] Red.domintros}
  premises has strictly smaller \<open>nu\<close> (steps a–d) and stays in \<open>T\<^sub>PS\<close>.\<close>

lemma m_6_5_Red_welldef:
  assumes "M \<in> T_PS"
  shows "Red_dom M"
proof -
  have "M \<in> T_PS \<longrightarrow> Red_dom M"
  proof (induction M rule: measure_induct_rule[where f=nu])
    case (less M)
    show ?case
    proof (rule impI)
      assume MT: "M \<in> T_PS"
      have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
      have LM1: "1 \<le> Lng M" using Mne by (cases M) auto
      show "Red_dom M"
      proof (rule Red.domintros)
        fix y assume mu: "multiT M"
          and yin: "y \<in> set (if Suc 0 < Lng M
                              then P (take (Pcut M) M) @ [drop (Pcut M) M] else [M])"
        have L1: "Lng M > 1" by (rule multiT_imp_Lng_gt1[OF MT mu])
        have "P M = P (take (Pcut M) M) @ [drop (Pcut M) M]"
          using mu L1 by (subst P.simps) simp
        hence ypm: "y \<in> set (P M)" using yin L1 by simp
        have yT: "y \<in> T_PS" using P_blocks_nonempty[OF Mne] ypm by (auto simp: T_PS_def)
        have "nu y < nu M" by (rule nu_Pblock_lt[OF MT mu ypm])
        thus "Red_dom y" using less.IH yT by blast
      next
        fix xd assume nz: "\<not> zeroT M" and nmu: "\<not> multiT M"
          and c0: "entry M 0 0 = 0" and c1: "entry M (Suc 0) 0 = 0"
          and JBr: "xd < Lng (Br M)" and bz: "entry (Br M ! xd) (Suc 0) 0 = 0"
        have mono: "monoT M" using nz nmu by (simp add: multiT_def)
        have Mpt: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
        have c1': "entry M 1 0 = 0" using c1 by simp
        have eq: "(Suc (Joints M ! xd), 0) # tl (Br M ! xd) = NJ M xd"
          using c0 c1 bz by (simp add: NJ_def npJ_def)
        have argT: "(Suc (Joints M ! xd), 0) # tl (Br M ! xd) \<in> T_PS" by (simp add: T_PS_def)
        have "nu (NJ M xd) < nu M" by (rule nu_NJ_lt[OF Mpt c0 c1' JBr])
        hence "nu ((Suc (Joints M ! xd), 0) # tl (Br M ! xd)) < nu M" using eq by simp
        thus "Red_dom ((Suc (Joints M ! xd), 0) # tl (Br M ! xd))"
          using less.IH argT by blast
      next
        fix xd assume nz: "\<not> zeroT M" and nmu: "\<not> multiT M"
          and c0: "entry M 0 0 = 0" and c1: "entry M (Suc 0) 0 = 0"
          and JBr: "xd < Lng (Br M)" and bp: "0 < entry (Br M ! xd) (Suc 0) 0"
        have mono: "monoT M" using nz nmu by (simp add: multiT_def)
        have Mpt: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
        have c1': "entry M 1 0 = 0" using c1 by simp
        have eq: "(Suc (Joints M ! xd), Suc (THE j. nextR M (Suc 0) j (FirstNodes M ! xd)))
                    # tl (Br M ! xd) = NJ M xd"
          using c0 c1 bp by (simp add: NJ_def npJ_def)
        have argT: "(Suc (Joints M ! xd), Suc (THE j. nextR M (Suc 0) j (FirstNodes M ! xd)))
                      # tl (Br M ! xd) \<in> T_PS" by (simp add: T_PS_def)
        have "nu (NJ M xd) < nu M" by (rule nu_NJ_lt[OF Mpt c0 c1' JBr])
        hence "nu ((Suc (Joints M ! xd),
                    Suc (THE j. nextR M (Suc 0) j (FirstNodes M ! xd))) # tl (Br M ! xd)) < nu M"
          using eq by simp
        thus "Red_dom ((Suc (Joints M ! xd),
                Suc (THE j. nextR M (Suc 0) j (FirstNodes M ! xd))) # tl (Br M ! xd))"
          using less.IH argT by blast
      next
        assume nz: "\<not> zeroT M" and nmu: "\<not> multiT M"
          and c1: "entry M (Suc 0) 0 = 0" and c0p: "0 < entry M 0 0"
        have mono: "monoT M" using nz nmu by (simp add: multiT_def)
        have noncore: "\<not> (entry M 0 0 = 0 \<and> entry M 1 0 = 0)" using c0p by simp
        let ?f = "\<lambda>j. (entry M 0 j - entry M 0 0, entry M (Suc 0) j)"
        have split: "[0..<Lng M] = [0..<Lng M - Suc 0] @ [Lng M - Suc 0]"
        proof -
          have eq: "Lng M = Suc (Lng M - Suc 0)" using LM1 by simp
          thus ?thesis using upt_Suc_append[of 0 "Lng M - Suc 0"] by (simp del: upt_Suc)
        qed
        have argeq: "map ?f [0..<Lng M - Suc 0] @ [?f (Lng M - Suc 0)] = coreReduce M"
          using c1 split by (simp add: coreReduce_def)
        have argT: "map ?f [0..<Lng M - Suc 0] @ [?f (Lng M - Suc 0)] \<in> T_PS" by (simp add: T_PS_def)
        have "nu (coreReduce M) < nu M" by (rule nu_coreReduce_lt[OF MT mono noncore])
        hence "nu (map ?f [0..<Lng M - Suc 0] @ [?f (Lng M - Suc 0)]) < nu M" using argeq by simp
        thus "Red_dom (map ?f [0..<Lng M - Suc 0] @ [?f (Lng M - Suc 0)])"
          using less.IH argT by blast
      next
        assume nz: "\<not> zeroT M" and nmu: "\<not> multiT M" and c1p: "0 < entry M (Suc 0) 0"
        have mono: "monoT M" using nz nmu by (simp add: multiT_def)
        have noncore: "\<not> (entry M 0 0 = 0 \<and> entry M 1 0 = 0)" using c1p by simp
        have argeq: "diagSeq 0 (entry M (Suc 0) 0 - Suc 0) @ (IncrFirst ^^ entry M (Suc 0) 0) M
                       = coreReduce M"
          using c1p by (simp add: coreReduce_def)
        have iFne: "(IncrFirst ^^ entry M (Suc 0) 0) M \<noteq> []"
          using Mne by (metis Lng_funpow_IncrFirst length_0_conv)
        have argT: "diagSeq 0 (entry M (Suc 0) 0 - Suc 0) @ (IncrFirst ^^ entry M (Suc 0) 0) M
                      \<in> T_PS" using iFne by (simp add: T_PS_def)
        have "nu (coreReduce M) < nu M" by (rule nu_coreReduce_lt[OF MT mono noncore])
        hence "nu (diagSeq 0 (entry M (Suc 0) 0 - Suc 0)
                    @ (IncrFirst ^^ entry M (Suc 0) 0) M) < nu M" using argeq by simp
        thus "Red_dom (diagSeq 0 (entry M (Suc 0) 0 - Suc 0)
                @ (IncrFirst ^^ entry M (Suc 0) 0) M)"
          using less.IH argT by blast
      qed
    qed
  qed
  thus ?thesis using assms by blast
qed

lemma p_6_5_Red_welldef:
  assumes "M \<in> T_PS"
  shows "Red_dom M"
  using assms by (rule m_6_5_Red_welldef)

end
