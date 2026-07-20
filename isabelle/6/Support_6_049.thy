theory Support_6_049
  imports Frontier_6_069
begin

(* === Front B: conditional nu-induction assembly === *)
text \<open>\<S>6.6 KEYSTONE BACKWARD monoT-core, nu-INDUCTION ASSEMBLY conditional on the
  per-branch Y-bundle (Front B, tag pss-bwdcore-assembly).  Proves the core
  keystone \<open>Red M = M\<close> for every monoT-core A&B \<open>M\<close> BY nu-induction, with the
  nontrunk per-branch obligation discharged through the GREEN inverse-shift
  reduction @{thm [source] bwd_invshift_via_rebase}: each branch's
  \<open>(IncrFirst\<^bsup>e\<^esup>) (Red (N\<^sub>J M J)) = N\<^sub>J M J\<close> reduces to \<open>Red Y\<^sub>J = Y\<^sub>J\<close> for the
  rebased \<open>Y\<^sub>J = rebaseRow0 e 0 (N\<^sub>J M J)\<close>:
    \<^item> if \<open>Y\<^sub>J\<close> is core (\<open>m\<^sub>1\<^sub>0(Y\<^sub>J) = 0\<close>) it is a nu-smaller core A&B sequence, so
      the nu-IH gives \<open>Red Y\<^sub>J = Y\<^sub>J\<close> DIRECTLY;
    \<^item> if \<open>m\<^sub>1\<^sub>0(Y\<^sub>J) > 0\<close> it is the \<open>m\<^sub>1\<^sub>0>0\<close> A&B case, discharged by the GREEN
      nu-bounded @{thm [source] kst_condAB_imp_reduced_monoT_m10pos_nu} whose
      lone core call lands on \<open>Q = diagSeq 0 (m\<^sub>1\<^sub>0-1) @ Y\<^sub>J\<close> with
      \<open>nu Q < nu Y\<^sub>J < nu M\<close> (GREEN @{thm [source] nu_diagSeq_m10pos_lt}).
  The per-branch hypothesis \<open>Ybundle\<close> packages exactly the Y-properties verified
  396/396 (\<open>/tmp/fb_Yprops.py\<close>): \<open>N\<^sub>J M J \<in> T_PS\<close>, the row-0 lower bound, and that
  \<open>Y\<^sub>J\<close> is in \<open>T_PS\<close>, monoT, has \<open>m\<^sub>0\<^sub>0(Y\<^sub>J) = m\<^sub>1\<^sub>0(Y\<^sub>J)\<close>, satisfies \<open>RedCondA\<close>,
  \<open>RedCondB\<close>, and is nu-smaller than \<open>M\<close>.  This isolates the SINGLE remaining gap
  to the heredity of that bundle along the branch \<open>N\<^sub>J M J\<close>.  Cites only GREEN
  facts; no \<open>p_*\<close> stub, no self-reference (the nu-IH is legitimate).\<close>

lemma kst_condAB_imp_reduced_monoT_core_of_Ybundle:
  assumes Ybundle:
      "\<And>M J. M \<in> T_PS \<Longrightarrow> monoT M \<Longrightarrow> entry M 0 0 = 0 \<Longrightarrow> entry M 1 0 = 0
         \<Longrightarrow> RedCondA M \<Longrightarrow> RedCondB M \<Longrightarrow> TrMax M \<noteq> Lng M - 1
         \<Longrightarrow> J < Lng (Br M)
         \<Longrightarrow> NJ M J \<in> T_PS
           \<and> (\<forall>j < Lng (NJ M J). entry (NJ M J) 0 0 - entry (NJ M J) 1 0 \<le> entry (NJ M J) 0 j)
           \<and> (let Y = rebaseRow0 (entry (NJ M J) 0 0 - entry (NJ M J) 1 0) 0 (NJ M J)
              in Y \<in> T_PS \<and> monoT Y \<and> entry Y 0 0 = entry Y 1 0
                 \<and> RedCondA Y \<and> RedCondB Y \<and> nu Y < nu M)"
    and MT0: "M0 \<in> T_PS" and mono0: "monoT M0"
    and c00: "entry M0 0 0 = 0" and c10: "entry M0 1 0 = 0"
    and condA0: "RedCondA M0" and condB0: "RedCondB M0"
  shows "Red M0 = M0"
proof -
  have "M0 \<in> T_PS \<and> monoT M0 \<and> entry M0 0 0 = 0 \<and> entry M0 1 0 = 0
          \<and> RedCondA M0 \<and> RedCondB M0 \<longrightarrow> Red M0 = M0"
  proof (induction M0 rule: measure_induct_rule[where f=nu])
    case (less M)
    show ?case
    proof (rule impI, elim conjE)
      assume MT: "M \<in> T_PS" and mono: "monoT M"
        and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
        and condA: "RedCondA M" and condB: "RedCondB M"
      show "Red M = M"
      proof (cases "TrMax M = Lng M - 1")
        case True
        show ?thesis by (rule kst_bwdcore_trunk[OF MT mono c0 c1 True condA])
      next
        case tne: False
        show ?thesis
        proof (rule kst_bwdcore_master_via_G[OF MT mono c0 c1 condA])
          fix J assume JBr: "J < Lng (Br M)"
          let ?e = "entry (NJ M J) 0 0 - entry (NJ M J) 1 0"
          let ?Y = "rebaseRow0 ?e 0 (NJ M J)"
          have bnd: "NJ M J \<in> T_PS
              \<and> (\<forall>j < Lng (NJ M J). ?e \<le> entry (NJ M J) 0 j)
              \<and> (let Y = ?Y in Y \<in> T_PS \<and> monoT Y \<and> entry Y 0 0 = entry Y 1 0
                   \<and> RedCondA Y \<and> RedCondB Y \<and> nu Y < nu M)"
            by (rule Ybundle[OF MT mono c0 c1 condA condB tne JBr])
          have NJT: "NJ M J \<in> T_PS" using bnd by simp
          have lb: "\<And>j. j < Lng (NJ M J) \<Longrightarrow> ?e \<le> entry (NJ M J) 0 j" using bnd by simp
          have YT: "?Y \<in> T_PS" using bnd by (simp add: Let_def)
          have Ymono: "monoT ?Y" using bnd by (simp add: Let_def)
          have Yeq: "entry ?Y 0 0 = entry ?Y 1 0" using bnd by (simp add: Let_def)
          have YA: "RedCondA ?Y" using bnd by (simp add: Let_def)
          have YB: "RedCondB ?Y" using bnd by (simp add: Let_def)
          have YnuM: "nu ?Y < nu M" using bnd by (simp add: Let_def)
          \<comment> \<open>\<open>Red Y = Y\<close>: core via nu-IH, m10>0 via the nu-bounded m10pos brick.\<close>
          have Yred: "Red ?Y = ?Y"
          proof (cases "entry ?Y 1 0 = 0")
            case Ycore: True
            have Ye00: "entry ?Y 0 0 = 0" using Yeq Ycore by simp
            show ?thesis
              using less.IH[OF YnuM] YT Ymono Ye00 Ycore YA YB by simp
          next
            case Ypos: False
            hence Ym10pos: "0 < entry ?Y 1 0" by simp
            \<comment> \<open>the m10pos brick's lone core call lands on \<open>Q = diagSeq 0 (m\<^sub>1\<^sub>0-1) @ Y\<close>;
                \<open>nu Q < nu Y < nu M\<close>, so the nu-IH covers it.\<close>
            have nuQlt: "nu (diagSeq 0 (entry ?Y 1 0 - 1) @ ?Y) < nu M"
            proof -
              have "nu (diagSeq 0 (entry ?Y 1 0 - 1) @ ?Y) < nu ?Y"
                by (rule nu_diagSeq_m10pos_lt[OF Ymono Ym10pos Yeq])
              also have "\<dots> < nu M" using YnuM .
              finally show ?thesis .
            qed
            show ?thesis
            proof (rule kst_condAB_imp_reduced_monoT_m10pos_nu
                      [where B="nu M", OF _ YT Ymono Ym10pos YA YB nuQlt])
              fix N assume nuN: "nu N < nu M" and NT: "N \<in> T_PS" and Nmono: "monoT N"
                and Ne00: "entry N 0 0 = 0" and Ne10: "entry N 1 0 = 0"
                and NA: "RedCondA N" and NB: "RedCondB N"
              show "Red N = N"
                using less.IH[OF nuN] NT Nmono Ne00 Ne10 NA NB by simp
            qed
          qed
          show "(IncrFirst ^^ (entry (NJ M J) 0 0 - entry (NJ M J) 1 0)) (Red (NJ M J)) = NJ M J"
            by (rule bwd_invshift_via_rebase[OF NJT lb Yred])
        qed
      qed
    qed
  qed
  thus ?thesis using MT0 mono0 c00 c10 condA0 condB0 by blast
qed

end
