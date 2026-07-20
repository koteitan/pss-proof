theory Support_7_016
  imports Frontier_7_019
begin

section \<open>§7.3 命題（\<open>2\<close>列ペア数列の基本性質）, part (1): the \<open>Trans\<close> value\<close>

text \<open>For reduced mono \<open>M\<close> of length 2 (head diagonal \<open>(v,v)\<close> by
  @{thm [source] reduced_mono_head_diag}): \<open>Trans M = D\<^bsub>M\<^bsub>1,0\<^esub>\<^esub> D\<^bsub>M\<^bsub>1,1\<^esub>\<^esub> 0\<close>.
  Article 2190; the conditions fire as (I) (\<open>b=0\<close>), (III) (\<open>0<b\<le>v\<close>) or (VI)
  (\<open>b=v+1\<close>, forced by RedCondA at the row-1 parent), and the scb-\<open>SOME\<close>
  evaluates to \<open>([],[])\<close> (@{thm [source] scb_SOME_self}).\<close>

lemma m_7_3_twoColumn_Trans:
  assumes M: "M \<in> RT_PS" and mono: "monoT M" and L2: "Lng M = 2"
  shows "Trans M = Dpt (enat (entry M 1 0)) (Dpt (enat (entry M 1 1)) 0\<^sub>B)"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  define v where "v = entry M 1 0"
  define b where "b = entry M 1 1"
  have hd0: "entry M 0 0 = v"
    using reduced_mono_head_diag[OF M mono] v_def by simp
  have predM: "Pred M = [(v, v)]"
  proof -
    obtain p0 p1 where Mp: "M = [p0, p1]"
      using L2 by (cases M rule: remdups_adj.cases) auto
    have "p0 = (v, v)"
      using hd0 v_def Mp by (cases p0) (simp add: entry_def)
    thus ?thesis using Mp by (simp add: Pred_def)
  qed
  have dom: "Trans_Mark_dom (Inl M)" by (rule m_7_3_Trans_welldef[OF M])
  have j1v: "Lng M - 1 = 1" using L2 by simp
  have Lgt1: "\<not> Lng M \<le> Suc 0" using L2 by simp
  have le01: "le0 M 0 1" using mono j1v by (simp add: monoT_def leR_def)
  have nr01: "nextrel0 M 0 1"
    using le0_adjacent_step[of M 0] le01 by simp
  have par0: "parent M 0 1 = 0"
  proof -
    have uniq: "\<And>j. nextR M 0 j 1 \<Longrightarrow> j = 0"
      by (auto simp: nextR_def nextrel0_def)
    have ex1: "\<exists>!j. nextR M 0 j 1"
      using nr01 uniq by (auto simp: nextR_def)
    show ?thesis unfolding parent_def
      using the1_equality[OF ex1] nr01 uniq by (auto simp: nextR_def)
  qed
  have adm0: "adm M 0" by (simp add: adm_def nadm_def nextR_def nextrel1_def)
  have Adm0: "Adm M 0 = 0" using adm0 by (simp add: Adm_def)
  have e10: "entry M 1 0 = v" using v_def by simp
  have e11: "entry M 1 1 = b" using b_def by simp
  show ?thesis
  proof (cases "v = 0")
    case True
    have t1z: "Trans (Pred M) = 0\<^sub>B" using predM Trans_singleton True by simp
    have "Trans M = Dpt 0 (Dpt (enat (entry M 1 (Lng M - 1))) 0\<^sub>B)"
      using Trans.psimps[OF dom] M j1v Lgt1 mono t1z by (simp add: Let_def)
    thus ?thesis using True e10 j1v by (simp add: zero_enat_def)
  next
    case False
    have vpos: "0 < v" using False by simp
    have t1v: "Trans (Pred M) = Dpt (enat v) 0\<^sub>B"
      using predM Trans_singleton False by simp
    have t1ne: "Trans (Pred M) \<noteq> 0\<^sub>B" using t1v by simp
    have c1v: "Mark (Pred M) 0 = Dpt (enat v) 0\<^sub>B"
      using predM Mark_singleton False by simp
    have somev: "(SOME sb. scb_decomp (Trans (Pred M)) (fst sb)
                    (flatBT (Dpt (enat v) 0\<^sub>B)) (snd sb)) = ([], [])"
    proof -
      have pt: "isPTB_str (flatBT (Dpt (enat v) (0\<^sub>B)))"
        by (rule isPTB_str_Dpt) simp_all
      show ?thesis
        using scb_SOME_self[OF pt] t1v by simp
    qed
    have conds: "(transCondI M \<or> transCondIII M \<or> transCondV M) \<or> transCondVI M"
    proof (cases "b = 0")
      case True
      thus ?thesis using adm0 par0 j1v e11 by (simp add: transCondI_def)
    next
      case bpos: False
      show ?thesis
      proof (cases "b \<le> v")
        case True
        thus ?thesis using bpos adm0 par0 j1v e10 e11
          by (simp add: transCondIII_def)
      next
        case False
        have vlb: "v < b" using False by simp
        have nr1: "nextrel1 M 0 1"
        proof -
          have valley: "\<And>j. 0 < j \<Longrightarrow> le0 M j 1 \<Longrightarrow> entry M 1 1 \<le> entry M 1 j"
          proof -
            fix j assume j0: "0 < j" and lej: "le0 M j 1"
            have "j < Lng M" using lej by (simp add: le0_def)
            hence "j = 1" using j0 L2 by simp
            thus "entry M 1 1 \<le> entry M 1 j" by simp
          qed
          show ?thesis
            unfolding nextrel1_def
            using L2 e10 e11 vlb le01 valley by auto
        qed
        have hp1: "hasParent M 1 1"
        proof -
          have "\<And>j. nextR M 1 j 1 \<Longrightarrow> j = 0"
            by (auto simp: nextR_def nextrel1_def)
          thus ?thesis using nr1 unfolding hasParent_def nextR_def by auto
        qed
        have par1: "parent M 1 1 = 0"
        proof -
          have uniq: "\<And>j. nextR M 1 j 1 \<Longrightarrow> j = 0"
            by (auto simp: nextR_def nextrel1_def)
          have ex1: "\<exists>!j. nextR M 1 j 1"
            using nr1 uniq by (auto simp: nextR_def)
          show ?thesis unfolding parent_def
            using the1_equality[OF ex1] nr1 uniq by (auto simp: nextR_def)
        qed
        have condA: "RedCondA M"
          using m_6_6_reduced_iff_cond[OF MT] M by auto
        have "entry M 1 (parent M 1 1) + 1 = entry M 1 1"
          using condA[unfolded RedCondA_def, rule_format, of 1 1] hp1 by simp
        hence "v + 1 = b" using par1 e10 e11 by simp
        thus ?thesis using vlb par0 j1v e10 e11
          by (simp add: transCondVI_def)
      qed
    qed
    have trans_val: "Trans M = unflatBT (flatBT (Dpt (enat v) (Dpt (enat b) 0\<^sub>B)))"
    proof (cases "transCondI M \<or> transCondIII M \<or> transCondV M")
      case True
      show ?thesis
        using Trans.psimps[OF dom] M j1v Lgt1 mono t1ne t1v c1v somev True
              par0 Adm0 e11
        by (simp add: Let_def)
    next
      case False
      hence VI: "transCondVI M" using conds by blast
      show ?thesis
        using Trans.psimps[OF dom] M j1v Lgt1 mono t1ne t1v c1v somev False VI
              par0 Adm0 e11
        by (simp add: Let_def)
    qed
    have ufl: "unflatBT (flatBT (Dpt (enat v) (Dpt (enat b) 0\<^sub>B)))
               = Dpt (enat v) (Dpt (enat b) 0\<^sub>B)"
      by (rule unflatBT_flat)
    show ?thesis using trans_val e10 e11 ufl by simp
  qed
qed


text \<open>Parts (2)–(5) of 命題（\<open>2\<close>列ペア数列の基本性質）: the marked-pair
  membership and the \<open>Mark\<close> values.\<close>

lemma m_7_3_twoColumn_Marked:
  assumes M: "M \<in> RT_PS" and mono: "monoT M" and L2: "Lng M = 2"
  shows "(M, 0) \<in> Marked" and "(M, 1) \<in> Marked"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: RT_PS_def)
  have adm0: "adm M 0" by (simp add: adm_def nadm_def nextR_def nextrel1_def)
  have adm1: "adm M 1"
    by (simp add: adm_def nadm_def nextR_def nextrel1_def L2)
  have le01: "leR M 0 0 1" using mono L2 by (simp add: monoT_def leR_def)
  have le11: "leR M 0 1 1" using L2 by (simp add: leR_def le0_def)
  show "(M, 0) \<in> Marked"
    using MT adm0 le01 L2 by (simp add: Marked_def)
  show "(M, 1) \<in> Marked"
    using MT adm1 le11 L2 by (simp add: Marked_def)
qed

end
