theory Frontier_6_057
  imports Support_6_038
begin

(* ===== block from workflow t2-rpred ===== *)
subsection \<open>§6.5 命題（\<open>Red\<close>と\<open>Pred\<close>の可換性）— core-nontrunk \<open>Hbr\<close> の解消\<close>

text \<open>rpred: \<open>Br (Pred M)\<close> shares the prefix \<open>butlast (Br M)\<close>.  Combined with
  @{thm [source] TrMax_Pred} this gives \<open>IdxSum\<close>/\<open>FirstNodes\<close> agreement on the
  prefix branch indices \<open>J \<le> Lng (Br M) - 1\<close>.\<close>

lemma rpred_Br_Pred_prefix:
  assumes M: "M \<in> T_PS" and m00: "entry M 0 0 = 0" and m10: "entry M 1 0 = 0"
    and br: "TrMax M \<noteq> Lng M - 1" and L: "1 < Lng M"
  shows "\<exists>ext. Br (Pred M) = butlast (Br M) @ ext"
proof -
  have "Br (Pred M) =
           butlast (Br M)
           @ (if Lng (last (Br M)) \<le> 1 then [] else [butlast (last (Br M))])"
    by (rule m_6_6_Br_Pred[OF M m00 m10 br L])
  thus ?thesis by blast
qed

text \<open>rpred: \<open>IdxSum\<close> agrees on a shared prefix region.  If \<open>Q\<^sub>1 = Q\<^sub>0 @ ext\<close> and
  \<open>J \<le> length Q\<^sub>0\<close>, then \<open>IdxSum Q\<^sub>1 ! J = IdxSum Q\<^sub>0 ! J\<close> (both are
  \<open>sum_list (map length (take J ·))\<close> and \<open>take J\<close> stays in the shared prefix).\<close>

lemma rpred_IdxSum_prefix_append:
  assumes "J \<le> length Q0"
  shows "IdxSum (Q0 @ ext) ! J = IdxSum Q0 ! J"
proof -
  have JleA: "J \<le> length (Q0 @ ext)" using assms by simp
  have a: "IdxSum (Q0 @ ext) ! J = sum_list (map length (take J (Q0 @ ext)))"
    by (rule idxsum_nth[OF JleA])
  have b: "IdxSum Q0 ! J = sum_list (map length (take J Q0))"
    by (rule idxsum_nth[OF assms])
  have c: "take J (Q0 @ ext) = take J Q0" using assms by (simp add: take_append)
  have "IdxSum (Q0 @ ext) ! J = sum_list (map length (take J Q0))" by (simp only: a c)
  thus ?thesis by (simp only: b)
qed

text \<open>rpred: \<open>IdxSum\<close> of \<open>butlast\<close> agrees with that of the full list on prefix
  indices \<open>J \<le> length L - 1\<close>.\<close>

lemma rpred_IdxSum_butlast:
  assumes "J \<le> length L - 1" and "L \<noteq> []"
  shows "IdxSum (butlast L) ! J = IdxSum L ! J"
proof -
  obtain Ls lst where Lsplit: "L = Ls @ [lst]" using assms(2)
    by (metis append_butlast_last_id)
  have but: "butlast L = Ls" using Lsplit by simp
  have lenLs: "length Ls = length L - 1" using Lsplit by simp
  have Jle: "J \<le> length Ls" using assms(1) lenLs by simp
  have "IdxSum L ! J = IdxSum (Ls @ [lst]) ! J" using Lsplit by simp
  also have "\<dots> = IdxSum Ls ! J" by (rule rpred_IdxSum_prefix_append[OF Jle])
  finally show ?thesis using but by simp
qed

text \<open>rpred: \<open>FirstNodes (Pred M) ! J = FirstNodes M ! J\<close> on prefix branches
  \<open>J < Lng (Br (Pred M))\<close>, for core-nontrunk \<open>M\<close>.  Uses \<open>TrMax (Pred M) = TrMax M\<close>
  (@{thm [source] TrMax_Pred}) and the \<open>IdxSum\<close> prefix agreement: \<open>Br (Pred M)\<close>
  starts with \<open>butlast (Br M)\<close>, so for \<open>J \<le> Lng (Br M) - 1\<close> the cumulative sums
  coincide.\<close>

lemma rpred_FirstNodes_Pred:
  assumes M: "M \<in> T_PS" and mono: "monoT M"
    and m00: "entry M 0 0 = 0" and m10: "entry M 1 0 = 0"
    and br: "TrMax M \<noteq> Lng M - 1" and L: "1 < Lng M"
    and JBr: "J < Lng (Br (Pred M))"
  shows "FirstNodes (Pred M) ! J = FirstNodes M ! J"
proof -
  have MP: "M \<in> PT_PS" using M mono by (simp add: PT_PS_def)
  have predT: "Pred M \<in> T_PS" by (rule Pred_preserves_T_PS[OF M])
  have predbl: "Pred M = butlast M" using L by (simp add: Pred_def)
  \<comment> \<open>\<open>Pred M\<close> is again core-nontrunk, so it has a nonempty \<open>Br\<close>.\<close>
  have trP: "TrMax (Pred M) = TrMax M" by (rule TrMax_Pred[OF M L br])
  \<comment> \<open>\<open>Br (Pred M)\<close> shares the prefix \<open>butlast (Br M)\<close>.\<close>
  obtain ext where ext: "Br (Pred M) = butlast (Br M) @ ext"
    using rpred_Br_Pred_prefix[OF M m00 m10 br L] by blast
  have brMne: "Br M \<noteq> []"
  proof -
    have "Br M = P (seg M (TrMax M + 1) (Lng M - 1))" using br by (simp add: Br_def)
    moreover have "0 < Lng (seg M (TrMax M + 1) (Lng M - 1))"
    proof -
      have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF M])
      with br have "TrMax M < Lng M - 1" by linarith
      thus ?thesis using L by (simp add: Lng_seg)
    qed
    ultimately show ?thesis by (metis P_nonempty)
  qed
  \<comment> \<open>prefix index bound: \<open>J \<le> Lng (Br M) - 1\<close>.\<close>
  have Jle: "J \<le> Lng (Br M) - 1"
  proof -
    have "Lng (Br (Pred M)) = Lng (butlast (Br M)) + Lng ext" using ext by simp
    hence "J < Lng (butlast (Br M)) + Lng ext" using JBr by simp
    \<comment> \<open>use the \<open>m_6_6_Br_Pred\<close> shape: \<open>ext\<close> has length \<le> 1 and the prefix is exactly
       \<open>butlast (Br M)\<close>; either way prefix indices we need satisfy \<open>J \<le> Lng(Br M)-1\<close>.\<close>
    have brEq: "Br (Pred M) =
             butlast (Br M)
             @ (if Lng (last (Br M)) \<le> 1 then [] else [butlast (last (Br M))])"
      by (rule m_6_6_Br_Pred[OF M m00 m10 br L])
    show ?thesis
    proof (cases "Lng (last (Br M)) \<le> 1")
      case True
      hence "Br (Pred M) = butlast (Br M)" using brEq by simp
      hence "J < Lng (butlast (Br M))" using JBr by simp
      thus ?thesis using brMne by simp
    next
      case False
      hence "Br (Pred M) = butlast (Br M) @ [butlast (last (Br M))]" using brEq by simp
      hence "J < Lng (butlast (Br M)) + 1" using JBr by simp
      thus ?thesis using brMne by simp
    qed
  qed
  have JleL: "J \<le> length (Br M) - 1" using Jle by simp
  \<comment> \<open>\<open>IdxSum (Br (Pred M)) ! J = IdxSum (Br M) ! J\<close>.\<close>
  have idxeq: "IdxSum (Br (Pred M)) ! J = IdxSum (Br M) ! J"
  proof -
    have JleBut: "J \<le> length (butlast (Br M))" using Jle brMne by simp
    have "IdxSum (Br (Pred M)) ! J = IdxSum (butlast (Br M)) ! J"
      using ext by (simp add: rpred_IdxSum_prefix_append[OF JleBut])
    also have "\<dots> = IdxSum (Br M) ! J"
      by (rule rpred_IdxSum_butlast[OF JleL brMne])
    finally show ?thesis .
  qed
  have fnP: "FirstNodes (Pred M) ! J = TrMax (Pred M) + 1 + IdxSum (Br (Pred M)) ! J"
    by (rule FirstNodes_nth[OF JBr])
  have JM: "J < Lng (Br M)" using Jle brMne by (cases "Br M") auto
  have fnM: "FirstNodes M ! J = TrMax M + 1 + IdxSum (Br M) ! J"
    by (rule FirstNodes_nth[OF JM])
  show ?thesis using fnP fnM trP idxeq by simp
qed

text \<open>rpred: the branch index bound \<open>J < Lng (Br (Pred M))\<close> forces \<open>J < Lng (Br M)\<close>
  for core-nontrunk \<open>M\<close> (the predecessor's branch list is no longer than the
  original's).\<close>

lemma rpred_JBr_Pred_imp:
  assumes M: "M \<in> T_PS" and m00: "entry M 0 0 = 0" and m10: "entry M 1 0 = 0"
    and br: "TrMax M \<noteq> Lng M - 1" and L: "1 < Lng M"
    and JBr: "J < Lng (Br (Pred M))"
  shows "J < Lng (Br M)"
proof -
  have brMne: "Br M \<noteq> []"
  proof -
    have "Br M = P (seg M (TrMax M + 1) (Lng M - 1))" using br by (simp add: Br_def)
    moreover have "0 < Lng (seg M (TrMax M + 1) (Lng M - 1))"
    proof -
      have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF M])
      with br have "TrMax M < Lng M - 1" by linarith
      thus ?thesis using L by (simp add: Lng_seg)
    qed
    ultimately show ?thesis by (metis P_nonempty)
  qed
  have brEq: "Br (Pred M) =
           butlast (Br M)
           @ (if Lng (last (Br M)) \<le> 1 then [] else [butlast (last (Br M))])"
    by (rule m_6_6_Br_Pred[OF M m00 m10 br L])
  show ?thesis
  proof (cases "Lng (last (Br M)) \<le> 1")
    case True
    hence "Br (Pred M) = butlast (Br M)" using brEq by simp
    hence "J < Lng (butlast (Br M))" using JBr by simp
    thus ?thesis using brMne by simp
  next
    case False
    hence "Br (Pred M) = butlast (Br M) @ [butlast (last (Br M))]" using brEq by simp
    hence "J < Lng (butlast (Br M)) + 1" using JBr by simp
    thus ?thesis using brMne by simp
  qed
qed

text \<open>rpred: a branch first node has a unique row-0 parent.\<close>

lemma rpred_hasParent_FirstNodes:
  assumes M: "M \<in> PT_PS" and JBr: "J < Lng (Br M)"
  shows "hasParent M 0 (FirstNodes M ! J)"
proof -
  have MT: "M \<in> T_PS" using M by (simp add: PT_PS_def)
  have brne: "Br M \<noteq> []" using JBr by auto
  have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
  have trne: "TrMax M \<noteq> Lng M - 1"
  proof
    assume "TrMax M = Lng M - 1"
    hence "Br M = []" by (simp add: Br_def)
    with brne show False by simp
  qed
  with tb have trlt: "TrMax M < Lng M - 1" by linarith
  let ?N = "seg M (TrMax M + 1) (Lng M - 1)"
  have brQ: "Br M = P ?N" using trne by (simp add: Br_def)
  have JQ: "J \<le> Lng (P ?N) - 1" using JBr brQ by (cases "P ?N") auto
  have hp: "hasParent M 0 (TrMax M + 1 + IdxSum (P ?N) ! J)"
    using m_6_4_mono_slice_next[OF M _ _ JQ] trlt by auto
  have fnJ: "TrMax M + 1 + IdxSum (P ?N) ! J = FirstNodes M ! J"
    using FirstNodes_nth[OF JBr] brQ by simp
  show ?thesis using hp fnJ by simp
qed

text \<open>rpred: \<open>Joints (Pred M) ! J = Joints M ! J\<close> on prefix branches.  Both are the
  \<open>THE\<close> row-0 parent of \<open>FirstNodes _ ! J\<close>; @{thm [source] rpred_FirstNodes_Pred}
  identifies the first nodes, and the parent transfers across the shared prefix
  \<open>[0, FirstNodes M ! J]\<close> (the dropped last column lies strictly right of it, since
  \<open>FirstNodes M ! J < Lng (Pred M)\<close>).\<close>

lemma rpred_Joints_Pred:
  assumes M: "M \<in> T_PS" and mono: "monoT M"
    and m00: "entry M 0 0 = 0" and m10: "entry M 1 0 = 0"
    and br: "TrMax M \<noteq> Lng M - 1" and L: "1 < Lng M"
    and JBr: "J < Lng (Br (Pred M))"
  shows "Joints (Pred M) ! J = Joints M ! J"
proof -
  have MP: "M \<in> PT_PS" using M mono by (simp add: PT_PS_def)
  have predT: "Pred M \<in> T_PS" by (rule Pred_preserves_T_PS[OF M])
  have JM: "J < Lng (Br M)" by (rule rpred_JBr_Pred_imp[OF M m00 m10 br L JBr])
  \<comment> \<open>\<open>Pred M\<close> is again core-nontrunk and in \<open>PT_PS\<close>.\<close>
  have predbl: "Pred M = butlast M" using L by (simp add: Pred_def)
  have nz: "\<not> zeroT M" using L by (simp add: zeroT_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  have nzP: "\<not> zeroT (Pred M)"
  proof -
    have LP: "Lng (Pred M) = Lng M - 1" using L by (simp add: predbl)
    \<comment> \<open>\<open>Pred M\<close> has a nonempty \<open>Br\<close>, so \<open>Lng (Pred M) > 1\<close>.\<close>
    have brPne: "Br (Pred M) \<noteq> []" using JBr by auto
    have tneP: "TrMax (Pred M) \<noteq> Lng (Pred M) - 1"
    proof
      assume "TrMax (Pred M) = Lng (Pred M) - 1"
      hence "Br (Pred M) = []" by (simp add: Br_def)
      with brPne show False by simp
    qed
    have LPgt: "1 < Lng (Pred M)"
    proof (rule ccontr)
      assume "\<not> 1 < Lng (Pred M)"
      hence "Lng (Pred M) \<le> 1" by simp
      moreover have "0 < Lng (Pred M)" using LP L by linarith
      ultimately have "Lng (Pred M) = 1" by linarith
      hence "TrMax (Pred M) = Lng (Pred M) - 1"
        using TrMax_bound[OF predT] by simp
      thus False using tneP by simp
    qed
    thus ?thesis by (simp add: zeroT_def)
  qed
  have nmuP: "\<not> multiT (Pred M)" by (rule nonmulti_Pred[OF M nmu L])
  have monoP: "monoT (Pred M)" using nzP nmuP by (simp add: multiT_def)
  have MPP: "Pred M \<in> PT_PS" using predT monoP by (simp add: PT_PS_def)
  let ?f = "FirstNodes M ! J"
  have fnP: "FirstNodes (Pred M) ! J = ?f"
    by (rule rpred_FirstNodes_Pred[OF M mono m00 m10 br L JBr])
  \<comment> \<open>the unique parent in \<open>Pred M\<close>.\<close>
  have hpP: "hasParent (Pred M) 0 ?f"
    using rpred_hasParent_FirstNodes[OF MPP JBr] fnP by simp
  \<comment> \<open>the parent in \<open>M\<close> transfers to \<open>Pred M\<close>.\<close>
  have nxM: "nextR M 0 (Joints M ! J) ?f" by (rule Joints_parent_nextR[OF MP JM])
  \<comment> \<open>bounds: both endpoints \<le> \<open>?f\<close> and \<open>?f < Lng (Pred M)\<close>.\<close>
  have jM_le: "Joints M ! J \<le> TrMax M \<and> TrMax M < ?f"
    by (rule m_6_4_FirstNodes_TrMax_Joints[OF MP JM])
  have f_lt_M: "?f < Lng M" using nxM by (simp add: nextR_def nextrel0_def)
  have f_lt_P: "?f < Lng (Pred M)"
  proof -
    have fnP': "?f = TrMax (Pred M) + 1 + IdxSum (Br (Pred M)) ! J"
      using fnP FirstNodes_nth[OF JBr] by simp
    have fnP2: "FirstNodes (Pred M) ! J < Lng (Pred M)"
      using Joints_parent_nextR[OF MPP JBr] by (simp add: nextR_def nextrel0_def)
    thus ?thesis using fnP by simp
  qed
  \<comment> \<open>row-0 agreement on the prefix \<open>[0, ?f]\<close>.\<close>
  have agree0: "\<And>j. j \<le> ?f \<Longrightarrow> entry M 0 j = entry (Pred M) 0 j"
  proof -
    fix j assume "j \<le> ?f"
    hence "j < Lng (Pred M)" using f_lt_P by linarith
    thus "entry M 0 j = entry (Pred M) 0 j"
      by (simp add: predbl entry_def nth_butlast)
  qed
  have agree0': "\<And>j. j \<le> ?f \<Longrightarrow> entry (Pred M) 0 j = entry M 0 j"
    using agree0 by simp
  \<comment> \<open>\<open>nextR (Pred M) 0 (Joints M ! J) ?f\<close> via row-0 prefix transfer.\<close>
  have jMle_f: "Joints M ! J \<le> ?f" using jM_le by linarith
  have nxMrel: "nextrel0 M (Joints M ! J) ?f" using nxM by (simp add: nextR_def)
  have nxMP: "nextR (Pred M) 0 (Joints M ! J) ?f"
  proof -
    have "nextrel0 (Pred M) (Joints M ! J) ?f"
      by (rule nextrel0_prefix_row0[OF agree0 f_lt_P jMle_f order.refl nxMrel])
    thus ?thesis by (simp add: nextR_def)
  qed
  \<comment> \<open>uniqueness of the parent in \<open>Pred M\<close>: \<open>Joints (Pred M) ! J\<close> is THE.\<close>
  have jP_eq: "Joints (Pred M) ! J = parent (Pred M) 0 ?f"
    using JBr fnP by (simp add: Joints_nth)
  have exu: "\<exists>!j0. nextR (Pred M) 0 j0 ?f"
    using hpP by (simp add: hasParent_def)
  have "parent (Pred M) 0 ?f = Joints M ! J"
    unfolding parent_def
    by (rule the1_equality[OF exu nxMP])
  thus ?thesis using jP_eq by simp
qed

text \<open>rpred: the block left-end \<open>(Br (Pred M) ! J)\<^bsub>1,0\<^esub> = (Br M ! J)\<^bsub>1,0\<^esub>\<close> on prefix
  branches \<open>J < Lng (Br (Pred M))\<close>.  Reads the row-1 entry of the \<open>J\<close>-th branch
  block; both equal \<open>entry M 1 (FirstNodes M ! J)\<close> (the first-node row-1 value),
  which only depends on indices in the shared prefix.\<close>

lemma rpred_branch_e1_Pred:
  assumes M: "M \<in> T_PS" and mono: "monoT M"
    and m00: "entry M 0 0 = 0" and m10: "entry M 1 0 = 0"
    and br: "TrMax M \<noteq> Lng M - 1" and L: "1 < Lng M"
    and JBr: "J < Lng (Br (Pred M))"
  shows "entry (Br (Pred M) ! J) 1 0 = entry (Br M ! J) 1 0"
proof -
  have MP: "M \<in> PT_PS" using M mono by (simp add: PT_PS_def)
  have predT: "Pred M \<in> T_PS" by (rule Pred_preserves_T_PS[OF M])
  have JM: "J < Lng (Br M)" by (rule rpred_JBr_Pred_imp[OF M m00 m10 br L JBr])
  \<comment> \<open>\<open>Pred M\<close> is core-nontrunk, in \<open>PT_PS\<close> (re-derive monoT of \<open>Pred M\<close>).\<close>
  have predbl: "Pred M = butlast M" using L by (simp add: Pred_def)
  have nz: "\<not> zeroT M" using L by (simp add: zeroT_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  have brPne: "Br (Pred M) \<noteq> []" using JBr by auto
  have tneP: "TrMax (Pred M) \<noteq> Lng (Pred M) - 1"
  proof
    assume "TrMax (Pred M) = Lng (Pred M) - 1"
    hence "Br (Pred M) = []" by (simp add: Br_def)
    with brPne show False by simp
  qed
  have LP: "Lng (Pred M) = Lng M - 1" using L by (simp add: predbl)
  have LPgt: "1 < Lng (Pred M)"
  proof (rule ccontr)
    assume "\<not> 1 < Lng (Pred M)"
    moreover have "0 < Lng (Pred M)" using LP L by linarith
    ultimately have "Lng (Pred M) = 1" by linarith
    hence "TrMax (Pred M) = Lng (Pred M) - 1" using TrMax_bound[OF predT] by simp
    thus False using tneP by simp
  qed
  have nzP: "\<not> zeroT (Pred M)" using LPgt by (simp add: zeroT_def)
  have nmuP: "\<not> multiT (Pred M)" by (rule nonmulti_Pred[OF M nmu L])
  have monoP: "monoT (Pred M)" using nzP nmuP by (simp add: multiT_def)
  have MPP: "Pred M \<in> PT_PS" using predT monoP by (simp add: PT_PS_def)
  \<comment> \<open>both branch row-1 left ends equal the first-node row-1 entry.\<close>
  have eP: "entry (Br (Pred M) ! J) 1 0 = entry (Pred M) 1 (FirstNodes (Pred M) ! J)"
    by (rule entry_FirstNodes_eq_component_gen[OF MPP JBr, symmetric])
  have eM: "entry (Br M ! J) 1 0 = entry M 1 (FirstNodes M ! J)"
    by (rule entry_FirstNodes_eq_component_gen[OF MP JM, symmetric])
  have fnP: "FirstNodes (Pred M) ! J = FirstNodes M ! J"
    by (rule rpred_FirstNodes_Pred[OF M mono m00 m10 br L JBr])
  \<comment> \<open>\<open>FirstNodes M ! J < Lng (Pred M)\<close>, so row-1 entries agree.\<close>
  have f_lt_P: "FirstNodes M ! J < Lng (Pred M)"
  proof -
    have "FirstNodes (Pred M) ! J < Lng (Pred M)"
      using Joints_parent_nextR[OF MPP JBr] by (simp add: nextR_def nextrel0_def)
    thus ?thesis using fnP by simp
  qed
  have "entry (Pred M) 1 (FirstNodes M ! J) = entry M 1 (FirstNodes M ! J)"
    using f_lt_P by (simp add: predbl entry_def nth_butlast)
  thus ?thesis using eP eM fnP by simp
qed

text \<open>rpred: \<open>npJ (Pred M) J = npJ M J\<close> on prefix branches.  The \<open>if\<close> guard
  \<open>(Br _ ! J)\<^bsub>1,0\<^esub> = 0\<close> transfers (@{thm [source] rpred_branch_e1_Pred}); in the
  nonzero arm both \<open>npJ = Suc p\<^sub>1\<close> with \<open>p\<^sub>1\<close> the unique row-1 parent of the (shared)
  first node, which is determined by data in the prefix \<open>[0, FirstNodes M ! J]\<close> and
  hence the same for \<open>M\<close> and \<open>Pred M\<close>.\<close>

lemma rpred_npJ_Pred:
  assumes M: "M \<in> T_PS" and mono: "monoT M"
    and m00: "entry M 0 0 = 0" and m10: "entry M 1 0 = 0"
    and br: "TrMax M \<noteq> Lng M - 1" and L: "1 < Lng M"
    and JBr: "J < Lng (Br (Pred M))"
  shows "npJ (Pred M) J = npJ M J"
proof -
  have MP: "M \<in> PT_PS" using M mono by (simp add: PT_PS_def)
  have MT: "M \<in> T_PS" using M .
  have predT: "Pred M \<in> T_PS" by (rule Pred_preserves_T_PS[OF M])
  have JM: "J < Lng (Br M)" by (rule rpred_JBr_Pred_imp[OF M m00 m10 br L JBr])
  have predbl: "Pred M = butlast M" using L by (simp add: Pred_def)
  have nz: "\<not> zeroT M" using L by (simp add: zeroT_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  \<comment> \<open>\<open>Pred M\<close> core-nontrunk in \<open>PT_PS\<close>.\<close>
  have brPne: "Br (Pred M) \<noteq> []" using JBr by auto
  have tneP: "TrMax (Pred M) \<noteq> Lng (Pred M) - 1"
  proof
    assume "TrMax (Pred M) = Lng (Pred M) - 1"
    hence "Br (Pred M) = []" by (simp add: Br_def)
    with brPne show False by simp
  qed
  have LP: "Lng (Pred M) = Lng M - 1" using L by (simp add: predbl)
  have LPgt: "1 < Lng (Pred M)"
  proof (rule ccontr)
    assume "\<not> 1 < Lng (Pred M)"
    moreover have "0 < Lng (Pred M)" using LP L by linarith
    ultimately have "Lng (Pred M) = 1" by linarith
    hence "TrMax (Pred M) = Lng (Pred M) - 1" using TrMax_bound[OF predT] by simp
    thus False using tneP by simp
  qed
  have nzP: "\<not> zeroT (Pred M)" using LPgt by (simp add: zeroT_def)
  have nmuP: "\<not> multiT (Pred M)" by (rule nonmulti_Pred[OF M nmu L])
  have monoP: "monoT (Pred M)" using nzP nmuP by (simp add: multiT_def)
  have MPP: "Pred M \<in> PT_PS" using predT monoP by (simp add: PT_PS_def)
  have e1P: "entry (Pred M) 1 0 = 0" using m10 entry_Pred_0[OF L] by simp
  have e0P: "entry (Pred M) 0 0 = 0" using m00 entry_Pred_0[OF L] by simp
  \<comment> \<open>branch row-1 guard transfers.\<close>
  have e1br: "entry (Br (Pred M) ! J) 1 0 = entry (Br M ! J) 1 0"
    by (rule rpred_branch_e1_Pred[OF M mono m00 m10 br L JBr])
  show ?thesis
  proof (cases "entry (Br M ! J) 1 0 = 0")
    case True
    have "entry (Br (Pred M) ! J) 1 0 = 0" using e1br True by simp
    thus ?thesis using True by (simp add: npJ_def)
  next
    case nzbr: False
    have nzbrP: "entry (Br (Pred M) ! J) 1 0 \<noteq> 0" using e1br nzbr by simp
    let ?f = "FirstNodes M ! J"
    have fnP: "FirstNodes (Pred M) ! J = ?f"
      by (rule rpred_FirstNodes_Pred[OF M mono m00 m10 br L JBr])
    \<comment> \<open>row-1 parent of \<open>?f\<close> in \<open>M\<close>: exists, unique = \<open>p1\<close>.\<close>
    have fnTr: "Joints M ! J \<le> TrMax M \<and> TrMax M < ?f"
      by (rule m_6_4_FirstNodes_TrMax_Joints[OF MP JM])
    have nxJ: "nextR M 0 (Joints M ! J) ?f" by (rule Joints_parent_nextR[OF MP JM])
    have fL: "?f < Lng M" using nxJ by (simp add: nextR_def nextrel0_def)
    have fpos: "0 < ?f" using fnTr by linarith
    have eBf1: "entry M 1 ?f = entry (Br M ! J) 1 0"
      by (rule entry_FirstNodes_eq_component_gen[OF MP JM])
    have f1pos: "0 < entry M 1 ?f" using eBf1 nzbr by simp
    have e10_lt: "entry M 1 0 < entry M 1 ?f" using m10 f1pos by simp
    have le00f: "leR M 0 0 ?f"
    proof -
      have root: "leR M 0 0 (Lng M - 1)" using mono by (simp add: monoT_def)
      have fle: "?f \<le> Lng M - 1" using fL by simp
      show ?thesis by (rule m_5_1_ancestor_tree_1[OF MT root _ fle]) simp
    qed
    obtain p1 where p1: "0 \<le> p1" "p1 < ?f" "nextR M 1 p1 ?f"
      using m_5_1_parent_exists_2[OF MT fpos fL e10_lt le00f] by blast
    have ex1M: "\<exists>!j. nextR M 1 j ?f" using p1(3) nextR1_unique by blast
    have theM: "(THE j. nextR M 1 j ?f) = p1" using p1(3) by (rule the1_equality[OF ex1M])
    \<comment> \<open>\<open>?f < Lng (Pred M)\<close>, and \<open>p1 < ?f\<close>; transfer \<open>nextR M 1 p1 ?f\<close> to \<open>Pred M\<close>.\<close>
    have f_lt_P: "?f < Lng (Pred M)"
    proof -
      have "FirstNodes (Pred M) ! J < Lng (Pred M)"
        using Joints_parent_nextR[OF MPP JBr] by (simp add: nextR_def nextrel0_def)
      thus ?thesis using fnP by simp
    qed
    have agreeMP: "\<And>j. j \<le> ?f \<Longrightarrow> M ! j = Pred M ! j"
    proof -
      fix j assume "j \<le> ?f"
      hence "j < Lng (Pred M)" using f_lt_P by linarith
      thus "M ! j = Pred M ! j" by (simp add: predbl nth_butlast)
    qed
    have p1le: "p1 \<le> ?f" using p1(2) by linarith
    have fle': "?f \<le> ?f" by simp
    have fLP: "?f < Lng (Pred M)" using f_lt_P .
    have fLM: "?f < Lng M" using fL .
    have rel1M: "nextrel1 M p1 ?f" using p1(3) by (simp add: nextR_def)
    have rel1P: "nextrel1 (Pred M) p1 ?f"
      by (rule nextrel1_prefix_imp[OF agreeMP fLM fLP p1le fle' rel1M])
    have nxP: "nextR (Pred M) 1 p1 ?f" using rel1P by (simp add: nextR_def)
    have ex1P: "\<exists>!j. nextR (Pred M) 1 j ?f" using nxP nextR1_unique by blast
    have theP0: "(THE j. nextR (Pred M) 1 j ?f) = p1" by (rule the1_equality[OF ex1P nxP])
    have theP: "(THE j. nextR (Pred M) 1 j (FirstNodes (Pred M) ! J)) = p1"
      using theP0 fnP by simp
    have "npJ (Pred M) J = Suc p1" using nzbrP theP by (simp add: npJ_def)
    moreover have "npJ M J = Suc p1" using nzbr theM by (simp add: npJ_def)
    ultimately show ?thesis by simp
  qed
qed

text \<open>rpred: the interior branch blocks of \<open>Pred M\<close> are verbatim those of \<open>M\<close>:
  \<open>Br (Pred M) ! J = Br M ! J\<close> for \<open>J < Lng (Br M) - 1\<close>.  (\<open>Br (Pred M)\<close> starts with
  \<open>butlast (Br M)\<close>; only the last block is touched.)\<close>

lemma rpred_block_eq_interior:
  assumes M: "M \<in> T_PS" and m00: "entry M 0 0 = 0" and m10: "entry M 1 0 = 0"
    and br: "TrMax M \<noteq> Lng M - 1" and L: "1 < Lng M"
    and Jlt: "J < Lng (Br M) - 1"
  shows "Br (Pred M) ! J = Br M ! J"
proof -
  obtain ext where ext: "Br (Pred M) = butlast (Br M) @ ext"
    using rpred_Br_Pred_prefix[OF M m00 m10 br L] by blast
  have brMne: "Br M \<noteq> []"
  proof -
    have "Br M = P (seg M (TrMax M + 1) (Lng M - 1))" using br by (simp add: Br_def)
    moreover have "0 < Lng (seg M (TrMax M + 1) (Lng M - 1))"
    proof -
      have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF M])
      with br have "TrMax M < Lng M - 1" by linarith
      thus ?thesis using L by (simp add: Lng_seg)
    qed
    ultimately show ?thesis by (metis P_nonempty)
  qed
  have JltBut: "J < length (butlast (Br M))" using Jlt brMne by simp
  have "Br (Pred M) ! J = butlast (Br M) ! J"
    using ext JltBut by (simp add: nth_append)
  also have "\<dots> = Br M ! J" using JltBut by (simp add: nth_butlast)
  finally show ?thesis .
qed

text \<open>rpred: \<open>NJ (Pred M) J = NJ M J\<close> on interior prefix branches \<open>J < Lng (Br M) - 1\<close>.
  All four ingredients (\<open>entry _ 0 0\<close>, \<open>entry _ 1 0\<close>, \<open>Joints\<close>, \<open>npJ\<close>) agree and the
  block \<open>Br _ ! J\<close> is verbatim, so the constructed \<open>N\<^sub>J\<close> coincides.\<close>

lemma rpred_NJ_interior:
  assumes M: "M \<in> T_PS" and mono: "monoT M"
    and m00: "entry M 0 0 = 0" and m10: "entry M 1 0 = 0"
    and br: "TrMax M \<noteq> Lng M - 1" and L: "1 < Lng M"
    and Jlt: "J < Lng (Br M) - 1"
    and JBrP: "J < Lng (Br (Pred M))"
  shows "NJ (Pred M) J = NJ M J"
proof -
  have e0P: "entry (Pred M) 0 0 = 0" using m00 entry_Pred_0[OF L] by simp
  have e1P: "entry (Pred M) 1 0 = 0" using m10 entry_Pred_0[OF L] by simp
  have joints: "Joints (Pred M) ! J = Joints M ! J"
    by (rule rpred_Joints_Pred[OF M mono m00 m10 br L JBrP])
  have np: "npJ (Pred M) J = npJ M J"
    by (rule rpred_npJ_Pred[OF M mono m00 m10 br L JBrP])
  have blk: "Br (Pred M) ! J = Br M ! J"
    by (rule rpred_block_eq_interior[OF M m00 m10 br L Jlt])
  show ?thesis
    unfolding NJ_def
    using e0P e1P m00 m10 joints np blk by simp
qed

text \<open>rpred: the last branch block of \<open>Pred M\<close> is \<open>butlast (last (Br M))\<close> when the
  last block of \<open>M\<close> has length \<open>> 1\<close>.  Then \<open>Lng (Br (Pred M)) = Lng (Br M)\<close>.\<close>

lemma rpred_lastblock_Pred:
  assumes M: "M \<in> T_PS" and m00: "entry M 0 0 = 0" and m10: "entry M 1 0 = 0"
    and br: "TrMax M \<noteq> Lng M - 1" and L: "1 < Lng M"
    and lastgt: "1 < Lng (last (Br M))"
  shows "Lng (Br (Pred M)) = Lng (Br M)
       \<and> Br (Pred M) ! (Lng (Br M) - 1) = butlast (Br M ! (Lng (Br M) - 1))"
proof -
  have brMne: "Br M \<noteq> []"
  proof -
    have "Br M = P (seg M (TrMax M + 1) (Lng M - 1))" using br by (simp add: Br_def)
    moreover have "0 < Lng (seg M (TrMax M + 1) (Lng M - 1))"
    proof -
      have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF M])
      with br have "TrMax M < Lng M - 1" by linarith
      thus ?thesis using L by (simp add: Lng_seg)
    qed
    ultimately show ?thesis by (metis P_nonempty)
  qed
  have brEq: "Br (Pred M) = butlast (Br M) @ [butlast (last (Br M))]"
  proof -
    have "\<not> Lng (last (Br M)) \<le> 1" using lastgt by simp
    thus ?thesis using m_6_6_Br_Pred[OF M m00 m10 br L] by simp
  qed
  have lenEq: "Lng (Br (Pred M)) = Lng (Br M)" using brEq brMne by simp
  have idx: "Lng (Br M) - 1 = length (butlast (Br M))" using brMne by simp
  have "Br (Pred M) ! (Lng (Br M) - 1) = butlast (last (Br M))"
    using brEq idx by (simp add: nth_append)
  also have "last (Br M) = Br M ! (Lng (Br M) - 1)"
    using brMne by (simp add: last_conv_nth)
  finally show ?thesis using lenEq by simp
qed

text \<open>rpred: \<open>NJ (Pred M) (Lng (Br M) - 1) = Pred (NJ M (Lng (Br M) - 1))\<close> on the last
  branch when \<open>Lng (last (Br M)) > 1\<close>.  The shared head \<open>(Joints+1, npJ)\<close> is fixed by
  the transfers; the tail is \<open>tl (butlast B) = butlast (tl B)\<close>, and
  \<open>Pred (N\<^sub>J) = butlast (N\<^sub>J)\<close> since \<open>Lng (N\<^sub>J) = Lng B > 1\<close>.\<close>

lemma rpred_NJ_lastblock:
  assumes M: "M \<in> T_PS" and mono: "monoT M"
    and m00: "entry M 0 0 = 0" and m10: "entry M 1 0 = 0"
    and br: "TrMax M \<noteq> Lng M - 1" and L: "1 < Lng M"
    and lastgt: "1 < Lng (last (Br M))"
  shows "NJ (Pred M) (Lng (Br M) - 1) = Pred (NJ M (Lng (Br M) - 1))"
proof -
  let ?J = "Lng (Br M) - 1"
  let ?B = "Br M ! ?J"
  have brMne: "Br M \<noteq> []"
  proof -
    have "Br M = P (seg M (TrMax M + 1) (Lng M - 1))" using br by (simp add: Br_def)
    moreover have "0 < Lng (seg M (TrMax M + 1) (Lng M - 1))"
    proof -
      have tb: "TrMax M \<le> Lng M - 1" by (rule TrMax_bound[OF M])
      with br have "TrMax M < Lng M - 1" by linarith
      thus ?thesis using L by (simp add: Lng_seg)
    qed
    ultimately show ?thesis by (metis P_nonempty)
  qed
  have JM: "?J < Lng (Br M)" using brMne by (cases "Br M") auto
  have lastB: "last (Br M) = ?B" using brMne by (simp add: last_conv_nth)
  have Bgt: "1 < Lng ?B" using lastgt lastB by simp
  obtain lenEq blkEq where
    lenEq: "Lng (Br (Pred M)) = Lng (Br M)" and
    blkEq: "Br (Pred M) ! ?J = butlast ?B"
    using rpred_lastblock_Pred[OF M m00 m10 br L lastgt] by auto
  have JBrP: "?J < Lng (Br (Pred M))" using JM lenEq by simp
  have e0P: "entry (Pred M) 0 0 = 0" using m00 entry_Pred_0[OF L] by simp
  have e1P: "entry (Pred M) 1 0 = 0" using m10 entry_Pred_0[OF L] by simp
  have joints: "Joints (Pred M) ! ?J = Joints M ! ?J"
    by (rule rpred_Joints_Pred[OF M mono m00 m10 br L JBrP])
  have np: "npJ (Pred M) ?J = npJ M ?J"
    by (rule rpred_npJ_Pred[OF M mono m00 m10 br L JBrP])
  \<comment> \<open>tail relation: \<open>tl (butlast ?B) = butlast (tl ?B)\<close>.\<close>
  have tltail: "tl (butlast ?B) = butlast (tl ?B)" by (simp add: butlast_tl)
  \<comment> \<open>both \<open>NJ\<close> expansions.\<close>
  have lhs: "NJ (Pred M) ?J
           = (Joints M ! ?J + 1, npJ M ?J) # butlast (tl ?B)"
    unfolding NJ_def using e0P e1P joints np blkEq tltail by simp
  have rhs0: "NJ M ?J = (Joints M ! ?J + 1, npJ M ?J) # tl ?B"
    unfolding NJ_def using m00 m10 by simp
  \<comment> \<open>\<open>Pred (NJ M ?J) = butlast (NJ M ?J)\<close> since \<open>Lng (NJ M ?J) = Lng ?B > 1\<close>.\<close>
  have LNJ: "Lng (NJ M ?J) = Lng ?B"
  proof -
    have Bne: "?B \<noteq> []" using Bgt by (cases ?B) auto
    show ?thesis by (rule Lng_NJ[OF Bne])
  qed
  have LNJgt: "1 < Lng (NJ M ?J)" using LNJ Bgt by simp
  have predNJ: "Pred (NJ M ?J) = butlast (NJ M ?J)" using LNJgt by (simp add: Pred_def)
  have "butlast (NJ M ?J) = butlast ((Joints M ! ?J + 1, npJ M ?J) # tl ?B)"
    using rhs0 by simp
  also have "\<dots> = (Joints M ! ?J + 1, npJ M ?J) # butlast (tl ?B)"
  proof -
    have "tl ?B \<noteq> []" using Bgt by (cases ?B) (auto simp: Suc_lessD)
    thus ?thesis by simp
  qed
  finally have rhs: "Pred (NJ M ?J) = (Joints M ! ?J + 1, npJ M ?J) # butlast (tl ?B)"
    using predNJ by simp
  show ?thesis using lhs rhs by simp
qed

text \<open>rpred: the branch block \<open>BL M J = IncrFirst\<^bsup>e\<^sub>J\<^esup>(Red (N\<^sub>J M J))\<close> is non-empty
  (its length is \<open>Lng (Br M ! J) > 0\<close>).\<close>

lemma rpred_BL_nonempty:
  assumes M: "M \<in> PT_PS" and JBr: "J < Lng (Br M)"
  shows "(IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J)) \<noteq> []"
proof -
  have brJne: "Br M ! J \<noteq> []" by (rule Br_component_nonempty[OF M JBr])
  have NJne: "NJ M J \<noteq> []" by (simp add: NJ_def)
  have NJT: "NJ M J \<in> T_PS" using NJne by (simp add: T_PS_def)
  have pos: "0 < Lng (Red (NJ M J))"
  proof -
    have "Lng (Red (NJ M J)) = Lng (NJ M J)" by (rule m_6_5_Lng_Red[OF NJT])
    moreover have "0 < Lng (NJ M J)" using NJne by (cases "NJ M J") auto
    ultimately show ?thesis by simp
  qed
  have leneq: "length ((IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J)))
            = length (Red (NJ M J))" by (rule Lng_funpow_IncrFirst)
  have lenpos: "0 < length ((IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J)))"
    unfolding leneq using pos by simp
  show ?thesis by (rule length_greater_0_conv[THEN iffD1, OF lenpos])
qed

text \<open>rpred: in the length-\<open>1\<close> last-block case the dropped block \<open>BL M (Lng(Br M)-1)\<close>
  has length \<open>1\<close> (its inner \<open>N\<^sub>J\<close> is a singleton).\<close>

lemma rpred_BL_lastlen1:
  assumes M: "M \<in> PT_PS" and JBr: "J < Lng (Br M)" and len1: "Lng (Br M ! J) = 1"
  shows "Lng ((IncrFirst ^^ (Joints M ! J + 1 - npJ M J)) (Red (NJ M J))) = 1"
proof -
  have brJne: "Br M ! J \<noteq> []" by (rule Br_component_nonempty[OF M JBr])
  have NJne: "NJ M J \<noteq> []" by (simp add: NJ_def)
  have NJT: "NJ M J \<in> T_PS" using NJne by (simp add: T_PS_def)
  have LNJ: "Lng (NJ M J) = 1" using Lng_NJ[OF brJne] len1 by simp
  have "Lng (Red (NJ M J)) = Lng (NJ M J)" by (rule m_6_5_Lng_Red[OF NJT])
  hence "Lng (Red (NJ M J)) = 1" using LNJ by simp
  thus ?thesis by simp
qed

text \<open>rpred: CORE-NONTRUNK STEP.  Given the per-branch \<open>Red\<close>/\<open>Pred\<close> commutation IH on
  the recursion arguments \<open>N\<^sub>J M J\<close>, the core-nontrunk obligation
  \<open>Red (Pred M) = Pred (Red M)\<close> holds.  \<open>Red M\<close> and \<open>Red (Pred M)\<close> both unfold via
  @{thm [source] d_Red_core_nontrunk_unfold} (same trunk \<open>diagSeq 0 (TrMax M)\<close> by
  @{thm [source] TrMax_Pred}); the branch tails differ only in the last block, which
  is dropped (singleton case, @{thm [source] rpred_BL_lastlen1}) or
  \<open>butlast\<close>-ed (via @{thm [source] rpred_NJ_lastblock} + the IH +
  @{thm [source] funpow_IncrFirst_butlast}); the interior blocks are verbatim
  (@{thm [source] rpred_NJ_interior}).\<close>

lemma rpred_core_nontrunk_step:
  assumes MT: "M \<in> T_PS" and mono: "monoT M"
    and c0: "entry M 0 0 = 0" and c1: "entry M 1 0 = 0"
    and tne: "TrMax M \<noteq> Lng M - 1"
    and IH: "\<And>J. J < Lng (Br M) \<Longrightarrow> Red (Pred (NJ M J)) = Pred (Red (NJ M J))"
  shows "Red (Pred M) = Pred (Red M)"
proof -
  have nz: "\<not> zeroT M" using mono by (simp add: monoT_def)
  have nmu: "\<not> multiT M" using mono by (simp add: multiT_def)
  have MP: "M \<in> PT_PS" using MT mono by (simp add: PT_PS_def)
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have L: "1 < Lng M"
  proof (rule ccontr)
    assume "\<not> 1 < Lng M"
    moreover have "0 < Lng M" using Mne by (cases M) auto
    ultimately have "Lng M = 1" by linarith
    hence "TrMax M = Lng M - 1" using TrMax_bound[OF MT] by simp
    thus False using tne by simp
  qed
  let ?t = "TrMax M"
  let ?nM = "Lng (Br M)"
  let ?BL = "\<lambda>N J. (IncrFirst ^^ (Joints N ! J + 1 - npJ N J)) (Red (NJ N J))"
  \<comment> \<open>unfold \<open>Red M\<close>.\<close>
  have unfoldR: "Red M = diagSeq 0 ?t @ concat (map (?BL M) [0..<?nM])"
    by (rule d_Red_core_nontrunk_unfold[OF MT nz nmu c0 c1 tne])
  \<comment> \<open>\<open>Pred M\<close> is core-nontrunk.\<close>
  have predbl: "Pred M = butlast M" using L by (simp add: Pred_def)
  have predT: "Pred M \<in> T_PS" by (rule Pred_preserves_T_PS[OF MT])
  have trP: "TrMax (Pred M) = ?t" by (rule TrMax_Pred[OF MT L tne])
  have brMne: "Br M \<noteq> []"
  proof -
    have "Br M = P (seg M (?t + 1) (Lng M - 1))" using tne by (simp add: Br_def)
    moreover have "0 < Lng (seg M (?t + 1) (Lng M - 1))"
    proof -
      have tb: "?t \<le> Lng M - 1" by (rule TrMax_bound[OF MT])
      with tne have "?t < Lng M - 1" by linarith
      thus ?thesis using L by (simp add: Lng_seg)
    qed
    ultimately show ?thesis by (metis P_nonempty)
  qed
  have nMpos: "0 < ?nM" using brMne by (cases "Br M") auto
  have LP: "Lng (Pred M) = Lng M - 1" using L by (simp add: predbl)
  have c0P: "entry (Pred M) 0 0 = 0" using c0 entry_Pred_0[OF L] by simp
  have c1P: "entry (Pred M) 1 0 = 0" using c1 entry_Pred_0[OF L] by simp
  have nmuP: "\<not> multiT (Pred M)" by (rule nonmulti_Pred[OF MT nmu L])
  \<comment> \<open>\<open>Pred (Red M) = diagSeq 0 ?t @ butlast (concat (map (?BL M) [0..<?nM]))\<close>.\<close>
  have LrM: "Lng (Red M) = Lng M" by (rule m_6_5_Lng_Red[OF MT])
  have LrMgt: "1 < Lng (Red M)" using LrM L by simp
  have concatMne: "concat (map (?BL M) [0..<?nM]) \<noteq> []"
  proof -
    have ne0: "?BL M 0 \<noteq> []" by (rule rpred_BL_nonempty[OF MP]) (use nMpos in simp)
    have split0: "[0..<?nM] = 0 # [1..<?nM]" using nMpos by (simp add: upt_conv_Cons)
    have "concat (map (?BL M) [0..<?nM]) = ?BL M 0 @ concat (map (?BL M) [1..<?nM])"
      by (subst split0) simp
    thus ?thesis using ne0 by simp
  qed
  have predRedM: "Pred (Red M) = diagSeq 0 ?t @ butlast (concat (map (?BL M) [0..<?nM]))"
  proof -
    have "Pred (Red M) = butlast (Red M)" using LrMgt by (simp add: Pred_def)
    also have "\<dots> = butlast (diagSeq 0 ?t @ concat (map (?BL M) [0..<?nM]))"
      by (simp only: unfoldR)
    also have "\<dots> = diagSeq 0 ?t @ butlast (concat (map (?BL M) [0..<?nM]))"
      by (simp only: butlast_append if_not_P[OF concatMne])
    finally show ?thesis .
  qed
  \<comment> \<open>reduce to the concat residual.\<close>
  have residual: "concat (map (?BL (Pred M)) [0..<Lng (Br (Pred M))])
                = butlast (concat (map (?BL M) [0..<?nM]))"
  proof (cases "Lng (last (Br M)) \<le> 1")
    case singleton: True
    \<comment> \<open>last block dropped; \<open>Lng (Br (Pred M)) = ?nM - 1\<close> and interior blocks verbatim.\<close>
    have brEq: "Br (Pred M) = butlast (Br M)"
      using m_6_6_Br_Pred[OF MT c0 c1 tne L] singleton by simp
    have lenP: "Lng (Br (Pred M)) = ?nM - 1" using brEq brMne by simp
    \<comment> \<open>concat over \<open>M\<close> splits: prefix + last block; last block is length 1.\<close>
    have last_in: "last (Br M) = Br M ! (?nM - 1)" using brMne by (simp add: last_conv_nth)
    have JlastBr: "?nM - 1 < ?nM" using nMpos by simp
    have lastlen1: "Lng (last (Br M)) = 1"
    proof -
      have "0 < Lng (last (Br M))"
      proof -
        have "last (Br M) \<in> set (Br M)" using brMne by simp
        moreover have "Br M ! (?nM - 1) \<noteq> []"
          by (rule Br_component_nonempty[OF MP JlastBr])
        ultimately show ?thesis using last_in by (cases "last (Br M)") auto
      qed
      thus ?thesis using singleton by linarith
    qed
    have BLlast_len1: "Lng (?BL M (?nM - 1)) = 1"
      using rpred_BL_lastlen1[OF MP JlastBr] lastlen1 last_in by simp
    \<comment> \<open>split the \<open>M\<close>-range into \<open>[0..<?nM-1]\<close> and \<open>[?nM-1]\<close>.\<close>
    have rangeM: "[0..<?nM] = [0..<?nM - 1] @ [?nM - 1]"
      using nMpos by (simp add: upt_Suc_append[symmetric])
    have concatM_split: "concat (map (?BL M) [0..<?nM])
                       = concat (map (?BL M) [0..<?nM - 1]) @ ?BL M (?nM - 1)"
      using rangeM by simp
    have but_concat: "butlast (concat (map (?BL M) [0..<?nM]))
                    = concat (map (?BL M) [0..<?nM - 1])"
    proof -
      have len1: "length (?BL M (?nM - 1)) = 1" using BLlast_len1 by simp
      have BLne: "?BL M (?nM - 1) \<noteq> []"
        by (rule length_greater_0_conv[THEN iffD1]) (simp only: len1)
      have butnil: "butlast (?BL M (?nM - 1)) = []"
      proof -
        have "length (butlast (?BL M (?nM - 1))) = 0"
          by (simp only: length_butlast len1 diff_self_eq_0)
        thus ?thesis by (rule length_0_conv[THEN iffD1])
      qed
      have "butlast (concat (map (?BL M) [0..<?nM]))
            = butlast (concat (map (?BL M) [0..<?nM - 1]) @ ?BL M (?nM - 1))"
        using concatM_split by simp
      also have "\<dots> = concat (map (?BL M) [0..<?nM - 1]) @ butlast (?BL M (?nM - 1))"
        by (simp only: butlast_append if_not_P[OF BLne])
      also have "\<dots> = concat (map (?BL M) [0..<?nM - 1])" using butnil by simp
      finally show ?thesis .
    qed
    \<comment> \<open>interior blocks agree.\<close>
    have interior: "map (?BL (Pred M)) [0..<?nM - 1] = map (?BL M) [0..<?nM - 1]"
    proof (rule map_cong[OF refl])
      fix J assume "J \<in> set [0..<?nM - 1]"
      hence Jlt: "J < ?nM - 1" by simp
      have JBrP: "J < Lng (Br (Pred M))" using Jlt lenP by simp
      have JBr: "J < ?nM" using Jlt by simp
      have joints: "Joints (Pred M) ! J = Joints M ! J"
        by (rule rpred_Joints_Pred[OF MT mono c0 c1 tne L JBrP])
      have np: "npJ (Pred M) J = npJ M J"
        by (rule rpred_npJ_Pred[OF MT mono c0 c1 tne L JBrP])
      have njeq: "NJ (Pred M) J = NJ M J"
        by (rule rpred_NJ_interior[OF MT mono c0 c1 tne L Jlt JBrP])
      show "?BL (Pred M) J = ?BL M J" by (simp only: joints np njeq)
    qed
    have "concat (map (?BL (Pred M)) [0..<Lng (Br (Pred M))])
        = concat (map (?BL (Pred M)) [0..<?nM - 1])" using lenP by simp
    also have "\<dots> = concat (map (?BL M) [0..<?nM - 1])" by (simp only: interior)
    also have "\<dots> = butlast (concat (map (?BL M) [0..<?nM]))" by (rule but_concat[symmetric])
    finally show ?thesis .
  next
    case nonsing: False
    have lastgt: "1 < Lng (last (Br M))" using nonsing by simp
    \<comment> \<open>last block \<open>butlast\<close>-ed; \<open>Lng (Br (Pred M)) = ?nM\<close>.\<close>
    obtain lenEq blkEq where
      lenEq: "Lng (Br (Pred M)) = ?nM" and
      blkEq: "Br (Pred M) ! (?nM - 1) = butlast (Br M ! (?nM - 1))"
      using rpred_lastblock_Pred[OF MT c0 c1 tne L lastgt] by auto
    have last_in: "last (Br M) = Br M ! (?nM - 1)" using brMne by (simp add: last_conv_nth)
    have JlastBr: "?nM - 1 < ?nM" using nMpos by simp
    \<comment> \<open>split both ranges into \<open>[0..<?nM-1]\<close> and \<open>[?nM-1]\<close>.\<close>
    have rangeM: "[0..<?nM] = [0..<?nM - 1] @ [?nM - 1]"
      using nMpos by (simp add: upt_Suc_append[symmetric])
    have concatM_split: "concat (map (?BL M) [0..<?nM])
                       = concat (map (?BL M) [0..<?nM - 1]) @ ?BL M (?nM - 1)"
      using rangeM by simp
    have concatP_split: "concat (map (?BL (Pred M)) [0..<Lng (Br (Pred M))])
                       = concat (map (?BL (Pred M)) [0..<?nM - 1]) @ ?BL (Pred M) (?nM - 1)"
      using rangeM lenEq by simp
    \<comment> \<open>interior blocks agree.\<close>
    have interior: "map (?BL (Pred M)) [0..<?nM - 1] = map (?BL M) [0..<?nM - 1]"
    proof (rule map_cong[OF refl])
      fix J assume "J \<in> set [0..<?nM - 1]"
      hence Jlt: "J < ?nM - 1" by simp
      have JBrP: "J < Lng (Br (Pred M))" using Jlt lenEq by simp
      have joints: "Joints (Pred M) ! J = Joints M ! J"
        by (rule rpred_Joints_Pred[OF MT mono c0 c1 tne L JBrP])
      have np: "npJ (Pred M) J = npJ M J"
        by (rule rpred_npJ_Pred[OF MT mono c0 c1 tne L JBrP])
      have njeq: "NJ (Pred M) J = NJ M J"
        by (rule rpred_NJ_interior[OF MT mono c0 c1 tne L Jlt JBrP])
      show "?BL (Pred M) J = ?BL M J" by (simp only: joints np njeq)
    qed
    \<comment> \<open>last block: \<open>?BL (Pred M) (?nM-1) = butlast (?BL M (?nM-1))\<close> via the IH.\<close>
    have JBrP_last: "?nM - 1 < Lng (Br (Pred M))" using JlastBr lenEq by simp
    have joints_last: "Joints (Pred M) ! (?nM - 1) = Joints M ! (?nM - 1)"
      by (rule rpred_Joints_Pred[OF MT mono c0 c1 tne L JBrP_last])
    have np_last: "npJ (Pred M) (?nM - 1) = npJ M (?nM - 1)"
      by (rule rpred_npJ_Pred[OF MT mono c0 c1 tne L JBrP_last])
    have njlast: "NJ (Pred M) (?nM - 1) = Pred (NJ M (?nM - 1))"
      by (rule rpred_NJ_lastblock[OF MT mono c0 c1 tne L lastgt])
    have ihlast: "Red (Pred (NJ M (?nM - 1))) = Pred (Red (NJ M (?nM - 1)))"
      by (rule IH[OF JlastBr])
    \<comment> \<open>\<open>Red (NJ M (?nM-1))\<close> has length \<open>> 1\<close>, so \<open>Pred = butlast\<close>.\<close>
    have brJne: "Br M ! (?nM - 1) \<noteq> []" by (rule Br_component_nonempty[OF MP JlastBr])
    have Bgt: "1 < Lng (Br M ! (?nM - 1))" using lastgt last_in by simp
    have NJne: "NJ M (?nM - 1) \<noteq> []" by (simp add: NJ_def)
    have NJT: "NJ M (?nM - 1) \<in> T_PS" using NJne by (simp add: T_PS_def)
    have LNJgt: "1 < Lng (Red (NJ M (?nM - 1)))"
    proof -
      have "Lng (Red (NJ M (?nM - 1))) = Lng (NJ M (?nM - 1))" by (rule m_6_5_Lng_Red[OF NJT])
      moreover have "Lng (NJ M (?nM - 1)) = Lng (Br M ! (?nM - 1))" by (rule Lng_NJ[OF brJne])
      ultimately show ?thesis using Bgt by simp
    qed
    have predRedNJ: "Pred (Red (NJ M (?nM - 1))) = butlast (Red (NJ M (?nM - 1)))"
      using LNJgt by (simp add: Pred_def)
    have BLlast: "?BL (Pred M) (?nM - 1) = butlast (?BL M (?nM - 1))"
    proof -
      have "?BL (Pred M) (?nM - 1)
          = (IncrFirst ^^ (Joints M ! (?nM - 1) + 1 - npJ M (?nM - 1)))
              (Red (Pred (NJ M (?nM - 1))))"
        using joints_last np_last njlast by simp
      also have "\<dots> = (IncrFirst ^^ (Joints M ! (?nM - 1) + 1 - npJ M (?nM - 1)))
              (butlast (Red (NJ M (?nM - 1))))"
        using ihlast predRedNJ by simp
      also have "\<dots> = butlast ((IncrFirst ^^ (Joints M ! (?nM - 1) + 1 - npJ M (?nM - 1)))
              (Red (NJ M (?nM - 1))))"
        by (simp add: funpow_IncrFirst_butlast)
      finally show ?thesis .
    qed
    \<comment> \<open>assemble: butlast acts on the last block (it is non-empty).\<close>
    have BLlastM_ne: "?BL M (?nM - 1) \<noteq> []" by (rule rpred_BL_nonempty[OF MP JlastBr])
    have "concat (map (?BL (Pred M)) [0..<Lng (Br (Pred M))])
        = concat (map (?BL M) [0..<?nM - 1]) @ butlast (?BL M (?nM - 1))"
      by (simp only: concatP_split interior BLlast)
    also have "\<dots> = butlast (concat (map (?BL M) [0..<?nM - 1]) @ ?BL M (?nM - 1))"
      by (simp only: butlast_append if_not_P[OF BLlastM_ne])
    also have "\<dots> = butlast (concat (map (?BL M) [0..<?nM]))"
      using concatM_split by simp
    finally show ?thesis .
  qed
  \<comment> \<open>conclude, splitting on whether \<open>Pred M\<close> retains a branch region.\<close>
  show ?thesis
  proof (cases "Br (Pred M) = []")
    case brPemp: True
    \<comment> \<open>\<open>Pred M\<close> is core-trunk: \<open>Red (Pred M) = diagSeq 0 (Lng (Pred M) - 1) = diagSeq 0 ?t\<close>,
       and the dropped tail \<open>butlast (concat ...)\<close> is empty (\<open>?nM = 1\<close>, length-1 block).\<close>
    have tPeq: "TrMax (Pred M) = Lng (Pred M) - 1"
    proof (rule ccontr)
      assume "TrMax (Pred M) \<noteq> Lng (Pred M) - 1"
      hence "Br (Pred M) = P (seg (Pred M) (TrMax (Pred M) + 1) (Lng (Pred M) - 1))"
        by (simp add: Br_def)
      hence "Br (Pred M) \<noteq> []" by (metis P_nonempty)
      thus False using brPemp by simp
    qed
    \<comment> \<open>\<open>?nM = 1\<close>: the branch region of \<open>Pred M\<close> is empty, so \<open>Br M\<close> is a singleton.\<close>
    have nM1: "?nM = 1"
    proof -
      have brEq: "Br (Pred M) =
               butlast (Br M)
               @ (if Lng (last (Br M)) \<le> 1 then [] else [butlast (last (Br M))])"
        by (rule m_6_6_Br_Pred[OF MT c0 c1 tne L])
      have butBrnil: "butlast (Br M) = []"
        using brPemp brEq by (cases "Lng (last (Br M)) \<le> 1") auto
      have "length (butlast (Br M)) = 0" using butBrnil by simp
      hence "Lng (Br M) - 1 = 0" by (simp only: length_butlast)
      thus ?thesis using nMpos by linarith
    qed
    have JlastBr0: "(0::nat) < ?nM" using nMpos by simp
    have last_in: "last (Br M) = Br M ! 0" using brMne nM1 by (simp add: last_conv_nth)
    have lastlen1: "Lng (last (Br M)) = 1"
    proof -
      \<comment> \<open>\<open>Lng (last (Br M)) \<le> 1\<close> forced by \<open>Br (Pred M) = []\<close> + singleton.\<close>
      have brEq: "Br (Pred M) =
               butlast (Br M)
               @ (if Lng (last (Br M)) \<le> 1 then [] else [butlast (last (Br M))])"
        by (rule m_6_6_Br_Pred[OF MT c0 c1 tne L])
      have "\<not> (1 < Lng (last (Br M)))"
      proof
        assume "1 < Lng (last (Br M))"
        hence "Br (Pred M) = butlast (Br M) @ [butlast (last (Br M))]" using brEq by simp
        thus False using brPemp by simp
      qed
      moreover have "0 < Lng (last (Br M))"
      proof -
        have "Br M ! 0 \<noteq> []" by (rule Br_component_nonempty[OF MP JlastBr0])
        thus ?thesis using last_in by (cases "last (Br M)") auto
      qed
      ultimately show ?thesis by linarith
    qed
    have BLlast_len1: "Lng (?BL M 0) = 1"
      using rpred_BL_lastlen1[OF MP JlastBr0] lastlen1 last_in by simp
    \<comment> \<open>concat over \<open>M\<close> is the single block \<open>?BL M 0\<close>, length 1, so butlast is \<open>[]\<close>.\<close>
    have concatM_one: "concat (map (?BL M) [0..<?nM]) = ?BL M 0" using nM1 by simp
    have but_empty: "butlast (concat (map (?BL M) [0..<?nM])) = []"
    proof -
      have len1: "length (?BL M 0) = 1" using BLlast_len1 by simp
      have "length (butlast (?BL M 0)) = 0"
        by (simp only: length_butlast len1 diff_self_eq_0)
      hence "butlast (?BL M 0) = []" by (rule length_0_conv[THEN iffD1])
      thus ?thesis using concatM_one by simp
    qed
    \<comment> \<open>\<open>Red (Pred M)\<close> on the core-trunk branch (or zeroT when \<open>Lng (Pred M) = 1\<close>).\<close>
    have predT': "Pred M \<in> T_PS" using predT .
    have domP: "Red_dom (Pred M)" by (rule m_6_5_Red_welldef[OF predT'])
    have redPred: "Red (Pred M) = diagSeq 0 ?t"
    proof (cases "zeroT (Pred M)")
      case True
      have L1P: "Lng (Pred M) = 1" using True by (simp add: zeroT_def)
      have "?t = 0" using trP tPeq L1P by simp
      hence "diagSeq 0 ?t = [(0,0)]" by (simp add: diagSeq_def)
      moreover have "Red (Pred M) = [(0,0)]" using Red.psimps[OF domP] True by simp
      ultimately show ?thesis by simp
    next
      case False
      have nmuP': "\<not> multiT (Pred M)" using nmuP .
      have "Red (Pred M) = diagSeq (entry (Pred M) 1 0) (entry (Pred M) 1 0 + (Lng (Pred M) - 1))"
        using Red.psimps[OF domP] False nmuP' c0P c1P tPeq by (simp add: Let_def)
      also have "\<dots> = diagSeq 0 (Lng (Pred M) - 1)" using c1P by simp
      also have "\<dots> = diagSeq 0 ?t" using tPeq trP by simp
      finally show ?thesis .
    qed
    show ?thesis using redPred predRedM but_empty by simp
  next
    case brPne: False
    \<comment> \<open>\<open>Pred M\<close> is core-nontrunk: unfold and use the concat residual.\<close>
    have tneP: "TrMax (Pred M) \<noteq> Lng (Pred M) - 1"
    proof
      assume "TrMax (Pred M) = Lng (Pred M) - 1"
      hence "Br (Pred M) = []" by (simp add: Br_def)
      with brPne show False by simp
    qed
    have LPgt: "1 < Lng (Pred M)"
    proof -
      have tbP: "TrMax (Pred M) \<le> Lng (Pred M) - 1" by (rule TrMax_bound[OF predT])
      have "0 < Lng (Pred M)" using LP L by linarith
      thus ?thesis using tneP tbP by linarith
    qed
    have nzP: "\<not> zeroT (Pred M)" using LPgt by (simp add: zeroT_def)
    have unfoldRP: "Red (Pred M)
                  = diagSeq 0 ?t @ concat (map (?BL (Pred M)) [0..<Lng (Br (Pred M))])"
    proof -
      have "Red (Pred M)
          = diagSeq 0 (TrMax (Pred M)) @ concat (map (?BL (Pred M)) [0..<Lng (Br (Pred M))])"
        by (rule d_Red_core_nontrunk_unfold[OF predT nzP nmuP c0P c1P tneP])
      thus ?thesis using trP by simp
    qed
    show ?thesis using unfoldRP predRedM residual by simp
  qed
qed

end
