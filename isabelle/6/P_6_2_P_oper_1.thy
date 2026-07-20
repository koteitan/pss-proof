theory P_6_2_P_oper_1
  imports Frontier_6_010
begin

text \<open>命題（\<open>P\<close>と基本列の関係） — relation between \<open>P\<close> and the fundamental
  sequence (here \<open>P(M)\<^bsub>J\<^sub>1\<^esub> = last (P M)\<close>, \<open>(P(M)\<^sub>J)\<^bsub>J=0\<^esub>\<^bsup>J\<^sub>1-1\<^esup> = butlast (P M)\<close>).\<close>

text \<open>
  Case (1): when the last \<open>P\<close>-component has length 1.  If \<open>P M\<close> is a singleton
  then \<open>Lng M = 1\<close> and the operator is the identity; otherwise \<open>M\<close> is multi with
  \<open>Pcut M = Lng M - 1\<close>, the last index has no \<open>nextR\<close>-parent, so \<open>M[n] = Pred M\<close>.
\<close>

lemma m_6_2_P_oper_1:
  assumes M: "M \<in> T_PS" and n: "n \<ge> 1" and last1: "Lng (last (P M)) = 1"
  shows "M[n] = Pred M
       \<and> (if length (P M) = 1 then P (M[n]) = [(M[n])] else P (M[n]) = butlast (P M))"
proof (cases "length (P M) = 1")
  case sing: True
  hence notmulti: "\<not> multiT M" using m_6_2_P_components_2[OF M] by (simp del: P.simps)
  have PM: "P M = [M]"
  proof (cases "multiT M \<and> 1 < Lng M")
    case True thus ?thesis using notmulti by simp
  next
    case False thus ?thesis by (rule poper_P_nonmulti)
  qed
  hence "last (P M) = M" by simp
  hence L1: "Lng M = 1" using last1 by simp
  have op: "M[n] = M" using L1 by (simp add: oper_def Let_def)
  have pred: "Pred M = M" using L1 by (simp add: Pred_def)
  have "P (M[n]) = [(M[n])]" using op PM by (simp del: P.simps)
  thus ?thesis using op pred sing by (simp del: P.simps)
next
  case notsing: False
  have multi: "multiT M"
  proof -
    have "length (P M) > 1" using notsing P_nonempty[of M] by (cases "P M") auto
    thus ?thesis using m_6_2_P_components_2[OF M] by (simp del: P.simps)
  qed
  have L: "1 < Lng M" using multiT_imp_Lng_gt1[OF M multi] .
  let ?c = "Pcut M"
  have lastP: "last (P M) = drop ?c M" and butP: "butlast (P M) = P (take ?c M)"
    using poper_last_P_multi[OF multi L] by auto
  from Pcut_le[OF L] have c0: "0 < ?c" and cj1: "?c \<le> Lng M - 1" by auto
  have cL: "?c < Lng M" using cj1 L by linarith
  have lenD: "Lng (drop ?c M) = Lng M - ?c" by simp
  \<comment> \<open>the last component has length 1, so the cut is at the very end\<close>
  have "Lng (drop ?c M) = 1" using last1 lastP by simp
  hence ceq: "?c = Lng M - 1" using lenD cj1 cL by linarith
  \<comment> \<open>no \<open>nextR\<close>-parent of the last index, hence \<open>M[n] = Pred M\<close>\<close>
  have noparent: "\<not> hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
  proof
    assume "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    then obtain j0 where j0: "nextR M (idx1 M (Lng M - 1)) j0 (Lng M - 1)"
      unfolding hasParent_def by auto
    have "?c \<le> j0" using poper_parent_ge_c[OF M multi L j0] .
    moreover have "j0 < Lng M - 1" using poper_nextR_imp_le0[OF j0] by simp
    ultimately show False using ceq by simp
  qed
  have nz: "Lng M - 1 \<noteq> 0" using L by simp
  have op: "M[n] = Pred M"
  proof (cases "entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0")
    case True thus ?thesis using nz by (simp add: oper_def Let_def)
  next
    case False thus ?thesis using noparent nz by (simp add: oper_def Let_def)
  qed
  \<comment> \<open>\<open>P(M[n]) = P(Pred M) = P(take ?c M) = butlast (P M)\<close>\<close>
  have predtake: "Pred M = take ?c M" using ceq L by (simp add: Pred_def butlast_conv_take)
  have "P (M[n]) = P (take ?c M)" using op predtake by simp
  also have "\<dots> = butlast (P M)" using butP by simp
  finally have "P (M[n]) = butlast (P M)" .
  thus ?thesis using op notsing by (simp del: P.simps)
qed


lemma p_6_2_P_oper_1:
  assumes "M \<in> T_PS" "n \<ge> 1" "Lng (last (P M)) = 1"
  shows "M[n] = Pred M
       \<and> (if length (P M) = 1 then P (M[n]) = [(M[n])] else P (M[n]) = butlast (P M))"
  using assms by (rule m_6_2_P_oper_1)

end
