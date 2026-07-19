theory P_6_2_P_oper_2
  imports P_6_2_P_oper_1
begin

text \<open>
  Case (2): when the last \<open>P\<close>-component has length \<open>> 1\<close>.  Either \<open>P M\<close> is a
  singleton (then the statement is trivial), or \<open>M\<close> is multi and the expansion
  acts inside the last component \<open>drop (Pcut M) M\<close>; the result follows from
  @{thm [source] poper_oper_drop} and the additivity @{thm [source] m_6_2_P_additive}.
\<close>

lemma m_6_2_P_oper_2:
  assumes M: "M \<in> T_PS" and n: "n \<ge> 1" and lastgt: "Lng (last (P M)) > 1"
  shows "M[n] = concat (butlast (P M)) @ (last (P M))[n]
       \<and> P (M[n]) = butlast (P M) @ P ((last (P M))[n])"
proof (cases "length (P M) = 1")
  case sing: True
  have notmulti: "\<not> multiT M" using sing m_6_2_P_components_2[OF M] by (simp del: P.simps)
  have PM: "P M = [M]"
  proof (cases "multiT M \<and> 1 < Lng M")
    case True thus ?thesis using notmulti by simp
  next
    case False thus ?thesis by (rule poper_P_nonmulti)
  qed
  hence lastM: "last (P M) = M" and butl: "butlast (P M) = []" by simp_all
  show ?thesis using lastM butl PM by simp
next
  case notsing: False
  have multi: "multiT M"
  proof -
    have "length (P M) > 1" using notsing P_nonempty[of M] by (cases "P M") auto
    thus ?thesis using m_6_2_P_components_2[OF M] by (simp del: P.simps)
  qed
  have L: "1 < Lng M" using multiT_imp_Lng_gt1[OF M multi] .
  let ?c = "Pcut M"
  let ?M' = "drop ?c M"
  have lastP: "last (P M) = ?M'" and butP: "butlast (P M) = P (take ?c M)"
    using poper_last_P_multi[OF multi L] by auto
  from Pcut_le[OF L] have c0: "0 < ?c" and cj1: "?c \<le> Lng M - 1"
    and lec: "leR M 0 ?c (Lng M - 1)" by auto
  have cL: "?c < Lng M" using cj1 L by linarith
  have lenD: "Lng ?M' = Lng M - ?c" by simp
  have LD: "1 < Lng ?M'" using lastgt lastP by simp
  have clt: "?c < Lng M - 1" using LD lenD by linarith
  have cdef: "?c = Pcut M" by (rule refl)
  \<comment> \<open>part 1: \<open>M[n] = take ?c M @ ?M'[n]\<close> rewritten via \<open>concat (butlast (P M)) = take ?c M\<close>\<close>
  have concbut: "concat (butlast (P M)) = take ?c M"
    using butP poper_concat_P[of "take ?c M"] by simp
  have op_drop: "M[n] = take ?c M @ ?M'[n]"
    by (rule poper_oper_drop[OF M multi L cdef clt])
  have part1: "M[n] = concat (butlast (P M)) @ (last (P M))[n]"
    using op_drop concbut lastP by simp
  \<comment> \<open>part 2: additivity of \<open>P\<close> applied to \<open>N = M[n] = take ?c M @ ?M'[n]\<close>\<close>
  let ?N = "M[n]"
  have NT: "?N \<in> T_PS"
  proof -
    have "?M'[n] \<noteq> []" using poper_oper_nth0[OF _ LD n] cL by (cases ?M') (auto simp: T_PS_def)
    hence "?N \<noteq> []" using op_drop by simp
    thus ?thesis by (simp add: T_PS_def)
  qed
  have LtakeC: "Lng (take ?c M) = ?c" using cL by simp
  have takeN: "take ?c ?N = take ?c M"
    using op_drop LtakeC by simp
  have dropN: "drop ?c ?N = ?M'[n]"
    using op_drop LtakeC by simp
  \<comment> \<open>head of \<open>?M'[n]\<close> equals head of \<open>?M'\<close>, giving \<open>entry ?N 0 ?c = entry M 0 ?c\<close>\<close>
  have hd': "(?M'[n]) ! 0 = ?M' ! 0" using poper_oper_nth0[OF _ LD n] cL
    by (cases ?M') (auto simp: T_PS_def)
  have NcL: "?c < Lng ?N"
  proof -
    have "?M'[n] \<noteq> []" using poper_oper_nth0[OF _ LD n] cL by (cases ?M') (auto simp: T_PS_def)
    hence "0 < Lng (?M'[n])" by simp
    thus ?thesis using op_drop LtakeC by simp
  qed
  have entryNc: "entry ?N 0 ?c = entry M 0 ?c"
  proof -
    have "?N ! ?c = (?M'[n]) ! 0" using op_drop LtakeC by (simp add: nth_append)
    also have "\<dots> = ?M' ! 0" by (rule hd')
    also have "\<dots> = M ! ?c" using cL by (simp add: nth_drop)
    finally have "?N ! ?c = M ! ?c" .
    thus ?thesis by (simp add: entry_def)
  qed
  \<comment> \<open>left-minimality at \<open>?c\<close>: \<open>entry ?N 0 j \<ge> entry ?N 0 ?c\<close> for \<open>j < ?c\<close>\<close>
  have lmin: "\<And>j. j < ?c \<Longrightarrow> entry ?N 0 j \<ge> entry ?N 0 ?c"
  proof -
    fix j assume jc: "j < ?c"
    have "entry ?N 0 j = entry M 0 j"
    proof -
      have "?N ! j = (take ?c M) ! j" using op_drop jc LtakeC by (simp add: nth_append)
      also have "\<dots> = M ! j" using jc cL by (simp add: nth_take)
      finally show ?thesis by (simp add: entry_def)
    qed
    moreover have "entry M 0 j \<ge> entry M 0 ?c"
      using P_add_Pcut_left_min[OF M multi L jc] .
    ultimately show "entry ?N 0 j \<ge> entry ?N 0 ?c" using entryNc by simp
  qed
  have cN1: "?c \<le> Lng ?N - 1" using NcL by linarith
  have paddseg: "P ?N = P (seg ?N 0 (?c - 1)) @ P (seg ?N ?c (Lng ?N - 1))"
  proof (rule m_6_2_P_additive[OF NT c0 cN1])
    fix j assume "j < ?c" thus "entry ?N 0 ?c \<le> entry ?N 0 j" using lmin by simp
  qed
  have seg1: "seg ?N 0 (?c - 1) = take ?c ?N"
    using NcL c0 by (subst seg_0_eq_take) (auto simp del: P.simps)
  have seg2: "seg ?N ?c (Lng ?N - 1) = drop ?c ?N"
    using NcL by (simp add: drop_eq_seg del: P.simps)
  have padd: "P ?N = P (take ?c ?N) @ P (drop ?c ?N)"
    using paddseg seg1 seg2 by (simp del: P.simps)
  have part2: "P (M[n]) = butlast (P M) @ P ((last (P M))[n])"
    using padd takeN dropN butP lastP by (simp del: P.simps)
  show ?thesis using part1 part2 by blast
qed


lemma p_6_2_P_oper_2:
  assumes "M \<in> T_PS" "n \<ge> 1" "Lng (last (P M)) > 1"
  shows "M[n] = concat (butlast (P M)) @ (last (P M))[n]
       \<and> P (M[n]) = butlast (P M) @ P ((last (P M))[n])"
  using assms by (rule m_6_2_P_oper_2)

end
