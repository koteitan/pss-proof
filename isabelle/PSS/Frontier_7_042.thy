theory Frontier_7_042
  imports Support_7_036
begin

lemma nth_cnst:
  assumes "j < Suc j1"
  shows "(cnst u j1) ! j = (u, u)"
  by (rule nth_replicate[OF assms])

lemma entry_cnst:
  assumes "j < Suc j1"
  shows "entry (cnst u j1) i j = u"
  unfolding entry_def using nth_cnst[OF assms] by simp

lemma cnst_T_PS: "cnst u j1 \<in> T_PS"
  by (simp add: T_PS_def)

text \<open>No row has a parent in a constant sequence: \<open>nextrel0\<close> / \<open>nextrel1\<close>
  both require a strict increase in the corresponding row, impossible here.\<close>

lemma not_nextrel0_cnst: "\<not> nextrel0 (cnst u j1) j0 j1'"
proof
  assume h: "nextrel0 (cnst u j1) j0 j1'"
  hence b0: "j0 < Suc j1" and b1: "j1' < Suc j1"
    and lt: "entry (cnst u j1) 0 j0 < entry (cnst u j1) 0 j1'"
    by (auto simp: nextrel0_def Lng_cnst)
  have "entry (cnst u j1) 0 j0 = u" using b0 by (rule entry_cnst)
  moreover have "entry (cnst u j1) 0 j1' = u" using b1 by (rule entry_cnst)
  ultimately show False using lt by simp
qed

lemma not_nextrel1_cnst: "\<not> nextrel1 (cnst u j1) j0 j1'"
proof
  assume h: "nextrel1 (cnst u j1) j0 j1'"
  hence b0: "j0 < Suc j1" and b1: "j1' < Suc j1"
    and lt: "entry (cnst u j1) 1 j0 < entry (cnst u j1) 1 j1'"
    by (auto simp: nextrel1_def Lng_cnst)
  have "entry (cnst u j1) 1 j0 = u" using b0 by (rule entry_cnst)
  moreover have "entry (cnst u j1) 1 j1' = u" using b1 by (rule entry_cnst)
  ultimately show False using lt by simp
qed

lemma not_nextR_cnst: "\<not> nextR (cnst u j1) i j0 j1'"
  unfolding nextR_def
  using not_nextrel0_cnst not_nextrel1_cnst by simp

lemma not_hasParent_cnst: "\<not> hasParent (cnst u j1) i j1'"
  unfolding hasParent_def
proof
  assume "\<exists>!j0. nextR (cnst u j1) i j0 j1'"
  then obtain j0 where "nextR (cnst u j1) i j0 j1'" by blast
  thus False using not_nextR_cnst by simp
qed

lemma RedCondA_cnst: "RedCondA (cnst u j1)"
  unfolding RedCondA_def using not_hasParent_cnst by blast

lemma RedCondB_cnst: "RedCondB (cnst u j1)"
  unfolding RedCondB_def
proof (intro allI impI)
  fix j1' assume "\<not> hasParent (cnst u j1) 0 j1' \<and> j1' \<le> Lng (cnst u j1) - 1"
  hence jlt: "j1' < Suc j1" by simp
  show "entry (cnst u j1) 0 j1' = entry (cnst u j1) 1 j1'"
    using entry_cnst[OF jlt, of u 0] entry_cnst[OF jlt, of u 1] by simp
qed

lemma cnst_RT_PS: "cnst u j1 \<in> RT_PS"
  using m_6_6_reduced_iff_cond[OF cnst_T_PS] RedCondA_cnst RedCondB_cnst by blast

lemma not_monoT_cnst_pos:
  assumes "0 < j1"
  shows "\<not> monoT (cnst u j1)"
proof
  assume "monoT (cnst u j1)"
  hence le: "leR (cnst u j1) 0 0 (Lng (cnst u j1) - 1)" by (simp add: monoT_def)
  have "le0 (cnst u j1) 0 j1" using le by (simp add: leR_def)
  hence rt: "(nextrel0 (cnst u j1))\<^sup>*\<^sup>* 0 j1" by (simp add: le0_def)
  have "0 = j1"
    using rt by (induction rule: rtranclp_induct) (use not_nextrel0_cnst in auto)
  thus False using assms by simp
qed

lemma multiT_cnst_pos:
  assumes "0 < j1"
  shows "multiT (cnst u j1)"
proof -
  have "\<not> zeroT (cnst u j1)" using assms by (simp add: zeroT_def)
  thus ?thesis using not_monoT_cnst_pos[OF assms] by (simp add: multiT_def)
qed

text \<open>\<open>Pcut (cnst u j\<^sub>1) = j\<^sub>1\<close> for \<open>j\<^sub>1 > 0\<close>: the least \<open>j > 0\<close> with
  \<open>le0 M j j\<^sub>1\<close> is \<open>j\<^sub>1\<close> itself, as \<open>le0\<close> reduces to reflexivity here.\<close>

lemma le0_cnst_iff:
  assumes "a < Suc j1" "b < Suc j1"
  shows "le0 (cnst u j1) a b \<longleftrightarrow> a = b"
proof
  assume "le0 (cnst u j1) a b"
  hence "(nextrel0 (cnst u j1))\<^sup>*\<^sup>* a b" by (simp add: le0_def)
  thus "a = b"
    by (induction rule: rtranclp_induct) (use not_nextrel0_cnst in auto)
next
  assume "a = b"
  thus "le0 (cnst u j1) a b" using assms by (simp add: le0_def)
qed

lemma Pcut_cnst:
  assumes "0 < j1"
  shows "Pcut (cnst u j1) = j1"
  unfolding Pcut_def
proof (rule Least_equality)
  show "0 < j1 \<and> j1 \<le> Lng (cnst u j1) - 1 \<and> leR (cnst u j1) 0 j1 (Lng (cnst u j1) - 1)"
    using assms by (simp add: leR_def le0_def)
next
  fix y assume hy: "0 < y \<and> y \<le> Lng (cnst u j1) - 1 \<and> leR (cnst u j1) 0 y (Lng (cnst u j1) - 1)"
  hence yle: "y \<le> j1" and ylt: "y < Suc j1" and le: "le0 (cnst u j1) y j1"
    by (auto simp: leR_def)
  have "y = j1" using le0_cnst_iff[of y j1 j1 u] ylt le by simp
  thus "j1 \<le> y" by simp
qed

lemma take_cnst: "take j1 (cnst u j1) = cnst u (j1 - 1)" if "0 < j1"
proof -
  have "take j1 (replicate (Suc j1) (u, u)) = replicate (min j1 (Suc j1)) (u, u)"
    by (rule take_replicate)
  also have "\<dots> = replicate j1 (u, u)" by simp
  also have "\<dots> = replicate (Suc (j1 - 1)) (u, u)" using that by simp
  finally show ?thesis .
qed

lemma drop_cnst: "drop j1 (cnst u j1) = [(u, u)]" if "0 < j1"
proof -
  have "drop j1 (replicate (Suc j1) (u, u)) = replicate (Suc j1 - j1) (u, u)"
    by (rule drop_replicate)
  also have "\<dots> = [(u, u)]" by simp
  finally show ?thesis .
qed

lemma P_cnst: "P (cnst u j1) = replicate (Suc j1) [(u, u)]"
proof (induction j1)
  case 0
  have "\<not> (multiT (cnst u 0) \<and> 1 < Lng (cnst u 0))" by simp
  thus ?case by (subst P.simps) simp
next
  case (Suc k)
  have mult: "multiT (cnst u (Suc k))" by (rule multiT_cnst_pos) simp
  have Lgt: "1 < Lng (cnst u (Suc k))" by simp
  have pc: "Pcut (cnst u (Suc k)) = Suc k" by (rule Pcut_cnst) simp
  have tk: "take (Pcut (cnst u (Suc k))) (cnst u (Suc k)) = cnst u k"
    using pc take_cnst[of "Suc k" u] by simp
  have dp: "drop (Pcut (cnst u (Suc k))) (cnst u (Suc k)) = [(u, u)]"
    using pc drop_cnst[of "Suc k" u] by simp
  have "P (cnst u (Suc k)) = P (cnst u k) @ [[(u, u)]]"
    using mult Lgt tk dp by (subst P.simps) simp
  also have "\<dots> = replicate (Suc k) [(u, u)] @ [[(u, u)]]" using Suc.IH by simp
  also have "\<dots> = replicate (Suc (Suc k)) [(u, u)]"
    by (simp add: replicate_append_same)
  finally show ?case .
qed

text \<open>\<open>seg (cnst u j\<^sub>1) 0 k = cnst u k\<close> for \<open>k < Suc j\<^sub>1\<close> (a prefix of a
  constant sequence is the shorter constant sequence).\<close>

lemma seg_cnst:
  assumes "k \<le> j1"
  shows "seg (cnst u j1) 0 k = cnst u k"
proof -
  have lng: "Suc k \<le> Lng (cnst u j1)" using assms by simp
  have "seg (cnst u j1) 0 k = take (Suc k) (cnst u j1)"
    by (rule seg_0_eq_take[OF lng])
  also have "\<dots> = replicate (min (Suc k) (Suc j1)) (u, u)"
    by (simp only: take_replicate)
  also have "\<dots> = replicate (Suc k) (u, u)"
    using assms by (simp only: min.absorb1 Suc_le_mono)
  finally show ?thesis .
qed

text \<open>命題（公差\<open>(0,0)\<close>のペア数列の\<open>Trans\<close>の基本性質）: the main §8.7 const-00
  computation.  Induction on \<open>j\<^sub>1\<close> through the 複項 branch of \<open>Trans\<close>:
  \<open>P M = replicate (Suc j\<^sub>1) [(u,u)]\<close>, last block \<open>[(u,u)] \<noteq> [(0,0)]\<close> exactly
  when \<open>u > 0\<close>.\<close>

lemma m_8_7_cnst_Trans:
  "Trans (cnst u j1)
     = (if u = 0 then multBT (Dpt (enat u) 0\<^sub>B) j1
        else multBT (Dpt (enat u) 0\<^sub>B) (Suc j1))"
proof (induction j1)
  case 0
  have "Trans (cnst u 0) = Trans [(u, u)]" by simp
  also have "\<dots> = (if u = 0 then 0\<^sub>B else Dpt (enat u) 0\<^sub>B)" by (rule Trans_singleton)
  finally show ?case by simp
next
  case (Suc k)
  let ?M = "cnst u (Suc k)"
  have MR: "?M \<in> RT_PS" by (rule cnst_RT_PS)
  have domT: "Trans_Mark_dom (Inl ?M)" by (rule m_7_3_Trans_welldef[OF MR])
  have mult: "multiT ?M" by (rule multiT_cnst_pos) simp
  have notmono: "\<not> monoT ?M" using mult by (simp add: multiT_def)
  have notzero: "\<not> zeroT ?M" using mult by (simp add: multiT_def)
  have j1ne: "Lng ?M - 1 \<noteq> 0" by simp
  have PM: "P ?M = replicate (Suc (Suc k)) [(u, u)]" by (rule P_cnst)
  have LP: "Lng (P ?M) - 1 = Suc k" using PM by simp
  have PJ: "P ?M ! (Lng (P ?M) - 1) = [(u, u)]"
    using PM LP nth_replicate[of "Suc k" "Suc (Suc k)" "[(u, u)]"] by simp
  have LPJ: "Lng (P ?M ! (Lng (P ?M) - 1)) = 1" using PJ by simp
  \<comment> \<open>the 複項 branch's \<open>seg\<close> argument reduces to \<open>k\<close>\<close>
  have segarg: "(Lng ?M - 1) - Lng (P ?M ! (Lng (P ?M) - 1)) + 1 - 1 = k"
    using LPJ by simp
  have segeq: "seg ?M 0 ((Lng ?M - 1) - Lng (P ?M ! (Lng (P ?M) - 1)) + 1 - 1) = cnst u k"
    using segarg seg_cnst[of k "Suc k" u] by simp
  \<comment> \<open>unfold the 複項 branch of \<open>Trans\<close> once\<close>
  have transval:
    "Trans ?M = (if P ?M ! (Lng (P ?M) - 1) = [(0, 0)]
                 then Trans (seg ?M 0 ((Lng ?M - 1) - Lng (P ?M ! (Lng (P ?M) - 1)) + 1 - 1))
                        +\<^sub>B Dpt 0 0\<^sub>B
                 else Trans (seg ?M 0 ((Lng ?M - 1) - Lng (P ?M ! (Lng (P ?M) - 1)) + 1 - 1))
                        +\<^sub>B Trans (P ?M ! (Lng (P ?M) - 1)))"
    using Trans.psimps[OF domT] MR notmono notzero j1ne by (simp add: Let_def)
  show ?case
  proof (cases "u = 0")
    case True
    have PJ0: "P ?M ! (Lng (P ?M) - 1) = [(0, 0)]" using PJ True by simp
    have "Trans ?M = Trans (cnst u k) +\<^sub>B Dpt 0 0\<^sub>B"
      using transval PJ0 segeq by simp
    also have "\<dots> = multBT (Dpt (enat u) 0\<^sub>B) k +\<^sub>B Dpt (enat u) 0\<^sub>B"
      using Suc.IH True by (simp add: zero_enat_def)
    also have "\<dots> = multBT (Dpt (enat u) 0\<^sub>B) (Suc k)" by simp
    finally show ?thesis using True by simp
  next
    case False
    have PJne: "P ?M ! (Lng (P ?M) - 1) \<noteq> [(0, 0)]" using PJ False by simp
    have "Trans ?M = Trans (cnst u k) +\<^sub>B Trans [(u, u)]"
      using transval PJne segeq PJ by simp
    also have "\<dots> = multBT (Dpt (enat u) 0\<^sub>B) (Suc k) +\<^sub>B Dpt (enat u) 0\<^sub>B"
      using Suc.IH False Trans_singleton by simp
    also have "\<dots> = multBT (Dpt (enat u) 0\<^sub>B) (Suc (Suc k))" by simp
    finally show ?thesis using False by simp
  qed
qed

(* ===== §7.3 Trans-leftmost from wt-7lm ===== *)

section \<open>§7.3 命題（\<open>Trans\<close> の最左単項成分の左端の基本性質） — full form (1)(2)(3)\<close>

text \<open>The article proposition (content.md 2342) states, for every \<open>M \<in> RT\<^bsub>PS\<^esub>\<close>:
  (1) if \<open>P(M)\<^sub>0 = ((0,0))\<close> and \<open>Lng(P(M)) > 1\<close> then the left end of the leftmost
      principal component of \<open>Trans(M)\<close> is \<open>D\<^bsub>M\<^bsub>1,1\<^esub>\<^esub>\<close>;
  (2) if \<open>P(M)\<^sub>0 \<noteq> ((0,0))\<close> then the leftmost principal component of \<open>Trans(M)\<close>
      is \<open>Trans(P(M)\<^sub>0)\<close> and its left end is \<open>D\<^bsub>M\<^bsub>1,0\<^esub>\<^esub>\<close>;
  (3) if \<open>(1,0) <\<^bsub>M\<^esub>\<^sup>Next (1,1)\<close> then the leftmost principal component's left two
      characters are \<open>D\<^bsub>M\<^bsub>1,0\<^esub>\<^esub> D\<^bsub>u\<^esub>\<close> for some \<open>u\<close>.
  The "leftmost principal component" of a \<open>BT\<close> \<open>t\<close> is \<open>PB t ! 0 = Trm [hd (untrm t)]\<close>
  (defined when \<open>t \<noteq> 0\<^sub>B\<close>); its "left end" is \<open>D\<^bsub>bpHeadV t\<^esub>\<close>.

  The scalar left-end core (@{thm [source] m_7_3_Trans_leftend},
  \<open>bpHeadV (Trans M) = enat (entry M 1 0)\<close>) already handles the head value.  The
  substantial new content is (2): the *whole* leftmost principal component equals
  \<open>Trans (P M ! 0)\<close>.  Empirically TRUE: (1)/(2)/(3) hold over 88/1269/340 reduced
  cases (Lng \<le> 5, e \<le> 2), 0 CEX.\<close>

text \<open>The leftmost principal component of an \<open>+\<^sub>B\<close>-join is that of the left
  operand, when the left operand is nonzero.\<close>

lemma PB0_addBT_left:
  assumes "a \<noteq> 0\<^sub>B"
  shows "PB (a +\<^sub>B b) ! 0 = PB a ! 0"
proof -
  obtain as where a: "a = Trm as" by (cases a)
  obtain bs where b: "b = Trm bs" by (cases b)
  have asne: "as \<noteq> []" using assms a by auto
  show ?thesis using a b asne by (simp add: PB_def nth_append)
qed

text \<open>For a single-principal \<open>t\<close> (\<open>Lng (PB t) = 1\<close>), the leftmost principal
  component is \<open>t\<close> itself.\<close>

lemma PB0_principal:
  assumes "Lng (PB t) = 1"
  shows "PB t ! 0 = t"
proof -
  obtain ps where tps: "t = Trm ps" by (cases t)
  from assms have "length ps = 1" by (simp add: PB_def tps)
  then obtain p where psp: "ps = [p]" by (cases ps) auto
  show ?thesis using tps psp by (simp add: PB_def)
qed

end
