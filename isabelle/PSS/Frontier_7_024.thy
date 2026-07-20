theory Frontier_7_024
  imports Support_7_020
begin

text \<open>Helper: \<open>find\<close> distributes over append (local copy, name-independent).\<close>

lemma find_append_local:
  "find Q (xs @ ys) = (case find Q xs of None \<Rightarrow> find Q ys | Some r \<Rightarrow> Some r)"
  by (induction xs) auto

text \<open>Helper: the first \<open>D\<close>-symbol of a nonzero term's flat string carries its
  leftmost principal value \<open>bpHeadV\<close>.  (Single principal: the string starts with
  that \<open>Dsym\<close>; multi principal: it starts \<open>LP\<close> then that \<open>Dsym\<close>.)\<close>

lemma bpHeadV_find_Dsym:
  assumes "t \<noteq> 0\<^sub>B"
  shows "find (\<lambda>x. \<exists>v. x = Dsym v) (flatBT t) = Some (Dsym (bpHeadV t))"
proof -
  obtain ps where t: "t = Trm ps" by (cases t)
  have psne: "ps \<noteq> []" using assms t by auto
  obtain p qs where psc: "ps = p # qs" using psne by (cases ps) auto
  obtain w u where pwu: "p = DB w u" by (cases p)
  have bh: "bpHeadV t = w" using t psc pwu by simp
  show ?thesis
  proof (cases qs)
    case Nil
    have "flatBT t = Dsym w # flatBT u" using t psc pwu Nil by simp
    thus ?thesis using bh by simp
  next
    case (Cons q qs')
    have "flatBT t = LP # (Dsym w # flatBT u
                           @ concat (map (\<lambda>r. CM # flatBP r) (q # qs'))) @ [RP]"
      using t psc pwu Cons by simp
    hence "flatBT t = LP # Dsym w # (flatBT u
                           @ concat (map (\<lambda>r. CM # flatBP r) (q # qs')) @ [RP])"
      by simp
    thus ?thesis using bh by simp
  qed
qed

section \<open>§7.3 命題（\<open>Trans\<close> の最左単項成分の左端の基本性質）— content.md 2339\<close>

text \<open>Helper: a reduced pair sequence whose row-0 left end is \<open>0\<close> has its row-1
  left end \<open>0\<close> as well.  By strong \<open>Lng\<close>-induction: zero is \<open>[(0,0)]\<close>; mono uses
  @{thm [source] kfwd_reduced_monoT_diag00} (\<open>m\<^sub>0\<^sub>0 = m\<^sub>1\<^sub>0\<close>); multi recurses into
  the reduced prefix \<open>take (Pcut M) M\<close>, which shares the left column.\<close>

lemma reduced_e10_zero:
  "M \<in> RT_PS \<longrightarrow> entry M 0 0 = 0 \<longrightarrow> entry M 1 0 = 0"
proof (induction M rule: measure_induct_rule[where f=Lng])
  case (less M)
  show ?case
  proof (intro impI)
    assume MR: "M \<in> RT_PS" and e00: "entry M 0 0 = 0"
    have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
    have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
    show "entry M 1 0 = 0"
    proof (cases "zeroT M")
      case True
      thus ?thesis by (simp add: zeroT_def)
    next
      case nz: False
      show ?thesis
      proof (cases "monoT M")
        case mono: True
        have "entry M 0 0 = entry M 1 0"
          by (rule kfwd_reduced_monoT_diag00[OF MR mono])
        thus ?thesis using e00 by simp
      next
        case nmono: False
        have muM: "multiT M" using nz nmono by (simp add: multiT_def)
        have L: "1 < Lng M" by (rule multiT_imp_Lng_gt1[OF MT muM])
        have cut: "0 < Pcut M \<and> Pcut M \<le> Lng M - 1" using Pcut_le[OF L] by simp
        let ?A = "take (Pcut M) M"
        have Acut_RT: "?A \<in> RT_PS" by (rule trans_multiT_prefix_RT_PS[OF MR muM])
        have LA: "Lng ?A < Lng M"
        proof -
          have "Pcut M < Lng M" using cut L by linarith
          thus ?thesis by (simp add: min_def)
        qed
        have eA00: "entry ?A 0 0 = entry M 0 0"
        proof -
          have "(0::nat) < Pcut M" using cut by simp
          thus ?thesis by (simp add: entry_def)
        qed
        have eA10: "entry ?A 1 0 = entry M 1 0"
        proof -
          have "(0::nat) < Pcut M" using cut by simp
          thus ?thesis by (simp add: entry_def)
        qed
        have "entry ?A 1 0 = 0"
          using less.IH[OF LA] Acut_RT eA00 e00 by simp
        thus ?thesis using eA10 by simp
      qed
    qed
  qed
qed

end
