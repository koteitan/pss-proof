theory Support_7_047
  imports Frontier_7_051
begin

text \<open>Injectivity corollary: a reduced \<open>M\<close> whose proper initial slice \<open>take n M\<close>
  has the same \<open>Trans\<close> value must in fact be that whole slice (\<open>n = Lng M\<close>).\<close>

lemma Trans_take_eq_imp_full:
  assumes M: "M \<in> RT_PS" and npos: "0 < n" and nle: "n \<le> Lng M"
    and eq: "Trans (take n M) = Trans M"
  shows "n = Lng M"
proof (rule ccontr)
  assume "n \<noteq> Lng M"
  hence nlt: "n < Lng M" using nle by simp
  have "lessBT (Trans (take n M)) (Trans M)"
    by (rule Trans_take_lessBT[OF M npos nlt])
  thus False using eq lessBT_irrefl by simp
qed


text \<open>系（\<open>Trans\<close>と非可算基数の関係） (§7.3, content.md 2372).  Purely
  combinatorial: \<open>D\<^bsub>v\<^esub> 0 = \<psi>\<^bsub>v\<^esub>(0) = \<Omega>\<^bsub>v\<^esub>\<close> only in the NAME; the statement is a
  characterisation of which reduced \<open>M\<close> translate to the single-letter term
  \<open>D\<^bsub>v\<^esub> 0\<close>.  For \<open>v = 0\<close> the witness is \<open>[(0,0),(0,0)]\<close> (\<open>[(0,0)]\<close> translates to
  \<open>0\<^sub>B \<noteq> D\<^bsub>0\<^esub> 0\<close>); for \<open>v > 0\<close> it is the singleton diagonal \<open>[(v,v)]\<close>.\<close>

lemma m_7_3_Trans_Dv0_iff:
  assumes MR: "M \<in> RT_PS"
  shows "Trans M = Dpt (enat v) 0\<^sub>B
          \<longleftrightarrow> ((v = 0 \<and> M = [(0,0),(0,0)]) \<or> (0 < v \<and> M = [(v,v)]))"
proof
  \<comment> \<open>(2) \<Longrightarrow> (1): compute \<open>Trans\<close> on the two witnesses\<close>
  assume "(v = 0 \<and> M = [(0,0),(0,0)]) \<or> (0 < v \<and> M = [(v,v)])"
  thus "Trans M = Dpt (enat v) 0\<^sub>B"
  proof
    assume H: "v = 0 \<and> M = [(0,0),(0,0)]"
    hence v0: "v = 0" and Mw: "M = [(0,0),(0,0)]" by simp_all
    have "Trans ([(0,0),(0,0)]::pairseq) = Dpt 0 0\<^sub>B" by (rule Trans_two_zero)
    thus "Trans M = Dpt (enat v) 0\<^sub>B" using Mw v0 by (simp add: zero_enat_def)
  next
    assume H: "0 < v \<and> M = [(v,v)]"
    hence vpos: "0 < v" and Mw: "M = [(v,v)]" by simp_all
    have "Trans [(v,v)] = Dpt (enat v) 0\<^sub>B"
      using Trans_singleton vpos by simp
    thus "Trans M = Dpt (enat v) 0\<^sub>B" using Mw by simp
  qed
next
  \<comment> \<open>(1) \<Longrightarrow> (2)\<close>
  assume T: "Trans M = Dpt (enat v) 0\<^sub>B"
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have Mne: "M \<noteq> []" using MT by (simp add: T_PS_def)
  have Lpos: "0 < Lng M" using Mne by (cases M) auto
  \<comment> \<open>condB \<Longrightarrow> \<open>entry M 0 0 = entry M 1 0\<close>\<close>
  have condB: "RedCondB M" using m_6_6_reduced_iff_cond[OF MT] MR by simp
  have noPar00: "\<not> hasParent M 0 0"
    by (auto simp: hasParent_def nextR_def nextrel0_def)
  have e00_e10: "entry M 0 0 = entry M 1 0"
    using condB noPar00 Lpos by (auto simp: RedCondB_def)
  show "(v = 0 \<and> M = [(0,0),(0,0)]) \<or> (0 < v \<and> M = [(v,v)])"
  proof (cases "v = 0")
    case v0: True
    \<comment> \<open>\<open>entry M 1 0 = 0\<close> by the \<open>Trans\<close>-leftend basic property\<close>
    have e10_0: "entry M 1 0 = 0"
    proof (rule ccontr)
      assume "entry M 1 0 \<noteq> 0"
      hence pos: "0 < entry M 1 0" by simp
      have head: "bpHeadV (Trans M) = enat (entry M 1 0)"
        using m_7_3_Trans_leftend MR by blast
      have "bpHeadV (Dpt (enat v) 0\<^sub>B) = enat v" by simp
      hence "enat (entry M 1 0) = enat v" using head T by simp
      hence "entry M 1 0 = v" by simp
      thus False using v0 pos by simp
    qed
    \<comment> \<open>\<open>Lng M > 1\<close> (else \<open>M = [(0,0)]\<close>, \<open>Trans M = 0\<^sub>B \<noteq> D\<^bsub>0\<^esub> 0\<close>)\<close>
    have L1: "1 < Lng M"
    proof (rule ccontr)
      assume "\<not> 1 < Lng M"
      hence L1eq: "Lng M = 1" using Lpos by linarith
      obtain p where Mp: "M = [p]" using L1eq by (cases M) auto
      have "p = (0,0)"
      proof -
        have "fst p = entry M 0 0" using Mp by (simp add: entry_def)
        also have "\<dots> = entry M 1 0" by (rule e00_e10)
        also have "\<dots> = 0" by (rule e10_0)
        finally have f0: "fst p = 0" .
        have "snd p = entry M 1 0" using Mp by (simp add: entry_def)
        hence s0: "snd p = 0" using e10_0 by simp
        show ?thesis using f0 s0 by (cases p) simp
      qed
      hence "M = [(0,0)]" using Mp by simp
      hence "Trans M = 0\<^sub>B" using Trans_singleton by simp
      thus False using T by simp
    qed
    \<comment> \<open>\<open>M' = seg M 0 1 = take 2 M\<close>: reduced, length 2\<close>
    have two_le: "Suc 1 \<le> Lng M" using L1 by simp
    define Mp where "Mp = seg M 0 1"
    have Mp_take: "Mp = take 2 M"
    proof -
      have "Mp = take (Suc 1) M" using seg_0_eq_take[OF two_le] Mp_def by simp
      thus ?thesis by (simp add: numeral_2_eq_2)
    qed
    have LMp: "Lng Mp = 2"
    proof -
      have "Lng Mp = min 2 (Lng M)" using Mp_take by simp
      thus ?thesis using two_le by (simp add: numeral_2_eq_2)
    qed
    have oneLe: "(1::nat) \<le> Lng M - 1" using L1 by simp
    have MpRT: "Mp \<in> RT_PS"
      using seg_0_RT_PS[OF MR oneLe] Mp_def by simp
    \<comment> \<open>\<open>Mp = seg M 0 1\<close> shares \<open>M\<close>'s first two columns\<close>
    have eMp: "\<And>i j. j < 2 \<Longrightarrow> entry Mp i j = entry M i j"
    proof -
      fix i j :: nat assume jl: "j < 2"
      have jlt: "j < Lng (seg M 0 1)" using jl LMp Mp_def by simp
      have "entry Mp i j = entry (seg M 0 1) i j" using Mp_def by simp
      also have "\<dots> = entry M i (0 + j)" by (rule entry_seg[OF jlt])
      finally show "entry Mp i j = entry M i j" by simp
    qed
    have eMp00: "entry Mp 0 0 = entry M 0 0" using eMp[where i=0 and j=0] by simp
    have eMp01: "entry Mp 0 1 = entry M 0 1" using eMp[where i=0 and j=1] by simp
    have eMp10: "entry Mp 1 0 = entry M 1 0" using eMp[where i=1 and j=0] by simp
    have eMp11: "entry Mp 1 1 = entry M 1 1" using eMp[where i=1 and j=1] by simp
    \<comment> \<open>\<open>M'\<close> is multi: if mono, the 2-column basic property + descent contradict\<close>
    have e01_0: "entry M 0 1 = 0"
    proof (rule ccontr)
      assume e01: "entry M 0 1 \<noteq> 0"
      \<comment> \<open>if \<open>M'\<close> were mono, \<open>entry M 0 0 < entry M 0 1\<close> forces \<open>entry M 0 0 \<noteq> 0\<close>,
         but reduced+condB makes \<open>entry M' 0 0 = entry M' 1 0\<close>; we instead derive
         the contradiction the article uses (2-column basic property vs descent)\<close>
      have Mpmono: "monoT Mp"
      proof -
        have nz: "\<not> zeroT Mp" using LMp by (simp add: zeroT_def)
        have e0Mp0: "entry Mp 0 0 = entry M 0 0" using eMp00 by simp
        have e0Mp1: "entry Mp 0 1 = entry M 0 1" using eMp01 by simp
        \<comment> \<open>\<open>entry M 0 0 = 0 < entry M 0 1\<close>, so \<open>(0,0) <\<^bsub>M'\<^esub>\<^sup>Next (0,1)\<close>, hence mono\<close>
        have e000: "entry M 0 0 = 0" using e00_e10 e10_0 by simp
        have nr: "nextrel0 Mp 0 1"
          using LMp e0Mp0 e0Mp1 e000 e01
          by (auto simp: nextrel0_def)
        have "le0 Mp 0 1" using nr LMp by (auto simp: le0_def)
        thus ?thesis using nz LMp by (simp add: monoT_def leR_def)
      qed
      have tc: "Trans Mp = Dpt (enat (entry Mp 1 0)) (Dpt (enat (entry Mp 1 1)) 0\<^sub>B)"
        by (rule m_7_3_twoColumn_Trans[OF MpRT Mpmono LMp])
      \<comment> \<open>\<open>entry Mp 1 0 = entry M 1 0 = 0\<close>\<close>
      have e1Mp0: "entry Mp 1 0 = 0"
        using eMp10 e10_0 by simp
      have tcD0: "Trans Mp = Dpt 0 (Dpt (enat (entry Mp 1 1)) 0\<^sub>B)"
        using tc e1Mp0 by (simp add: zero_enat_def)
      \<comment> \<open>descent \<open>Trans Mp \<le> Trans M\<close>: actually \<open>lessBT (Trans (Pred^^) ..) ..\<close>;
         the article uses \<open>D\<^bsub>0\<^esub> 0 = Trans M \<ge> Trans Mp = D\<^bsub>0\<^esub> D\<^bsub>..\<^esub> 0 > D\<^bsub>0\<^esub> 0\<close>.
         We get it directly: \<open>Trans Mp\<close> would lie strictly below \<open>Trans M = D\<^bsub>0\<^esub> 0\<close>,
         yet \<open>Trans Mp = D\<^bsub>0\<^esub> (..)\<close> with a nonzero tail is \<open>> D\<^bsub>0\<^esub> 0\<close>.\<close>
      have lessMp: "lessBT (Trans Mp) (Trans M) \<or> Trans Mp = Trans M"
      proof (cases "Lng M = 2")
        case True
        hence "Mp = M" using Mp_take by simp
        thus ?thesis by simp
      next
        case False
        hence "2 < Lng M" using L1 by simp
        hence "lessBT (Trans Mp) (Trans M)"
          using Trans_take_lessBT[OF MR, of 2] Mp_take by simp
        thus ?thesis by simp
      qed
      \<comment> \<open>\<open>Trans M = D\<^bsub>0\<^esub> 0\<close>; \<open>Trans Mp = D\<^bsub>0\<^esub> (D\<^bsub>b\<^esub> 0)\<close> with the second letter present,
         so \<open>lessBT (Trans M) (Trans Mp)\<close>, contradicting \<open>\<le>\<close>.\<close>
      have lessM_Mp: "lessBT (Trans M) (Trans Mp)"
      proof -
        have "lessBT (Dpt 0 0\<^sub>B) (Dpt 0 (Dpt (enat (entry Mp 1 1)) 0\<^sub>B))"
          by (simp add: zero_enat_def)
        thus ?thesis using T tcD0 v0 by (simp add: zero_enat_def)
      qed
      from lessMp show False
      proof
        assume "lessBT (Trans Mp) (Trans M)"
        hence "lessBT (Trans M) (Trans M)"
          using lessM_Mp lessBT_trans by blast
        thus False using lessBT_irrefl by simp
      next
        assume "Trans Mp = Trans M"
        hence "lessBT (Trans M) (Trans M)" using lessM_Mp by simp
        thus False using lessBT_irrefl by simp
      qed
    qed
    \<comment> \<open>\<open>Mp\<close> is multi (\<open>entry M 0 1 = 0 = entry M 0 0\<close>, so no \<open>nextrel0\<close>): condB on
       \<open>Mp\<close> at column 1 gives \<open>entry M 1 1 = entry M 0 1 = 0\<close>; then
       \<open>Trans Mp = D\<^bsub>0\<^esub> 0 = Trans M\<close>, descent injectivity \<Longrightarrow> \<open>Lng M = 2\<close>\<close>
    have e000: "entry M 0 0 = 0" using e00_e10 e10_0 by simp
    have noPar01_Mp: "\<not> hasParent Mp 0 1"
    proof
      assume "hasParent Mp 0 1"
      then obtain j0 where nx: "nextR Mp 0 j0 1" by (auto simp: hasParent_def)
      hence "nextrel0 Mp j0 1" by (simp add: nextR_def)
      hence j0lt: "j0 < 1" and ent: "entry Mp 0 j0 < entry Mp 0 1"
        by (auto simp: nextrel0_def)
      hence j0eq: "j0 = 0" by simp
      have "entry Mp 0 0 = entry M 0 0" using eMp00 by simp
      moreover have "entry Mp 0 1 = entry M 0 1" using eMp01 by simp
      ultimately show False using ent j0eq e000 e01_0 by simp
    qed
    have MpT: "Mp \<in> T_PS" using MpRT by (simp add: RT_PS_def)
    have condB_Mp: "RedCondB Mp"
      using m_6_6_reduced_iff_cond[OF MpT] MpRT by simp
    have e1Mp1_eq: "entry Mp 0 1 = entry Mp 1 1"
      using condB_Mp noPar01_Mp LMp by (auto simp: RedCondB_def)
    have e0Mp1: "entry Mp 0 1 = entry M 0 1" using eMp01 by simp
    have e1Mp1: "entry Mp 1 1 = entry M 1 1" using eMp11 by simp
    have e11_0: "entry M 1 1 = 0"
      using e1Mp1_eq e0Mp1 e1Mp1 e01_0 by simp
    \<comment> \<open>\<open>Mp = [(0,0),(0,0)]\<close>, so \<open>Trans Mp = Trans [(0,0),(0,0)]\<close>\<close>
    have Mpcols: "Mp = [(0,0),(0,0)]"
    proof -
      obtain p0 p1 where Mp2: "Mp = [p0, p1]"
        using LMp by (cases Mp rule: remdups_adj.cases) auto
      have "fst p0 = entry Mp 0 0" using Mp2 by (simp add: entry_def)
      moreover have "entry Mp 0 0 = entry M 0 0" using eMp00 by simp
      ultimately have fp0: "fst p0 = 0" using e000 by simp
      have "snd p0 = entry Mp 1 0" using Mp2 by (simp add: entry_def)
      moreover have "entry Mp 1 0 = entry M 1 0" using eMp10 by simp
      ultimately have sp0: "snd p0 = 0" using e10_0 by simp
      have "fst p1 = entry Mp 0 1" using Mp2 by (simp add: entry_def)
      hence fp1: "fst p1 = 0" using e0Mp1 e01_0 by simp
      have "snd p1 = entry Mp 1 1" using Mp2 by (simp add: entry_def)
      hence sp1: "snd p1 = 0" using e1Mp1 e11_0 by simp
      show ?thesis using Mp2 fp0 sp0 fp1 sp1 by (cases p0; cases p1) simp
    qed
    have TMp: "Trans Mp = Dpt (enat v) 0\<^sub>B"
    proof -
      have "Trans Mp = Dpt 0 0\<^sub>B"
        using Mpcols Trans_two_zero by simp
      thus ?thesis using v0 by (simp add: zero_enat_def)
    qed
    \<comment> \<open>descent injectivity: \<open>Trans (take 2 M) = Trans M\<close> \<Longrightarrow> \<open>Lng M = 2\<close>\<close>
    have Teq: "Trans (take 2 M) = Trans M" using TMp T Mp_take by simp
    have twopos: "(0::nat) < 2" by simp
    have twole: "(2::nat) \<le> Lng M" using L1 by simp
    have L2: "(2::nat) = Lng M"
      by (rule Trans_take_eq_imp_full[OF MR twopos twole Teq])
    \<comment> \<open>\<open>M = take 2 M = Mp = [(0,0),(0,0)]\<close>\<close>
    have "M = take 2 M" using L2 by simp
    also have "\<dots> = Mp" using Mp_take by simp
    finally have "M = [(0,0),(0,0)]"
      using \<open>Mp = [(0,0),(0,0)]\<close> by simp
    thus ?thesis using v0 by simp
  next
    case vpos: False
    hence v0: "0 < v" by simp
    \<comment> \<open>leftmost head \<open>= entry M 1 0 = v\<close> (\<open>Trans\<close>-leftend basic property)\<close>
    have head: "bpHeadV (Trans M) = enat (entry M 1 0)"
      using m_7_3_Trans_leftend MR by blast
    have e10v: "entry M 1 0 = v"
    proof -
      have "bpHeadV (Dpt (enat v) 0\<^sub>B) = enat v" by simp
      thus ?thesis using head T by simp
    qed
    \<comment> \<open>the first \<open>P\<close>-component shares \<open>M\<close>'s left ends, so \<open>entry (P M ! 0) 1 0 = v > 0\<close>\<close>
    have neP: "P M \<noteq> []" by (rule P_nonempty)
    have Jle: "(0::nat) \<le> Lng (P M) - 1" using neP by (cases "P M") simp_all
    have P0seg: "P M ! 0 = seg M (IdxSum (P M) ! 0) (IdxSum (P M) ! 1 - 1)"
      using m_6_4_P_IdxSum[OF MT Jle] by simp
    have idx0: "IdxSum (P M) ! 0 = 0" by (simp add: idxsum_nth)
    have P0RT: "P M ! 0 \<in> RT_PS"
      using m_6_6_P_reduced[OF MT] MR neP by (metis length_greater_0_conv nth_mem)
    have P0len_pos: "0 < Lng (P M ! 0)"
      using P0RT by (auto simp: RT_PS_def T_PS_def)
    have lp: "0 < Lng (seg M (IdxSum (P M) ! 0) (IdxSum (P M) ! 1 - 1))"
      using P0len_pos P0seg by simp
    have e10eq: "entry (P M ! 0) 1 0 = entry M 1 0"
    proof -
      have "entry (P M ! 0) 1 0
           = entry (seg M (IdxSum (P M) ! 0) (IdxSum (P M) ! 1 - 1)) 1 0"
        using P0seg by simp
      also have "\<dots> = entry M 1 (IdxSum (P M) ! 0 + 0)" by (rule entry_seg[OF lp])
      finally show ?thesis by (simp add: idx0)
    qed
    \<comment> \<open>\<open>P(M)_0\<close> is not zeroT (its row-1 head is \<open>v > 0\<close>, a zeroT term has it \<open>= 0\<close>)\<close>
    have P0nz: "\<not> zeroT (P M ! 0)"
    proof
      assume z: "zeroT (P M ! 0)"
      hence "entry (P M ! 0) 1 0 = 0" by (simp add: zeroT_def)
      thus False using e10eq e10v v0 by simp
    qed
    \<comment> \<open>\<open>M\<close> mono (\<open>Trans\<close>-monoT, A16), since \<open>Trans M = D\<^bsub>v\<^esub> 0\<close> is principal\<close>
    have Lng_eq1: "Lng (PB (Trans M)) = 1"
      using T by (simp add: PB_def)
    have mono: "monoT M"
      using m_7_3_Trans_monoT[OF MR P0nz] Lng_eq1 by simp
    \<comment> \<open>\<open>Trans [M\<^sub>0] = D\<^bsub>v\<^esub> 0 = Trans M\<close>, descent injectivity \<Longrightarrow> \<open>Lng M = 1\<close>\<close>
    have e00v: "entry M 0 0 = v" using e00_e10 e10v by simp
    have M0col: "take 1 M = [(v,v)]"
    proof -
      obtain p where "take 1 M = [p]"
        using Lpos by (cases M) auto
      moreover have "fst p = entry M 0 0"
        using \<open>take 1 M = [p]\<close> Lpos by (cases M) (auto simp: entry_def)
      moreover have "snd p = entry M 1 0"
        using \<open>take 1 M = [p]\<close> Lpos by (cases M) (auto simp: entry_def)
      ultimately show ?thesis using e00v e10v by (cases p) simp
    qed
    have Ttake: "Trans (take 1 M) = Dpt (enat v) 0\<^sub>B"
      using M0col Trans_singleton v0 by simp
    have Teq: "Trans (take 1 M) = Trans M" using Ttake T by simp
    have onepos: "(0::nat) < 1" by simp
    have onele: "(1::nat) \<le> Lng M" using Lpos by linarith
    have L1: "(1::nat) = Lng M"
      by (rule Trans_take_eq_imp_full[OF MR onepos onele Teq])
    have "M = take 1 M" using L1 by simp
    hence "M = [(v,v)]" using M0col by simp
    thus ?thesis using v0 by simp
  qed
qed

end
