theory Frontier_6_026
  imports P_6_7_standard_prefix
begin

subsection \<open>§6.7 標準形の単項成分が標準形であること (P-components are standard, same rank)\<close>

text \<open>
  Proof of \<open>p_6_7_standard_P_components\<close> (\<open>M \<in> SkT_PS k \<Longrightarrow> P M ! J \<in> SkT_PS k\<close>).
  The article proof (content.md line 1392) is faulty (correction A6): it derives
  "the components of \<open>M'\<close> are in \<open>S\<^sub>k\<close>" from the induction hypothesis, which only
  yields \<open>S\<^bsub>k-1\<^esub>\<close>, and \<open>S\<^bsub>k-1\<^esub> \<subseteq> S\<^sub>k\<close> is false.  The repair uses two facts the
  article omits, both empirically verified in \<open>python/sk_67_audit.py\<close>:
    \<^item> (R) a non-last \<open>P\<close>-component has row 1 identically zero;
    \<^item> (U) a row-1-zero standard form in \<open>S\<^sub>k\<close> is also in \<open>S\<^bsub>k+1\<^esub>\<close>.
  Step 1 below is the self-contained part of (R): components of a row-1-zero
  sequence are themselves row-1-zero (they are sublists, and \<open>concat (P M) = M\<close>).
\<close>

text \<open>Auxiliary predicate: row 1 is identically zero (article: \<open>M\<^bsub>1,j\<^esub> = 0\<close> for all \<open>j\<close>).\<close>
definition Row1Zero :: "pairseq \<Rightarrow> bool" where
  "Row1Zero M \<longleftrightarrow> (\<forall>p \<in> set M. snd p = 0)"

text \<open>
  \<open>SkT_PS\<close> is monotone: \<open>SkT_PS k \<subseteq> SkT_PS (Suc k)\<close>.  This is the fact the
  article's §6.7 proof of standard_P_components silently relies on (correction
  A6): a rank-\<open>k\<close> standard form is also rank-\<open>(k+1)\<close>.  Witness for the base
  case: \<open>diagSeq u v = Pred (diagSeq u (v+1)) = (diagSeq u (v+1))[1]\<close>, and
  \<open>diagSeq u (v+1) \<in> SkT_PS 0\<close>.  (Monotonicity makes the \<open>Row1Zero\<close> route to
  the leading components unnecessary — see docs/standard-P-components.md.)
\<close>

text \<open>Auxiliary: \<open>diagSeq u (Suc v) = diagSeq u v @ [(Suc v, Suc v)]\<close> and hence
  \<open>Pred (diagSeq u (Suc v)) = diagSeq u v\<close>.\<close>
lemma diagSeq_Suc_snoc:
  assumes uv: "u \<le> v"
  shows "diagSeq u (Suc v) = diagSeq u v @ [(Suc v, Suc v)]"
  using uv by (simp add: diagSeq_def upt_Suc_append)

lemma Pred_diagSeq_Suc:
  assumes uv: "u \<le> v"
  shows "Pred (diagSeq u (Suc v)) = diagSeq u v"
proof -
  have Lgt1: "1 < Lng (diagSeq u (Suc v))" using uv by simp
  have "Pred (diagSeq u (Suc v)) = butlast (diagSeq u (Suc v))"
    using Lgt1 by (simp add: Pred_def)
  also have "\<dots> = butlast (diagSeq u v @ [(Suc v, Suc v)])"
    by (simp only: diagSeq_Suc_snoc[OF uv])
  also have "\<dots> = diagSeq u v" by simp
  finally show ?thesis .
qed

text \<open>A diagonal segment is never multi-term (row 0 is strictly increasing, so
  \<open>(0,0) \<le>\<^bsub>M\<^esub> (0, Lng-1)\<close>).  Used for the \<open>k = 0\<close> base of \<open>SkT_P_comp\<close>.\<close>
lemma not_multiT_diagSeq:
  assumes uv: "u \<le> v"
  shows "\<not> multiT (diagSeq u v)"
proof -
  have MT: "diagSeq u v \<in> T_PS" using uv by (simp add: T_PS_def diagSeq_def del: upt_Suc)
  show ?thesis
  proof (cases "1 < Lng (diagSeq u v)")
    case False
    thus ?thesis using MT multiT_imp_Lng_gt1[OF MT] by auto
  next
    case True
    let ?M = "diagSeq u v"
    have j1lt: "Lng ?M - 1 < Lng ?M" using True by simp
    have j0lt: "(0::nat) < Lng ?M - 1" using True by simp
    have "(nextrel0 ?M)\<^sup>*\<^sup>* 0 (Lng ?M - 1)"
    proof (rule le0_build[OF MT j1lt j0lt])
      show "\<forall>j. 0 < j \<and> j \<le> Lng ?M - 1 \<longrightarrow> entry ?M 0 0 < entry ?M 0 j"
      proof (intro allI impI)
        fix j assume jj: "0 < j \<and> j \<le> Lng ?M - 1"
        hence jLM: "j < Lng ?M" using True by linarith
        hence ej: "entry ?M 0 j = u + j" by (simp add: entry_diagSeq)
        have "entry ?M 0 0 = u" using True by (simp add: entry_diagSeq)
        thus "entry ?M 0 0 < entry ?M 0 j" using ej jj by simp
      qed
    qed
    hence "le0 ?M 0 (Lng ?M - 1)" using j1lt by (simp add: le0_def)
    hence "leR ?M 0 0 (Lng ?M - 1)" by (simp add: leR_def)
    thus ?thesis using m_6_2_not_multi_iff_le[OF MT] by simp
  qed
qed

lemma SkT_PS_mono: "SkT_PS k \<subseteq> SkT_PS (Suc k)"
proof (induction k)
  case 0
  show "SkT_PS 0 \<subseteq> SkT_PS (Suc 0)"
  proof
    fix M assume "M \<in> SkT_PS 0"
    then obtain u v where Muv: "M = diagSeq u v" and uv: "u \<le> v" by auto
    have NinS0: "diagSeq u (Suc v) \<in> SkT_PS 0" using uv by force
    have LN: "1 < Lng (diagSeq u (Suc v))" using uv by simp
    have NT: "diagSeq u (Suc v) \<in> T_PS"
      using diagSeq_Suc_snoc[OF uv] by (simp add: T_PS_def)
    have "M = diagSeq u v" by (rule Muv)
    also have "\<dots> = Pred (diagSeq u (Suc v))" by (simp add: Pred_diagSeq_Suc[OF uv])
    also have "\<dots> = (diagSeq u (Suc v))[1]" by (rule m_5_3_pred_is_oper1[OF NT LN])
    finally have Meq: "M = (diagSeq u (Suc v))[1]" .
    have "(diagSeq u (Suc v))[1] \<in> SkT_PS (Suc 0)" using NinS0 by auto
    thus "M \<in> SkT_PS (Suc 0)" using Meq by simp
  qed
next
  case (Suc k)
  show "SkT_PS (Suc k) \<subseteq> SkT_PS (Suc (Suc k))"
  proof
    fix M assume "M \<in> SkT_PS (Suc k)"
    then obtain N n where MNn: "M = (N::pairseq)[n]"
                      and NK: "N \<in> SkT_PS k" and n1: "1 \<le> n" by auto
    have "N \<in> SkT_PS (Suc k)" using Suc.IH NK by blast
    thus "M \<in> SkT_PS (Suc (Suc k))" using n1 MNn by auto
  qed
qed

text \<open>
  m: 命題（標準形の単項成分が標準形であること） (§6.7).  Discharges
  \<open>p_6_7_standard_P_components\<close>.  The article proof (content.md 1392, correction
  A6) is essentially right but omits the monotonicity lemma \<open>SkT_PS_mono\<close> on
  which it relies; here we use it explicitly.  Structure (docs/standard-P-components.md):
  outer induction on \<open>k\<close>, inner strong induction on \<open>Lng X\<close>; leading \<open>P\<close>-components
  come from the rank-\<open>k\<close> IH and are lifted by \<open>SkT_PS_mono\<close>; the relation-(2) tail
  \<open>(last (P M'))[n]\<close> is strictly shorter, handled by the inner IH.
\<close>

lemma SkT_P_comp:
  shows "X \<in> SkT_PS k \<Longrightarrow> c \<in> set (P X) \<Longrightarrow> c \<in> SkT_PS k"
proof -
  have "\<forall>X. X \<in> SkT_PS k \<longrightarrow> (\<forall>c \<in> set (P X). c \<in> SkT_PS k)"
  proof (induction k)
    case 0
    show ?case
    proof (intro allI impI ballI)
      fix X c assume X0: "X \<in> SkT_PS 0" and cP: "c \<in> set (P X)"
      from X0 obtain u v where Xuv: "X = diagSeq u v" and uv: "u \<le> v" by auto
      have "\<not> multiT X" using Xuv not_multiT_diagSeq[OF uv] by simp
      hence "P X = [X]" by (simp add: poper_P_nonmulti)
      with cP have "c = X" by simp
      thus "c \<in> SkT_PS 0" using X0 by simp
    qed
  next
    case (Suc k)
    note IHk = Suc.IH
    have inner: "\<forall>X. Lng X = L \<longrightarrow> X \<in> SkT_PS (Suc k) \<longrightarrow> (\<forall>c \<in> set (P X). c \<in> SkT_PS (Suc k))"
      for L
    proof (induction L rule: less_induct)
      case (less L)
      note IHL = less.IH
      show ?case
      proof (intro allI impI ballI)
        fix X c assume LX: "Lng X = L" and XS: "X \<in> SkT_PS (Suc k)" and cP: "c \<in> set (P X)"
        from XS obtain M' n where Xeq: "X = (M'::pairseq)[n]"
                              and M'S: "M' \<in> SkT_PS k" and n1: "1 \<le> n" by auto
        have M'T: "M' \<in> T_PS" using M'S SkT_PS_subset_ST_PS ST_PS_T_PS by blast
        show "c \<in> SkT_PS (Suc k)"
        proof (cases "multiT M'")
          case nonmulti: False
          show ?thesis
          proof (cases "nextR M' 0 0 (Lng M' - 1) \<and> entry M' 1 (Lng M' - 1) = 0")
            case cond1: True
            have PX: "P X = replicate n (Pred M')"
              using m_6_2_nonmulti_oper_1[OF M'T n1 nonmulti conjunct1[OF cond1] conjunct2[OF cond1]]
                    Xeq by simp
            from cP PX n1 have cpred: "c = Pred M'"
              by (auto simp: set_replicate_conv_if split: if_splits)
            have "Pred M' \<in> SkT_PS (Suc k)"
            proof (cases "1 < Lng M'")
              case True
              have "Pred M' = M'[1]" by (rule m_5_3_pred_is_oper1[OF M'T True])
              thus ?thesis using M'S by auto
            next
              case False
              hence "Pred M' = M'" by (simp add: Pred_def)
              thus ?thesis using rev_subsetD[OF M'S SkT_PS_mono] by simp
            qed
            thus ?thesis using cpred by simp
          next
            case cond2: False
            hence H: "\<not> nextR M' 0 0 (Lng M' - 1) \<or> entry M' 1 (Lng M' - 1) > 0" by auto
            have "P X = [X]"
              using m_6_2_nonmulti_oper_2[OF M'T n1 nonmulti H] Xeq by simp
            with cP have "c = X" by simp
            thus ?thesis using XS by simp
          qed
        next
          case multi: True
          have lenP: "length (P M') > 1" using multi m_6_2_P_components_2[OF M'T] by simp
          have LM': "1 < Lng M'" using multi multiT_imp_Lng_gt1[OF M'T] by simp
          show ?thesis
          proof (cases "Lng (last (P M')) = 1")
            case last1: True
            have PX: "P X = butlast (P M')"
            proof -
              have "P (M'[n]) = butlast (P M')"
                using conjunct2[OF m_6_2_P_oper_1[OF M'T n1 last1]] lenP by simp
              thus ?thesis using Xeq by simp
            qed
            from cP PX have "c \<in> set (butlast (P M'))" by simp
            hence "c \<in> set (P M')" using in_set_butlastD by fast
            hence "c \<in> SkT_PS k" using IHk M'S by blast
            thus ?thesis by (rule rev_subsetD[OF _ SkT_PS_mono])
          next
            case False
            have lastpos: "0 < Lng (last (P M'))"
              using idxsum_P_component_nonempty[OF M'T, of "length (P M') - 1"]
                    P_nonempty by (simp add: last_conv_nth)
            from False lastpos have lastgt: "Lng (last (P M')) > 1" by linarith
            have PX: "P X = butlast (P M') @ P ((last (P M'))[n])"
              using conjunct2[OF m_6_2_P_oper_2[OF M'T n1 lastgt]] Xeq by simp
            have Xsplit: "X = concat (butlast (P M')) @ (last (P M'))[n]"
              using conjunct1[OF m_6_2_P_oper_2[OF M'T n1 lastgt]] Xeq by simp
            from cP PX have "c \<in> set (butlast (P M')) \<or> c \<in> set (P ((last (P M'))[n]))"
              by auto
            thus ?thesis
            proof
              assume "c \<in> set (butlast (P M'))"
              hence "c \<in> set (P M')" using in_set_butlastD by fast
              hence "c \<in> SkT_PS k" using IHk M'S by blast
              thus ?thesis by (rule rev_subsetD[OF _ SkT_PS_mono])
            next
              assume cT: "c \<in> set (P ((last (P M'))[n]))"
              have lastM: "last (P M') \<in> set (P M')" using P_nonempty by simp
              hence lastSk: "last (P M') \<in> SkT_PS k" using IHk M'S by blast
              hence YS: "(last (P M'))[n] \<in> SkT_PS (Suc k)" using n1 by auto
              have cbut: "concat (butlast (P M')) = take (Pcut M') M'"
                using poper_last_P_multi[OF multi LM'] idxsum_concat_P by simp
              have Pcutpos: "0 < Pcut M'" using Pcut_le[OF LM'] by simp
              have Pcutle: "Pcut M' \<le> Lng M' - 1" using Pcut_le[OF LM'] by simp
              have "Lng (concat (butlast (P M'))) = Pcut M'"
                using cbut Pcutle LM' by simp
              hence "Lng ((last (P M'))[n]) < Lng X"
                using Xsplit Pcutpos by simp
              hence "Lng ((last (P M'))[n]) < L" using LX by simp
              with IHL YS cT show ?thesis by blast
            qed
          qed
        qed
      qed
    qed
    show ?case using inner by blast
  qed
  thus "X \<in> SkT_PS k \<Longrightarrow> c \<in> set (P X) \<Longrightarrow> c \<in> SkT_PS k" by blast
qed

end
