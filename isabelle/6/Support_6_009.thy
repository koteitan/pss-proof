theory Support_6_009
  imports P_6_7_standard_P_components
begin

subsection \<open>§6.8 降順性 (standard \<open>P\<close>-components are descending)\<close>

text \<open>
  Auxiliary facts for the §6.8 proposition «標準形の単項成分が降順であること».
  The oper \<open>M[n]\<close> preserves the left column \<open>entry _ i 0\<close>, and for a non-multi
  \<open>c\<close> every \<open>P\<close>-component of \<open>c[n]\<close> keeps \<open>c\<close>'s \<open>(0,0)\<close> and \<open>(1,0)\<close> entries.
\<close>

lemma oper_entry_0:
  assumes M: "M \<in> T_PS" and n: "1 \<le> n"
  shows "entry (M[n]) i 0 = entry M i 0"
proof (cases "1 < Lng M")
  case True
  have "(M[n]) ! 0 = M ! 0" using poper_oper_nth0[OF M True n] by simp
  thus ?thesis by (simp add: entry_def)
next
  case False
  hence "Lng M - 1 = 0" by simp
  hence "M[n] = M" by (simp add: oper_def Let_def)
  thus ?thesis by simp
qed

lemma nonmulti_oper_components_leftcol:
  assumes c: "c \<in> T_PS" and n: "1 \<le> n" and nm: "\<not> multiT c"
    and d: "d \<in> set (P ((c::pairseq)[n]))"
  shows "entry d 0 0 = entry c 0 0 \<and> entry d 1 0 = entry c 1 0"
proof (cases "nextR c 0 0 (Lng c - 1) \<and> entry c 1 (Lng c - 1) = 0")
  case cond1: True
  have PX: "P ((c::pairseq)[n]) = replicate n (Pred c)"
    using m_6_2_nonmulti_oper_1[OF c n nm conjunct1[OF cond1] conjunct2[OF cond1]] .
  from d PX n have deq: "d = Pred c"
    by (auto simp: set_replicate_conv_if split: if_splits)
  \<comment> \<open>\<open>cond1\<close>'s \<open>nextR c 0 0 (Lng c - 1)\<close> forces \<open>1 < Lng c\<close>\<close>
  have L: "1 < Lng c"
  proof -
    have "nextrel0 c 0 (Lng c - 1)" using conjunct1[OF cond1] by (simp add: nextR_def)
    hence "0 < Lng c - 1" by (simp add: nextrel0_def)
    thus ?thesis by linarith
  qed
  have pc: "Pred c = butlast c" using L by (simp add: Pred_def)
  have "butlast c ! 0 = c ! 0" using L by (simp add: nth_butlast)
  thus ?thesis using deq pc by (simp add: entry_def)
next
  case cond2: False
  hence H: "\<not> nextR c 0 0 (Lng c - 1) \<or> entry c 1 (Lng c - 1) > 0" by auto
  have PX: "P (c[n]) = [c[n]]" using m_6_2_nonmulti_oper_2[OF c n nm H] .
  from d PX have deq: "d = c[n]" by simp
  thus ?thesis using oper_entry_0[OF c n] by simp
qed

text \<open>
  Main §6.8 proposition (row-1 tie-break of \<open>P M\<close>).  We avoid the article's
  minimal-rank \<open>k\<^sub>0\<close> induction: thanks to @{thm [source] SkT_PS_mono} a plain
  induction on the level \<open>k\<close> with \<open>M \<in> SkT_PS k\<close> suffices, with the recursive
  step handled by @{thm [source] m_6_2_P_oper_1} / @{thm [source] m_6_2_P_oper_2}
  and the inductive hypothesis applied to the parent \<open>M'\<close>.
\<close>

lemma SkT_P_descending:
  shows "X \<in> SkT_PS k \<Longrightarrow> J0' \<le> J1' \<Longrightarrow> J1' \<le> Lng (P X) - 1
         \<Longrightarrow> entry (P X ! J0') 0 0 = entry (P X ! J1') 0 0
         \<Longrightarrow> entry (P X ! J0') 1 0 \<ge> entry (P X ! J1') 1 0"
proof -
  have "\<forall>X. X \<in> SkT_PS k \<longrightarrow>
          (\<forall>J0' J1'. J0' \<le> J1' \<and> J1' \<le> Lng (P X) - 1
             \<and> entry (P X ! J0') 0 0 = entry (P X ! J1') 0 0
             \<longrightarrow> entry (P X ! J0') 1 0 \<ge> entry (P X ! J1') 1 0)"
  proof (induction k)
    case 0
    show ?case
    proof (intro allI impI)
      fix X J0' J1'
      assume X0: "X \<in> SkT_PS 0"
        and A: "J0' \<le> J1' \<and> J1' \<le> Lng (P X) - 1
                \<and> entry (P X ! J0') 0 0 = entry (P X ! J1') 0 0"
      from X0 obtain u v where Xuv: "X = diagSeq u v" and uv: "u \<le> v" by auto
      have "\<not> multiT X" using Xuv not_multiT_diagSeq[OF uv] by simp
      hence PX: "P X = [X]" by (simp add: poper_P_nonmulti)
      have "Lng (P X) = 1" using PX by simp
      hence "J1' = 0" "J0' = 0" using A by auto
      thus "entry (P X ! J0') 1 0 \<ge> entry (P X ! J1') 1 0" by simp
    qed
  next
    case (Suc k)
    note IHk = Suc.IH
    show ?case
    proof (intro allI impI)
      fix X J0' J1'
      assume XS: "X \<in> SkT_PS (Suc k)"
        and A: "J0' \<le> J1' \<and> J1' \<le> Lng (P X) - 1
                \<and> entry (P X ! J0') 0 0 = entry (P X ! J1') 0 0"
      from XS obtain M' n where Xeq: "X = (M'::pairseq)[n]"
        and M'S: "M' \<in> SkT_PS k" and n1: "1 \<le> n" by auto
      have M'T: "M' \<in> T_PS" using M'S SkT_PS_subset_ST_PS ST_PS_T_PS by blast
      from A have le01: "J0' \<le> J1'" and J1le: "J1' \<le> Lng (P X) - 1"
        and r0eq: "entry (P X ! J0') 0 0 = entry (P X ! J1') 0 0" by auto
      show "entry (P X ! J0') 1 0 \<ge> entry (P X ! J1') 1 0"
        proof (cases "multiT M'")
          case nonmulti: False
          \<comment> \<open>all \<open>P X\<close>-components agree, so the goal is reflexive\<close>
          have "P X ! J0' = P X ! J1'"
          proof (cases "nextR M' 0 0 (Lng M' - 1) \<and> entry M' 1 (Lng M' - 1) = 0")
            case cond1: True
            have PX: "P X = replicate n (Pred M')"
              using m_6_2_nonmulti_oper_1[OF M'T n1 nonmulti conjunct1[OF cond1] conjunct2[OF cond1]] Xeq by simp
            have lpx: "Lng (P X) = n" using PX by simp
            have J1n: "J1' < n" using J1le lpx n1 by linarith
            have J0n: "J0' < n" using le01 J1n by linarith
            show ?thesis using PX J0n J1n by simp
          next
            case cond2: False
            hence H: "\<not> nextR M' 0 0 (Lng M' - 1) \<or> entry M' 1 (Lng M' - 1) > 0" by auto
            have PX: "P X = [X]" using m_6_2_nonmulti_oper_2[OF M'T n1 nonmulti H] Xeq by simp
            hence "J1' \<le> 0" using J1le by simp
            hence "J0' = 0 \<and> J1' = 0" using le01 by auto
            thus ?thesis by simp
          qed
          thus ?thesis by simp
        next
          case multi: True
          have lenP: "1 < length (P M')" using multi m_6_2_P_components_2[OF M'T] by simp
          let ?c = "last (P M')"
          have ne: "P M' \<noteq> []" by (rule P_nonempty)
          have cidx: "?c = P M' ! (Lng (P M') - 1)" using ne by (simp add: last_conv_nth)
          have cmem: "?c \<in> SkT_PS k"
          proof -
            have "Lng (P M') - 1 < Lng (P M')" using ne by (cases "P M'") auto
            hence "P M' ! (Lng (P M') - 1) \<in> SkT_PS k"
              using m_6_7_standard_P_components[OF M'S] by blast
            thus ?thesis using cidx by simp
          qed
          have cT: "?c \<in> T_PS" using cmem SkT_PS_subset_ST_PS ST_PS_T_PS by blast
          have cnm: "\<not> multiT ?c"
            using m_6_2_P_components_1[OF M'T] last_in_set[OF ne] by (auto simp: multiT_def)
          show ?thesis
          proof (cases "Lng (last (P M')) = 1")
            case last1: True
            \<comment> \<open>\<open>P X = butlast (P M')\<close>: every component agrees with \<open>P M'\<close>, IH on \<open>M'\<close>\<close>
            have PX: "P X = butlast (P M')"
              using conjunct2[OF m_6_2_P_oper_1[OF M'T n1 last1]] lenP Xeq by simp
            have J1lt: "J1' < length (butlast (P M'))"
              using J1le PX lenP by simp
            have J0lt: "J0' < length (butlast (P M'))" using le01 J1lt by linarith
            have e0: "P X ! J0' = P M' ! J0'" using PX J0lt by (simp add: nth_butlast)
            have e1: "P X ! J1' = P M' ! J1'" using PX J1lt by (simp add: nth_butlast)
            have J1leM': "J1' \<le> Lng (P M') - 1" using J1lt by simp
            have h0: "entry (P M' ! J0') 0 0 = entry (P M' ! J1') 0 0"
              using r0eq e0 e1 by simp
            have "entry (P M' ! J0') 1 0 \<ge> entry (P M' ! J1') 1 0"
              using IHk M'S le01 J1leM' h0 by blast
            thus ?thesis using e0 e1 by simp
          next
            case False
            have lastpos: "0 < Lng (last (P M'))"
              using idxsum_P_component_nonempty[OF M'T, of "length (P M') - 1"] P_nonempty
              by (simp add: last_conv_nth)
            from False lastpos have lastgt: "1 < Lng (last (P M'))" by linarith
            \<comment> \<open>\<open>P X = butlast (P M') @ P (c[n])\<close>\<close>
            have PX: "P X = butlast (P M') @ P (?c[n])"
              using conjunct2[OF m_6_2_P_oper_2[OF M'T n1 lastgt]] Xeq by simp
            define J0 where "J0 = length (butlast (P M'))"
            have J0eq: "J0 = Lng (P M') - 1" by (simp add: J0_def)
            have lenPX: "length (P X) = J0 + length (P (?c[n]))"
              using PX by (simp add: J0_def)
            have ccidx: "?c = P M' ! J0" using cidx J0eq by simp
            have pre: "P X ! J = P M' ! J" if "J < J0" for J
              using PX that by (simp add: nth_append nth_butlast J0_def)
            have tail: "P X ! J = P (?c[n]) ! (J - J0)" if "J0 \<le> J" for J
              using PX that by (simp add: nth_append J0_def)
            have neX: "P X \<noteq> []" by (rule P_nonempty)
            have J1ltX: "J1' < length (P X)" using J1le neX by (cases "P X") auto
            show ?thesis
            proof (cases "J1' < J0")
              case AA: True
              \<comment> \<open>both in the prefix: IH on \<open>M'\<close>\<close>
              have e0: "P X ! J0' = P M' ! J0'" using pre le01 AA by simp
              have e1: "P X ! J1' = P M' ! J1'" using pre AA by simp
              have J1leM': "J1' \<le> Lng (P M') - 1" using AA J0eq by linarith
              have h0: "entry (P M' ! J0') 0 0 = entry (P M' ! J1') 0 0"
                using r0eq e0 e1 by simp
              have "entry (P M' ! J0') 1 0 \<ge> entry (P M' ! J1') 1 0"
                using IHk M'S le01 J1leM' h0 by blast
              thus ?thesis using e0 e1 by simp
            next
              case AB: False
              hence J0leJ1: "J0 \<le> J1'" by simp
              have dmem: "P X ! J1' \<in> set (P (?c[n]))"
              proof -
                have "J1' - J0 < length (P (?c[n]))" using lenPX J0leJ1 J1ltX by linarith
                hence "P (?c[n]) ! (J1' - J0) \<in> set (P (?c[n]))" by (rule nth_mem)
                thus ?thesis using tail[OF J0leJ1] by simp
              qed
              have dlc0: "entry (P X ! J1') 0 0 = entry ?c 0 0"
                and dlc1: "entry (P X ! J1') 1 0 = entry ?c 1 0"
                using nonmulti_oper_components_leftcol[OF cT n1 cnm dmem] by auto
              show ?thesis
              proof (cases "J0' < J0")
                case BB: True
                \<comment> \<open>\<open>J0' < J0 \<le> J1'\<close>: prefix vs tail, IH on \<open>M'\<close> at \<open>(J0', J0)\<close>\<close>
                have e0: "P X ! J0' = P M' ! J0'" using pre BB by simp
                have r0M': "entry (P M' ! J0') 0 0 = entry (P M' ! J0) 0 0"
                  using r0eq e0 dlc0 ccidx by simp
                have J0leJ0: "J0' \<le> J0" using BB by linarith
                have J0leM': "J0 \<le> Lng (P M') - 1" using J0eq by simp
                have "entry (P M' ! J0') 1 0 \<ge> entry (P M' ! J0) 1 0"
                  using IHk M'S J0leJ0 J0leM' r0M' by blast
                hence "entry (P X ! J0') 1 0 \<ge> entry ?c 1 0" using e0 ccidx by simp
                thus ?thesis using dlc1 by simp
              next
                case BC: False
                \<comment> \<open>both in the tail: helper gives equal row-1\<close>
                hence J0leJ0': "J0 \<le> J0'" by simp
                have d0mem: "P X ! J0' \<in> set (P (?c[n]))"
                proof -
                  have "J0' < length (P X)" using le01 J1ltX by linarith
                  hence "J0' - J0 < length (P (?c[n]))" using lenPX J0leJ0' by linarith
                  hence "P (?c[n]) ! (J0' - J0) \<in> set (P (?c[n]))" by (rule nth_mem)
                  thus ?thesis using tail[OF J0leJ0'] by simp
                qed
                have "entry (P X ! J0') 1 0 = entry ?c 1 0"
                  using nonmulti_oper_components_leftcol[OF cT n1 cnm d0mem] by simp
                thus ?thesis using dlc1 by simp
              qed
            qed
          qed
        qed
      qed
    qed
  thus "X \<in> SkT_PS k \<Longrightarrow> J0' \<le> J1' \<Longrightarrow> J1' \<le> Lng (P X) - 1
         \<Longrightarrow> entry (P X ! J0') 0 0 = entry (P X ! J1') 0 0
         \<Longrightarrow> entry (P X ! J0') 1 0 \<ge> entry (P X ! J1') 1 0" by blast
qed

end
