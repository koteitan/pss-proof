theory Support_6_028
  imports Frontier_6_046
begin

text \<open>T4 structural core (NO outer \<open>Red\<close>): the core-reduce \<^emph>\<open>argument\<close>
  \<open>diagSeq 0 (m\<^sub>1\<^sub>0-1) @ IncrFirst\<^bsup>m\<^sub>1\<^sub>0\<^esup>(\<cdot>)\<close> commutes with \<open>Pred\<close> when \<open>Lng M > 1\<close>
  (so the tail piece is non-empty and \<open>butlast\<close> stays inside it).  This is the
  cheap, \<open>Red\<close>-free half of T4(i); the remaining half is the OUTER \<open>Red\<close>
  commutation \<open>Red(Pred X)=Pred(Red X)\<close> on this argument \<open>X\<close>, which is the
  parent goal \<open>p_6_5_Red_Pred\<close> itself (blocker — see report).\<close>

lemma m_6_5_T4_coreArg_Pred:
  assumes L: "1 < Lng M" and pos: "0 < entry M 1 0"
  shows "diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ (entry M 1 0)) (Pred M)
       = Pred (diagSeq 0 (entry M 1 0 - 1) @ (IncrFirst ^^ (entry M 1 0)) M)"
proof -
  let ?m10 = "entry M 1 0"
  have m10P: "entry (Pred M) 1 0 = ?m10" by (rule entry_Pred_0[OF L])
  have ne: "M \<noteq> []" using L by (cases M) auto
  have predbl: "Pred M = butlast M" using L by (simp add: Pred_def)
  \<comment> \<open>the tail \<open>IncrFirst\<^bsup>m10\<^esup> M\<close> is non-empty, so \<open>butlast\<close> of the concatenation
     lands entirely inside it.\<close>
  have tne: "(IncrFirst ^^ ?m10) M \<noteq> []"
    using ne by (metis Lng_funpow_IncrFirst length_0_conv)
  have Lgt: "1 < Lng (diagSeq 0 (?m10 - 1) @ (IncrFirst ^^ ?m10) M)"
  proof -
    have "Lng (diagSeq 0 (?m10 - 1)) = ?m10" using pos by (simp del: upt_Suc)
    moreover have "0 < Lng ((IncrFirst ^^ ?m10) M)"
      using tne by (cases "(IncrFirst ^^ ?m10) M") auto
    ultimately show ?thesis using pos L by simp
  qed
  have notle: "\<not> Lng (diagSeq 0 (?m10 - 1) @ (IncrFirst ^^ ?m10) M) \<le> 1"
    using Lgt by linarith
  have "Pred (diagSeq 0 (?m10 - 1) @ (IncrFirst ^^ ?m10) M)
      = butlast (diagSeq 0 (?m10 - 1) @ (IncrFirst ^^ ?m10) M)"
    by (simp only: Pred_def if_not_P[OF notle])
  also have "\<dots> = diagSeq 0 (?m10 - 1) @ butlast ((IncrFirst ^^ ?m10) M)"
    using tne by (simp add: butlast_append)
  also have "butlast ((IncrFirst ^^ ?m10) M) = (IncrFirst ^^ ?m10) (butlast M)"
    by (simp add: funpow_IncrFirst_butlast)
  also have "\<dots> = (IncrFirst ^^ ?m10) (Pred M)" using predbl by simp
  finally show ?thesis using m10P by simp
qed



(* ===== Br-under-Pred decomposition (T3(ii) corrected) ===== *)
text \<open>General \<open>P\<close>-under-\<open>Pred\<close> decomposition for ANY \<open>Q \<in> T_PS\<close> with \<open>1 < Lng Q\<close>
  (both the mono and the multi class).  This unifies @{thm [source] pred_P_decomp}
  (which assumed \<open>multiT Q\<close>) with the mono case (\<open>P Q = [Q]\<close>, where \<open>Pred Q =
  butlast Q\<close> is again mono so \<open>P (Pred Q) = [butlast Q]\<close>): in both cases
  \<open>P (Pred Q)\<close> drops a singleton last block (when \<open>Lng (last (P Q)) \<le> 1\<close>) or
  \<open>butlast\<close>s it.  Empirically verified 500000/0.\<close>

lemma m_6_6_P_Pred_decomp:
  assumes Q: "Q \<in> T_PS" and L: "1 < Lng Q"
  shows "P (Pred Q) =
           butlast (P Q)
           @ (if Lng (last (P Q)) \<le> 1 then [] else [butlast (last (P Q))])"
proof (cases "multiT Q")
  case True
  \<comment> \<open>The multi class is exactly @{thm [source] pred_P_decomp}, with
     \<open>Pred (last (P Q)) = butlast (last (P Q))\<close> when the last block has length \<open>> 1\<close>.\<close>
  have dec: "P (Pred Q) =
               (if Lng (last (P Q)) = 1
                then butlast (P Q)
                else butlast (P Q) @ [Pred (last (P Q))])"
    by (rule pred_P_decomp[OF Q True])
  show ?thesis
  proof (cases "Lng (last (P Q)) = 1")
    case True
    thus ?thesis using dec by simp
  next
    case False
    \<comment> \<open>last block has length \<open>> 1\<close>, so its \<open>Pred\<close> is its \<open>butlast\<close>.\<close>
    have PQne: "P Q \<noteq> []" by (rule P_nonempty)
    have lastidx: "last (P Q) = P Q ! (length (P Q) - 1)" using PQne by (simp add: last_conv_nth)
    have idxlt: "length (P Q) - 1 < length (P Q)" using PQne by (cases "P Q") auto
    have "Lng (last (P Q)) > 0"
      using idxsum_P_component_nonempty[OF Q idxlt] lastidx by simp
    with False have Lgt1: "1 < Lng (last (P Q))" by linarith
    have predlast: "Pred (last (P Q)) = butlast (last (P Q))"
      using Lgt1 by (simp add: Pred_def)
    have notle: "\<not> Lng (last (P Q)) \<le> 1" using Lgt1 by linarith
    show ?thesis using dec False predlast notle by simp
  qed
next
  case False
  \<comment> \<open>Mono class: \<open>P Q = [Q]\<close>, and \<open>Pred Q = butlast Q\<close> is again mono.\<close>
  have nz: "\<not> zeroT Q" using L by (simp add: zeroT_def)
  have mono: "monoT Q" using False nz by (simp add: multiT_def)
  have QPT: "Q \<in> PT_PS" using Q mono by (simp add: PT_PS_def)
  have PQ: "P Q = [Q]" using False by (subst P.simps) simp
  have predbl: "Pred Q = butlast Q" using L by (simp add: Pred_def)
  \<comment> \<open>\<open>butlast Q\<close> is mono (prefix of a mono term), hence non-multi, hence \<open>P\<close> is a singleton.\<close>
  have notmulti_bl: "\<not> multiT (butlast Q)"
  proof (cases "1 < Lng Q - 1")
    case True
    have j0pos: "0 < Lng Q - 2" using True by simp
    have j0lt: "Lng Q - 2 < Lng Q" using L by simp
    have "monoT (seg Q 0 (Lng Q - 2))"
      by (rule m_6_2_mono_prefix[OF QPT j0pos j0lt])
    moreover have "seg Q 0 (Lng Q - 2) = butlast Q"
    proof -
      have suc: "Suc (Lng Q - 2) \<le> Lng Q" using True by simp
      have "seg Q 0 (Lng Q - 2) = take (Suc (Lng Q - 2)) Q" by (rule seg_0_eq_take[OF suc])
      also have "Suc (Lng Q - 2) = Lng Q - 1" using True by simp
      also have "take (Lng Q - 1) Q = butlast Q" by (simp add: butlast_conv_take)
      finally show ?thesis .
    qed
    ultimately have "monoT (butlast Q)" by simp
    thus ?thesis by (simp add: multiT_def)
  next
    case False
    \<comment> \<open>\<open>Lng Q = 2\<close>, so \<open>butlast Q\<close> is a singleton: non-multi.\<close>
    have "Lng Q = 2" using L False by simp
    hence Lbn: "Lng (butlast Q) = 1" by simp
    show ?thesis
    proof (cases "zeroT (butlast Q)")
      case True thus ?thesis by (simp add: multiT_def)
    next
      case False
      have "monoT (butlast Q)" using Lbn False by (simp add: monoT_def leR_def le0_def)
      thus ?thesis by (simp add: multiT_def)
    qed
  qed
  have Pbl: "P (butlast Q) = [butlast Q]" using notmulti_bl by (subst P.simps) simp
  \<comment> \<open>Last block is \<open>Q\<close> with \<open>Lng Q > 1\<close>, so the RHS keeps the \<open>butlast\<close> branch.\<close>
  have "P (Pred Q) = [butlast Q]" using predbl Pbl by simp
  thus ?thesis using PQ L by simp
qed

text \<open>T3(ii) corrected: the branch decomposition \<open>Br\<close> under \<open>Pred\<close>.  For
  \<open>M \<in> T\<^bsub>PS\<^esub>\<close> with \<open>m\<^sub>0\<^sub>0 = m\<^sub>1\<^sub>0 = 0\<close>, \<open>TrMax M \<noteq> Lng M - 1\<close>, \<open>1 < Lng M\<close>:
  \<open>Pred = butlast\<close> drops the last pair, which lies in the BRANCH region
  \<open>S = seg M (TrMax M + 1) (Lng M - 1) = drop (TrMax M + 1) M\<close>.  By
  @{thm [source] TrMax_Pred} the trunk is unchanged, so the branch region of
  \<open>Pred M\<close> is \<open>butlast S\<close> and \<open>Br (Pred M) = P (Pred S)\<close> (when \<open>Lng S > 1\<close>), or
  \<open>[]\<close> (when \<open>Lng S = 1\<close>, the singleton last branch block is dropped wholesale).
  @{thm [source] m_6_6_P_Pred_decomp} (with \<open>Br M = P S\<close>) then gives the result.
  Empirically verified 142600/0 (the literal "last branch predecessored" was a
  counterexample, 87267/177609 fail).\<close>

lemma m_6_6_Br_Pred:
  assumes M: "M \<in> T_PS" and m00: "entry M 0 0 = 0" and m10: "entry M 1 0 = 0"
    and br: "TrMax M \<noteq> Lng M - 1" and L: "1 < Lng M"
  shows "Br (Pred M) =
           butlast (Br M)
           @ (if Lng (last (Br M)) \<le> 1 then [] else [butlast (last (Br M))])"
proof -
  let ?t = "TrMax M"
  let ?j0 = "TrMax M + 1"
  let ?S = "seg M ?j0 (Lng M - 1)"
  \<comment> \<open>The branch region is the drop past the trunk; it is nonempty.\<close>
  have tb: "?t \<le> Lng M - 1" by (rule TrMax_bound[OF M])
  with br have tlt: "?t < Lng M - 1" by linarith
  have j0lt: "?j0 < Lng M" using tlt by linarith
  have LMpos: "0 < Lng M" using L by linarith
  have Sdrop: "?S = drop ?j0 M" using LMpos by (rule seg_to_last_eq_drop)
  have Sne: "?S \<noteq> []" using j0lt unfolding Sdrop by simp
  have ST: "?S \<in> T_PS" using Sne by (simp add: T_PS_def)
  have LS: "Lng ?S = Lng M - ?j0" by (simp add: Sdrop)
  \<comment> \<open>\<open>Br M = P S\<close> (the trunk is nontrivial).\<close>
  have brM: "Br M = P ?S" using br by (simp add: Br_def)
  \<comment> \<open>\<open>Pred M = butlast M\<close>; the trunk is preserved.\<close>
  have predbl: "Pred M = butlast M" using L by (simp add: Pred_def)
  have predT: "Pred M \<in> T_PS" by (rule Pred_preserves_T_PS[OF M])
  have LP: "Lng (Pred M) = Lng M - 1" using L by (simp add: predbl)
  have trP: "TrMax (Pred M) = ?t" by (rule TrMax_Pred[OF M L br])
  \<comment> \<open>The branch region of \<open>Pred M\<close> is \<open>drop ?j0 (butlast M) = butlast S\<close>.\<close>
  have SpredEq: "seg (Pred M) ?j0 (Lng (Pred M) - 1) = butlast ?S"
  proof -
    have Ppos: "0 < Lng (Pred M)" using LP tlt by linarith
    have "seg (Pred M) ?j0 (Lng (Pred M) - 1) = drop ?j0 (Pred M)"
      using Ppos by (rule seg_to_last_eq_drop)
    also have "\<dots> = drop ?j0 (butlast M)" by (simp add: predbl)
    also have "\<dots> = butlast (drop ?j0 M)" by (simp add: butlast_drop)
    also have "drop ?j0 M = ?S" by (rule Sdrop[symmetric])
    finally show ?thesis .
  qed
  show ?thesis
  proof (cases "Lng ?S = 1")
    case True
    \<comment> \<open>Singleton branch region: \<open>TrMax (Pred M) = Lng (Pred M) - 1\<close>, so \<open>Br (Pred M) = []\<close>,
       and \<open>Br M = [S]\<close> with \<open>Lng (last (Br M)) = 1\<close>.\<close>
    have treq: "?t = Lng M - 2" using True LS j0lt by simp
    have tPeq: "TrMax (Pred M) = Lng (Pred M) - 1" using trP treq LP tlt by simp
    have brPM: "Br (Pred M) = []" using tPeq by (simp add: Br_def)
    have PS1: "P ?S = [?S]"
    proof -
      have "\<not> multiT ?S"
      proof (cases "zeroT ?S")
        case True thus ?thesis by (simp add: multiT_def)
      next
        case False
        have "monoT ?S" using True \<open>Lng ?S = 1\<close> False
          by (simp add: monoT_def leR_def le0_def)
        thus ?thesis by (simp add: multiT_def)
      qed
      thus ?thesis by (subst P.simps) simp
    qed
    have brMeq: "Br M = [?S]" using brM PS1 by simp
    have lastle: "Lng (last (Br M)) \<le> 1" using brMeq True by simp
    show ?thesis using brPM brMeq lastle by simp
  next
    case False
    \<comment> \<open>\<open>Lng S > 1\<close>: \<open>TrMax (Pred M) \<noteq> Lng (Pred M) - 1\<close>, so \<open>Br (Pred M) = P (butlast S)\<close>.\<close>
    have LSpos: "0 < Lng ?S" using Sne by (cases ?S) auto
    have LSgt1: "1 < Lng ?S" using False LSpos by linarith
    have trne: "?t < Lng M - 2" using LSgt1 LS j0lt by simp
    have tPne: "TrMax (Pred M) \<noteq> Lng (Pred M) - 1" using trP trne LP tlt by simp
    have "Br (Pred M) = P (seg (Pred M) (TrMax (Pred M) + 1) (Lng (Pred M) - 1))"
      using tPne by (simp add: Br_def)
    also have "\<dots> = P (seg (Pred M) ?j0 (Lng (Pred M) - 1))" by (simp add: trP)
    also have "\<dots> = P (butlast ?S)" by (rule arg_cong[OF SpredEq])
    also have "butlast ?S = Pred ?S" using LSgt1 by (simp add: Pred_def)
    finally have brPM: "Br (Pred M) = P (Pred ?S)" .
    \<comment> \<open>Apply the general \<open>P\<close>-under-\<open>Pred\<close> decomposition to \<open>S\<close>.\<close>
    have dec: "P (Pred ?S) =
                 butlast (P ?S)
                 @ (if Lng (last (P ?S)) \<le> 1 then [] else [butlast (last (P ?S))])"
      by (rule m_6_6_P_Pred_decomp[OF ST LSgt1])
    show ?thesis using brPM dec by (simp add: brM)
  qed
qed

end
