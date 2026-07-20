theory Support_7_050
  imports P_7_2_scb_fseq
begin

text \<open>\<^bold>\<open>Part (2) — status.\<close>  \<open>Trans(M)[n-1] = Trans(([1]\<^bsup>j\<^sub>1-1-j\<^sub>-\<^sub>2\<^esup>)(M[n+1]))\<close> is
  \<^bold>\<open>TRUE\<close> under the corrected \<open>operB\<close> (130/130 non-vacuous exercises over genuine
  \<open>ST\<^bsub>PS\<^esub>\<close> condIII/IV hosts, two seeds, 0 counterexamples — python/_r74_84_operbasic.py;
  correction A33's retraction is thereby confirmed empirically).  It is NOT proved
  here.  OBSTRUCTION: by part (1) the right-hand side is \<open>M[n]\<close> extended by ONE
  entry of the appended block, i.e. an intermediate sequence that is \<^bold>\<open>not\<close> of the
  form \<open>M[m]\<close>; every \<open>Trans\<close> closed form in the corpus (\<open>cpx_condIII_mnform\<close>,
  \<open>c4cx2_condIV_mnform_of_slice\<close>, \<open>d13x_fseq_condIII\<close>) is indexed by the
  fundamental sequence \<open>M[m]\<close>, so no existing brick evaluates \<open>Trans\<close> there.
  NEXT IDEA: prove a one-step readback \<open>flatBT (Trans (M[n] @ [M ! (j\<^sub>-\<^sub>2+1)]))
  = s\<^sub>1 @ flatBP (D\<^bsub>e\<^sub>3\<^esub> (d4vx_core s\<^sub>0 ub b\<^sub>0 0\<^sub>B n)) @ b\<^sub>1\<close> — i.e. that appending the
  single block entry lands exactly on the \<open>0\<^sub>B\<close>-seeded tower level that \<open>fOn\<close> at
  index \<open>n-1\<close> already names; then part (2) is \<open>m_7_flatBT_inj\<close>.  This needs a
  \<open>Trans\<close>-recursion step lemma for the (non-fseq) one-entry extension, which the
  \<section>8.4 corpus does not yet have.\<close>

section \<open>r74 (y3s): the \<section>7 \<open>T\<^bsub>PS\<^esub>\<close> scope gap --- \<open>Red\<close>-iteration transport\<close>

text \<open>The article states seven \<section>7.3/\<section>7.4 propositions for all \<open>M \<in> T\<^bsub>PS\<^esub>\<close>; we had
  proved them only on \<open>RT\<^bsub>PS\<^esub>\<close>.  The obstruction is that \<open>Trans\<close>/\<open>Mark\<close>/\<open>RightAnces\<close>
  are defined on a non-reduced \<open>M\<close> by \<open>Trans M := Trans (Red M)\<close>, and \<open>Red\<close> is NOT
  idempotent on \<open>T\<^bsub>PS\<^esub>\<close> (correction A4, counterexample \<open>(0,0)(0,2)\<close>), so a single
  \<open>Red\<close>-step need not land in \<open>RT\<^bsub>PS\<^esub>\<close> and the recursion unfolds again.

  The right move is to transport along the \<^emph>\<open>iterated\<close> \<open>Red\<close>.  Define
  \<open>RedStab M \<equiv> \<exists>k. (Red\<^sup>k) M \<in> RT\<^bsub>PS\<^esub>\<close> (this is precisely the domain of the
  \<open>Trans\<close>/\<open>Mark\<close>/\<open>RightAnces\<close> recursions).  \<open>RedStab\<close> is NOT a vacuous side
  condition: it holds for every \<open>M \<in> RT\<^bsub>PS\<^esub>\<close> (\<open>k=0\<close>), for every non-\<open>multiT\<close>
  \<open>M \<in> T\<^bsub>PS\<^esub>\<close> (\<open>k=1\<close>, @{thm [source] idem_nonmulti}), and empirically for every
  \<open>M \<in> T\<^bsub>PS\<^esub>\<close> whatsoever with \<open>k \<le> 2\<close> (exhaustive census: 7380/7380 sequences of
  length \<open>\<le> 4\<close> over entries \<open>< 3\<close>, and 16275/16275 of length \<open>\<le> 3\<close> over entries
  \<open>< 5\<close>, all reach a \<open>Red\<close>-fixed point in at most two steps; 0 failures).  So
  \<open>RedStab = T\<^bsub>PS\<^esub>\<close> is a purely \<section>6 statement (\<open>Red (Red M) \<in> RT\<^bsub>PS\<^esub>\<close>), independent
  of \<section>7; see \<open>y3s_RedStab_of_Red2\<close> for the one-line bridge.

  On \<open>RedStab\<close> we prove FOUR of the seven article propositions verbatim
  (\<open>p_7_3_Trans_zeroT\<close>, \<open>p_7_3_Pred_Trans_descend\<close>, \<open>p_7_4_RightAnces_RightNodes\<close>,
  \<open>p_7_4_RightAnces_zeroT\<close>).  Of the other three:

    \<^item> \<open>p_7_4_Mark_nextAdm\<close> is covered by recorded correction A47
      (retaining correction A18's corrected pair/order); it lifts only with its
      hypotheses read off the REDUCT, see \<open>y3s_7_4_Mark_nextAdm_TPS_reduct\<close>;

    \<^item> \<open>p_7_4_Trans_nextAdm\<close> and \<open>p_7_4_Trans_Mark_Pred\<close> are \<^bold>\<open>FALSE\<close> as stated on
      \<open>T\<^bsub>PS\<^esub>\<close>.  These are the recorded corrections A45
      (\<open>p_7_4_Trans_nextAdm\<close>) and A46 (\<open>p_7_4_Trans_Mark_Pred\<close>), respectively.
      Witness (vetted \<open>red_model\<close>/\<open>trans_model\<close>):
      \<open>M = (0,0)(0,1)(1,2)(1,0) \<in> T\<^bsub>PS\<^esub>\<close>, non-reduced, with
      \<open>Red M = (0,0)(1,1)(2,2)(2,0) \<in> RT\<^bsub>PS\<^esub>\<close>.  Take \<open>m = j\<^sub>0 = 1\<close>, \<open>j\<^sub>1 = 3\<close>.
      Then \<open>adm M 1\<close> and \<open>(0,1) \<le>\<^sub>M (0,3)\<close>, so \<open>(M,1) \<in> T\<^bsub>PS\<^esub>\<^sup>Marked\<close> and \<open>1\<close> is the
      UNIQUE \<open><\<^bsub>M\<^esub>\<^sup>NextAdm\<close>-parent of \<open>3\<close> --- both propositions' hypotheses hold.
      But \<open>Trans (Pred M) = D\<^sub>0(D\<^sub>2(0))\<close>, \<open>Mark (Pred M) 1 = D\<^sub>2(0)\<close>,
      \<open>Trans M = D\<^sub>0(D\<^sub>2(0) + D\<^sub>1(D\<^sub>2(0) + D\<^sub>0(0)))\<close>, \<open>Mark M 1 = D\<^sub>0(0)\<close>, and there is
      \<^bold>\<open>no\<close> \<open>(s\<^sub>0,b\<^sub>0)\<close> at all that scb-decomposes BOTH pairs (the two singleton scb
      sets are disjoint) --- existence fails, not merely uniqueness.  Root cause:
      \<open>Mark M m := Mark (Red M) m\<close> evaluates the basepoint at the reduct, but
      \<open>\<le>\<^sub>M\<close> is NOT \<open>Red\<close>-invariant on \<open>T\<^bsub>PS\<^esub>\<close> (correction A4): here \<open>(0,1) \<le>\<^sub>M (0,3)\<close>
      holds while \<open>(0,1) \<le>\<^bsub>Red M\<^esub> (0,3)\<close> FAILS, so column \<open>1\<close> is not a basepoint of
      \<open>Red M\<close> and \<open>Mark\<close> returns a value unrelated to \<open>M\<close>'s own structure.  Census
      (entries \<open>< 3\<close>, \<open>Lng \<le> 4\<close>): \<open>p_7_4_Trans_nextAdm\<close> 3990/4023,
      \<open>p_7_4_Trans_Mark_Pred\<close> 4490/4523 --- 33 counterexamples each, ALL non-reduced;
      on reduced \<open>M\<close> both hold (224/224), i.e. our \<open>RT\<^bsub>PS\<^esub>\<close> lemmas
      @{thm [source] m_7_4_Trans_nextAdm}, @{thm [source] m_7_4_Trans_Mark_Pred}
      are exactly right and the article's domain is the error.
      The correct \<open>T\<^bsub>PS\<^esub>\<close>-level statement must read \<open>Marked\<close>/\<open>NextAdm\<close> off \<open>Red M\<close>,
      or restrict to \<open>RT\<^bsub>PS\<^esub>\<close>.\<close>

subsection \<open>Basic \<open>Red\<close>-iteration bricks\<close>

lemma y3s_Red_T_PS:
  assumes MT: "M \<in> T_PS" shows "Red M \<in> T_PS"
proof -
  have "Lng (Red M) = Lng M" by (rule m_6_5_Lng_Red[OF MT])
  moreover have "0 < Lng M" using MT by (auto simp: T_PS_def)
  ultimately have "Red M \<noteq> []" by auto
  thus ?thesis by (simp add: T_PS_def)
qed

lemma y3s_Red_funpow_T_PS:
  assumes MT: "M \<in> T_PS" shows "(Red ^^ k) M \<in> T_PS"
  using MT by (induction k) (simp_all add: y3s_Red_T_PS)

lemma y3s_Lng_funpow_Red:
  assumes MT: "M \<in> T_PS" shows "Lng ((Red ^^ k) M) = Lng M"
proof (induction k)
  case 0 show ?case by simp
next
  case (Suc k)
  have "(Red ^^ Suc k) M = Red ((Red ^^ k) M)" by simp
  moreover have "Lng (Red ((Red ^^ k) M)) = Lng ((Red ^^ k) M)"
    by (rule m_6_5_Lng_Red[OF y3s_Red_funpow_T_PS[OF MT]])
  ultimately show ?case using Suc.IH by simp
qed

lemma y3s_zeroT_funpow_Red:
  assumes MT: "M \<in> T_PS" shows "zeroT M \<longleftrightarrow> zeroT ((Red ^^ k) M)"
proof (induction k)
  case 0 show ?case by simp
next
  case (Suc k)
  have "zeroT ((Red ^^ k) M) \<longleftrightarrow> zeroT (Red ((Red ^^ k) M))"
    by (rule m_6_5_Red_zeroT[OF y3s_Red_funpow_T_PS[OF MT]])
  thus ?case using Suc.IH by simp
qed

text \<open>\<open>Red\<close> commutes with \<open>Pred\<close> on all of \<open>T\<^bsub>PS\<^esub>\<close> (@{thm [source] m_6_5_Red_Pred},
  unconditional), hence so does every iterate.\<close>

lemma y3s_Pred_T_PS:
  assumes MT: "M \<in> T_PS" shows "Pred M \<in> T_PS"
proof (cases "Lng M \<le> 1")
  case True thus ?thesis using MT by (simp add: Pred_def)
next
  case False
  hence L: "1 < Lng M" by simp
  have "Lng (butlast M) = Lng M - 1" by simp
  hence "butlast M \<noteq> []" using L by (cases "butlast M") auto
  thus ?thesis using False by (simp add: Pred_def T_PS_def)
qed

lemma y3s_Pred_funpow_Red:
  assumes MT: "M \<in> T_PS" shows "(Red ^^ k) (Pred M) = Pred ((Red ^^ k) M)"
proof (induction k)
  case 0 show ?case by simp
next
  case (Suc k)
  have "(Red ^^ Suc k) (Pred M) = Red ((Red ^^ k) (Pred M))" by simp
  also have "\<dots> = Red (Pred ((Red ^^ k) M))" using Suc.IH by simp
  also have "\<dots> = Pred (Red ((Red ^^ k) M))"
    by (rule m_6_5_Red_Pred[OF y3s_Red_funpow_T_PS[OF MT]])
  finally show ?case by simp
qed

text \<open>\<open>RT\<^bsub>PS\<^esub>\<close> is closed under \<open>Pred\<close> (for \<open>Lng > 1\<close>): \<open>Red (Pred M) = Pred (Red M)
  = Pred M\<close>.\<close>

lemma y3s_Pred_RT_PS:
  assumes MR: "M \<in> RT_PS" and L: "1 < Lng M" shows "Pred M \<in> RT_PS"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have "Red (Pred M) = Pred (Red M)" by (rule m_6_5_Red_Pred[OF MT])
  also have "\<dots> = Pred M" using MR by (simp add: RT_PS_def)
  finally have e: "Red (Pred M) = Pred M" .
  have "Pred M \<in> T_PS" by (rule y3s_Pred_T_PS[OF MT])
  thus ?thesis using e by (simp add: RT_PS_def)
qed

end
