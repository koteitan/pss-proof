theory Support_7_045
  imports P_7_2_scb_unique
begin

section \<open>§7.3 命題（\<open>Trans\<close>の\<open>(IncrFirst,Red)\<close>不変\<open>P\<close>同変性）(2) — the \<open>\<Sigma>\<^bsub>B\<^esub>\<close>
  representation (A16-corrected: non-zero leading \<open>P\<close>-component)\<close>

text \<open>Article (content.md 2236), conjunct (2): for multiterm \<open>M\<close>, with each
  \<open>P\<close>-component contributing \<open>t\<^sub>J = D\<^sub>0 0\<close> if it is a zero-term and
  \<open>t\<^sub>J = Trans(P(M)\<^sub>J)\<close> otherwise, \<open>Trans M = \<Sigma>\<^bsub>B\<^esub>(t\<^sub>J)\<^bsub>J=0\<^esub>\<^bsup>J\<^sub>1\<^esup>\<close>.

  CORRECTION A16: as literally stated this is FALSE — the recursive (C) branch of
  \<open>Trans\<close> peels off the LAST \<open>P\<close>-component and recurses into the prefix
  \<open>take (Pcut M) M\<close>, whose base case \<open>((0,0))\<close> evaluates to \<open>0\<^sub>B\<close> (not \<open>D\<^sub>0 0\<close>):
  a leading zero-term \<open>P\<close>-block is ABSORBED, so the naive sum is off by a leading
  \<open>D\<^sub>0 0\<close>.  Empirically (\<open>check_transP.py\<close>): of 3529 reduced multiterm cases,
  the 102 failures all have \<open>zeroT (P M ! 0)\<close>; restricting to
  \<open>\<not> zeroT (P M ! 0)\<close> gives 0/3427 failures.  Stated here as the A16-corrected
  iff on \<open>RT\<^bsub>PS\<^esub>\<close> with that hypothesis (which is INDUCTIVE: \<open>P (take (Pcut M) M)
  = butlast (P M)\<close> keeps the same leading component).

  Form: \<open>Trans M = \<Sigma>\<^bsub>B\<^esub> (map (\<lambda>PJ. if zeroT PJ then D\<^sub>0 0 else Trans PJ) (P M))\<close>.
  On reduced \<open>M\<close> each zero-term \<open>P\<close>-component equals exactly \<open>[(0,0)]\<close>
  (@{thm [source] m_6_6_oneColumn}), so the \<open>zeroT\<close> test matches the recursion's
  literal \<open>= [(0,0)]\<close> test.\<close>

lemma SigmaB_single: "SigmaB [t] = t"
  by (cases t) (simp add: SigmaB_def)

lemma m_7_3_Trans_P_equivariance:
  assumes MR: "M \<in> RT_PS" and nz0: "\<not> zeroT (P M ! 0)"
  shows "Trans M
         = SigmaB (map (\<lambda>PJ. if zeroT PJ then Dpt 0 0\<^sub>B else Trans PJ) (P M))"
proof -
  let ?tJ = "\<lambda>PJ. if zeroT PJ then Dpt 0 0\<^sub>B else Trans PJ"
  \<comment> \<open>strengthen to an induction on \<open>Lng M\<close>; the hypothesis is inductive\<close>
  have main: "\<And>N. N \<in> RT_PS \<longrightarrow> \<not> zeroT (P N ! 0)
              \<longrightarrow> Trans N = SigmaB (map ?tJ (P N))"
  proof -
    fix N0 :: pairseq
    show "N0 \<in> RT_PS \<longrightarrow> \<not> zeroT (P N0 ! 0)
          \<longrightarrow> Trans N0 = SigmaB (map ?tJ (P N0))"
    proof (induction N0 rule: measure_induct_rule[where f=Lng])
      case (less N)
      show ?case
      proof (intro impI)
        assume NR: "N \<in> RT_PS" and nzN: "\<not> zeroT (P N ! 0)"
        have NT: "N \<in> T_PS" using NR by (simp add: RT_PS_def)
        show "Trans N = SigmaB (map ?tJ (P N))"
        proof (cases "multiT N \<and> 1 < Lng N")
          case False
          \<comment> \<open>base: \<open>P N = [N]\<close>, so the sum is the single term \<open>?tJ N\<close>\<close>
          have PN: "P N = [N]" by (rule poper_P_nonmulti[OF False])
          have nzNN: "\<not> zeroT N" using nzN PN by simp
          have "SigmaB (map ?tJ (P N)) = ?tJ N"
            by (simp only: PN list.map SigmaB_single)
          also have "\<dots> = Trans N" using nzNN by simp
          finally show ?thesis ..
        next
          case True
          hence mu: "multiT N" and L: "1 < Lng N" by simp_all
          let ?A = "take (Pcut N) N"
          let ?PJ = "drop (Pcut N) N"
          \<comment> \<open>P-decomposition of the multiterm: prefix \<open>?A\<close> + last block \<open>?PJ\<close>\<close>
          have PNsplit: "P N = P ?A @ [?PJ]"
            by (rule poper_P_multi[OF True])
          have PAne: "P ?A \<noteq> []" by (rule P_nonempty)
          \<comment> \<open>the prefix is reduced and inherits the non-zero leading component\<close>
          have ARC: "?A \<in> RT_PS" by (rule trans_multiT_prefix_RT_PS[OF NR mu])
          have headA: "P ?A ! 0 = P N ! 0"
            using PNsplit PAne by (simp add: nth_append)
          have nzA: "\<not> zeroT (P ?A ! 0)" using nzN headA by simp
          have Lpref: "Lng ?A < Lng N"
          proof -
            have cut: "0 < Pcut N \<and> Pcut N \<le> Lng N - 1" using Pcut_le[OF L] by simp
            have "Lng ?A = min (Lng N) (Pcut N)" by simp
            thus ?thesis using cut L by linarith
          qed
          \<comment> \<open>IH on the strictly-shorter prefix\<close>
          have IHA: "Trans ?A = SigmaB (map ?tJ (P ?A))"
            using less.IH[OF Lpref] ARC nzA by blast
          \<comment> \<open>the multiterm (C) branch of the \<open>Trans\<close> recursion\<close>
          have nmono: "\<not> monoT N" using mu by (simp add: multiT_def)
          have domT: "Trans_Mark_dom (Inl N)" by (rule m_7_3_Trans_welldef[OF NR])
          have PJeq: "P N ! (Lng (P N) - 1) = ?PJ"
            by (rule trans_multiT_last_component(1)[OF NT mu])
          have cut: "0 < Pcut N \<and> Pcut N \<le> Lng N - 1" using Pcut_le[OF L] by simp
          have LdJ: "Lng (drop (Pcut N) N) = Lng N - Pcut N" by simp
          have Aeq2: "seg N 0 (Lng N - 1 - Lng (drop (Pcut N) N) + 1 - 1) = ?A"
          proof -
            have "Lng N - 1 - Lng (drop (Pcut N) N) + 1 - 1 = Pcut N - 1"
              using LdJ cut by linarith
            moreover have "seg N 0 (Pcut N - 1) = take (Suc (Pcut N - 1)) N"
              by (rule seg_0_eq_take) (use cut L in linarith)
            moreover have "Suc (Pcut N - 1) = Pcut N" using cut by simp
            ultimately show ?thesis by simp
          qed
          have c1: "(N \<notin> RT_PS) = False" using NR by simp
          have c2: "(Lng N - 1 = 0) = False" using L by simp
          have c3: "monoT N = False" using nmono by simp
          have transN: "Trans N = (if ?PJ = [(0, 0)] then Trans ?A +\<^sub>B Dpt 0 0\<^sub>B
                                   else Trans ?A +\<^sub>B Trans ?PJ)"
          proof -
            have raw: "Trans N =
                (if P N ! (Lng (P N) - 1) = [(0, 0)]
                 then Trans (seg N 0 (Lng N - 1 - Lng (P N ! (Lng (P N) - 1)) + 1 - 1))
                        +\<^sub>B Dpt 0 0\<^sub>B
                 else Trans (seg N 0 (Lng N - 1 - Lng (P N ! (Lng (P N) - 1)) + 1 - 1))
                        +\<^sub>B Trans (P N ! (Lng (P N) - 1)))"
              by (subst Trans.psimps[OF domT]) (simp only: c1 c2 c3 if_False Let_def)
            show ?thesis unfolding raw PJeq Aeq2 ..
          qed
          \<comment> \<open>on the reduced last block, \<open>zeroT ?PJ \<longleftrightarrow> ?PJ = [(0,0)]\<close>\<close>
          have Pne: "P N \<noteq> []" by (rule P_nonempty)
          have J1lt: "Lng (P N) - 1 < Lng (P N)" using Pne by (cases "P N") auto
          have PJRT: "?PJ \<in> RT_PS"
            using m_6_6_P_reduced[OF NT] NR J1lt PJeq by auto
          have PJT: "?PJ \<in> T_PS" using PJRT by (simp add: RT_PS_def)
          have ziff: "zeroT ?PJ \<longleftrightarrow> ?PJ = [(0, 0)]"
          proof
            assume z: "zeroT ?PJ"
            have L1: "Lng ?PJ = 1" using z by (simp add: zeroT_def)
            then obtain v where v: "?PJ = [(v, v)]"
              using m_6_6_oneColumn[OF PJT] PJRT by auto
            have "entry ?PJ 1 0 = 0" using z by (simp add: zeroT_def)
            hence "v = 0" using v by (simp add: entry_def)
            thus "?PJ = [(0, 0)]" using v by simp
          next
            assume "?PJ = [(0, 0)]"
            thus "zeroT ?PJ" by (simp add: zeroT_def entry_def)
          qed
          \<comment> \<open>assemble: RHS sum splits off the last block via @{thm SigmaB_snoc}\<close>
          have "SigmaB (map ?tJ (P N)) = SigmaB (map ?tJ (P ?A) @ [?tJ ?PJ])"
            by (simp add: PNsplit)
          also have "\<dots> = SigmaB (map ?tJ (P ?A)) +\<^sub>B ?tJ ?PJ"
            by (rule SigmaB_snoc)
          also have "\<dots> = Trans ?A +\<^sub>B ?tJ ?PJ" using IHA by simp
          also have "\<dots> = Trans N"
          proof (cases "?PJ = [(0, 0)]")
            case True
            have "?tJ ?PJ = Dpt 0 0\<^sub>B" using True ziff by simp
            thus ?thesis using transN True by simp
          next
            case False
            have "?tJ ?PJ = Trans ?PJ" using False ziff by simp
            thus ?thesis using transN False by simp
          qed
          finally show ?thesis ..
        qed
      qed
    qed
  qed
  show ?thesis using main[of M] MR nz0 by blast
qed


section \<open>§7.3 命題（\<open>Mark\<close> の \<open>(IncrFirst,Red,P)\<close> 不変性）part (2): the P-invariance\<close>

text \<open>The article's \<open>Mark\<close>-\<open>(IncrFirst,Red,P)\<close>-invariance proposition (content.md
  2246–2252) has two parts.  Part (1) — \<open>Mark M m = Mark (Red M) m =
  Mark (IncrFirst M) m\<close> — is @{thm [source] m_7_3_Mark_Red} /
  @{thm [source] m_7_3_Mark_IncrFirst}.  Part (2) is the \<open>P\<close>-invariance for a
  \<open>multiT\<close> sequence: with \<open>J\<^sub>1 := Lng (P M) - 1\<close> the LAST component is
  \<open>P M ! J\<^sub>1 = drop (Pcut M) M\<close> (@{thm [source] trans_multiT_last_component}) and,
  writing \<open>j\<^sub>0 := Pcut M\<close> for the index offset (the article's
  \<open>j\<^sub>0 = Lng M - Lng (P M)\<^bsub>J\<^sub>1\<^esub>\<close>; the source text's \<open>-1\<close> is an off-by-one typo —
  the formalised offset \<open>Pcut M = Lng M - Lng (drop (Pcut M) M)\<close> is what the
  \<open>Mark\<close>/\<open>Trans\<close> recursion actually uses, matching \<open>python/trans_model.py\<close>),
  \<open>Mark M m = D\<^sub>0 0\<close> if the last component is zero (\<open>= [(0,0)]\<close>) and
  \<open>Mark M m = Mark (P M)\<^bsub>J\<^sub>1\<^esub> (m - j\<^sub>0)\<close> otherwise.

  This is the \<open>(C)\<close>-branch of the \<open>Mark\<close> recursion, read off
  @{thm [source] Mark.psimps} on the \<open>RT\<^sub>PS\<close> domain (the §7.3 convention; on
  \<open>T\<^sub>PS\<close> the recursion bottoms out only after \<open>Red\<close>, the same A4 idempotency
  caveat as well-definedness).  No \<open>P\<close>-equivariance §6 machinery is needed: the
  equation is the function's own definitional unfolding, so the proof is the
  \<open>markM\<close> step already used inside @{thm [source] trans_inv_C} /
  @{thm [source] m_7_4_repr_multiT_step}, extracted as a standalone lemma.

  Empirical check (\<open>python/trans_model.py\<close>): on all reduced \<open>multiT\<close> sequences of
  \<open>Lng \<le> 5\<close>, entries \<open>\<le> 3\<close> (and the \<open>Lng \<le> 4\<close> yaBMS-standard subset), the
  equation holds with 0 counterexamples for every \<open>m\<close>.\<close>

lemma m_7_3_Mark_P_invariance:
  assumes MR: "M \<in> RT_PS" and mu: "multiT M"
  shows "Mark M m
         = (if drop (Pcut M) M = [(0, 0)] then Dpt 0 0\<^sub>B
            else Mark (drop (Pcut M) M) (m - Pcut M))"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have L: "1 < Lng M" by (rule multiT_imp_Lng_gt1[OF MT mu])
  have nmono: "\<not> monoT M" using mu by (simp add: multiT_def)
  have domK: "Trans_Mark_dom (Inr (M, m))" by (rule m_7_3_Mark_welldef[OF MR])
  let ?PJ = "drop (Pcut M) M"
  \<comment> \<open>identify the def's \<open>PJ\<close> / \<open>j\<^sub>0\<close> with their \<open>Pcut\<close>-forms\<close>
  have PJeq: "P M ! (Lng (P M) - 1) = ?PJ"
    by (rule trans_multiT_last_component(1)[OF MT mu])
  \<comment> \<open>offset equation in \<open>drop\<close>-form so it matches AFTER @{thm PJeq} has
     rewritten \<open>P M ! (Lng (P M) - 1)\<close> to \<open>?PJ\<close> (a \<open>P M ! \<dots>\<close>-form would no
     longer match, leaving an unreduced offset — the failure mode of the
     naive \<open>unfolding\<close>)\<close>
  have cut: "0 < Pcut M \<and> Pcut M \<le> Lng M - 1" using Pcut_le[OF L] by simp
  have LdJ: "Lng ?PJ = Lng M - Pcut M" by simp
  have meq2: "m - (Lng M - 1 - Lng ?PJ + 1) = m - Pcut M"
  proof -
    have "Lng M - 1 - Lng ?PJ + 1 = Pcut M" using LdJ cut by linarith
    thus ?thesis by simp
  qed
  \<comment> \<open>collapse only the OUTER ifs of the \<open>Mark\<close> body with \<open>simp only\<close>\<close>
  have c1: "(M \<notin> RT_PS) = False" using MR by simp
  have c2: "(Lng M - 1 = 0) = False" using L by simp
  have c3: "monoT M = False" using nmono by simp
  have raw: "Mark M m =
      (if P M ! (Lng (P M) - 1) = [(0, 0)] then Dpt 0 0\<^sub>B
       else Mark (P M ! (Lng (P M) - 1))
              (m - (Lng M - 1 - Lng (P M ! (Lng (P M) - 1)) + 1)))"
    by (subst Mark.psimps[OF domK]) (simp only: c1 c2 c3 if_False Let_def)
  show ?thesis unfolding raw PJeq meq2 ..
qed

end
