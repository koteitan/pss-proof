theory Support_7_022
  imports Frontier_7_026
begin

text \<open>Helper: the §7.2 \<open>RightNodes\<close>-subexpression engine
  (@{thm [source] m_7_2_RightNodes_subexpr}) without its \<open>t \<in> PT\<^bsub>B\<^esub>\<close>
  (\<open>\<exists>p. t = Trm [p]\<close>) hypothesis.  The principality of the substituted body \<open>t\<close>
  is never used in the engine's proof (only \<open>t \<in> T\<^bsub>B\<^esub>\<close> via the spine
  substitution bricks @{thm [source] rnsub_flat_main},
  @{thm [source] rnsub_RightNodes_spineSub}, @{thm [source] rnsub_RightNodes_t0_lastv}),
  but it is needed here because the body of \<open>Mark M m\<close> is in general a multi
  term (empirically 47/140 marked cases), not principal.\<close>

lemma m_7_4_RightNodes_subexpr_gen:
  fixes v :: nat
  assumes tTB: "t \<in> T_B"
    and bRP: "\<forall>x \<in> set b. x = RP"
    and t0TB: "t\<^sub>0 \<in> T_B" and flat0: "flatBT t\<^sub>0 = s @ flatBT (Dpt (enat v) 0\<^sub>B) @ b"
  shows "\<exists>!aa. RightNodes (spineSub t\<^sub>0 t) = fst aa @ [v] @ snd aa
            \<and> RightNodes t\<^sub>0 = fst aa @ [v]
            \<and> RightNodes (Dpt (enat v) t) = [v] @ snd aa"
proof -
  have Hf: "flatBT t\<^sub>0 = s @ Dsym (enat v) # Zsym # b"
    using flat0 by simp
  have t0_ne: "t\<^sub>0 \<noteq> Trm []"
  proof
    assume "t\<^sub>0 = Trm []"
    hence "flatBT t\<^sub>0 = [Zsym]" by simp
    thus False using flat0 by (cases s) auto
  qed
  have rn1: "RightNodes (spineSub t\<^sub>0 t) = RightNodes t\<^sub>0 @ RightNodes t"
    using rnsub_RightNodes_spineSub[OF t0_ne] by blast
  have rn0_last: "\<exists>a0. RightNodes t\<^sub>0 = a0 @ [v]"
    using rnsub_RightNodes_t0_lastv Hf bRP t0TB by blast
  then obtain a0 where rn0: "RightNodes t\<^sub>0 = a0 @ [v]" by blast
  define a1 where "a1 = RightNodes t"
  have rnDvt: "RightNodes (Dpt (enat v) t) = [v] @ a1"
    unfolding a1_def by simp
  have rnt1: "RightNodes (spineSub t\<^sub>0 t) = a0 @ [v] @ a1"
    using rn1 rn0 unfolding a1_def by simp
  show "\<exists>!aa. RightNodes (spineSub t\<^sub>0 t) = fst aa @ [v] @ snd aa
            \<and> RightNodes t\<^sub>0 = fst aa @ [v]
            \<and> RightNodes (Dpt (enat v) t) = [v] @ snd aa"
  proof (rule ex1I[of _ "(a0, a1)"])
    show "RightNodes (spineSub t\<^sub>0 t) = fst (a0,a1) @ [v] @ snd (a0,a1)
        \<and> RightNodes t\<^sub>0 = fst (a0,a1) @ [v]
        \<and> RightNodes (Dpt (enat v) t) = [v] @ snd (a0,a1)"
      using rnt1 rn0 rnDvt by simp
  next
    fix aa
    assume "RightNodes (spineSub t\<^sub>0 t) = fst aa @ [v] @ snd aa
          \<and> RightNodes t\<^sub>0 = fst aa @ [v]
          \<and> RightNodes (Dpt (enat v) t) = [v] @ snd aa"
    hence f0: "RightNodes t\<^sub>0 = fst aa @ [v]"
      and fD: "RightNodes (Dpt (enat v) t) = [v] @ snd aa" by auto
    have "fst aa = a0" using f0 rn0 by simp
    moreover have "snd aa = a1" using fD rnDvt by simp
    ultimately show "aa = (a0, a1)" by (cases aa) simp
  qed
qed

end
