theory P_7_2_RightNodes_subexpr
  imports Frontier_7_008
begin

text \<open>
  m: 命題（\<open>RightNodes\<close>と部分表現の関係） (§7.2).  The target stub
  \<open>p_7_2_RightNodes_subexpr\<close>: discharged via the spine substitution \<open>spineSub\<close>.
  The unique \<open>(a\<^sub>0,a\<^sub>1)\<close> is \<open>a\<^sub>0 = RightNodes t\<^sub>0\<close> minus the last \<open>[v]\<close>, \<open>a\<^sub>1 = RightNodes t\<close>.
\<close>

lemma m_7_2_RightNodes_subexpr:
  fixes v :: nat
  assumes "t \<in> T_B" "\<exists>p. t = Trm [p]"
    and "\<forall>x \<in> set b. x = RP"
    and "t\<^sub>0 \<in> T_B" "flatBT t\<^sub>0 = s @ flatBT (Dpt (enat v) 0\<^sub>B) @ b"
  shows "\<exists>t\<^sub>1. t\<^sub>1 \<in> T_B \<and> flatBT t\<^sub>1 = s @ flatBT (Dpt (enat v) t) @ b
            \<and> Lng (PB t\<^sub>1) = Lng (PB t\<^sub>0)
            \<and> (\<exists>!aa. RightNodes t\<^sub>1 = fst aa @ [v] @ snd aa
                  \<and> RightNodes t\<^sub>0 = fst aa @ [v]
                  \<and> RightNodes (Dpt (enat v) t) = [v] @ snd aa)"
proof -
  define t1 where "t1 = spineSub t\<^sub>0 t"
  \<comment> \<open>the flat hypothesis in cons form\<close>
  have Hf: "flatBT t\<^sub>0 = s @ Dsym (enat v) # Zsym # b"
    using assms(5) by simp
  \<comment> \<open>main structural lemma\<close>
  have main: "flatBT t1 = s @ Dsym (enat v) # flatBT t @ b \<and> t1 \<in> T_B"
    unfolding t1_def
    using rnsub_flat_main Hf assms(3) assms(4) assms(1) by blast
  have flat1: "flatBT t1 = s @ flatBT (Dpt (enat v) t) @ b"
    using main by simp
  have memTB: "t1 \<in> T_B" using main by blast
  \<comment> \<open>\<open>t\<^sub>0 \<noteq> 0\<close> (its flat contains a \<open>Dsym\<close>)\<close>
  have t0_ne: "t\<^sub>0 \<noteq> Trm []"
  proof
    assume "t\<^sub>0 = Trm []"
    hence "flatBT t\<^sub>0 = [Zsym]" by simp
    thus False using assms(5) by (cases s) auto
  qed
  \<comment> \<open>RightNodes of the substitution: \<open>RightNodes t\<^sub>0 \<frown> RightNodes t\<close>\<close>
  have rn1: "RightNodes t1 = RightNodes t\<^sub>0 @ RightNodes t"
    unfolding t1_def using rnsub_RightNodes_spineSub[OF t0_ne] by blast
  \<comment> \<open>\<open>RightNodes t\<^sub>0 = a\<^sub>0 @ [v]\<close>: the rightmost-spine bottom is \<open>D\<^sub>v 0\<close>.\<close>
  obtain p where tp: "t = Trm [p]" using assms(2) by blast
  \<comment> \<open>Identify the spine bottom of \<open>t\<^sub>0\<close> as \<open>D\<^sub>v 0\<close> by re-running the bottom alignment.\<close>
  have rn0_last: "\<exists>a0. RightNodes t\<^sub>0 = a0 @ [v]"
    using rnsub_RightNodes_t0_lastv Hf assms(3) assms(4) by blast
  then obtain a0 where rn0: "RightNodes t\<^sub>0 = a0 @ [v]" by blast
  define a1 where "a1 = RightNodes t"
  have rnDvt: "RightNodes (Dpt (enat v) t) = [v] @ a1"
    unfolding a1_def by simp
  have rnt1: "RightNodes t1 = a0 @ [v] @ a1"
    using rn1 rn0 unfolding a1_def by simp
  \<comment> \<open>Lng PB preserved: only the last component's argument changes.\<close>
  have lng: "Lng (PB t1) = Lng (PB t\<^sub>0)"
    unfolding t1_def using rnsub_Lng_spineSub[OF t0_ne] .
  \<comment> \<open>the unique pair\<close>
  have uniq: "\<exists>!aa. RightNodes t1 = fst aa @ [v] @ snd aa
                  \<and> RightNodes t\<^sub>0 = fst aa @ [v]
                  \<and> RightNodes (Dpt (enat v) t) = [v] @ snd aa"
  proof (rule ex1I[of _ "(a0, a1)"])
    show "RightNodes t1 = fst (a0,a1) @ [v] @ snd (a0,a1)
        \<and> RightNodes t\<^sub>0 = fst (a0,a1) @ [v]
        \<and> RightNodes (Dpt (enat v) t) = [v] @ snd (a0,a1)"
      using rnt1 rn0 rnDvt by simp
  next
    fix aa
    assume "RightNodes t1 = fst aa @ [v] @ snd aa
          \<and> RightNodes t\<^sub>0 = fst aa @ [v]
          \<and> RightNodes (Dpt (enat v) t) = [v] @ snd aa"
    hence f0: "RightNodes t\<^sub>0 = fst aa @ [v]"
      and fD: "RightNodes (Dpt (enat v) t) = [v] @ snd aa" by auto
    have "fst aa = a0" using f0 rn0 by simp
    moreover have "snd aa = a1" using fD rnDvt by simp
    ultimately show "aa = (a0, a1)" by (cases aa) simp
  qed
  show ?thesis
    using memTB flat1 lng uniq by blast
qed


text \<open>命題（\<open>RightNodes\<close>と部分表現の関係） (§7.2): for strings \<open>s,b\<close>, \<open>v \<in> \<nat>\<close> and
  \<open>t \<in> PT\<^bsub>B\<^esub>\<close>, if \<open>b\<close> consists only of \<open>\<^bold>)\<close> and \<open>s\<frown>flat(D\<^sub>v 0)\<frown>b \<in> T\<^bsub>B\<^esub>\<close>, then
  \<open>s\<frown>flat(D\<^sub>v t)\<frown>b \<in> T\<^bsub>B\<^esub>\<close>, \<open>Lng(P(s D\<^sub>v t b)) = Lng(P(s D\<^sub>v 0 b))\<close>, and there are
  unique \<open>a\<^sub>0,a\<^sub>1 \<in> \<nat>\<^bsup><\<omega>\<^esup>\<close> with
  (1) \<open>RightNodes(s D\<^sub>v t b) = a\<^sub>0 \<frown> [v] \<frown> a\<^sub>1\<close>;
  (2) \<open>RightNodes(s D\<^sub>v 0 b) = a\<^sub>0 \<frown> [v]\<close>;
  (3) \<open>RightNodes(D\<^sub>v t) = [v] \<frown> a\<^sub>1\<close>.
  Modelling: \<open>P(\<dots>)\<close> on a string = \<open>P\<^bsub>B\<^esub>\<close> of the witnessing term \<open>unflatBT\<close>.\<close>

lemma p_7_2_RightNodes_subexpr:
  fixes v :: nat
  assumes "t \<in> T_B" "\<exists>p. t = Trm [p]"
    and "\<forall>x \<in> set b. x = RP"
    and "t\<^sub>0 \<in> T_B" "flatBT t\<^sub>0 = s @ flatBT (Dpt (enat v) 0\<^sub>B) @ b"
  shows "\<exists>t\<^sub>1. t\<^sub>1 \<in> T_B \<and> flatBT t\<^sub>1 = s @ flatBT (Dpt (enat v) t) @ b
            \<and> Lng (PB t\<^sub>1) = Lng (PB t\<^sub>0)
            \<and> (\<exists>!aa. RightNodes t\<^sub>1 = fst aa @ [v] @ snd aa
                  \<and> RightNodes t\<^sub>0 = fst aa @ [v]
                  \<and> RightNodes (Dpt (enat v) t) = [v] @ snd aa)"
  using assms by (rule m_7_2_RightNodes_subexpr)

end
