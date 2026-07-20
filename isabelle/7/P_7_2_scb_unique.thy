theory P_7_2_scb_unique
  imports Support_7_044
begin

section \<open>§7.2 第1種 scb分解の一意性 — conjunct (5) clean assembly (no rneq)\<close>

text \<open>
  Clean nonempty branch of conjunct (5) of @{text p_7_2_scb_unique}: for
  \<open>t \<in> T\<^bsub>B\<^esub>\<close> with \<open>t \<noteq> Trm []\<close>, the 第1種
  (\<^const>\<open>scb_kind1\<close>) scb-decomposition is unique.  A14 is retracted:
  the former empty-term counterexample was an artefact of encoding the kind condition
  only as a vacuous universal implication.  The current positive \<open>isPTB_str c\<close>
  conjunct excludes that case, and the final article proposition handles zero separately.

  This is exactly the HEAD lemma @{thm [source] m_7_2_scb_kind1_unique_uncond'},
  which discharges the residual \<open>RightNodes\<close> length-pin (the extra \<open>rneq\<close>
  hypothesis of @{thm [source] m_7_2_scb_kind1_unique_uncond}) internally via
  @{thm [source] rnsub_kind1_len_pin}: two kind-1 decompositions of the same
  \<open>t\<close> force equal marked-principal \<open>RightNodes\<close> lengths (each is a suffix of
  \<open>RightNodes t\<close> and the kind-1 shape pins the start index).  Hence NO \<open>rneq\<close>
  precondition remains.

  SOUND: cites only the GREEN @{thm [source] m_7_2_scb_kind1_unique_uncond'}
  (itself fully discharged in HEAD), never the goal, never an unproven \<open>p_*\<close>
  axiom, never a domain-false proposition.  The legacy checker
  \<open>python/_scbkind_check.py\<close> covered the nonempty branch (1560 depth-2
  \<open>D\<^sub>\<omega>\<close>-free terms, 0 violations); the zero branch is discharged logically below.\<close>

lemma m_7_2_scb_unique_kind1:
  assumes tTB: "t \<in> T_B" and tne: "t \<noteq> Trm []"
      and d0: "scb_kind1 t s\<^sub>0 c\<^sub>0 b\<^sub>0"
      and d1: "scb_kind1 t s\<^sub>1 c\<^sub>1 b\<^sub>1"
  shows "(s\<^sub>0, c\<^sub>0, b\<^sub>0) = (s\<^sub>1, c\<^sub>1, b\<^sub>1)"
  by (rule m_7_2_scb_kind1_unique_uncond'[OF tTB tne d0 d1])


text \<open>命題（scb分解の一意性） (§7.2):
  (1) the \<open>(s,b)\<close>-part of an scb-decomposition with a fixed \<open>c\<close> is unique;
  (2) \<open>dom(t) = \<nat>\<close> iff \<open>t\<close> is 第\<open>0\<close>種- or 第\<open>1\<close>種-scb-decomposable;
  (3) \<open>t\<close> is not both 第\<open>0\<close>種- and 第\<open>1\<close>種-scb-decomposable;
  (4) the 第\<open>0\<close>種 scb-decomposition of \<open>t\<close> is unique;
  (5) the 第\<open>1\<close>種 scb-decomposition of \<open>t\<close> is unique.\<close>

lemma p_7_2_scb_unique:
  assumes "t \<in> T_B"
  shows "\<And>s\<^sub>0 s\<^sub>1 c b\<^sub>0 b\<^sub>1.
            scb_decomp t s\<^sub>0 c b\<^sub>0 \<Longrightarrow> scb_decomp t s\<^sub>1 c b\<^sub>1 \<Longrightarrow>
            s\<^sub>0 = s\<^sub>1 \<and> b\<^sub>0 = b\<^sub>1"
    and "(domB t = NatSet) \<longleftrightarrow> (scb_kind0_able t \<or> scb_kind1_able t)"
    and "\<not> scb_kind0_able t \<or> \<not> scb_kind1_able t"
    and "\<And>s\<^sub>0 c\<^sub>0 b\<^sub>0 s\<^sub>1 c\<^sub>1 b\<^sub>1.
            scb_kind0 t s\<^sub>0 c\<^sub>0 b\<^sub>0 \<Longrightarrow> scb_kind0 t s\<^sub>1 c\<^sub>1 b\<^sub>1 \<Longrightarrow>
            (s\<^sub>0, c\<^sub>0, b\<^sub>0) = (s\<^sub>1, c\<^sub>1, b\<^sub>1)"
    and "\<And>s\<^sub>0 c\<^sub>0 b\<^sub>0 s\<^sub>1 c\<^sub>1 b\<^sub>1.
            scb_kind1 t s\<^sub>0 c\<^sub>0 b\<^sub>0 \<Longrightarrow> scb_kind1 t s\<^sub>1 c\<^sub>1 b\<^sub>1 \<Longrightarrow>
            (s\<^sub>0, c\<^sub>0, b\<^sub>0) = (s\<^sub>1, c\<^sub>1, b\<^sub>1)"
proof -
  have zero_no_kind:
    "\<And>s c b. scb_kind0 (Trm []) s c b \<or> scb_kind1 (Trm []) s c b \<Longrightarrow> False"
  proof -
    fix s c b
    assume k: "scb_kind0 (Trm []) s c b \<or> scb_kind1 (Trm []) s c b"
    have eq: "[Zsym] = s @ c @ b" and pt: "isPTB_str c"
      using k by (auto simp: scb_kind0_def scb_kind1_def scb_decomp_def)
    obtain p where cp: "c = flatBP p" using pt unfolding isPTB_str_def by blast
    have "length (flatBP p) \<le> length [Zsym]" using eq cp by simp
    moreover have "2 \<le> length (flatBP p)" by (rule flatBP_len_ge2)
    ultimately show False by simp
  qed
  show "\<And>s\<^sub>0 s\<^sub>1 c b\<^sub>0 b\<^sub>1.
            scb_decomp t s\<^sub>0 c b\<^sub>0 \<Longrightarrow> scb_decomp t s\<^sub>1 c b\<^sub>1 \<Longrightarrow>
            s\<^sub>0 = s\<^sub>1 \<and> b\<^sub>0 = b\<^sub>1"
    by (rule m_7_2_scb_unique_decomp[OF assms])
  show "(domB t = NatSet) \<longleftrightarrow> (scb_kind0_able t \<or> scb_kind1_able t)"
  proof (cases "t = Trm []")
    case True
    have nk0: "\<not> scb_kind0_able t" using True zero_no_kind by blast
    have nk1: "\<not> scb_kind1_able t" using True zero_no_kind by blast
    show ?thesis using True nk0 nk1
      by (simp add: domB_unfold NatSet_def)
  next
    case False
    show ?thesis by (rule m_7_2_scb_unique_domB[OF assms False])
  qed
  show "\<not> scb_kind0_able t \<or> \<not> scb_kind1_able t"
  proof (cases "t = Trm []")
    case True
    have "\<not> scb_kind0_able t" using True zero_no_kind by blast
    thus ?thesis by blast
  next
    case False
    show ?thesis by (rule m_7_2_scb_kinds_exclusive[OF False])
  qed
  show "\<And>s\<^sub>0 c\<^sub>0 b\<^sub>0 s\<^sub>1 c\<^sub>1 b\<^sub>1.
            scb_kind0 t s\<^sub>0 c\<^sub>0 b\<^sub>0 \<Longrightarrow> scb_kind0 t s\<^sub>1 c\<^sub>1 b\<^sub>1 \<Longrightarrow>
            (s\<^sub>0, c\<^sub>0, b\<^sub>0) = (s\<^sub>1, c\<^sub>1, b\<^sub>1)"
  proof -
    fix s\<^sub>0 c\<^sub>0 b\<^sub>0 s\<^sub>1 c\<^sub>1 b\<^sub>1
    assume d0: "scb_kind0 t s\<^sub>0 c\<^sub>0 b\<^sub>0"
       and d1: "scb_kind0 t s\<^sub>1 c\<^sub>1 b\<^sub>1"
    show "(s\<^sub>0, c\<^sub>0, b\<^sub>0) = (s\<^sub>1, c\<^sub>1, b\<^sub>1)"
    proof (cases "t = Trm []")
      case True
      thus ?thesis using zero_no_kind d0 by blast
    next
      case False
      show ?thesis by (rule m_7_2_scb_kind0_unique_uncond[OF assms False d0 d1])
    qed
  qed
  show "\<And>s\<^sub>0 c\<^sub>0 b\<^sub>0 s\<^sub>1 c\<^sub>1 b\<^sub>1.
            scb_kind1 t s\<^sub>0 c\<^sub>0 b\<^sub>0 \<Longrightarrow> scb_kind1 t s\<^sub>1 c\<^sub>1 b\<^sub>1 \<Longrightarrow>
            (s\<^sub>0, c\<^sub>0, b\<^sub>0) = (s\<^sub>1, c\<^sub>1, b\<^sub>1)"
  proof -
    fix s\<^sub>0 c\<^sub>0 b\<^sub>0 s\<^sub>1 c\<^sub>1 b\<^sub>1
    assume d0: "scb_kind1 t s\<^sub>0 c\<^sub>0 b\<^sub>0"
       and d1: "scb_kind1 t s\<^sub>1 c\<^sub>1 b\<^sub>1"
    show "(s\<^sub>0, c\<^sub>0, b\<^sub>0) = (s\<^sub>1, c\<^sub>1, b\<^sub>1)"
    proof (cases "t = Trm []")
      case True
      thus ?thesis using zero_no_kind d0 by blast
    next
      case False
      show ?thesis by (rule m_7_2_scb_unique_kind1[OF assms False d0 d1])
    qed
  qed
qed

end
