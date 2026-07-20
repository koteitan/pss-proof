theory Support_7_035
  imports Frontier_7_040
begin

section \<open>§7.3 系（\<open>s\<^sub>1\<close> と \<open>b\<^sub>1\<close> の空性と基点の関係）— content.md 2444\<close>

text \<open>With \<open>s\<^sub>1, b\<^sub>1\<close> the scb-decomposition that the \<open>Trans\<close> recursion uses to match
  \<open>c\<^sub>1\<close> inside \<open>t\<^sub>1 = Trans (Pred M)\<close> (the \<open>SOME\<close> of @{thm [source] Trans.psimps}),
  the following are equivalent for \<open>M \<in> RT\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close> (with \<open>j\<^sub>1 > 0\<close>,
  \<open>t\<^sub>1 \<noteq> 0\<close>): (1) \<open>j\<^sub>-\<^sub>1 = 0\<close>; (2) \<open>s\<^sub>1 = ()\<close>, \<open>c\<^sub>1 = t\<^sub>1\<close>, \<open>b\<^sub>1 = ()\<close>.  Both reduce
  to \<open>c\<^sub>1 = t\<^sub>1\<close>: by 系（左端第\<open>1\<close>基点の \<open>Mark\<close> の基本性質）(2) applied to \<open>Pred M\<close>,
  \<open>c\<^sub>1 = Mark (Pred M) j\<^sub>-\<^sub>1 = Trans (Pred M) = t\<^sub>1 \<longleftrightarrow> j\<^sub>-\<^sub>1 = 0\<close>; and given \<open>c\<^sub>1 = t\<^sub>1\<close>,
  the scb-\<open>SOME\<close> is the trivial self-decomposition \<open>([],[])\<close>
  (@{thm [source] scb_SOME_self}).\<close>

lemma m_7_3_s1_b1_empty:
  assumes MR: "M \<in> RT_PS" and MP: "M \<in> PT_PS"
    and J1pos: "transJ1 M > 0" and T1: "transT1 M \<noteq> 0\<^sub>B"
  defines "sb1 \<equiv> (SOME sb. scb_decomp (transT1 M) (fst sb)
                              (flatBT (transC1 M)) (snd sb))"
  shows "(transJm1 M = 0)
           \<longleftrightarrow> (fst sb1 = [] \<and> transC1 M = transT1 M \<and> snd sb1 = [])"
proof -
  have MT: "M \<in> T_PS" using MP by (simp add: PT_PS_def)
  have mono: "monoT M" using MP by (simp add: PT_PS_def)
  have predRT: "Pred M \<in> RT_PS" by (rule Pred_PT_PS_t1ne(1)[OF MR MP J1pos T1])
  have predPT: "Pred M \<in> PT_PS" by (rule Pred_PT_PS_t1ne(2)[OF MR MP J1pos T1])
  have L: "1 < Lng M" using J1pos by (simp add: transJ1_def)
  have hp: "hasParent M 0 (Lng M - 1)" by (rule monoT_hasParent0_last[OF MT mono L])
  \<comment> \<open>\<open>c\<^sub>1 = Mark (Pred M) j\<^sub>-\<^sub>1\<close>, \<open>t\<^sub>1 = Trans (Pred M)\<close>\<close>
  have c1mark: "transC1 M = Mark (Pred M) (transJm1 M)" by (simp add: transC1_def)
  have t1eq: "transT1 M = Trans (Pred M)" by (simp add: transT1_def)
  \<comment> \<open>\<open>(Pred M, j\<^sub>-\<^sub>1) \<in> Marked\<close>\<close>
  have mkd: "(Pred M, transJm1 M) \<in> Marked"
    using Marked_Pred_Adm[OF MT L hp] by (simp add: transJm1_def transJ0_def transJ1_def)
  \<comment> \<open>core equivalence: \<open>c\<^sub>1 = t\<^sub>1 \<longleftrightarrow> j\<^sub>-\<^sub>1 = 0\<close> (左端第\<open>1\<close>基点, on \<open>Pred M\<close>)\<close>
  have core: "(transC1 M = transT1 M) \<longleftrightarrow> (transJm1 M = 0)"
    using m_7_3_Mark_leftmost1(2)[OF predRT predPT mkd] c1mark t1eq by simp
  show ?thesis
  proof
    assume "transJm1 M = 0"
    hence c1t1: "transC1 M = transT1 M" using core by simp
    \<comment> \<open>\<open>c\<^sub>1\<close> single principal, so scb-\<open>SOME\<close> against itself is \<open>([],[])\<close>\<close>
    have pc1: "Lng (PB (transC1 M)) = 1"
      by (rule transC1_single_principal[OF MR MP J1pos T1])
    have c1Dpt: "transC1 M = Dpt (transV M) (transT2 M)"
      using principal_reconstruct[OF pc1] by (simp add: transV_def transT2_def)
    have mkdC: "(Pred M, transJm1 M) \<in> Marked" using mkd .
    have c1TB: "transC1 M \<in> T_B"
      using m_7_3_Mark_in_T_B[OF predRT mkdC] c1mark by simp
    have vne: "transV M \<noteq> \<infinity>" using c1TB c1Dpt by (auto simp: T_B_def)
    have t2df: "dfree_BT (transT2 M)" using c1TB c1Dpt by (auto simp: T_B_def)
    have c1p: "transC1 M = Trm [DB (transV M) (transT2 M)]" using c1Dpt by simp
    have iptc1: "isPTB_str (flatBT (transC1 M))"
    proof -
      have "dfree_BP (DB (transV M) (transT2 M))" using vne t2df by simp
      moreover have "flatBT (transC1 M) = flatBP (DB (transV M) (transT2 M))"
        using c1p by simp
      ultimately show ?thesis unfolding isPTB_str_def by blast
    qed
    have c1ne: "transC1 M \<noteq> Trm []" using c1p by simp
    have "(SOME sb. scb_decomp (transC1 M) (fst sb)
                      (flatBT (transC1 M)) (snd sb)) = ([], [])"
      by (rule scb_SOME_self[OF iptc1 c1ne])
    hence sbself: "sb1 = ([], [])" using c1t1 by (simp add: sb1_def)
    show "fst sb1 = [] \<and> transC1 M = transT1 M \<and> snd sb1 = []"
      using sbself c1t1 by simp
  next
    assume "fst sb1 = [] \<and> transC1 M = transT1 M \<and> snd sb1 = []"
    hence "transC1 M = transT1 M" by simp
    thus "transJm1 M = 0" using core by simp
  qed
qed


section \<open>§7.3 系（\<open>s\<^sub>-\<^sub>1\<close> と \<open>b\<^sub>-\<^sub>1\<close> の空性と基点の関係）— content.md 2470\<close>

text \<open>For a basepoint \<open>(N, m) \<in> Marked\<close> of a reduced mono \<open>N\<close> with the \<open>Trans\<close>
  recursion symbols of the parent \<open>M\<close> (so \<open>N = Pred M\<close>, \<open>c\<^sub>1 = Mark N j\<^sub>-\<^sub>1\<close>,
  \<open>c\<^sub>0 = Mark N m\<close>), the scb-decomposition \<open>s\<^sub>-\<^sub>1 c\<^sub>0 b\<^sub>-\<^sub>1 = c\<^sub>1\<close> (\<open>c\<^sub>0\<close> nested inside
  \<open>c\<^sub>1\<close>, valid for \<open>j\<^sub>-\<^sub>1 \<le> m\<close>) is
  trivial exactly at the basepoint: (1) \<open>m = j\<^sub>-\<^sub>1\<close> \<longleftrightarrow> (2) \<open>s\<^sub>-\<^sub>1 = ()\<close> and
  \<open>b\<^sub>-\<^sub>1 = ()\<close>.  The core is \<open>c\<^sub>0 = c\<^sub>1 \<longleftrightarrow> m = j\<^sub>-\<^sub>1\<close> (\<open>Mark\<close> is injective on
  basepoints, @{thm [source] m_7_4_Mark_order}); given \<open>c\<^sub>0 = c\<^sub>1\<close> the scb-\<open>SOME\<close>
  is the trivial self-decomposition (@{thm [source] scb_SOME_self}).\<close>

lemma m_7_3_sm1_bm1_empty:
  assumes NR: "N \<in> RT_PS"
    and mM: "(N, m) \<in> Marked" and jm1M: "(N, jm1) \<in> Marked"
    and jle: "jm1 \<le> m"
    and c1ne: "Mark N jm1 \<noteq> Trm []"
    and iptc1: "isPTB_str (flatBT (Mark N jm1))"
  defines "sbm1 \<equiv> (SOME sb. scb_decomp (Mark N jm1) (fst sb)
                               (flatBT (Mark N m)) (snd sb))"
  shows "(m = jm1) \<longleftrightarrow> (fst sbm1 = [] \<and> snd sbm1 = [])"
proof -
  \<comment> \<open>core: \<open>Mark N m = Mark N jm1 \<longleftrightarrow> m = jm1\<close> (\<open>Mark\<close> injective on basepoints)\<close>
  have core: "(Mark N m = Mark N jm1) \<longleftrightarrow> (m = jm1)"
  proof
    assume eqc: "Mark N m = Mark N jm1"
    show "m = jm1"
    proof (rule ccontr)
      assume mne: "m \<noteq> jm1"
      hence gt: "jm1 < m" using jle by linarith
      have "Mark N m \<noteq> Mark N jm1"
        using m_7_4_Mark_order[OF NR jm1M mM] gt by simp
      thus False using eqc by simp
    qed
  next
    assume "m = jm1" thus "Mark N m = Mark N jm1" by simp
  qed
  show ?thesis
  proof
    assume "m = jm1"
    hence c0c1: "Mark N m = Mark N jm1" by simp
    have "(SOME sb. scb_decomp (Mark N jm1) (fst sb)
                      (flatBT (Mark N jm1)) (snd sb)) = ([], [])"
      by (rule scb_SOME_self[OF iptc1 c1ne])
    hence "sbm1 = ([], [])" using c0c1 by (simp add: sbm1_def)
    thus "fst sbm1 = [] \<and> snd sbm1 = []" by simp
  next
    assume triv: "fst sbm1 = [] \<and> snd sbm1 = []"
    \<comment> \<open>at \<open>jm1 \<le> m\<close>, \<open>c\<^sub>0 = Mark N m\<close> nests in \<open>c\<^sub>1 = Mark N jm1\<close> (\<open>s\<^sub>-\<^sub>1 c\<^sub>0 b\<^sub>-\<^sub>1 = c\<^sub>1\<close>),
        so a decomposition exists and the \<open>SOME\<close> is real; with trivial \<open>s,b\<close> it
        forces \<open>c\<^sub>0 = c\<^sub>1\<close>\<close>
    have ex: "\<exists>s b. scb_decomp (Mark N jm1) s (flatBT (Mark N m)) b"
    proof (cases "m = jm1")
      case True
      have "scb_decomp (Mark N jm1) [] (flatBT (Mark N jm1)) []"
        by (rule scb_decomp_self[OF iptc1])
      thus ?thesis using True by blast
    next
      case False
      hence gt: "jm1 < m" using jle by linarith
      have "(Mark N jm1, Mark N m) \<in> MarkedB"
        using m_7_4_Mark_order[OF NR jm1M mM] gt by simp
      thus ?thesis by (simp add: MarkedB_def)
    qed
    obtain s b where "scb_decomp (Mark N jm1) s (flatBT (Mark N m)) b" using ex by blast
    hence dec: "scb_decomp (Mark N jm1) (fst sbm1) (flatBT (Mark N m)) (snd sbm1)"
      unfolding sbm1_def
      by (rule someI[where P="\<lambda>sb. scb_decomp (Mark N jm1) (fst sb)
                                     (flatBT (Mark N m)) (snd sb)"
                     and x="(s,b)", simplified])
    \<comment> \<open>with trivial \<open>s,b\<close> the matched string equals \<open>c\<^sub>1\<close>: \<open>flatBT c\<^sub>1 = flatBT c\<^sub>0\<close>\<close>
    have "flatBT (Mark N jm1) = flatBT (Mark N m)"
      using dec triv by (simp add: scb_decomp_def)
    hence "Mark N jm1 = Mark N m" by (rule m_7_flatBT_inj)
    thus "m = jm1" using core by simp
  qed
qed

end
