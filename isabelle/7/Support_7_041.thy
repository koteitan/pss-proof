theory Support_7_041
  imports Frontier_7_047
begin

lemma rnNatShape_imp_kindable:
  assumes tTB: "t \<in> T_B" and tne: "t \<noteq> Trm []"
      and shape: "rnNatShape (RightNodes t)"
  shows "scb_kind0_able t \<or> scb_kind1_able t"
proof -
  define R where "R = RightNodes t"
  define j1 where "j1 = length R - 1"
  have len2: "length R \<ge> 2" using shape unfolding rnNatShape_def R_def by simp
  have j1ge1: "j1 \<ge> 1" using len2 unfolding j1_def by simp
  have disj: "R ! j1 = 0 \<or> (\<exists>k < j1. R ! k < R ! j1)"
    using shape unfolding rnNatShape_def R_def j1_def by simp
  from disj show ?thesis
  proof
    assume z: "R ! j1 = 0"
    \<comment> \<open>kind-0: marked principal at depth \<open>j1 - 1\<close>, suffix \<open>[R!(j1-1), R!j1] = [w,0]\<close>\<close>
    have jm1lt: "j1 - 1 < length R" using j1ge1 len2 unfolding j1_def by simp
    obtain p s b where pf: "dfree_BP p"
        and d: "scb_decomp t s (flatBP p) b"
        and rn: "RightNodes (Trm [p]) = drop (j1 - 1) R"
      using scb_suffix_realized[OF tTB tne, of "j1 - 1"] jm1lt
      unfolding R_def by blast
    have dropeq: "drop (j1 - 1) R = [R ! (j1 - 1), R ! j1]"
    proof -
      have e1: "j1 - 1 < length R" using jm1lt .
      have e2: "Suc (j1 - 1) = j1" using j1ge1 by simp
      have e3: "Suc j1 = length R" using len2 unfolding j1_def by simp
      have j1lt: "j1 < length R" using e3 by simp
      have step1: "drop (j1 - 1) R = R ! (j1 - 1) # drop j1 R"
        using e1 e2 Cons_nth_drop_Suc[OF e1] by simp
      have step2: "drop j1 R = R ! j1 # drop (Suc j1) R"
        using Cons_nth_drop_Suc[OF j1lt] by simp
      have step3: "drop (Suc j1) R = []" using e3 by simp
      show ?thesis using step1 step2 step3 by simp
    qed
    have rn2: "RightNodes (Trm [p]) = [R ! (j1 - 1), 0]" using rn dropeq z by simp
    have "scb_kind0 t s (flatBP p) b" by (rule scb_kind0_of_suffix[OF pf d rn2])
    hence "scb_kind0_able t" by blast
    thus ?thesis by blast
  next
    assume "\<exists>k < j1. R ! k < R ! j1"
    then obtain k where klt: "k < j1" and kw: "R ! k < R ! j1" by blast
    \<comment> \<open>kind-1: marked principal at depth \<open>k\<close>; its suffix \<open>r = drop k R\<close> has
       \<open>r!0 = R!k\<close>, \<open>r!(len-1) = R!j1\<close>, and \<open>r!(len-1)\<close> a running min? No — kind1
       does NOT need a running minimum at the chosen \<open>k\<close>; but the literal
       definition quantifies \<open>\<forall>j. 0<j<j1\<^bsup>r\<^esup>. r!j \<ge> r!j1\<^bsup>r\<^esup>\<close>.  This may FAIL for an
       arbitrary \<open>k\<close>.  So pick \<open>k\<close> as the LAST index \<open>< j1\<close> with \<open>R!k < R!j1\<close>;
       then every \<open>k < i < j1\<close> has \<open>R!i \<ge> R!j1\<close>.\<close>
    define k0 where "k0 = Max {k. k < j1 \<and> R ! k < R ! j1}"
    have fin: "finite {k. k < j1 \<and> R ! k < R ! j1}" by simp
    have ne: "{k. k < j1 \<and> R ! k < R ! j1} \<noteq> {}" using klt kw by auto
    have k0mem: "k0 < j1 \<and> R ! k0 < R ! j1"
      using Max_in[OF fin ne] unfolding k0_def by blast
    have k0lt: "k0 < j1" using k0mem by simp
    have k0w: "R ! k0 < R ! j1" using k0mem by simp
    have k0max: "\<forall>i. k0 < i \<and> i < j1 \<longrightarrow> R ! i \<ge> R ! j1"
    proof (intro allI impI)
      fix i assume "k0 < i \<and> i < j1"
      hence ki: "k0 < i" and ij1: "i < j1" by auto
      show "R ! i \<ge> R ! j1"
      proof (rule ccontr)
        assume "\<not> R ! i \<ge> R ! j1"
        hence "R ! i < R ! j1" by simp
        hence "i \<in> {k. k < j1 \<and> R ! k < R ! j1}" using ij1 by simp
        hence "i \<le> k0" using Max_ge[OF fin] unfolding k0_def by simp
        thus False using ki by simp
      qed
    qed
    have k0ltlen: "k0 < length R" using k0lt unfolding j1_def using len2 by simp
    obtain p s b where pf: "dfree_BP p"
        and d: "scb_decomp t s (flatBP p) b"
        and rn: "RightNodes (Trm [p]) = drop k0 R"
      using scb_suffix_realized[OF tTB tne, of k0] k0ltlen
      unfolding R_def by blast
    define r where "r = RightNodes (Trm [p])"
    have rdrop: "r = drop k0 R" using rn r_def by simp
    have lenr: "length r = length R - k0" using rdrop k0ltlen by simp
    have rj1id: "Lng r - 1 = j1 - k0"
      using lenr unfolding j1_def by simp
    have j1rge1: "Lng r - 1 \<ge> 1" using k0lt rj1id by simp
    \<comment> \<open>\<open>r ! 0 = R ! k0\<close>; \<open>r ! (Lng r - 1) = R ! j1\<close>\<close>
    have r0: "r ! 0 = R ! k0" using rdrop k0ltlen by (simp add: nth_drop)
    have rj1: "r ! (Lng r - 1) = R ! j1"
    proof -
      have "Lng r - 1 = j1 - k0" using rj1id .
      have "r ! (j1 - k0) = R ! (k0 + (j1 - k0))"
        using rdrop k0ltlen k0lt unfolding j1_def
        by (simp add: nth_drop)
      moreover have "k0 + (j1 - k0) = j1" using k0lt by simp
      ultimately show ?thesis using rj1id by simp
    qed
    have hd_lt: "r ! 0 < r ! (Lng r - 1)" using r0 rj1 k0w by simp
    \<comment> \<open>running-min on \<open>(0, Lng r - 1)\<close>: \<open>r!j = R!(k0+j) \<ge> R!j1 = r!(Lng r-1)\<close>\<close>
    have runmin: "\<forall>j. 0 < j \<and> j < Lng r - 1 \<longrightarrow> r ! j \<ge> r ! (Lng r - 1)"
    proof (intro allI impI)
      fix jj assume "0 < jj \<and> jj < Lng r - 1"
      hence jjpos: "0 < jj" and jjlt: "jj < Lng r - 1" by auto
      have jjlt': "jj < j1 - k0" using jjlt rj1id by simp
      have idx: "r ! jj = R ! (k0 + jj)"
        using rdrop k0ltlen jjlt' k0lt unfolding j1_def
        by (simp add: nth_drop)
      have lo: "k0 < k0 + jj" using jjpos by simp
      have hi: "k0 + jj < j1" using jjlt' by simp
      have "R ! (k0 + jj) \<ge> R ! j1" using k0max lo hi by simp
      thus "r ! jj \<ge> r ! (Lng r - 1)" using idx rj1 by simp
    qed
    have rcond: "let r = RightNodes (Trm [p]); j1 = Lng r - 1 in
                   j1 \<ge> 1 \<and> r ! 0 < r ! j1 \<and> (\<forall>j. 0 < j \<and> j < j1 \<longrightarrow> r ! j \<ge> r ! j1)"
      using j1rge1 hd_lt runmin unfolding r_def by (simp add: Let_def)
    have "scb_kind1 t s (flatBP p) b" by (rule scb_kind1_of_suffix[OF pf d rcond])
    hence "scb_kind1_able t" by blast
    thus ?thesis by blast
  qed
qed


text \<open>Conjunct (2) of @{text p_7_2_scb_unique}, NOW UNBLOCKED (the
  \<open>domB\<close>-side is reachable via @{thm [source] domB_unfold}/@{thm [source] domB_dom_all}).
  Assembles the \<open>domB\<close>-side equivalence
  @{thm [source] domB_NatSet_iff_rnNatShape} with the two \<open>scb\<close>-side directions:
  \<open>\<Rightarrow>\<close> = @{thm [source] rnNatShape_imp_kindable}, and \<open>\<Leftarrow>\<close> via the GREEN forward
  @{thm [source] rnsub_kindable_imp_natshape} (\<open>Support_7_013\<close>) bridged by
  @{thm [source] rnNatShape_iff_natshape}.  This helper carries
  \<open>t \<noteq> Trm []\<close> as its nonempty-branch premise; A14 is retracted, and the
  article's unconditional zero branch is assembled in @{text p_7_2_scb_unique}.\<close>

lemma m_7_2_scb_unique_domB:
  assumes tTB: "t \<in> T_B" and tne: "t \<noteq> Trm []"
  shows "(domB t = NatSet) \<longleftrightarrow> (scb_kind0_able t \<or> scb_kind1_able t)"
proof
  assume "domB t = NatSet"
  hence shape: "rnNatShape (RightNodes t)"
    using domB_NatSet_iff_rnNatShape[OF tTB tne] by simp
  thus "scb_kind0_able t \<or> scb_kind1_able t"
    by (rule rnNatShape_imp_kindable[OF tTB tne])
next
  assume kab: "scb_kind0_able t \<or> scb_kind1_able t"
  \<comment> \<open>forward (GREEN, Support_7_013): kind-able \<Rightarrow> RightNodes natshape\<close>
  have natshape: "Lng (RightNodes t) - 1 \<ge> 1
        \<and> (RightNodes t ! (Lng (RightNodes t) - 1) = 0
           \<or> (\<exists>k < Lng (RightNodes t) - 1.
                RightNodes t ! k < RightNodes t ! (Lng (RightNodes t) - 1)))"
    by (rule rnsub_kindable_imp_natshape[OF tne kab])
  hence "rnNatShape (RightNodes t)" by (simp add: rnNatShape_iff_natshape)
  thus "domB t = NatSet"
    using domB_NatSet_iff_rnNatShape[OF tTB tne] by simp
qed

end
