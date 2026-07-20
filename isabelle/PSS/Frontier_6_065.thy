theory Frontier_6_065
  imports Support_6_044
begin

text \<open>The backward rebase \<open>N'\<close> of content.md 1224.  For a next-tie slice
  \<open>seg M j'\<^sub>0 j'\<^sub>1\<close>, \<open>N'\<^bsub>j\<^esub> := (M\<^bsub>0,j'\<^sub>0+j\<^esub> - M\<^bsub>0,j'\<^sub>0\<^esub> + M\<^bsub>1,j'\<^sub>0\<^esub>, M\<^bsub>1,j'\<^sub>0+j\<^esub>)\<close>
  (local index \<open>j = 0 .. j'\<^sub>1-j'\<^sub>0\<close>).  It shifts row-0 down by \<open>M\<^bsub>0,j'\<^sub>0\<^esub>-M\<^bsub>1,j'\<^sub>0\<^esub>\<close>
  (well-defined in \<open>\<nat>\<^sup>2\<close> by condAB_coeff (2): \<open>M\<^bsub>1,j'\<^sub>0\<^esub>\<le>M\<^bsub>0,j'\<^sub>0\<^esub>\<close>).\<close>

definition rebaseNp :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> pairseq" where
  "rebaseNp M j0' j1' =
     map (\<lambda>j. (entry M 0 (j0' + j) - entry M 0 j0' + entry M 1 j0',
               entry M 1 (j0' + j))) [0 ..< Suc (j1' - j0')]"

lemma Lng_rebaseNp[simp]: "Lng (rebaseNp M j0' j1') = Suc (j1' - j0')"
  by (simp add: rebaseNp_def)

lemma rebaseNp_nth:
  assumes "j < Suc (j1' - j0')"
  shows "rebaseNp M j0' j1' ! j
           = (entry M 0 (j0' + j) - entry M 0 j0' + entry M 1 j0',
              entry M 1 (j0' + j))"
proof -
  have lt: "j < length [0 ..< Suc (j1' - j0')]" using assms by simp
  have uj: "[0 ..< Suc (j1' - j0')] ! j = j"
    using assms by (simp add: nth_upt del: upt_Suc)
  show ?thesis
    unfolding rebaseNp_def
    by (simp add: nth_map[OF lt] uj del: upt_Suc)
qed

lemma entry_rebaseNp:
  assumes "j < Suc (j1' - j0')"
  shows "entry (rebaseNp M j0' j1') 0 j
           = entry M 0 (j0' + j) - entry M 0 j0' + entry M 1 j0'"
    and "entry (rebaseNp M j0' j1') 1 j = entry M 1 (j0' + j)"
proof -
  have nthj: "rebaseNp M j0' j1' ! j
                = (entry M 0 (j0' + j) - entry M 0 j0' + entry M 1 j0',
                   entry M 1 (j0' + j))"
    by (rule rebaseNp_nth[OF assms])
  have "entry (rebaseNp M j0' j1') 0 j = fst (rebaseNp M j0' j1' ! j)"
    by (simp add: entry_def)
  thus "entry (rebaseNp M j0' j1') 0 j
          = entry M 0 (j0' + j) - entry M 0 j0' + entry M 1 j0'"
    by (simp add: nthj)
  have "entry (rebaseNp M j0' j1') 1 j = snd (rebaseNp M j0' j1' ! j)"
    by (simp add: entry_def)
  thus "entry (rebaseNp M j0' j1') 1 j = entry M 1 (j0' + j)"
    by (simp add: nthj)
qed

text \<open>The diagonal prefix \<open>((j,j))\<^bsub>j=0\<^esub>\<^bsup>m-1\<^esup>\<close> of length \<open>m\<close>, encoded so that
  \<open>m = 0\<close> gives the empty list (article's empty range, NOT \<open>diagSeq 0 (m-1)\<close>
  which is \<open>[(0,0)]\<close> at \<open>m=0\<close> under nat subtraction).\<close>

definition diagPre :: "nat \<Rightarrow> pairseq" where
  "diagPre m = map (\<lambda>j. (j, j)) [0 ..< m]"

lemma Lng_diagPre[simp]: "Lng (diagPre m) = m"
  by (simp add: diagPre_def)

lemma diagPre_nth: "k < m \<Longrightarrow> diagPre m ! k = (k, k)"
  by (simp add: diagPre_def)

lemma entry_diagPre: "k < m \<Longrightarrow> entry (diagPre m) i k = k"
  by (simp add: diagPre_nth entry_def)

text \<open>The backward induction column \<open>N := ((j,j))\<^bsub>j=0\<^esub>\<^bsup>M\<^bsub>1,j'\<^sub>0\<^esub>-1\<^esup> \<oplus> N'\<close>
  (content.md 1226).  Its length is \<open>j'\<^sub>1 - j'\<^sub>0 + M\<^bsub>1,j'\<^sub>0\<^esub> + 1\<close>
  (content.md 1228).  Uses \<open>diagPre\<close> so the prefix is empty when \<open>M\<^bsub>1,j'\<^sub>0\<^esub>=0\<close>.\<close>

definition bwdN :: "pairseq \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> pairseq" where
  "bwdN M j0' j1' = diagPre (entry M 1 j0') @ rebaseNp M j0' j1'"

lemma Lng_bwdN: "Lng (bwdN M j0' j1') = entry M 1 j0' + Suc (j1' - j0')"
  by (simp add: bwdN_def)

lemma Lng_bwdN_zero:
  assumes "entry M 1 j0' = 0"
  shows "bwdN M j0' j1' = rebaseNp M j0' j1'"
proof -
  have "diagPre (entry M 1 j0') = diagPre 0" using assms by simp
  also have "\<dots> = []" by (simp add: diagPre_def)
  finally show ?thesis by (simp add: bwdN_def)
qed

text \<open>Entry transfer for the backward column \<open>N\<close>.  On the diagonal prefix
  (\<open>k < M\<^bsub>1,j'\<^sub>0\<^esub>\<close>): \<open>N\<^bsub>i,k\<^esub> = k\<close>.  On the rebase part (\<open>k \<ge> M\<^bsub>1,j'\<^sub>0\<^esub>\<close>):
  \<open>N\<^bsub>i,k\<^esub> = N'\<^bsub>i,k-M\<^bsub>1,j'\<^sub>0\<^esub>\<^esub>\<close>.\<close>

lemma entry_bwdN_diag:
  assumes "k < entry M 1 j0'"
  shows "entry (bwdN M j0' j1') i k = k"
proof -
  have lp: "k < Lng (diagPre (entry M 1 j0'))" using assms by simp
  have "entry (bwdN M j0' j1') i k = entry (diagPre (entry M 1 j0')) i k"
    using lp by (simp add: bwdN_def entry_def nth_append)
  thus ?thesis using entry_diagPre[OF assms] by simp
qed

lemma entry_bwdN_rebase:
  assumes "entry M 1 j0' \<le> k"
  shows "entry (bwdN M j0' j1') i k = entry (rebaseNp M j0' j1') i (k - entry M 1 j0')"
proof -
  have ge: "\<not> k < Lng (diagPre (entry M 1 j0'))" using assms by simp
  show ?thesis
    using ge by (simp add: bwdN_def entry_def nth_append)
qed

text \<open>Left end of the backward column is \<open>(0,0)\<close> (content.md 1230).\<close>

lemma bwdN_left_end:
  shows "entry (bwdN M j0' j1') 0 0 = 0 \<and> entry (bwdN M j0' j1') 1 0 = 0"
proof (cases "entry M 1 j0' = 0")
  case True
  have e0: "entry (bwdN M j0' j1') 0 0 = entry (rebaseNp M j0' j1') 0 0"
    using True by (simp add: entry_bwdN_rebase)
  have e1: "entry (bwdN M j0' j1') 1 0 = entry (rebaseNp M j0' j1') 1 0"
    using True by (simp add: entry_bwdN_rebase)
  have lt: "(0::nat) < Suc (j1' - j0')" by simp
  have r0: "entry (rebaseNp M j0' j1') 0 0
              = entry M 0 (j0' + 0) - entry M 0 j0' + entry M 1 j0'"
    by (rule entry_rebaseNp(1)[OF lt])
  have r1: "entry (rebaseNp M j0' j1') 1 0 = entry M 1 (j0' + 0)"
    by (rule entry_rebaseNp(2)[OF lt])
  show ?thesis using e0 e1 r0 r1 True by simp
next
  case False
  hence pos: "0 < entry M 1 j0'" by simp
  have e0: "entry (bwdN M j0' j1') 0 0 = 0" by (rule entry_bwdN_diag[OF pos])
  have e1: "entry (bwdN M j0' j1') 1 0 = 0" by (rule entry_bwdN_diag[OF pos])
  show ?thesis using e0 e1 by simp
qed

end
