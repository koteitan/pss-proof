theory Frontier_7_047
  imports Support_7_040
begin

\<comment> \<open>kind-1 helper: a principal whose \<^const>\<open>RightNodes\<close> suffix \<open>r\<close> has \<open>j\<^sub>1 \<ge> 1\<close>,
   \<open>r!0 < r!j\<^sub>1\<close> and \<open>r!j\<^sub>1\<close> a running minimum on \<open>(0, j\<^sub>1)\<close> realizes \<^const>\<open>scb_kind1\<close>.\<close>
lemma scb_kind1_of_suffix:
  assumes pf: "dfree_BP p"
      and d: "scb_decomp t s (flatBP p) b"
      and rn: "let r = RightNodes (Trm [p]); j1 = Lng r - 1 in
                 j1 \<ge> 1 \<and> r ! 0 < r ! j1 \<and> (\<forall>j. 0 < j \<and> j < j1 \<longrightarrow> r ! j \<ge> r ! j1)"
  shows "scb_kind1 t s (flatBP p) b"
  unfolding scb_kind1_def
proof (intro conjI)
  show "scb_decomp t s (flatBP p) b" by (rule d)
next
  show "isPTB_str (flatBP p)"
    using pf unfolding isPTB_str_def by blast
next
  show "\<forall>q. flatBP p = flatBP q \<longrightarrow>
          (let r = RightNodes (Trm [q]); j1 = Lng r - 1 in
             j1 \<ge> 1 \<and> r ! 0 < r ! j1 \<and> (\<forall>j. 0 < j \<and> j < j1 \<longrightarrow> r ! j \<ge> r ! j1))"
  proof (intro allI impI)
    fix q assume cq: "flatBP p = flatBP q"
    have "flatBT (Trm [p]) = flatBT (Trm [q])" using cq by simp
    hence "Trm [p] = Trm [q]" by (rule m_7_flatBT_inj)
    hence "RightNodes (Trm [q]) = RightNodes (Trm [p])" by simp
    thus "let r = RightNodes (Trm [q]); j1 = Lng r - 1 in
            j1 \<ge> 1 \<and> r ! 0 < r ! j1 \<and> (\<forall>j. 0 < j \<and> j < j1 \<longrightarrow> r ! j \<ge> r ! j1)"
      using rn by (simp add: Let_def)
  qed
qed

end
