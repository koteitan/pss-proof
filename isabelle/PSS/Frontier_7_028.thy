theory Frontier_7_028
  imports Support_7_023
begin

text \<open>\<open>RightNodes\<close> of a term is empty iff the term is \<open>0\<close>: a non-empty principal
  list has a \<open>DB\<close>-headed last component, contributing a head node.\<close>

lemma rnsub_RightNodes_empty_iff: "RightNodes t = [] \<longleftrightarrow> t = 0\<^sub>B"
proof
  assume h: "RightNodes t = []"
  obtain xs where t: "t = Trm xs" by (cases t)
  show "t = 0\<^sub>B"
  proof (cases xs)
    case Nil thus ?thesis using t by simp
  next
    case (Cons a as)
    hence ne: "xs \<noteq> []" by simp
    obtain u b where lb: "last xs = DB u b" by (cases "last xs") auto
    have "RightNodes (Trm xs) = RightNodes (Trm [last xs])"
      using ne by (rule rnsub_RightNodes_last)
    also have "\<dots> = the_enat u # RightNodes b" by (simp add: lb)
    finally have "RightNodes (Trm xs) = the_enat u # RightNodes b" .
    hence False using h t by simp
    thus ?thesis ..
  qed
next
  assume "t = 0\<^sub>B" thus "RightNodes t = []" by simp
qed

end
