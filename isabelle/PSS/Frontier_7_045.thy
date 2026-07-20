theory Frontier_7_045
  imports P_7_3_Trans_monoT
begin

section \<open>§7.1 [Buc1] dom/oper domain predicate — \<open>domB\<close> is total\<close>

text \<open>The \<open>domB\<close> branch of the mutual recursion (\<open>Inl a\<close>) only recurses into
  structurally smaller \<^typ>\<open>BT\<close> arguments (\<open>x2\<close> inside \<open>D\<^sub>v x2\<close>; the head
  component \<open>Trm [x21a]\<close>; \<open>Trm [last x22a]\<close>).  Hence \<open>domB_operB_xseq_dom (Inl a)\<close>
  holds for \<^emph>\<open>every\<close> \<open>a\<close>, by induction on \<open>size a\<close>: \<open>domB\<close> is total
  (unconditionally — no \<open>[]\<close>-freeness needed; the deferred [Buc1] Lemma 3.2 is
  only needed for \<open>operB\<close>/\<open>xseq\<close>).\<close>

lemma domB_dom_all: "domB_operB_xseq_dom (Inl a)"
proof (induction a rule: measure_induct_rule[where f=size])
  case (less a)
  show ?case
  proof (rule domB_operB_xseq.domintros(1))
    \<comment> \<open>(1) recurse into the principal argument \<open>x2\<close> of \<open>D\<^sub>x1 x2\<close>\<close>
    fix x1 x2 assume "a = Dpt x1 x2" "x2 \<noteq> 0\<^sub>B"
    hence "size x2 < size a" by simp
    thus "domB_operB_xseq_dom (Inl x2)" by (rule less.IH)
  next
    \<comment> \<open>(2) two-component \<open>Trm [DB x1 x2, x21a]\<close>: recurse into \<open>Trm [x21a]\<close>\<close>
    fix x1 x2 x21a assume "a = Trm [DB x1 x2, x21a]"
    hence "size (Trm [x21a] :: BT) < size a" by simp
    thus "domB_operB_xseq_dom (Inl (Trm [x21a]))" by (rule less.IH)
  next
    \<comment> \<open>(3) \<open>(\<ge>3)\<close>-component term: recurse into \<open>Trm [last x22a]\<close>\<close>
    fix x1 x2 x21a x22a
    assume aeq: "a = Trm (DB x1 x2 # x21a # x22a)" and ne: "x22a \<noteq> []"
    have "last x22a \<in> set x22a" using ne by simp
    hence "size (last x22a) \<le> size_list size x22a"
      by (induction x22a) auto
    hence "size (Trm [last x22a] :: BT) < size a"
      using aeq ne by (cases x22a) auto
    thus "domB_operB_xseq_dom (Inl (Trm [last x22a]))" by (rule less.IH)
  qed
qed

text \<open>Hence the conditional simp rule \<open>domB.psimps\<close> fires unconditionally for any
  argument: \<open>domB\<close> may be unfolded freely.\<close>

lemma domB_unfold:
  "domB a =
     (case a of Trm xs \<Rightarrow> (case xs of
        [] \<Rightarrow> {}
      | [DB v b] \<Rightarrow>
          (if b = Trm [] then
             (if v = 0 then {Trm []}
              else if v = \<infinity> then NatSet
              else TBv (enat (the_enat v - 1)))
           else
             (let db = domB b in
              if db = {Trm []} then NatSet
              else if (\<exists>u. v \<le> enat u \<and> db = TBv (enat u)) then NatSet
              else db))
      | (p # q # rest) \<Rightarrow> domB (Trm [last (p # q # rest)])))"
  by (rule domB.psimps[OF domB_dom_all])

end
