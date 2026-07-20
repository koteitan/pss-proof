theory Support_7_040
  imports Frontier_7_046
begin

text \<open>Bridge: the \<open>RightNodes\<close>-shape used in @{thm [source] rnNatShape_def} agrees
  with the \<open>scb\<close>-side shape of @{thm [source] rnsub_kindable_imp_natshape}
  (\<open>Lng R - 1 \<ge> 1\<close> i.e. \<open>length R \<ge> 2\<close>; and the \<open>R!j\<^sub>1 = 0 \<or> \<exists>k<j\<^sub>1. \<dots>\<close> disjunct).\<close>

lemma rnNatShape_iff_natshape:
  "rnNatShape R \<longleftrightarrow>
     (Lng R - 1 \<ge> 1
      \<and> (R ! (Lng R - 1) = 0
         \<or> (\<exists>k < Lng R - 1. R ! k < R ! (Lng R - 1))))"
  unfolding rnNatShape_def
  by (cases "length R") auto

text \<open>The \<open>domB t = NatSet \<Rightarrow> shape\<close> and \<open>shape \<Rightarrow> domB t = NatSet\<close> halves, packaged.\<close>

lemma domB_NatSet_iff_rnNatShape:
  assumes "t \<in> T_B" "t \<noteq> Trm []"
  shows "domB t = NatSet \<longleftrightarrow> rnNatShape (RightNodes t)"
proof
  assume "domB t = NatSet"
  \<comment> \<open>if NOT shape, the classification gives \<open>{Trm []}\<close> or \<open>TBv\<close>, both \<noteq> NatSet\<close>
  show "rnNatShape (RightNodes t)"
  proof (rule ccontr)
    assume ns: "\<not> rnNatShape (RightNodes t)"
    have cl: "(\<not> rnNatShape (RightNodes t) \<and> last (RightNodes t) = 0
                \<longrightarrow> domB t = {Trm []})
            \<and> (\<not> rnNatShape (RightNodes t) \<and> last (RightNodes t) \<noteq> 0
                \<longrightarrow> domB t = TBv (enat (last (RightNodes t) - 1)))"
      using domB_classify_RN[OF assms] by simp
    show False
    proof (cases "last (RightNodes t) = 0")
      case True
      hence "domB t = {Trm []}" using cl ns by simp
      thus False using \<open>domB t = NatSet\<close> NatSet_neq_zero by simp
    next
      case False
      hence "domB t = TBv (enat (last (RightNodes t) - 1))" using cl ns by simp
      thus False using \<open>domB t = NatSet\<close> NatSet_neq_TBv by simp
    qed
  qed
next
  assume "rnNatShape (RightNodes t)"
  thus "domB t = NatSet" using domB_classify_RN[OF assms] by simp
qed

text \<open>The \<open>scb\<close>-side converse \<open>shape \<Rightarrow> scb_kind0_able \<or> scb_kind1_able\<close> for a
  nonempty \<open>t \<in> T\<^bsub>B\<^esub>\<close>.  From \<open>rnNatShape (RightNodes t)\<close> we obtain a marked
  right-spine principal whose own \<open>RightNodes\<close> is a length-\<open>(j+1)\<close> suffix of
  \<open>R = RightNodes t\<close> realizing a kind-0 (last \<open>= 0\<close>) or kind-1 (some earlier \<open><\<close>
  last) decomposition.  The right-spine principals' \<open>RightNodes\<close> are exactly the
  \<open>drop\<close>-suffixes of \<open>R\<close>, materialized below by an scb-decomposition.\<close>

\<comment> \<open>Constructive converse engine: every right-spine descent depth \<open>j\<close> of a
   nonempty \<open>t \<in> T\<^bsub>B\<^esub>\<close> is realized by an scb-decomposition whose marked
   principal \<open>Trm [p]\<close> has \<open>RightNodes (Trm [p]) = drop j (RightNodes t)\<close>.
   Base \<open>j = 0\<close>: the last component (via @{thm [source] scb_from_last_component}).
   Step: descend into the body \<open>a\<close> of the last principal, lift back by prefixing
   \<open>Dsym u\<close> to the surgery prefix.\<close>
lemma scb_suffix_realized:
  "\<And>j. t \<in> T_B \<Longrightarrow> t \<noteq> Trm [] \<Longrightarrow> j < length (RightNodes t) \<Longrightarrow>
       \<exists>p s b. dfree_BP p
             \<and> scb_decomp t s (flatBP p) b
             \<and> RightNodes (Trm [p]) = drop j (RightNodes t)"
proof (induction t rule: measure_induct_rule[where f=size])
  case (less t j)
  obtain ys where ys: "t = Trm ys" by (cases t)
  have ysne: "ys \<noteq> []" using less.prems(2) ys by auto
  obtain u a where lastp: "last ys = DB u a"
    by (cases "last ys")
  have RNlast: "RightNodes t = the_enat u # RightNodes a"
    unfolding ys using rnsub_RightNodes_last[OF ysne] lastp by simp
  have ufin: "u \<noteq> \<infinity>" and aTB: "a \<in> T_B"
    using rnsub_TB_last[OF _ ysne lastp] less.prems(1) ys by auto
  have dfree_last: "dfree_BP (DB u a)"
    using ufin aTB by (simp add: T_B_def)
  show ?case
  proof (cases j)
    case 0
    \<comment> \<open>marked principal = last component \<open>DB u a\<close>; surgery at component level\<close>
    have comp: "flatBP (last (untrm t)) = [] @ flatBP (DB u a) @ []"
      using ys lastp by simp
    have rb: "\<forall>x \<in> set ([]::Sym list). x = RP" by simp
    have wne: "untrm t \<noteq> []" using ys ysne by simp
    obtain s' b' where d: "scb_decomp t s' (flatBT (Trm [DB u a])) b'"
      using scb_from_last_component[OF comp rb wne dfree_last] by blast
    have dd: "scb_decomp t s' (flatBP (DB u a)) b'" using d by simp
    have rn: "RightNodes (Trm [DB u a]) = drop j (RightNodes t)"
      using RNlast 0 by simp
    show ?thesis using dfree_last dd rn by blast
  next
    case (Suc j0)
    \<comment> \<open>descend into the body \<open>a\<close> at depth \<open>j0\<close>\<close>
    have szlt: "size a < size t"
      using rnsub_size_arg_lt'[OF lastp ysne] ys by simp
    have ane: "a \<noteq> Trm []"
    proof
      assume z: "a = Trm []"
      have "RightNodes a = []" using z by simp
      hence "length (RightNodes t) = 1" using RNlast by simp
      thus False using less.prems(3) Suc by simp
    qed
    have j0lt: "j0 < length (RightNodes a)"
      using less.prems(3) Suc RNlast by simp
    obtain p s' b' where pf: "dfree_BP p"
        and da: "scb_decomp a s' (flatBP p) b'"
        and rna: "RightNodes (Trm [p]) = drop j0 (RightNodes a)"
      using less.IH[OF szlt aTB ane j0lt] by blast
    \<comment> \<open>lift the occurrence in \<open>a\<close> back to the last component of \<open>t\<close>\<close>
    from da have occa: "flatBT a = s' @ flatBP p @ b'"
      and bRP: "\<forall>x \<in> set b'. x = RP"
      by (auto simp: scb_decomp_def)
    have comp: "flatBP (last (untrm t)) = (Dsym u # s') @ flatBP p @ b'"
      using ys lastp occa by simp
    have wne: "untrm t \<noteq> []" using ys ysne by simp
    obtain s'' b'' where d: "scb_decomp t s'' (flatBT (Trm [p])) b''"
      using scb_from_last_component[OF comp bRP wne pf] by blast
    have dd: "scb_decomp t s'' (flatBP p) b''" using d by simp
    have rn: "RightNodes (Trm [p]) = drop j (RightNodes t)"
      using rna RNlast Suc by simp
    show ?thesis using pf dd rn by blast
  qed
qed

text \<open>The \<open>scb\<close>-side converse \<open>shape \<Rightarrow> scb_kind0_able \<or> scb_kind1_able\<close> for a
  nonempty \<open>t \<in> T\<^bsub>B\<^esub>\<close>.  Choose the marked-principal depth as the witness index of
  @{thm [source] rnNatShape_def}: for the \<open>R!j\<^sub>1 = 0\<close> disjunct take the principal
  at depth \<open>j\<^sub>1 - 1\<close> (its \<^const>\<open>RightNodes\<close> is the length-2 suffix \<open>[R!(j\<^sub>1-1), 0]\<close>,
  giving \<^const>\<open>scb_kind0\<close>); for the \<open>R!k < R!j\<^sub>1\<close> disjunct take depth \<open>k\<close>.\<close>

\<comment> \<open>kind-0 helper: a principal whose \<^const>\<open>RightNodes\<close> is a length-2 suffix
   \<open>[w, 0]\<close> realizes \<^const>\<open>scb_kind0\<close>.\<close>
lemma scb_kind0_of_suffix:
  assumes pf: "dfree_BP p"
      and d: "scb_decomp t s (flatBP p) b"
      and rn: "RightNodes (Trm [p]) = [w, 0]"
  shows "scb_kind0 t s (flatBP p) b"
  unfolding scb_kind0_def
proof (intro conjI)
  show "scb_decomp t s (flatBP p) b" by (rule d)
next
  show "isPTB_str (flatBP p)"
    using pf unfolding isPTB_str_def by blast
next
  show "\<forall>q. flatBP p = flatBP q \<longrightarrow>
          (Lng (RightNodes (Trm [q])) = 2 \<and> RightNodes (Trm [q]) ! 1 = 0)"
  proof (intro allI impI)
    fix q assume cq: "flatBP p = flatBP q"
    have "flatBT (Trm [p]) = flatBT (Trm [q])" using cq by simp
    hence "Trm [p] = Trm [q]" by (rule m_7_flatBT_inj)
    hence "RightNodes (Trm [q]) = [w, 0]" using rn by simp
    thus "Lng (RightNodes (Trm [q])) = 2 \<and> RightNodes (Trm [q]) ! 1 = 0" by simp
  qed
qed

end
