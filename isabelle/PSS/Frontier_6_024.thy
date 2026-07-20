theory Frontier_6_024
  imports P_6_5_Red_zeroT
begin

section \<open>§6.7 標準形の階層和による表示\<close>

text \<open>補助補題: \<open>SkT_PS k \<subseteq> ST_PS\<close>  (帰納法 on \<open>k\<close>)\<close>

lemma SkT_PS_subset_ST_PS:
  shows "SkT_PS k \<subseteq> ST_PS"
proof (induction k)
  case 0
  \<comment> \<open>SkT_PS 0 = {diagSeq u v | u ≤ v}. Each element is in ST_PS by the diag rule.\<close>
  show "SkT_PS 0 \<subseteq> ST_PS"
  proof
    fix N assume "N \<in> SkT_PS 0"
    then obtain u v where Nuv: "N = diagSeq u v" and uv: "u \<le> v"
      by auto
    show "N \<in> ST_PS" using uv unfolding Nuv by (rule ST_PS.diag)
  qed
next
  case (Suc k)
  \<comment> \<open>SkT_PS (Suc k) = {M[n] | M ∈ SkT_PS k, 1 ≤ n}.
      By IH M ∈ ST_PS, so M[n] ∈ ST_PS by the oper rule.\<close>
  show "SkT_PS (Suc k) \<subseteq> ST_PS"
  proof
    fix N assume "N \<in> SkT_PS (Suc k)"
    then obtain M n where NMn: "N = (M::pairseq)[n]"
                      and Mk:  "M \<in> SkT_PS k"
                      and n1:  "1 \<le> n"
      by auto
    have MST: "M \<in> ST_PS" using Mk Suc.IH by blast
    show "N \<in> ST_PS" using MST n1 unfolding NMn by (rule ST_PS.oper)
  qed
qed

text \<open>m: 命題（標準形の階層和による表示） — discharges p_6_7_ST_eq_Union_SkT.
  \<open>ST_PS = \<Union>\<^sub>k SkT_PS k\<close>  (§6.7 命題, 標準形の階層和による表示)\<close>

text \<open>補助補題: \<open>ST_PS \<subseteq> \<Union>k. SkT_PS k\<close>  (ST_PS.induct で帰納)\<close>

\<comment> \<open>Introduce a wrapper predicate to avoid the ⋃ IH unfolding problem.\<close>
definition in_some_SkT :: "pairseq \<Rightarrow> bool" where
  "in_some_SkT x \<longleftrightarrow> (\<exists>k. x \<in> SkT_PS k)"

lemma ST_PS_in_some_SkT:
  "x \<in> ST_PS \<Longrightarrow> in_some_SkT x"
proof (induct x rule: ST_PS.induct)
  \<comment> \<open>diag case: diagSeq u v ∈ SkT_PS 0.\<close>
  case (diag u v)
  have "diagSeq u v \<in> SkT_PS 0" using diag by auto
  thus "in_some_SkT (diagSeq u v)" unfolding in_some_SkT_def by blast
next
  \<comment> \<open>oper case: in_some_SkT M (IH) ⟹ in_some_SkT M[n].\<close>
  case (oper M n)
  \<comment> \<open>oper.hyps: (1) M ∈ ST_PS, (2) in_some_SkT M (IH), (3) 1 ≤ n\<close>
  from oper.hyps(2) obtain k where Mk: "M \<in> SkT_PS k"
    unfolding in_some_SkT_def by blast
  have "(M::pairseq)[n] \<in> SkT_PS (Suc k)" using Mk oper.hyps(3) by auto
  thus "in_some_SkT ((M::pairseq)[n])" unfolding in_some_SkT_def by blast
qed

lemma ST_PS_subset_Union_SkT:
  "x \<in> ST_PS \<Longrightarrow> x \<in> (\<Union>k. SkT_PS k)"
  using ST_PS_in_some_SkT unfolding in_some_SkT_def by blast

end
