theory Frontier_7_009
  imports P_7_2_RightNodes_subexpr
begin

(* ===== block from workflow t2-scbuniq ===== *)

subsection \<open>§7.2 scb分解の一意性 (1) — the \<open>(s,b)\<close>-part is unique for fixed \<open>c\<close>\<close>

text \<open>
  Discharges the first conjunct of @{text p_7_2_scb_unique}: if both
  \<open>(s\<^sub>0, c, b\<^sub>0)\<close> and \<open>(s\<^sub>1, c, b\<^sub>1)\<close> are scb-decompositions of the same \<open>t\<close>
  (i.e. \<open>flat t = s\<^sub>i \<frown> c \<frown> b\<^sub>i\<close> with \<open>b\<^sub>i\<close> all \<open>\<^bold>)\<close> and \<open>c\<close> a principal string),
  then \<open>s\<^sub>0 = s\<^sub>1\<close> and \<open>b\<^sub>0 = b\<^sub>1\<close>.

  Article argument (content.md 1872): "(1) は \<open>c\<close> が単項であり単項は \<open>\<^bold>)\<close> 以外の
  文字を含むことから即座に従う" — \<open>c\<close> is a principal term string, which contains a
  letter other than \<open>\<^bold>)\<close>, while \<open>b\<^sub>0, b\<^sub>1\<close> consist only of \<open>\<^bold>)\<close>.

  Mechanization.  Measure the length of the maximal trailing run of \<open>RP\<close> via
  \<open>trailRP xs = length (takeWhile ((=) RP) (rev xs))\<close>.  Appending an all-\<open>RP\<close>
  block \<open>b\<close> adds exactly \<open>length b\<close> to it, and — because \<open>c\<close> contains a non-\<open>RP\<close>
  letter — \<open>trailRP (s \<frown> c)\<close> does not depend on \<open>s\<close> (it equals \<open>trailRP c\<close>).
  Hence \<open>trailRP (flat t) = length b\<^sub>i + trailRP c\<close> for both \<open>i\<close>, forcing
  \<open>length b\<^sub>0 = length b\<^sub>1\<close>; both being all-\<open>RP\<close> of equal length gives \<open>b\<^sub>0 = b\<^sub>1\<close>,
  and a total-length count then gives \<open>s\<^sub>0 = s\<^sub>1\<close>.
\<close>

definition trailRP :: "Sym list \<Rightarrow> nat" where
  "trailRP xs = length (takeWhile ((=) RP) (rev xs))"

\<comment> \<open>A principal-term string starts with a \<open>Dsym\<close>, hence contains a non-\<open>RP\<close> letter.\<close>
lemma scbuniq_isPTB_has_nonRP:
  assumes "isPTB_str c"
  shows "\<exists>x \<in> set c. x \<noteq> RP"
proof -
  from assms obtain p where p: "c = flatBP p" unfolding isPTB_str_def by blast
  obtain u a where "p = DB u a" by (cases p)
  hence "c = Dsym u # flatBT a" using p by simp
  thus ?thesis by auto
qed

\<comment> \<open>Appending an all-\<open>RP\<close> block adds exactly its length to the trailing-\<open>RP\<close> run.\<close>
lemma scbuniq_trailRP_append_RP:
  assumes "\<forall>x \<in> set b. x = RP"
  shows "trailRP (xs @ b) = length b + trailRP xs"
proof -
  have allP: "\<forall>y \<in> set (rev b). ((=) RP) y" using assms by auto
  have "trailRP (xs @ b) = length (takeWhile ((=) RP) (rev b @ rev xs))"
    by (simp add: trailRP_def)
  also have "takeWhile ((=) RP) (rev b @ rev xs) = rev b @ takeWhile ((=) RP) (rev xs)"
    using allP by (simp add: takeWhile_append)
  finally show ?thesis by (simp add: trailRP_def)
qed

\<comment> \<open>If \<open>c\<close> contains a non-\<open>RP\<close> letter, prefixing \<open>s\<close> does not change \<open>trailRP\<close>.\<close>
lemma scbuniq_trailRP_prefix_indep:
  assumes "\<exists>x \<in> set c. x \<noteq> RP"
  shows "trailRP (s @ c) = trailRP c"
proof -
  from assms obtain x where x: "x \<in> set (rev c)" "\<not> ((=) RP) x" by auto
  have "trailRP (s @ c) = length (takeWhile ((=) RP) (rev c @ rev s))"
    by (simp add: trailRP_def)
  also have "takeWhile ((=) RP) (rev c @ rev s) = takeWhile ((=) RP) (rev c)"
    by (rule takeWhile_append1[where P="(=) RP" and xs="rev c" and ys="rev s", OF x(1) x(2)])
  finally show ?thesis by (simp add: trailRP_def)
qed

\<comment> \<open>Two all-\<open>RP\<close> lists of equal length are equal.\<close>
lemma scbuniq_all_RP_eq:
  assumes "\<forall>x \<in> set b\<^sub>0. x = RP" "\<forall>x \<in> set b\<^sub>1. x = RP" "length b\<^sub>0 = length b\<^sub>1"
  shows "b\<^sub>0 = b\<^sub>1"
proof -
  have "b\<^sub>0 = replicate (length b\<^sub>0) RP" by (metis assms(1) replicate_eqI)
  moreover have "b\<^sub>1 = replicate (length b\<^sub>1) RP" by (metis assms(2) replicate_eqI)
  ultimately show ?thesis using assms(3) by simp
qed

end
