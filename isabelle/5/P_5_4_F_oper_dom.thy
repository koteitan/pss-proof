theory P_5_4_F_oper_dom
  imports Pre_5
begin

subsection \<open>§5.4 ペア数列システム\<close>

text \<open>
  命題（\<open>F\<^sub>M\<close>と基本列の関係） — relation between \<open>F\<^sub>M\<close> and the fundamental
  sequence.  The article states the equivalence of: (1) \<open>(M,n) \<in> Dom F\<close>;
  (2) \<open>(M[n],n) \<in> Dom F\<close>; (3) both, together with \<open>F\<^sub>M(n) = F\<^bsub>M[n]\<^esub>(n)\<close>.

  CORRECTED form (see @{file "../../corrections.md"} entry A1): the article's second
  argument \<open>n\<close> is an apparent typo for \<open>f n\<close>, and the substantive content is
  the case \<open>Lng M > 1\<close> (for \<open>Lng M = 1\<close> the relation is trivial since
  \<open>M[n] = M\<close>).
\<close>
section \<open>§5.4 ペア数列システム\<close>

lemma p_5_4_F_oper_dom:
  assumes "M \<in> T_PS" "n \<ge> 1" "Lng M > 1"
  shows "Fdom f M n \<longleftrightarrow> Fdom f (M[n]) (f n)"
proof
  assume h: "Fdom f M n"
  show "Fdom f (M[n]) (f n)" using h
  proof (cases rule: Fdom.cases)
    case Fdom_base
    with assms(3) show ?thesis by simp
  next
    case Fdom_step
    then show ?thesis by blast
  qed
next
  assume "Fdom f (M[n]) (f n)"
  with assms(3) show "Fdom f M n" by (rule Fdom.Fdom_step)
qed

text \<open>
  m: 命題（F_M と基本列の関係）— corrected form (see @{file "../../corrections.md"} A1).
  Discharges @{thm [source] p_5_4_F_oper_dom}.  Immediate from the inductive
  definition of @{const Fdom}: with \<open>Lng M > 1\<close> only @{thm [source] Fdom.Fdom_step}
  applies.
\<close>

lemma m_5_4_F_oper_dom:
  assumes "M \<in> T_PS" "n \<ge> 1" "Lng M > 1"
  shows "Fdom f M n \<longleftrightarrow> Fdom f (M[n]) (f n)"
proof
  assume h: "Fdom f M n"
  show "Fdom f (M[n]) (f n)" using h
  proof (cases rule: Fdom.cases)
    case Fdom_base
    with assms(3) show ?thesis by simp
  next
    case Fdom_step
    then show ?thesis by blast
  qed
next
  assume "Fdom f (M[n]) (f n)"
  with assms(3) show "Fdom f M n" by (rule Fdom.Fdom_step)
qed

end
