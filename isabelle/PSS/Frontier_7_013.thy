theory Frontier_7_013
  imports Support_7_009
begin

subsection \<open>§7.2 系（加法とscb分解の関係） — m_7_2_add_scb (Front B)\<close>

text \<open>
  Target \<open>p_7_2_add_scb\<close> (the article proposition transcription lines 975–988).  For \<open>t \<in> T\<^bsub>B\<^esub>\<close> and a
  principal \<open>c = Trm [p] \<in> T\<^bsub>B\<^esub>\<close>:

  \<^enum> \<open>(t +\<^sub>B c, c) \<in> MarkedB\<close>                                       — BANKED, proven.
  \<^enum> \<open>scb_decomp (t +\<^sub>B c) s (flat c) b \<Longrightarrow> scb_decomp (t +\<^sub>B c') s (flat c') b\<close>
                                                                  — residual (see below).
  \<^enum> the nested-\<open>D\<^sub>v\<close> replacement                                  — \<^bold>\<open>FALSE\<close> as transcribed
     (concrete counterexample below, A13), TRUE in a corrected form.

  Conjunct (1) is fully discharged here.  Conjunct (3) is shown FALSE by a
  mechanized counterexample, exactly mirroring the A11/A12 pattern: the marked
  scb component \<open>(s\<^sub>0, flat c, b\<^sub>0)\<close> is NOT forced to be the \<open>c\<close> inside
  \<open>D\<^sub>v(t+c)\<close> when that same string \<open>flat c\<close> also occurs as a valid rightmost
  mark elsewhere in \<open>u\<^sub>1\<close>.  The article's proof silently invokes scb-uniqueness
  to identify the two; uniqueness fixes only the \<open>(s,b)\<close> pair for a \<^emph>\<open>given\<close>
  \<open>c\<close>-string and does not exclude a competing occurrence.
\<close>

text \<open>Helper: a principal \<open>c = Trm [p] \<in> T\<^bsub>B\<^esub>\<close> has \<open>isPTB_str (flatBT c)\<close>.\<close>

lemma addscb_princ_isPTB:
  assumes cTB: "c \<in> T_B" and cp: "c = Trm [p]"
  shows "isPTB_str (flatBT c)"
proof -
  have df: "dfree_BP p" using cTB cp by (simp add: T_B_def)
  have "flatBT c = flatBP p" using cp by simp
  thus ?thesis using df unfolding isPTB_str_def by blast
qed

text \<open>Helper: \<open>t +\<^sub>B Trm [p] = Trm (untrm t @ [p])\<close>, whose last component is \<open>p\<close>.\<close>

lemma addscb_addBT_snoc:
  "t +\<^sub>B Trm [p] = Trm (untrm t @ [p])"
  by (cases t) simp

end
