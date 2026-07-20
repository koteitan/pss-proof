theory Support_7_039
  imports Frontier_7_045
begin

section \<open>§7.2 系（加法とscb分解の関係） (3) — corrected with the alignment premise (A13)\<close>

text \<open>
  A13.  The literal conjunct (3) of \<open>p_7_2_add_scb\<close> is FALSE
  (counterexample @{thm [source] m_7_2_add_scb_conj3_counterexample}): the
  occurrence of \<open>D\<^sub>v(t+c)\<close> pinned by \<open>flatBT u\<^sub>1 = s\<^sub>1 @ (D\<^sub>v # flatBT (t+c)) @ b\<^sub>1\<close>
  and the occurrence of \<open>c\<close> pinned by \<open>scb_decomp u\<^sub>1 s\<^sub>0 (flatBT c) b\<^sub>0\<close> need NOT
  be the same subterm of \<open>u\<^sub>1\<close>.

  CORRECTED form (corrections.md A13 訂正案): add the \<^bold>\<open>alignment\<close> premise that
  the marked \<open>c\<close> (occ.2) IS the trailing principal of the \<open>t+c\<close> block (occ.1).
  Concretely, with the canonical trailing-principal split
  \<open>flatBT (t+c) = pre @ flatBT c @ post\<close> (the \<open>pre\<close>/\<open>post\<close> depend only on
  \<open>untrm t\<close>, by @{thm [source] addscb_flat_pre_post2}), the alignment is
  \<open>s\<^sub>0 = s\<^sub>1 @ (D\<^sub>v # pre)\<close> and \<open>b\<^sub>0 = post @ b\<^sub>1\<close>.  This is exactly the A13
  condition "\<open>s\<^sub>0 = s\<^sub>1 @ D\<^sub>v (flat-prefix-of t+c before c)\<close>" (it specialises to
  \<open>s\<^sub>0 = s\<^sub>1 @ D\<^sub>v (flatBT t)\<close> when \<open>t = c\<close> is single-principal, \<open>pre = []\<close>; in
  general the trailing principal carries the bracket \<open>pre\<close>/\<open>post\<close>).

  Under the alignment, the two flat strings required of the witness \<open>u\<^sub>1'\<close>
  coincide (\<open>s\<^sub>1 @ (D\<^sub>v # flatBT (t+c')) @ b\<^sub>1 = s\<^sub>0 @ flatBT c' @ b\<^sub>0\<close>, using the
  \<^bold>\<open>same\<close> \<open>pre\<close>/\<open>post\<close> for \<open>c'\<close>), so a single \<open>u\<^sub>1'\<close> serves both, and its
  scb-decomposition follows from @{thm [source] scbrepl_concl_from_image}.

  RESIDUAL.  The EXISTENCE of \<open>u\<^sub>1' \<in> T\<^bsub>B\<^esub>\<close> with the spliced flat string is the
  image-membership residual \<open>scbrepl_image\<close> (the recorded multi-hundred-line
  right-spine surgery, see @{thm [source] m_7_2_scb_replaceable_corr_mod_image}):
  the principal \<open>c\<close> sits at a valid scb position of \<open>u\<^sub>1\<close>, and \<open>c \<mapsto> c'\<close> there
  yields the witness.  We take it as a hypothesis (the constructive caller in the
  \<open>Trans\<close> well-foundedness argument supplies it), so the lemma below is the
  RIGOROUS green reduction of corrected (3) to that single residual — no
  circular / false citation.

  EMPIRICAL CHECK.  With the alignment premise the statement holds on every
  small-\<^typ>\<open>BT\<close> instance: occ.1 and occ.2 reference the same location, the two
  conclusion flat strings are syntactically equal, and (given the image witness)
  the scb side-conditions hold.  The literal (no-alignment) form fails exactly at
  the conj3 counterexample, which violates \<open>s\<^sub>0 = s\<^sub>1 @ D\<^sub>v # pre\<close>
  (\<open>s\<^sub>0 = [LP,D\<^sub>0,D\<^sub>0,Z,CM]\<close> but \<open>s\<^sub>1 @ D\<^sub>v # pre = [LP,D\<^sub>0]\<close> there).
\<close>

lemma m_7_2_add_scb_conj3:
  assumes tTB: "t \<in> T_B" and cTB: "c \<in> T_B" and cp: "\<exists>p. c = Trm [p]"
      and c'TB: "c' \<in> T_B" and c'p: "\<exists>p. c' = Trm [p]"
      and u1TB: "u\<^sub>1 \<in> T_B"
      and hyp1: "flatBT u\<^sub>1 = s\<^sub>1 @ (Dsym (enat v) # flatBT (t +\<^sub>B c)) @ b\<^sub>1"
      and hyp0: "scb_decomp u\<^sub>1 s\<^sub>0 (flatBT c) b\<^sub>0"
      \<comment> \<open>ALIGNMENT (A13): occ.2's \<open>c\<close> is the trailing principal of occ.1's \<open>t+c\<close>.\<close>
      and align_pre: "flatBT (t +\<^sub>B c) = pre @ flatBT c @ post"
      and align_s: "s\<^sub>0 = s\<^sub>1 @ (Dsym (enat v) # pre)"
      and align_b: "b\<^sub>0 = post @ b\<^sub>1"
      and align_post: "\<forall>x \<in> set post. x = RP"
      \<comment> \<open>The same \<open>pre\<close>/\<open>post\<close> serve \<open>c'\<close> (caller's split; cf. \<open>addscb_flat_pre_post2\<close>).\<close>
      and align_pre': "flatBT (t +\<^sub>B c') = pre @ flatBT c' @ post"
      \<comment> \<open>RESIDUAL: image-membership of the spliced string (\<open>scbrepl_image\<close>).\<close>
      and image: "\<exists>u\<^sub>1'. u\<^sub>1' \<in> T_B
                    \<and> flatBT u\<^sub>1' = s\<^sub>1 @ (Dsym (enat v) # flatBT (t +\<^sub>B c')) @ b\<^sub>1"
  shows "\<exists>u\<^sub>1'. u\<^sub>1' \<in> T_B
             \<and> flatBT u\<^sub>1' = s\<^sub>1 @ (Dsym (enat v) # flatBT (t +\<^sub>B c')) @ b\<^sub>1
             \<and> scb_decomp u\<^sub>1' s\<^sub>0 (flatBT c') b\<^sub>0"
proof -
  \<comment> \<open>The two flat strings required of \<open>u\<^sub>1'\<close> coincide (same \<open>pre\<close>/\<open>post\<close>).\<close>
  have str_eq: "s\<^sub>1 @ (Dsym (enat v) # flatBT (t +\<^sub>B c')) @ b\<^sub>1
                  = s\<^sub>0 @ flatBT c' @ b\<^sub>0"
    using align_s align_b align_pre' by simp
  \<comment> \<open>\<open>b\<^sub>0\<close> is all-\<open>RP\<close>: \<open>post\<close> all-\<open>RP\<close> and \<open>b\<^sub>1\<close> all-\<open>RP\<close> (the tail of \<open>hyp0\<close>).\<close>
  from hyp0 have b0_RP: "\<forall>x \<in> set b\<^sub>0. x = RP" unfolding scb_decomp_def by simp
  have b1_RP: "\<forall>x \<in> set b\<^sub>1. x = RP"
    using b0_RP align_b by simp
  \<comment> \<open>\<open>flatBT c'\<close> is a principal string (\<open>c'\<close> is single-principal in \<open>T\<^bsub>B\<^esub>\<close>).\<close>
  have ptb_c': "isPTB_str (flatBT c')"
    using c'p addscb_princ_isPTB[OF c'TB] by blast
  \<comment> \<open>Pull the image witness and assemble its scb-decomposition.\<close>
  from image obtain u1' where u1'TB: "u1' \<in> T_B"
      and fu1': "flatBT u1' = s\<^sub>1 @ (Dsym (enat v) # flatBT (t +\<^sub>B c')) @ b\<^sub>1"
    by blast
  have fu1'0: "flatBT u1' = s\<^sub>0 @ flatBT c' @ b\<^sub>0"
    using fu1' str_eq by simp
  have sd': "scb_decomp u1' s\<^sub>0 (flatBT c') b\<^sub>0"
    by (rule scbrepl_concl_from_image[OF u1'TB fu1'0 b0_RP disjI1[OF ptb_c']])
  show ?thesis using u1'TB fu1' sd' by blast
qed

end
