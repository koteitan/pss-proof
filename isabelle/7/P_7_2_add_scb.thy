theory P_7_2_add_scb
  imports Support_7_045
begin

section \<open>§7.2 系（加法とscb分解の関係） (3) — UNCONDITIONAL (A13, image residual discharged)\<close>

text \<open>
  The corrected corollary (3) @{thm [source] m_7_2_add_scb_conj3} carried one
  residual hypothesis: the image-membership of the spliced flat string
  \<open>∃u\<^sub>1'∈T\<^bsub>B\<^esub>. flatBT u\<^sub>1' = s\<^sub>1 @ (D\<^sub>v # flatBT (t+c')) @ b\<^sub>1\<close>.  That residual is now
  the proven UNCONDITIONAL lemma @{thm [source] m_7_2_add_scb_conj3_image}
  (right-spine surgery via \<open>gensurg_image_BT\<close>), whose premises are exactly
  \<open>t,c',u\<^sub>1 ∈ T\<^bsub>B\<^esub>\<close> and the occurrence equation \<open>flatBT u\<^sub>1 = s\<^sub>1 @ (D\<^sub>v # flatBT (t+c)) @ b\<^sub>1\<close>
  — all available here as \<open>tTB\<close>, \<open>c'TB\<close>, \<open>u1TB\<close>, \<open>hyp1\<close>.  Discharging it makes
  the corollary unconditional.  No new hypotheses, same conclusion as
  @{thm [source] m_7_2_add_scb_conj3} minus the \<open>image\<close> premise.
\<close>

lemma m_7_2_add_scb_conj3_uncond:
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
      and align_pre': "flatBT (t +\<^sub>B c') = pre @ flatBT c' @ post"
  shows "\<exists>u\<^sub>1'. u\<^sub>1' \<in> T_B
             \<and> flatBT u\<^sub>1' = s\<^sub>1 @ (Dsym (enat v) # flatBT (t +\<^sub>B c')) @ b\<^sub>1
             \<and> scb_decomp u\<^sub>1' s\<^sub>0 (flatBT c') b\<^sub>0"
proof -
  \<comment> \<open>Discharge the image residual UNCONDITIONALLY via @{thm m_7_2_add_scb_conj3_image}.\<close>
  have image: "\<exists>u\<^sub>1'. u\<^sub>1' \<in> T_B
                    \<and> flatBT u\<^sub>1' = s\<^sub>1 @ (Dsym (enat v) # flatBT (t +\<^sub>B c')) @ b\<^sub>1"
    by (rule m_7_2_add_scb_conj3_image[OF tTB c'TB u1TB hyp1])
  show ?thesis
    by (rule m_7_2_add_scb_conj3[OF tTB cTB cp c'TB c'p u1TB hyp1 hyp0
              align_pre align_s align_b align_post align_pre' image])
qed


text \<open>系（加法とscb分解の関係） (§7.2): for \<open>t \<in> T\<^bsub>B\<^esub>\<close>, \<open>c \<in> PT\<^bsub>B\<^esub>\<close>:
  (1) \<open>(t+c, c) \<in> T\<^bsub>B\<^esub>\<^sup>Marked\<close>;
  (2) if \<open>(s,flat c,b)\<close> is an scb-decomposition of \<open>t+c\<close>, then \<open>(s,flat c',b)\<close>
      is one of \<open>t+c'\<close>;
  (3) if \<open>s\<^sub>1\<frown>D\<^sub>v(t+c)\<frown>b\<^sub>1 \<in> T\<^bsub>B\<^esub>\<close> and \<open>(s\<^sub>0,flat c,b\<^sub>0)\<close> is an scb-decomposition of
      \<open>s\<^sub>1 D\<^sub>v(t+c) b\<^sub>1\<close>, then \<open>s\<^sub>1 D\<^sub>v(t+c') b\<^sub>1 \<in> T\<^bsub>B\<^esub>\<close> and \<open>(s\<^sub>0,flat c',b\<^sub>0)\<close> is
      an scb-decomposition of it.\<close>


text \<open>This proposition records the corrected form in
  @{file "../../corrections.md"}; the original annotation above is retained for
  comparison.\<close>

lemma p_7_2_add_scb:
  assumes "t \<in> T_B" "c \<in> T_B" "\<exists>p. c = Trm [p]"
  shows "(t +\<^sub>B c, c) \<in> MarkedB"
    and "\<And>s b c'. c' \<in> T_B \<Longrightarrow> (\<exists>p. c' = Trm [p]) \<Longrightarrow>
            scb_decomp (t +\<^sub>B c) s (flatBT c) b \<Longrightarrow>
            scb_decomp (t +\<^sub>B c') s (flatBT c') b"
    and "\<And>v s\<^sub>0 s\<^sub>1 b\<^sub>0 b\<^sub>1 c' u\<^sub>1 pre post.
            c' \<in> T_B \<Longrightarrow> (\<exists>p. c' = Trm [p]) \<Longrightarrow>
            u\<^sub>1 \<in> T_B \<Longrightarrow>
            flatBT u\<^sub>1 = s\<^sub>1 @ (Dsym (enat v) # flatBT (t +\<^sub>B c)) @ b\<^sub>1 \<Longrightarrow>
            scb_decomp u\<^sub>1 s\<^sub>0 (flatBT c) b\<^sub>0 \<Longrightarrow>
            flatBT (t +\<^sub>B c) = pre @ flatBT c @ post \<Longrightarrow>
            s\<^sub>0 = s\<^sub>1 @ (Dsym (enat v) # pre) \<Longrightarrow>
            b\<^sub>0 = post @ b\<^sub>1 \<Longrightarrow>
            (\<forall>x \<in> set post. x = RP) \<Longrightarrow>
            flatBT (t +\<^sub>B c') = pre @ flatBT c' @ post \<Longrightarrow>
            (\<exists>u\<^sub>1'. u\<^sub>1' \<in> T_B
                 \<and> flatBT u\<^sub>1' = s\<^sub>1 @ (Dsym (enat v) # flatBT (t +\<^sub>B c')) @ b\<^sub>1
                 \<and> scb_decomp u\<^sub>1' s\<^sub>0 (flatBT c') b\<^sub>0)"
  using assms
  by (blast intro: m_7_2_add_scb_conj1 m_7_2_add_scb_conj2
      m_7_2_add_scb_conj3_uncond)+

end
