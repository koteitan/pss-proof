theory P_7_2_scb_compose
  imports Support_7_008
begin

text \<open>
  Therefore only part (1) of \<open>p_7_2_scb_compose\<close> is mechanized below as
  \<open>m_7_2_scb_compose\<close>; part (2) holds in the corrected form \<open>scbcomp_compose2_PT\<close>
  (with the side-condition \<open>isPTB_str c\<close>, equivalently for any \<open>t \<noteq> Trm []\<close>).
  Reporting part (2) as a BLOCKER / counterexample (see \<open>corrections.md\<close>).
\<close>

lemma m_7_2_scb_compose:
  assumes c0prin: "\<exists>p. c\<^sub>0 = Trm [p]"
    and d0: "scb_decomp t s\<^sub>0 (flatBT c\<^sub>0) b\<^sub>0"
    and d1: "scb_decomp c\<^sub>0 s\<^sub>1 c\<^sub>1 b\<^sub>1"
  shows "scb_decomp t (s\<^sub>0 @ s\<^sub>1) c\<^sub>1 (b\<^sub>1 @ b\<^sub>0)"
  using scbcomp_compose1[OF c0prin d0 d1] .


text \<open>命題（scb分解の合成則） (§7.2):
  (1) if \<open>(s\<^sub>0,flat c\<^sub>0,b\<^sub>0)\<close> is an scb-decomposition of \<open>t\<close> (\<open>c\<^sub>0 \<in> PT\<^bsub>B\<^esub>\<close>) and
      \<open>(s\<^sub>1,c\<^sub>1,b\<^sub>1)\<close> is an scb-decomposition of \<open>c\<^sub>0\<close>, then \<open>(s\<^sub>0\<frown>s\<^sub>1, c\<^sub>1, b\<^sub>1\<frown>b\<^sub>0)\<close>
      is an scb-decomposition of \<open>t\<close>;
  (2) if \<open>(s,c,b)\<close> is an scb-decomposition of \<open>t\<close> then \<open>(D\<^sub>v s, c, b)\<close> is one of
      \<open>D\<^sub>v t\<close>.\<close>


text \<open>This proposition records the corrected form in
  @{file "../../corrections.md"}; the original annotation above is retained for
  comparison.\<close>

lemma p_7_2_scb_compose:
  assumes "t \<in> T_B"
  shows "\<And>c\<^sub>0 s\<^sub>0 s\<^sub>1 c\<^sub>1 b\<^sub>1 b\<^sub>0.
            c\<^sub>0 \<in> T_B \<Longrightarrow> (\<exists>p. c\<^sub>0 = Trm [p]) \<Longrightarrow>
            scb_decomp t s\<^sub>0 (flatBT c\<^sub>0) b\<^sub>0 \<Longrightarrow>
            scb_decomp c\<^sub>0 s\<^sub>1 c\<^sub>1 b\<^sub>1 \<Longrightarrow>
            scb_decomp t (s\<^sub>0 @ s\<^sub>1) c\<^sub>1 (b\<^sub>1 @ b\<^sub>0)"
    and "\<And>v s c b. isPTB_str c \<Longrightarrow> scb_decomp t s c b \<Longrightarrow>
            scb_decomp (Dpt (enat v) t) (Dsym (enat v) # s) c b"
  using assms
  by (blast intro: m_7_2_scb_compose scbcomp_compose2_PT)+

end
