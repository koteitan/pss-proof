theory P_7_2_scb_replaceable
  imports P_7_4_RightAnces_zeroT
begin

(* ===================================================================== *)
(* r77-Y3U: the CORRECTED forms of the genuinely-FALSE article            *)
(*   proposition statements.                                              *)
(*                                                                        *)
(* Before the reorganization, pss_paper held ~130 article statements as   *)
(* `sorry' (by design: statements there, proofs elsewhere).  NINE of them *)
(* were propositions we had REFUTED, i.e. FALSE statements carrying a     *)
(* `sorry' --- inconsistent axioms.  The ML audit at the end of this file *)
(* proves that NOTHING in the termination chain cites them, but they are  *)
(* a landmine.  The §7 reorganization removes the old §7 transcription   *)
(* stubs from pss_paper and states and proves HERE, under the y3u_ prefix, *)
(* the CORRECTED                                                            *)
(* form of each (per the corresponding correction Axx of corrections.md), *)
(* and register every y3u_ fact in the ML audit list below.  The `text'   *)
(* block after the lemmas is the register: false p_* |-> its replacement. *)
(*                                                                        *)
(* NOTE the fifteen RETRACTED corrections (A14 A24 A25 A26 A27 A28 A32    *)
(* A33 A34 A35 A36 A37 A38 A42 A43): those article statements are TRUE    *)
(* and are NOT touched here.                                              *)
(* ===================================================================== *)

section \<open>r77-Y3U --- corrected forms of the FALSE article statements\<close>

subsection \<open>A12 --- \<section>7.2 命題（scb分解の置換可能性）\<close>

text \<open>@{text p_7_2_scb_replaceable} is FALSE: its disjunctive premise
  \<open>(\<not> principal c\<^sub>0) \<or> principal c\<^sub>1\<close> is satisfied by the LEFT disjunct alone when
  \<open>c\<^sub>0 = 0\<close>, and then constrains \<open>c\<^sub>1\<close> not at all --- take \<open>t\<^sub>0 = c\<^sub>0 = 0\<close>, \<open>s = b = ()\<close>,
  \<open>c\<^sub>1 = D\<^sub>0 0 + D\<^sub>1 0\<close> (multi, hence non-principal): the conclusion's \<open>t\<^sub>1\<close> is forced to
  \<open>c\<^sub>1\<close> by \<open>flat\<close>-injectivity, but \<open>scb_decomp t\<^sub>1 s (flat c\<^sub>1) b\<close> then demands
  \<open>isPTB_str (flat c\<^sub>1)\<close>, which fails.  Correction \<^bold>\<open>A12\<close> moves the disjunction to
  \<open>c\<^sub>1\<close> and the RESULT: \<open>principal c\<^sub>1 \<or> s\<frown>flat(c\<^sub>1)\<frown>b = flat(0)\<close>.

  Proof of the corrected form: the \<open>image\<close> half (existence of \<open>t\<^sub>1 \<in> T\<^bsub>B\<^esub>\<close> with that
  flattening) is @{thm [source] scbrepl_image_principal} on the principal leg --- for
  \<open>t\<^sub>0 \<noteq> 0\<close> the scb-decomposition itself forces \<open>c\<^sub>0\<close> principal, and \<open>t\<^sub>0 = 0\<close> collapses
  \<open>s\<close> and \<open>b\<close> to \<open>()\<close> so \<open>t\<^sub>1 = c\<^sub>1\<close> serves; the \<open>scb\<close> half is then
  @{thm [source] m_7_2_scb_replaceable_corr_mod_image}.\<close>

theorem y3u_p_7_2_scb_replaceable:
  fixes c\<^sub>0 c\<^sub>1 t\<^sub>0 :: BT and s b :: "Sym list"
  assumes c0TB: "c\<^sub>0 \<in> T_B" and c1TB: "c\<^sub>1 \<in> T_B" and t0TB: "t\<^sub>0 \<in> T_B"
    and d0: "scb_decomp t\<^sub>0 s (flatBT c\<^sub>0) b"
    and side: "isPTB_str (flatBT c\<^sub>1) \<or> s @ flatBT c\<^sub>1 @ b = [Zsym]"
  shows "\<exists>t\<^sub>1. t\<^sub>1 \<in> T_B \<and> flatBT t\<^sub>1 = s @ flatBT c\<^sub>1 @ b
            \<and> scb_decomp t\<^sub>1 s (flatBT c\<^sub>1) b"
proof -
  have image: "\<exists>t\<^sub>1. t\<^sub>1 \<in> T_B \<and> flatBT t\<^sub>1 = s @ flatBT c\<^sub>1 @ b"
  proof (cases "t\<^sub>0 = Trm []")
    case True
    \<comment> \<open>zero host: \<open>flat t\<^sub>0 = [Zsym]\<close> has length 1 and \<open>flat c\<^sub>0 \<noteq> ()\<close>, so \<open>s = b = ()\<close>\<close>
    have fl: "flatBT t\<^sub>0 = s @ flatBT c\<^sub>0 @ b" using d0 by (simp add: scb_decomp_def)
    have z: "s @ flatBT c\<^sub>0 @ b = [Zsym]" using fl True by simp
    have cne: "flatBT c\<^sub>0 \<noteq> []" by (rule flatBT_nonempty)
    have s0: "s = []"
    proof (rule ccontr)
      assume "s \<noteq> []"
      then obtain x xs where sx: "s = x # xs" by (cases s) auto
      have "length (s @ flatBT c\<^sub>0 @ b) \<ge> 2"
        using sx cne by (cases "flatBT c\<^sub>0") auto
      thus False using z by simp
    qed
    have b0: "b = []"
    proof (rule ccontr)
      assume "b \<noteq> []"
      then obtain y ys where by': "b = y # ys" by (cases b) auto
      have "length (s @ flatBT c\<^sub>0 @ b) \<ge> 2"
        using by' cne by (cases "flatBT c\<^sub>0") auto
      thus False using z by simp
    qed
    have "flatBT c\<^sub>1 = s @ flatBT c\<^sub>1 @ b" using s0 b0 by simp
    thus ?thesis using c1TB by blast
  next
    case False
    \<comment> \<open>non-zero host: the scb-decomposition forces \<open>c\<^sub>0\<close> principal\<close>
    have pc0: "isPTB_str (flatBT c\<^sub>0)" using d0 False by (simp add: scb_decomp_def)
    then obtain p\<^sub>0 where p0: "dfree_BP p\<^sub>0" "flatBT c\<^sub>0 = flatBP p\<^sub>0"
      by (auto simp: isPTB_str_def)
    have c0eq: "c\<^sub>0 = Trm [p\<^sub>0]"
      by (rule m_7_flatBT_inj) (use p0(2) in simp)
    show ?thesis
    proof (cases "isPTB_str (flatBT c\<^sub>1)")
      case True
      then obtain p\<^sub>1 where p1: "dfree_BP p\<^sub>1" "flatBT c\<^sub>1 = flatBP p\<^sub>1"
        by (auto simp: isPTB_str_def)
      have c1eq: "c\<^sub>1 = Trm [p\<^sub>1]"
        by (rule m_7_flatBT_inj) (use p1(2) in simp)
      show ?thesis
        by (rule scbrepl_image_principal[OF t0TB c0eq c1TB c1eq d0])
    next
      case False
      \<comment> \<open>then the RESULT is the zero term, and \<open>t\<^sub>1 = 0\<close> serves\<close>
      have zr: "s @ flatBT c\<^sub>1 @ b = [Zsym]" using side False by blast
      have "(Trm [] :: BT) \<in> T_B" by (simp add: T_B_def)
      thus ?thesis using zr by auto
    qed
  qed
  show ?thesis
    by (rule m_7_2_scb_replaceable_corr_mod_image[OF c1TB d0 side image])
qed

text \<open>
  Modelling note for the §7.2 propositions below.  The article ranges over
  \<open>\<Sigma>\<^bsup><\<omega>\<^esup>\<close> (strings) and \<open>\<nat>\<^bsup><\<omega>\<^esup>\<close>; we model the former as \<^typ>\<open>Sym list\<close>
  and the latter as \<^typ>\<open>nat list\<close>, with the string connective \<open>s c b\<close> = list
  append \<open>@\<close> and \<open>\<oplus>\<^sub>\<nat>\<close> = \<open>@\<close>.  "\<open>x \<in> T\<^bsub>B\<^esub>\<close> as a string" (i.e. the string is the
  \<open>flat\<close> of a \<open>D\<^sub>\<omega>\<close>-free term) is written \<open>\<exists>t. t \<in> T\<^bsub>B\<^esub> \<and> flatBT t = \<dots>\<close>; the
  unique witnessing term is recovered by \<open>unflatBT\<close> (defined in §7.3).  "\<open>c\<close> 単項" (\<open>c \<in> PT\<^bsub>B\<^esub>\<close>)
  for a \<^typ>\<open>BT\<close> is \<open>\<exists>p. c = Trm [p]\<close> (a single principal component), with
  \<open>D\<^sub>\<omega>\<close>-freeness added as \<open>c \<in> T\<^bsub>B\<^esub>\<close> where the article writes \<open>PT\<^bsub>B\<^esub>\<close>.  The
  string-level \<open>D\<^sub>v\<close>-prefix \<open>D\<^sub>v s\<close> is \<open>Dsym (enat v) # s\<close> (cf. \<^const>\<open>flatBP\<close>).
\<close>

text \<open>命題（scb分解の置換可能性） (§7.2): for strings \<open>s,b\<close> and terms \<open>c\<^sub>0,c\<^sub>1\<close>,
  if (\<open>c\<^sub>0\<close> is not principal \<open>\<or>\<close> \<open>c\<^sub>1\<close> is principal), the string \<open>s\<frown>flat c\<^sub>0\<frown>b\<close> is
  (the \<open>flat\<close> of) a term \<open>\<in> T\<^bsub>B\<^esub>\<close>, and \<open>(s, flat c\<^sub>0, b)\<close> is an scb-decomposition
  of it, then \<open>s\<frown>flat c\<^sub>1\<frown>b\<close> is also (the \<open>flat\<close> of) a term \<open>\<in> T\<^bsub>B\<^esub>\<close> and
  \<open>(s, flat c\<^sub>1, b)\<close> is an scb-decomposition of it.\<close>


text \<open>This proposition records the corrected form in
  @{file "../../corrections.md"}; the original annotation above is retained for
  comparison.\<close>

lemma p_7_2_scb_replaceable:
  assumes "c\<^sub>0 \<in> T_B" "c\<^sub>1 \<in> T_B"
    and "t\<^sub>0 \<in> T_B" "flatBT t\<^sub>0 = s @ flatBT c\<^sub>0 @ b"
    and "scb_decomp t\<^sub>0 s (flatBT c\<^sub>0) b"
    and "isPTB_str (flatBT c\<^sub>1) \<or> s @ flatBT c\<^sub>1 @ b = [Zsym]"
  shows "\<exists>t\<^sub>1. t\<^sub>1 \<in> T_B \<and> flatBT t\<^sub>1 = s @ flatBT c\<^sub>1 @ b
            \<and> scb_decomp t\<^sub>1 s (flatBT c\<^sub>1) b"
  by (rule y3u_p_7_2_scb_replaceable
      [OF assms(1) assms(2) assms(3) assms(5) assms(6)])

end
