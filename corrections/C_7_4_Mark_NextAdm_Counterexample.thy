theory C_7_4_Mark_NextAdm_Counterexample
  imports C_7_3_Red_Admissibility_Counterexample
begin

text \<open>Relocated proof material.  The declarations retain their original source order,
  and every relocated annotation is preserved below.  This theory is machine-checked
  outside the termination build tree.\<close>

subsection \<open>(g) closing note --- the \<open>T\<^bsub>PS\<^esub>\<close> form of the §7.4 系 is FALSE\<close>

text \<open>\<^bold>\<open>Do not look for a \<open>T\<^bsub>PS\<^esub>\<close> proof of the §7.4 系 (\<open>Mark\<close> vs. \<open>NextAdm\<close>): there
  isn't one.\<close>  The \<open>RT\<^bsub>PS\<^esub>\<close> statement is true and already proved
  (@{thm [source] m_7_4_Mark_nextAdm}); the \<open>T\<^bsub>PS\<^esub>\<close> statement is refuted.  Witness
  (verified with the vetted executable models \<open>python/red_model.py\<close> and
  \<open>python/trans_model.py\<close>):

    \<^item> \<open>M = (0,0)(4,2)(2,6)(4,2)(8,4)(6,4) \<in> T\<^bsub>PS\<^esub>\<close>, NOT reduced, \<open>Lng M - 1 = 5\<close>;
    \<^item> the unique \<open>j\<^sub>0\<close> with \<open>nextAdm M 0 j\<^sub>0 5\<close> is \<open>j\<^sub>0 = 3\<close>;
    \<^item> for \<open>j = 0\<close> (and likewise for \<open>j = 2\<close>): \<open>adm M j\<close>, \<open>leR M 0 j 5\<close> --- so
      \<open>(M,j) \<in> Marked\<close>, which is exactly the hypothesis correction A18 requires ---
      and \<open>leR M 0 j j\<^sub>0\<close>, which is the 系's own hypothesis;
    \<^item> yet the number of \<open>(s\<^sub>0,b\<^sub>0)\<close> that decompose BOTH \<open>Mark (Pred M) j\<close> with core
      \<open>Mark (Pred M) j\<^sub>0\<close> AND \<open>Mark M j\<close> with core \<open>Mark M j\<^sub>0\<close> is \<^bold>\<open>0\<close> (each side
      separately has exactly one, and they differ).

  \<^bold>\<open>Mechanism.\<close>  \<open>Mark M j\<^sub>0 = Mark (Pred M) j\<^sub>0\<close> --- the two cores COINCIDE --- while
  \<open>Mark M j \<noteq> Mark (Pred M) j\<close>.  A common \<open>(s\<^sub>0,b\<^sub>0)\<close> would give the two scb equations the
  same right-hand side, so flat-injectivity (@{thm [source] m_7_flatBT_inj}) would force
  \<open>Mark (Pred M) j = Mark M j\<close> --- contradiction.  Hence NO common position exists.

  \<^bold>\<open>Root cause\<close> --- the same one as corrections A45 and A46, which already had to move
  the neighbouring §7.4 propositions from \<open>T\<^bsub>PS\<^esub>\<close> to \<open>RT\<^bsub>PS\<^esub>\<close>: by correction A4, \<open>\<le>\<^sub>M\<close> is
  NOT \<open>Red\<close>-invariant.  \<open>Trans\<close>/\<open>Mark\<close> read their basepoints off \<open>Red M\<close>, whereas
  \<open>adm\<close>/\<open>nextAdm\<close>/\<open>leR\<close> in the hypotheses are read off \<open>M\<close>; on a non-reduced \<open>M\<close> the two
  need not agree, and @{thm [source] y3z_C4_false} / @{thm [source] y3z_brickA_false}
  show they really do not.  This 系 therefore belongs on \<open>RT\<^bsub>PS\<^esub>\<close> like its neighbours.

  \<^bold>\<open>What survives, and is new.\<close>  On \<open>RT\<^bsub>PS\<^esub>\<close> the nesting needs far less than the article
  asks for: @{thm [source] y4b_Mark_nest_free} / @{thm [source] y4c_Mark_nest_free_ex1}
  give it with NO admissibility, NO \<open>Marked\<close>-ness and NO ancestry at all, for every
  \<open>j \<le> j\<^sub>0\<close>.  What genuinely IS needed --- and only for the \<^emph>\<open>joint\<close> (\<open>Pred\<close>-companion)
  form that the 系's proof uses --- is that the OUTER column be a surgery column,
  \<open>j\<^sub>0 \<le> transJm1 N\<close> (@{thm [source] y4f_Mark_nest_Pred_joint_sharp}); \<open>Marked\<close>-ness of
  \<open>j\<^sub>0\<close> is merely a convenient stronger sufficient condition, and it is also the thing
  that transports through the \<open>multiT\<close> recursion (@{thm [source] y4d_Mark_nest_Pred_joint}).\<close>
(* ===================================================================== *)
(* r81-Y6: the T_PS TRANSPORT and the ASSEMBLY of the §7.4 Mark/NextAdm   *)
(* proposition (article's 系, correction A18's form).                     *)
(*                                                                        *)
(* (1) y6_scb_self / y6_scb_self_unique: the SELF scb-decomposition of a  *)
(*     principal-or-zero term is ([],[]) --- and it is the ONLY one.      *)
(* (2) y6_Mark_selfnest_RT / y6_Mark_selfnest_TPS: the REFLEXIVE half of  *)
(*     the proposition (j = j0) --- UNCONDITIONALLY on T_PS.  No Marked,  *)
(*     no adm, no nextAdm, no ancestry.  This is precisely the half that  *)
(*     Brick A (adm (Red (Red M)) j0) killed: y3z_brickA_false's witness  *)
(*     is a j = j0 exercise.                                              *)
(* (3) y6_7_4_Mark_nextAdm_TPS: the article's statement, on ALL of T_PS,  *)
(*     with the hypotheses read off M (NOT off the reduct), modulo the    *)
(*     RELAXED (adm-free) §7 nesting engine as an explicit 'assumes'.     *)
(* ===================================================================== *)

section \<open>r81-Y6 --- \<section>7.4 \<open>Mark\<close>/\<open>NextAdm\<close> on \<open>T\<^bsub>PS\<^esub>\<close>: transport and assembly\<close>

subsection \<open>The self scb-decomposition of a principal-or-zero term\<close>

text \<open>If \<open>t\<close> is \<open>0\<^sub>B\<close> or a single principal term, then \<open>([], flat t, [])\<close> IS an
  scb-decomposition of \<open>t\<close>, and \<^emph>\<open>every\<close> scb-decomposition of \<open>t\<close> whose core is
  \<open>flat t\<close> is that one (a length count on \<open>flat t = s @ flat t @ b\<close>).\<close>

lemma y6_scb_self_unique:
  assumes d: "scb_decomp t s (flatBT t) b"
  shows "s = [] \<and> b = []"
proof -
  have e: "flatBT t = s @ flatBT t @ b" using d by (simp add: scb_decomp_def)
  have L: "length (flatBT t) = length s + (length (flatBT t) + length b)"
    using arg_cong[where f = length, OF e] by simp
  have s0: "length s = 0" using L by linarith
  have b0: "length b = 0" using L by linarith
  show ?thesis using s0 b0 by simp
qed

lemma y6_scb_self:
  assumes p: "t = 0\<^sub>B \<or> isPTB_str (flatBT t)"
  shows "scb_decomp t [] (flatBT t) []"
  using p by (auto simp: scb_decomp_def)

subsection \<open>The reflexive half (\<open>j = j\<^sub>0\<close>), unconditionally\<close>

text \<open>\<^bold>\<open>The \<open>j = j\<^sub>0\<close> case of the \<section>7.4 proposition needs no hypothesis at all\<close>
  beyond \<open>M \<in> T\<^bsub>PS\<^esub>\<close>: by @{thm [source] y3y_Mark_princ} the value of \<open>Mark\<close> at
  \<^emph>\<open>every\<close> column of a reduced sequence is principal-or-zero, hence self-nests
  uniquely --- and both \<open>Mark N m\<close> and \<open>Mark (Pred N) m\<close> are such values
  (\<open>Pred\<close> preserves \<open>RT\<^bsub>PS\<^esub>\<close>, @{thm [source] Pred_RT_PS}).\<close>

theorem y6_Mark_selfnest_RT:
  assumes NR: "N \<in> RT_PS"
  shows "\<exists>!sb. scb_decomp (Mark (Pred N) m) (fst sb) (flatBT (Mark (Pred N) m)) (snd sb)
             \<and> scb_decomp (Mark N m) (fst sb) (flatBT (Mark N m)) (snd sb)"
proof -
  have PR: "Pred N \<in> RT_PS" by (rule Pred_RT_PS[OF NR])
  have p1: "scb_decomp (Mark (Pred N) m) [] (flatBT (Mark (Pred N) m)) []"
    by (rule y6_scb_self) (rule y3y_Mark_princ(2)[OF PR])
  have p2: "scb_decomp (Mark N m) [] (flatBT (Mark N m)) []"
    by (rule y6_scb_self) (rule y3y_Mark_princ(2)[OF NR])
  show ?thesis
  proof (rule ex1I[of _ "([], [])"])
    show "scb_decomp (Mark (Pred N) m) (fst ([], []))
             (flatBT (Mark (Pred N) m)) (snd ([], []))
        \<and> scb_decomp (Mark N m) (fst ([], [])) (flatBT (Mark N m)) (snd ([], []))"
      using p1 p2 by simp
  next
    fix sb :: "Sym list \<times> Sym list"
    assume a: "scb_decomp (Mark (Pred N) m) (fst sb) (flatBT (Mark (Pred N) m)) (snd sb)
             \<and> scb_decomp (Mark N m) (fst sb) (flatBT (Mark N m)) (snd sb)"
    have "fst sb = [] \<and> snd sb = []" using y6_scb_self_unique[of "Mark N m"] a by blast
    thus "sb = ([], [])" by (cases sb) simp
  qed
qed

text \<open>Transport to \<open>T\<^bsub>PS\<^esub>\<close>: \<open>Mark M i = Mark (Red\<^sup>2 M) i\<close> (@{thm [source] y3s_Mark_funpow_Red})
  and --- the crux --- \<open>Mark (Pred M) i = Mark (Pred (Red\<^sup>2 M)) i\<close>, which holds because
  \<open>Red\<close> COMMUTES with \<open>Pred\<close> on all of \<open>T\<^bsub>PS\<^esub>\<close> (@{thm [source] m_6_5_Red_Pred},
  @{thm [source] y3s_Pred_funpow_Red}: \<open>Red\<^sup>k (Pred M) = Pred (Red\<^sup>k M)\<close>) and \<open>Red\<^sup>2 M\<close> is
  reduced (@{thm [source] y3r_RED2}).  So the \<^emph>\<open>subject matter\<close> of the proposition
  transports verbatim; only \<open>adm\<close>/\<open>Marked\<close>/\<open>nextAdm\<close> --- its \<^emph>\<open>hypotheses\<close> --- do not.\<close>

theorem y6_Mark_selfnest_TPS:
  assumes MT: "M \<in> T_PS"
  shows "\<exists>!sb. scb_decomp (Mark (Pred M) m) (fst sb) (flatBT (Mark (Pred M) m)) (snd sb)
             \<and> scb_decomp (Mark M m) (fst sb) (flatBT (Mark M m)) (snd sb)"
proof -
  let ?R = "Red (Red M)"
  have RR: "?R \<in> RT_PS" by (rule y3r_RED2[OF MT])
  have F2: "(Red ^^ 2) M = ?R" by (simp add: numeral_2_eq_2)
  have F: "(Red ^^ 2) M \<in> RT_PS" using RR F2 by simp
  have pe: "(Red ^^ 2) (Pred M) = Pred ?R"
    using y3s_Pred_funpow_Red[OF MT, of 2] F2 by simp
  have PF: "Pred ?R \<in> RT_PS" by (rule Pred_RT_PS[OF RR])
  have PFR: "(Red ^^ 2) (Pred M) \<in> RT_PS" using pe PF by simp
  have mM: "\<And>i. Mark M i = Mark ?R i" using y3s_Mark_funpow_Red[OF F] F2 by simp
  have mP: "\<And>i. Mark (Pred M) i = Mark (Pred ?R) i"
    using y3s_Mark_funpow_Red[OF PFR] pe by simp
  have base: "\<exists>!sb. scb_decomp (Mark (Pred ?R) m) (fst sb)
                       (flatBT (Mark (Pred ?R) m)) (snd sb)
                   \<and> scb_decomp (Mark ?R m) (fst sb) (flatBT (Mark ?R m)) (snd sb)"
    by (rule y6_Mark_selfnest_RT[OF RR])
  show ?thesis using base mM mP by simp
qed

subsection \<open>The article's \<section>7.4 proposition on \<open>T\<^bsub>PS\<^esub>\<close>, modulo the relaxed engine\<close>

text \<open>\<^bold>\<open>The assembly.\<close>  The hypotheses are read off \<open>M\<close>, exactly as the article
  states them (correction A18's form).  The only thing assumed is the
  \<^bold>\<open>relaxed nesting engine\<close> \<open>ENG\<close>: @{thm [source] Mark_nest_common_marked} with the
  two \<open>Marked\<close> premises weakened to their \<open>\<le>\<^sub>M\<close>-halves (i.e. \<open>adm\<close> DROPPED at both
  columns), and only for the STRICT case \<open>m < m'\<close> --- the reflexive case is
  discharged here by @{thm [source] y6_Mark_selfnest_TPS}.  Every hypothesis of
  \<open>ENG\<close> is one this proof can actually supply at the reduct \<open>R = Red (Red M)\<close>:

    \<^item> \<open>R \<in> RT\<^bsub>PS\<^esub>\<close> --- @{thm [source] y3r_RED2};
    \<^item> \<open>le\<^sub>0 R j j\<^sub>0\<close>, \<open>le\<^sub>0 R j (Lng R - 1)\<close>, \<open>le\<^sub>0 R j\<^sub>0 (Lng R - 1)\<close> --- (F),
      @{thm [source] y3w_Red2_le0}: \<open>Red\<close> only ADDS row-0 ancestor edges;
    \<^item> \<open>j < j\<^sub>0\<close>, \<open>j\<^sub>0 < Lng R - 1\<close> --- from \<open>nextAdm\<close> and \<open>Lng (Red\<^sup>2 M) = Lng M\<close>.

  \<^bold>\<open>adm is NOT among them\<close>, and cannot be: \<open>adm R j\<^sub>0\<close> is refuted by
  @{thm [source] y3z_brickA_false}.  So \<open>ENG\<close> is exactly the residue of the whole
  \<open>T\<^bsub>PS\<^esub>\<close> statement.\<close>

theorem y6_7_4_Mark_nextAdm_TPS:
  assumes ENG: "\<And>N m m'. N \<in> RT_PS \<Longrightarrow> le0 N m m' \<Longrightarrow> le0 N m (Lng N - 1)
                  \<Longrightarrow> le0 N m' (Lng N - 1) \<Longrightarrow> m < m' \<Longrightarrow> m' < Lng N - 1
                  \<Longrightarrow> \<exists>!sb. scb_decomp (Mark (Pred N) m) (fst sb)
                               (flatBT (Mark (Pred N) m')) (snd sb)
                          \<and> scb_decomp (Mark N m) (fst sb)
                               (flatBT (Mark N m')) (snd sb)"
    and MT: "M \<in> T_PS"
    and uniq: "\<exists>!j0. nextAdm M 0 j0 (Lng M - 1)"
    and jM: "(M, j) \<in> Marked"
    and jle: "leR M 0 j (THE j0. nextAdm M 0 j0 (Lng M - 1))"
  shows "\<exists>!sb. scb_decomp (Mark (Pred M) j)
                  (fst sb) (flatBT (Mark (Pred M)
                     (THE j0. nextAdm M 0 j0 (Lng M - 1)))) (snd sb)
            \<and> scb_decomp (Mark M j)
                  (fst sb) (flatBT (Mark M
                     (THE j0. nextAdm M 0 j0 (Lng M - 1)))) (snd sb)"
proof -
  let ?j0 = "THE j0. nextAdm M 0 j0 (Lng M - 1)"
  let ?R = "Red (Red M)"
  have RR: "?R \<in> RT_PS" by (rule y3r_RED2[OF MT])
  have F2: "(Red ^^ 2) M = ?R" by (simp add: numeral_2_eq_2)
  have F: "(Red ^^ 2) M \<in> RT_PS" using RR F2 by simp
  have na: "nextAdm M 0 ?j0 (Lng M - 1)" by (rule theI'[OF uniq])
  have j0lt: "?j0 < Lng M - 1" using na unfolding nextAdm_def by blast
  have LR: "Lng ?R = Lng M" using y3s_Lng_funpow_Red[OF MT, of 2] F2 by simp
  have j0ltR: "?j0 < Lng ?R - 1" using j0lt LR by simp
  \<comment> \<open>the three \<open>\<le>\<^sub>M\<close> facts, read off \<open>M\<close> \<dots>\<close>
  have leRA: "leR M 0 ?j0 (Lng M - 1)" using na unfolding nextAdm_def by blast
  have leA_M: "le0 M ?j0 (Lng M - 1)" using leRA by (simp add: leR_def)
  have leRB: "leR M 0 j (Lng M - 1)" using jM by (simp add: Marked_def)
  have leB_M: "le0 M j (Lng M - 1)" using leRB by (simp add: leR_def)
  have lejj_M: "le0 M j ?j0" using jle by (simp add: leR_def)
  \<comment> \<open>\<dots> and transported to the reduct by (F)\<close>
  have leA: "le0 ?R ?j0 (Lng ?R - 1)" using y3w_Red2_le0[OF MT leA_M] LR by simp
  have leB: "le0 ?R j (Lng ?R - 1)" using y3w_Red2_le0[OF MT leB_M] LR by simp
  have lejj: "le0 ?R j ?j0" by (rule y3w_Red2_le0[OF MT lejj_M])
  have jle0: "j \<le> ?j0"
  proof -
    have "(nextrel0 M)\<^sup>*\<^sup>* j ?j0" using jle by (simp add: leR_def le0_def)
    thus ?thesis by (rule nextrel0_rtrancl_mono)
  qed
  have pe: "(Red ^^ 2) (Pred M) = Pred ?R"
    using y3s_Pred_funpow_Red[OF MT, of 2] F2 by simp
  have PF: "Pred ?R \<in> RT_PS" by (rule Pred_RT_PS[OF RR])
  have PFR: "(Red ^^ 2) (Pred M) \<in> RT_PS" using pe PF by simp
  have mM: "\<And>i. Mark M i = Mark ?R i" using y3s_Mark_funpow_Red[OF F] F2 by simp
  have mP: "\<And>i. Mark (Pred M) i = Mark (Pred ?R) i"
    using y3s_Mark_funpow_Red[OF PFR] pe by simp
  show ?thesis
  proof (cases "j = ?j0")
    case eq: True
    have self: "\<exists>!sb. scb_decomp (Mark (Pred M) j) (fst sb)
                         (flatBT (Mark (Pred M) j)) (snd sb)
                     \<and> scb_decomp (Mark M j) (fst sb) (flatBT (Mark M j)) (snd sb)"
      by (rule y6_Mark_selfnest_TPS[OF MT])
    show ?thesis using self eq by simp
  next
    case False
    hence jlt: "j < ?j0" using jle0 by simp
    have base: "\<exists>!sb. scb_decomp (Mark (Pred ?R) j) (fst sb)
                         (flatBT (Mark (Pred ?R) ?j0)) (snd sb)
                     \<and> scb_decomp (Mark ?R j) (fst sb) (flatBT (Mark ?R ?j0)) (snd sb)"
      by (rule ENG[OF RR lejj leB leA jlt j0ltR])
    show ?thesis using base mM mP by simp
  qed
qed

text \<open>\<^bold>\<open>STATUS (r81)\<close>.  The \<open>T\<^bsub>PS\<^esub>\<close> transport is \<^bold>\<open>complete\<close>: nothing about \<open>Pred\<close>,
  \<open>Mark\<close>, \<open>Lng\<close> or \<open>\<le>\<^sub>0\<close> is left to prove, and the reflexive case is closed
  outright.  The \<^bold>\<open>single\<close> residual of the article's \<section>7.4 系 on \<open>T\<^bsub>PS\<^esub>\<close> is the
  relaxed engine \<open>ENG\<close> above --- an \<open>RT\<^bsub>PS\<^esub>\<close>-only, \<open>adm\<close>-free statement.

  \<^bold>\<open>\<open>ENG\<close> IS FALSE\<close> (r81, next subsection).  Hence
  @{thm [source] y6_7_4_Mark_nextAdm_TPS} is a \<^emph>\<open>valid but vacuous\<close> implication ---
  it is kept only because it pins the residue exactly, and the residue turns out
  to be refutable.  \<^bold>\<open>The article's \<section>7.4 系 does NOT hold on \<open>T\<^bsub>PS\<^esub>\<close>.\<close>\<close>


(* ===================================================================== *)
(* r81-Y6Z: THE TARGET IS FALSE.                                          *)
(*                                                                        *)
(* The article's §7.4 系 does NOT extend from RT_PS to T_PS, and the       *)
(* adm-free ("relaxed") §7 nesting engine is FALSE already on RT_PS.      *)
(* The MECHANISM is proved here outright (y6z_no_common_position); the    *)
(* witnesses are computed with the vetted model (python/red_model.py,     *)
(* python/trans_model.py) and recorded below.                             *)
(* ===================================================================== *)

section \<open>r81-Y6Z --- refutation: \<open>adm\<close> at the OUTER column is load-bearing\<close>

subsection \<open>The mechanism, proved: coinciding cores + differing ambients\<close>

text \<open>\<^bold>\<open>The obstruction.\<close>  The \<section>7.4 conclusion asks for \<^emph>\<open>one\<close> scb-position
  \<open>(s\<^sub>0,b\<^sub>0)\<close> that works simultaneously for the \<open>Pred\<close>-side and the \<open>M\<close>-side.  Both
  decompositions have the SAME \<open>(s\<^sub>0,b\<^sub>0)\<close> but DIFFERENT cores --- \<open>Mark (Pred N) m'\<close>
  resp. \<open>Mark N m'\<close>.  So if the two cores happen to \<^emph>\<open>coincide\<close> while the two
  ambient terms do not, the two equations
    \<open>flat (Mark (Pred N) m) = s\<^sub>0 @ flat (Mark (Pred N) m') @ b\<^sub>0\<close>,
    \<open>flat (Mark N m)        = s\<^sub>0 @ flat (Mark N m')        @ b\<^sub>0\<close>
  have equal right-hand sides, forcing \<open>Mark (Pred N) m = Mark N m\<close> by injectivity of
  \<open>flat\<close> (@{thm [source] m_7_flatBT_inj}) --- a contradiction.  No \<open>Mark\<close>-computation,
  no \<open>Red\<close>, no hypothesis whatsoever is needed for this.\<close>

lemma y6z_no_common_position:
  assumes core: "Mark N m' = Mark (Pred N) m'"
      and ne: "Mark N m \<noteq> Mark (Pred N) m"
  shows "\<not> (\<exists>sb. scb_decomp (Mark (Pred N) m) (fst sb) (flatBT (Mark (Pred N) m')) (snd sb)
               \<and> scb_decomp (Mark N m) (fst sb) (flatBT (Mark N m')) (snd sb))"
proof
  assume "\<exists>sb. scb_decomp (Mark (Pred N) m) (fst sb) (flatBT (Mark (Pred N) m')) (snd sb)
             \<and> scb_decomp (Mark N m) (fst sb) (flatBT (Mark N m')) (snd sb)"
  then obtain sb where
       d1: "scb_decomp (Mark (Pred N) m) (fst sb) (flatBT (Mark (Pred N) m')) (snd sb)"
   and d2: "scb_decomp (Mark N m) (fst sb) (flatBT (Mark N m')) (snd sb)" by blast
  have e1: "flatBT (Mark (Pred N) m) = fst sb @ flatBT (Mark (Pred N) m') @ snd sb"
    using d1 by (simp add: scb_decomp_def)
  have e2: "flatBT (Mark N m) = fst sb @ flatBT (Mark N m') @ snd sb"
    using d2 by (simp add: scb_decomp_def)
  have "flatBT (Mark (Pred N) m) = flatBT (Mark N m)" using e1 e2 core by simp
  hence "Mark (Pred N) m = Mark N m" by (rule m_7_flatBT_inj)
  thus False using ne by simp
qed

corollary y6z_nest_false_at:
  assumes core: "Mark N m' = Mark (Pred N) m'"
      and ne: "Mark N m \<noteq> Mark (Pred N) m"
  shows "\<not> (\<exists>!sb. scb_decomp (Mark (Pred N) m) (fst sb) (flatBT (Mark (Pred N) m')) (snd sb)
                \<and> scb_decomp (Mark N m) (fst sb) (flatBT (Mark N m')) (snd sb))"
  using y6z_no_common_position[OF core ne] by blast

lemma y6_Lng [simp]:
  "Lng y6B1 = 1" "Lng y6B2 = 2" "Lng y6B3 = 3"
  "Lng y6B4 = 4" "Lng y6B5 = 5" "Lng y6B6 = 6" "Lng y6M = 6"
  by (simp_all add: y6B1_def y6B2_def y6B3_def y6B4_def y6B5_def y6B6_def y6M_def)

lemma y6_TPS [simp]:
  "y6B1 \<in> T_PS" "y6B2 \<in> T_PS" "y6B3 \<in> T_PS"
  "y6B4 \<in> T_PS" "y6B5 \<in> T_PS" "y6B6 \<in> T_PS" "y6M \<in> T_PS"
  by (simp_all add: T_PS_def y6B1_def y6B2_def y6B3_def y6B4_def y6B5_def y6B6_def y6M_def)

lemma y6_Pred:
  "Pred y6B2 = y6B1" "Pred y6B3 = y6B2" "Pred y6B4 = y6B3"
  "Pred y6B5 = y6B4" "Pred y6B6 = y6B5"
  by (simp_all add: Pred_def y6B1_def y6B2_def y6B3_def y6B4_def y6B5_def y6B6_def)

lemma y6_L:
  "1 < Lng y6B2" "1 < Lng y6B3" "1 < Lng y6B4" "1 < Lng y6B5" "1 < Lng y6B6"
  by simp_all


subsection \<open>\<open>\<le>\<^sub>0\<close>, parents and admissibility on the reduct tower\<close>

lemma y6B2_le0: "le0 y6B2 0 1"
proof -
  have "\<forall>j. 0 < j \<longrightarrow> j \<le> 1 \<longrightarrow> entry y6B2 0 0 < entry y6B2 0 j"
  proof (intro allI impI)
    fix j :: nat assume "0 < j" "j \<le> 1"
    hence "j = 1" by linarith
    thus "entry y6B2 0 0 < entry y6B2 0 j" by (simp add: y6B2_def entry_def)
  qed
  thus ?thesis using y3w_le0_iff[of 0 1 y6B2] by simp
qed

lemma y6B3_le0: "le0 y6B3 0 2"
proof -
  have "\<forall>j. 0 < j \<longrightarrow> j \<le> 2 \<longrightarrow> entry y6B3 0 0 < entry y6B3 0 j"
  proof (intro allI impI)
    fix j :: nat assume "0 < j" "j \<le> 2"
    then consider "j=1"|"j=2" by linarith
    thus "entry y6B3 0 0 < entry y6B3 0 j" by cases (simp_all add: y6B3_def entry_def)
  qed
  thus ?thesis using y3w_le0_iff[of 0 2 y6B3] by simp
qed

lemma y6B4_le0: "le0 y6B4 0 3"
proof -
  have "\<forall>j. 0 < j \<longrightarrow> j \<le> 3 \<longrightarrow> entry y6B4 0 0 < entry y6B4 0 j"
  proof (intro allI impI)
    fix j :: nat assume "0 < j" "j \<le> 3"
    then consider "j=1"|"j=2"|"j=3" by linarith
    thus "entry y6B4 0 0 < entry y6B4 0 j" by cases (simp_all add: y6B4_def entry_def)
  qed
  thus ?thesis using y3w_le0_iff[of 0 3 y6B4] by simp
qed

lemma y6B5_le0: "le0 y6B5 0 4"
proof -
  have "\<forall>j. 0 < j \<longrightarrow> j \<le> 4 \<longrightarrow> entry y6B5 0 0 < entry y6B5 0 j"
  proof (intro allI impI)
    fix j :: nat assume "0 < j" "j \<le> 4"
    then consider "j=1"|"j=2"|"j=3"|"j=4" by linarith
    thus "entry y6B5 0 0 < entry y6B5 0 j" by cases (simp_all add: y6B5_def entry_def)
  qed
  thus ?thesis using y3w_le0_iff[of 0 4 y6B5] by simp
qed

lemma y6B6_le0: "le0 y6B6 0 5"
proof -
  have "\<forall>j. 0 < j \<longrightarrow> j \<le> 5 \<longrightarrow> entry y6B6 0 0 < entry y6B6 0 j"
  proof (intro allI impI)
    fix j :: nat assume "0 < j" "j \<le> 5"
    then consider "j=1"|"j=2"|"j=3"|"j=4"|"j=5" by linarith
    thus "entry y6B6 0 0 < entry y6B6 0 j" by cases (simp_all add: y6B6_def entry_def)
  qed
  thus ?thesis using y3w_le0_iff[of 0 5 y6B6] by simp
qed

lemma y6_monoT:
  "monoT y6B2" "monoT y6B3" "monoT y6B4" "monoT y6B5" "monoT y6B6"
  using y6B2_le0 y6B3_le0 y6B4_le0 y6B5_le0 y6B6_le0
  by (simp_all add: monoT_def zeroT_def leR_def)

text \<open>Row-0 parents of the right end.\<close>

lemma y6B3_par: "parent y6B3 0 2 = 0"
proof -
  have K: "\<And>j. nextrel0 y6B3 j 2 \<longleftrightarrow> j = 0"
  proof -
    fix j show "nextrel0 y6B3 j 2 \<longleftrightarrow> j = 0"
    proof
      assume H: "nextrel0 y6B3 j 2"
      hence jl: "j < 2" and lt: "entry y6B3 0 j < entry y6B3 0 2"
        by (simp_all add: nextrel0_def)
      show "j = 0"
      proof (rule ccontr)
        assume "j \<noteq> 0" hence "j = 1" using jl by simp
        thus False using lt by (simp add: y6B3_def entry_def)
      qed
    next
      assume j: "j = 0"
      have bet: "\<forall>j'. 0 < j' \<and> j' < 2 \<longrightarrow> entry y6B3 0 2 \<le> entry y6B3 0 j'"
      proof (intro allI impI)
        fix j' :: nat assume "0 < j' \<and> j' < 2"
        hence "j' = 1" by linarith
        thus "entry y6B3 0 2 \<le> entry y6B3 0 j'" by (simp add: y6B3_def entry_def)
      qed
      show "nextrel0 y6B3 j 2"
        unfolding nextrel0_def using j bet by (simp add: y6B3_def entry_def)
    qed
  qed
  show ?thesis using K by (simp add: parent_def nextR_def)
qed

lemma y6B4_par: "parent y6B4 0 3 = 2"
proof -
  have K: "\<And>j. nextrel0 y6B4 j 3 \<longleftrightarrow> j = 2"
  proof -
    fix j show "nextrel0 y6B4 j 3 \<longleftrightarrow> j = 2"
    proof
      assume H: "nextrel0 y6B4 j 3"
      hence jl: "j < 3"
        and bet: "\<forall>j'. j < j' \<and> j' < 3 \<longrightarrow> entry y6B4 0 3 \<le> entry y6B4 0 j'"
        by (simp_all add: nextrel0_def)
      show "j = 2"
      proof (rule ccontr)
        assume ne: "j \<noteq> 2"
        have "entry y6B4 0 3 \<le> entry y6B4 0 2" using bet jl ne by simp
        thus False by (simp add: y6B4_def entry_def)
      qed
    next
      assume j: "j = 2"
      show "nextrel0 y6B4 j 3"
        unfolding nextrel0_def using j by (simp add: y6B4_def entry_def)
    qed
  qed
  show ?thesis using K by (simp add: parent_def nextR_def)
qed

lemma y6B5_par: "parent y6B5 0 4 = 3"
proof -
  have K: "\<And>j. nextrel0 y6B5 j 4 \<longleftrightarrow> j = 3"
  proof -
    fix j show "nextrel0 y6B5 j 4 \<longleftrightarrow> j = 3"
    proof
      assume H: "nextrel0 y6B5 j 4"
      hence jl: "j < 4"
        and bet: "\<forall>j'. j < j' \<and> j' < 4 \<longrightarrow> entry y6B5 0 4 \<le> entry y6B5 0 j'"
        by (simp_all add: nextrel0_def)
      show "j = 3"
      proof (rule ccontr)
        assume ne: "j \<noteq> 3"
        have "entry y6B5 0 4 \<le> entry y6B5 0 3" using bet jl ne by simp
        thus False by (simp add: y6B5_def entry_def)
      qed
    next
      assume j: "j = 3"
      show "nextrel0 y6B5 j 4"
        unfolding nextrel0_def using j by (simp add: y6B5_def entry_def)
    qed
  qed
  show ?thesis using K by (simp add: parent_def nextR_def)
qed

lemma y6B6_par: "parent y6B6 0 5 = 3"
proof -
  have K: "\<And>j. nextrel0 y6B6 j 5 \<longleftrightarrow> j = 3"
  proof -
    fix j show "nextrel0 y6B6 j 5 \<longleftrightarrow> j = 3"
    proof
      assume H: "nextrel0 y6B6 j 5"
      hence jl: "j < 5" and lt: "entry y6B6 0 j < entry y6B6 0 5"
        and bet: "\<forall>j'. j < j' \<and> j' < 5 \<longrightarrow> entry y6B6 0 5 \<le> entry y6B6 0 j'"
        by (simp_all add: nextrel0_def)
      show "j = 3"
      proof (rule ccontr)
        assume ne: "j \<noteq> 3"
        consider "j = 0" | "j = 1" | "j = 2" | "j = 4" using jl ne by linarith
        thus False
        proof cases
          case 1
          have "entry y6B6 0 5 \<le> entry y6B6 0 3" using bet 1 by simp
          thus False by (simp add: y6B6_def entry_def)
        next
          case 2
          have "entry y6B6 0 5 \<le> entry y6B6 0 3" using bet 2 by simp
          thus False by (simp add: y6B6_def entry_def)
        next
          case 3
          have "entry y6B6 0 5 \<le> entry y6B6 0 3" using bet 3 by simp
          thus False by (simp add: y6B6_def entry_def)
        next
          case 4
          thus False using lt by (simp add: y6B6_def entry_def)
        qed
      qed
    next
      assume j: "j = 3"
      have bet: "\<forall>j'. 3 < j' \<and> j' < 5 \<longrightarrow> entry y6B6 0 5 \<le> entry y6B6 0 j'"
      proof (intro allI impI)
        fix j' :: nat assume "3 < j' \<and> j' < 5"
        hence "j' = 4" by linarith
        thus "entry y6B6 0 5 \<le> entry y6B6 0 j'" by (simp add: y6B6_def entry_def)
      qed
      show "nextrel0 y6B6 j 5"
        unfolding nextrel0_def using j bet by (simp add: y6B6_def entry_def)
    qed
  qed
  show ?thesis using K by (simp add: parent_def nextR_def)
qed

text \<open>The \<open>Lng - 1\<close> forms, in which the \<open>trans*\<close> accessors phrase the parent.\<close>

lemma y6B3_jp: "parent y6B3 0 (Lng y6B3 - 1) = 0" using y6B3_par by simp
lemma y6B4_jp: "parent y6B4 0 (Lng y6B4 - 1) = 2" using y6B4_par by simp
lemma y6B5_jp: "parent y6B5 0 (Lng y6B5 - 1) = 3" using y6B5_par by simp
lemma y6B6_jp: "parent y6B6 0 (Lng y6B6 - 1) = 3" using y6B6_par by simp

subsection \<open>The \<open>T\<^bsub>PS\<^esub>\<close> witness \<open>y6M\<close>, and \<open>Red y6M = y6B6\<close>\<close>

lemma y6M_le0_05: "le0 y6M 0 5"
proof -
  have "\<forall>j. 0 < j \<longrightarrow> j \<le> 5 \<longrightarrow> entry y6M 0 0 < entry y6M 0 j"
  proof (intro allI impI)
    fix j :: nat assume "0 < j" "j \<le> 5"
    then consider "j=1"|"j=2"|"j=3"|"j=4"|"j=5" by linarith
    thus "entry y6M 0 0 < entry y6M 0 j" by cases (simp_all add: y6M_def entry_def)
  qed
  thus ?thesis using y3w_le0_iff[of 0 5 y6M] by simp
qed

lemma y6M_le0_03: "le0 y6M 0 3"
proof -
  have "\<forall>j. 0 < j \<longrightarrow> j \<le> 3 \<longrightarrow> entry y6M 0 0 < entry y6M 0 j"
  proof (intro allI impI)
    fix j :: nat assume "0 < j" "j \<le> 3"
    then consider "j=1"|"j=2"|"j=3" by linarith
    thus "entry y6M 0 0 < entry y6M 0 j" by cases (simp_all add: y6M_def entry_def)
  qed
  thus ?thesis using y3w_le0_iff[of 0 3 y6M] by simp
qed

lemma y6M_le0_35: "le0 y6M 3 5"
proof -
  have "\<forall>j. 3 < j \<longrightarrow> j \<le> 5 \<longrightarrow> entry y6M 0 3 < entry y6M 0 j"
  proof (intro allI impI)
    fix j :: nat assume "3 < j" "j \<le> 5"
    then consider "j=4"|"j=5" by linarith
    thus "entry y6M 0 3 < entry y6M 0 j" by cases (simp_all add: y6M_def entry_def)
  qed
  thus ?thesis using y3w_le0_iff[of 3 5 y6M] by simp
qed

lemma y6M_le0_02: "le0 y6M 0 2"
proof -
  have "\<forall>j. 0 < j \<longrightarrow> j \<le> 2 \<longrightarrow> entry y6M 0 0 < entry y6M 0 j"
  proof (intro allI impI)
    fix j :: nat assume "0 < j" "j \<le> 2"
    then consider "j=1"|"j=2" by linarith
    thus "entry y6M 0 0 < entry y6M 0 j" by cases (simp_all add: y6M_def entry_def)
  qed
  thus ?thesis using y3w_le0_iff[of 0 2 y6M] by simp
qed

lemma y6M_nle0_45: "\<not> le0 y6M 4 5"
proof
  assume "le0 y6M 4 5"
  hence "\<forall>j. 4 < j \<longrightarrow> j \<le> 5 \<longrightarrow> entry y6M 0 4 < entry y6M 0 j"
    using y3w_le0_iff[of 4 5 y6M] by simp
  hence "entry y6M 0 4 < entry y6M 0 5" by simp
  thus False by (simp add: y6M_def entry_def)
qed

lemma y6M_nle0_12: "\<not> le0 y6M 1 2"
proof
  assume "le0 y6M 1 2"
  hence "\<forall>j. 1 < j \<longrightarrow> j \<le> 2 \<longrightarrow> entry y6M 0 1 < entry y6M 0 j"
    using y3w_le0_iff[of 1 2 y6M] by simp
  hence "entry y6M 0 1 < entry y6M 0 2" by simp
  thus False by (simp add: y6M_def entry_def)
qed

lemma y6M_monoT: "monoT y6M"
  using y6M_le0_05 by (simp add: monoT_def zeroT_def leR_def)

lemma y6M_nmulti: "\<not> multiT y6M" using y6M_monoT by (simp add: multiT_def)
lemma y6M_nzero: "\<not> zeroT y6M" by (simp add: zeroT_def)

text \<open>\<^bold>\<open>All six columns of \<open>y6M\<close> are \<open>y6M\<close>-admissible\<close> --- this is precisely what the
  reduct destroys at column 3.\<close>

lemma y6M_adm: "j < 6 \<Longrightarrow> adm y6M j"
proof -
  assume j: "j < 6"
  consider "j=0"|"j=1"|"j=2"|"j=3"|"j=4"|"j=5" using j by linarith
  thus "adm y6M j"
  proof cases
    case 1 thus ?thesis by (simp add: y3w_adm_0)
  next
    case 2
    have "\<not> nadm y6M 1"
      using y3w_nadm_local[of 1 y6M] by (simp add: y6M_def entry_def)
    thus ?thesis using 2 by (simp add: adm_def)
  next
    case 3
    have "\<not> nadm y6M 2"
      using y3w_nadm_local[of 2 y6M] by (simp add: y6M_def entry_def)
    thus ?thesis using 3 by (simp add: adm_def)
  next
    case 4
    have "\<not> nadm y6M 3"
      using y3w_nadm_local[of 3 y6M] by (simp add: y6M_def entry_def)
    thus ?thesis using 4 by (simp add: adm_def)
  next
    case 5
    have "\<not> nadm y6M 4"
      using y3w_nadm_local[of 4 y6M] by (simp add: y6M_def entry_def)
    thus ?thesis using 5 by (simp add: adm_def)
  next
    case 6 thus ?thesis using y3x_adm_last[of 5 y6M] by simp
  qed
qed

lemma y6M_adm3: "adm y6M 3" using y6M_adm[of 3] by simp

lemma y6M_TrMax: "TrMax y6M = 1"
proof (rule TrMax_eqI_endpoint[OF y6_TPS(7)])
  fix j' :: nat assume "j' < 1"
  hence z: "j' = 0" by simp
  have "nextrel1 y6M 0 (Suc 0)"
    using y3w_nextrel1_adj[of 0 y6M] by (simp add: y6M_def entry_def)
  thus "nextR y6M 1 j' (j' + 1)" using z by (simp add: nextR_def)
next
  have "\<not> nextrel1 y6M 1 (Suc 1)"
    using y3w_nextrel1_adj[of 1 y6M] by (simp add: y6M_def entry_def)
  thus "1 = Lng y6M - 1 \<or> \<not> nextR y6M 1 1 (1 + 1)" by (simp add: nextR_def)
qed

lemma y6M_seg25: "seg y6M 2 5 = [(2,6),(4,2),(8,4),(6,4)]"
  by (simp add: seg_def y6M_def eval_nat_numeral)

lemma y6M_branch_monoT: "monoT [(2::nat,6::nat),(4,2),(8,4),(6,4)]"
proof -
  let ?S = "[(2::nat,6::nat),(4,2),(8,4),(6,4)]"
  have H: "\<forall>j. 0 < j \<longrightarrow> j \<le> 3 \<longrightarrow> entry ?S 0 0 < entry ?S 0 j"
  proof (intro allI impI)
    fix j :: nat assume "0 < j" "j \<le> 3"
    then consider "j=1"|"j=2"|"j=3" by linarith
    thus "entry ?S 0 0 < entry ?S 0 j" by cases (simp_all add: entry_def)
  qed
  have iff: "le0 ?S 0 3 \<longleftrightarrow> (\<forall>j. 0 < j \<longrightarrow> j \<le> 3 \<longrightarrow> entry ?S 0 0 < entry ?S 0 j)"
    by (rule y3w_le0_iff) simp_all
  have le: "le0 ?S 0 3" using iff H by blast
  have Lm: "Lng ?S - 1 = 3" by simp
  have le': "le0 ?S 0 (Lng ?S - 1)" unfolding Lm by (rule le)
  have nz: "\<not> zeroT ?S" by (simp add: zeroT_def)
  show ?thesis using nz le' by (simp add: monoT_def leR_def)
qed

lemma y6M_Br: "Br y6M = [[(2,6),(4,2),(8,4),(6,4)]]"
proof -
  let ?S = "[(2::nat,6::nat),(4,2),(8,4),(6,4)]"
  have tne: "TrMax y6M \<noteq> Lng y6M - 1" using y6M_TrMax by simp
  have ST: "?S \<in> T_PS" by (simp add: T_PS_def)
  have nm: "\<not> multiT ?S" using y6M_branch_monoT by (simp add: multiT_def)
  have b: "Br y6M = P (seg y6M (TrMax y6M + 1) (Lng y6M - 1))"
    using tne by (simp add: Br_def)
  have tm: "TrMax y6M + 1 = 2" using y6M_TrMax by simp
  have lm: "Lng y6M - 1 = 5" by simp
  have s: "seg y6M (TrMax y6M + 1) (Lng y6M - 1) = ?S"
    unfolding tm lm by (rule y6M_seg25)
  have "Br y6M = P ?S" using b s by simp
  also have "\<dots> = [?S]" by (rule y3r_P_nonmulti[OF ST nm])
  finally show ?thesis .
qed

lemma y6M_LngBr [simp]: "Lng (Br y6M) = 1" using y6M_Br by simp

lemma y6M_FirstNodes: "FirstNodes y6M ! 0 = 2"
proof -
  have "FirstNodes y6M ! 0 = TrMax y6M + 1 + IdxSum (Br y6M) ! 0"
    by (rule FirstNodes_nth) (simp add: y6M_Br)
  also have "\<dots> = 2" using y6M_TrMax by (simp add: y6M_Br IdxSum_def)
  finally show ?thesis .
qed

lemma y6M_nx0_2: "nextrel0 y6M j 2 \<longleftrightarrow> j = 0"
proof
  assume H: "nextrel0 y6M j 2"
  hence jl: "j < 2" and lt: "entry y6M 0 j < entry y6M 0 2"
    by (simp_all add: nextrel0_def)
  show "j = 0"
  proof (rule ccontr)
    assume "j \<noteq> 0" hence "j = 1" using jl by simp
    thus False using lt by (simp add: y6M_def entry_def)
  qed
next
  assume j: "j = 0"
  have bet: "\<forall>j'. 0 < j' \<and> j' < 2 \<longrightarrow> entry y6M 0 2 \<le> entry y6M 0 j'"
  proof (intro allI impI)
    fix j' :: nat assume "0 < j' \<and> j' < 2"
        hence "j' = 1" by linarith
    thus "entry y6M 0 2 \<le> entry y6M 0 j'" by (simp add: y6M_def entry_def)
  qed
  show "nextrel0 y6M j 2"
    unfolding nextrel0_def using j bet by (simp add: y6M_def entry_def)
qed

lemma y6M_Joints: "Joints y6M ! 0 = 0"
proof -
  have "Joints y6M ! 0 = (THE j. nextR y6M 0 j (FirstNodes y6M ! 0))"
    by (simp add: Joints_def y6M_Br)
  also have "\<dots> = (THE j. nextrel0 y6M j 2)"
    using y6M_FirstNodes by (simp add: nextR_def)
  also have "\<dots> = 0" using y6M_nx0_2 by auto
  finally show ?thesis .
qed

lemma y6M_nx1_2: "nextrel1 y6M j 2 \<longleftrightarrow> j = 0"
proof
  assume H: "nextrel1 y6M j 2"
  hence jl: "j < 2" and le: "le0 y6M j 2" by (simp_all add: nextrel1_def)
  show "j = 0"
  proof (rule ccontr)
    assume "j \<noteq> 0" hence "j = 1" using jl by simp
    thus False using le y6M_nle0_12 by simp
  qed
next
  assume j: "j = 0"
  have bet: "\<forall>j'. 0 < j' \<and> le0 y6M j' 2 \<longrightarrow> entry y6M 1 2 \<le> entry y6M 1 j'"
  proof (intro allI impI)
    fix j' assume hj: "0 < j' \<and> le0 y6M j' 2"
    hence "j' \<le> 2" using y3w_le0_bounds by blast
    hence "j' = 1 \<or> j' = 2" using hj by linarith
    thus "entry y6M 1 2 \<le> entry y6M 1 j'"
      using hj y6M_nle0_12 by (auto simp: y6M_def entry_def)
  qed
  show "nextrel1 y6M j 2"
    unfolding nextrel1_def using j y6M_le0_02 bet by (simp add: y6M_def entry_def)
qed

lemma y6M_npJ: "npJ y6M 0 = 1"
proof -
  have b: "entry (Br y6M ! 0) 1 0 = 6" using y6M_Br by (simp add: entry_def)
  have "npJ y6M 0 = Suc (THE j. nextR y6M 1 j (FirstNodes y6M ! 0))"
    using b by (simp add: npJ_def)
  also have "\<dots> = Suc (THE j. nextrel1 y6M j 2)"
    using y6M_FirstNodes by (simp add: nextR_def)
  also have "\<dots> = 1" using y6M_nx1_2 by auto
  finally show ?thesis .
qed

lemma y6M_NJ: "NJ y6M 0 = [(1,1),(4,2),(8,4),(6,4)]"
  using y6M_Joints y6M_npJ y6M_Br by (simp add: NJ_def y6M_def entry_def)

text \<open>The rebase argument, a core-nontrunk sequence whose own single branch is the
  reduced one-column \<open>[(3,3)]\<close>.\<close>

lemma y6_redNarg:
  "Red [(0,0),(2,1),(5,2),(9,4),(7,4)] = [(0,0),(1,1),(2,2),(3,3),(3,3)]"
proof -
  let ?A = "[(0::nat,0::nat),(2,1),(5,2),(9,4),(7,4)]"
  have AT: "?A \<in> T_PS" by (simp add: T_PS_def)
  have LA: "Lng ?A = 5" by simp
  have H: "\<forall>j. 0 < j \<longrightarrow> j \<le> 4 \<longrightarrow> entry ?A 0 0 < entry ?A 0 j"
  proof (intro allI impI)
    fix j :: nat assume "0 < j" "j \<le> 4"
    then consider "j=1"|"j=2"|"j=3"|"j=4" by linarith
    thus "entry ?A 0 0 < entry ?A 0 j" by cases (simp_all add: entry_def)
  qed
  have iff: "le0 ?A 0 4 \<longleftrightarrow> (\<forall>j. 0 < j \<longrightarrow> j \<le> 4 \<longrightarrow> entry ?A 0 0 < entry ?A 0 j)"
    by (rule y3w_le0_iff) (simp_all add: LA)
  have le04: "le0 ?A 0 4" using iff H by blast
  have Lm: "Lng ?A - 1 = 4" using LA by simp
  have leA: "le0 ?A 0 (Lng ?A - 1)" unfolding Lm by (rule le04)
  have nz: "\<not> zeroT ?A" by (simp add: zeroT_def)
  have mono: "monoT ?A" using nz leA by (simp add: monoT_def leR_def)
  have nmu: "\<not> multiT ?A" using mono by (simp add: multiT_def)
  have c0: "entry ?A 0 0 = 0" by (simp add: entry_def)
  have c1: "entry ?A 1 0 = 0" by (simp add: entry_def)
  have TA: "TrMax ?A = 3"
  proof (rule TrMax_eqI_endpoint[OF AT])
    fix j' :: nat assume "j' < 3"
    then consider "j'=0"|"j'=1"|"j'=2" by linarith
    hence "nextrel1 ?A j' (Suc j')"
    proof cases
      case 1 thus ?thesis using y3w_nextrel1_adj[of 0 ?A] by (simp add: entry_def)
    next
      case 2 thus ?thesis using y3w_nextrel1_adj[of 1 ?A] by (simp add: entry_def)
    next
      case 3 thus ?thesis using y3w_nextrel1_adj[of 2 ?A] by (simp add: entry_def)
    qed
    thus "nextR ?A 1 j' (j' + 1)" by (simp add: nextR_def)
  next
    have "\<not> nextrel1 ?A 3 (Suc 3)"
      using y3w_nextrel1_adj[of 3 ?A] by (simp add: entry_def)
    thus "3 = Lng ?A - 1 \<or> \<not> nextR ?A 1 3 (3 + 1)" using LA by (simp add: nextR_def)
  qed
  have tne: "TrMax ?A \<noteq> Lng ?A - 1" using TA LA by simp
  have segA: "seg ?A 4 4 = [(7,4)]" by (simp add: seg_def eval_nat_numeral)
  have BT7: "[(7::nat,4::nat)] \<in> T_PS" by (simp add: T_PS_def)
  have nz7: "\<not> zeroT [(7::nat,4::nat)]" by (simp add: zeroT_def entry_def)
  have mono7: "monoT [(7::nat,4::nat)]"
  proof -
    have "le0 [(7::nat,4::nat)] 0 0" by (simp add: le0_def)
    thus ?thesis using nz7 by (simp add: monoT_def leR_def)
  qed
  have nm7: "\<not> multiT [(7::nat,4::nat)]" using mono7 by (simp add: multiT_def)
  have BrA: "Br ?A = [[(7,4)]]"
  proof -
    have b: "Br ?A = P (seg ?A (TrMax ?A + 1) (Lng ?A - 1))"
      using tne by (simp add: Br_def)
    have tmA: "TrMax ?A + 1 = 4" using TA by simp
    have lmA: "Lng ?A - 1 = 4" using LA by simp
    have s: "seg ?A (TrMax ?A + 1) (Lng ?A - 1) = [(7,4)]"
      unfolding tmA lmA by (rule segA)
    have "Br ?A = P [(7,4)]" using b s by simp
    also have "\<dots> = [[(7,4)]]" by (rule y3r_P_nonmulti[OF BT7 nm7])
    finally show ?thesis .
  qed
  have LBrA [simp]: "Lng (Br ?A) = 1" unfolding BrA by simp
  have lenA: "(0::nat) < length (Br ?A)" unfolding BrA by simp
  have FNA: "FirstNodes ?A ! 0 = 4"
  proof -
    have "FirstNodes ?A ! 0 = TrMax ?A + 1 + IdxSum (Br ?A) ! 0"
      by (rule FirstNodes_nth[OF lenA])
    also have "\<dots> = 4" unfolding BrA TA by (simp add: IdxSum_def)
    finally show ?thesis .
  qed
  have nx0: "\<And>j. nextrel0 ?A j 4 \<longleftrightarrow> j = 2"
  proof -
    fix j show "nextrel0 ?A j 4 \<longleftrightarrow> j = 2"
    proof
      assume Hh: "nextrel0 ?A j 4"
      hence jl: "j < 4" and lt: "entry ?A 0 j < entry ?A 0 4"
        and bet: "\<forall>j'. j < j' \<and> j' < 4 \<longrightarrow> entry ?A 0 4 \<le> entry ?A 0 j'"
        by (simp_all add: nextrel0_def)
      show "j = 2"
      proof (rule ccontr)
        assume ne: "j \<noteq> 2"
        consider "j=0"|"j=1"|"j=3" using jl ne by linarith
        thus False
        proof cases
          case 1
          have "entry ?A 0 4 \<le> entry ?A 0 1" using bet 1 by simp
          thus False by (simp add: entry_def)
        next
          case 2
          have "entry ?A 0 4 \<le> entry ?A 0 2" using bet 2 by simp
          thus False by (simp add: entry_def)
        next
          case 3
          thus False using lt by (simp add: entry_def)
        qed
      qed
    next
      assume j: "j = 2"
      have bet: "\<forall>j'. 2 < j' \<and> j' < 4 \<longrightarrow> entry ?A 0 4 \<le> entry ?A 0 j'"
      proof (intro allI impI)
        fix j' :: nat assume "2 < j' \<and> j' < 4"
        hence "j' = 3" by linarith
        thus "entry ?A 0 4 \<le> entry ?A 0 j'" by (simp add: entry_def)
      qed
      show "nextrel0 ?A j 4"
        unfolding nextrel0_def using j bet by (simp add: entry_def)
    qed
  qed
  have JA: "Joints ?A ! 0 = 2"
  proof -
    have "Joints ?A ! 0 = (THE j. nextR ?A 0 j (FirstNodes ?A ! 0))"
      unfolding Joints_def BrA by simp
    also have "\<dots> = (THE j. nextrel0 ?A j 4)" using FNA by (simp add: nextR_def)
    also have "\<dots> = 2" using nx0 by auto
    finally show ?thesis .
  qed
  have le24: "le0 ?A 2 4"
  proof -
    have Hh: "\<forall>j. 2 < j \<longrightarrow> j \<le> 4 \<longrightarrow> entry ?A 0 2 < entry ?A 0 j"
    proof (intro allI impI)
      fix j :: nat assume "2 < j" "j \<le> 4"
      then consider "j=3"|"j=4" by linarith
      thus "entry ?A 0 2 < entry ?A 0 j" by cases (simp_all add: entry_def)
    qed
    have iff2: "le0 ?A 2 4 \<longleftrightarrow> (\<forall>j. 2 < j \<longrightarrow> j \<le> 4 \<longrightarrow> entry ?A 0 2 < entry ?A 0 j)"
      by (rule y3w_le0_iff) (simp_all add: LA)
    show ?thesis using iff2 Hh by blast
  qed
  have le14: "le0 ?A 1 4"
  proof -
    have Hh: "\<forall>j. 1 < j \<longrightarrow> j \<le> 4 \<longrightarrow> entry ?A 0 1 < entry ?A 0 j"
    proof (intro allI impI)
      fix j :: nat assume "1 < j" "j \<le> 4"
      then consider "j=2"|"j=3"|"j=4" by linarith
      thus "entry ?A 0 1 < entry ?A 0 j" by cases (simp_all add: entry_def)
    qed
    have iff2: "le0 ?A 1 4 \<longleftrightarrow> (\<forall>j. 1 < j \<longrightarrow> j \<le> 4 \<longrightarrow> entry ?A 0 1 < entry ?A 0 j)"
      by (rule y3w_le0_iff) (simp_all add: LA)
    show ?thesis using iff2 Hh by blast
  qed
  have nle34: "\<not> le0 ?A 3 4"
  proof
    assume "le0 ?A 3 4"
    hence "\<forall>j. 3 < j \<longrightarrow> j \<le> 4 \<longrightarrow> entry ?A 0 3 < entry ?A 0 j"
      using y3w_le0_iff[of 3 4 ?A] LA by simp
    hence "entry ?A 0 3 < entry ?A 0 4" by simp
    thus False by (simp add: entry_def)
  qed
  have nx1: "\<And>j. nextrel1 ?A j 4 \<longleftrightarrow> j = 2"
  proof -
    fix j show "nextrel1 ?A j 4 \<longleftrightarrow> j = 2"
    proof
      assume Hh: "nextrel1 ?A j 4"
      hence jl: "j < 4" and lt: "entry ?A 1 j < entry ?A 1 4"
        and bet: "\<forall>j'. j < j' \<and> le0 ?A j' 4 \<longrightarrow> entry ?A 1 4 \<le> entry ?A 1 j'"
        by (simp_all add: nextrel1_def)
      show "j = 2"
      proof (rule ccontr)
        assume ne: "j \<noteq> 2"
        consider "j=0"|"j=1"|"j=3" using jl ne by linarith
        thus False
        proof cases
          case 1
          have "entry ?A 1 4 \<le> entry ?A 1 1" using bet le14 1 by simp
          thus False by (simp add: entry_def)
        next
          case 2
          have "entry ?A 1 4 \<le> entry ?A 1 2" using bet le24 2 by simp
          thus False by (simp add: entry_def)
        next
          case 3
          thus False using lt by (simp add: entry_def)
        qed
      qed
    next
      assume j: "j = 2"
      have bet: "\<forall>j'. 2 < j' \<and> le0 ?A j' 4 \<longrightarrow> entry ?A 1 4 \<le> entry ?A 1 j'"
      proof (intro allI impI)
        fix j' assume hj: "2 < j' \<and> le0 ?A j' 4"
        hence "j' \<le> 4" using y3w_le0_bounds by blast
        hence "j' = 3 \<or> j' = 4" using hj by linarith
        thus "entry ?A 1 4 \<le> entry ?A 1 j'" using hj nle34 by (auto simp: entry_def)
      qed
      show "nextrel1 ?A j 4"
        unfolding nextrel1_def using j le24 bet LA by (simp add: entry_def)
    qed
  qed
  have npA: "npJ ?A 0 = 3"
  proof -
    have b: "entry (Br ?A ! 0) 1 0 = 4" unfolding BrA by (simp add: entry_def)
    have "npJ ?A 0 = Suc (THE j. nextR ?A 1 j (FirstNodes ?A ! 0))"
      using b by (simp add: npJ_def)
    also have "\<dots> = Suc (THE j. nextrel1 ?A j 4)" using FNA by (simp add: nextR_def)
    also have "\<dots> = 3" using nx1 by auto
    finally show ?thesis .
  qed
  have NJA: "NJ ?A 0 = [(3,3)]"
    using JA npA unfolding NJ_def BrA by (simp add: entry_def)
  have R33: "Red [(3,3)] = [(3::nat,3::nat)]"
  proof -
    have "([(3::nat,3::nat)]) \<in> T_PS" by (simp add: T_PS_def)
    hence "[(3::nat,3::nat)] \<in> RT_PS"
      using m_6_6_oneColumn[of "[(3::nat,3::nat)]"] by auto
    thus ?thesis by (simp add: RT_PS_def)
  qed
  have "Red ?A = diagSeq 0 (TrMax ?A)
          @ concat (map (\<lambda>J. (IncrFirst ^^ (Joints ?A ! J + 1 - npJ ?A J))
                                 (Red (NJ ?A J)))
                    [0..<Lng (Br ?A)])"
    by (rule d_Red_core_nontrunk_unfold[OF AT nz nmu c0 c1 tne])
  also have "\<dots> = diagSeq 0 3 @ (IncrFirst ^^ 0) (Red (NJ ?A 0))"
    using TA JA npA unfolding LBrA by simp
  also have "\<dots> = diagSeq 0 3 @ [(3,3)]" using NJA R33 by simp
  also have "\<dots> = [(0,0),(1,1),(2,2),(3,3),(3,3)]"
    by (simp add: diagSeq_def eval_nat_numeral)
  finally show ?thesis .
qed

lemma y6_redNJ: "Red [(1,1),(4,2),(8,4),(6,4)] = [(1,1),(2,2),(3,3),(3,3)]"
proof -
  let ?B = "[(1::nat,1::nat),(4,2),(8,4),(6,4)]"
  let ?N = "[(0::nat,0::nat),(1,1),(2,2),(3,3),(3,3)]"
  have BT: "?B \<in> T_PS" by (simp add: T_PS_def)
  have LB: "Lng ?B = 4" by simp
  have H: "\<forall>j. 0 < j \<longrightarrow> j \<le> 3 \<longrightarrow> entry ?B 0 0 < entry ?B 0 j"
  proof (intro allI impI)
    fix j :: nat assume "0 < j" "j \<le> 3"
    then consider "j=1"|"j=2"|"j=3" by linarith
    thus "entry ?B 0 0 < entry ?B 0 j" by cases (simp_all add: entry_def)
  qed
  have iff: "le0 ?B 0 3 \<longleftrightarrow> (\<forall>j. 0 < j \<longrightarrow> j \<le> 3 \<longrightarrow> entry ?B 0 0 < entry ?B 0 j)"
    by (rule y3w_le0_iff) (simp_all add: LB)
  have le03: "le0 ?B 0 3" using iff H by blast
  have LmB: "Lng ?B - 1 = 3" using LB by simp
  have leB: "le0 ?B 0 (Lng ?B - 1)" unfolding LmB by (rule le03)
  have nz: "\<not> zeroT ?B" by (simp add: zeroT_def)
  have mono: "monoT ?B" using nz leB by (simp add: monoT_def leR_def)
  have nmu: "\<not> multiT ?B" using mono by (simp add: multiT_def)
  have m00: "entry ?B 0 0 = 1" by (simp add: entry_def)
  have m10: "entry ?B 1 0 = 1" by (simp add: entry_def)
  have nc: "\<not> (entry ?B 0 0 = 0 \<and> entry ?B 1 0 = 0)" using m00 by simp
  have c1p: "0 < entry ?B 1 0" using m10 by simp
  have dom: "Red_dom ?B" by (rule m_6_5_Red_welldef[OF BT])
  have argeq: "diagSeq 0 (entry ?B 1 0 - 1) @ (IncrFirst ^^ entry ?B 1 0) ?B
                 = [(0,0),(2,1),(5,2),(9,4),(7,4)]"
    using m10 by (simp add: diagSeq_def IncrFirst_def)
  have Neq: "Red (diagSeq 0 (entry ?B 1 0 - 1) @ (IncrFirst ^^ entry ?B 1 0) ?B) = ?N"
    unfolding argeq by (rule y6_redNarg)
  have LN: "Lng ?N = 5" by simp
  have segN: "seg ?N 1 4 = [(1,1),(2,2),(3,3),(3,3)]"
    by (simp add: seg_def eval_nat_numeral)
  have segPT: "seg ?N (entry ?B 1 0) (Lng ?N - 1) \<in> PT_PS"
  proof -
    let ?S = "[(1::nat,1::nat),(2,2),(3,3),(3,3)]"
    have ST: "?S \<in> T_PS" by (simp add: T_PS_def)
    have Hs: "\<forall>j. 0 < j \<longrightarrow> j \<le> 3 \<longrightarrow> entry ?S 0 0 < entry ?S 0 j"
    proof (intro allI impI)
      fix j :: nat assume "0 < j" "j \<le> 3"
    then consider "j=1"|"j=2"|"j=3" by linarith
      thus "entry ?S 0 0 < entry ?S 0 j" by cases (simp_all add: entry_def)
    qed
    have iffs: "le0 ?S 0 3 \<longleftrightarrow> (\<forall>j. 0 < j \<longrightarrow> j \<le> 3 \<longrightarrow> entry ?S 0 0 < entry ?S 0 j)"
      by (rule y3w_le0_iff) simp_all
    have le3: "le0 ?S 0 3" using iffs Hs by blast
    have LmS: "Lng ?S - 1 = 3" by simp
    have leS: "le0 ?S 0 (Lng ?S - 1)" unfolding LmS by (rule le3)
    have nzS: "\<not> zeroT ?S" by (simp add: zeroT_def)
    have monoS: "monoT ?S" using nzS leS by (simp add: monoT_def leR_def)
    have LNm: "Lng ?N - 1 = 4" using LN by simp
    have seq: "seg ?N (entry ?B 1 0) (Lng ?N - 1) = ?S"
      unfolding m10 LNm by (rule segN)
    show ?thesis unfolding seq using ST monoS by (simp add: PT_PS_def)
  qed
  have cond: "entry ?B 1 0 \<le> Lng ?N - 1 \<and> seg ?N (entry ?B 1 0) (Lng ?N - 1) \<in> PT_PS"
    using m10 LN segPT by simp
  have "Red ?B = map (\<lambda>j. (entry ?N 0 j - entry ?N 0 (entry ?B 1 0)
                              + entry ?N 1 (entry ?B 1 0), entry ?N 1 j))
                     [entry ?B 1 0..<Suc (Lng ?N - 1)]"
    using Red.psimps[OF dom] nz nmu nc c1p Neq cond by (simp add: Let_def)
  also have "\<dots> = [(1,1),(2,2),(3,3),(3,3)]"
    using m10 LN by (simp add: entry_def eval_nat_numeral)
  finally show ?thesis .
qed

lemma y6M_Red: "Red y6M = y6B6"
proof -
  have tne: "TrMax y6M \<noteq> Lng y6M - 1" using y6M_TrMax by simp
  have c0: "entry y6M 0 0 = 0" by (simp add: y6M_def entry_def)
  have c1: "entry y6M 1 0 = 0" by (simp add: y6M_def entry_def)
  have "Red y6M = diagSeq 0 (TrMax y6M)
          @ concat (map (\<lambda>J. (IncrFirst ^^ (Joints y6M ! J + 1 - npJ y6M J))
                                 (Red (NJ y6M J)))
                    [0..<Lng (Br y6M)])"
    by (rule d_Red_core_nontrunk_unfold[OF y6_TPS(7) y6M_nzero y6M_nmulti c0 c1 tne])
  also have "\<dots> = diagSeq 0 1 @ (IncrFirst ^^ 0) (Red (NJ y6M 0))"
    using y6M_TrMax y6M_Joints y6M_npJ by simp
  also have "\<dots> = diagSeq 0 1 @ [(1,1),(2,2),(3,3),(3,3)]"
    using y6M_NJ y6_redNJ by simp
  also have "\<dots> = y6B6" by (simp add: diagSeq_def y6B6_def eval_nat_numeral)
  finally show ?thesis .
qed

lemma y6B6_RT: "y6B6 \<in> RT_PS"
proof -
  have PM: "P y6M = [y6M]" by (rule y3r_P_nonmulti[OF y6_TPS(7) y6M_nmulti])
  have diag: "\<forall>I < length (P y6M). entry (P y6M ! I) 0 0 = entry (P y6M ! I) 1 0"
    using PM by (simp add: y6M_def entry_def)
  have "Red y6M \<in> RT_PS" by (rule y3r_Red_reduced_of_diag[OF y6_TPS(7) diag])
  thus ?thesis using y6M_Red by simp
qed

lemma y6B5_RT: "y6B5 \<in> RT_PS" using Pred_RT_PS[OF y6B6_RT] y6_Pred(5) by simp
lemma y6B4_RT: "y6B4 \<in> RT_PS" using Pred_RT_PS[OF y6B5_RT] y6_Pred(4) by simp
lemma y6B3_RT: "y6B3 \<in> RT_PS" using Pred_RT_PS[OF y6B4_RT] y6_Pred(3) by simp
lemma y6B2_RT: "y6B2 \<in> RT_PS" using Pred_RT_PS[OF y6B3_RT] y6_Pred(2) by simp


subsection \<open>Evaluating \<open>Trans\<close> and \<open>Mark\<close> up the tower\<close>

lemma y6_Trans_B1: "Trans y6B1 = 0\<^sub>B"
  using Trans_singleton[of 0] by (simp add: y6B1_def)

lemma y6_Trans_B2: "Trans y6B2 = Dpt 0 (Dpt (enat 1) 0\<^sub>B)"
proof -
  have t1z: "Trans (Pred y6B2) = 0\<^sub>B" using y6_Pred(1) y6_Trans_B1 by simp
  have "Trans y6B2 = Dpt 0 (Dpt (enat (entry y6B2 1 (Lng y6B2 - 1))) 0\<^sub>B)"
    by (rule y6x_Trans_t1z[OF y6B2_RT y6_L(1) y6_monoT(1) t1z])
  thus ?thesis by (simp add: y6B2_def entry_def)
qed

lemma y6_Mark_B2:
  "Mark y6B2 m = (if m = 0 then Dpt 0 (Dpt (enat 1) 0\<^sub>B) else Dpt (enat 1) 0\<^sub>B)"
proof -
  have t1z: "Trans (Pred y6B2) = 0\<^sub>B" using y6_Pred(1) y6_Trans_B1 by simp
  have "Mark y6B2 m = (if m = 0 then Dpt 0 (Dpt (enat (entry y6B2 1 (Lng y6B2 - 1))) 0\<^sub>B)
                       else Dpt (enat (entry y6B2 1 (Lng y6B2 - 1))) 0\<^sub>B)"
    by (rule y6x_Mark_t1z[OF y6B2_RT y6_L(1) y6_monoT(1) t1z])
  thus ?thesis by (simp add: y6B2_def entry_def)
qed

lemma y6_Mark_B2_0: "Mark y6B2 0 = Dpt 0 (Dpt (enat 1) 0\<^sub>B)" using y6_Mark_B2 by simp

text \<open>\<^bold>\<open>Level 3.\<close>  \<open>j\<^sub>0 = 0\<close> (admissible), \<open>c\<^sub>1 = Mark y6B2 0 = t\<^sub>1\<close>: the scb position is
  the trivial \<open>([],[])\<close>, so \<open>Trans y6B3 = Mark y6B3 0 = c\<^sub>2\<close>.  Condition (V).\<close>

lemma y6B3_c1: "transC1 y6B3 = Dpt 0 (Dpt (enat 1) 0\<^sub>B)"
proof -
  have "transC1 y6B3 = Mark (Pred y6B3) (Adm y6B3 (parent y6B3 0 (Lng y6B3 - 1)))"
    by (simp add: transC1_def transJm1_def transJ0_def transJ1_def)
  also have "\<dots> = Mark y6B2 (Adm y6B3 0)" using y6B3_jp y6_Pred(2) by simp
  also have "\<dots> = Mark y6B2 0" using y6B3_Adm0 by simp
  also have "\<dots> = Dpt 0 (Dpt (enat 1) 0\<^sub>B)" by (rule y6_Mark_B2_0)
  finally show ?thesis .
qed

lemma y6B3_condV: "transCondV y6B3"
  unfolding transCondV_def y6B3_jp by (simp add: y6B3_def entry_def)

lemma y6B3_c2: "transC2 y6B3 = Dpt 0 (Trm [DB (enat 1) 0\<^sub>B, DB (enat 1) 0\<^sub>B])"
proof -
  have v: "transV y6B3 = 0" using y6B3_c1 by (simp add: transV_def)
  have t2: "transT2 y6B3 = Dpt (enat 1) 0\<^sub>B" using y6B3_c1 by (simp add: transT2_def)
  have e1: "entry y6B3 1 (transJ1 y6B3) = 1"
    by (simp add: transJ1_def y6B3_def entry_def)
  show ?thesis
    using y6B3_condV v t2 e1 unfolding transC2_def Let_def by simp
qed

lemma y6_Trans_B3: "Trans y6B3 = Dpt 0 (Trm [DB (enat 1) 0\<^sub>B, DB (enat 1) 0\<^sub>B])"
proof -
  have t1: "Trans (Pred y6B3) = Dpt 0 (Dpt (enat 1) 0\<^sub>B)"
    using y6_Pred(2) y6_Trans_B2 by simp
  have t1ne: "Trans (Pred y6B3) \<noteq> 0\<^sub>B" using t1 by simp
  have self0: "scb_decomp (Trans (Pred y6B3)) [] (flatBT (Dpt 0 (Dpt (enat 1) 0\<^sub>B))) []"
    by (rule y6x_scb_self[OF t1]) simp_all
  have self: "scb_decomp (Trans (Pred y6B3)) [] (flatBT (transC1 y6B3)) []"
    using self0 y6B3_c1 by simp
  have some: "(SOME sb. scb_decomp (Trans (Pred y6B3)) (fst sb)
                          (flatBT (transC1 y6B3)) (snd sb)) = ([], [])"
    by (rule y6x_SOME_scb[OF self t1ne])
  have "Trans y6B3 = unflatBT ([] @ flatBT (transC2 y6B3) @ [])"
    using y6x_Trans_surg[OF y6B3_RT y6_L(2) y6_monoT(2) t1ne] some by simp
  also have "\<dots> = transC2 y6B3" using unflatBT_flat by simp
  finally show ?thesis using y6B3_c2 by simp
qed

lemma y6_Mark_B3_0: "Mark y6B3 0 = Dpt 0 (Trm [DB (enat 1) 0\<^sub>B, DB (enat 1) 0\<^sub>B])"
proof -
  have t1ne: "Trans (Pred y6B3) \<noteq> 0\<^sub>B" using y6_Pred(2) y6_Trans_B2 by simp
  have c0: "Mark (Pred y6B3) 0 = Dpt 0 (Dpt (enat 1) 0\<^sub>B)"
    using y6_Pred(2) y6_Mark_B2_0 by simp
  have c0ne: "Mark (Pred y6B3) 0 \<noteq> 0\<^sub>B" using c0 by simp
  have self0: "scb_decomp (Mark (Pred y6B3) 0) [] (flatBT (Dpt 0 (Dpt (enat 1) 0\<^sub>B))) []"
    by (rule y6x_scb_self[OF c0]) simp_all
  have self: "scb_decomp (Mark (Pred y6B3) 0) [] (flatBT (transC1 y6B3)) []"
    using self0 y6B3_c1 by simp
  have mb: "(Mark (Pred y6B3) 0, transC1 y6B3) \<in> MarkedB"
    by (rule y6x_MarkedB_I[OF self])
  have some: "(SOME sb. scb_decomp (Mark (Pred y6B3) 0) (fst sb)
                          (flatBT (transC1 y6B3)) (snd sb)) = ([], [])"
    by (rule y6x_SOME_scb[OF self c0ne])
  have mlt: "(0::nat) < Lng y6B3 - 1" by simp
  have "Mark y6B3 0 = unflatBT ([] @ flatBT (transC2 y6B3) @ [])"
    using y6x_Mark_surg[OF y6B3_RT y6_L(2) y6_monoT(2) t1ne mlt] mb some by simp
  also have "\<dots> = transC2 y6B3" using unflatBT_flat by simp
  finally show ?thesis using y6B3_c2 by simp
qed

lemma y6_Mark_B3_2: "Mark y6B3 2 = Dpt (enat 1) 0\<^sub>B"
proof -
  have t1ne: "Trans (Pred y6B3) \<noteq> 0\<^sub>B" using y6_Pred(2) y6_Trans_B2 by simp
  have mge: "\<not> (2::nat) < Lng y6B3 - 1" by simp
  have "Mark y6B3 2 = Dpt (enat (entry y6B3 1 (Lng y6B3 - 1))) 0\<^sub>B"
    by (rule y6x_Mark_ge[OF y6B3_RT y6_L(2) y6_monoT(2) t1ne mge])
  thus ?thesis by (simp add: y6B3_def entry_def)
qed

text \<open>\<^bold>\<open>Level 4.\<close>  \<open>j\<^sub>0 = 2\<close> (admissible), \<open>c\<^sub>1 = Mark y6B3 2 = D\<^sub>1 0\<close>, condition (VI).\<close>

lemma y6B4_c1: "transC1 y6B4 = Dpt (enat 1) 0\<^sub>B"
proof -
  have "transC1 y6B4 = Mark (Pred y6B4) (Adm y6B4 (parent y6B4 0 (Lng y6B4 - 1)))"
    by (simp add: transC1_def transJm1_def transJ0_def transJ1_def)
  also have "\<dots> = Mark y6B3 (Adm y6B4 2)" using y6B4_jp y6_Pred(3) by simp
  also have "\<dots> = Mark y6B3 2" using y6B4_Adm2 by simp
  also have "\<dots> = Dpt (enat 1) 0\<^sub>B" by (rule y6_Mark_B3_2)
  finally show ?thesis .
qed

lemma y6B4_conds:
  "\<not> transCondI y6B4" "\<not> transCondIII y6B4" "\<not> transCondV y6B4" "transCondVI y6B4"
  unfolding transCondI_def transCondIII_def transCondV_def transCondVI_def y6B4_jp
  by (simp_all add: y6B4_def entry_def)

lemma y6B4_c2: "transC2 y6B4 = Dpt (enat 1) (Dpt (enat 2) 0\<^sub>B)"
proof -
  have v: "transV y6B4 = enat 1" using y6B4_c1 by (simp add: transV_def)
  have t2: "transT2 y6B4 = 0\<^sub>B" using y6B4_c1 by (simp add: transT2_def)
  have e1: "entry y6B4 1 (transJ1 y6B4) = 2"
    by (simp add: transJ1_def y6B4_def entry_def)
  show ?thesis
    using y6B4_conds v t2 e1 unfolding transC2_def Let_def by simp
qed

lemma y6_Trans_B4:
  "Trans y6B4 = Dpt 0 (Trm [DB (enat 1) 0\<^sub>B, DB (enat 1) (Dpt (enat 2) 0\<^sub>B)])"
proof -
  have t1: "Trans (Pred y6B4) = Dpt 0 (Trm [DB (enat 1) 0\<^sub>B, DB (enat 1) 0\<^sub>B])"
    using y6_Pred(3) y6_Trans_B3 by simp
  have t1ne: "Trans (Pred y6B4) \<noteq> 0\<^sub>B" using t1 by simp
  have df: "dfree_BT (0\<^sub>B :: BT)" by simp
  have d0: "scb_decomp (Trans (Pred y6B4)) [Dsym 0, LP, Dsym (enat 1), Zsym, CM]
              (flatBT (Dpt (enat 1) 0\<^sub>B)) [RP]"
    by (rule y6x_scb_right[OF t1 df])
  have d: "scb_decomp (Trans (Pred y6B4)) [Dsym 0, LP, Dsym (enat 1), Zsym, CM]
             (flatBT (transC1 y6B4)) [RP]"
    using d0 y6B4_c1 by simp
  have some: "(SOME sb. scb_decomp (Trans (Pred y6B4)) (fst sb)
                          (flatBT (transC1 y6B4)) (snd sb))
                = ([Dsym 0, LP, Dsym (enat 1), Zsym, CM], [RP])"
    by (rule y6x_SOME_scb[OF d t1ne])
  have "Trans y6B4 = unflatBT ([Dsym 0, LP, Dsym (enat 1), Zsym, CM]
                                 @ flatBT (transC2 y6B4) @ [RP])"
    using y6x_Trans_surg[OF y6B4_RT y6_L(3) y6_monoT(3) t1ne] some by simp
  also have "\<dots> = unflatBT (flatBT (Dpt 0 (Trm [DB (enat 1) 0\<^sub>B,
                                DB (enat 1) (Dpt (enat 2) 0\<^sub>B)])))"
    using y6B4_c2 by simp
  also have "\<dots> = Dpt 0 (Trm [DB (enat 1) 0\<^sub>B, DB (enat 1) (Dpt (enat 2) 0\<^sub>B)])"
    by (rule unflatBT_flat)
  finally show ?thesis .
qed

lemma y6_Mark_B4_0:
  "Mark y6B4 0 = Dpt 0 (Trm [DB (enat 1) 0\<^sub>B, DB (enat 1) (Dpt (enat 2) 0\<^sub>B)])"
proof -
  have t1ne: "Trans (Pred y6B4) \<noteq> 0\<^sub>B" using y6_Pred(3) y6_Trans_B3 by simp
  have c0: "Mark (Pred y6B4) 0 = Dpt 0 (Trm [DB (enat 1) 0\<^sub>B, DB (enat 1) 0\<^sub>B])"
    using y6_Pred(3) y6_Mark_B3_0 by simp
  have c0ne: "Mark (Pred y6B4) 0 \<noteq> 0\<^sub>B" using c0 by simp
  have df: "dfree_BT (0\<^sub>B :: BT)" by simp
  have d0: "scb_decomp (Mark (Pred y6B4) 0) [Dsym 0, LP, Dsym (enat 1), Zsym, CM]
              (flatBT (Dpt (enat 1) 0\<^sub>B)) [RP]"
    by (rule y6x_scb_right[OF c0 df])
  have d: "scb_decomp (Mark (Pred y6B4) 0) [Dsym 0, LP, Dsym (enat 1), Zsym, CM]
             (flatBT (transC1 y6B4)) [RP]"
    using d0 y6B4_c1 by simp
  have mb: "(Mark (Pred y6B4) 0, transC1 y6B4) \<in> MarkedB" by (rule y6x_MarkedB_I[OF d])
  have some: "(SOME sb. scb_decomp (Mark (Pred y6B4) 0) (fst sb)
                          (flatBT (transC1 y6B4)) (snd sb))
                = ([Dsym 0, LP, Dsym (enat 1), Zsym, CM], [RP])"
    by (rule y6x_SOME_scb[OF d c0ne])
  have mlt: "(0::nat) < Lng y6B4 - 1" by simp
  have "Mark y6B4 0 = unflatBT ([Dsym 0, LP, Dsym (enat 1), Zsym, CM]
                                  @ flatBT (transC2 y6B4) @ [RP])"
    using y6x_Mark_surg[OF y6B4_RT y6_L(3) y6_monoT(3) t1ne mlt] mb some by simp
  also have "\<dots> = unflatBT (flatBT (Dpt 0 (Trm [DB (enat 1) 0\<^sub>B,
                                DB (enat 1) (Dpt (enat 2) 0\<^sub>B)])))"
    using y6B4_c2 by simp
  also have "\<dots> = Dpt 0 (Trm [DB (enat 1) 0\<^sub>B, DB (enat 1) (Dpt (enat 2) 0\<^sub>B)])"
    by (rule unflatBT_flat)
  finally show ?thesis .
qed

lemma y6_Mark_B4_2: "Mark y6B4 2 = Dpt (enat 1) (Dpt (enat 2) 0\<^sub>B)"
proof -
  have t1ne: "Trans (Pred y6B4) \<noteq> 0\<^sub>B" using y6_Pred(3) y6_Trans_B3 by simp
  have c0: "Mark (Pred y6B4) 2 = Dpt (enat 1) 0\<^sub>B"
    using y6_Pred(3) y6_Mark_B3_2 by simp
  have c0ne: "Mark (Pred y6B4) 2 \<noteq> 0\<^sub>B" using c0 by simp
  have self0: "scb_decomp (Mark (Pred y6B4) 2) [] (flatBT (Dpt (enat 1) 0\<^sub>B)) []"
    by (rule y6x_scb_self[OF c0]) simp_all
  have self: "scb_decomp (Mark (Pred y6B4) 2) [] (flatBT (transC1 y6B4)) []"
    using self0 y6B4_c1 by simp
  have mb: "(Mark (Pred y6B4) 2, transC1 y6B4) \<in> MarkedB"
    by (rule y6x_MarkedB_I[OF self])
  have some: "(SOME sb. scb_decomp (Mark (Pred y6B4) 2) (fst sb)
                          (flatBT (transC1 y6B4)) (snd sb)) = ([], [])"
    by (rule y6x_SOME_scb[OF self c0ne])
  have mlt: "(2::nat) < Lng y6B4 - 1" by simp
  have "Mark y6B4 2 = unflatBT ([] @ flatBT (transC2 y6B4) @ [])"
    using y6x_Mark_surg[OF y6B4_RT y6_L(3) y6_monoT(3) t1ne mlt] mb some by simp
  also have "\<dots> = transC2 y6B4" using unflatBT_flat by simp
  finally show ?thesis using y6B4_c2 by simp
qed

lemma y6_Mark_B4_3: "Mark y6B4 3 = Dpt (enat 2) 0\<^sub>B"
proof -
  have t1ne: "Trans (Pred y6B4) \<noteq> 0\<^sub>B" using y6_Pred(3) y6_Trans_B3 by simp
  have mge: "\<not> (3::nat) < Lng y6B4 - 1" by simp
  have "Mark y6B4 3 = Dpt (enat (entry y6B4 1 (Lng y6B4 - 1))) 0\<^sub>B"
    by (rule y6x_Mark_ge[OF y6B4_RT y6_L(3) y6_monoT(3) t1ne mge])
  thus ?thesis by (simp add: y6B4_def entry_def)
qed

text \<open>\<^bold>\<open>Level 5.\<close>  The parent \<open>j\<^sub>0 = 3\<close> is \<^bold>\<open>NOT admissible\<close>, so \<open>c\<^sub>1\<close> is read at the
  admissibilization \<open>Adm y6B5 3 = 2\<close>.  Condition (VI).  At \<open>m = 3\<close> the ambient
  \<open>c\<^sub>0 = Mark y6B4 3 = D\<^sub>2 0\<close> is \<^bold>\<open>too short\<close> to contain \<open>c\<^sub>1 = D\<^sub>1(D\<^sub>2 0)\<close>: the
  \<open>MarkedB\<close> test FAILS and \<open>Mark\<close> returns the bare leaf \<open>D\<^sub>3 0\<close>.\<close>

lemma y6B5_c1: "transC1 y6B5 = Dpt (enat 1) (Dpt (enat 2) 0\<^sub>B)"
proof -
  have "transC1 y6B5 = Mark (Pred y6B5) (Adm y6B5 (parent y6B5 0 (Lng y6B5 - 1)))"
    by (simp add: transC1_def transJm1_def transJ0_def transJ1_def)
  also have "\<dots> = Mark y6B4 (Adm y6B5 3)" using y6B5_jp y6_Pred(4) by simp
  also have "\<dots> = Mark y6B4 2" using y6B5_Adm3 by simp
  also have "\<dots> = Dpt (enat 1) (Dpt (enat 2) 0\<^sub>B)" by (rule y6_Mark_B4_2)
  finally show ?thesis .
qed

lemma y6B5_conds:
  "\<not> transCondI y6B5" "\<not> transCondIII y6B5" "\<not> transCondV y6B5" "transCondVI y6B5"
  unfolding transCondI_def transCondIII_def transCondV_def transCondVI_def y6B5_jp
  by (simp_all add: y6B5_def entry_def)

lemma y6B5_c2: "transC2 y6B5 = Dpt (enat 1) (Dpt (enat 3) 0\<^sub>B)"
proof -
  have v: "transV y6B5 = enat 1" using y6B5_c1 by (simp add: transV_def)
  have t2: "transT2 y6B5 = Dpt (enat 2) 0\<^sub>B" using y6B5_c1 by (simp add: transT2_def)
  have e1: "entry y6B5 1 (transJ1 y6B5) = 3"
    by (simp add: transJ1_def y6B5_def entry_def)
  show ?thesis
    using y6B5_conds v t2 e1 unfolding transC2_def Let_def by simp
qed

lemma y6_Trans_B5:
  "Trans y6B5 = Dpt 0 (Trm [DB (enat 1) 0\<^sub>B, DB (enat 1) (Dpt (enat 3) 0\<^sub>B)])"
proof -
  have t1: "Trans (Pred y6B5)
              = Dpt 0 (Trm [DB (enat 1) 0\<^sub>B, DB (enat 1) (Dpt (enat 2) 0\<^sub>B)])"
    using y6_Pred(4) y6_Trans_B4 by simp
  have t1ne: "Trans (Pred y6B5) \<noteq> 0\<^sub>B" using t1 by simp
  have df: "dfree_BT (Dpt (enat 2) 0\<^sub>B)" by simp
  have d0: "scb_decomp (Trans (Pred y6B5)) [Dsym 0, LP, Dsym (enat 1), Zsym, CM]
              (flatBT (Dpt (enat 1) (Dpt (enat 2) 0\<^sub>B))) [RP]"
    by (rule y6x_scb_right[OF t1 df])
  have d: "scb_decomp (Trans (Pred y6B5)) [Dsym 0, LP, Dsym (enat 1), Zsym, CM]
             (flatBT (transC1 y6B5)) [RP]"
    using d0 y6B5_c1 by simp
  have some: "(SOME sb. scb_decomp (Trans (Pred y6B5)) (fst sb)
                          (flatBT (transC1 y6B5)) (snd sb))
                = ([Dsym 0, LP, Dsym (enat 1), Zsym, CM], [RP])"
    by (rule y6x_SOME_scb[OF d t1ne])
  have "Trans y6B5 = unflatBT ([Dsym 0, LP, Dsym (enat 1), Zsym, CM]
                                 @ flatBT (transC2 y6B5) @ [RP])"
    using y6x_Trans_surg[OF y6B5_RT y6_L(4) y6_monoT(4) t1ne] some by simp
  also have "\<dots> = unflatBT (flatBT (Dpt 0 (Trm [DB (enat 1) 0\<^sub>B,
                                DB (enat 1) (Dpt (enat 3) 0\<^sub>B)])))"
    using y6B5_c2 by simp
  also have "\<dots> = Dpt 0 (Trm [DB (enat 1) 0\<^sub>B, DB (enat 1) (Dpt (enat 3) 0\<^sub>B)])"
    by (rule unflatBT_flat)
  finally show ?thesis .
qed

lemma y6_Mark_B5_0:
  "Mark y6B5 0 = Dpt 0 (Trm [DB (enat 1) 0\<^sub>B, DB (enat 1) (Dpt (enat 3) 0\<^sub>B)])"
proof -
  have t1ne: "Trans (Pred y6B5) \<noteq> 0\<^sub>B" using y6_Pred(4) y6_Trans_B4 by simp
  have c0: "Mark (Pred y6B5) 0
              = Dpt 0 (Trm [DB (enat 1) 0\<^sub>B, DB (enat 1) (Dpt (enat 2) 0\<^sub>B)])"
    using y6_Pred(4) y6_Mark_B4_0 by simp
  have c0ne: "Mark (Pred y6B5) 0 \<noteq> 0\<^sub>B" using c0 by simp
  have df: "dfree_BT (Dpt (enat 2) 0\<^sub>B)" by simp
  have d0: "scb_decomp (Mark (Pred y6B5) 0) [Dsym 0, LP, Dsym (enat 1), Zsym, CM]
              (flatBT (Dpt (enat 1) (Dpt (enat 2) 0\<^sub>B))) [RP]"
    by (rule y6x_scb_right[OF c0 df])
  have d: "scb_decomp (Mark (Pred y6B5) 0) [Dsym 0, LP, Dsym (enat 1), Zsym, CM]
             (flatBT (transC1 y6B5)) [RP]"
    using d0 y6B5_c1 by simp
  have mb: "(Mark (Pred y6B5) 0, transC1 y6B5) \<in> MarkedB" by (rule y6x_MarkedB_I[OF d])
  have some: "(SOME sb. scb_decomp (Mark (Pred y6B5) 0) (fst sb)
                          (flatBT (transC1 y6B5)) (snd sb))
                = ([Dsym 0, LP, Dsym (enat 1), Zsym, CM], [RP])"
    by (rule y6x_SOME_scb[OF d c0ne])
  have mlt: "(0::nat) < Lng y6B5 - 1" by simp
  have "Mark y6B5 0 = unflatBT ([Dsym 0, LP, Dsym (enat 1), Zsym, CM]
                                  @ flatBT (transC2 y6B5) @ [RP])"
    using y6x_Mark_surg[OF y6B5_RT y6_L(4) y6_monoT(4) t1ne mlt] mb some by simp
  also have "\<dots> = unflatBT (flatBT (Dpt 0 (Trm [DB (enat 1) 0\<^sub>B,
                                DB (enat 1) (Dpt (enat 3) 0\<^sub>B)])))"
    using y6B5_c2 by simp
  also have "\<dots> = Dpt 0 (Trm [DB (enat 1) 0\<^sub>B, DB (enat 1) (Dpt (enat 3) 0\<^sub>B)])"
    by (rule unflatBT_flat)
  finally show ?thesis .
qed

lemma y6_Mark_B5_2: "Mark y6B5 2 = Dpt (enat 1) (Dpt (enat 3) 0\<^sub>B)"
proof -
  have t1ne: "Trans (Pred y6B5) \<noteq> 0\<^sub>B" using y6_Pred(4) y6_Trans_B4 by simp
  have c0: "Mark (Pred y6B5) 2 = Dpt (enat 1) (Dpt (enat 2) 0\<^sub>B)"
    using y6_Pred(4) y6_Mark_B4_2 by simp
  have c0ne: "Mark (Pred y6B5) 2 \<noteq> 0\<^sub>B" using c0 by simp
  have self0: "scb_decomp (Mark (Pred y6B5) 2) []
                 (flatBT (Dpt (enat 1) (Dpt (enat 2) 0\<^sub>B))) []"
    by (rule y6x_scb_self[OF c0]) simp_all
  have self: "scb_decomp (Mark (Pred y6B5) 2) [] (flatBT (transC1 y6B5)) []"
    using self0 y6B5_c1 by simp
  have mb: "(Mark (Pred y6B5) 2, transC1 y6B5) \<in> MarkedB"
    by (rule y6x_MarkedB_I[OF self])
  have some: "(SOME sb. scb_decomp (Mark (Pred y6B5) 2) (fst sb)
                          (flatBT (transC1 y6B5)) (snd sb)) = ([], [])"
    by (rule y6x_SOME_scb[OF self c0ne])
  have mlt: "(2::nat) < Lng y6B5 - 1" by simp
  have "Mark y6B5 2 = unflatBT ([] @ flatBT (transC2 y6B5) @ [])"
    using y6x_Mark_surg[OF y6B5_RT y6_L(4) y6_monoT(4) t1ne mlt] mb some by simp
  also have "\<dots> = transC2 y6B5" using unflatBT_flat by simp
  finally show ?thesis using y6B5_c2 by simp
qed

lemma y6_Mark_B5_3: "Mark y6B5 3 = Dpt (enat 3) 0\<^sub>B"
proof -
  have t1ne: "Trans (Pred y6B5) \<noteq> 0\<^sub>B" using y6_Pred(4) y6_Trans_B4 by simp
  have c0: "Mark (Pred y6B5) 3 = Dpt (enat 2) 0\<^sub>B"
    using y6_Pred(4) y6_Mark_B4_3 by simp
  have len: "length (flatBT (Mark (Pred y6B5) 3)) < length (flatBT (transC1 y6B5))"
    using c0 y6B5_c1 by simp
  have nmb: "(Mark (Pred y6B5) 3, transC1 y6B5) \<notin> MarkedB"
    by (rule y6x_not_MarkedB[OF len])
  have mlt: "(3::nat) < Lng y6B5 - 1" by simp
  have "Mark y6B5 3 = Dpt (enat (entry y6B5 1 (Lng y6B5 - 1))) 0\<^sub>B"
    using y6x_Mark_surg[OF y6B5_RT y6_L(4) y6_monoT(4) t1ne mlt] nmb by simp
  thus ?thesis by (simp add: y6B5_def entry_def)
qed

text \<open>\<^bold>\<open>Level 6 --- the two facts that kill the article's 系.\<close>  Same picture one level
  up (\<open>j\<^sub>0 = 3\<close> non-admissible, \<open>c\<^sub>1\<close> at the admissibilization 2, condition (V)).  At
  \<open>m = 3\<close> the \<open>MarkedB\<close> test fails again and \<open>Mark y6B6 3 = D\<^sub>3 0 = Mark y6B5 3\<close>: the
  \<^bold>\<open>cores COINCIDE\<close>.  At \<open>m = 0\<close> the surgery does fire, and the \<^bold>\<open>ambients DIFFER\<close>.\<close>

lemma y6B6_c1: "transC1 y6B6 = Dpt (enat 1) (Dpt (enat 3) 0\<^sub>B)"
proof -
  have "transC1 y6B6 = Mark (Pred y6B6) (Adm y6B6 (parent y6B6 0 (Lng y6B6 - 1)))"
    by (simp add: transC1_def transJm1_def transJ0_def transJ1_def)
  also have "\<dots> = Mark y6B5 (Adm y6B6 3)" using y6B6_jp y6_Pred(5) by simp
  also have "\<dots> = Mark y6B5 2" using y6B6_Adm3 by simp
  also have "\<dots> = Dpt (enat 1) (Dpt (enat 3) 0\<^sub>B)" by (rule y6_Mark_B5_2)
  finally show ?thesis .
qed

lemma y6B6_condV: "transCondV y6B6"
  unfolding transCondV_def y6B6_jp by (simp add: y6B6_def entry_def)

lemma y6B6_c2: "transC2 y6B6 = Dpt (enat 1) (Trm [DB (enat 3) 0\<^sub>B, DB (enat 3) 0\<^sub>B])"
proof -
  have v: "transV y6B6 = enat 1" using y6B6_c1 by (simp add: transV_def)
  have t2: "transT2 y6B6 = Dpt (enat 3) 0\<^sub>B" using y6B6_c1 by (simp add: transT2_def)
  have e1: "entry y6B6 1 (transJ1 y6B6) = 3"
    by (simp add: transJ1_def y6B6_def entry_def)
  show ?thesis
    using y6B6_condV v t2 e1 unfolding transC2_def Let_def by simp
qed

lemma y6_Mark_B6_3: "Mark y6B6 3 = Dpt (enat 3) 0\<^sub>B"
proof -
  have t1ne: "Trans (Pred y6B6) \<noteq> 0\<^sub>B" using y6_Pred(5) y6_Trans_B5 by simp
  have c0: "Mark (Pred y6B6) 3 = Dpt (enat 3) 0\<^sub>B"
    using y6_Pred(5) y6_Mark_B5_3 by simp
  have len: "length (flatBT (Mark (Pred y6B6) 3)) < length (flatBT (transC1 y6B6))"
    using c0 y6B6_c1 by simp
  have nmb: "(Mark (Pred y6B6) 3, transC1 y6B6) \<notin> MarkedB"
    by (rule y6x_not_MarkedB[OF len])
  have mlt: "(3::nat) < Lng y6B6 - 1" by simp
  have "Mark y6B6 3 = Dpt (enat (entry y6B6 1 (Lng y6B6 - 1))) 0\<^sub>B"
    using y6x_Mark_surg[OF y6B6_RT y6_L(5) y6_monoT(5) t1ne mlt] nmb by simp
  thus ?thesis by (simp add: y6B6_def entry_def)
qed

lemma y6_Mark_B6_0:
  "Mark y6B6 0 = Dpt 0 (Trm [DB (enat 1) 0\<^sub>B,
                             DB (enat 1) (Trm [DB (enat 3) 0\<^sub>B, DB (enat 3) 0\<^sub>B])])"
proof -
  have t1ne: "Trans (Pred y6B6) \<noteq> 0\<^sub>B" using y6_Pred(5) y6_Trans_B5 by simp
  have c0: "Mark (Pred y6B6) 0
              = Dpt 0 (Trm [DB (enat 1) 0\<^sub>B, DB (enat 1) (Dpt (enat 3) 0\<^sub>B)])"
    using y6_Pred(5) y6_Mark_B5_0 by simp
  have c0ne: "Mark (Pred y6B6) 0 \<noteq> 0\<^sub>B" using c0 by simp
  have df: "dfree_BT (Dpt (enat 3) 0\<^sub>B)" by simp
  have d0: "scb_decomp (Mark (Pred y6B6) 0) [Dsym 0, LP, Dsym (enat 1), Zsym, CM]
              (flatBT (Dpt (enat 1) (Dpt (enat 3) 0\<^sub>B))) [RP]"
    by (rule y6x_scb_right[OF c0 df])
  have d: "scb_decomp (Mark (Pred y6B6) 0) [Dsym 0, LP, Dsym (enat 1), Zsym, CM]
             (flatBT (transC1 y6B6)) [RP]"
    using d0 y6B6_c1 by simp
  have mb: "(Mark (Pred y6B6) 0, transC1 y6B6) \<in> MarkedB" by (rule y6x_MarkedB_I[OF d])
  have some: "(SOME sb. scb_decomp (Mark (Pred y6B6) 0) (fst sb)
                          (flatBT (transC1 y6B6)) (snd sb))
                = ([Dsym 0, LP, Dsym (enat 1), Zsym, CM], [RP])"
    by (rule y6x_SOME_scb[OF d c0ne])
  have mlt: "(0::nat) < Lng y6B6 - 1" by simp
  have "Mark y6B6 0 = unflatBT ([Dsym 0, LP, Dsym (enat 1), Zsym, CM]
                                  @ flatBT (transC2 y6B6) @ [RP])"
    using y6x_Mark_surg[OF y6B6_RT y6_L(5) y6_monoT(5) t1ne mlt] mb some by simp
  also have "\<dots> = unflatBT (flatBT (Dpt 0 (Trm [DB (enat 1) 0\<^sub>B,
                     DB (enat 1) (Trm [DB (enat 3) 0\<^sub>B, DB (enat 3) 0\<^sub>B])])))"
    using y6B6_c2 by simp
  also have "\<dots> = Dpt 0 (Trm [DB (enat 1) 0\<^sub>B,
                     DB (enat 1) (Trm [DB (enat 3) 0\<^sub>B, DB (enat 3) 0\<^sub>B])])"
    by (rule unflatBT_flat)
  finally show ?thesis .
qed


subsection \<open>Transporting the \<open>Mark\<close> values back to \<open>y6M\<close>\<close>

lemma y6M_Red2: "(Red ^^ 2) y6M = y6B6"
proof -
  have F2: "(Red ^^ 2) y6M = Red (Red y6M)" by (simp add: numeral_2_eq_2)
  have "Red (Red y6M) = Red y6B6" using y6M_Red by simp
  also have "\<dots> = y6B6" using y6B6_RT by (simp add: RT_PS_def)
  finally show ?thesis using F2 by simp
qed

lemma y6M_Mark: "Mark y6M i = Mark y6B6 i"
proof -
  have F: "(Red ^^ 2) y6M \<in> RT_PS" using y6M_Red2 y6B6_RT by simp
  show ?thesis using y3s_Mark_funpow_Red[OF F, of i] y6M_Red2 by simp
qed

lemma y6M_Pred_Mark: "Mark (Pred y6M) i = Mark y6B5 i"
proof -
  have pe: "(Red ^^ 2) (Pred y6M) = Pred ((Red ^^ 2) y6M)"
    by (rule y3s_Pred_funpow_Red[OF y6_TPS(7)])
  have pe2: "(Red ^^ 2) (Pred y6M) = y6B5" using pe y6M_Red2 y6_Pred(5) by simp
  have F: "(Red ^^ 2) (Pred y6M) \<in> RT_PS" using pe2 y6B5_RT by simp
  show ?thesis using y3s_Mark_funpow_Red[OF F, of i] pe2 by simp
qed


subsection \<open>The hypotheses of the article's 系, at \<open>y6M\<close>\<close>

lemma y6M_nextAdm3: "nextAdm y6M 0 3 (Lng y6M - 1)"
proof -
  have Lm: "Lng y6M - 1 = 5" by simp
  have l: "leR y6M 0 3 (Lng y6M - 1)" unfolding Lm leR_def using y6M_le0_35 by simp
  have lt: "(3::nat) < Lng y6M - 1" using Lm by simp
  have n4: "\<not> leR y6M 0 4 (Lng y6M - 1)"
    unfolding Lm leR_def using y6M_nle0_45 by simp
  have vac: "\<forall>j. 3 < j \<and> j < Lng y6M - 1
                  \<longrightarrow> \<not> leR y6M 0 j (Lng y6M - 1) \<or> \<not> adm y6M j"
  proof (intro allI impI)
    fix j assume A: "3 < j \<and> j < Lng y6M - 1"
    hence j4: "j = 4" using Lm by linarith
    show "\<not> leR y6M 0 j (Lng y6M - 1) \<or> \<not> adm y6M j" using j4 n4 by simp
  qed
  show ?thesis unfolding nextAdm_def using l lt y6M_adm3 vac by simp
qed

lemma y6M_nextAdm_only3:
  assumes H: "nextAdm y6M 0 j0 (Lng y6M - 1)" shows "j0 = 3"
proof -
  have Lm: "Lng y6M - 1 = 5" by simp
  have lt: "j0 < 5" using H Lm by (simp add: nextAdm_def)
  have le: "leR y6M 0 j0 (Lng y6M - 1)" using H by (simp add: nextAdm_def)
  have l3: "leR y6M 0 3 (Lng y6M - 1)" unfolding Lm leR_def using y6M_le0_35 by simp
  have n4: "\<not> leR y6M 0 4 (Lng y6M - 1)"
    unfolding Lm leR_def using y6M_nle0_45 by simp
  show ?thesis
  proof (rule ccontr)
    assume ne: "j0 \<noteq> 3"
    consider "j0 < 3" | "j0 = 4" using lt ne by linarith
    thus False
    proof cases
      case 1
      have gap: "\<not> leR y6M 0 3 (Lng y6M - 1) \<or> \<not> adm y6M 3"
        using H 1 Lm unfolding nextAdm_def by simp
      show False using gap l3 y6M_adm3 by simp
    next
      case 2
      show False using le n4 2 by simp
    qed
  qed
qed

lemma y6M_nextAdm_ex1: "\<exists>!j0. nextAdm y6M 0 j0 (Lng y6M - 1)"
  using y6M_nextAdm3 y6M_nextAdm_only3 by blast

lemma y6M_nextAdm_THE: "(THE j0. nextAdm y6M 0 j0 (Lng y6M - 1)) = 3"
  using y6M_nextAdm3 y6M_nextAdm_only3 by (rule the_equality)

lemma y6M_marked0: "(y6M, 0) \<in> Marked"
proof -
  have "leR y6M 0 0 (Lng y6M - 1)" using y6M_le0_05 by (simp add: leR_def)
  thus ?thesis using y3w_adm_0 by (simp add: Marked_def)
qed

lemma y6M_leR_0_3: "leR y6M 0 0 (THE j0. nextAdm y6M 0 j0 (Lng y6M - 1))"
  using y6M_nextAdm_THE y6M_le0_03 by (simp add: leR_def)


subsection \<open>\<^bold>\<open>The refutation\<close>\<close>

lemma y6M_cores_coincide: "Mark y6M 3 = Mark (Pred y6M) 3"
  using y6M_Mark[of 3] y6M_Pred_Mark[of 3] y6_Mark_B6_3 y6_Mark_B5_3 by simp

lemma y6M_marks_differ: "Mark y6M 0 \<noteq> Mark (Pred y6M) 0"
  using y6M_Mark[of 0] y6M_Pred_Mark[of 0] y6_Mark_B6_0 y6_Mark_B5_0 by simp

theorem y6z_7_4_Mark_nextAdm_TPS_false:
  "\<not> (\<forall>M j. M \<in> T_PS \<longrightarrow> (\<exists>!j0. nextAdm M 0 j0 (Lng M - 1))
             \<longrightarrow> (M, j) \<in> Marked
             \<longrightarrow> leR M 0 j (THE j0. nextAdm M 0 j0 (Lng M - 1))
             \<longrightarrow> (\<exists>!sb. scb_decomp (Mark (Pred M) j) (fst sb)
                          (flatBT (Mark (Pred M)
                             (THE j0. nextAdm M 0 j0 (Lng M - 1)))) (snd sb)
                      \<and> scb_decomp (Mark M j) (fst sb)
                          (flatBT (Mark M
                             (THE j0. nextAdm M 0 j0 (Lng M - 1)))) (snd sb)))"
proof
  assume A: "\<forall>M j. M \<in> T_PS \<longrightarrow> (\<exists>!j0. nextAdm M 0 j0 (Lng M - 1))
               \<longrightarrow> (M, j) \<in> Marked
               \<longrightarrow> leR M 0 j (THE j0. nextAdm M 0 j0 (Lng M - 1))
               \<longrightarrow> (\<exists>!sb. scb_decomp (Mark (Pred M) j) (fst sb)
                            (flatBT (Mark (Pred M)
                               (THE j0. nextAdm M 0 j0 (Lng M - 1)))) (snd sb)
                        \<and> scb_decomp (Mark M j) (fst sb)
                            (flatBT (Mark M
                               (THE j0. nextAdm M 0 j0 (Lng M - 1)))) (snd sb))"
  have ex1: "\<exists>!sb. scb_decomp (Mark (Pred y6M) 0) (fst sb)
                     (flatBT (Mark (Pred y6M)
                        (THE j0. nextAdm y6M 0 j0 (Lng y6M - 1)))) (snd sb)
                 \<and> scb_decomp (Mark y6M 0) (fst sb)
                     (flatBT (Mark y6M
                        (THE j0. nextAdm y6M 0 j0 (Lng y6M - 1)))) (snd sb)"
    using A[rule_format, of y6M 0] y6_TPS(7) y6M_nextAdm_ex1 y6M_marked0 y6M_leR_0_3
    by blast
  have ex1': "\<exists>!sb. scb_decomp (Mark (Pred y6M) 0) (fst sb)
                      (flatBT (Mark (Pred y6M) 3)) (snd sb)
                  \<and> scb_decomp (Mark y6M 0) (fst sb)
                      (flatBT (Mark y6M 3)) (snd sb)"
    using ex1 y6M_nextAdm_THE by simp
  have no: "\<not> (\<exists>!sb. scb_decomp (Mark (Pred y6M) 0) (fst sb)
                       (flatBT (Mark (Pred y6M) 3)) (snd sb)
                   \<and> scb_decomp (Mark y6M 0) (fst sb)
                       (flatBT (Mark y6M 3)) (snd sb))"
    by (rule y6z_nest_false_at[OF y6M_cores_coincide y6M_marks_differ])
  show False using ex1' no by blast
qed


section \<open>Additional relocated campaign annotations\<close>

subsection \<open>The witnesses (vetted model), and what they kill\<close>

text \<open>\<^bold>\<open>(1) The relaxed engine \<open>ENG\<close> is FALSE on \<open>RT\<^bsub>PS\<^esub>\<close>.\<close>  Witness

    \<open>N = (0,0)(1,1)(1,1)(2,2)(3,3)(3,3)\<close>,   \<open>m = 0\<close>,   \<open>m' = 3\<close>.

  \<open>N\<close> is reduced (\<open>N \<in> RT\<^bsub>PS\<^esub>\<close>), \<open>Lng N = 6\<close>, and \<^emph>\<open>every\<close> hypothesis of \<open>ENG\<close> holds:
  \<open>le\<^sub>0 N 0 3\<close>, \<open>le\<^sub>0 N 0 5\<close>, \<open>le\<^sub>0 N 3 5\<close> (row 0 is \<open>0,1,1,2,3,3\<close>), \<open>0 < 3\<close>,
  \<open>3 < Lng N - 1 = 5\<close>.  The only thing that fails is the DROPPED hypothesis:
  \<open>adm N 3 = False\<close> (columns \<open>2,3,4\<close> of \<open>N\<close> are \<open>(1,1),(2,2),(3,3)\<close>, so both rows
  strictly increase across \<open>2 \<to> 3 \<to> 4\<close> --- @{thm [source] y3w_nadm_local}).  The
  \<open>Mark\<close> values (vetted model):

    \<open>Mark (Pred N) 3 = D\<^sub>3 0 = Mark N 3\<close>            (the two cores COINCIDE),
    \<open>Mark (Pred N) 0 = D\<^sub>0 (D\<^sub>1 0 \<oplus> D\<^sub>1 (D\<^sub>3 0))\<close>,
    \<open>Mark N 0        = D\<^sub>0 (D\<^sub>1 0 \<oplus> D\<^sub>1 (D\<^sub>3 0 \<oplus> D\<^sub>3 0))\<close>   (the ambients DIFFER).

  So @{thm [source] y6z_nest_false_at} applies verbatim: there is NO common
  scb-position (the \<open>Pred\<close>-side has the unique position
  \<open>s\<^sub>0 = D\<^sub>0 \<^bold>( D\<^sub>1 Z \<^bold>, D\<^sub>1\<close>, \<open>b\<^sub>0 = \<^bold>)\<close>, the \<open>M\<close>-side the unique position
  \<open>s\<^sub>0 = D\<^sub>0 \<^bold>( D\<^sub>1 Z \<^bold>, D\<^sub>1 \<^bold>( D\<^sub>3 Z \<^bold>,\<close>, \<open>b\<^sub>0 = \<^bold>)\<^bold>)\<close> --- the scb-tail condition
  "\<open>b\<close> is all \<open>\<^bold>)\<close>" pins the \<^emph>\<open>rightmost\<close> occurrence of the core, and the surgery
  has implanted a SECOND copy of \<open>D\<^sub>3 0\<close> to the right of the first).

  \<^bold>\<open>Why \<open>adm\<close> was load-bearing\<close>: at an admissible \<open>m'\<close> the value \<open>Mark N m'\<close> is the
  surgically GROWN block (it moves in step with \<open>Mark N m\<close>); at the non-admissible
  \<open>m' = 3\<close> the \<open>Mark\<close> recursion takes its FALLBACK branch and returns the bare leaf
  \<open>D\<^bsub>N\<^sub>1\<^sub>,\<^sub>j\<^sub>1\<^esub> 0 = D\<^sub>3 0\<close> --- which is exactly what \<open>Mark (Pred N) 3\<close> returns as well
  (\<open>N\<^sub>1\<^sub>,\<^sub>5 = 3 = (Pred N)\<^sub>1\<^sub>,\<^sub>4\<close>).  Cores coincide, ambients do not.  \<open>adm\<close> at the
  OUTER column cannot be dropped.

  \<^bold>\<open>(2) The article's \<section>7.4 系 is FALSE on \<open>T\<^bsub>PS\<^esub>\<close>.\<close>  Witness

    \<open>M = (1,0)(5,3)(2,5)(3,3)(6,5)(5,7)\<close>,   \<open>j = 0\<close>,   \<open>j\<^sub>0 = 3\<close>.

  \<open>M \<in> T\<^bsub>PS\<^esub>\<close>; row 0 is \<open>1,5,2,3,6,5\<close>, row 1 is \<open>0,3,5,3,5,7\<close>; \<open>j\<^sub>1 = 5\<close>.  All
  hypotheses of the proposition (A18's form) hold:

    \<^item> \<open>\<exists>!j\<^sub>0. nextAdm M 0 j\<^sub>0 5\<close>, and that \<open>j\<^sub>0\<close> is \<open>3\<close> (the \<open>\<le>\<^sub>0\<close>-ancestors of \<open>5\<close> are
      \<open>0,2,3\<close>; \<open>2\<close> and \<open>0\<close> are disqualified because the admissible \<open>3\<close> lies
      \<open>\<le>\<^sub>0\<close>-between them and \<open>5\<close>);
    \<^item> \<open>(M,0) \<in> T\<^bsub>PS\<^esub>\<^sup>Marked\<close> (\<open>adm M 0\<close> always, and \<open>le\<^sub>0 M 0 5\<close> via \<open>0 \<to> 2 \<to> 3 \<to> 5\<close>);
    \<^item> \<open>le\<^sub>R M 0 0 3\<close> (via \<open>0 \<to> 2 \<to> 3\<close>).

  And \<open>Red M = N\<close> above (already reduced, so \<open>Red (Red M) = N\<close> too), whence by
  @{thm [source] y3s_Mark_funpow_Red} and @{thm [source] y3s_Pred_funpow_Red}
  \<open>Mark M i = Mark N i\<close> and \<open>Mark (Pred M) i = Mark (Pred N) i\<close> for every \<open>i\<close>:
  the conclusion demanded at \<open>(M,0,3)\<close> IS the conclusion refuted at \<open>(N,0,3)\<close>.
  @{thm [source] y6z_nest_false_at} kills it.

  \<^bold>\<open>Censuses\<close> (this round; \<open>python/_y6_census.py\<close>, \<open>python/_y6_engine.py\<close>,
  \<open>python/_y6_hunt.py\<close>; the models are memoised in \<open>python/_y6_fast.py\<close> and
  cross-validated against the raw \<open>trans_model\<close>):

    \<^item> \<^bold>\<open>Why this was missed for four rounds\<close>: the proposition has NO counterexample
      at entries \<open>\<le> 3\<close> / \<open>Lng \<le> 4\<close> (4523 non-vacuous exercises, 0 failures --- the
      very census that was quoted as evidence), and none at any bound previously
      swept.  The smallest witnesses need \<open>Lng = 6\<close> AND a row-1 entry \<open>\<ge> 5\<close>.  This
      is the project's \<^bold>\<open>fifth\<close> entry-bounded false positive.
    \<^item> random \<open>T\<^bsub>PS\<^esub>\<close> sweep, entries \<open>\<le> 8\<close>, \<open>Lng \<le> 6\<close>: failures appear
      (\<approx>1 per \<open>10\<^sup>4\<close> non-vacuous exercises); random sweep entries \<open>\<le> 12\<close>, \<open>Lng \<le> 8\<close>:
      failures appear at \<approx>7 per \<open>10\<^sup>4\<close>.
    \<^item> the \<open>Mark\<close>-transport (*) \<open>Mark (Pred M) i = Mark (Pred (Red (Red M))) i\<close> --- the
      thing this front was asked to check first --- is TRUE (it is a theorem:
      @{thm [source] m_6_5_Red_Pred} + @{thm [source] y3s_Mark_funpow_Red}), and
      5000 random sequences at entries \<open>\<le> 20\<close>, \<open>Lng \<le> 10\<close> confirm it: 0 violations.
      The transport was never the problem; the STATEMENT is false.\<close>



(* ===================================================================== *)
(* r82-Y6X: THE MACHINE-CHECKED COUNTEREXAMPLE.                           *)
(*                                                                        *)
(* The article's §7.4 系（Mark と <^NextAdm の関係）is FALSE on T_PS.       *)
(*                                                                        *)
(*   M  = (0,0)(4,2)(2,6)(4,2)(8,4)(6,4)   (NOT reduced),  j = 0, j0 = 3  *)
(*   Red M = Red (Red M) = (0,0)(1,1)(1,1)(2,2)(3,3)(3,3)                 *)
(*                                                                        *)
(* Every hypothesis holds at M (all six columns of M are admissible, and  *)
(* the <^NextAdm-predecessor of the right end is UNIQUELY 3), but at the  *)
(* reduct column 3 is NOT admissible, so Mark takes its FALLBACK branch   *)
(* there and returns the same bare leaf D_3 0 as Mark (Pred -) 3 does.    *)
(* Cores coincide, ambients do not: y6z_nest_false_at (r81) applies.      *)
text \<open>\<^bold>\<open>STATUS (r82) --- the last open item of the project, CLOSED NEGATIVELY.\<close>

  The article's \<section>7.4 系（\<open>Mark\<close> と \<open><\<^sup>NextAdm\<close> の関係）does \<^bold>\<open>not\<close> hold on \<open>T\<^bsub>PS\<^esub>\<close>.
  It holds on \<open>RT\<^bsub>PS\<^esub>\<close> (@{thm [source] m_7_4_Mark_nextAdm}), and \<^emph>\<open>that is all it can
  hold on\<close>.  Witness, machine-checked above (no census, no sampling ---
  @{thm [source] y6z_7_4_Mark_nextAdm_TPS_false} is a closed theorem):

    \<open>M = (0,0)(4,2)(2,6)(4,2)(8,4)(6,4) \<in> T\<^bsub>PS\<^esub>\<close>,   \<open>j = 0\<close>,   \<open>j\<^sub>0 = 3\<close>.

  \<^item> \<^bold>\<open>Every hypothesis holds at \<open>M\<close>\<close> (A18's form, read off \<open>M\<close> exactly as the article
    states them): all six columns of \<open>M\<close> are \<open>M\<close>-admissible (@{thm [source] y6M_adm});
    \<open>3\<close> is the \<^bold>\<open>unique\<close> \<open><\<^sup>NextAdm\<close>-predecessor of the right end
    (@{thm [source] y6M_nextAdm_ex1}, @{thm [source] y6M_nextAdm_THE});
    \<open>(M,0) \<in> T\<^bsub>PS\<^esub>\<^sup>Marked\<close> (@{thm [source] y6M_marked0}); \<open>(0,0) \<le>\<^sub>M (0,3)\<close>
    (@{thm [source] y6M_leR_0_3}).
  \<^item> \<^bold>\<open>The conclusion fails\<close>.  \<open>Red M = Red\<^sup>2 M = (0,0)(1,1)(1,1)(2,2)(3,3)(3,3)\<close>
    (@{thm [source] y6M_Red}, @{thm [source] y6M_Red2}), and \<^bold>\<open>at the reduct column 3 is
    NOT admissible\<close> (@{thm [source] y6B6_nadm3}) --- correction A4 once more: \<open>\<le>\<^sub>M\<close> and
    \<open>adm\<close> are not \<open>Red\<close>-invariant, while \<open>Mark\<close> reads its basepoints off the reduct
    (@{thm [source] y3s_Mark_funpow_Red}).  So the \<open>Mark\<close> recursion takes its
    \<^bold>\<open>fallback\<close> branch at column 3 --- the \<open>MarkedB\<close> test fails on a bare length count,
    \<open>flat (D\<^sub>2 0)\<close> being shorter than \<open>flat (D\<^sub>1 (D\<^sub>2 0))\<close> --- and returns the leaf
    \<open>D\<^sub>3 0\<close>, which is \<^emph>\<open>exactly\<close> what \<open>Mark (Pred M) 3\<close> returns:

      \<open>Mark M 3 = D\<^sub>3 0 = Mark (Pred M) 3\<close>          (@{thm [source] y6M_cores_coincide}),
      \<open>Mark M 0 = D\<^sub>0(D\<^sub>1 0, D\<^sub>1(D\<^sub>3 0, D\<^sub>3 0))
                  \<noteq> D\<^sub>0(D\<^sub>1 0, D\<^sub>1(D\<^sub>3 0)) = Mark (Pred M) 0\<close>
                                                   (@{thm [source] y6M_marks_differ}).

    Coinciding cores + differing ambients \<Longrightarrow> there is \<^bold>\<open>no\<close> common scb position at all
    (@{thm [source] y6z_nest_false_at}, r81).  Not "the unique one is hard to find":
    there is \<^bold>\<open>none\<close>.
  \<^item> \<^bold>\<open>Corollary for r81\<close>: the relaxed engine \<open>ENG\<close> assumed by
    @{thm [source] y6_7_4_Mark_nextAdm_TPS} is \<^bold>\<open>unsatisfiable\<close> (its own witness
    \<open>N = (0,0)(1,1)(1,1)(2,2)(3,3)(3,3)\<close>, \<open>m = 0\<close>, \<open>m' = 3\<close> is the reduct here).  That
    theorem is a valid but \<^emph>\<open>vacuous\<close> implication, kept only because it pins the
    residue exactly.  \<^bold>\<open>It is NOT a route that can be completed\<close>: no \<open>adm\<close>-free
    relaxation of the \<section>7 nesting engine exists.
  \<^item> \<^bold>\<open>The correction\<close>: the 系 must be restricted to \<open>RT\<^bsub>PS\<^esub>\<close>, exactly as its \<section>7.4
    neighbours already are (corrections A45 / A46).  Same family, same root cause
    (correction A4).

  Why four rounds of censuses missed it: there is no counterexample at entries \<open>\<le> 3\<close>
  or at \<open>Lng \<le> 5\<close>; the smallest need \<open>Lng = 6\<close> \<^emph>\<open>and\<close> a row-1 entry \<open>\<ge> 5\<close>.  A
  counterexample only has to be \<^emph>\<open>checked\<close>, though --- and this one now is.\<close>


end
