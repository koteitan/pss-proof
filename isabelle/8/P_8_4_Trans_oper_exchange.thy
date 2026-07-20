theory P_8_4_Trans_oper_exchange
  imports Support_8_C
begin

subsection \<open>§8.4 条件(III)か(IV)の下での展開規則\<close>

text \<open>This subsection (article ## 条件(III)か(IV)の下での展開規則) builds up to the
  exchange relation between the translation \<open>Trans\<close> and the pair-sequence
  fundamental sequence under conditions (III)/(IV).

  COMMON SETUP / NOTATION used throughout the article's §8.4 statements:
    \<^item> \<open>j\<^sub>1 = Lng M - 1\<close>, the rightmost index;
    \<^item> \<open>j\<^sub>0\<close> = the row-0 nearest ancestor of \<open>j\<^sub>1\<close> (\<open>= parent M 0 j\<^sub>1\<close>);
    \<^item> \<open>j\<^sub>-\<^sub>2\<close> = the \<^bold>\<open>unique\<close> \<open>j\<close> with \<open>(1,j) <\<^bsub>M\<^esub>\<^sup>Next (1,j\<^sub>1)\<close>, i.e.
      \<open>nextR M 1 j\<^sub>-\<^sub>2 j\<^sub>1\<close>; modelled by \<open>parent M 1 j\<^sub>1\<close> under \<open>hasParent M 1 j\<^sub>1\<close>;
    \<^item> \<open>j\<^sub>-\<^sub>1 = Adm M j\<^sub>0\<close>, \<open>j\<^sub>-\<^sub>3 = Adm M j\<^sub>-\<^sub>2\<close>;
    \<^item> "条件(III)/(IV)/(V)/(VI)" = \<open>transCondIII\<close>/\<open>transCondIV\<close>/\<open>transCondV\<close>/\<open>transCondVI\<close>;
    \<^item> the Buchholz-side fundamental sequence \<open>t[n]\<close> is \<open>operB t (numBT n)\<close>, and
      \<open>< / \<le>\<close> on \<open>T\<^bsub>B\<^esub>\<close> are \<open>lessBT\<close>/\<open>leBT\<close>.

  FAITHFULNESS / DEFERRAL.  Most of the auxiliary §8.4 \<^emph>\<open>lemmas\<close> state relations
  among the \<^emph>\<open>internal symbols of the \<open>Trans\<close> recursion\<close> (\<open>c\<^sub>1\<close>, \<open>c\<^sub>2\<close>, \<open>t\<^sub>2\<close>,
  \<open>t\<^sub>3\<close>, \<open>t\<^sub>4\<close>, \<open>v\<close>, the scb-strings \<open>s\<^sub>1\<close>/\<open>b\<^sub>1\<close>, \<open>s'\<^sub>0\<dots>b'\<^sub>0\<close>, \<dots>) — the same
  symbols that, in §7.3, are \<^bold>\<open>not\<close> exposed as separate Isabelle functions (cf.
  the deferred §7.3 命題（\<open>c\<^sub>1\<close>と\<open>c\<^sub>2\<close>の大小関係）).  Those auxiliary lemmas are
  therefore \<^bold>\<open>deferred\<close> (documented as \<open>text\<close> notes with the precise blocking
  symbols), and only the two \<^emph>\<open>externally-statable\<close> facts — the headline
  proposition and the fundamental-sequence basic property — are transcribed as
  \<open>sorry\<close> lemmas.\<close>

text \<open>命題（条件(III)か(IV)の下での\<open>Trans\<close>と基本列の交換関係） (§8.4): for
  \<open>M \<in> ST\<^bsub>PS\<^esub> \<inter> PT\<^bsub>PS\<^esub>\<close> and \<open>n \<in> \<nat>\<^sub>+\<close>, assuming a unique \<open>j\<^sub>-\<^sub>2\<close> with
  \<open>(1,j\<^sub>-\<^sub>2) <\<^bsub>M\<^esub>\<^sup>Next (1,j\<^sub>1)\<close> exists (\<open>hasParent M 1 (Lng M - 1)\<close>), if
  \<open>j\<^sub>1 > 1\<close> and \<open>M\<close> satisfies condition (III) or (IV), then:
    (1) \<open>Trans(M[n]) \<le> Trans(M)[n-1]\<close>;
    (2) \<open>Trans(M[n]) < Trans(M)\<close>;
    (3) \<open>Trans(M)[n-1] < Trans(M[n+1])\<close>.
  Here \<open>Trans(M)[k] = operB (Trans M) (numBT k)\<close> is the Buchholz-side
  fundamental sequence.  (The setup symbols \<open>j\<^sub>-\<^sub>2\<close>/\<open>j\<^sub>-\<^sub>3\<close> appear only in the
  hypothesis; the conclusions (1)–(3) are symbol-free, hence transcribable.)\<close>

text \<open>The old \<open>_corrected\<close> helper family used the pre-A23, transposed
  reading of Buchholz's rule and therefore compared with index \<open>n\<close>.  After A23,
  @{thm [source] oy1_base1Y} supplies the missing re-seeded base comparison
  \<open>A\<^sub>0 < ins 0\<^sub>B\<close>.  The following small tower lemma records exactly why this
  gives the article's printed index \<open>n-1\<close>.\<close>

lemma p84_exchange1_core:
  fixes M :: pairseq and n e3 ub :: nat and A0 :: BT and hole :: BP
    and s0 b0 s1 b1 :: "Sym list" and body :: BT
  assumes n1: "1 \<le> n"
    and wrap: "flatBT body = s0 @ flatBP hole @ b0"
    and b0RP: "\<forall>x \<in> set b0. x = RP"
    and b1RP: "\<forall>x \<in> set b1. x = RP"
    and fM: "flatBT (Trans ((M::pairseq)[n]))
          = s1 @ flatBP (DB (enat e3) (d4vx_core s0 ub b0 A0 (n - 1))) @ b1"
    and fO: "flatBT (operB (Trans M) (numBT (n - 1)))
          = s1 @ flatBP (DB (enat e3) (d4vx_core s0 ub b0 0\<^sub>B n)) @ b1"
    and base1: "lessBT A0 (d4vx_ins s0 ub b0 0\<^sub>B)"
  shows "leBT (Trans ((M::pairseq)[n])) (operB (Trans M) (numBT (n - 1)))"
proof -
  have mono: "lessBT (d4vx_core s0 ub b0 A0 (n - 1))
                    (d4vx_core s0 ub b0 (d4vx_ins s0 ub b0 0\<^sub>B) (n - 1))"
    by (rule oy1_core_mono[OF wrap b0RP base1])
  have tower: "d4vx_core s0 ub b0 (d4vx_ins s0 ub b0 0\<^sub>B) (n - 1)
             = d4vx_core s0 ub b0 0\<^sub>B n"
    using oy1_core_add[of s0 ub b0 "0\<^sub>B" "n - 1" 1] n1 by simp
  have core: "lessBP (DB (enat e3) (d4vx_core s0 ub b0 A0 (n - 1)))
                    (DB (enat e3) (d4vx_core s0 ub b0 0\<^sub>B n))"
    using mono tower by simp
  have "lessBT (Trans ((M::pairseq)[n])) (operB (Trans M) (numBT (n - 1)))"
    by (rule scbext_lessBT[OF fM fO b1RP core])
  thus ?thesis by blast
qed

text \<open>The non-corner regime \<open>j\<^sub>-\<^sub>3 < j\<^sub>-\<^sub>1\<close>.  This includes every
  condition-(III) host and the non-\<open>admeq\<close> condition-(IV) hosts.  The producer
  package and every annotation are the frozen §8 machinery; only the one-line
  A23 re-seeding comparison above is new.\<close>

lemma p84_exchange_ltJ:
  assumes MST: "M \<in> ST_PS" and MPT: "M \<in> PT_PS" and n1: "1 \<le> n"
    and hp: "hasParent M 1 (Lng M - 1)"
    and j1gt: "1 < Lng M - 1"
    and branch: "transCondIII M \<or> transCondIV M"
    and ltJ: "s84x_jm3 M < transJm1 M"
  shows "leBT (Trans ((M::pairseq)[n])) (operB (Trans M) (numBT (n - 1)))"
    and "lessBT (Trans ((M::pairseq)[n])) (Trans M)"
    and "lessBT (operB (Trans M) (numBT (n - 1))) (Trans ((M::pairseq)[n+1]))"
proof -
  let ?e3 = "entry M 1 (s84x_jm3 M)"
  let ?v1 = "entry M 1 (Lng M - 1)"
  let ?ub = "?v1 - 1"
  let ?A0 = "bpHeadT (Trans (Pred (s84x_N M)))"
  let ?body = "bpHeadT (Trans (s84x_N M))"
  obtain s0 b0 s1 b1 where
      b0RP: "\<forall>x \<in> set b0. x = RP" and b1RP: "\<forall>x \<in> set b1. x = RP"
    and inner: "scb_decomp ?body s0 (flatBT (Dpt (enat ?v1) 0\<^sub>B)) b0"
    and k1: "scb_kind1 (Trans M) s1 (flatBT (Dpt (enat ?e3) ?body)) b1"
    and MN: "\<forall>m. 1 \<le> m \<longrightarrow> flatBT (Trans ((M::pairseq)[m]))
          = s1 @ Dsym (enat ?e3) # flatBT (d4vx_core s0 ?ub b0 ?A0 (m - 1)) @ b1"
    and base0: "lessBT (Dpt (enat ?ub) 0\<^sub>B) ?A0"
    and base1: "lessBT ?A0 (d4vx_ins s0 ?ub b0 0\<^sub>B)"
    and A0TB: "?A0 \<in> T_B"
    by (rule oi5_IIIIV_pkg[OF MST MPT hp j1gt branch ltJ])
  note regime = oi5_regime[OF MST MPT hp j1gt branch]
  have uv: "?e3 < ?v1" by (rule regime(1))
  have bodyT: "?body \<in> T_B" by (rule regime(3))
  have dbbody: "domB ?body = TBv (enat ?ub)" by (rule regime(4))
  have TT: "Trans M \<in> T_B" by (rule regime(5))
  have wrap: "flatBT ?body = s0 @ flatBP (DB (enat ?v1) 0\<^sub>B) @ b0"
    using inner by (simp add: scb_decomp_def)
  have bodyne: "?body \<noteq> 0\<^sub>B"
  proof
    assume z: "?body = 0\<^sub>B"
    have "[Zsym] = s0 @ [Dsym (enat ?v1), Zsym] @ b0" using wrap z by simp
    thus False by (cases s0) auto
  qed
  have fseq: "flatBT (operB (Trans M) (numBT k))
      = s1 @ (Dsym (enat ?e3)
          # concat (replicate (k + 1) (s0 @ [Dsym (enat ?ub)]))
          @ [Zsym] @ concat (replicate (k + 1) b0)) @ b1" for k
    by (rule d13x_fseq_condIII[OF TT uv bodyT dbbody bodyne inner k1])
  have Yflat: "flatBT (d4vx_core s0 ?ub b0 0\<^sub>B k)
      = concat (replicate k (s0 @ [Dsym (enat ?ub)]))
          @ [Zsym] @ concat (replicate k b0)" for k
    using d4vx_core_flat[OF wrap b0RP] by simp
  have fO: "flatBT (operB (Trans M) (numBT (n - 1)))
      = s1 @ flatBP (DB (enat ?e3) (d4vx_core s0 ?ub b0 0\<^sub>B n)) @ b1"
    using fseq[of "n - 1"] Yflat[of n] n1 by simp
  have fM: "flatBT (Trans ((M::pairseq)[n]))
      = s1 @ flatBP (DB (enat ?e3) (d4vx_core s0 ?ub b0 ?A0 (n - 1))) @ b1"
    using MN n1 by simp
  show C1: "leBT (Trans ((M::pairseq)[n])) (operB (Trans M) (numBT (n - 1)))"
    by (rule p84_exchange1_core[OF n1 wrap b0RP b1RP fM fO base1])
  show C2: "lessBT (Trans ((M::pairseq)[n])) (Trans M)"
    by (rule y5_Trans_descend[OF MST n1]) (use j1gt in linarith)
  have zX: "lessBT (0\<^sub>B :: BT) (Dpt (enat ?ub) 0\<^sub>B)" by simp
  have inslt: "lessBT (d4vx_ins s0 ?ub b0 0\<^sub>B)
                    (d4vx_ins s0 ?ub b0 (Dpt (enat ?ub) 0\<^sub>B))"
    by (rule c4cx_d4vx_ins_mono[OF wrap b0RP zX])
  have base1old: "lessBT ?A0 (d4vx_ins s0 ?ub b0 (Dpt (enat ?ub) 0\<^sub>B))"
    by (rule lessBT_trans[OF base1 inslt])
  have OT: "Trans M \<in> OT_B" by (rule y5_Trans_OT_B[OF MST])
  have Lbase: "leBT (Dpt (enat ?ub) 0\<^sub>B) (d4vx_ins s0 ?ub b0 0\<^sub>B)"
    by (rule oi5_LbaseU[OF MST MPT j1gt branch OT hp inner])
  have tri: "lessBT (Trans ((M::pairseq)[n])) (operB (Trans M) (numBT n))
           \<and> lessBT (operB (Trans M) (numBT (n - 1))) (Trans ((M::pairseq)[n+1]))"
    by (rule w84x_exchange13_core[OF MST n1 uv bodyT bodyne dbbody inner k1 _
          base0 base1old Lbase]) (use MN in blast)
  show "lessBT (operB (Trans M) (numBT (n - 1))) (Trans ((M::pairseq)[n+1]))"
    using tri by blast
qed

text \<open>The remaining condition-(IV) equality corner is anchored at \<open>c\<^sub>2\<close>
  rather than at \<open>Trans (s84x_N M)\<close>.  Its frozen producer is
  @{thm [source] c4cx2_condIV_mnform_of_slice}; A23's matching re-seeded base is
  @{thm [source] oy1_base1Y_t2}.\<close>

lemma p84_exchange_IV_admeq:
  assumes MST: "M \<in> ST_PS" and MPT: "M \<in> PT_PS" and n1: "1 \<le> n"
    and hp: "hasParent M 1 (Lng M - 1)"
    and j1gt: "1 < Lng M - 1"
    and cIV: "transCondIV M"
    and admeq: "Adm M (s84x_jm2 M) = transJm1 M"
  shows "leBT (Trans ((M::pairseq)[n])) (operB (Trans M) (numBT (n - 1)))"
    and "lessBT (Trans ((M::pairseq)[n])) (Trans M)"
    and "lessBT (operB (Trans M) (numBT (n - 1))) (Trans ((M::pairseq)[n+1]))"
proof -
  let ?e3 = "entry M 1 (s84x_jm3 M)"
  let ?v1 = "entry M 1 (Lng M - 1)"
  let ?ub = "?v1 - 1"
  have MR: "M \<in> RT_PS" using MST m_6_7_ST_PS_subseteq_RT_PS by blast
  have branch: "transCondIII M \<or> transCondIV M" by (rule disjI2[OF cIV])
  have nVI: "\<not> transCondVI M" using c4dx_condIV_excl(4)[OF cIV] .
  have T1: "transT1 M \<noteq> 0\<^sub>B" using s84d_L4_regime[OF MST MPT hp nVI] by simp
  have J1pos: "transJ1 M > 0" using j1gt by (simp add: transJ1_def)
  have TT: "Trans M \<in> T_B" by (rule m_7_3_Trans_in_T_B[OF MR])
  have reg: "s84x_jm2 M < transJ0 M \<or> adm M (transJ0 M)"
    using m_8_4_oper_props_1(1)[OF MST MPT hp j1gt] cIV by blast
  have rng: "s84x_jm2 M + 1 < Lng M - 1" by (rule s84d_L5_rng[OF MST MPT hp nVI])
  have REGS: "s84x_jm3 M < s84x_jm2 M \<Longrightarrow>
      cfbx_reg (s84x_jm2 M - s84x_jm3 M) (Red (s84x_N M))"
    by (rule mcx_regS[OF MST MPT hp j1gt branch])
  have REGSP: "s84x_jm3 M < s84x_jm2 M \<Longrightarrow>
      Br (Red (Pred (s84x_N M))) \<noteq> [] \<Longrightarrow>
      cfbx_reg (s84x_jm2 M - s84x_jm3 M) (Red (Pred (s84x_N M)))"
    by (rule slx37_regSP_uncond[OF MST MPT hp j1gt branch])
  obtain sb where d1: "scb_decomp (transC2 M)
      (Dsym (enat (entry M 1 (transJm1 M))) # fst sb)
      (flatBT (Dpt (enat ?v1) 0\<^sub>B)) (snd sb)"
    using ex1_implies_ex[OF m_8_4_slice_scb_part1[OF MST MPT hp nVI admeq]] by auto
  have d2: "scb_decomp (Trans (s84x_Np M))
      (Dsym (enat (entry M 1 (s84x_jm2 M))) # fst sb)
      (flatBT (Dpt (enat ?v1) 0\<^sub>B)) (snd sb)"
    by (rule cpx_d2_condIV[OF MST MPT hp nVI admeq REGS d1])
  have d3: "Trans (Pred (s84x_Np M))
      = Dpt (enat (entry M 1 (s84x_jm2 M))) (transT2 M)"
    by (rule cpx_d3_condIV[OF MST MPT hp nVI admeq rng REGSP])
  obtain s0 b0 where
    inner: "scb_decomp (bpHeadT (transC2 M)) s0
              (flatBT (Dpt (enat ?v1) 0\<^sub>B)) b0"
    and MN: "\<forall>m. 1 \<le> m \<longrightarrow> flatBT (Trans ((M::pairseq)[m]))
       = s84x_s1 M @ Dsym (enat ?e3)
           # flatBT (d4vx_core s0 ?ub b0 (transT2 M) (m - 1)) @ s84x_b1 M"
    using c4cx2_condIV_mnform_of_slice[OF MST MPT hp cIV reg admeq d1 d2 d3] by blast
  have b0RP: "\<forall>x \<in> set b0. x = RP" using inner by (simp add: scb_decomp_def)
  have wrap: "flatBT (bpHeadT (transC2 M))
      = s0 @ flatBP (DB (enat ?v1) 0\<^sub>B) @ b0"
    using inner by (simp add: scb_decomp_def)
  have uv: "?e3 < ?v1" by (rule c4dx_uv[OF hp])
  have bodyT: "bpHeadT (transC2 M) \<in> T_B"
  proof -
    obtain t3 t4 where t3TB: "t3 \<in> T_B" and t4TB: "t4 \<in> T_B"
      and body: "bpHeadT (transC2 M) = t3 +\<^sub>B Dpt (enat (entry M 1 (transJ0 M)))
                    (t4 +\<^sub>B Dpt (enat ?v1) 0\<^sub>B)"
      using c4dx_condIV_c2body_shape[OF MR MPT J1pos T1 cIV] by blast
    obtain as where "t3 = Trm as" by (cases t3)
    moreover obtain bs where "t4 = Trm bs" by (cases t4)
    ultimately show ?thesis using body t3TB t4TB by (auto simp: T_B_def)
  qed
  have bodyne: "bpHeadT (transC2 M) \<noteq> 0\<^sub>B" by (rule bpHeadT_transC2_nonzero)
  have dbbody: "domB (bpHeadT (transC2 M)) = TBv (enat ?ub)"
    by (rule c4dx_condIV_dbbody[OF MR MPT J1pos T1 cIV])
  have k1: "scb_kind1 (Trans M) (s84x_s1 M)
      (flatBT (Dpt (enat ?e3) (bpHeadT (transC2 M)))) (s84x_b1 M)"
    by (rule c4dx_condIV_k1[OF MST MPT hp cIV admeq])
  have b1RP: "\<forall>x \<in> set (s84x_b1 M). x = RP"
    using k1 by (simp add: scb_kind1_def scb_decomp_def)
  have fseq: "flatBT (operB (Trans M) (numBT k))
      = s84x_s1 M @ (Dsym (enat ?e3)
          # concat (replicate (k + 1) (s0 @ [Dsym (enat ?ub)]))
          @ [Zsym] @ concat (replicate (k + 1) b0)) @ s84x_b1 M" for k
    by (rule d13x_fseq_condIII[OF TT uv bodyT dbbody bodyne inner k1])
  have Yflat: "flatBT (d4vx_core s0 ?ub b0 0\<^sub>B k)
      = concat (replicate k (s0 @ [Dsym (enat ?ub)]))
          @ [Zsym] @ concat (replicate k b0)" for k
    using d4vx_core_flat[OF wrap b0RP] by simp
  have fO: "flatBT (operB (Trans M) (numBT (n - 1)))
      = s84x_s1 M @ flatBP (DB (enat ?e3) (d4vx_core s0 ?ub b0 0\<^sub>B n))
          @ s84x_b1 M"
    using fseq[of "n - 1"] Yflat[of n] n1 by simp
  have fM: "flatBT (Trans ((M::pairseq)[n]))
      = s84x_s1 M @ flatBP (DB (enat ?e3)
          (d4vx_core s0 ?ub b0 (transT2 M) (n - 1))) @ s84x_b1 M"
    using MN n1 by simp
  have base1: "lessBT (transT2 M) (d4vx_ins s0 ?ub b0 0\<^sub>B)"
    by (rule oy1_base1Y_t2[OF MR MPT J1pos T1 cIV inner])
  show C1: "leBT (Trans ((M::pairseq)[n])) (operB (Trans M) (numBT (n - 1)))"
    by (rule p84_exchange1_core[OF n1 wrap b0RP b1RP fM fO base1])
  show C2: "lessBT (Trans ((M::pairseq)[n])) (Trans M)"
    by (rule y5_Trans_descend[OF MST n1]) (use j1gt in linarith)
  have old: "lessBT (Trans ((M::pairseq)[n])) (operB (Trans M) (numBT n))
       \<and> lessBT (Trans ((M::pairseq)[n])) (Trans M)
       \<and> lessBT (operB (Trans M) (numBT (n - 1))) (Trans ((M::pairseq)[n+1]))"
    by (rule cpx_condIV_exchange_uncond[OF MST MPT hp cIV admeq n1
          y3h_LbaseH_uncond[OF MST MPT j1gt branch hp]])
  show "lessBT (operB (Trans M) (numBT (n - 1))) (Trans ((M::pairseq)[n+1]))"
    using old by blast
qed

lemma p_8_4_Trans_oper_exchange:
  assumes "M \<in> ST_PS" "M \<in> PT_PS" "n \<ge> 1"
    and "hasParent M 1 (Lng M - 1)"
    and "Lng M - 1 > 1"
    and "transCondIII M \<or> transCondIV M"
  shows "leBT (Trans (M[n])) (operB (Trans M) (numBT (n - 1)))"
    and "lessBT (Trans (M[n])) (Trans M)"
    and "lessBT (operB (Trans M) (numBT (n - 1))) (Trans (M[n+1]))"
proof -
  have n1: "1 \<le> n" using assms(3) .
  have j1gt: "1 < Lng M - 1" using assms(5) .
  have branch: "transCondIII M \<or> transCondIV M" using assms(6) .
  have all: "leBT (Trans (M[n])) (operB (Trans M) (numBT (n - 1)))
      \<and> lessBT (Trans (M[n])) (Trans M)
      \<and> lessBT (operB (Trans M) (numBT (n - 1))) (Trans (M[n+1]))"
  proof (cases "s84x_jm3 M < transJm1 M")
    case True
    show ?thesis
      using p84_exchange_ltJ[OF assms(1,2) n1 assms(4) j1gt branch True] by blast
  next
    case False
    have corner: "transCondIV M \<and> Adm M (s84x_jm2 M) = transJm1 M"
      using oi5_ltJ_or_IVadmeq[OF assms(1,2,4) j1gt branch] False by blast
    have cIV: "transCondIV M" using corner by blast
    have admeq: "Adm M (s84x_jm2 M) = transJm1 M" using corner by blast
    show ?thesis
      using p84_exchange_IV_admeq[OF assms(1,2) n1 assms(4) j1gt cIV admeq] by blast
  qed
  show "leBT (Trans (M[n])) (operB (Trans M) (numBT (n - 1)))" using all by blast
  show "lessBT (Trans (M[n])) (Trans M)" using all by blast
  show "lessBT (operB (Trans M) (numBT (n - 1))) (Trans (M[n+1]))" using all by blast
qed

end
