theory Frontier_7_030
  imports P_7_4_Trans_nextAdm
begin

section \<open>§7.4 系（\<open>Mark\<close>と\<open><\<^bsub>M\<^esub>\<^sup>NextAdm\<close>の関係） — m_7_4_Mark_nextAdm\<close>

text \<open>Helper: a marked image \<open>Mark M m\<close> of a reduced \<open>M\<close> with \<open>Trans M \<noteq> Trm []\<close>
  is a single principal term, hence \<open>\<noteq> Trm []\<close> and \<open>isPTB_str\<close>.  It is the
  marked block of the (nonzero) \<open>Trans M\<close>, recovered from the
  \<open>(Trans M, Mark M m) \<in> MarkedB\<close> invariant.\<close>

lemma mark_marked_principal:
  assumes MR: "M \<in> RT_PS" and mM: "(M, m) \<in> Marked" and tne: "Trans M \<noteq> Trm []"
  shows "\<exists>p. Mark M m = Trm [p]" and "Mark M m \<noteq> Trm []"
    and "isPTB_str (flatBT (Mark M m))"
proof -
  have mb: "(Trans M, Mark M m) \<in> MarkedB"
    by (rule m_7_3_Trans_Mark_MarkedB[OF MR mM])
  obtain s b where d: "scb_decomp (Trans M) s (flatBT (Mark M m)) b"
    using mb by (auto simp: MarkedB_def)
  show ipt: "isPTB_str (flatBT (Mark M m))"
    using d tne by (simp add: scb_decomp_def)
  then obtain pc where pcl: "flatBT (Mark M m) = flatBP pc"
    by (auto simp: isPTB_str_def)
  show "\<exists>p. Mark M m = Trm [p]"
  proof -
    have "flatBT (Mark M m) = flatBT (Trm [pc])" using pcl by simp
    hence "Mark M m = Trm [pc]" by (rule m_7_flatBT_inj)
    thus ?thesis by blast
  qed
  then obtain p where "Mark M m = Trm [p]" by blast
  thus "Mark M m \<noteq> Trm []" by simp
qed

text \<open>Helper (marked case): for a reduced \<open>M\<close> and marked columns \<open>m \<le> m'\<close> with
  \<open>m' < Lng M - 1\<close>, there is a UNIQUE common scb-position \<open>(s\<^sub>0,b\<^sub>0)\<close> with
  \<open>(s\<^sub>0, Mark(Pred M, m'), b\<^sub>0)\<close> an scb-decomposition of \<open>Mark(Pred M, m)\<close> and
  \<open>(s\<^sub>0, Mark(M, m'), b\<^sub>0)\<close> one of \<open>Mark(M, m)\<close>.  Proof by the composition rule
  on \<open>Trans\<close>: by @{thm [source] m_7_4_Trans_Mark_Pred} both \<open>Mark _ m\<close> and
  \<open>Mark _ m'\<close> sit in \<open>Trans _\<close> at common positions \<open>(s\<^sub>m,b\<^sub>m)\<close> resp. \<open>(s\<^sub>m\<^sub>'\<^sub>,b\<^sub>m\<^sub>'\<^sub>)\<close>;
  by @{thm [source] Mark_MarkedB_nest} \<open>Mark _ m'\<close> nests in \<open>Mark _ m\<close>; composing
  and using @{thm [source] m_7_2_scb_unique_sb} pins the nest position to the
  SAME \<open>(s\<^sub>0,b\<^sub>0)\<close> for both \<open>Pred M\<close> and \<open>M\<close>.\<close>

lemma Mark_nest_common_marked:
  assumes MR: "M \<in> RT_PS"
    and mM: "(M, m) \<in> Marked" and mM': "(M, m') \<in> Marked"
    and mle: "m \<le> m'" and m'lt: "m' < Lng M - 1"
  shows "\<exists>!sb. scb_decomp (Mark (Pred M) m) (fst sb) (flatBT (Mark (Pred M) m')) (snd sb)
            \<and> scb_decomp (Mark M m) (fst sb) (flatBT (Mark M m')) (snd sb)"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  have mlt: "m < Lng M - 1" using mle m'lt by simp
  have L: "1 < Lng M" using m'lt by linarith
  have predRT: "Pred M \<in> RT_PS" by (rule Pred_RT_PS[OF MR])
  have predT: "Pred M \<in> T_PS" using predRT by (simp add: RT_PS_def)
  have mP: "(Pred M, m) \<in> Marked" by (rule Marked_Pred[OF MT L mM mlt])
  have mP': "(Pred M, m') \<in> Marked" by (rule Marked_Pred[OF MT L mM' m'lt])
  show ?thesis
  proof (cases "m = m'")
    case eq: True
    \<comment> \<open>reflexive: the core equals the whole term, position \<open>([],[])\<close>\<close>
    have selfdecomp: "\<And>t::BT. scb_decomp t [] (flatBT t) []
                        \<longleftrightarrow> (t \<noteq> Trm [] \<longrightarrow> isPTB_str (flatBT t))"
      by (auto simp: scb_decomp_def)
    \<comment> \<open>generic: a marked block is principal (\<open>isPTB_str\<close>) or empty\<close>
    have ipt_gen: "\<And>N k. N \<in> RT_PS \<Longrightarrow> (N, k) \<in> Marked
        \<Longrightarrow> Mark N k \<noteq> Trm [] \<longrightarrow> isPTB_str (flatBT (Mark N k))"
    proof -
      fix N k assume NR: "N \<in> RT_PS" and kN: "(N, k) \<in> Marked"
      show "Mark N k \<noteq> Trm [] \<longrightarrow> isPTB_str (flatBT (Mark N k))"
      proof
        assume kne: "Mark N k \<noteq> Trm []"
        have mb: "(Trans N, Mark N k) \<in> MarkedB"
          by (rule m_7_3_Trans_Mark_MarkedB[OF NR kN])
        obtain s b where d: "scb_decomp (Trans N) s (flatBT (Mark N k)) b"
          using mb by (auto simp: MarkedB_def)
        \<comment> \<open>\<open>flatBT (Mark N k)\<close> is nonempty and does not equal \<open>[Zsym]\<close>
            (a nonempty \<open>Trm\<close> flattens to a list whose head is \<open>Dsym\<close> or \<open>LP\<close>)\<close>
        have knhd: "flatBT (Mark N k) \<noteq> [] \<and> flatBT (Mark N k) \<noteq> [Zsym]"
        proof (cases "Mark N k")
          case (Trm xs)
          show ?thesis
          proof (cases xs)
            case Nil thus ?thesis using Trm kne by simp
          next
            case (Cons a as)
            obtain u t' where a: "a = DB u t'" by (cases a)
            show ?thesis
            proof (cases as)
              case Nil thus ?thesis using Trm Cons a by simp
            next
              case (Cons b bs) thus ?thesis using Trm \<open>xs = a # as\<close> by simp
            qed
          qed
        qed
        have tNne: "Trans N \<noteq> Trm []"
        proof
          assume z: "Trans N = Trm []"
          have "[Zsym] = s @ flatBT (Mark N k) @ b" using d z by (simp add: scb_decomp_def)
          thus False using knhd
            by (cases s; cases b rule: rev_cases) auto
        qed
        show "isPTB_str (flatBT (Mark N k))" using d tNne by (simp add: scb_decomp_def)
      qed
    qed
    have iptP: "Mark (Pred M) m \<noteq> Trm [] \<longrightarrow> isPTB_str (flatBT (Mark (Pred M) m))"
      by (rule ipt_gen[OF predRT mP])
    have iptM: "Mark M m \<noteq> Trm [] \<longrightarrow> isPTB_str (flatBT (Mark M m))"
      by (rule ipt_gen[OF MR mM])
    have dP0: "scb_decomp (Mark (Pred M) m) [] (flatBT (Mark (Pred M) m')) []"
      using selfdecomp[of "Mark (Pred M) m"] iptP eq by simp
    have dM0: "scb_decomp (Mark M m) [] (flatBT (Mark M m')) []"
      using selfdecomp[of "Mark M m"] iptM eq by simp
    show ?thesis
    proof (rule ex1I[of _ "([], [])"])
      show "scb_decomp (Mark (Pred M) m) (fst ([]::Sym list,[]::Sym list))
               (flatBT (Mark (Pred M) m')) (snd ([],[]))
          \<and> scb_decomp (Mark M m) (fst ([]::Sym list,[]::Sym list))
               (flatBT (Mark M m')) (snd ([],[]))"
        using dP0 dM0 by simp
    next
      fix sb
      assume A: "scb_decomp (Mark (Pred M) m) (fst sb) (flatBT (Mark (Pred M) m')) (snd sb)
               \<and> scb_decomp (Mark M m) (fst sb) (flatBT (Mark M m')) (snd sb)"
      have dsb: "scb_decomp (Mark (Pred M) m) (fst sb) (flatBT (Mark (Pred M) m)) (snd sb)"
        using A eq by simp
      have e: "flatBT (Mark (Pred M) m) = fst sb @ flatBT (Mark (Pred M) m) @ snd sb"
        using dsb by (simp add: scb_decomp_def)
      have "length (flatBT (Mark (Pred M) m))
            = length (fst sb) + length (flatBT (Mark (Pred M) m)) + length (snd sb)"
        using arg_cong[OF e, of length] by simp
      hence "length (fst sb) = 0 \<and> length (snd sb) = 0" by simp
      hence "fst sb = [] \<and> snd sb = []" by simp
      thus "sb = ([], [])" by (cases sb) auto
    qed
  next
    case neq: False
    have mltm': "m < m'" using mle neq by simp
  \<comment> \<open>Trans-positions of \<open>Mark _ m\<close> and \<open>Mark _ m'\<close> (common to \<open>Pred M\<close> and \<open>M\<close>)\<close>
  obtain sm bm where
    Pm: "scb_decomp (Trans (Pred M)) sm (flatBT (Mark (Pred M) m)) bm"
    and Mm: "scb_decomp (Trans M) sm (flatBT (Mark M m)) bm"
    using m_7_4_Trans_Mark_Pred[OF mM MR mlt] ex1_implies_ex by force
  obtain sm' bm' where
    Pm': "scb_decomp (Trans (Pred M)) sm' (flatBT (Mark (Pred M) m')) bm'"
    and Mm': "scb_decomp (Trans M) sm' (flatBT (Mark M m')) bm'"
    using m_7_4_Trans_Mark_Pred[OF mM' MR m'lt] ex1_implies_ex by force
  \<comment> \<open>\<open>Mark _ m'\<close> nests in \<open>Mark _ m\<close> (order preservation)\<close>
  have nestP: "(Mark (Pred M) m, Mark (Pred M) m') \<in> MarkedB"
    using Mark_MarkedB_nest mP mP' mle predRT by blast
  have nestM: "(Mark M m, Mark M m') \<in> MarkedB"
    using Mark_MarkedB_nest mM mM' mle MR by blast
  obtain sP bP where dP: "scb_decomp (Mark (Pred M) m) sP (flatBT (Mark (Pred M) m')) bP"
    using nestP by (auto simp: MarkedB_def)
  obtain sM bM where dM: "scb_decomp (Mark M m) sM (flatBT (Mark M m')) bM"
    using nestM by (auto simp: MarkedB_def)
  \<comment> \<open>principality and non-emptiness of the cores\<close>
  have tPne: "Trans (Pred M) \<noteq> Trm []"
  proof -
    have nzP: "\<not> zeroT (Pred M)"
    proof
      assume "zeroT (Pred M)"
      hence "Lng (Pred M) = 1" by (simp add: zeroT_def)
      moreover have "Lng (Pred M) = Lng M - 1" using L by (simp add: Pred_def)
      ultimately have "Lng M = 2" using L by linarith
      thus False using m'lt mltm' by simp
    qed
    show ?thesis using m_7_3_Trans_zeroT[OF predRT] nzP by auto
  qed
  have tMne: "Trans M \<noteq> Trm []"
  proof -
    have "\<not> zeroT M" using L by (auto simp: zeroT_def)
    thus ?thesis using m_7_3_Trans_zeroT[OF MR] by auto
  qed
  have prinPm: "\<exists>p. Mark (Pred M) m = Trm [p]"
    by (rule mark_marked_principal(1)[OF predRT mP tPne])
  have prinMm: "\<exists>p. Mark M m = Trm [p]"
    by (rule mark_marked_principal(1)[OF MR mM tMne])
  have mPmne: "Mark (Pred M) m \<noteq> Trm []"
    by (rule mark_marked_principal(2)[OF predRT mP tPne])
  have mMmne: "Mark M m \<noteq> Trm []"
    by (rule mark_marked_principal(2)[OF MR mM tMne])
  \<comment> \<open>compose: position of \<open>Mark _ m'\<close> in \<open>Trans _\<close> via \<open>Mark _ m\<close>; uniqueness pins it\<close>
  have compP: "scb_decomp (Trans (Pred M)) (sm @ sP) (flatBT (Mark (Pred M) m')) (bP @ bm)"
    by (rule m_7_2_scb_compose[OF prinPm Pm dP])
  have cohP: "sm @ sP = sm' \<and> bP @ bm = bm'"
    by (rule m_7_2_scb_unique_sb[OF compP Pm' tPne])
  have compM: "scb_decomp (Trans M) (sm @ sM) (flatBT (Mark M m')) (bM @ bm)"
    by (rule m_7_2_scb_compose[OF prinMm Mm dM])
  have cohM: "sm @ sM = sm' \<and> bM @ bm = bm'"
    by (rule m_7_2_scb_unique_sb[OF compM Mm' tMne])
  \<comment> \<open>hence \<open>sP = sM\<close> and \<open>bP = bM\<close>: the common position\<close>
  have sEq: "sP = sM"
  proof -
    have "sm @ sP = sm @ sM" using cohP cohM by simp
    thus ?thesis by simp
  qed
  have bEq: "bP = bM"
  proof -
    have "bP @ bm = bM @ bm" using cohP cohM by simp
    thus ?thesis by simp
  qed
  have dM': "scb_decomp (Mark M m) sP (flatBT (Mark M m')) bP"
    using dM sEq bEq by simp
  show ?thesis
  proof (rule ex1I[of _ "(sP, bP)"])
    show "scb_decomp (Mark (Pred M) m) (fst (sP,bP)) (flatBT (Mark (Pred M) m')) (snd (sP,bP))
        \<and> scb_decomp (Mark M m) (fst (sP,bP)) (flatBT (Mark M m')) (snd (sP,bP))"
      using dP dM' by simp
  next
    fix sb
    assume A: "scb_decomp (Mark (Pred M) m) (fst sb) (flatBT (Mark (Pred M) m')) (snd sb)
             \<and> scb_decomp (Mark M m) (fst sb) (flatBT (Mark M m')) (snd sb)"
    have "scb_decomp (Mark (Pred M) m) (fst sb) (flatBT (Mark (Pred M) m')) (snd sb)"
      using A by simp
    hence "fst sb = sP \<and> snd sb = bP"
      by (rule m_7_2_scb_unique_sb[OF _ dP mPmne])
    thus "sb = (sP, bP)" by (cases sb) auto
  qed
  qed
qed

end
