theory P_7_2_scb_fseq
  imports Frontier_7_054
begin

text \<open>命題（scb分解と基本列の関係） (§7.2), conjunct (2), GENERAL case,
  in the article's literal \<open>n+1\<close> form.  A24 is retracted: the apparent
  counterexample came from the earlier misreading of \<open>([].4)(ii)\<close>; under the
  corrected Buchholz basic sequence the printed statement is the faithful one.
  The marked principal is \<open>c\<^sub>2 = D\<^sub>u(body)\<close> whose body has \<open>flat(body) =
  s\<^sub>0 \<frown> flat(D\<^sub>v 0) \<frown> b\<^sub>0\<close> (the marked leaf \<open>D\<^sub>v 0\<close> sits on the trailing right
  spine, \<open>domB body = T\<^bsub>v-1\<^esub>\<close>), prefixed by \<open>s\<^sub>0\<close> and suffixed by an all-\<open>RP\<close>
  tail \<open>b\<^sub>0\<close>.  The RHS wraps \<open>(s\<^sub>0 D\<^bsub>v-1\<^esub>)\<close> exactly \<open>n+1\<close> times,
  as validated by @{path \<open>python/scb_fseq_kind1_check.py\<close>}.  The OUTER spine is transported by
  @{thm [source] operB_scb_spine}; the INNER tower by
  @{thm [source] xseq_body_tower_flat}.\<close>

lemma m_7_2_scb_fseq_kind1_general:
  fixes u v n :: nat
  assumes tT: "t \<in> T_B"
    and uv: "u < v"
    and bodyT: "body \<in> T_B"
    and dbbody: "domB body = TBv (enat (v - 1))"
    and bodyne: "body \<noteq> Trm []"
    and innerscb: "scb_decomp body s\<^sub>0 (flatBT (Dpt (enat v) 0\<^sub>B)) b\<^sub>0"
    and k1: "scb_kind1 t s\<^sub>1 (flatBT (Dpt (enat u) body)) b\<^sub>1"
  shows "v > u \<and>
         flatBT (operB t (numBT n)) =
           s\<^sub>1 @ (Dsym (enat u)
             # concat (replicate (n + 1) (s\<^sub>0 @ [Dsym (enat (v - 1))]))
             @ [Zsym]
             @ concat (replicate (n + 1) b\<^sub>0))
           @ b\<^sub>1"
proof -
  let ?cp = "DB (enat u) body"
  let ?D = "Dsym (enat (v - 1))"
  let ?xn = "xseq body (enat (v - 1)) n"
  let ?core = "operB body ?xn"
  let ?RHS = "Dprin (enat u) ?core"
  have vpos: "0 < v" using uv by simp
  \<comment> \<open>scb-decomp of \<open>t\<close> with marked principal \<open>?cp\<close>\<close>
  have dcp: "scb_decomp t s\<^sub>1 (flatBT (Trm [?cp])) b\<^sub>1"
    using k1 by (simp add: scb_kind1_def)
  have domcp: "domB (Trm [?cp]) = NatSet"
    by (rule domB_Du_body_NatSet[OF uv dbbody bodyne])
  have dfbody: "dfree_BT body" using bodyT by (simp add: T_B_def)
  have dfreecp: "dfree_BP ?cp" using dfbody by simp
  have vu: "enat u \<le> enat (v - 1)" using uv by simp
  have domcpz: "domB_operB_xseq_dom (Inr (Inl (Trm [?cp], numBT n)))"
    by (rule operB_dom_kind1[OF dbbody vu bodyne])
  have opercp: "operB (Trm [?cp]) (numBT n) = ?RHS"
    by (rule operB_Du_body_kind1_eval[OF uv dbbody bodyne])
  obtain qs where coreqs: "?core = Trm qs" by (cases "?core")
  have oprp: "operB (Trm [?cp]) (numBT n) = Trm [DB (enat u) (Trm qs)]"
    using opercp coreqs by simp
  \<comment> \<open>OUTER spine transport (NatSet marked principal)\<close>
  have flatid: "flatBT (operB t (numBT n))
                  = s\<^sub>1 @ flatBT (operB (Trm [?cp]) (numBT n)) @ b\<^sub>1"
    by (rule operB_scb_spine[OF dcp domcp dfreecp domcpz oprp])
  have flatid2: "flatBT (operB t (numBT n)) = s\<^sub>1 @ flatBT ?RHS @ b\<^sub>1"
    using flatid opercp by simp
  \<comment> \<open>INNER: the corrected \<open>([].4)(ii)\<close> value is \<open>D\<^sub>u body[x\<^sub>n]\<close>; transport
     \<open>flat (body[x\<^sub>n])\<close> over the body's own scb-spine (marked leaf \<open>D\<^sub>v 0\<close>,
     whose \<open>operB\<close>-image is the identity)\<close>
  let ?cp0 = "DB (enat v) 0\<^sub>B"
  have dcp0: "scb_decomp body s\<^sub>0 (flatBT (Trm [?cp0])) b\<^sub>0" using innerscb by simp
  have domcp0: "domB (Trm [?cp0]) = TBv (enat (v - 1))" by (rule domB_Dw0[OF vpos])
  have dfreecp0: "dfree_BP ?cp0" by simp
  have domcp0z: "domB_operB_xseq_dom (Inr (Inl (Trm [?cp0], ?xn)))"
    by (rule operB_dom_Dv0)
  have imgcp0: "operB (Trm [?cp0]) ?xn = ?xn" by (rule operB_Dv0_id[OF vpos])
  obtain rp where xnps: "?xn = Trm [rp]"
    using xseq_single_TBv[OF dbbody, of "enat (v - 1)" n] by auto
  have oprp0: "operB (Trm [?cp0]) ?xn = Trm [rp]" using imgcp0 xnps by simp
  have flatcore: "flatBT ?core = s\<^sub>0 @ flatBT ?xn @ b\<^sub>0"
  proof -
    have "flatBT ?core = s\<^sub>0 @ flatBT (operB (Trm [?cp0]) ?xn) @ b\<^sub>0"
      by (rule operB_TBv_body_spine[OF dcp0 domcp0 dfreecp0 dbbody domcp0z oprp0])
    thus ?thesis using imgcp0 by simp
  qed
  have flatxn: "flatBT ?xn
                  = concat (replicate n ([?D] @ s\<^sub>0)) @ [?D] @ [Zsym]
                    @ concat (replicate n b\<^sub>0)"
    by (rule xseq_body_tower_flat[OF vpos dbbody innerscb])
  \<comment> \<open>read-back: the prefix \<open>s\<^sub>0\<close> shifts through the tower, producing exactly
     \<open>n+1\<close> copies of \<open>(s\<^sub>0 D\<^bsub>v-1\<^esub>)\<close> and \<open>n+1\<close> copies of \<open>b\<^sub>0\<close>
     (the article's literal \<open>n+1\<close> form; the A24 \<open>n\<close>-form was an artefact of the
     mis-transcribed \<open>([].4)(ii)\<close>)\<close>
  have shift: "s\<^sub>0 @ concat (replicate n ([?D] @ s\<^sub>0))
                 = concat (replicate n (s\<^sub>0 @ [?D])) @ s\<^sub>0"
    by (rule concat_replicate_shift)
  have tailfold: "concat (replicate n b\<^sub>0) @ b\<^sub>0 = concat (replicate (n + 1) b\<^sub>0)"
  proof -
    have "replicate (n + 1) b\<^sub>0 = replicate n b\<^sub>0 @ [b\<^sub>0]"
      by (simp add: replicate_append_same)
    thus ?thesis by simp
  qed
  have headfold: "concat (replicate n (s\<^sub>0 @ [?D])) @ (s\<^sub>0 @ [?D])
                    = concat (replicate (n + 1) (s\<^sub>0 @ [?D]))"
  proof -
    have "replicate (n + 1) (s\<^sub>0 @ [?D]) = replicate n (s\<^sub>0 @ [?D]) @ [s\<^sub>0 @ [?D]]"
      by (simp add: replicate_append_same)
    thus ?thesis by simp
  qed
  have flatcore2: "flatBT ?core
                     = concat (replicate (n + 1) (s\<^sub>0 @ [?D])) @ [Zsym]
                       @ concat (replicate (n + 1) b\<^sub>0)"
  proof -
    have "flatBT ?core
            = (s\<^sub>0 @ concat (replicate n ([?D] @ s\<^sub>0)))
              @ [?D] @ [Zsym] @ (concat (replicate n b\<^sub>0) @ b\<^sub>0)"
      using flatcore flatxn by simp
    also have "\<dots> = (concat (replicate n (s\<^sub>0 @ [?D])) @ s\<^sub>0)
              @ [?D] @ [Zsym] @ concat (replicate (n + 1) b\<^sub>0)"
      using shift tailfold by simp
    also have "\<dots> = (concat (replicate n (s\<^sub>0 @ [?D])) @ (s\<^sub>0 @ [?D]))
              @ [Zsym] @ concat (replicate (n + 1) b\<^sub>0)"
      by simp
    also have "\<dots> = concat (replicate (n + 1) (s\<^sub>0 @ [?D])) @ [Zsym]
                    @ concat (replicate (n + 1) b\<^sub>0)"
      using headfold by simp
    finally show ?thesis .
  qed
  have flatRHS: "flatBT ?RHS = Dsym (enat u) # flatBT ?core" by simp
  have "flatBT (operB t (numBT n))
          = s\<^sub>1 @ (Dsym (enat u)
             # concat (replicate (n + 1) (s\<^sub>0 @ [?D]))
             @ [Zsym]
             @ concat (replicate (n + 1) b\<^sub>0)) @ b\<^sub>1"
    using flatid2 flatRHS flatcore2 by simp
  thus ?thesis using uv by simp
qed


text \<open>命題（scb分解と基本列の関係） (§7.2):
  (1-1) \<open>t'\<^sub>0 + D\<^sub>v(t'\<^sub>1 + D\<^sub>0 0)[n] = t'\<^sub>0 + (D\<^sub>v t'\<^sub>1)\<cdot>(n+1)\<close>;
  (1-2) if \<open>(s, D\<^sub>u(t'\<^sub>0 + D\<^sub>v(t'\<^sub>1+D\<^sub>0 0)), b)\<close> is an scb-decomposition of \<open>t\<close>,
        then \<open>(s, D\<^sub>u(t'\<^sub>0 + (D\<^sub>v t'\<^sub>1)\<cdot>(n+1)), b)\<close> is one of \<open>t[n]\<close>;
  (2) if \<open>(s\<^sub>1,c\<^sub>2,b\<^sub>1)\<close> is a 第\<open>1\<close>種 scb-decomposition of \<open>t\<close> and
        \<open>(D\<^sub>u s\<^sub>0, D\<^sub>v 0, b\<^sub>0)\<close> is an scb-decomposition of \<open>c\<^sub>2\<close>, then \<open>v > u\<close> and
        the \<open>\<Sigma>\<close>-string of \<open>t[n]\<close> is
        \<open>s\<^sub>1 D\<^sub>u (s\<^sub>0 D\<^bsub>v-1\<^esub>)\<^bsup>n+1\<^esup> 0 b\<^sub>0\<^bsup>n+1\<^esup> b\<^sub>1\<close>.
  Modelling: BT fundamental sequence \<open>t[n] = operB t (numB<\<close>\<open>n)\<close> (numeral term);
  string powers \<open>x\<^bsup>k\<^esup> = concat (replicate k x)\<close>.\<close>

lemma p_7_2_scb_fseq:
  fixes v n :: nat
  shows "\<And>t'\<^sub>0 t'\<^sub>1. t'\<^sub>0 \<in> T_B \<Longrightarrow> t'\<^sub>1 \<in> T_B \<Longrightarrow>
            operB (t'\<^sub>0 +\<^sub>B Dpt (enat v) (t'\<^sub>1 +\<^sub>B Dpt 0 0\<^sub>B)) (numBT n)
              = t'\<^sub>0 +\<^sub>B multBT (Dpt (enat v) t'\<^sub>1) (n + 1)"
    and "\<And>t'\<^sub>0 t'\<^sub>1 t u s b.
            t'\<^sub>0 \<in> T_B \<Longrightarrow> t'\<^sub>1 \<in> T_B \<Longrightarrow> t \<in> T_B \<Longrightarrow>
            scb_decomp t s
              (flatBT (Dpt (enat u) (t'\<^sub>0 +\<^sub>B Dpt (enat v) (t'\<^sub>1 +\<^sub>B Dpt 0 0\<^sub>B)))) b \<Longrightarrow>
            scb_decomp (operB t (numBT n)) s
              (flatBT (Dpt (enat u) (t'\<^sub>0 +\<^sub>B multBT (Dpt (enat v) t'\<^sub>1) (n + 1)))) b"
    and "\<And>t u s\<^sub>0 s\<^sub>1 c\<^sub>2 b\<^sub>0 b\<^sub>1.
            t \<in> T_B \<Longrightarrow>
            scb_kind1 t s\<^sub>1 (flatBT c\<^sub>2) b\<^sub>1 \<Longrightarrow>
            scb_decomp c\<^sub>2 (Dsym (enat u) # s\<^sub>0) (flatBT (Dpt (enat v) 0\<^sub>B)) b\<^sub>0 \<Longrightarrow>
            v > u \<and>
            flatBT (operB t (numBT n)) =
              s\<^sub>1 @ (Dsym (enat u)
                # concat (replicate (n + 1) (s\<^sub>0 @ [Dsym (enat (v - 1))]))
                @ [Zsym]
                @ concat (replicate (n + 1) b\<^sub>0))
              @ b\<^sub>1"
  apply (rule m_7_2_scb_fseq_succ)
  apply assumption+
  apply (rule m_7_2_scb_fseq_scb)
  apply assumption+
proof -
  fix t u s\<^sub>0 s\<^sub>1 c\<^sub>2 b\<^sub>0 b\<^sub>1
  assume tT: "t \<in> T_B"
     and k1: "scb_kind1 t s\<^sub>1 (flatBT c\<^sub>2) b\<^sub>1"
     and inner: "scb_decomp c\<^sub>2 (Dsym (enat u) # s\<^sub>0)
                   (flatBT (Dpt (enat v) 0\<^sub>B)) b\<^sub>0"
  have ptc2: "isPTB_str (flatBT c\<^sub>2)"
    using k1 by (simp add: scb_kind1_def)
  obtain p where pdf: "dfree_BP p" and c2flat: "flatBT c\<^sub>2 = flatBP p"
    using ptc2 unfolding isPTB_str_def by blast
  have c2p: "c\<^sub>2 = Trm [p]"
    by (rule m_7_flatBT_inj) (use c2flat in simp)
  obtain w body where pDB: "p = DB w body" by (cases p)
  have innerflat:
    "flatBT c\<^sub>2 = (Dsym (enat u) # s\<^sub>0)
       @ flatBT (Dpt (enat v) 0\<^sub>B) @ b\<^sub>0"
    using inner by (simp add: scb_decomp_def)
  have wu: "w = enat u" using innerflat c2p pDB by simp
  have c2form: "c\<^sub>2 = Dpt (enat u) body" using c2p pDB wu by simp
  have bodyflat:
    "flatBT body = s\<^sub>0 @ flatBT (Dpt (enat v) 0\<^sub>B) @ b\<^sub>0"
    using innerflat c2form by simp
  have bodyT: "body \<in> T_B" using pdf pDB by (simp add: T_B_def)
  have bodyne: "body \<noteq> Trm []"
  proof
    assume z: "body = Trm []"
    have "length (flatBT (Dpt (enat v) 0\<^sub>B)) \<le> length (flatBT body)"
      using bodyflat by simp
    thus False using z by simp
  qed
  have bRP: "\<forall>x \<in> set b\<^sub>0. x = RP"
    using inner by (simp add: scb_decomp_def)
  have innerbody:
    "scb_decomp body s\<^sub>0 (flatBT (Dpt (enat v) 0\<^sub>B)) b\<^sub>0"
  proof -
    have pt: "isPTB_str (flatBT (Dpt (enat v) 0\<^sub>B))"
      by (rule isPTB_str_Dpt) simp_all
    show ?thesis
      unfolding scb_decomp_def using bodyflat bodyne bRP pt by simp
  qed
  have bodyflat':
    "flatBT body = s\<^sub>0 @ Dsym (enat v) # Zsym # b\<^sub>0"
    using bodyflat by simp
  obtain a where RNbody: "RightNodes body = a @ [v]"
    using rnsub_RightNodes_t0_lastv[OF bodyflat' bRP bodyT] by blast
  have kc:
    "let r = RightNodes (Trm [p]); j1 = Lng r - 1 in
       j1 \<ge> 1 \<and> r ! 0 < r ! j1
       \<and> (\<forall>j. 0 < j \<and> j < j1 \<longrightarrow> r ! j \<ge> r ! j1)"
    using k1 c2flat by (simp add: scb_kind1_def)
  have uv: "u < v" using kc pDB wu RNbody by (simp add: Let_def)
  have amid: "\<forall>k < length a. a ! k \<ge> v"
  proof (intro allI impI)
    fix k
    assume klt: "k < length a"
    have jrange:
      "0 < Suc k \<and> Suc k < Lng (RightNodes (Trm [p])) - 1"
      using klt pDB wu RNbody by simp
    have "RightNodes (Trm [p]) ! Suc k
            \<ge> RightNodes (Trm [p]) ! (Lng (RightNodes (Trm [p])) - 1)"
      using kc jrange by (simp add: Let_def)
    thus "a ! k \<ge> v" using pDB wu RNbody klt by (simp add: nth_append)
  qed
  have notshape: "\<not> rnNatShape (RightNodes body)"
  proof
    assume shape: "rnNatShape (RightNodes body)"
    have "v = 0 \<or> (\<exists>k < length a. a ! k < v)"
      using shape RNbody unfolding rnNatShape_def
      by (auto simp: nth_append)
    then show False
    proof
      assume "v = 0"
      thus False using uv by simp
    next
      assume "\<exists>k < length a. a ! k < v"
      then obtain k where klt: "k < length a" and kval: "a ! k < v" by blast
      have "a ! k \<ge> v" using amid klt by simp
      thus False using kval by simp
    qed
  qed
  have dbbody: "domB body = TBv (enat (v - 1))"
    using domB_classify_RN[OF bodyT bodyne] notshape uv RNbody by simp
  have k1body:
    "scb_kind1 t s\<^sub>1 (flatBT (Dpt (enat u) body)) b\<^sub>1"
    using k1 c2form by simp
  show "v > u \<and>
        flatBT (operB t (numBT n)) =
          s\<^sub>1 @ (Dsym (enat u)
            # concat (replicate (n + 1) (s\<^sub>0 @ [Dsym (enat (v - 1))]))
            @ [Zsym]
            @ concat (replicate (n + 1) b\<^sub>0))
          @ b\<^sub>1"
    by (rule m_7_2_scb_fseq_kind1_general
        [OF tT uv bodyT dbbody bodyne innerbody k1body])
qed

end
