theory Support_7_044
  imports Frontier_7_050
begin

text \<open>命題（scb分解と基本列の関係） (§7.2), conjunct (1-2).\<close>

lemma m_7_2_scb_fseq_scb:
  fixes u v n :: nat
  assumes t0: "t\<^sub>0 \<in> T_B" and t1: "t\<^sub>1 \<in> T_B" and tT: "t \<in> T_B"
    and d: "scb_decomp t s
              (flatBT (Dpt (enat u) (t\<^sub>0 +\<^sub>B Dpt (enat v) (t\<^sub>1 +\<^sub>B Dpt 0 0\<^sub>B)))) b"
  shows "scb_decomp (operB t (numBT n)) s
           (flatBT (Dpt (enat u) (t\<^sub>0 +\<^sub>B multBT (Dpt (enat v) t\<^sub>1) (n + 1)))) b"
proof -
  let ?BODY = "t\<^sub>0 +\<^sub>B Dpt (enat v) (t\<^sub>1 +\<^sub>B Dpt 0 0\<^sub>B)"
  let ?cp = "DB (enat u) ?BODY"
  let ?RHS = "Dpt (enat u) (t\<^sub>0 +\<^sub>B multBT (Dpt (enat v) t\<^sub>1) (n + 1))"
  have dcp: "scb_decomp t s (flatBT (Trm [?cp])) b" using d by simp
  have domcp: "domB (Trm [?cp]) = NatSet"
    by (rule domB_principal_NatSet[OF domB_succ_body_NatSet succ_body_ne])
  have df0: "dfree_BT t\<^sub>0" using t0 by (simp add: T_B_def)
  have df1: "dfree_BT t\<^sub>1" using t1 by (simp add: T_B_def)
  have dfBody: "dfree_BT ?BODY"
  proof -
    obtain xs where x0: "t\<^sub>0 = Trm xs" by (cases t\<^sub>0)
    have "dfree_BT (Trm (xs @ [DB (enat v) (t\<^sub>1 +\<^sub>B Dpt 0 0\<^sub>B)]))"
      using df0 df1 x0 by (cases t\<^sub>1) (auto simp: zero_enat_def)
    thus ?thesis using x0 by simp
  qed
  have dfreecp: "dfree_BP ?cp" using dfBody by simp
  have bne: "?BODY \<noteq> Trm []" by (rule succ_body_ne)
  have ds_body: "d0succ ?BODY" by (rule d0succ_succ_body)
  have domb: "domB_operB_xseq_dom (Inr (Inl (?BODY, numBT n)))"
    by (rule operB_dom_d0succ[OF ds_body])
  have domcpz: "domB_operB_xseq_dom (Inr (Inl (Trm [?cp], numBT n)))"
    by (rule operB_dom_NatSet_principal[OF domB_succ_body_NatSet bne domb])
  have opercp: "operB (Trm [?cp]) (numBT n) = ?RHS"
    using m_7_2_scb_fseq_inner[OF t0 t1] by simp
  have oprp: "operB (Trm [?cp]) (numBT n) = Trm [DB (enat u) (t\<^sub>0 +\<^sub>B multBT (Dpt (enat v) t\<^sub>1) (n + 1))]"
    using opercp by simp
  have flatid: "flatBT (operB t (numBT n)) = s @ flatBT (operB (Trm [?cp]) (numBT n)) @ b"
    by (rule operB_scb_spine[OF dcp domcp dfreecp domcpz oprp])
  have flatid2: "flatBT (operB t (numBT n)) = s @ flatBT ?RHS @ b"
    using flatid opercp by simp
  have dfDv1: "dfree_BT (Dpt (enat v) t\<^sub>1)" using df1 by simp
  have dfRHSbody: "dfree_BT (t\<^sub>0 +\<^sub>B multBT (Dpt (enat v) t\<^sub>1) (n + 1))"
    using df0 dfDv1 by (simp add: dfree_BT_addBT dfree_BT_multBT)
  have iptRHS: "isPTB_str (flatBT ?RHS)"
    by (rule isPTB_str_Dpt[OF _ dfRHSbody]) simp
  have rbS: "\<forall>x \<in> set b. x = RP" using d by (simp add: scb_decomp_def)
  show ?thesis
    unfolding scb_decomp_def using flatid2 iptRHS rbS by simp
qed

end
