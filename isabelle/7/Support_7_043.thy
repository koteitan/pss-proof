theory Support_7_043
  imports Frontier_7_049
begin

text \<open>\<open>operB\<close> on the marked principal \<open>c\<^sub>0 = D\<^sub>u BODY\<close>: \<open>BODY\<close> is \<open>d0succ\<close>
  (\<open>operB BODY z\<close> defined) with \<open>domB BODY = NatSet\<close>; the \<open>D\<^sub>u\<close>-step is the \<open>else\<close>
  branch \<open>D\<^sub>u(operB BODY z)\<close>; conjunct (1) evaluates \<open>operB BODY (numBT n)\<close>.\<close>

lemma m_7_2_scb_fseq_inner:
  fixes u v n :: nat
  assumes "t\<^sub>0 \<in> T_B" "t\<^sub>1 \<in> T_B"
  shows "operB (Dpt (enat u) (t\<^sub>0 +\<^sub>B Dpt (enat v) (t\<^sub>1 +\<^sub>B Dpt 0 0\<^sub>B))) (numBT n)
           = Dpt (enat u) (t\<^sub>0 +\<^sub>B multBT (Dpt (enat v) t\<^sub>1) (n + 1))"
proof -
  let ?BODY = "t\<^sub>0 +\<^sub>B Dpt (enat v) (t\<^sub>1 +\<^sub>B Dpt 0 0\<^sub>B)"
  have bne: "?BODY \<noteq> Trm []" by (rule succ_body_ne)
  have db: "domB ?BODY = NatSet" by (rule domB_succ_body_NatSet)
  have ds_body: "d0succ ?BODY" by (rule d0succ_succ_body)
  have domb: "domB_operB_xseq_dom (Inr (Inl (?BODY, numBT n)))"
    by (rule operB_dom_d0succ[OF ds_body])
  have "operB (Dpt (enat u) ?BODY) (numBT n) = Dprin (enat u) (operB ?BODY (numBT n))"
    by (rule operB_NatSet_principal_unfold[OF db bne domb])
  also have "operB ?BODY (numBT n) = t\<^sub>0 +\<^sub>B multBT (Dpt (enat v) t\<^sub>1) (n + 1)"
    by (rule m_7_2_scb_fseq_succ[OF assms])
  finally show ?thesis by simp
qed

end
