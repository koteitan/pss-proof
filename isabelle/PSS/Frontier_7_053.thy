theory Frontier_7_053
  imports Support_7_048
begin

text \<open>\<open>operB (D\<^sub>u(D\<^sub>v 0)) (numBT n) = D\<^sub>u ((D\<^bsub>v-1\<^esub>)\<^bsup>n+1\<^esup> 0)\<close> for \<open>u < v\<close>:
  the kind-1 unfold @{thm [source] operB_kind1_unfold} then the tower
  @{thm [source] xseq_Dv0_tower} (with \<open>numNat (numBT n) = n\<close>).\<close>

lemma operB_Du_Dv0_kind1_eval:
  assumes uv: "u < v"
  shows "operB (Dpt (enat u) (Dpt (enat v) 0\<^sub>B)) (numBT n)
           = Dpt (enat u) (((\<lambda>a. Dpt (enat (v - 1)) a) ^^ (n + 1)) 0\<^sub>B)"
proof -
  have vpos: "0 < v" using uv by simp
  have db: "domB (Dpt (enat v) 0\<^sub>B) = TBv (enat (v - 1))" by (rule domB_Dw0[OF vpos])
  have vu: "enat u \<le> enat (v - 1)" using uv by simp
  have bne: "Dpt (enat v) 0\<^sub>B \<noteq> Trm []" by simp
  have "operB (Trm [DB (enat u) (Dpt (enat v) 0\<^sub>B)]) (numBT n)
          = Dprin (enat u)
              (operB (Dpt (enat v) 0\<^sub>B)
                (xseq (Dpt (enat v) 0\<^sub>B) (enat (v - 1)) (numNat (numBT n))))"
    by (rule operB_kind1_unfold[OF db vu bne])
  also have "\<dots> = Dprin (enat u)
              (operB (Dpt (enat v) 0\<^sub>B) (xseq (Dpt (enat v) 0\<^sub>B) (enat (v - 1)) n))"
    by (simp add: numNat_numBT)
  also have "\<dots> = Dprin (enat u) (xseq (Dpt (enat v) 0\<^sub>B) (enat (v - 1)) n)"
    using operB_Dv0_id[OF vpos] by simp
  also have "\<dots> = Dprin (enat u) (((\<lambda>a. Dpt (enat (v - 1)) a) ^^ (n + 1)) 0\<^sub>B)"
    using xseq_Dv0_tower[OF vpos] by simp
  finally show ?thesis .
qed

end
