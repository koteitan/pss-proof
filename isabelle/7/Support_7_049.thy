theory Support_7_049
  imports Frontier_7_053
begin

text \<open>\<open>flat ((D\<^sub>m)\<^bsup>k\<^esup> 0) = (D\<^sub>m)\<^bsup>k\<^esup> \<frown> 0\<close> as a \<open>\<Sigma>\<close>-string:
  \<open>concat (replicate k [D\<^sub>m]) \<frown> [Z]\<close>.\<close>

lemma flatBT_Dprin_funpow_tower:
  "flatBT (((\<lambda>a. Dpt m a) ^^ k) 0\<^sub>B) = concat (replicate k [Dsym m]) @ [Zsym]"
proof (induction k)
  case 0
  show ?case by simp
next
  case (Suc k)
  have "flatBT (((\<lambda>a. Dpt m a) ^^ (Suc k)) 0\<^sub>B)
          = flatBT (Dpt m (((\<lambda>a. Dpt m a) ^^ k) 0\<^sub>B))"
    by simp
  also have "\<dots> = Dsym m # flatBT (((\<lambda>a. Dpt m a) ^^ k) 0\<^sub>B)"
    by simp
  also have "\<dots> = Dsym m # (concat (replicate k [Dsym m]) @ [Zsym])"
    using Suc.IH by simp
  also have "\<dots> = concat (replicate (Suc k) [Dsym m]) @ [Zsym]"
    by simp
  finally show ?case .
qed

text \<open>\<open>v > u\<close> half of conjunct (2): the marked \<open>D\<^sub>v 0\<close> of \<open>c\<^sub>2\<close> is the leaf at
  the bottom of \<open>c\<^sub>2\<close>'s rightmost spine, so \<open>v = RightNodes(c\<^sub>2)\<^bsub>j\<^sub>1\<^esub>\<close> and
  \<open>u = RightNodes(c\<^sub>2)\<^bsub>0\<^esub>\<close>; the kind-1 condition gives \<open>RightNodes(c\<^sub>2)\<^bsub>0\<^esub> <
  RightNodes(c\<^sub>2)\<^bsub>j\<^sub>1\<^esub>\<close>.  Here we prove it for the basic \<open>c\<^sub>2 = D\<^sub>u(D\<^sub>v 0)\<close>.\<close>

text \<open>命題（scb分解と基本列の関係） (§7.2), conjunct (2), basic case
  \<open>c\<^sub>2 = D\<^sub>u(D\<^sub>v 0)\<close> (\<open>s\<^sub>0 = b\<^sub>0 = ()\<close>).  See the section header for the
  faithfulness note: A24 is retracted, the general RHS is article-faithful, and this
  basic regime is the one the downstream 零化 lemmas need.\<close>

lemma m_7_2_scb_fseq_kind1_basic:
  fixes u v n :: nat
  assumes tT: "t \<in> T_B"
    and uv: "u < v"
    and k1: "scb_kind1 t s\<^sub>1 (flatBT (Dpt (enat u) (Dpt (enat v) 0\<^sub>B))) b\<^sub>1"
  shows "v > u \<and>
         flatBT (operB t (numBT n)) =
           s\<^sub>1 @ (Dsym (enat u)
             # concat (replicate (n + 1) [Dsym (enat (v - 1))])
             @ [Zsym]
             @ concat (replicate (n + 1) []))
           @ b\<^sub>1"
proof -
  let ?cp = "DB (enat u) (Dpt (enat v) 0\<^sub>B)"
  let ?tower = "((\<lambda>a. Dpt (enat (v - 1)) a) ^^ (n + 1)) 0\<^sub>B"
  let ?RHS = "Dpt (enat u) ?tower"
  \<comment> \<open>scb-decomp of \<open>t\<close> with marked principal \<open>?cp\<close>\<close>
  have dcp: "scb_decomp t s\<^sub>1 (flatBT (Trm [?cp])) b\<^sub>1"
    using k1 by (simp add: scb_kind1_def)
  \<comment> \<open>NatSet + dfree + operB-domain + value of the marked principal\<close>
  have domcp: "domB (Trm [?cp]) = NatSet"
    by (rule domB_Du_Dv0_NatSet[OF uv])
  have dfreecp: "dfree_BP ?cp" by simp
  have vpos: "0 < v" using uv by simp
  have db: "domB (Dpt (enat v) 0\<^sub>B) = TBv (enat (v - 1))" by (rule domB_Dw0[OF vpos])
  have vu: "enat u \<le> enat (v - 1)" using uv by simp
  have bne: "Dpt (enat v) 0\<^sub>B \<noteq> Trm []" by simp
  have domcpz: "domB_operB_xseq_dom (Inr (Inl (Trm [?cp], numBT n)))"
    by (rule operB_dom_kind1[OF db vu bne])
  have opercp: "operB (Trm [?cp]) (numBT n) = ?RHS"
    by (rule operB_Du_Dv0_kind1_eval[OF uv])
  have oprp: "operB (Trm [?cp]) (numBT n) = Trm [DB (enat u) ?tower]"
    using opercp by simp
  \<comment> \<open>spine transport: read \<open>flat (operB t (numBT n))\<close> off the marked principal\<close>
  have flatid: "flatBT (operB t (numBT n)) = s\<^sub>1 @ flatBT (operB (Trm [?cp]) (numBT n)) @ b\<^sub>1"
    by (rule operB_scb_spine[OF dcp domcp dfreecp domcpz oprp])
  have flatid2: "flatBT (operB t (numBT n)) = s\<^sub>1 @ flatBT ?RHS @ b\<^sub>1"
    using flatid opercp by simp
  \<comment> \<open>read-back of \<open>flat ?RHS = D\<^sub>u (D\<^bsub>v-1\<^esub>)\<^bsup>n+1\<^esup> 0\<close>\<close>
  have flatRHS: "flatBT ?RHS
                   = Dsym (enat u) # concat (replicate (n + 1) [Dsym (enat (v - 1))]) @ [Zsym]"
  proof -
    have "flatBT ?RHS = Dsym (enat u) # flatBT ?tower" by simp
    also have "\<dots> = Dsym (enat u) # (concat (replicate (n + 1) [Dsym (enat (v - 1))]) @ [Zsym])"
      using flatBT_Dprin_funpow_tower[where m = "enat (v - 1)" and k = "n + 1"] by simp
    finally show ?thesis by simp
  qed
  have "flatBT (operB t (numBT n))
          = s\<^sub>1 @ (Dsym (enat u) # concat (replicate (n + 1) [Dsym (enat (v - 1))]) @ [Zsym]) @ b\<^sub>1"
    using flatid2 flatRHS by simp
  thus ?thesis using uv by simp
qed

end
