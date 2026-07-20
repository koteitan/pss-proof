theory Support_7_042
  imports Frontier_7_048
begin

text \<open>命題（scb分解と基本列の関係） (§7.2), conjunct (1) (article (1-1)):
  \<open>t'\<^sub>0 + D\<^sub>v(t'\<^sub>1 + D\<^sub>0 0)[n] = t'\<^sub>0 + (D\<^sub>v t'\<^sub>1)\<cdot>(n+1)\<close>.\<close>

lemma m_7_2_scb_fseq_succ:
  fixes v n :: nat
  assumes "t\<^sub>0 \<in> T_B" "t\<^sub>1 \<in> T_B"
  shows "operB (t\<^sub>0 +\<^sub>B Dpt (enat v) (t\<^sub>1 +\<^sub>B Dpt 0 0\<^sub>B)) (numBT n)
           = t\<^sub>0 +\<^sub>B multBT (Dpt (enat v) t\<^sub>1) (n + 1)"
proof -
  let ?inner = "t\<^sub>1 +\<^sub>B Dpt 0 0\<^sub>B"
  let ?single = "Dpt (enat v) ?inner"
  obtain xs where x0: "t\<^sub>0 = Trm xs" by (cases t\<^sub>0)
  \<comment> \<open>single-principal value\<close>
  have sv: "operB ?single (numBT n) = multBT (Dpt (enat v) t\<^sub>1) (numNat (numBT n) + 1)"
    by (rule operB_single_succ)
  have svn: "operB ?single (numBT n) = multBT (Dpt (enat v) t\<^sub>1) (n + 1)"
    using sv by (simp add: numNat_numBT)
  show ?thesis
  proof (cases xs)
    case Nil
    \<comment> \<open>\<open>t\<^sub>0 = 0\<close>: outer term IS the single principal\<close>
    have t0z: "t\<^sub>0 = Trm []" using x0 Nil by simp
    have outer: "t\<^sub>0 +\<^sub>B ?single = ?single" using t0z by (cases ?single) simp
    have rhs: "t\<^sub>0 +\<^sub>B multBT (Dpt (enat v) t\<^sub>1) (n + 1)
                 = multBT (Dpt (enat v) t\<^sub>1) (n + 1)"
      using t0z by (cases "multBT (Dpt (enat v) t\<^sub>1) (n + 1)") simp
    show ?thesis using outer svn rhs by simp
  next
    case (Cons p ps)
    \<comment> \<open>\<open>t\<^sub>0\<close> nonempty: outer term is multi \<open>Trm (p # q # rest)\<close>, operB peels off \<open>t\<^sub>0\<close>\<close>
    let ?outer = "t\<^sub>0 +\<^sub>B ?single"
    obtain q rest where qr: "ps @ [DB (enat v) ?inner] = q # rest"
      by (cases "ps @ [DB (enat v) ?inner]") auto
    have oeq: "?outer = Trm (p # q # rest)" using x0 Cons qr by simp
    \<comment> \<open>the last component \<open>D\<^sub>v ?inner\<close> is itself \<open>d0succ\<close>, so \<open>?outer\<close> is \<open>d0succ\<close>\<close>
    have pqr0: "p # q # rest = p # ps @ [DB (enat v) ?inner]" using qr by simp
    have ds_last: "d0succ (Trm [last (p # q # rest)])"
    proof -
      have l: "last (p # q # rest) = DB (enat v) ?inner" using pqr0 by simp
      have bne: "?inner \<noteq> Trm []" by (cases t\<^sub>1) simp
      have ends: "endsD00 ?inner" by (rule endsD00_addD00)
      have ds_b: "d0succ ?inner" by (rule d0succ_addD00)
      have "d0succ (Dpt (enat v) ?inner)"
        by (rule d0succ_single_nonzero[OF bne ends ds_b])
      thus ?thesis using l by simp
    qed
    have ds': "d0succ (Trm (p # q # rest))"
      using ds_last by (simp add: d0succ_def)
    have peel: "operB ?outer (numBT n)
                  = addBT (Trm (butlast (p # q # rest)))
                          (operB (Trm [last (p # q # rest)]) (numBT n))"
      using operB_d0succ_multi_peel[OF ds'] oeq by simp
    have pqr: "p # q # rest = p # ps @ [DB (enat v) ?inner]" using qr by simp
    have lst: "last (p # q # rest) = DB (enat v) ?inner" using pqr by simp
    have but: "butlast (p # q # rest) = p # ps" using pqr by (simp add: butlast_append)
    have "operB ?outer (numBT n)
            = addBT (Trm (p # ps)) (operB (Dpt (enat v) ?inner) (numBT n))"
      using peel lst but by simp
    also have "\<dots> = addBT (Trm (p # ps)) (multBT (Dpt (enat v) t\<^sub>1) (n + 1))"
      using svn by simp
    also have "\<dots> = t\<^sub>0 +\<^sub>B multBT (Dpt (enat v) t\<^sub>1) (n + 1)"
      using x0 Cons by (cases "multBT (Dpt (enat v) t\<^sub>1) (n + 1)") simp
    finally show ?thesis .
  qed
qed

end
