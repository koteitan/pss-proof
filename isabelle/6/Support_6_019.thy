theory Support_6_019
  imports Frontier_6_036
begin

text \<open>§6.8 (c): the LOW component-list identity (d0pos, \<open>i\<^sub>1=1\<close>).  Combining
  (a) @{thm [source] oper_d1pos_LOW_source_eq} (the in-block slice of \<open>M[n]\<close> is the
  \<open>(IncrFirst^^(q\<cdot>\<delta>))\<close>-shift of the base slice of \<open>M\<close>) with (b)
  @{thm [source] P_funpow_IncrFirst} (\<open>P\<close> commutes with iterated \<open>IncrFirst\<close> as a
  per-component map): the \<open>P\<close>-decomposition of the LOW source slice of \<open>M[n]\<close> is the
  \<open>map (IncrFirst^^(q\<cdot>\<delta>))\<close> of the base \<open>P\<close>-decomposition.  In the §6.8 assembly the
  base is \<open>N\<close>, \<open>P (seg N (j\<^sub>0+s\<^sub>0) (j\<^sub>0+e\<^sub>0))\<close> is the N-side branch prefix
  \<open>take J\<^sub>1 (Br N')\<close>, and the LHS \<open>P (seg (N[n]) lo hi)\<close> is the LOW component list
  \<open>P (seg Y\<^sub>p 0 (c-1))\<close>; descending then follows from
  @{thm [source] descending_map_IncrFirst} on the N-side @{thm [source] descending_take}.\<close>

lemma oper_d1pos_notbrle_LOW_eq:
  fixes M :: pairseq
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 1"
    and j0lt: "parent M 1 (Lng M - 1) < Lng M - 1"
    and q: "q < n"
    and s0e0: "s0 \<le> e0"
    and e0lt: "e0 < Lng M - 1 - parent M 1 (Lng M - 1)"
  shows "P (seg (M[n])
              (parent M 1 (Lng M - 1) + q * (Lng M - 1 - parent M 1 (Lng M - 1)) + s0)
              (parent M 1 (Lng M - 1) + q * (Lng M - 1 - parent M 1 (Lng M - 1)) + e0))
       = map (IncrFirst ^^ (q * (entry M 0 (Lng M - 1) - entry M 0 (parent M 1 (Lng M - 1)))))
             (P (seg M (parent M 1 (Lng M - 1) + s0) (parent M 1 (Lng M - 1) + e0)))"
proof -
  let ?sh = "q * (entry M 0 (Lng M - 1) - entry M 0 (parent M 1 (Lng M - 1)))"
  let ?base = "seg M (parent M 1 (Lng M - 1) + s0) (parent M 1 (Lng M - 1) + e0)"
  have aeq: "seg (M[n])
              (parent M 1 (Lng M - 1) + q * (Lng M - 1 - parent M 1 (Lng M - 1)) + s0)
              (parent M 1 (Lng M - 1) + q * (Lng M - 1 - parent M 1 (Lng M - 1)) + e0)
            = (IncrFirst ^^ ?sh) ?base"
    by (rule oper_d1pos_LOW_source_eq[OF L notzero hp i1z j0lt q s0e0 e0lt])
  have "P (seg (M[n])
              (parent M 1 (Lng M - 1) + q * (Lng M - 1 - parent M 1 (Lng M - 1)) + s0)
              (parent M 1 (Lng M - 1) + q * (Lng M - 1 - parent M 1 (Lng M - 1)) + e0))
        = P ((IncrFirst ^^ ?sh) ?base)"
    using aeq by simp
  also have "\<dots> = map (IncrFirst ^^ ?sh) (P ?base)"
    by (rule P_funpow_IncrFirst)
  finally show ?thesis .
qed

end
