theory Support_6_015
  imports Frontier_6_032
begin

text \<open>Period reduction (article 1472, \<open>WLOG q = n-1\<close>): a slice of \<open>M[n]\<close> ending in
  block \<open>q\<close> agrees with the same slice of \<open>M[q+1]\<close>, since the first \<open>q+1\<close> blocks
  are identical.\<close>

lemma oper_d0zero_seg_period_reduce:
  assumes L: "1 < Lng M"
    and notzero: "\<not> (entry M 0 (Lng M - 1) = 0 \<and> entry M 1 (Lng M - 1) = 0)"
    and hp: "hasParent M (idx1 M (Lng M - 1)) (Lng M - 1)"
    and i1z: "idx1 M (Lng M - 1) = 0"
    and qn1: "q + 1 \<le> n"
    and ble: "b < parent M 0 (Lng M - 1) + (q + 1) * (Lng M - 1 - parent M 0 (Lng M - 1))"
  shows "seg ((M::pairseq)[n]) a b = seg ((M::pairseq)[q + 1]) a b"
proof (rule nth_equalityI)
  show "length (seg ((M::pairseq)[n]) a b) = length (seg ((M::pairseq)[q + 1]) a b)" by simp
next
  let ?j0 = "parent M 0 (Lng M - 1)"  let ?w = "Lng M - 1 - ?j0"
  have hp0: "hasParent M 0 (Lng M - 1)" using hp i1z by simp
  have parR: "nextR M 0 ?j0 (Lng M - 1)"
    using hp0 unfolding hasParent_def parent_def by (rule theI')
  have j0lt: "?j0 < Lng M - 1" using poper_nextR_imp_le0[OF parR] by simp
  have w0: "0 < ?w" using j0lt by linarith
  fix i assume "i < length (seg ((M::pairseq)[n]) a b)"
  hence ic: "i < Suc b - a" by simp
  have agree: "((M::pairseq)[n]) ! (a + i) = ((M::pairseq)[q + 1]) ! (a + i)"
  proof (cases "a + i < ?j0")
    case True
    show ?thesis
      using oper_d0zero_nth_prefix[OF L notzero hp i1z True, of n]
            oper_d0zero_nth_prefix[OF L notzero hp i1z True, of "q + 1"] by simp
  next
    case False
    hence ge: "?j0 \<le> a + i" by simp
    let ?qx = "(a + i - ?j0) div ?w"  let ?sx = "(a + i - ?j0) mod ?w"
    have aible: "a + i < ?j0 + (q + 1) * ?w" using ic ble by linarith
    have sx: "?sx < ?w" using w0 by simp
    have xmj: "a + i - ?j0 < (q + 1) * ?w" using aible ge by linarith
    have qxq: "?qx < q + 1" using less_mult_imp_div_less[OF xmj] .
    have qxn: "?qx < n" using qxq qn1 by linarith
    have splitmod: "?qx * ?w + ?sx = a + i - ?j0"
      using div_mult_mod_eq[of "a + i - ?j0" ?w] by (simp add: mult.commute)
    have split: "a + i = ?j0 + ?qx * ?w + ?sx" using splitmod ge by linarith
    have "((M::pairseq)[n]) ! (a + i) = M ! (?j0 + ?sx)"
      using split oper_d0zero_nth[OF L notzero hp i1z j0lt qxn sx] by simp
    moreover have "((M::pairseq)[q + 1]) ! (a + i) = M ! (?j0 + ?sx)"
      using split oper_d0zero_nth[OF L notzero hp i1z j0lt qxq sx] by simp
    ultimately show ?thesis by simp
  qed
  have "seg ((M::pairseq)[n]) a b ! i = ((M::pairseq)[n]) ! (a + i)"
    using ic by (rule seg_nth_eq)
  also have "\<dots> = ((M::pairseq)[q + 1]) ! (a + i)" by (rule agree)
  also have "\<dots> = seg ((M::pairseq)[q + 1]) a b ! i" using ic by (simp add: seg_nth_eq)
  finally show "seg ((M::pairseq)[n]) a b ! i = seg ((M::pairseq)[q + 1]) a b ! i" .
qed

end
