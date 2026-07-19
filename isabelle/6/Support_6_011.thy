theory Support_6_011
  imports Frontier_6_028
begin

text \<open>\<open>descending\<close> is invariant under a uniform row-0 shift \<open>IncrFirst\<close> applied
  componentwise (\<open>map IncrFirst\<close>): each component head's row-0 entry is bumped by
  the SAME \<open>+1\<close> and the row-1 head is unchanged, so every \<open>cdom\<close> step (a row-0
  comparison with a row-1 tie-break) is preserved.  Requires each component to be
  nonempty so \<open>entry .. 0 0\<close> actually reads the shifted head.  This is the
  closing brick for the \<open>i\<^sub>1 = 1\<close> (d1pos) branch prefix, whose \<open>P\<close>-components are
  \<open>q\<cdot>\<delta>\<close>-shifted copies of the \<open>N\<close>-side branch components.\<close>

lemma descending_map_IncrFirst:
  assumes dQ: "descending Q"
    and ne: "\<And>J. J < Lng Q \<Longrightarrow> 0 < Lng (Q ! J)"
  shows "descending (map IncrFirst Q)"
proof (rule descendingI_cdom)
  fix J0 J1 assume le: "J0 \<le> J1" and j1: "J1 < Lng (map IncrFirst Q)"
  have lenEq: "Lng (map IncrFirst Q) = Lng Q" by simp
  have j1Q: "J1 < Lng Q" using j1 lenEq by simp
  have j0Q: "J0 < Lng Q" using le j1Q by linarith
  have m0: "map IncrFirst Q ! J0 = IncrFirst (Q ! J0)" using j0Q by simp
  have m1: "map IncrFirst Q ! J1 = IncrFirst (Q ! J1)" using j1Q by simp
  have e00: "entry (IncrFirst (Q ! J0)) 0 0 = Suc (entry (Q ! J0) 0 0)"
    using entry_IncrFirst[of 0 "Q ! J0" 0] ne[OF j0Q] by simp
  have e10: "entry (IncrFirst (Q ! J0)) 1 0 = entry (Q ! J0) 1 0"
    using entry_IncrFirst[of 0 "Q ! J0" 1] ne[OF j0Q] by simp
  have e01: "entry (IncrFirst (Q ! J1)) 0 0 = Suc (entry (Q ! J1) 0 0)"
    using entry_IncrFirst[of 0 "Q ! J1" 0] ne[OF j1Q] by simp
  have e11: "entry (IncrFirst (Q ! J1)) 1 0 = entry (Q ! J1) 1 0"
    using entry_IncrFirst[of 0 "Q ! J1" 1] ne[OF j1Q] by simp
  \<comment> \<open>the underlying \<open>cdom\<close> step on \<open>Q\<close>\<close>
  have base: "cdom (Q ! J0) (Q ! J1)" using descending_cdomD[OF dQ le j1Q] .
  have b0: "entry (Q ! J1) 0 0 \<le> entry (Q ! J0) 0 0"
    using base unfolding cdom_def by simp
  have b1: "entry (Q ! J0) 0 0 = entry (Q ! J1) 0 0
            \<longrightarrow> entry (Q ! J1) 1 0 \<le> entry (Q ! J0) 1 0"
    using base unfolding cdom_def by simp
  show "cdom (map IncrFirst Q ! J0) (map IncrFirst Q ! J1)"
    unfolding cdom_def m0 m1
  proof (intro conjI impI)
    \<comment> \<open>row-0: the shift is uniform, so \<open>\<le>\<close> is preserved\<close>
    show "entry (IncrFirst (Q ! J1)) 0 0 \<le> entry (IncrFirst (Q ! J0)) 0 0"
      using b0 e00 e01 by simp
  next
    assume "entry (IncrFirst (Q ! J0)) 0 0 = entry (IncrFirst (Q ! J1)) 0 0"
    hence "entry (Q ! J0) 0 0 = entry (Q ! J1) 0 0" using e00 e01 by simp
    hence "entry (Q ! J1) 1 0 \<le> entry (Q ! J0) 1 0" using b1 by simp
    thus "entry (IncrFirst (Q ! J1)) 1 0 \<le> entry (IncrFirst (Q ! J0)) 1 0"
      using e10 e11 by simp
  qed
qed

end
