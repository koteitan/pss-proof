theory Support_6_048
  imports Frontier_6_068
begin

text \<open>\<S>6.6 KEYSTONE BACKWARD, INVERSE-SHIFT INFRASTRUCTURE (Front B, tag
  pss-bwdcore-invshift).  The single residual of the backward monoT-core keystone
  is the per-branch obligation \<open>(IncrFirst ^^ e\<^sub>J) (Red (N\<^sub>J M J)) = Br M ! J\<close>.
  Since (GREEN) \<open>Br M!J = N\<^sub>J M J\<close> (@{thm [source] kst_bwdcore_NJ_eq_Br}) and
  \<open>e\<^sub>J = Joints M!J + 1 - npJ M J = entry (N\<^sub>J M J) 0 0 - entry (N\<^sub>J M J) 1 0\<close>
  (the head row0/row1 gap of the shifted block \<open>N\<^sub>J M J\<close>), the obligation is
  EXACTLY the INVERSE-SHIFT identity
    \<open>IncrFirst\<^bsup>m\<^sub>0\<^sub>0 - m\<^sub>1\<^sub>0\<^esup> (Red X) = X\<close>   for \<open>X = N\<^sub>J M J\<close>.
  This is verified empirically (\<open>/tmp/fb_verify.py\<close>, \<open>/tmp/fb_gen3.py\<close>): over the
  non-multi \<open>RedCondA\<close> sequences with \<open>m\<^sub>1\<^sub>0 \<le> m\<^sub>0\<^sub>0\<close> (len\<le>4, vals\<le>3) the
  identity holds 396/396; over the 96 core-nontrunk A&B branches the obligation
  holds 96/96, splitting into 58 \<open>npJ = 0\<close> (so \<open>m\<^sub>1\<^sub>0(N\<^sub>J) = 0\<close>) plus 37 zeroT
  branches (also \<open>m\<^sub>1\<^sub>0 = 0\<close>) and 38 \<open>m\<^sub>1\<^sub>0 > 0\<close> branches.\<close>

text \<open>The pure entry-algebra inverse of @{const shiftRow0}: raising row 0 back up by
  \<open>m\<^sub>0\<^sub>0 = entry M 0 0\<close> via @{const IncrFirst} undoes the row-0 down-shift, provided
  row 0 never underflowed (\<open>monoT M\<close> gives \<open>entry M 0 0 \<le> entry M 0 j\<close>, so
  \<open>(entry M 0 j - m\<^sub>0\<^sub>0) + m\<^sub>0\<^sub>0 = entry M 0 j\<close>).  EMPIRICAL: 0-fail over all
  non-multi sequences (\<open>/tmp/fb_alg.py\<close>, 10224 cases).\<close>

lemma bwd_IncrFirst_m00_shiftRow0_monoT:
  assumes MT: "M \<in> T_PS" and mono: "monoT M"
  shows "(IncrFirst ^^ (entry M 0 0)) (shiftRow0 M) = M"
proof (rule nth_equalityI)
  let ?m00 = "entry M 0 0"
  show "Lng ((IncrFirst ^^ ?m00) (shiftRow0 M)) = Lng M" by simp
next
  fix j assume jl0: "j < Lng ((IncrFirst ^^ (entry M 0 0)) (shiftRow0 M))"
  let ?m00 = "entry M 0 0"
  have jl: "j < Lng M" using jl0 by simp
  have jsh: "j < Lng (shiftRow0 M)" using jl by simp
  \<comment> \<open>row 0 (fst): \<open>(entry M 0 j - m\<^sub>0\<^sub>0) + m\<^sub>0\<^sub>0 = entry M 0 j\<close>.\<close>
  have e0: "entry ((IncrFirst ^^ ?m00) (shiftRow0 M)) 0 j = entry M 0 j"
  proof -
    have "entry ((IncrFirst ^^ ?m00) (shiftRow0 M)) 0 j
        = entry (shiftRow0 M) 0 j + ?m00"
      by (rule entry_funpow_IncrFirst0[OF jsh])
    also have "\<dots> = (entry M 0 j - ?m00) + ?m00"
      using entry_shiftRow0_0[OF jl] by simp
    also have "\<dots> = entry M 0 j"
      using entry0_ge_min[OF MT mono jl] by simp
    finally show ?thesis .
  qed
  \<comment> \<open>row 1 (snd): unchanged.\<close>
  have e1: "entry ((IncrFirst ^^ ?m00) (shiftRow0 M)) 1 j = entry M 1 j"
  proof -
    have "entry ((IncrFirst ^^ ?m00) (shiftRow0 M)) 1 j
        = entry (shiftRow0 M) 1 j"
      by (rule entry_funpow_IncrFirst1[OF jsh])
    also have "\<dots> = entry M 1 j" using entry_shiftRow0_1[OF jl] by simp
    finally show ?thesis .
  qed
  show "(IncrFirst ^^ ?m00) (shiftRow0 M) ! j = M ! j"
  proof -
    have "fst ((IncrFirst ^^ ?m00) (shiftRow0 M) ! j) = fst (M ! j)"
      using e0 by (simp add: entry_def)
    moreover have "snd ((IncrFirst ^^ ?m00) (shiftRow0 M) ! j) = snd (M ! j)"
      using e1 by (simp add: entry_def)
    ultimately show ?thesis by (simp add: prod_eq_iff)
  qed
qed

end
