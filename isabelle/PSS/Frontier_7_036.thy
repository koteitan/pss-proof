theory Frontier_7_036
  imports Support_7_030
begin

\<comment> \<open>§7.4 monoT interior (C): id3 structural collapse green; atom/cond
   correspondences (A.3 entries + transCond) supplied as hyps for the assembly.
   (A) transJ0/transJm1/entry1 shift unconditional; (B) id2 / (C) id3 callable.\<close>


section \<open>§7.4 monoT-interior identity (3) — transCond correspondences (Step 1)\<close>

text \<open>(A.4) \<open>adm\<close> at the row-0 parent shifts: \<open>adm N (transJ0 N) = adm M (transJ0 M)\<close>
  where \<open>N = Red(seg M m j\<^sub>1)\<close>.  Both sides are the row-0 nearest-ancestor
  admissibility used by every \<open>transCond\<close>.  Proof: \<open>transJ0 N = j\<^sub>0 - m\<close> (A.1);
  transport \<open>adm\<close> through \<open>S = (IncrFirst^^k) N\<close> (invariant) then through the
  slice via @{thm [source] m_6_3_adm_slice} (the boundary \<open>m = j\<^sub>0\<close> subcase is
  absorbed because there \<open>adm M j\<^sub>0 = adm M m\<close> holds from \<open>(M,m) \<in> Marked\<close>).\<close>

lemma repr_adm_transJ0_shift:
  assumes mM: "(M, m) \<in> Marked" and MR: "M \<in> RT_PS" and mint: "m < Lng M - 2"
    and leM: "leR M 0 m (Lng M - 1)"
    and hp: "hasParent M 0 (Lng M - 1)"
    and anc0: "m \<le> parent M 0 (Lng M - 1)"
    and j0lt: "parent M 0 (Lng M - 1) < Lng M - 1"
  shows "adm (Red (seg M m (Lng M - 1))) (transJ0 (Red (seg M m (Lng M - 1))))
       = adm M (transJ0 M)"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  let ?j1 = "Lng M - 1"  let ?S = "seg M m ?j1"  let ?N = "Red ?S"
  let ?j0 = "parent M 0 ?j1"
  have L: "2 < Lng M" using mint by linarith
  have mj1: "m < ?j1" using mint by linarith
  have j1L: "?j1 \<le> Lng M - 1" by simp
  define k where "k = entry M 0 m - entry M 1 m"
  have segeq: "?S = (IncrFirst ^^ k) ?N"
    using m_6_6_ancestor_slice_Red_IncrFirst[OF MR mj1 j1L leM] k_def by simp
  \<comment> \<open>A.1: \<open>transJ0 N = j\<^sub>0 - m\<close>\<close>
  have j0N: "transJ0 ?N = ?j0 - m"
    using repr_transJ0_shift[OF MR mint leM hp anc0]
    by (simp add: transJ0_def transJ1_def)
  \<comment> \<open>transport \<open>adm\<close>: N \<leftrightarrow> S (IncrFirst-invariant), then S \<leftrightarrow> M (slice)\<close>
  have admNS: "adm ?N (?j0 - m) = adm ?S (?j0 - m)"
    using segeq adm_funpow_IncrFirst_eq[of k ?N "?j0 - m"] by simp
  have mj0: "m \<le> ?j0" using anc0 .
  have j0j1: "?j0 \<le> ?j1" using j0lt by simp
  have admSM: "(adm M ?j0 \<or> m = ?j0 \<or> ?j0 = ?j1) = adm ?S (?j0 - m)"
    by (rule m_6_3_adm_slice[OF MT mj0 j0j1 j1L])
  \<comment> \<open>\<open>?j0 = ?j1\<close> impossible (\<open>j0lt\<close>); \<open>m = ?j0\<close> forces \<open>adm M ?j0 = adm M m\<close>\<close>
  have admMm: "adm M m" using mM by (simp add: Marked_def)
  have collapse: "(adm M ?j0 \<or> m = ?j0 \<or> ?j0 = ?j1) = adm M ?j0"
  proof
    assume "adm M ?j0 \<or> m = ?j0 \<or> ?j0 = ?j1"
    moreover have "?j0 \<noteq> ?j1" using j0lt by simp
    ultimately have "adm M ?j0 \<or> m = ?j0" by blast
    thus "adm M ?j0" using admMm by auto
  next
    assume "adm M ?j0" thus "adm M ?j0 \<or> m = ?j0 \<or> ?j0 = ?j1" by blast
  qed
  have "adm ?N (transJ0 ?N) = adm ?N (?j0 - m)" using j0N by simp
  also have "\<dots> = adm ?S (?j0 - m)" using admNS by simp
  also have "\<dots> = adm M ?j0" using admSM collapse by simp
  also have "\<dots> = adm M (transJ0 M)" by (simp add: transJ0_def transJ1_def)
  finally show ?thesis .
qed

text \<open>The bundle of atom correspondences between \<open>M\<close> and \<open>N = Red(seg M m j\<^sub>1)\<close>
  on which all four \<open>transCond\<close>s depend, collected once.  Endpoint/parent shift
  by \<open>-m\<close>, row-1 entries at the two basepoints, and the row-0-parent
  admissibility.  (\<open>jp\<close> abbreviates \<open>parent M 0 (Lng M-1) = transJ0 M\<close>.)\<close>

lemma repr_transCond_atoms:
  assumes mM: "(M, m) \<in> Marked" and MR: "M \<in> RT_PS" and mint: "m < Lng M - 2"
    and leM: "leR M 0 m (Lng M - 1)"
    and hp: "hasParent M 0 (Lng M - 1)"
    and anc0: "m \<le> parent M 0 (Lng M - 1)"
    and j0lt: "parent M 0 (Lng M - 1) < Lng M - 1"
  shows "Lng (Red (seg M m (Lng M - 1))) - 1 = (Lng M - 1) - m"
    and "parent (Red (seg M m (Lng M - 1))) 0
           (Lng (Red (seg M m (Lng M - 1))) - 1) = parent M 0 (Lng M - 1) - m"
    and "entry (Red (seg M m (Lng M - 1))) 1
           (Lng (Red (seg M m (Lng M - 1))) - 1) = entry M 1 (Lng M - 1)"
    and "entry (Red (seg M m (Lng M - 1))) 1
           (parent (Red (seg M m (Lng M - 1))) 0
              (Lng (Red (seg M m (Lng M - 1))) - 1))
         = entry M 1 (parent M 0 (Lng M - 1))"
    and "adm (Red (seg M m (Lng M - 1)))
           (parent (Red (seg M m (Lng M - 1))) 0
              (Lng (Red (seg M m (Lng M - 1))) - 1))
         = adm M (parent M 0 (Lng M - 1))"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  let ?j1 = "Lng M - 1"  let ?S = "seg M m ?j1"  let ?N = "Red ?S"
  let ?j0 = "parent M 0 ?j1"
  have L: "2 < Lng M" using mint by linarith
  have mj1: "m < ?j1" using mint by linarith
  have j1L: "?j1 \<le> Lng M - 1" by simp
  have mj0: "m \<le> ?j0" using anc0 .
  have j0j1: "?j0 < ?j1" using j0lt by simp
  define k where "k = entry M 0 m - entry M 1 m"
  have segeq: "?S = (IncrFirst ^^ k) ?N"
    using m_6_6_ancestor_slice_Red_IncrFirst[OF MR mj1 j1L leM] k_def by simp
  \<comment> \<open>\<open>Lng N = Suc j\<^sub>1 - m\<close>, hence \<open>Lng N - 1 = j\<^sub>1 - m\<close>\<close>
  have LS: "Lng ?S = Suc ?j1 - m" by simp
  have LNS: "Lng ?N = Lng ?S"
    using arg_cong[OF segeq, of Lng] by (simp add: Lng_funpow_IncrFirst)
  have LN: "Lng ?N = Suc ?j1 - m" using LNS LS by simp
  show endp: "Lng ?N - 1 = ?j1 - m" using LN mj1 by simp
  \<comment> \<open>\<open>parent N 0 (Lng N-1) = transJ0 N = j\<^sub>0 - m\<close> (A.1)\<close>
  have parN: "parent ?N 0 (Lng ?N - 1) = ?j0 - m"
    using repr_transJ0_shift[OF MR mint leM hp anc0]
    by (simp add: transJ0_def transJ1_def)
  show "parent ?N 0 (Lng ?N - 1) = ?j0 - m" by (rule parN)
  \<comment> \<open>\<open>entry N 1 (Lng N-1) = entry M 1 j\<^sub>1\<close> (A.3 at \<open>i = j\<^sub>1 - m\<close>)\<close>
  have iN1: "?j1 - m < Lng ?N" using LN mj1 by linarith
  have e1: "entry ?N 1 (Lng ?N - 1) = entry M 1 ?j1"
  proof -
    have "entry ?N 1 (?j1 - m) = entry M 1 (m + (?j1 - m))"
      by (rule repr_entry1_shift[OF MR mint leM]) (use iN1 endp in simp)
    thus ?thesis using endp mj1 by simp
  qed
  show "entry ?N 1 (Lng ?N - 1) = entry M 1 ?j1" by (rule e1)
  \<comment> \<open>\<open>entry N 1 (parent N 0 (Lng N-1)) = entry M 1 j\<^sub>0\<close> (A.3 at \<open>i = j\<^sub>0 - m\<close>)\<close>
  have iN0: "?j0 - m < Lng ?N" using LN j0j1 mj0 by linarith
  have e0: "entry ?N 1 (parent ?N 0 (Lng ?N - 1)) = entry M 1 ?j0"
  proof -
    have "entry ?N 1 (?j0 - m) = entry M 1 (m + (?j0 - m))"
      by (rule repr_entry1_shift[OF MR mint leM]) (use iN0 endp in simp)
    thus ?thesis using parN mj0 by simp
  qed
  show "entry ?N 1 (parent ?N 0 (Lng ?N - 1)) = entry M 1 ?j0" by (rule e0)
  \<comment> \<open>\<open>adm N (parent N 0 (Lng N-1)) = adm M j\<^sub>0\<close> (A.4)\<close>
  have a1: "adm ?N (parent ?N 0 (Lng ?N - 1)) = adm M ?j0"
    using repr_adm_transJ0_shift[OF mM MR mint leM hp anc0 j0lt]
    by (simp add: transJ0_def transJ1_def)
  show "adm ?N (parent ?N 0 (Lng ?N - 1)) = adm M ?j0" by (rule a1)
qed


text \<open>Step 1: the four \<open>transCond\<close> correspondences \<open>transCond* N = transCond* M\<close>
  (\<open>N = Red(seg M m j\<^sub>1)\<close>), under the monoT-interior hypotheses.  Each unfolds the
  \<open>transCond*_def\<close> and rewrites every \<open>N\<close>-atom by the bundle
  @{thm [source] repr_transCond_atoms}; the residual length/index arithmetic uses
  \<open>m \<le> j\<^sub>0\<close> (\<open>anc0\<close>).  Empirically exact (\<open>repr_transcond_check\<close>: 0 viol).\<close>

lemma repr_transCondI_eq:
  assumes mM: "(M, m) \<in> Marked" and MR: "M \<in> RT_PS" and mint: "m < Lng M - 2"
    and leM: "leR M 0 m (Lng M - 1)"
    and hp: "hasParent M 0 (Lng M - 1)"
    and anc0: "m \<le> parent M 0 (Lng M - 1)"
    and j0lt: "parent M 0 (Lng M - 1) < Lng M - 1"
  shows "transCondI (Red (seg M m (Lng M - 1))) = transCondI M"
proof -
  note B = repr_transCond_atoms[OF mM MR mint leM hp anc0 j0lt]
  let ?N = "Red (seg M m (Lng M - 1))"
  have "transCondI ?N \<longleftrightarrow>
          entry ?N 1 (Lng ?N - 1) = 0 \<and> adm ?N (parent ?N 0 (Lng ?N - 1))"
    by (simp add: transCondI_def)
  also have "\<dots> \<longleftrightarrow> entry M 1 (Lng M - 1) = 0 \<and> adm M (parent M 0 (Lng M - 1))"
    by (simp only: B(3) B(5))
  also have "\<dots> \<longleftrightarrow> transCondI M" by (simp add: transCondI_def)
  finally show ?thesis .
qed

lemma repr_transCondIII_eq:
  assumes mM: "(M, m) \<in> Marked" and MR: "M \<in> RT_PS" and mint: "m < Lng M - 2"
    and leM: "leR M 0 m (Lng M - 1)"
    and hp: "hasParent M 0 (Lng M - 1)"
    and anc0: "m \<le> parent M 0 (Lng M - 1)"
    and j0lt: "parent M 0 (Lng M - 1) < Lng M - 1"
  shows "transCondIII (Red (seg M m (Lng M - 1))) = transCondIII M"
proof -
  note B = repr_transCond_atoms[OF mM MR mint leM hp anc0 j0lt]
  let ?N = "Red (seg M m (Lng M - 1))"
  have "transCondIII ?N \<longleftrightarrow>
          entry ?N 1 (Lng ?N - 1) > 0
        \<and> entry ?N 1 (parent ?N 0 (Lng ?N - 1)) \<ge> entry ?N 1 (Lng ?N - 1)
        \<and> adm ?N (parent ?N 0 (Lng ?N - 1))"
    by (simp add: transCondIII_def)
  also have "\<dots> \<longleftrightarrow>
          entry M 1 (Lng M - 1) > 0
        \<and> entry M 1 (parent M 0 (Lng M - 1)) \<ge> entry M 1 (Lng M - 1)
        \<and> adm M (parent M 0 (Lng M - 1))"
    by (simp only: B(3) B(4) B(5))
  also have "\<dots> \<longleftrightarrow> transCondIII M" by (simp add: transCondIII_def)
  finally show ?thesis .
qed

lemma repr_transCondV_eq:
  assumes mM: "(M, m) \<in> Marked" and MR: "M \<in> RT_PS" and mint: "m < Lng M - 2"
    and leM: "leR M 0 m (Lng M - 1)"
    and hp: "hasParent M 0 (Lng M - 1)"
    and anc0: "m \<le> parent M 0 (Lng M - 1)"
    and j0lt: "parent M 0 (Lng M - 1) < Lng M - 1"
  shows "transCondV (Red (seg M m (Lng M - 1))) = transCondV M"
proof -
  note B = repr_transCond_atoms[OF mM MR mint leM hp anc0 j0lt]
  let ?N = "Red (seg M m (Lng M - 1))"
  let ?j1 = "Lng M - 1"  let ?j0 = "parent M 0 ?j1"
  \<comment> \<open>endpoint/parent in shifted form, with the length arithmetic\<close>
  have endp: "Lng ?N - 1 = ?j1 - m" by (rule B(1))
  have parN: "parent ?N 0 (Lng ?N - 1) = ?j0 - m" by (rule B(2))
  \<comment> \<open>\<open>(j\<^sub>0 - m) + 1 < (j\<^sub>1 - m) \<longleftrightarrow> j\<^sub>0 + 1 < j\<^sub>1\<close> since \<open>m \<le> j\<^sub>0 < j\<^sub>1\<close>\<close>
  have ar: "(?j0 - m) + 1 < ?j1 - m \<longleftrightarrow> ?j0 + 1 < ?j1"
    using anc0 j0lt by linarith
  have "transCondV ?N \<longleftrightarrow>
          entry ?N 1 (Lng ?N - 1) > 0
        \<and> entry ?N 1 (parent ?N 0 (Lng ?N - 1)) + 1 = entry ?N 1 (Lng ?N - 1)
        \<and> parent ?N 0 (Lng ?N - 1) + 1 < Lng ?N - 1"
    by (simp add: transCondV_def)
  also have "\<dots> \<longleftrightarrow>
          entry M 1 ?j1 > 0
        \<and> entry M 1 ?j0 + 1 = entry M 1 ?j1
        \<and> ?j0 + 1 < ?j1"
    using B(3) B(4) endp parN ar by simp
  also have "\<dots> \<longleftrightarrow> transCondV M" by (simp add: transCondV_def)
  finally show ?thesis .
qed

lemma repr_transCondVI_eq:
  assumes mM: "(M, m) \<in> Marked" and MR: "M \<in> RT_PS" and mint: "m < Lng M - 2"
    and leM: "leR M 0 m (Lng M - 1)"
    and hp: "hasParent M 0 (Lng M - 1)"
    and anc0: "m \<le> parent M 0 (Lng M - 1)"
    and j0lt: "parent M 0 (Lng M - 1) < Lng M - 1"
  shows "transCondVI (Red (seg M m (Lng M - 1))) = transCondVI M"
proof -
  note B = repr_transCond_atoms[OF mM MR mint leM hp anc0 j0lt]
  let ?N = "Red (seg M m (Lng M - 1))"
  let ?j1 = "Lng M - 1"  let ?j0 = "parent M 0 ?j1"
  have endp: "Lng ?N - 1 = ?j1 - m" by (rule B(1))
  have parN: "parent ?N 0 (Lng ?N - 1) = ?j0 - m" by (rule B(2))
  have ar: "(?j0 - m) + 1 = ?j1 - m \<longleftrightarrow> ?j0 + 1 = ?j1"
    using anc0 j0lt by linarith
  have "transCondVI ?N \<longleftrightarrow>
          entry ?N 1 (Lng ?N - 1) > 0
        \<and> entry ?N 1 (parent ?N 0 (Lng ?N - 1)) + 1 = entry ?N 1 (Lng ?N - 1)
        \<and> parent ?N 0 (Lng ?N - 1) + 1 = Lng ?N - 1"
    by (simp add: transCondVI_def)
  also have "\<dots> \<longleftrightarrow>
          entry M 1 ?j1 > 0
        \<and> entry M 1 ?j0 + 1 = entry M 1 ?j1
        \<and> ?j0 + 1 = ?j1"
    using B(3) B(4) endp parN ar by simp
  also have "\<dots> \<longleftrightarrow> transCondVI M" by (simp add: transCondVI_def)
  finally show ?thesis .
qed

end
