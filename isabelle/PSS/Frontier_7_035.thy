theory Frontier_7_035
  imports Support_7_029
begin

\<comment> \<open>§7.4 monoT interior: helpers (1)-(3) + identity (1) green; (2)/(3) pending.\<close>


section \<open>§7.4 monoT-interior basepoint index-shift bridge (A)\<close>

text \<open>The basepoint indices/entries of \<open>N = Red (seg M m j\<^sub>1)\<close> equal those of
  \<open>M\<close> shifted by \<open>-m\<close>.  Two transports compose:
  \<^item> (S\<leftrightarrow>M) a backward slice \<open>S = seg M m j\<^sub>1\<close> sees the same parent/admissibility
    structure as \<open>M\<close>, offset by \<open>m\<close> (slice bridge @{thm [source] rcpb_nextR_seg},
    parents are globally unique so an in-slice parent IS the \<open>M\<close>-parent);
  \<^item> (S\<leftrightarrow>N) \<open>S = (IncrFirst^^k) N\<close> (@{thm [source] m_6_6_ancestor_slice_Red_IncrFirst}),
    and \<open>IncrFirst\<close> preserves \<open>nextR\<close> (@{thm [source] nextR_funpow_IncrFirst_eq}),
    hence \<open>parent\<close>/\<open>hasParent\<close>/\<open>adm\<close>/\<open>Adm\<close>, and row-1 entries
    (@{thm [source] entry_funpow_IncrFirst1}).\<close>

text \<open>\<open>parent\<close>/\<open>hasParent\<close>/\<open>adm\<close>/\<open>Adm\<close> are \<open>(IncrFirst^^k)\<close>-invariant
  (all are defined purely from \<open>nextR\<close>, which is invariant).\<close>

lemma parent_funpow_IncrFirst_eq:
  "parent ((IncrFirst ^^ k) M) i j = parent M i j"
  unfolding parent_def using nextR_funpow_IncrFirst_eq[of k M] by simp

lemma nadm_funpow_IncrFirst_eq:
  "nadm ((IncrFirst ^^ k) M) j = nadm M j"
  unfolding nadm_def using nextR_funpow_IncrFirst_eq[of k M]
  by (simp add: Lng_funpow_IncrFirst)

lemma adm_funpow_IncrFirst_eq:
  "adm ((IncrFirst ^^ k) M) j = adm M j"
  unfolding adm_def using nadm_funpow_IncrFirst_eq[of k M] by simp

lemma Adm_funpow_IncrFirst_eq:
  "Adm ((IncrFirst ^^ k) M) j = Adm M j"
  unfolding Adm_def using adm_funpow_IncrFirst_eq[of k M]
  by (simp cong: Collect_cong)

text \<open>Converse direction (M\<Rightarrow>S): if \<open>M\<close> has a row-\<open>i\<close> parent of \<open>m+jl\<close> that lies
  inside the slice (\<open>m \<le> parent\<close>) then the slice has the corresponding parent.\<close>

lemma repr_parent_M_to_seg:
  assumes i: "i \<le> (1::nat)" and bL: "b < Lng M"
    and jlS: "jl < Lng (seg M m b)"
    and hpM: "hasParent M i (m + jl)"
    and anc: "m \<le> parent M i (m + jl)"
  shows "hasParent (seg M m b) i jl
         \<and> parent (seg M m b) i jl = parent M i (m + jl) - m"
proof -
  let ?S = "seg M m b"
  obtain p where pM: "nextR M i p (m + jl)"
    and uM: "\<And>p'. nextR M i p' (m + jl) \<Longrightarrow> p' = p"
    using hpM by (auto simp: hasParent_def)
  have peq: "parent M i (m + jl) = p"
    unfolding parent_def
    by (rule the_equality[where P="\<lambda>p. nextR M i p (m + jl)", OF pM uM])
  have mp: "m \<le> p" using anc peq by simp
  then obtain pl where ple: "p = m + pl" by (metis le_add_diff_inverse)
  have pj: "p < m + jl" using pM
    by (cases "i = 0") (auto simp: nextR_def nextrel0_def nextrel1_def)
  have plj: "pl < jl" using ple pj by simp
  have plS: "pl < Lng ?S" using plj jlS by simp
  have nS: "nextR ?S i pl jl"
    using rcpb_nextR_seg[OF bL i plS jlS] pM ple by simp
  have uS: "\<And>pl'. nextR ?S i pl' jl \<Longrightarrow> pl' = pl"
  proof -
    fix pl' assume H: "nextR ?S i pl' jl"
    have plS': "pl' < Lng ?S" and pljj: "pl' < jl"
      using H by (cases "i = 0"; simp_all add: nextR_def nextrel0_def nextrel1_def)+
    have "nextR M i (m + pl') (m + jl)"
      using rcpb_nextR_seg[OF bL i plS' jlS] H by simp
    hence "m + pl' = p" using uM by simp
    thus "pl' = pl" using ple by simp
  qed
  have hpS: "hasParent ?S i jl" unfolding hasParent_def using nS uS by blast
  have pS: "parent ?S i jl = pl"
    unfolding parent_def
    by (rule the_equality[where P="\<lambda>pl. nextR ?S i pl jl", OF nS uS])
  show ?thesis using hpS pS ple peq by simp
qed

text \<open>(A.1) \<open>transJ0\<close> shift: \<open>transJ0 N = transJ0 M - m\<close> where \<open>N = Red(seg M m j\<^sub>1)\<close>,
  \<open>j\<^sub>1 = Lng M - 1\<close>.  Hyp \<open>anc0 : m \<le> parent M 0 j\<^sub>1\<close> (the leR-anchoring, which the
  monoT-interior assembly supplies); \<open>hp : hasParent M 0 j\<^sub>1\<close>.\<close>

lemma repr_transJ0_shift:
  assumes MR: "M \<in> RT_PS" and mint: "m < Lng M - 2"
    and leM: "leR M 0 m (Lng M - 1)"
    and hp: "hasParent M 0 (Lng M - 1)"
    and anc0: "m \<le> parent M 0 (Lng M - 1)"
  shows "transJ0 (Red (seg M m (Lng M - 1))) = transJ0 M - m"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  let ?j1 = "Lng M - 1"  let ?S = "seg M m ?j1"  let ?N = "Red ?S"
  have L: "2 < Lng M" using mint by linarith
  have mj1: "m < ?j1" using mint by linarith
  have j1L: "?j1 \<le> Lng M - 1" by simp
  have j1lt: "?j1 < Lng M" using L by linarith
  \<comment> \<open>\<open>S = (IncrFirst^^k) N\<close>, and \<open>Lng N = Lng S = Suc j\<^sub>1 - m\<close>\<close>
  define k where "k = entry M 0 m - entry M 1 m"
  have segeq: "?S = (IncrFirst ^^ k) ?N"
    using m_6_6_ancestor_slice_Red_IncrFirst[OF MR mj1 j1L leM] k_def by simp
  have LS: "Lng ?S = Suc ?j1 - m" by simp
  have LNS: "Lng ?N = Lng ?S"
    using arg_cong[OF segeq, of Lng] by (simp add: Lng_funpow_IncrFirst)
  have LN: "Lng ?N = Suc ?j1 - m" using LNS LS by simp
  have LNm1: "Lng ?N - 1 = ?j1 - m" using LN mj1 by simp
  \<comment> \<open>local last column \<open>jl = j\<^sub>1 - m\<close>, with \<open>m + jl = j\<^sub>1\<close>\<close>
  have jlS: "?j1 - m < Lng ?S" using mj1 by simp
  have mjl: "m + (?j1 - m) = ?j1" using mj1 by simp
  \<comment> \<open>(M\<Rightarrow>S): slice has the parent, shifted\<close>
  have hpMjl: "hasParent M 0 (m + (?j1 - m))" using hp mjl by simp
  have ancjl: "m \<le> parent M 0 (m + (?j1 - m))" using anc0 mjl by simp
  have sS: "hasParent ?S 0 (?j1 - m)
            \<and> parent ?S 0 (?j1 - m) = parent M 0 (m + (?j1 - m)) - m"
    by (rule repr_parent_M_to_seg[OF _ j1lt jlS hpMjl ancjl]) simp
  have pSeg: "parent ?S 0 (?j1 - m) = parent M 0 ?j1 - m"
    using sS mjl by simp
  \<comment> \<open>(S\<leftrightarrow>N): \<open>parent\<close> invariant under \<open>IncrFirst^^k\<close>\<close>
  have pN: "parent ?N 0 (?j1 - m) = parent ?S 0 (?j1 - m)"
    using segeq parent_funpow_IncrFirst_eq[of k ?N 0 "?j1 - m"] by simp
  have "transJ0 ?N = parent ?N 0 (Lng ?N - 1)" by (simp add: transJ0_def transJ1_def)
  also have "\<dots> = parent ?N 0 (?j1 - m)" using LNm1 by simp
  also have "\<dots> = parent M 0 ?j1 - m" using pN pSeg by simp
  also have "\<dots> = transJ0 M - m" by (simp add: transJ0_def transJ1_def)
  finally show ?thesis .
qed

text \<open>(A.3) row-1 entry shift: \<open>entry N 1 i = entry M 1 (m+i)\<close> for in-range \<open>i\<close>.
  (Stated as A.3 first since A.2 \<open>transJm1\<close> reuses A.1.)\<close>

lemma repr_entry1_shift:
  assumes MR: "M \<in> RT_PS" and mint: "m < Lng M - 2"
    and leM: "leR M 0 m (Lng M - 1)"
    and il: "i < Lng (Red (seg M m (Lng M - 1)))"
  shows "entry (Red (seg M m (Lng M - 1))) 1 i = entry M 1 (m + i)"
proof -
  have MT: "M \<in> T_PS" using MR by (simp add: RT_PS_def)
  let ?j1 = "Lng M - 1"  let ?S = "seg M m ?j1"  let ?N = "Red ?S"
  have L: "2 < Lng M" using mint by linarith
  have mj1: "m < ?j1" using mint by linarith
  have j1L: "?j1 \<le> Lng M - 1" by simp
  define k where "k = entry M 0 m - entry M 1 m"
  have segeq: "?S = (IncrFirst ^^ k) ?N"
    using m_6_6_ancestor_slice_Red_IncrFirst[OF MR mj1 j1L leM] k_def by simp
  have LS: "Lng ?S = Suc ?j1 - m" by simp
  have LNS: "Lng ?N = Lng ?S"
    using arg_cong[OF segeq, of Lng] by (simp add: Lng_funpow_IncrFirst)
  have LN: "Lng ?N = Suc ?j1 - m" using LNS LS by simp
  have iN: "i < Lng ?N" using il by simp
  have iS: "i < Lng ?S" using iN LN LS by simp
  \<comment> \<open>row-1 entry: \<open>S\<leftrightarrow>N\<close> (\<open>IncrFirst^^k\<close> preserves row 1), then \<open>S\<leftrightarrow>M\<close> (\<open>entry_seg\<close>)\<close>
  have eN: "entry ?S 1 i = entry ?N 1 i"
    using segeq entry_funpow_IncrFirst1[OF iN, of k] by simp
  have eM: "entry ?S 1 i = entry M 1 (m + i)" using iS by (simp add: entry_seg)
  show ?thesis using eN eM by simp
qed

text \<open>(A.2) \<open>transJm1\<close> shift: \<open>transJm1 N = transJm1 M - m\<close>.  Reuses A.1
  (\<open>transJ0\<close> shift) inside the \<open>Adm\<close> slice lemma @{thm [source] m_6_3_admof_slice}.\<close>

lemma repr_transJm1_shift:
  assumes mM: "(M, m) \<in> Marked" and MR: "M \<in> RT_PS" and mint: "m < Lng M - 2"
    and leM: "leR M 0 m (Lng M - 1)"
    and hp: "hasParent M 0 (Lng M - 1)"
    and anc0: "m \<le> parent M 0 (Lng M - 1)"
    and j0lt: "parent M 0 (Lng M - 1) < Lng M - 1"
  shows "transJm1 (Red (seg M m (Lng M - 1))) = transJm1 M - m"
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
  \<comment> \<open>A.1: \<open>transJ0 N = transJ0 M - m\<close>, i.e. \<open>parent N 0 (Lng N -1) = ?j0 - m\<close>\<close>
  have j0N: "transJ0 ?N = transJ0 M - m"
    by (rule repr_transJ0_shift[OF MR mint leM hp anc0])
  have j0Neq: "transJ0 ?N = ?j0 - m" using j0N by (simp add: transJ0_def transJ1_def)
  \<comment> \<open>transport \<open>Adm\<close> through \<open>IncrFirst^^k\<close> then slice\<close>
  have AdmN: "Adm ?N (?j0 - m) = Adm ?S (?j0 - m)"
    using segeq Adm_funpow_IncrFirst_eq[of k ?N "?j0 - m"] by simp
  \<comment> \<open>need \<open>m \<le> Adm M ?j0\<close>: \<open>m\<close> is \<open>M\<close>-admissible and \<open>m \<le> ?j0\<close>, so by maximality\<close>
  have mAdm: "adm M m" using mM by (simp add: Marked_def)
  have mAdmJ0: "m \<le> Adm M ?j0" by (rule adm_Adm_max[OF mAdm anc0])
  have AdmSlice: "Adm ?S (?j0 - m) = Adm M ?j0 - m"
    by (rule m_6_3_admof_slice[OF MT mAdmJ0 j0lt j1L])
  have "transJm1 ?N = Adm ?N (transJ0 ?N)" by (simp add: transJm1_def)
  also have "\<dots> = Adm ?N (?j0 - m)" using j0Neq by simp
  also have "\<dots> = Adm ?S (?j0 - m)" using AdmN by simp
  also have "\<dots> = Adm M ?j0 - m" using AdmSlice by simp
  also have "\<dots> = transJm1 M - m" by (simp add: transJm1_def transJ0_def transJ1_def)
  finally show ?thesis .
qed

end
