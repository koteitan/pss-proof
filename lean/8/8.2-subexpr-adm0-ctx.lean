import «5».«5.1-ancestor-basic»
import «6».«6.2-P-fseq»
import «6».«6.2-mono-ancestor-slice»
import «6».«6.3-admof-slice»
import «6».«6.4-P-IdxSum»
import «6».«6.4-FirstNodes-TrMax-Joints»
import «6».«6.4-FirstNodes-Joints-mono»
import «6».«6.4-mono-slice»
import «6».«6.5-Red-welldefined»
import «6».«6.5-Red-le-core»
import «6».«6.5-Red-Pred-commute»
import «6».«6.6-P-condAB»
import «6».«6.6-reduced-iff-condAB»
import «6».«6.6-reduced-coeff»
import «7».«7.3-Trans-welldefined»
import «7».«7.3-Trans-preserves-zeroT»
import «7».«7.3-c1-c2-order»
import «7».«7.3-Mark-rightmost1»
import «7».«7.4-RightNodes-Mark»

/-!
# §8.2 Adm0 文脈ブリック（keystone 幾何ブリッジ＋ガード放電）

- 原文: `tmp/content.md` §8.2（強単項性）。keystone（部分表現の単項成分と `Pred` の
  関係）の Adm0 枝（`Adm_M(j₀) = 0` レジーム）を支える文脈補題群。
- 訂正: **A9**（軽微、LastStep の添字 `J₁ := Lng(Br M) - 1`）と整合する
  添字 `(Br M).length - 1` を使う（Isabelle 版と同一）。
- Isabelle: `isabelle/layerB/pss_wip.thy` の
  `m_8_2_parent_le_TrMax_Adm0` (20615) / `m_8_2_j1eq_Adm0` (20639) /
  `m_8_2_j0eq_Adm0` (20657) / `m_8_2_gA_Adm0` (20727) / `m_8_2_notVI_Adm0` (20763) /
  `m_8_2_condII_or_condIV` (21105) / `m_8_2_nadmj0_notAVI` (21198) /
  `m_8_2_t2ne_notAVI` (21217) / `m_8_2_gB_condIorIII` (21246) /
  `m_8_2_e0gt_e1zero` (21259) / `m_8_2_e0gt_condIV` (21282)。
  私的再証明（suffix `_sx`）: `m_8_2_lastbranch_eq_j1` (20470) /
  `adm_TrMax_succ` (20575) / `nextR1_TrMax_fail` (20680) / `adm_TrMax` (20705) /
  `row0_valley_last` (20973) / `row1_last_bound` (21016) /
  `nadm_Adm_lt` (§7.3) / `m_7_3_t2_nonzero_condIIorIV` (13354)。
- 依存: `6.3-admof-slice`（`Adm_max`/`Adm_le`/`Adm_adm`）、`6.4-*`（`TrMax`/`Br`/
  `FirstNodes`/`Joints` 機構）、`6.5-Red-le-core`（`RedCondA_apply`）、
  `6.6-P-condAB`（`mono_hasParent_row0`）、`6.6-reduced-iff-condAB`（`RTPS_condAB`）、
  `6.6-reduced-coeff`、`7.3-*`/`7.4-RightNodes-Mark`（`Mark` 左端形・非零尾）、
  `5.1-ancestor-basic`。
- 状態: ✅ 証明済（sorry 0）

Isabelle の `M ∈ RT_PS` は `hR : RTPS M`、`M ∈ PT_PS` は
`hmono : monoT M = true`（`TPS` は `RTPS_TPS` で回収）と写す。
これらは次 wave の Adm0 組み立て（wip 20828）が消費する文脈放電ブリックである。
-/

namespace PSS

/-! ## 支援私的補題（幹の右端の許容性、wip 20575–20714 の再証明） -/

/-- 行 1 の幹ステップは `TrMax M` で必ず破れる（wip `nextR1_TrMax_fail` 20680）。 -/
private theorem nextR1_TrMax_fail_sx (M : PS) (hM : TPS M) :
    nextR M 1 (TrMax M) (TrMax M + 1) = false := by
  cases hst : nextR M 1 (TrMax M) (TrMax M + 1) with
  | false => rfl
  | true =>
      exfalso
      have hall : ∀ j, j < TrMax M + 1 → nextR M 1 j (j + 1) = true := by
        intro j hj
        rcases Nat.lt_or_ge j (TrMax M) with h | h
        · exact TrMax_trunk_step M j hM h
        · have hje : j = TrMax M := by omega
          rw [hje]
          exact hst
      have := le_TrMax_intro_wd M (TrMax M + 1) hM hall
      omega

/-- `TrMax M + 1` は `M` 許容（wip `adm_TrMax_succ` 20575、並列 scope の私的再証明）。 -/
private theorem adm_TrMax_succ_sx (M : PS) (hM : TPS M) :
    adm M (TrMax M + 1) = true := by
  have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have htb : TrMax M ≤ Lng M - 1 := TrMax_bound M hM
  have hnostep := nextR1_TrMax_fail_sx M hM
  have hno : ¬ Lng M < TrMax M + 1 := by omega
  simp [adm, nadm, hnostep, hno]

/-- `TrMax M` 自身も `M` 許容（wip `adm_TrMax` 20705）。 -/
private theorem adm_TrMax_sx (M : PS) (hM : TPS M) :
    adm M (TrMax M) = true := by
  have hMpos : 0 < Lng M := List.length_pos_of_ne_nil hM
  have htb : TrMax M ≤ Lng M - 1 := TrMax_bound M hM
  have hnostep := nextR1_TrMax_fail_sx M hM
  have hno : ¬ Lng M < TrMax M := by omega
  simp [adm, nadm, hnostep, hno]

/-- 非許容点の許容化は真に下がる（Isabelle `nadm_Adm_lt` の再証明）。 -/
private theorem nadm_Adm_lt_sx (M : PS) (j : ℕ) (hna : adm M j = false) :
    Adm M j < j := by
  have hle := Adm_le M j
  have hadm := Adm_adm M j
  rcases Nat.lt_or_ge (Adm M j) j with h | h
  · exact h
  · exfalso
    have heq : Adm M j = j := by omega
    rw [heq] at hadm
    rw [hadm] at hna
    exact absurd hna (by simp)

/-! ## H3: Adm0 レジームでは最終列の行 0 親は幹内（wip 20615） -/

/-- §8.2 keystone 幾何ブリッジ H3（Isabelle `m_8_2_parent_le_TrMax_Adm0` 20615）。
`transJm1 M = 0` のとき `parent M 0 (Lng M - 1) ≤ TrMax M`。 -/
theorem parent_le_TrMax_Adm0 (M : PS) (hR : RTPS M)
    (_hmono : monoT M = true) (hAdm0 : transJm1 M = 0) :
    parent M 0 (Lng M - 1) ≤ TrMax M := by
  have hM : TPS M := RTPS_TPS M hR
  by_contra hnot
  have hgt : TrMax M + 1 ≤ parent M 0 (Lng M - 1) := by omega
  have ha := adm_TrMax_succ_sx M hM
  have hmax := Adm_max M (TrMax M + 1) (parent M 0 (Lng M - 1)) ha hgt
  have h0 : Adm M (parent M 0 (Lng M - 1)) = 0 := by
    simpa [transJm1, transJ0, lastParent, lastIdx] using hAdm0
  omega

/-! ## clause-(1) ガード gB / clause-(2) ガード e0gt（条件別、wip 21246/21259） -/

/-- §8.2 Adm0 clause-(1) ガード `gB`、(I)/(III) 部分ケース
（Isabelle `m_8_2_gB_condIorIII` 21246）。 -/
theorem gB_condIorIII (M : PS)
    (hcond : transCondI M = true ∨ transCondIII M = true) :
    adm M (parent M 0 (Lng M - 1)) = true := by
  rcases hcond with h | h
  · simp only [transCondI, Bool.and_eq_true] at h
    simpa [lastParent, lastIdx] using h.2
  · simp only [transCondIII, Bool.and_eq_true] at h
    simpa [lastParent, lastIdx] using h.2

/-- §8.2 Adm0 clause-(2) ガード `e0gt`、`M_{1,j₁} = 0` 部分ケース
（Isabelle `m_8_2_e0gt_e1zero` 21259）。 -/
theorem e0gt_e1zero (M : PS) (hM : TPS M) (hmono : monoT M = true)
    (hL : 1 < Lng M) (he1z : entry M 1 (Lng M - 1) = 0) :
    entry M 1 (Lng M - 1) < entry M 0 (Lng M - 1) := by
  have hleM : leR M 0 0 (Lng M - 1) = true := by
    simp only [monoT, Bool.and_eq_true] at hmono
    exact hmono.2
  have := ancestor_basic_1 M 0 (Lng M - 1) (Lng M - 1) hM
    (by omega) (le_refl _) hleM
  omega

/-! ## 幾何ブリッジ: 最終枝の左端 = 最終列（wip 20470 の私的再証明） -/

/-- §8.2 keystone 幾何ブリッジ（Isabelle `m_8_2_lastbranch_eq_j1` 20470、
並列 scope の私的再証明）。`parent M 0 (Lng M - 1) ≤ TrMax M` の下で最終枝の
左端は最終列に一致する。証明: そうでなければ最終枝は長さ 2 以上の `monoT`
ブロックで、その左端 `j₁'` の行 0 値は最終列の行 0 値より真に小さい
（`ancestor_basic_1`）。すると `nextR0_largest_below` が
`j₁' ≤ parent M 0 (Lng M - 1) ≤ TrMax M < j₁'` を強制して矛盾。 -/
private theorem lastbranch_eq_j1_sx (M : PS) (_hR : RTPS M)
    (hmono : monoT M = true) (hBrne : Br M ≠ []) (hj1gt : 1 < Lng M - 1)
    (hparTr : parent M 0 (Lng M - 1) ≤ TrMax M) (hM : TPS M) :
    (FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1 := by
  have hBrL : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hJ : (Br M).length - 1 < (Br M).length := by omega
  have htrj1 : TrMax M < (FirstNodes M).getD ((Br M).length - 1) 0 :=
    (FirstNodes_TrMax_Joints M ((Br M).length - 1) hM hmono hJ).2
  -- 枝分解の骨格
  have hbound : TrMax M ≤ Lng M - 1 := TrMax_bound M hM
  have hne : TrMax M ≠ Lng M - 1 := by
    intro heq
    exact hBrne (by simp [Br, heq])
  have hBr : Br M = P (seg M (TrMax M + 1) (Lng M - 1)) := by
    simp [Br, hne]
  set N := seg M (TrMax M + 1) (Lng M - 1) with hN_def
  have hNlen : Lng N = Lng M - 1 - TrMax M := by
    simp [hN_def]
  have hNpos : 0 < Lng N := by omega
  have hNT : TPS N := by
    intro hnil
    have : Lng N = 0 := by simp [hnil]
    omega
  have hJP : (Br M).length - 1 < (P N).length := by
    rw [← hBr]
    exact hJ
  -- 最終ブロック = seg N a (Lng N - 1)
  set a := (IdxSum (P N)).getD ((Br M).length - 1) 0 with ha_def
  have hPlen : (P N).length = (Br M).length := by rw [hBr]
  have hsucc : (Br M).length - 1 + 1 = (P N).length := by omega
  have htot : (IdxSum (P N)).getD ((Br M).length - 1 + 1) 0 = Lng N := by
    rw [hsucc, idxSum_total]
    rw [P_concat N]
  have hblock : (P N).getD ((Br M).length - 1) [] = seg N a (Lng N - 1) := by
    have := P_IdxSum N ((Br M).length - 1) hNT (by omega)
    rw [htot] at this
    exact this
  have hCne : 0 < Lng ((P N).getD ((Br M).length - 1) []) :=
    P_component_nonempty N ((Br M).length - 1) hNT hJP
  have hClen : Lng ((P N).getD ((Br M).length - 1) []) = Lng N - a := by
    rw [hblock]
    simp
    omega
  have haN : a < Lng N := by omega
  -- j₁' = TrMax M + 1 + a
  have hfn : (FirstNodes M).getD ((Br M).length - 1) 0 = TrMax M + 1 + a := by
    have h := FirstNodes_getD M ((Br M).length - 1) hJ
    rw [h, hBr, hPlen, ← ha_def]
  have hj1'le : (FirstNodes M).getD ((Br M).length - 1) 0 ≤ Lng M - 1 := by
    omega
  by_contra hne2
  have hj1lt : (FirstNodes M).getD ((Br M).length - 1) 0 < Lng M - 1 := by
    omega
  -- 最終ブロックは長さ ≥ 2、よって monoT
  have hClen2 : 1 < Lng ((P N).getD ((Br M).length - 1) []) := by omega
  set C := (Br M).getD ((Br M).length - 1) [] with hC_def
  have hCP : C = (P N).getD ((Br M).length - 1) [] := by
    rw [hC_def, hBr]
  have hCz : zeroT C = false := by
    have hlen : Lng C ≠ 1 := by rw [hCP]; omega
    simp only [zeroT, Bool.and_eq_false_iff]
    left
    simpa using hlen
  have hCmono : monoT C = true := by
    rcases Br_component_nonmulti M ((Br M).length - 1) hM hJ with hz | hm
    · rw [← hC_def] at hz
      rw [hCz] at hz
      exact absurd hz (by simp)
    · rw [← hC_def] at hm
      exact hm
  have hCT : TPS C := by
    have := Br_component_TPS M ((Br M).length - 1) hM hJ
    rwa [← hC_def] at this
  -- 左端の行 0 値はブロック右端の行 0 値より真に小さい
  have hCleR : leR C 0 0 (Lng C - 1) = true := by
    simp only [monoT, Bool.and_eq_true] at hCmono
    exact hCmono.2
  have hCLlen : 1 < Lng C := by rw [hCP]; omega
  have hCent : entry C 0 0 < entry C 0 (Lng C - 1) :=
    ancestor_basic_1 C 0 (Lng C - 1) (Lng C - 1) hCT (by omega)
      (le_refl _) hCleR
  -- 左端の値の転送
  have hleft : entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0)
      = entry C 0 0 := by
    have := entry_FirstNodes_eq_component M ((Br M).length - 1) hM hmono hJ
    rwa [← hC_def] at this
  -- 右端の値の転送
  have hCseg : C = seg N a (Lng N - 1) := by rw [hCP, hblock]
  have hClenC : Lng C = Lng N - a := by rw [hCP, hClen]
  have hright : entry C 0 (Lng C - 1) = entry M 0 (Lng M - 1) := by
    have h1 : entry C 0 (Lng C - 1) = entry N 0 (a + (Lng C - 1)) := by
      rw [hCseg]
      apply entry_seg
      simp
      omega
    have h2 : a + (Lng C - 1) = Lng N - 1 := by omega
    have h3 : entry N 0 (Lng N - 1)
        = entry M 0 (TrMax M + 1 + (Lng N - 1)) := by
      rw [hN_def]
      apply entry_seg
      simp
      omega
    have h4 : TrMax M + 1 + (Lng N - 1) = Lng M - 1 := by omega
    rw [h1, h2, h3, h4]
  have hentlt : entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0)
      < entry M 0 (Lng M - 1) := by
    rw [hleft, ← hright]
    exact hCent
  -- 行 0 親の最大性で矛盾
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hnxt := nextR_parent0_of_hasParent M (Lng M - 1) hp
  have hlb := nextR0_largest_below M (parent M 0 (Lng M - 1))
    ((FirstNodes M).getD ((Br M).length - 1) 0) (Lng M - 1) hnxt hj1lt hentlt
  omega

/-- §8.2 keystone ブリッジ、Adm0 で `j₁' = j₁` 無条件化
（Isabelle `m_8_2_j1eq_Adm0` 20639）。 -/
theorem j1eq_Adm0 (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hj1gt : 1 < Lng M - 1) (hAdm0 : transJm1 M = 0) :
    (FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1 :=
  lastbranch_eq_j1_sx M hR hmono hBrne hj1gt
    (parent_le_TrMax_Adm0 M hR hmono hAdm0) (RTPS_TPS M hR)

/-- §8.2 keystone ブリッジ、Adm0 で `j₀' = transJ0 M` 無条件化
（Isabelle `m_8_2_j0eq_Adm0` 20657）。 -/
theorem j0eq_Adm0 (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hj1gt : 1 < Lng M - 1) (hAdm0 : transJm1 M = 0) :
    (Joints M).getD ((Br M).length - 1) 0 = transJ0 M := by
  have hBrL : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hJ : (Br M).length - 1 < (Br M).length := by omega
  have hj1eq := j1eq_Adm0 M hR hmono hBrne hj1gt hAdm0
  rw [Joints_getD M ((Br M).length - 1) hJ, hj1eq]
  simp [transJ0, lastParent, lastIdx]

/-! ## clause-(1) ガード gA と cond VI の空虚性（wip 20727/20763） -/

/-- §8.2 keystone clause-(1) ガード `gA`、Adm0 枝
（Isabelle `m_8_2_gA_Adm0` 20727）。 -/
theorem gA_Adm0 (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hj1gt : 1 < Lng M - 1) (hAdm0 : transJm1 M = 0) :
    TrMax M = 0 ∨ (Joints M).getD ((Br M).length - 1) 0 < TrMax M := by
  have hM : TPS M := RTPS_TPS M hR
  have hAdm0' : Adm M (parent M 0 (Lng M - 1)) = 0 := by
    simpa [transJm1, transJ0, lastParent, lastIdx] using hAdm0
  have hj0eq : (Joints M).getD ((Br M).length - 1) 0
      = parent M 0 (Lng M - 1) := by
    have := j0eq_Adm0 M hR hmono hBrne hj1gt hAdm0
    simpa [transJ0, lastParent, lastIdx] using this
  rw [hj0eq]
  by_contra hnot
  have hpos : TrMax M ≠ 0 := fun h => hnot (Or.inl h)
  have hge : TrMax M ≤ parent M 0 (Lng M - 1) := by
    by_contra hlt
    exact hnot (Or.inr (by omega))
  have ha := adm_TrMax_sx M hM
  have hmax := Adm_max M (TrMax M) (parent M 0 (Lng M - 1)) ha hge
  omega

/-- §8.2 Adm0 では条件 (VI) は空虚（Isabelle `m_8_2_notVI_Adm0` 20763）。 -/
theorem notVI_Adm0 (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hBrne : Br M ≠ []) (hj1gt : 1 < Lng M - 1) (hAdm0 : transJm1 M = 0) :
    transCondVI M = false := by
  have hM : TPS M := RTPS_TPS M hR
  have htb : TrMax M ≤ Lng M - 1 := TrMax_bound M hM
  have htrne : TrMax M ≠ Lng M - 1 := by
    intro heq
    exact hBrne (by simp [Br, heq])
  have htrlt : TrMax M < Lng M - 1 := by omega
  have h3 : parent M 0 (Lng M - 1) ≤ TrMax M :=
    parent_le_TrMax_Adm0 M hR hmono hAdm0
  have hj0eq : (Joints M).getD ((Br M).length - 1) 0
      = parent M 0 (Lng M - 1) := by
    have := j0eq_Adm0 M hR hmono hBrne hj1gt hAdm0
    simpa [transJ0, lastParent, lastIdx] using this
  have hgA := gA_Adm0 M hR hmono hBrne hj1gt hAdm0
  rw [hj0eq] at hgA
  have hneq : parent M 0 (Lng M - 1) + 1 ≠ Lng M - 1 := by
    rcases hgA with h0 | hlt
    · omega
    · omega
  have hlast : (lastParent M + 1 == lastIdx M) = false := by
    simp only [lastParent, lastIdx, beq_eq_false_iff_ne, ne_eq]
    exact hneq
  simp [transCondVI, hlast]

/-! ## 行 1 の最終列バウンド（wip 20973/21016 の私的再証明） -/

/-- `le0Aux` の添字単調性（5.1 の私的補題の再証明）。 -/
private theorem le0Aux_index_mono_sx {M : PS} {fuel a b : ℕ}
    (h : le0Aux M fuel a b = true) : a ≤ b := by
  induction fuel generalizing b with
  | zero =>
      have : a = b := by simpa [le0Aux] using h
      omega
  | succ fuel ih =>
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨p, hpb, _, hap⟩
      · omega
      · have := ih hap
        omega

/-- `le0Aux` の最終ステップ剥がし: `a ≠ b` なら `b` の直前点 `p` がある。 -/
private theorem le0Aux_last_step_sx {M : PS} {fuel a b : ℕ}
    (h : le0Aux M fuel a b = true) (hne : a ≠ b) :
    ∃ p, nextrel0 M p b = true ∧ le0Aux M fuel a p = true := by
  cases fuel with
  | zero =>
      have : a = b := by simpa [le0Aux] using h
      exact absurd this hne
  | succ fuel =>
      simp only [le0Aux, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
        Bool.and_eq_true, List.mem_range] at h
      rcases h with h | ⟨p, _, hnext, hap⟩
      · exact absurd h hne
      · exact ⟨p, hnext,
          le0Aux_mono_fseq M fuel (fuel + 1) a p (by omega) hap⟩

/-- 行 0 の谷（wip `row0_valley_last` 20973 の私的再証明）: `monoT M` で
`parent M 0 (Lng M - 1) < j` かつ `le0 M j (Lng M - 1)` なら `j = Lng M - 1`。 -/
private theorem row0_valley_last_sx (M : PS) (_hM : TPS M)
    (_hmono : monoT M = true) (_hL : 1 < Lng M) (j : ℕ)
    (hj : parent M 0 (Lng M - 1) < j)
    (hle : le0 M j (Lng M - 1) = true) : j = Lng M - 1 := by
  by_contra hne
  have hh := hle
  simp only [le0, Bool.and_eq_true, decide_eq_true_eq] at hh
  obtain ⟨p, hnext, hap⟩ := le0Aux_last_step_sx hh.2 hne
  have hpR : nextR M 0 p (Lng M - 1) = true := by simpa [nextR] using hnext
  have hpar : parent M 0 (Lng M - 1) = p := parent_eq_of_nextR0 M p _ hpR
  have hjp : j ≤ p := le0Aux_index_mono_sx hap
  omega

/-- 行 1 の最終列バウンド（wip `row1_last_bound` 21016 の私的再証明）:
簡約 `monoT` では `M_{1,j₀} ≥ M_{1,j₁}` または `M_{1,j₀} + 1 = M_{1,j₁}`。
厳密減少ケースでは `j₀ = parent M 0 j₁` が行 1 の親にもなり（谷が中間祖先を殺す）、
`RedCondA` の行 1 が `+1` ステップを強制する。 -/
private theorem row1_last_bound_sx (M : PS) (hR : RTPS M)
    (hmono : monoT M = true) (hL : 1 < Lng M) :
    entry M 1 (Lng M - 1) ≤ entry M 1 (parent M 0 (Lng M - 1)) ∨
      entry M 1 (parent M 0 (Lng M - 1)) + 1 = entry M 1 (Lng M - 1) := by
  by_cases hge : entry M 1 (Lng M - 1) ≤ entry M 1 (parent M 0 (Lng M - 1))
  · exact Or.inl hge
  right
  have hM : TPS M := RTPS_TPS M hR
  have he1lt : entry M 1 (parent M 0 (Lng M - 1)) < entry M 1 (Lng M - 1) := by
    omega
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hparR := nextR_parent0_of_hasParent M (Lng M - 1) hp0
  have hn0 : nextrel0 M (parent M 0 (Lng M - 1)) (Lng M - 1) = true := by
    simpa [nextR] using hparR
  have hjplt : parent M 0 (Lng M - 1) < Lng M - 1 := by
    have hh := hn0
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.1.2
  have hjpL : parent M 0 (Lng M - 1) < Lng M := by omega
  have hle0jp : le0 M (parent M 0 (Lng M - 1)) (Lng M - 1) = true := by
    have := nextR0_leR M (parent M 0 (Lng M - 1)) (Lng M - 1) hparR
    simpa [leR] using this
  -- `jp` は行 1 の親でもある
  have hn1 : nextrel1 M (parent M 0 (Lng M - 1)) (Lng M - 1) = true := by
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range]
    refine ⟨⟨⟨⟨⟨hjpL, by omega⟩, hjplt⟩, he1lt⟩, hle0jp⟩, ?_⟩
    intro x _hx
    by_cases hxgt : parent M 0 (Lng M - 1) < x
    · by_cases hxle : le0 M x (Lng M - 1) = true
      · have hxeq : x = Lng M - 1 :=
          row0_valley_last_sx M hM hmono hL x hxgt hxle
        subst hxeq
        simp
      · simp [hxle]
    · simp [hxgt]
  have hn1R : nextR M 1 (parent M 0 (Lng M - 1)) (Lng M - 1) = true := by
    simpa [nextR] using hn1
  -- 行 1 の親の一意性
  have huniq1 : ∀ k, nextR M 1 k (Lng M - 1) = true
      → k = parent M 0 (Lng M - 1) := by
    intro k hk
    have hnk : nextrel1 M k (Lng M - 1) = true := by simpa [nextR] using hk
    have hh := hnk
    simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range] at hh
    obtain ⟨⟨⟨⟨⟨_hkL, _⟩, hklt⟩, _hke1⟩, hkle0⟩, hall⟩ := hh
    by_contra hkne
    rcases Nat.lt_or_ge k (parent M 0 (Lng M - 1)) with hklt2 | hge2
    · -- k < jp: 行 1 の谷条件を jp で読む
      have h := hall (parent M 0 (Lng M - 1)) hjpL
      rw [hle0jp] at h
      simp only [hklt2, decide_true, Bool.and_true, Bool.not_true,
        Bool.false_or, decide_eq_true_eq] at h
      omega
    · -- jp < k: 谷で k = Lng M - 1、しかし k < Lng M - 1
      have hkgt : parent M 0 (Lng M - 1) < k := by omega
      have := row0_valley_last_sx M hM hmono hL k hkgt hkle0
      omega
  have hp1 : hasParent M 1 (Lng M - 1) = true :=
    (hasParent_iff_unique_fseq M 1 (Lng M - 1)).mpr ⟨_, hn1R, huniq1⟩
  have hpar1 : parent M 1 (Lng M - 1) = parent M 0 (Lng M - 1) :=
    parent_eq_of_unique_fseq M 1 (Lng M - 1) _ hn1R huniq1
  -- RedCondA の行 1
  have hA := (RTPS_condAB M hR).1
  have hstep := RedCondA_apply M hA 1 (Lng M - 1) (by omega) (by omega) hp1
  rw [hpar1] at hstep
  exact hstep

/-! ## Adm0 ガード放電: (II) ∨ (IV)（wip 21105/21198） -/

/-- §8.2 Adm0 ガード放電（Isabelle `m_8_2_condII_or_condIV` 21105）:
`¬(I ∨ III ∨ V)` かつ `¬VI` なら (II) または (IV)。 -/
theorem condII_or_condIV (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hL : 1 < Lng M)
    (hnotA : ¬(transCondI M = true ∨ transCondIII M = true
      ∨ transCondV M = true))
    (hnotVI : transCondVI M = false) :
    transCondII M = true ∨ transCondIV M = true := by
  have hM : TPS M := RTPS_TPS M hR
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hparR := nextR_parent0_of_hasParent M (Lng M - 1) hp0
  have hjplt : parent M 0 (Lng M - 1) < Lng M - 1 := by
    have hh : nextrel0 M (parent M 0 (Lng M - 1)) (Lng M - 1) = true := by
      simpa [nextR] using hparR
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.1.2
  have hbnd := row1_last_bound_sx M hR hmono hL
  -- ¬ adm M jp（さもなくば (I)/(III)/(V)/(VI) が発火）
  have hnadmjp : adm M (parent M 0 (Lng M - 1)) = false := by
    cases hadm : adm M (parent M 0 (Lng M - 1)) with
    | false => rfl
    | true =>
        exfalso
        by_cases he1z : entry M 1 (Lng M - 1) = 0
        · exact hnotA (Or.inl (by
            simp [transCondI, lastIdx, lastParent, he1z, hadm]))
        · have hpos : 0 < entry M 1 (Lng M - 1) := by omega
          by_cases hge : entry M 1 (Lng M - 1)
              ≤ entry M 1 (parent M 0 (Lng M - 1))
          · exact hnotA (Or.inr (Or.inl (by
              simp [transCondIII, lastIdx, lastParent, hpos, hge, hadm])))
          · have heq1 : entry M 1 (parent M 0 (Lng M - 1)) + 1
                = entry M 1 (Lng M - 1) := by
              rcases hbnd with h | h
              · omega
              · exact h
            by_cases hlt : parent M 0 (Lng M - 1) + 1 < Lng M - 1
            · exact hnotA (Or.inr (Or.inr (by
                simp [transCondV, lastIdx, lastParent, hpos, heq1, hlt])))
            · have heqj : parent M 0 (Lng M - 1) + 1 = Lng M - 1 := by omega
              have : transCondVI M = true := by
                simp [transCondVI, lastIdx, lastParent, hpos, heq1, heqj]
              rw [hnotVI] at this
              exact absurd this (by simp)
  -- (II) または (IV)
  by_cases he1z : entry M 1 (Lng M - 1) = 0
  · exact Or.inl (by simp [transCondII, lastIdx, lastParent, he1z, hnadmjp])
  · have hpos : 0 < entry M 1 (Lng M - 1) := by omega
    have hge : entry M 1 (Lng M - 1) ≤ entry M 1 (parent M 0 (Lng M - 1)) := by
      by_contra hnge
      have heq1 : entry M 1 (parent M 0 (Lng M - 1)) + 1
          = entry M 1 (Lng M - 1) := by
        rcases hbnd with h | h
        · omega
        · exact h
      by_cases hlt : parent M 0 (Lng M - 1) + 1 < Lng M - 1
      · exact hnotA (Or.inr (Or.inr (by
          simp [transCondV, lastIdx, lastParent, hpos, heq1, hlt])))
      · have heqj : parent M 0 (Lng M - 1) + 1 = Lng M - 1 := by omega
        have : transCondVI M = true := by
          simp [transCondVI, lastIdx, lastParent, hpos, heq1, heqj]
        rw [hnotVI] at this
        exact absurd this (by simp)
    exact Or.inr (by
      simp [transCondIV, lastIdx, lastParent, hpos, hge, hnadmjp])

/-- §8.2 Adm0 ガード `nadmj0` の無条件化（Isabelle `m_8_2_nadmj0_notAVI` 21198）。 -/
theorem nadmj0_notAVI (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hL : 1 < Lng M)
    (hnotA : ¬(transCondI M = true ∨ transCondIII M = true
      ∨ transCondV M = true))
    (hnotVI : transCondVI M = false) :
    adm M (transJ0 M) = false := by
  rcases condII_or_condIV M hR hmono hL hnotA hnotVI with h | h
  · simp only [transCondII, Bool.and_eq_true, Bool.not_eq_true'] at h
    simpa [transJ0] using h.2
  · simp only [transCondIV, Bool.and_eq_true, Bool.not_eq_true'] at h
    simpa [transJ0] using h.2

/-! ## t₂ ≠ 0（wip 13354 の私的再証明 ＋ 21217） -/

/-- 条件 (II)/(IV) の下で `t₂ = transT2 M ≠ 0`（Isabelle
`m_7_3_t2_nonzero_condIIorIV` 13354 の私的再証明）。(II)/(IV) は
`¬ adm M j₀` を主張するので基点 `j₋₁ = Adm_M(j₀) < j₀ < j₁`、よって
`j₋₁ < Lng (Pred M) - 1` で `c₁` は右端基点形 `D_v 0` になれない
（`Mark_tail_nonzero`）。だが `c₁` は単一 principal `D_v t₂`
（`transC1_single_principal`＋`principal_reconstruct`）で左端頭は
`(Pred M)_{1,j₋₁}`（`Mark_leftend_form_proper`）だから、`t₂ = 0` なら
排除形そのもの — 矛盾。 -/
private theorem t2_nonzero_condIIorIV_sx (M : PS) (hR : RTPS M)
    (hmono : monoT M = true) (hj1 : 0 < transJ1 M) (ht1 : transT1 M ≠ BZero)
    (hcond : transCondII M = true ∨ transCondIV M = true) :
    transT2 M ≠ BZero := by
  intro ht2z
  have hM : TPS M := RTPS_TPS M hR
  have hL : 1 < Lng M := by
    have := hj1
    simp only [transJ1, lastIdx] at this
    omega
  have hpredR : RTPS (Pred M) := RTPS_Pred M hR
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  -- (II)/(IV) はともに ¬ adm M j₀ を主張
  have hnadm : adm M (lastParent M) = false := by
    rcases hcond with h | h
    · simp only [transCondII, Bool.and_eq_true, Bool.not_eq_true'] at h
      exact h.2
    · simp only [transCondIV, Bool.and_eq_true, Bool.not_eq_true'] at h
      exact h.2
  -- j₋₁ < j₀ < j₁
  have hjm1lt : transJm1 M < lastParent M := by
    have := nadm_Adm_lt_sx M (lastParent M) hnadm
    simpa [transJm1, transJ0] using this
  have hparR := nextR_parent0_of_hasParent M (Lng M - 1) hp
  have hjplt : parent M 0 (Lng M - 1) < Lng M - 1 := by
    have hh : nextrel0 M (parent M 0 (Lng M - 1)) (Lng M - 1) = true := by
      simpa [nextR] using hparR
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.1.2
  have hLP : Lng (Pred M) = Lng M - 1 := by
    have hn1 : ¬ Lng M ≤ 1 := by omega
    simp [Pred, hn1]
  have hjm1small : transJm1 M < Lng (Pred M) - 1 := by
    have hlp : lastParent M = parent M 0 (Lng M - 1) := by
      simp [lastParent, lastIdx]
    omega
  -- (Pred M, j₋₁) ∈ Marked
  have hmarked : Marked (Pred M) (transJm1 M) := by
    have := Marked_Pred_Adm M hM hL hp
    simpa [transJm1, transJ0, lastParent, lastIdx] using this
  -- c₁ は単一 principal 項 D_v t₂
  have hpc1 : (PB (transC1 M)).length = 1 :=
    transC1_single_principal M hR hmono hj1 ht1
  have hc1Dpt := principal_reconstruct hpc1
  have ht2z' : bpHeadT (transC1 M) = BZero := ht2z
  rw [ht2z'] at hc1Dpt
  -- 左端形と合成すると排除形 D_{(Pred M)_{1,j₋₁}} 0 になる
  obtain ⟨t, hlf⟩ := Mark_leftend_form_proper (Pred M) (transJm1 M)
    hmarked hpredR hjm1small
  have hc1mark : transC1 M = Mark (Pred M) (transJm1 M) := rfl
  have hcomb : Dprin (bpHeadV (transC1 M)) BZero
      = Dprin ((entry (Pred M) 1 (transJm1 M) : ℕ∞)) t := by
    rw [← hc1Dpt, hc1mark, hlf]
  have hteq : BZero = t := by
    simpa [Dprin] using (congrArg (fun c => bpHeadT c) hcomb)
  have hform : Mark (Pred M) (transJm1 M)
      = Dprin ((entry (Pred M) 1 (transJm1 M) : ℕ∞)) BZero := by
    rw [hlf, ← hteq]
  exact Mark_tail_nonzero (Pred M) (transJm1 M) hmarked hpredR hjm1small hform

/-- §8.2 Adm0 ガード `t2ne` の無条件化（Isabelle `m_8_2_t2ne_notAVI` 21217）。 -/
theorem t2ne_notAVI (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hL : 1 < Lng M) (hj1gt : 1 < Lng M - 1)
    (hnotA : ¬(transCondI M = true ∨ transCondIII M = true
      ∨ transCondV M = true))
    (hnotVI : transCondVI M = false) :
    transT2 M ≠ BZero := by
  have hM : TPS M := RTPS_TPS M hR
  have hj1 : 0 < transJ1 M := by
    simp only [transJ1, lastIdx]
    omega
  -- t₁ = Trans (Pred M) ≠ 0（`Pred M` は長さ ≥ 2 で零項でない）
  have hLP : Lng (Pred M) = Lng M - 1 := by
    have hn1 : ¬ Lng M ≤ 1 := by omega
    simp [Pred, hn1]
  have hPT : TPS (Pred M) := by
    intro hnil
    have : Lng (Pred M) = 0 := by simp [hnil]
    omega
  have hzP : zeroT (Pred M) = false := by
    have hlen : Lng (Pred M) ≠ 1 := by omega
    simp only [zeroT, Bool.and_eq_false_iff]
    left
    simpa using hlen
  have ht1 : transT1 M ≠ BZero := by
    intro h
    have hz := (Trans_preserves_zeroT (Pred M) hPT).mpr
      (by simpa [transT1] using h)
    rw [hzP] at hz
    exact absurd hz (by simp)
  have hcond := condII_or_condIV M hR hmono hL hnotA hnotVI
  exact t2_nonzero_condIIorIV_sx M hR hmono hj1 ht1 hcond

/-! ## clause-(2) ガード e0gt、(IV) 部分ケース（wip 21282） -/

/-- §8.2 Adm0 clause-(2) ガード `e0gt`、(IV) 部分ケース
（Isabelle `m_8_2_e0gt_condIV` 21282）。行 0 の親ステップ（`RedCondA`）と
行 0/行 1 支配（`reduced_coeff`）から
`M_{0,j₁} = M_{0,j₀} + 1 ≥ M_{1,j₀} + 1 ≥ M_{1,j₁} + 1 > M_{1,j₁}`。 -/
theorem e0gt_condIV (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hL : 1 < Lng M) (hcond : transCondIV M = true) :
    entry M 1 (Lng M - 1) < entry M 0 (Lng M - 1) := by
  have hM : TPS M := RTPS_TPS M hR
  -- (IV): M_{1,j₀} ≥ M_{1,j₁}
  have hIV := hcond
  simp only [transCondIV, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at hIV
  have hge1 : entry M 1 (Lng M - 1)
      ≤ entry M 1 (parent M 0 (Lng M - 1)) := by
    have := hIV.1.2
    simpa [lastIdx, lastParent] using this
  -- 行 0 の親ステップ
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hparR := nextR_parent0_of_hasParent M (Lng M - 1) hp0
  have hjplt : parent M 0 (Lng M - 1) < Lng M - 1 := by
    have hh : nextrel0 M (parent M 0 (Lng M - 1)) (Lng M - 1) = true := by
      simpa [nextR] using hparR
    simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hh
    exact hh.1.1.2
  have hA := (RTPS_condAB M hR).1
  have hstep : entry M 0 (parent M 0 (Lng M - 1)) + 1
      = entry M 0 (Lng M - 1) :=
    RedCondA_apply M hA 0 (Lng M - 1) (by omega) (by omega) hp0
  -- 行 0/行 1 支配
  have hdom : entry M 1 (parent M 0 (Lng M - 1))
      ≤ entry M 0 (parent M 0 (Lng M - 1)) :=
    reduced_coeff M hR (parent M 0 (Lng M - 1)) (by omega)
  omega

/-! ## 公理監査 -/

#print axioms parent_le_TrMax_Adm0
#print axioms j1eq_Adm0
#print axioms j0eq_Adm0
#print axioms gA_Adm0
#print axioms notVI_Adm0
#print axioms condII_or_condIV
#print axioms nadmj0_notAVI
#print axioms t2ne_notAVI
#print axioms gB_condIorIII
#print axioms e0gt_e1zero
#print axioms e0gt_condIV

end PSS
