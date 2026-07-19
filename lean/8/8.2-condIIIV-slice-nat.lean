import «8».«8.2-condIIIV-geometry»
import «8».«8.2-condIIIV-headeq0»
import «8».«8.2-subexpr-adm0-cores»
import «6».«6.3-marked-slice»
import «6».«6.8-standard-slice-Br-descending»

/-!
# §8.2 条件(II)/(IV) STEP スロット: 終切片 surgery データの自然性 (slice naturality)

- Isabelle: `tsx_c1_eq` (isabelle/layerB/pss_wip.thy 103771) と
  `tsx_c2_eq` (103971)。
- 目標: `8.2-condIIIV-assembly` の残差 `TspinGeomIH_as` の
  `transC1/transC2`-自然性 conjunct を **VERBATIM** に供給する 2 本の公開定理:
  `transC1 Mp = transC1 N`, `transC2 Mp = transC2 N`
  （`Mp = seg N j₀' (Lng N-1)`, `j₀' = (Joints N).getD ((Br N).length-1) 0`）を
  STEP 体制仮説 `VE34Reg4D N` ＋ `VEj1p N < Lng N - 1` の下で証明する。
  sibling agent（assembly）が exact statement で消費する。

## 証明構造（Isabelle 忠実移植）

`tsx_c1_eq`: 両ホスト `N` / `Mp` の `transC1` は accessor 展開で
`Mark (Pred ·) (Adm · (parent · 0 (last)))` に落ちる。終切片 `Mp` の parent/Adm は
ホストの shift（`parent0_terminal_seg_sn` / `admof_slice`）。`Adm N jp < Lng N - 2`
（内部）と `= Lng N - 2`（境界）で場合分け:
- 内部: 両 Mark は同じ `Pred N` の部分切片の `Trans`（`Mark_Trans_repr`）で、
  `Pred Mp = seg (Pred N) j₀' (Lng(Pred N)-1)`（`hqx_Pred_seg_hq`+`seg_Pred_eq`）と
  `seg_of_seg_68` で切片が一致。
- 境界: 両 Mark は右端 principal `Dprin (entry · 1 jp) 0_B`
  （`Mark_Pred_terminal_boundary`）で、`entry_seg` で entry が一致。

`tsx_c2_eq`: `transC2_congr_74_sn`（`transC1` 一致＋entry/adm/cond 自然性から
`transC2` 一致）へ、`entry_seg` による entry 転送・`adm_slice` による adm 転送・
`Bool.eq_iff_iff` による cond 転送を流し込む（`Mark_Trans_repr_mono_interior` の
cond-transport ブロックと同型）。

## 数値検証

STEP witness `w = (0,0)(1,1)(2,2)(2,1)(3,1)`（assembly の `w1_as`）で
`transC1/transC2` 自然性・`VE34Reg4D`・`VEj1p < Lng-1` を `#guard` で確認。

- 訂正: なし。
- 状態: sorry 0、公理 `[propext, Classical.choice, Quot.sound]` のみ。
- Private suffix: `_sn`。
-/

namespace PSS

/-! ## 複製した private helper（house pattern: `_sn` 接尾辞） -/

/-- `7.4-Mark-Trans-repr` の private `parent0_terminal_seg` の複製。終切片の row-0 parent は
ホストの parent の shift。 -/
private theorem parent0_terminal_seg_sn (M : PS) (m j₁ : ℕ)
    (hj₁ : j₁ < Lng M) (hmp : m ≤ parent M 0 j₁)
    (hp : hasParent M 0 j₁ = true) :
    hasParent (seg M m j₁) 0 (j₁ - m) = true ∧
      parent (seg M m j₁) 0 (j₁ - m) = parent M 0 j₁ - m := by
  let p := parent M 0 j₁
  let pl := p - m
  let jl := j₁ - m
  have hnextM : nextR M 0 p j₁ = true := by
    simpa [p] using hasParent_next_fseq M 0 j₁ hp
  have hpLt : p < j₁ := by
    simpa [p] using parent_lt_of_hasParent M 0 j₁ hp
  have hmpl : m + pl = p := by simp [pl, p, hmp]
  have hmjl : m + jl = j₁ := by simp [jl]; omega
  have hpljl : pl < jl := by omega
  have hjlS : jl < Lng (seg M m j₁) := by simp [jl]; omega
  have hplS : pl < Lng (seg M m j₁) := hpljl.trans hjlS
  have hnextS : nextR (seg M m j₁) 0 pl jl = true := by
    rw [nextR_seg_adm M m j₁ 0 pl jl (by omega) hj₁ hplS hjlS]
    simpa [hmpl, hmjl] using hnextM
  have huniq : ∀ q, nextR (seg M m j₁) 0 q jl = true → q = pl := by
    intro q hq
    exact row0_parent_unique (seg M m j₁) q pl jl hq hnextS
  have hpS : hasParent (seg M m j₁) 0 jl = true :=
    (hasParent_iff_unique_fseq (seg M m j₁) 0 jl).mpr
      ⟨pl, hnextS, huniq⟩
  have hparS : parent (seg M m j₁) 0 jl = pl :=
    parent_eq_of_unique_fseq (seg M m j₁) 0 jl pl hnextS huniq
  simpa [jl, pl, p] using And.intro hpS hparS

/-- `7.4-Mark-Trans-repr` の private `transC2_congr_74` の複製。`transC1` 一致＋entry/adm/cond
自然性から `transC2` 一致。 -/
private theorem transC2_congr_74_sn (M N : PS)
    (hc1 : transC1 M = transC1 N)
    (he0 : entry N 1 (lastParent N) = entry M 1 (lastParent M))
    (he1 : entry N 1 (lastIdx N) = entry M 1 (lastIdx M))
    (hI : transCondI N = transCondI M)
    (hIII : transCondIII N = transCondIII M)
    (hV : transCondV N = transCondV M)
    (hVI : transCondVI N = transCondVI M) :
    transC2 M = transC2 N := by
  have hv : transV N = transV M := by simp [transV, hc1]
  have ht2 : transT2 N = transT2 M := by simp [transT2, hc1]
  unfold transC2 transC2Core
  simp only [hv, ht2, he0, he1, hI, hIII, hV, hVI]

/-- `8.2-subexpr-adm0-ctx` の private `nadm_Adm_lt_sx` の複製。 -/
private theorem nadm_Adm_lt_sn (M : PS) (j : ℕ) (hna : adm M j = false) :
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

/-! ## (1) `transC1` 自然性（Isabelle `tsx_c1_eq` 103771） -/

/-- **終切片 surgery データ `c₁` の自然性** `transC1 Mp = transC1 N`。 -/
theorem tsx_c1_eq_sn (N : PS) (regD : VE34Reg4D N) (hlt : VEj1p N < Lng N - 1) :
    transC1 (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) = transC1 N := by
  -- 終切片 regime facts（set より前に取り出す）
  have hMpready := stepTerminalReady_holds N regD hlt
  obtain ⟨hMpR, hMpMono, _hMpBrne, hMpLen⟩ := hMpready
  obtain ⟨⟨⟨⟨hR, hmono, hBrne⟩, _hguard⟩, hj0pos, hj0ltTr⟩, _hdesc⟩ := regD
  set j0 := (Joints N).getD ((Br N).length - 1) 0 with hj0def
  have hM : TPS N := RTPS_TPS N hR
  -- 幾何: TrMax < VEj1p, TrMax < Lng-1, 1 < Lng, jp geometry
  have hBrpos : 0 < (Br N).length := List.length_pos_of_ne_nil hBrne
  have hJ : (Br N).length - 1 < (Br N).length := by omega
  have hFN := FirstNodes_TrMax_Joints N ((Br N).length - 1) hM hmono hJ
  have htrj1p : TrMax N < VEj1p N := hFN.2
  have htrlt : TrMax N < Lng N - 1 := by omega
  have hL1 : 1 < Lng N := by omega
  have hj1gt : 1 < Lng N - 1 := by omega
  have hpN : hasParent N 0 (Lng N - 1) = true :=
    mono_hasParent_row0 N hM hmono (Lng N - 1) (by omega) (by omega)
  have hjplt : parent N 0 (Lng N - 1) < Lng N - 1 :=
    parent_lt_of_hasParent N 0 (Lng N - 1) hpN
  have hparR : nextR N 0 (parent N 0 (Lng N - 1)) (Lng N - 1) = true :=
    hasParent_next_fseq N 0 (Lng N - 1) hpN
  have htrjp : TrMax N < parent N 0 (Lng N - 1) := by
    by_contra hcon
    have hparTr : parent N 0 (Lng N - 1) ≤ TrMax N := by omega
    have hlb := lastbranch_eq_j1 N hR hmono hBrne hj1gt hparTr
    have : VEj1p N = Lng N - 1 := hlb
    omega
  have hj0jp : j0 < parent N 0 (Lng N - 1) := by omega
  -- Adm 系
  have hadmTr : adm N (TrMax N) = true := by
    have htb : TrMax N ≤ Lng N - 1 := TrMax_bound N hM
    have hno : ¬ Lng N < TrMax N := by omega
    have hstop := TrMax_stop_uncond N hM
    simp [adm, nadm, hstop, hno]
  have hj0A : j0 < Adm N (parent N 0 (Lng N - 1)) := by
    have hle := Adm_max N (TrMax N) (parent N 0 (Lng N - 1)) hadmTr (by omega)
    omega
  -- 終切片 length / transport
  have hLngMp : Lng (seg N j0 (Lng N - 1)) = Lng N - j0 := by
    rw [length_seg]; omega
  have hj02 : j0 + 2 < Lng N - 1 := by omega
  have hLMp : 1 < Lng (seg N j0 (Lng N - 1)) := by omega
  have hMpT : TPS (seg N j0 (Lng N - 1)) := RTPS_TPS _ hMpR
  have hidxeq : Lng (seg N j0 (Lng N - 1)) - 1 = (Lng N - 1) - j0 := by
    rw [hLngMp]; omega
  have hparMp : parent (seg N j0 (Lng N - 1)) 0 (Lng (seg N j0 (Lng N - 1)) - 1)
      = parent N 0 (Lng N - 1) - j0 := by
    rw [hidxeq]
    exact (parent0_terminal_seg_sn N j0 (Lng N - 1) (by omega) hj0jp.le hpN).2
  have hAdmMp : Adm (seg N j0 (Lng N - 1)) (parent N 0 (Lng N - 1) - j0)
      = Adm N (parent N 0 (Lng N - 1)) - j0 :=
    admof_slice N j0 (parent N 0 (Lng N - 1)) (Lng N - 1) hM hj0A.le hjplt (le_refl _)
  have hLPred : Lng (Pred N) = Lng N - 1 := length_Pred N hL1
  -- accessor 展開。`Mark` の fuel を defeq で叩くと重いので、引数のみ書き換える
  -- （`transC1 · ≡ Mark (Pred ·) (transJm1 ·)`、`transJm1 ·` は Adm/parent へ安価に defeq）。
  have htjm1N : transJm1 N = Adm N (parent N 0 (Lng N - 1)) := rfl
  have c1N : transC1 N = Mark (Pred N) (Adm N (parent N 0 (Lng N - 1))) := by
    show Mark (Pred N) (transJm1 N) = Mark (Pred N) (Adm N (parent N 0 (Lng N - 1)))
    rw [htjm1N]
  have htjm1Mp : transJm1 (seg N j0 (Lng N - 1))
      = Adm (seg N j0 (Lng N - 1))
          (parent (seg N j0 (Lng N - 1)) 0 (Lng (seg N j0 (Lng N - 1)) - 1)) := rfl
  have c1Mp : transC1 (seg N j0 (Lng N - 1))
      = Mark (Pred (seg N j0 (Lng N - 1))) (Adm N (parent N 0 (Lng N - 1)) - j0) := by
    show Mark (Pred (seg N j0 (Lng N - 1))) (transJm1 (seg N j0 (Lng N - 1)))
      = Mark (Pred (seg N j0 (Lng N - 1))) (Adm N (parent N 0 (Lng N - 1)) - j0)
    rw [htjm1Mp, hparMp, hAdmMp]
  by_cases hcase : Adm N (parent N 0 (Lng N - 1)) < Lng N - 2
  · -- 内部ケース
    have hPredNR : RTPS (Pred N) := RTPS_Pred N hR
    have hPredMpR : RTPS (Pred (seg N j0 (Lng N - 1))) := RTPS_Pred _ hMpR
    have mkdN : Marked (Pred N) (Adm N (parent N 0 (Lng N - 1))) :=
      Marked_Pred_Adm N hM hL1 hpN
    have hsideN : Adm N (parent N 0 (Lng N - 1)) < Lng (Pred N) - 1 := by
      rw [hLPred]; omega
    have reprN : Mark (Pred N) (Adm N (parent N 0 (Lng N - 1)))
        = Trans (seg (Pred N) (Adm N (parent N 0 (Lng N - 1))) (Lng (Pred N) - 1)) :=
      Mark_Trans_repr (Pred N) (Adm N (parent N 0 (Lng N - 1))) mkdN hPredNR hsideN
    have hpMp : hasParent (seg N j0 (Lng N - 1)) 0 (Lng (seg N j0 (Lng N - 1)) - 1) = true :=
      mono_hasParent_row0 (seg N j0 (Lng N - 1)) hMpT hMpMono
        (Lng (seg N j0 (Lng N - 1)) - 1) (by omega) (by omega)
    have mkdMp : Marked (Pred (seg N j0 (Lng N - 1))) (Adm N (parent N 0 (Lng N - 1)) - j0) := by
      have h := Marked_Pred_Adm (seg N j0 (Lng N - 1)) hMpT hLMp hpMp
      rw [hparMp, hAdmMp] at h
      exact h
    have hLPredMp : Lng (Pred (seg N j0 (Lng N - 1))) = Lng (seg N j0 (Lng N - 1)) - 1 :=
      length_Pred _ hLMp
    have hsideMp : Adm N (parent N 0 (Lng N - 1)) - j0
        < Lng (Pred (seg N j0 (Lng N - 1))) - 1 := by
      rw [hLPredMp, hLngMp]; omega
    have reprMp : Mark (Pred (seg N j0 (Lng N - 1))) (Adm N (parent N 0 (Lng N - 1)) - j0)
        = Trans (seg (Pred (seg N j0 (Lng N - 1))) (Adm N (parent N 0 (Lng N - 1)) - j0)
            (Lng (Pred (seg N j0 (Lng N - 1))) - 1)) :=
      Mark_Trans_repr (Pred (seg N j0 (Lng N - 1))) (Adm N (parent N 0 (Lng N - 1)) - j0)
        mkdMp hPredMpR hsideMp
    have predMp : Pred (seg N j0 (Lng N - 1)) = seg (Pred N) j0 (Lng (Pred N) - 1) := by
      have e1 : Lng (Pred N) - 1 = Lng N - 2 := by omega
      rw [e1, hqx_Pred_seg_hq N j0 hL1 (by omega),
        ← seg_Pred_eq N j0 (Lng N - 2) hL1 (by omega) (by omega)]
    have segseg : seg (Pred (seg N j0 (Lng N - 1))) (Adm N (parent N 0 (Lng N - 1)) - j0)
          (Lng (Pred (seg N j0 (Lng N - 1))) - 1)
        = seg (Pred N) (Adm N (parent N 0 (Lng N - 1))) (Lng (Pred N) - 1) := by
      have hd : Lng (Pred (seg N j0 (Lng N - 1))) - 1 = Lng N - j0 - 2 := by
        rw [hLPredMp, hLngMp]; omega
      have ea : j0 + (Adm N (parent N 0 (Lng N - 1)) - j0)
          = Adm N (parent N 0 (Lng N - 1)) := by omega
      have eb : j0 + (Lng N - j0 - 2) = Lng (Pred N) - 1 := by omega
      rw [hd, predMp,
        seg_of_seg_68 (Pred N) j0 (Lng (Pred N) - 1) (Adm N (parent N 0 (Lng N - 1)) - j0)
          (Lng N - j0 - 2) (by omega) (by omega), ea, eb]
    -- 組立は proof-term 連鎖（`Mark`/`Trans` の fuel を defeq で叩かない）
    calc transC1 (seg N j0 (Lng N - 1))
        = Mark (Pred (seg N j0 (Lng N - 1))) (Adm N (parent N 0 (Lng N - 1)) - j0) := c1Mp
      _ = Trans (seg (Pred (seg N j0 (Lng N - 1))) (Adm N (parent N 0 (Lng N - 1)) - j0)
            (Lng (Pred (seg N j0 (Lng N - 1))) - 1)) := reprMp
      _ = Trans (seg (Pred N) (Adm N (parent N 0 (Lng N - 1))) (Lng (Pred N) - 1)) :=
            congrArg Trans segseg
      _ = Mark (Pred N) (Adm N (parent N 0 (Lng N - 1))) := reprN.symm
      _ = transC1 N := c1N.symm
  · -- 境界ケース
    have hAle : Adm N (parent N 0 (Lng N - 1)) ≤ parent N 0 (Lng N - 1) := Adm_le N _
    have haeq : Adm N (parent N 0 (Lng N - 1)) = Lng N - 2 := by omega
    have hjpeq : parent N 0 (Lng N - 1) = Lng N - 2 := by omega
    have hAeqJp : Adm N (parent N 0 (Lng N - 1)) = parent N 0 (Lng N - 1) := by omega
    have admjp : adm N (parent N 0 (Lng N - 1)) = true := by
      by_contra hcon
      have hf : adm N (parent N 0 (Lng N - 1)) = false := by
        simpa using hcon
      have hlt2 := nadm_Adm_lt_sn N (parent N 0 (Lng N - 1)) hf
      omega
    have leN : leR N 0 (parent N 0 (Lng N - 1)) (Lng N - 1) = true :=
      nextR0_leR N (parent N 0 (Lng N - 1)) (Lng N - 1) hparR
    have mkdN2 : Marked N (parent N 0 (Lng N - 1)) := ⟨hM, admjp, leN⟩
    have bndN : Mark (Pred N) (parent N 0 (Lng N - 1))
        = Dprin (entry N 1 (parent N 0 (Lng N - 1)) : ℕ∞) BZero :=
      Mark_Pred_terminal_boundary N (parent N 0 (Lng N - 1)) mkdN2 hR hjpeq hj1gt
    have mkdMp2 : Marked (seg N j0 (Lng N - 1)) (parent N 0 (Lng N - 1) - j0) :=
      marked_slice N (parent N 0 (Lng N - 1)) j0 (Lng N - 1) mkdN2 hj0jp.le hjplt.le (le_refl _)
    have jpMpeq : parent N 0 (Lng N - 1) - j0 = Lng (seg N j0 (Lng N - 1)) - 2 := by
      rw [hLngMp]; omega
    have bndMp : Mark (Pred (seg N j0 (Lng N - 1))) (parent N 0 (Lng N - 1) - j0)
        = Dprin (entry (seg N j0 (Lng N - 1)) 1 (parent N 0 (Lng N - 1) - j0) : ℕ∞) BZero :=
      Mark_Pred_terminal_boundary (seg N j0 (Lng N - 1)) (parent N 0 (Lng N - 1) - j0)
        mkdMp2 hMpR jpMpeq hMpLen
    have hlt3 : parent N 0 (Lng N - 1) - j0 < Lng (seg N j0 (Lng N - 1)) := by
      rw [hLngMp]; omega
    have eMp : entry (seg N j0 (Lng N - 1)) 1 (parent N 0 (Lng N - 1) - j0)
        = entry N 1 (parent N 0 (Lng N - 1)) := by
      rw [entry_seg N j0 (Lng N - 1) 1 (parent N 0 (Lng N - 1) - j0) hlt3]
      have hsum : j0 + (parent N 0 (Lng N - 1) - j0) = parent N 0 (Lng N - 1) := by omega
      rw [hsum]
    calc transC1 (seg N j0 (Lng N - 1))
        = Mark (Pred (seg N j0 (Lng N - 1))) (Adm N (parent N 0 (Lng N - 1)) - j0) := c1Mp
      _ = Mark (Pred (seg N j0 (Lng N - 1))) (parent N 0 (Lng N - 1) - j0) := by rw [hAeqJp]
      _ = Dprin (entry (seg N j0 (Lng N - 1)) 1 (parent N 0 (Lng N - 1) - j0) : ℕ∞) BZero := bndMp
      _ = Dprin (entry N 1 (parent N 0 (Lng N - 1)) : ℕ∞) BZero := by rw [eMp]
      _ = Mark (Pred N) (parent N 0 (Lng N - 1)) := bndN.symm
      _ = Mark (Pred N) (Adm N (parent N 0 (Lng N - 1))) := by rw [hAeqJp]
      _ = transC1 N := c1N.symm

/-! ## (2) `transC2` 自然性（Isabelle `tsx_c2_eq` 103971） -/

/-- **終切片 surgery データ `c₂` の自然性** `transC2 Mp = transC2 N`。`tsx_c1_eq_sn`（`c₁`
一致）＋entry/adm/cond 自然性を `transC2_congr_74_sn` に流し込む。 -/
theorem tsx_c2_eq_sn (N : PS) (regD : VE34Reg4D N) (hlt : VEj1p N < Lng N - 1) :
    transC2 (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) = transC2 N := by
  have hc1 := tsx_c1_eq_sn N regD hlt
  obtain ⟨⟨⟨⟨hR, hmono, hBrne⟩, _hguard⟩, hj0pos, hj0ltTr⟩, _hdesc⟩ := regD
  set j0 := (Joints N).getD ((Br N).length - 1) 0 with hj0def
  have hM : TPS N := RTPS_TPS N hR
  have hBrpos : 0 < (Br N).length := List.length_pos_of_ne_nil hBrne
  have hJ : (Br N).length - 1 < (Br N).length := by omega
  have hFN := FirstNodes_TrMax_Joints N ((Br N).length - 1) hM hmono hJ
  have htrj1p : TrMax N < VEj1p N := hFN.2
  have htrlt : TrMax N < Lng N - 1 := by omega
  have hL1 : 1 < Lng N := by omega
  have hj1gt : 1 < Lng N - 1 := by omega
  have hpN : hasParent N 0 (Lng N - 1) = true :=
    mono_hasParent_row0 N hM hmono (Lng N - 1) (by omega) (by omega)
  have hjplt : parent N 0 (Lng N - 1) < Lng N - 1 :=
    parent_lt_of_hasParent N 0 (Lng N - 1) hpN
  have htrjp : TrMax N < parent N 0 (Lng N - 1) := by
    by_contra hcon
    have hparTr : parent N 0 (Lng N - 1) ≤ TrMax N := by omega
    have hlb := lastbranch_eq_j1 N hR hmono hBrne hj1gt hparTr
    have : VEj1p N = Lng N - 1 := hlb
    omega
  have hj0jp : j0 < parent N 0 (Lng N - 1) := by omega
  have hLngMp : Lng (seg N j0 (Lng N - 1)) = Lng N - j0 := by rw [length_seg]; omega
  have hj02 : j0 + 2 < Lng N - 1 := by omega
  have hidxeq : Lng (seg N j0 (Lng N - 1)) - 1 = (Lng N - 1) - j0 := by rw [hLngMp]; omega
  have hparMp : parent (seg N j0 (Lng N - 1)) 0 (Lng (seg N j0 (Lng N - 1)) - 1)
      = parent N 0 (Lng N - 1) - j0 := by
    rw [hidxeq]
    exact (parent0_terminal_seg_sn N j0 (Lng N - 1) (by omega) hj0jp.le hpN).2
  -- adm 転送: `adm Mp (jp - j₀') = adm N jp`（`adm_slice`、端点 escape は j₀'<jp<Lng-1 で消える）
  have hadmEq : adm (seg N j0 (Lng N - 1)) (parent N 0 (Lng N - 1) - j0)
      = adm N (parent N 0 (Lng N - 1)) := by
    have hiff := adm_slice N j0 (parent N 0 (Lng N - 1)) (Lng N - 1) hM hj0jp.le hjplt.le (le_refl _)
    have hj0ne : j0 ≠ parent N 0 (Lng N - 1) := by omega
    have hjpne : parent N 0 (Lng N - 1) ≠ Lng N - 1 := by omega
    cases hb : adm N (parent N 0 (Lng N - 1)) with
    | true => exact hiff.mp (Or.inl hb)
    | false =>
      cases hc : adm (seg N j0 (Lng N - 1)) (parent N 0 (Lng N - 1) - j0) with
      | true =>
        rcases hiff.mpr hc with h1 | h2 | h3
        · rw [hb] at h1; exact absurd h1 (by simp)
        · exact absurd h2 hj0ne
        · exact absurd h3 hjpne
      | false => rfl
  -- last* を算術形へ（`omega` が positional guard を等値化できるように）
  have hLastIdxN : lastIdx N = Lng N - 1 := rfl
  have hLastParN : lastParent N = parent N 0 (Lng N - 1) := rfl
  have hLastIdxMp : lastIdx (seg N j0 (Lng N - 1)) = Lng N - 1 - j0 := by
    simp only [lastIdx]; rw [hLngMp]; omega
  have hLastParMp : lastParent (seg N j0 (Lng N - 1)) = parent N 0 (Lng N - 1) - j0 := by
    simp only [lastParent, lastIdx]; exact hparMp
  -- entry / adm / positional 転送
  have heLast : entry N 1 (lastIdx N)
      = entry (seg N j0 (Lng N - 1)) 1 (lastIdx (seg N j0 (Lng N - 1))) := by
    rw [hLastIdxN, hLastIdxMp,
      entry_seg N j0 (Lng N - 1) 1 (Lng N - 1 - j0) (by rw [hLngMp]; omega)]
    have hsum : j0 + (Lng N - 1 - j0) = Lng N - 1 := by omega
    rw [hsum]
  have hePar : entry N 1 (lastParent N)
      = entry (seg N j0 (Lng N - 1)) 1 (lastParent (seg N j0 (Lng N - 1))) := by
    rw [hLastParN, hLastParMp,
      entry_seg N j0 (Lng N - 1) 1 (parent N 0 (Lng N - 1) - j0) (by rw [hLngMp]; omega)]
    have hsum : j0 + (parent N 0 (Lng N - 1) - j0) = parent N 0 (Lng N - 1) := by omega
    rw [hsum]
  have hAdm : adm N (lastParent N)
      = adm (seg N j0 (Lng N - 1)) (lastParent (seg N j0 (Lng N - 1))) := by
    rw [hLastParN, hLastParMp]; exact hadmEq.symm
  have hltAr : (lastParent N + 1 < lastIdx N)
      ↔ (lastParent (seg N j0 (Lng N - 1)) + 1 < lastIdx (seg N j0 (Lng N - 1))) := by
    rw [hLastParN, hLastIdxN, hLastParMp, hLastIdxMp]; omega
  have heqAr : (lastParent N + 1 = lastIdx N)
      ↔ (lastParent (seg N j0 (Lng N - 1)) + 1 = lastIdx (seg N j0 (Lng N - 1))) := by
    rw [hLastParN, hLastIdxN, hLastParMp, hLastIdxMp]; omega
  -- cond 転送（`Mark_Trans_repr_mono_interior` の cond-transport ブロックと同型）
  have hI : transCondI N = transCondI (seg N j0 (Lng N - 1)) := by
    apply Bool.eq_iff_iff.mpr
    simp [transCondI, heLast, hAdm]
  have hIII : transCondIII N = transCondIII (seg N j0 (Lng N - 1)) := by
    apply Bool.eq_iff_iff.mpr
    simp [transCondIII, heLast, hePar, hAdm]
  have hV : transCondV N = transCondV (seg N j0 (Lng N - 1)) := by
    apply Bool.eq_iff_iff.mpr
    simp [transCondV, heLast, hePar, hltAr]
  have hVI : transCondVI N = transCondVI (seg N j0 (Lng N - 1)) := by
    apply Bool.eq_iff_iff.mpr
    simp [transCondVI, heLast, hePar, heqAr]
  exact transC2_congr_74_sn (seg N j0 (Lng N - 1)) N hc1 hePar heLast hI hIII hV hVI

/-! ## 転記の数値検証（STEP witness `w = (0,0)(1,1)(2,2)(2,1)(3,1)`、assembly の `w1_as`） -/

private def w1_sn : PS := [(0,0),(1,1),(2,2),(2,1),(3,1)]

-- STEP 体制であること（残差が空虚でない）。
#guard decide (VE34Reg4D w1_sn) = true
#guard (VEj1p w1_sn < Lng w1_sn - 1) = true

-- `c₁` の自然性（実 `Trans` で成立）。
#guard (transC1 (seg w1_sn ((Joints w1_sn).getD ((Br w1_sn).length - 1) 0) (Lng w1_sn - 1))
  == transC1 w1_sn) = true

-- `c₂` の自然性（実 `Trans` で成立）。
#guard (transC2 (seg w1_sn ((Joints w1_sn).getD ((Br w1_sn).length - 1) 0) (Lng w1_sn - 1))
  == transC2 w1_sn) = true

#print axioms tsx_c1_eq_sn
#print axioms tsx_c2_eq_sn

end PSS
