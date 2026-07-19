import «8».«8.2-condIIIV-headeq0»

/-!
# §8.2 条件(II)/(IV) VE34 — **HEADEQ0 の討伐**（`HEADEQ0All_hq` を無条件で閉じる）

- 原文: `tmp/content.md` L1624 付近（命題「条件(II)か(IV)の下での終切片と `Trans` の関係」）。
  本ファイルは `8.2-condIIIV-headeq0` で名前付き Prop として露出された残差
  `HEADEQ0All_hq`（Isabelle `hqx_HEADEQ0`, `layerB/pss_wip.thy:108441`, 240 行, 2 ケース）を
  逐語移植で討伐する。これが閉じると（`BgxVE34RedHE0_hq` と合わせて）`hqx_VE34_of_DT_hq`、
  ひいては §8.2 条件(II)/(IV) の VE34 が無条件化する。

## Isabelle 証明の構造（`hqx_HEADEQ0`）

BASE run-base ホスト（`VE34Reg4D N`, `VEj1p N = Lng N - 1`, `LastStep N = Lng(Br N)-1`）
について、終切片 `seg N j₀ (Lng N-1)`（`j₀ = Joints N ! (Lng(Br N)-1)`）の `Pred` の deep head が
host `N` の `Pred` の deep head に等しいことを、`Pred N` の枝の有無で場合分けして示す：

```
[trunk corner]  Br (Pred N) = []:  Pred N も seg も対角列 diagSeq（同じ右端 e+TrMax N）ゆえ
    m_8_1_diagSeq_Trans（Lean: diagSeq_Trans）の閉形式で両辺の bpHeadT が一致。
[branching]     Br (Pred N) ≠ []:  regime VEReg j₀ (Pred N) を組み（headedge/descending/
    LastStep 最小性で分岐の非許容性を確定）、移植済 vcx_VE_all を適用。
```

## 移植したブリック（本ファイル内、private suffix `_h0`）

- `diagSeq_getElem_h0`（Isabelle `diagSeq_nth`）／`descendingB_row0_h0`（`descending_def` の row-0 単調）
- `lastBr_singleton_h0` / `BrLen_Pred_h0`（Isabelle `bfx_BrLen_Pred_base`）
- `a1_FN_hasParent_h0` / `a1_FN_lt_h0`（`a1_FN_lt`）
- `headEdge_h0`（Isabelle `bgx_headedge`：`entry N 0 (Joints N!J) + 1 = entry N 0 (FirstNodes N!J)`）
- `gtN_h0`（Isabelle `bfx_gtN`：最終枝頭は狭義ガード）
- `LastStep_find_min_h0`（Isabelle `vgx_LastStep_elsecase` の全域版最小性）

その他の依存（`hqx_Pred_seg_hq`, `TrMax_Pred_nontrunk`, `Joints_Pred_core`,
`FirstNodes_Pred_core`, `FirstNodes_TrMax_Joints`, `entry_FirstNodes_eq_component_mr`,
`trunk_entries_offset`, `reduced_coeff`, `RTPS_mono_head_eq`, `seg_Pred_eq`, `diagSeq_Trans`,
`descending_Br_Pred`, `vcx_VE_all`, …）は移植済で `8.2-condIIIV-headeq0` から推移的に可視。

- 訂正: なし（Isabelle 済補題の逐語移植）。
- 状態: ✅（sorry 0, rc=0）。`HEADEQ0All_hq` を無条件討伐。
- 依存 module: `8.2-condIIIV-headeq0`。
- Private suffix: `_h0`。
-/

namespace PSS

/-! ## 移植ブリック -/

/-- Isabelle `diagSeq_nth`: `diagSeq u v` の `i` 番目は対角ペア `(u+i, u+i)`。 -/
private theorem diagSeq_getElem_h0 (u v i : ℕ) (hi : i < Lng (diagSeq u v)) :
    (diagSeq u v)[i] = (u + i, u + i) := by
  simp [diagSeq, List.getElem_map, List.getElem_range']

/-- `descending (Br N)` (= `descendingB … = true`) の row-0 単調成分：
`J₀ ≤ J₁ < Lng Q` で `(Q_J₁)₀,₀ ≤ (Q_J₀)₀,₀`。 -/
private theorem descendingB_row0_h0 (Q : List PS) (h : descendingB Q = true)
    (J₀ J₁ : ℕ) (hle : J₀ ≤ J₁) (hlt : J₁ < Q.length) :
    entry (Q.getD J₁ []) 0 0 ≤ entry (Q.getD J₀ []) 0 0 := by
  simp only [descendingB, List.all_eq_true, List.mem_range] at h
  have hc := h J₁ hlt J₀ (by omega)
  simp only [cdomB, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact hc.1

/-- 最終枝は単項（BASE）: `Lng ((Br N).getLastD []) = 1`（`bfx_BrLen_Pred_base` の下段）。 -/
private theorem lastBr_singleton_h0 (N : PS) (hM : TPS N) (hBrne : Br N ≠ [])
    (hbase : VEj1p N = Lng N - 1) : Lng ((Br N).getLastD []) = 1 := by
  have hfneq : (FirstNodes N).getD ((Br N).length - 1) 0 = Lng N - 1 := by
    simpa only [VEj1p] using hbase
  rw [getLastD_eq_getD_last_68 (Br N) [] hBrne, wf21_Br_eq_seg N hM hBrne, hfneq,
    length_seg]
  omega

/-- **枝数減少**（Isabelle `bfx_BrLen_Pred_base`）: BASE run ホストで
`(Br (Pred N)).length = (Br N).length - 1`。 -/
private theorem BrLen_Pred_h0 (N : PS) (hM : TPS N) (hBrne : Br N ≠ [])
    (hL1 : 1 < Lng N) (htrne : TrMax N ≠ Lng N - 1) (hbase : VEj1p N = Lng N - 1) :
    (Br (Pred N)).length = (Br N).length - 1 := by
  rw [Br_Pred_core_nontrunk N hM hL1 htrne,
    if_pos (show Lng ((Br N).getLastD []) ≤ 1 by
      rw [lastBr_singleton_h0 N hM hBrne hbase])]
  simp

/-- Isabelle `a1_FN_hasParent`: 枝 first node は row-0 に親を持つ。 -/
private theorem a1_FN_hasParent_h0 (M : PS) (J : ℕ)
    (hM : TPS M) (hmono : monoT M = true) (hJ : J < (Br M).length) :
    hasParent M 0 ((FirstNodes M).getD J 0) = true := by
  have htb := TrMax_bound M hM
  have hne : TrMax M ≠ Lng M - 1 := by
    intro heq
    have hbr : Br M = [] := by simp [Br, heq]
    rw [hbr] at hJ; simp at hJ
  have htrlt : TrMax M < Lng M - 1 := by omega
  have hBr : Br M = P (seg M (TrMax M + 1) (Lng M - 1)) := by simp [Br, hne]
  have hJQ : J ≤ (P (seg M (TrMax M + 1) (Lng M - 1))).length - 1 := by
    rw [← hBr]; omega
  have hn := mono_slice_next M (TrMax M + 1) J hM hmono (by omega) (by omega) hJQ
  have hfn := FirstNodes_getD M J hJ
  rw [hfn, hBr]
  exact hn.1

/-- Isabelle `a1_FN_lt`: 枝 first node は範囲内 `< Lng M`。 -/
private theorem a1_FN_lt_h0 (M : PS) (J : ℕ)
    (hM : TPS M) (hmono : monoT M = true) (hJ : J < (Br M).length) :
    (FirstNodes M).getD J 0 < Lng M := by
  have hnx := Joints_nextR_FirstNodes M J hM hmono hJ
  have hn0 : nextrel0 M ((Joints M).getD J 0) ((FirstNodes M).getD J 0) = true := by
    simpa [nextR] using hnx
  have h := hn0
  simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.2

/-- **`bgx_headedge`** (Isabelle `pss_wip.thy:106811`): 各枝 `J` で頭 joint の row-0 値 + 1 =
first node の row-0 値。`RedCondA` の親辺条件を `FirstNodes` に適用し、`Joints = parent∘FirstNodes`
で書き換える。 -/
private theorem headEdge_h0 (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (J : ℕ) (hJ : J < (Br M).length) :
    entry M 0 ((Joints M).getD J 0) + 1 = entry M 0 ((FirstNodes M).getD J 0) := by
  have hM : TPS M := RTPS_TPS M hR
  have hcondA : RedCondA M = true := (RTPS_condAB M hR).1
  have hhas : hasParent M 0 ((FirstNodes M).getD J 0) = true :=
    a1_FN_hasParent_h0 M J hM hmono hJ
  have hlt : (FirstNodes M).getD J 0 < Lng M := a1_FN_lt_h0 M J hM hmono hJ
  have hedge := RedCondA_apply M hcondA 0 ((FirstNodes M).getD J 0) (by omega) hlt hhas
  rw [Joints_getD M J hJ]
  exact hedge

/-- **`bfx_gtN`** (Isabelle `pss_wip.thy:104527`): BASE run ホストで最終枝頭は狭義ガード
（row-1 < row-0）。体制の guard を `entry_FirstNodes_eq_component_mr` で枝成分表示に移す。 -/
private theorem gtN_h0 (N : PS) (hR : RTPS N) (hBrne : Br N ≠ [])
    (hguard : entry N 1 (VEj1p N) < entry N 0 (VEj1p N)) :
    entry ((Br N).getD ((Br N).length - 1) []) 1 0
      < entry ((Br N).getD ((Br N).length - 1) []) 0 0 := by
  have hM : TPS N := RTPS_TPS N hR
  have hJ1lt : (Br N).length - 1 < (Br N).length := by
    have := List.length_pos_of_ne_nil hBrne; omega
  have h0 : entry N 0 ((FirstNodes N).getD ((Br N).length - 1) 0)
      = entry ((Br N).getD ((Br N).length - 1) []) 0 0 :=
    entry_FirstNodes_eq_component_mr N ((Br N).length - 1) 0 hM hJ1lt
  have h1 : entry N 1 ((FirstNodes N).getD ((Br N).length - 1) 0)
      = entry ((Br N).getD ((Br N).length - 1) []) 1 0 :=
    entry_FirstNodes_eq_component_mr N ((Br N).length - 1) 1 hM hJ1lt
  rw [← h0, ← h1]
  simpa only [VEj1p] using hguard

/-- **`vgx_LastStep_elsecase` の全域版最小性** (Isabelle `pss_wip.thy:104553`/deep3 `notInS`):
非対角ガード下で `k < LastStep N` の枝 `k` は `S`-述語（同 row-0 枝頭 ∧ row-1 < row-0）を満たさない。 -/
private theorem LastStep_find_min_h0 (M : PS) (hBrne : Br M ≠ [])
    (hnd : entry ((Br M).getD ((Br M).length - 1) []) 0 0
         ≠ entry ((Br M).getD ((Br M).length - 1) []) 1 0)
    (k : ℕ) (hk : k < LastStep M) :
    ¬ (entry ((Br M).getD ((Br M).length - 1) []) 0 0 = entry ((Br M).getD k []) 0 0
       ∧ entry ((Br M).getD k []) 1 0 < entry ((Br M).getD k []) 0 0) := by
  have hLpos : 0 < (Br M).length := List.length_pos_of_ne_nil hBrne
  have hL : (Br M).length ≠ 0 := by omega
  rintro ⟨heq0, hlt0⟩
  have hpk : (decide (entry ((Br M).getD ((Br M).length - 1) []) 0 0 = entry ((Br M).getD k []) 0 0)
             && decide (entry ((Br M).getD k []) 1 0 < entry ((Br M).getD k []) 0 0)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨heq0, hlt0⟩
  have hLSval : LastStep M
      = ((List.range (Br M).length).find? (fun J =>
          decide (entry ((Br M).getD ((Br M).length - 1) []) 0 0 = entry ((Br M).getD J []) 0 0) &&
          decide (entry ((Br M).getD J []) 1 0 < entry ((Br M).getD J []) 0 0))).getD
            ((Br M).length - 1) := by
    unfold LastStep
    simp only [hL, if_false]
    split
    · next heq => exact absurd heq hnd
    · rfl
  rw [hLSval] at hk
  cases hfind : (List.range (Br M).length).find? (fun J =>
      decide (entry ((Br M).getD ((Br M).length - 1) []) 0 0 = entry ((Br M).getD J []) 0 0) &&
      decide (entry ((Br M).getD J []) 1 0 < entry ((Br M).getD J []) 0 0)) with
  | none =>
      simp only [hfind, Option.getD_none] at hk
      have hkmem : k ∈ List.range (Br M).length := List.mem_range.mpr (by omega)
      exact (List.find?_eq_none.mp hfind) k hkmem hpk
  | some c =>
      simp only [hfind, Option.getD_some] at hk
      have hf' : (List.range' 0 (Br M).length).find? (fun J =>
          decide (entry ((Br M).getD ((Br M).length - 1) []) 0 0 = entry ((Br M).getD J []) 0 0) &&
          decide (entry ((Br M).getD J []) 1 0 < entry ((Br M).getD J []) 0 0)) = some c := by
        simpa using hfind
      have hmin := (List.find?_range'_eq_some.mp hf').2.2 k (Nat.zero_le k) hk
      rw [hpk] at hmin
      simp at hmin

/-- `bpHeadT (Dprin a X) = X`（`Dprin a X = .trm [.db a X]` の頭抽出）。 -/
private theorem bpHeadT_Dprin_h0 (a : ℕ∞) (X : BT) : bpHeadT (Dprin a X) = X := rfl

/-! ## 主定理: `HEADEQ0All_hq` の無条件討伐 -/

/-- **`HEADEQ0All_hq`**（Isabelle `hqx_HEADEQ0`, `pss_wip.thy:108441`）: BASE run-base ホスト
（`VE34Reg4D N`, `VEj1p N = Lng N - 1`, `LastStep N = Lng(Br N)-1`）で終切片 `seg N j₀ (Lng N-1)`
の `Pred` の deep head は host `N` の `Pred` の deep head に等しい。`Pred N` の枝の有無で
[trunk corner]（diagSeq 閉形式）／[branching]（regime + `vcx_VE_all`）に分岐する。 -/
theorem headEq0All_holds : HEADEQ0All_hq := by
  intro N reg base r0
  obtain ⟨reg4, hdesc⟩ := reg
  obtain ⟨⟨⟨hR, hmono, hBrne⟩, hguard⟩, hj0pos, hj0lt⟩ := reg4
  -- 基本セットアップ（Isabelle `bfx_base_setup`）
  have hM : TPS N := RTPS_TPS N hR
  have htrbd : TrMax N ≤ Lng N - 1 := TrMax_bound N hM
  have htrne : TrMax N ≠ Lng N - 1 := fun h => hBrne (by simp [Br, h])
  have htrlt : TrMax N < Lng N - 1 := by omega
  have hL : 1 < Lng N := by omega
  have hLQ : Lng (Pred N) = Lng N - 1 := length_Pred N hL
  have hTrQ : TrMax (Pred N) = TrMax N := TrMax_Pred_nontrunk N hM hL htrne
  have hcondA : RedCondA N = true := (RTPS_condAB N hR).1
  have hdiag : entry N 0 0 = entry N 1 0 := RTPS_mono_head_eq N hR hmono
  have hj0lt2 : (Joints N).getD ((Br N).length - 1) 0 < Lng N - 1 := by omega
  have hPseg : Pred (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1))
      = seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 2) :=
    hqx_Pred_seg_hq N ((Joints N).getD ((Br N).length - 1) 0) hL hj0lt2
  by_cases hBrQ : Br (Pred N) = []
  · -- ===== trunk corner: Br (Pred N) = [] =====
    have trunkQ : TrMax (Pred N) = Lng (Pred N) - 1 := by
      by_contra hc
      have hBrP : Br (Pred N) = P (seg (Pred N) (TrMax (Pred N) + 1) (Lng (Pred N) - 1)) := by
        simp [Br, hc]
      exact P_nonempty _ (hBrP.symm.trans hBrQ)
    have hLN2 : Lng N - 2 = TrMax N := by omega
    have hRQ : RTPS (Pred N) := RTPS_Pred N hR
    have hQdiag : Pred N
        = diagSeq (entry (Pred N) 1 0) (entry (Pred N) 1 0 + (Lng (Pred N) - 1)) :=
      wnx_trunk_diagSeq (Pred N) hRQ trunkQ
    have heQ : entry (Pred N) 1 0 = entry N 1 0 := entry_Pred N 1 0 (by omega)
    have hLQ1 : Lng (Pred N) - 1 = TrMax N := by omega
    -- Trans (Pred N)
    have hTP : Trans (Pred N)
        = Dprin ((entry N 1 0 : ℕ) : ℕ∞) (Dprin ((entry N 1 0 + TrMax N : ℕ) : ℕ∞) BZero) := by
      have hrw : Pred N = diagSeq (entry N 1 0) (entry N 1 0 + TrMax N) := by
        rw [hQdiag, heQ, hLQ1]
      rw [hrw, diagSeq_Trans (entry N 1 0) (entry N 1 0 + TrMax N) (by omega)]
    -- seg N j₀ (Lng N-2) = diagSeq (e+j₀) (e+TrMax N)
    have hlistS : seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 2)
        = diagSeq (entry N 1 0 + (Joints N).getD ((Br N).length - 1) 0)
            (entry N 1 0 + TrMax N) := by
      apply List.ext_getElem
      · simp only [length_seg, diagSeq, List.length_map, List.length_range']
        omega
      · intro i h1 h2
        rw [seg_getElem_68 N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 2) i h1,
            diagSeq_getElem_h0 (entry N 1 0 + (Joints N).getD ((Br N).length - 1) 0)
              (entry N 1 0 + TrMax N) i h2]
        have hilt : i < Lng (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 2)) := h1
        have hij : (Joints N).getD ((Br N).length - 1) 0 + i ≤ TrMax N := by
          rw [length_seg] at hilt; omega
        have ho := trunk_entries_offset N hM hcondA
          ((Joints N).getD ((Br N).length - 1) 0 + i) hij
        rw [Prod.mk.injEq]
        refine ⟨?_, ?_⟩
        · rw [ho.1, hdiag]; omega
        · rw [ho.2]; omega
    have hTS : Trans (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 2))
        = Dprin ((entry N 1 0 + (Joints N).getD ((Br N).length - 1) 0 : ℕ) : ℕ∞)
            (Dprin ((entry N 1 0 + TrMax N : ℕ) : ℕ∞) BZero) := by
      rw [hlistS, diagSeq_Trans (entry N 1 0 + (Joints N).getD ((Br N).length - 1) 0)
        (entry N 1 0 + TrMax N) (by omega)]
    rw [hPseg, hTS, hTP, bpHeadT_Dprin_h0, bpHeadT_Dprin_h0]
  · -- ===== branching: Br (Pred N) ≠ [] =====
    have hLQgt : 1 < Lng (Pred N) := by rw [hLQ]; omega
    have hDN : DTPS N := (DTPS_iff N).mpr ⟨hR, hmono, hdesc⟩
    have hDQ : DTPS (Pred N) := descending_Br_Pred N hDN hBrne hLQgt
    obtain ⟨hRQ, hmonoQ, hdescQ⟩ := (DTPS_iff (Pred N)).mp hDQ
    have hMQ : TPS (Pred N) := RTPS_TPS (Pred N) hRQ
    have hBrLenQ : (Br (Pred N)).length = (Br N).length - 1 :=
      BrLen_Pred_h0 N hM hBrne hL htrne base
    have hBrpos : 0 < (Br N).length := List.length_pos_of_ne_nil hBrne
    have hBrQpos : 0 < (Br (Pred N)).length := List.length_pos_of_ne_nil hBrQ
    have hJ1ge1 : 1 ≤ (Br N).length - 1 := by omega
    have hJpP : (Br N).length - 2 < (Br (Pred N)).length := by omega
    have hJpN : (Br (Pred N)).length - 1 = (Br N).length - 2 := by omega
    have hJpltBrN : (Br N).length - 2 < (Br N).length := by omega
    have hJ1Br : (Br N).length - 1 < (Br N).length := by omega
    -- Joints / FirstNodes transport (wid_*)
    have hjqQ : (Joints (Pred N)).getD ((Br N).length - 2) 0
        = (Joints N).getD ((Br N).length - 2) 0 :=
      Joints_Pred_core N hM hmono hL htrne ((Br N).length - 2) hJpP
    have hfqQ : (FirstNodes (Pred N)).getD ((Br N).length - 2) 0
        = (FirstNodes N).getD ((Br N).length - 2) 0 :=
      FirstNodes_Pred_core N hM hL htrne ((Br N).length - 2) hJpP
    have hgeomp := FirstNodes_TrMax_Joints N ((Br N).length - 2) hM hmono hJpltBrN
    have hfqltQ : (FirstNodes (Pred N)).getD ((Br N).length - 2) 0 < Lng (Pred N) :=
      a1_FN_lt_h0 (Pred N) ((Br N).length - 2) hMQ hmonoQ hJpP
    have hfqlt : (FirstNodes N).getD ((Br N).length - 2) 0 < Lng N - 1 := by
      rw [hfqQ, hLQ] at hfqltQ; exact hfqltQ
    have hfqLngN : (FirstNodes N).getD ((Br N).length - 2) 0 < Lng N := by omega
    -- headedges (bgx_headedge)
    have he_p : entry N 0 ((Joints N).getD ((Br N).length - 2) 0) + 1
        = entry N 0 ((FirstNodes N).getD ((Br N).length - 2) 0) :=
      headEdge_h0 N hR hmono ((Br N).length - 2) hJpltBrN
    have fn1 : (FirstNodes N).getD ((Br N).length - 1) 0 = Lng N - 1 := by
      simpa only [VEj1p] using base
    have he_1 : entry N 0 ((Joints N).getD ((Br N).length - 1) 0) + 1
        = entry N 0 (Lng N - 1) := by
      have h := headEdge_h0 N hR hmono ((Br N).length - 1) hJ1Br
      rw [fn1] at h; exact h
    -- component readouts (entry_FirstNodes_eq_component)
    have brhd_p0 : entry N 0 ((FirstNodes N).getD ((Br N).length - 2) 0)
        = entry ((Br N).getD ((Br N).length - 2) []) 0 0 :=
      entry_FirstNodes_eq_component_mr N ((Br N).length - 2) 0 hM hJpltBrN
    have brhd_10 : entry N 0 (Lng N - 1)
        = entry ((Br N).getD ((Br N).length - 1) []) 0 0 := by
      have h := entry_FirstNodes_eq_component_mr N ((Br N).length - 1) 0 hM hJ1Br
      rw [fn1] at h; exact h
    -- descending row-0 monotone
    have deschd : entry ((Br N).getD ((Br N).length - 1) []) 0 0
        ≤ entry ((Br N).getD ((Br N).length - 2) []) 0 0 :=
      descendingB_row0_h0 (Br N) hdesc ((Br N).length - 2) ((Br N).length - 1) (by omega) hJ1Br
    -- j₀ ≤ j_q
    have hjqge : (Joints N).getD ((Br N).length - 1) 0
        ≤ (Joints N).getD ((Br N).length - 2) 0 := by
      have hfge : entry N 0 (Lng N - 1)
          ≤ entry N 0 ((FirstNodes N).getD ((Br N).length - 2) 0) := by
        rw [brhd_p0, brhd_10]; exact deschd
      have ho_jq := (trunk_entries_offset N hM hcondA
        ((Joints N).getD ((Br N).length - 2) 0) hgeomp.1).1
      have ho_j0 := (trunk_entries_offset N hM hcondA
        ((Joints N).getD ((Br N).length - 1) 0) (le_of_lt hj0lt)).1
      omega
    -- regime VEReg j₀ (Pred N)
    have regQ : VEReg ((Joints N).getD ((Br N).length - 1) 0) (Pred N) := by
      refine ⟨hRQ, hmonoQ, hBrQ, ?_⟩
      by_cases hcase : (Joints N).getD ((Br N).length - 1) 0
          = (Joints N).getD ((Br N).length - 2) 0
      · -- shared joint: run-base LastStep minimality forbids a guarded head
        have heqfq : entry N 0 ((FirstNodes N).getD ((Br N).length - 2) 0)
            = entry N 1 ((FirstNodes N).getD ((Br N).length - 2) 0) := by
          have hcoeff := reduced_coeff N hR ((FirstNodes N).getD ((Br N).length - 2) 0) hfqLngN
          have hngt : ¬ entry N 1 ((FirstNodes N).getD ((Br N).length - 2) 0)
              < entry N 0 ((FirstNodes N).getD ((Br N).length - 2) 0) := by
            intro hgt
            have h1 := he_1
            rw [hcase] at h1
            have heqfq10 : entry N 0 ((FirstNodes N).getD ((Br N).length - 2) 0)
                = entry N 0 (Lng N - 1) := by omega
            have hdeq : entry ((Br N).getD ((Br N).length - 1) []) 0 0
                = entry ((Br N).getD ((Br N).length - 2) []) 0 0 := by
              rw [← brhd_10, ← brhd_p0]; exact heqfq10.symm
            have brhd_p1 : entry N 1 ((FirstNodes N).getD ((Br N).length - 2) 0)
                = entry ((Br N).getD ((Br N).length - 2) []) 1 0 :=
              entry_FirstNodes_eq_component_mr N ((Br N).length - 2) 1 hM hJpltBrN
            have hgrd : entry ((Br N).getD ((Br N).length - 2) []) 1 0
                < entry ((Br N).getD ((Br N).length - 2) []) 0 0 := by
              rw [← brhd_p1, ← brhd_p0]; exact hgt
            have hgtJ1 := gtN_h0 N hR hBrne hguard
            have hnd : entry ((Br N).getD ((Br N).length - 1) []) 0 0
                ≠ entry ((Br N).getD ((Br N).length - 1) []) 1 0 := by omega
            have hJpltLS : (Br N).length - 2 < LastStep N := by rw [r0]; omega
            exact LastStep_find_min_h0 N hBrne hnd ((Br N).length - 2) hJpltLS ⟨hdeq, hgrd⟩
          omega
        right
        refine ⟨by rw [hJpN, hjqQ]; exact hcase, ?_, hdescQ⟩
        simp only [VEj1p]
        rw [hJpN, hfqQ,
            entry_Pred N 0 ((FirstNodes N).getD ((Br N).length - 2) 0) hfqlt,
            entry_Pred N 1 ((FirstNodes N).getD ((Br N).length - 2) 0) hfqlt]
        exact heqfq
      · left
        rw [hJpN, hjqQ]
        exact lt_of_le_of_ne hjqge hcase
    have hVEQ : VEeq ((Joints N).getD ((Br N).length - 1) 0) (Pred N) :=
      vcx_VE_all ((Joints N).getD ((Br N).length - 1) 0) (Pred N) regQ
    -- final chain
    have hLQm1 : Lng (Pred N) - 1 = Lng N - 2 := by omega
    have hj0le2 : (Joints N).getD ((Br N).length - 1) 0 ≤ Lng N - 2 := by omega
    have hs2 : seg (Pred N) ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 2)
        = seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 2) :=
      seg_Pred_eq N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 2) hL hj0le2 (by omega)
    rw [hPseg, ← hs2, ← hLQm1]
    exact hVEQ

#print axioms headEq0All_holds

end PSS
