import «8».«8.4-exch84-nest-scb»
import «8».«8.4-exch84-corner»

/-!
# §8.4 交換パッケージ condIV admeq 隅の RE-DESIGN（`8.4-exch84-corner` の反証を受けて）

## 背景（何が壊れていたか）

- `8.4-exch84-nest-scb` の `exch84_nestScbTriple_holds` は `transCondIII ∨ transCondIV` の
  **全域**で nest 三つ組 `Exch84_nestScbTriple`（«8».«8.4-exch84-scbdecomp»:362）を組もうとし、
  隅（condIV ∧ admeq, すなわち `s84x_jm3 M = transJm1 M`）を残差 `NestScbCornerTriple_ns` に
  委ねていた。
- `8.4-exch84-corner` が **`NestScbCornerTriple_ns` を機械反証**した（`NestScbCornerTriple_ns_refuted_cn`）。
  隅では切片が潰れ `Trans (Pred (s84x_N M)) = transC1 M` となるため、非空 prefix
  `Dsym e₃ :: u1` を持つ dP は長さで矛盾する。d2 側も同様に `Trans (s84x_N M) = transC2 M`
  で潰れる。**よって nest 三つ組は隅で不成立で、`Exch84_nestScbTriple`（無ガード）は偽**。

## Isabelle が隅で「三つ組の代わりに」生むもの（faithful なルート）

Isabelle は隅を **nest 三つ組で通さない**。分岐 `oi5_ltJ_or_IVadmeq`（= Lean
`ltJ_or_IVadmeq_sp`）で早期に ltJ と admeq 隅を分け、隅では:

* `w84x_TN_c2_of_admeq` (layerB/pss_wip.thy:79333 近傍): `Trans (s84x_N M) = transC2 M`。
* `w84x_PN_c1_of_admeq` (layerB/pss_wip.thy:79359): `Trans (Pred (s84x_N M)) = transC1 M`。

を **collapse 恒等式**として産み、その上で「terminal-slice transport」
（`w84x_d2_IIIV_dispatch` wip:79420 / `w84x_d3_IIIV_dispatch` wip:79495。inner は
`flatBT (Dpt e₁ 0_B)`、subject は `transC2 M` / `Trans (s84x_Np M)` / `Trans (Pred (s84x_Np M))`）
で `w84x_various_scb_IIIV_of_sliceregs`（wip:79569）にまとめる。**nest 三つ組
（inner = `flatBT (transC1/transC2 M)`, 共通 `(u1,v1)`）は ltJ 専用**（`cpx_various_scb_IIIIV`
wip:98539 は仮定に `ltJ: s84x_jm3 M < transJm1 M` を持つ）。

Lean 側では隅の交換は既に **slicepkg ルート**（`Mnform_condIV_admeq_sp`
→ `SlicepkgMnformOut_sp`, «8».«8.4-exch84-slicepkg»）が担っており、非退化である。

## 本ファイルの成果物

1. **正しい隅 Prop = collapse 恒等式**（`CornerCollapse_cr` / `cornerCollapse_holds_cr`、
   完全証明）。これが Isabelle が隅で三つ組の代わりに生むもの
   （= `w84x_TN_c2_of_admeq` + `w84x_PN_c1_of_admeq`）。
2. **三つ組は再設計が必要**（機械証明 `exch84_nestScbTriple_false_cr : ¬ Exch84_nestScbTriple`）。
   隅の任意の Prop から `Exch84_nestScbTriple`（無ガード）を導くことは**不可能**
   （偽命題を結論に置けない）。よってミッションの
   `theorem exch84_nestScbTriple_corner_fix : … → Exch84_nestScbTriple` は原理的に組めない。
3. **正しい再設計 = ltJ ガードの再付与**（`Exch84_nestScbTriple_ltJ_cr` def ＋ discharge
   `exch84_nestScbTriple_ltJ_holds_cr`）。Isabelle `cpx_various_scb_IIIIV` の `ltJ` 仮定を
   Lean が落としていたのが根本原因。ltJ ガード付きなら nest エンジンで discharge 可能。

## パーレント向け配線指示（precise）

- `Exch84_nestScbTriple`（«8».«8.4-exch84-scbdecomp»:362）と、それに依存する
  `Exch84_scbDecompPkg`（«8».«8.4-exch84-base1p»:370）、`Exch84_scbDecompPkg_of_triple`、
  `mnformBottomResidual_holds`（«8».«8.4-exch84-mnform-bottom»:108）、
  `MnformBottomResidual`（«8».«8.4-exch84-mnform-residual»）は **すべて `transCondIII ∨ transCondIV`
  の全域で dP/d2 を要求しており、隅（condIV ∧ admeq）で偽**。
  → これらの Prop に `s84x_jm3 M < transJm1 M`（ltJ）ガードを加えて再言明せよ。
- 隅（condIV ∧ admeq）は nest ルートを**通さず**、本ファイルの `cornerCollapse_holds_cr`
  ＋ slicepkg ルート（`Mnform_condIV_admeq_sp` → `SlicepkgMnformOut_sp`）へ配線せよ。
  条件(III) では admeq は空虚（`ltJ_or_IVadmeq_sp` が `Or.inl` を強制）なので ltJ ガードは
  条件(III) では自由。

- 依存（ビルド済み・committed at main 56b1dda）: «8».«8.4-exch84-nest-scb»
  （`Exch84_nestScbTriple`・`NestScbD4aTransport_ns`・`s84x_N`/`s84x_jm2`/`s84x_jm3`・
  `transC1`/`transC2`/`transJm1`・`Mark_Trans_repr`/`m_7_3_Mark_rightmost2`/`Mark_order`/
  `scb_decomposition_triviality`/`Mark_leftend_form_proper`/`Mark_nest_common_marked`/
  `Regs_jm3Marked_holds`/`Marked_Pred`/`seg_Pred_eq`/`Trans_Mark_invariant`/`RTPS_Pred`/
  `mono_hasParent_row0`/`adm_row1_ancestry`/`row1_implies_row0`/`row0_transitive`/
  `Adm_adm`/`Adm_le`/`nextR0_leR`/`hasParent_next_fseq`/`parent_lt_of_hasParent`）、
  «8».«8.4-exch84-corner»（`NestScbCornerTriple_ns_refuted_cn`）。
- 状態: 🤖 GREEN（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  collapse 恒等式＋三つ組の反証＋ ltJ ガード版の discharge を完全証明。
- 訂正候補: corrections.md へ「Lean 移植の §8.4 nest 三つ組束
  （`Exch84_nestScbTriple` 系）は Isabelle `cpx_various_scb_IIIIV` の `ltJ` 仮定を
  落としており、隅で偽。ltJ ガードを再付与せよ」（本ファイル外・スコープ外）。
- Private helper suffix: `_cr`。
-/

namespace PSS

/-! ## 1. 隅の幾何補助（`8.4-exch84-nest-scb` の private helper の再掲、suffix `_cr`） -/

/-- Isabelle `s84c2_seg_butlast` (layerB/pss_wip.thy:54216): `dropLast (seg M a b) = seg M a (b-1)`。
`8.4-exch84-nest-scb` の private `seg_dropLast_ns` の再掲。 -/
private theorem seg_dropLast_cr (M : PS) (a b : ℕ) (hb : 1 ≤ b) :
    (seg M a b).dropLast = seg M a (b - 1) := by
  apply List.ext_getElem
  · simp only [List.length_dropLast, length_seg]; omega
  · intro i h1 h2
    simp only [List.getElem_dropLast, seg, List.getElem_map, List.getElem_range']

/-- Isabelle `s84d_jm1_Marked` (layerB/pss_wip.thy:58808): 第2基点 `j₋₁ = transJm1 M` は
`M` 側でも marked 列であり、最終列より真に左。`8.4-exch84-nest-scb` の private
`marked_transJm1_ns` の再掲。 -/
private theorem marked_transJm1_cr (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hj1gt : 1 < Lng M - 1) :
    Marked M (transJm1 M) ∧ transJm1 M < Lng M - 1 := by
  have hM : TPS M := RTPS_TPS M hR
  have hlen : 1 < Lng M := by omega
  have hp : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hM hmono (Lng M - 1) (by omega) (by omega)
  have hj0lt : transJ0 M < Lng M - 1 := by
    simpa [transJ0, lastParent, lastIdx] using
      parent_lt_of_hasParent M 0 (Lng M - 1) hp
  have hnpar : nextR M 0 (transJ0 M) (Lng M - 1) = true := by
    simpa [transJ0, lastParent, lastIdx] using
      hasParent_next_fseq M 0 (Lng M - 1) hp
  have hleJ0 : leR M 0 (transJ0 M) (Lng M - 1) = true := nextR0_leR M _ _ hnpar
  have haAdm : adm M (Adm M (transJ0 M)) = true := Adm_adm M (transJ0 M)
  have hle1a : leR M 1 (Adm M (transJ0 M)) (transJ0 M) = true :=
    adm_row1_ancestry M (transJ0 M) hM (by omega)
  have hle0a : leR M 0 (Adm M (transJ0 M)) (transJ0 M) = true :=
    row1_implies_row0 M _ _ hM hle1a
  have hchain : leR M 0 (Adm M (transJ0 M)) (Lng M - 1) = true :=
    row0_transitive M _ _ _ hM hle0a hleJ0
  have haLe : Adm M (transJ0 M) ≤ transJ0 M := Adm_le M (transJ0 M)
  refine ⟨⟨hM, ?_, ?_⟩, ?_⟩
  · simpa [transJm1] using haAdm
  · simpa [transJm1] using hchain
  · simp only [transJm1]; omega

/-! ## 2. 正しい隅 Prop = collapse 恒等式（Isabelle `w84x_TN_c2_of_admeq`
     ＋ `w84x_PN_c1_of_admeq`）。これが Isabelle が隅で三つ組の代わりに生むもの。 -/

/-- **正しい隅 Prop**（faithful to Isabelle）。隅（condIV ∧ admeq, `s84x_jm3 M = transJm1 M`）
では切片が潰れ、`Trans (s84x_N M)` / `Trans (Pred (s84x_N M))` は非退化 scb 分解ではなく
**collapse 恒等式** `transC2 M` / `transC1 M` に等しくなる。Isabelle
`w84x_TN_c2_of_admeq` (wip:79333 近傍) + `w84x_PN_c1_of_admeq` (wip:79359) の逐語。 -/
def CornerCollapse_cr : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → transCondIV M = true → Adm M (s84x_jm2 M) = transJm1 M →
    Trans (s84x_N M) = transC2 M ∧ Trans (Pred (s84x_N M)) = transC1 M

/-- **`CornerCollapse_cr` の完全証明**。隅の collapse 恒等式を、nest エンジンを一切使わず
値レベルの `Mark_Trans_repr`（jm3=jm1 特殊化）＋ `m_7_3_Mark_rightmost2`（右端第2基点）＋
`transC1 M = Mark (Pred M) (transJm1 M)`（定義）だけで組む。 -/
theorem cornerCollapse_holds_cr : CornerCollapse_cr := by
  intro M hST hmono hp hj1 hIV hadmeq
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  have hlen : 1 < Lng M := by omega
  -- 隅の要 `s84x_jm3 M = transJm1 M`
  have jm3eq : s84x_jm3 M = transJm1 M := hadmeq
  -- 範囲 `rng : j₋₂ + 1 < Lng M - 1`（Isabelle `w84x_PN_c1_of_admeq` の仮定 `rng`）を
  -- condIV から `j₋₂ < transJ0 < Lng M - 1` で導出する。
  have jm2ltj0 : s84x_jm2 M < transJ0 M :=
    regs_jm2_lt_transJ0_holds M hST hmono hp hj1 (Or.inr hIV)
  have hp0 : hasParent M 0 (Lng M - 1) = true :=
    mono_hasParent_row0 M hMT hmono (Lng M - 1) (by omega) (by omega)
  have hj0lt : transJ0 M < Lng M - 1 := by
    simpa [transJ0, lastParent, lastIdx] using
      parent_lt_of_hasParent M 0 (Lng M - 1) hp0
  have rng : s84x_jm2 M + 1 < Lng M - 1 := by omega
  have jm3le2 : s84x_jm3 M ≤ s84x_jm2 M := Adm_le M (s84x_jm2 M)
  -- 基点情報
  obtain ⟨mM3, _jm3le, _jm2lt⟩ := Regs_jm3Marked_holds M hMR hMT hp
  obtain ⟨mM1, jm1lt⟩ := marked_transJm1_cr M hMR hmono hj1
  have jm3lt : s84x_jm3 M < Lng M - 1 := by rw [jm3eq]; exact jm1lt
  have J1pos : 0 < transJ1 M := by simp only [transJ1, lastIdx]; omega
  -- `transT1 M ≠ 0_B`（`m_7_3_Mark_rightmost2` の前提）
  have hLP : Lng (Pred M) = Lng M - 1 := by simp [Pred, Nat.not_le.mpr hlen]
  have nzP : zeroT (Pred M) = false := by
    have hne : ¬ (Lng (Pred M) = 1) := by rw [hLP]; omega
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    exact Or.inl hne
  have T1 : transT1 M ≠ BZero := by
    have T1' : Trans (Pred M) ≠ BZero :=
      (Trans_Mark_invariant (Pred M) (RTPS_Pred M hMR)).2.1 nzP
    simpa [transT1] using T1'
  -- 値書き換え（M 側）
  have rm2 : Mark M (transJm1 M) = transC2 M := m_7_3_Mark_rightmost2 M hMR hmono J1pos T1
  have reprM : Mark M (s84x_jm3 M) = Trans (s84x_N M) :=
    Mark_Trans_repr M (s84x_jm3 M) mM3 hMR jm3lt
  -- 値書き換え（Pred 側）: `Mark (Pred M) (s84x_jm3 M) = Trans (Pred (s84x_N M))`
  have c1v : Mark (Pred M) (transJm1 M) = transC1 M := rfl
  have mM3P : Marked (Pred M) (s84x_jm3 M) := Marked_Pred M (s84x_jm3 M) hMT hlen mM3 jm3lt
  have hPR : RTPS (Pred M) := RTPS_Pred M hMR
  have jm3ltP : s84x_jm3 M < Lng (Pred M) - 1 := by
    rw [hLP]; omega  -- j₋₃ ≤ j₋₂ < Lng M - 2 = Lng (Pred M) - 1（`rng`）
  have r0 : Mark (Pred M) (s84x_jm3 M)
      = Trans (seg (Pred M) (s84x_jm3 M) (Lng (Pred M) - 1)) :=
    Mark_Trans_repr (Pred M) (s84x_jm3 M) mM3P hPR jm3ltP
  have segeq : seg (Pred M) (s84x_jm3 M) (Lng (Pred M) - 1)
      = seg M (s84x_jm3 M) (Lng M - 2) := by
    have h1 : Lng (Pred M) - 1 = Lng M - 2 := by omega
    rw [h1]
    exact seg_Pred_eq M (s84x_jm3 M) (Lng M - 2) hlen (by omega) (by omega)
  have blN : Pred (s84x_N M) = seg M (s84x_jm3 M) (Lng M - 2) := by
    have hNlen : 1 < Lng (s84x_N M) := by
      simp only [s84x_N, length_seg]; omega
    have : Pred (s84x_N M) = (s84x_N M).dropLast := by
      simp [Pred, Nat.not_le.mpr hNlen]
    rw [this]
    show (seg M (s84x_jm3 M) (Lng M - 1)).dropLast = _
    have harg : Lng M - 1 - 1 = Lng M - 2 := by omega
    rw [seg_dropLast_cr M (s84x_jm3 M) (Lng M - 1) (by omega), harg]
  have reprP : Mark (Pred M) (s84x_jm3 M) = Trans (Pred (s84x_N M)) := by
    rw [r0, segeq, blN]
  -- 隅の 2 collapse 恒等式
  refine ⟨?_, ?_⟩
  · calc Trans (s84x_N M) = Mark M (s84x_jm3 M) := reprM.symm
      _ = Mark M (transJm1 M) := by rw [jm3eq]
      _ = transC2 M := rm2
  · calc Trans (Pred (s84x_N M)) = Mark (Pred M) (s84x_jm3 M) := reprP.symm
      _ = Mark (Pred M) (transJm1 M) := by rw [jm3eq]
      _ = transC1 M := c1v

#print axioms cornerCollapse_holds_cr

/-! ## 3. 三つ組は再設計が必要（機械証明 `¬ Exch84_nestScbTriple`） -/

/-- **`Exch84_nestScbTriple`（無ガード、«8».«8.4-exch84-scbdecomp»:362）は偽**。
隅 witness で `Or.inr` を選べば結論は `NestScbCornerTriple_ns` の要求と同型なので、
`8.4-exch84-corner` の反証 `NestScbCornerTriple_ns_refuted_cn` に矛盾する。
**帰結: 隅の任意の Prop から `Exch84_nestScbTriple` を導く定理
（ミッションの `exch84_nestScbTriple_corner_fix : … → Exch84_nestScbTriple`）は
原理的に存在しない。三つ組 Prop 自体を再言明する必要がある（§4）。** -/
theorem exch84_nestScbTriple_false_cr : ¬ Exch84_nestScbTriple := fun h =>
  NestScbCornerTriple_ns_refuted_cn
    (fun M hST hmono hp hj1 hIV _hadmeq => h M hST hmono hp hj1 (Or.inr hIV))

#print axioms exch84_nestScbTriple_false_cr

/-! ## 4. 正しい再設計 = ltJ ガード付き三つ組（`Exch84_nestScbTriple` の置換）

Isabelle `cpx_various_scb_IIIIV`（wip:98539）は仮定に `ltJ : s84x_jm3 M < transJm1 M` を
持つ。Lean の `Exch84_nestScbTriple` はこれを落として `transCondIII ∨ transCondIV` 全域に
主張したため隅で偽になった。ここで **ltJ ガードを再付与した正しい版**を定義し、nest エンジンで
discharge する。パーレントは `Exch84_nestScbTriple` をこれに置換し、隅は §2/slicepkg へ回せばよい。 -/

/-- **`Exch84_nestScbTriple` の正しい再言明**（ltJ ガード付き）。`Exch84_nestScbTriple`
（«8».«8.4-exch84-scbdecomp»:362）に Isabelle `cpx_various_scb_IIIIV` の `ltJ` 仮定
`s84x_jm3 M < transJm1 M` を加えた形。これは充足可能（下記 `exch84_nestScbTriple_ltJ_holds_cr`）。 -/
def Exch84_nestScbTriple_ltJ_cr : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) →
    s84x_jm3 M < transJm1 M →
    ∃ u1 v1 : List Sym,
      scb_decomp (Trans (Pred (s84x_N M)))
        (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC1 M)) v1 ∧
      scb_decomp (Trans (s84x_N M))
        (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC2 M)) v1 ∧
      scb_decomp (Trans (Pred (s84x_Np M)))
        (Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC1 M)) v1

/-- ltJ 枝の nest エンジン（Isabelle `s84d_dec2_nest_scb` の存在形）。`8.4-exch84-nest-scb` の
private `nestDec2_ltJ_ns` は import 越しに見えないため、公開補題のみで再証明する。 -/
private theorem nestDec2_ltJ_cr (M : PS) (hST : STPS M) (hmono : monoT M = true)
    (hp : hasParent M 1 (Lng M - 1) = true) (hj1 : 1 < Lng M - 1)
    (hltJ : s84x_jm3 M < transJm1 M) :
    ∃ u1 v1 : List Sym,
      scb_decomp (Trans (Pred (s84x_N M)))
        (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC1 M)) v1 ∧
      scb_decomp (Trans (s84x_N M))
        (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC2 M)) v1 := by
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  have hlen : 1 < Lng M := by omega
  obtain ⟨mM3, _jm3le, _jm2lt⟩ := Regs_jm3Marked_holds M hMR hMT hp
  obtain ⟨mM1, jm1lt⟩ := marked_transJm1_cr M hMR hmono hj1
  have jm3lt : s84x_jm3 M < Lng M - 1 := lt_trans hltJ jm1lt
  have hLP : Lng (Pred M) = Lng M - 1 := by simp [Pred, Nat.not_le.mpr hlen]
  have nzP : zeroT (Pred M) = false := by
    have hne : ¬ (Lng (Pred M) = 1) := by rw [hLP]; omega
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    exact Or.inl hne
  have T1 : transT1 M ≠ BZero := by
    have T1' : Trans (Pred M) ≠ BZero :=
      (Trans_Mark_invariant (Pred M) (RTPS_Pred M hMR)).2.1 nzP
    simpa [transT1] using T1'
  have J1pos : 0 < transJ1 M := by simp only [transJ1, lastIdx]; omega
  -- nest エンジン発火
  obtain ⟨⟨s, b⟩, ⟨dP, dM⟩, -⟩ :=
    Mark_nest_common_marked M (s84x_jm3 M) (transJm1 M) hMR mM3 mM1 (le_of_lt hltJ) jm1lt
  -- 値書き換え
  have rm2 : Mark M (transJm1 M) = transC2 M := m_7_3_Mark_rightmost2 M hMR hmono J1pos T1
  have c1v : Mark (Pred M) (transJm1 M) = transC1 M := rfl
  have reprM : Mark M (s84x_jm3 M) = Trans (s84x_N M) :=
    Mark_Trans_repr M (s84x_jm3 M) mM3 hMR jm3lt
  have mM3P : Marked (Pred M) (s84x_jm3 M) := Marked_Pred M (s84x_jm3 M) hMT hlen mM3 jm3lt
  have hPR : RTPS (Pred M) := RTPS_Pred M hMR
  have jm3ltP : s84x_jm3 M < Lng (Pred M) - 1 := by rw [hLP]; omega
  have r0 : Mark (Pred M) (s84x_jm3 M)
      = Trans (seg (Pred M) (s84x_jm3 M) (Lng (Pred M) - 1)) :=
    Mark_Trans_repr (Pred M) (s84x_jm3 M) mM3P hPR jm3ltP
  have segeq : seg (Pred M) (s84x_jm3 M) (Lng (Pred M) - 1)
      = seg M (s84x_jm3 M) (Lng M - 2) := by
    have h1 : Lng (Pred M) - 1 = Lng M - 2 := by omega
    rw [h1]
    exact seg_Pred_eq M (s84x_jm3 M) (Lng M - 2) hlen (by omega) (by omega)
  have blN : Pred (s84x_N M) = seg M (s84x_jm3 M) (Lng M - 2) := by
    have hNlen : 1 < Lng (s84x_N M) := by
      simp only [s84x_N, length_seg]; omega
    have : Pred (s84x_N M) = (s84x_N M).dropLast := by
      simp [Pred, Nat.not_le.mpr hNlen]
    rw [this]
    show (seg M (s84x_jm3 M) (Lng M - 1)).dropLast = _
    have harg : Lng M - 1 - 1 = Lng M - 2 := by omega
    rw [seg_dropLast_cr M (s84x_jm3 M) (Lng M - 1) (by omega), harg]
  have reprP : Mark (Pred M) (s84x_jm3 M) = Trans (Pred (s84x_N M)) := by
    rw [r0, segeq, blN]
  -- 非自明性 `Mark M (s84x_jm3 M) ≠ Mark M (transJm1 M)`
  have neq : Mark M (s84x_jm3 M) ≠ Mark M (transJm1 M) := by
    intro h
    exact ((Mark_order M (s84x_jm3 M) (transJm1 M) hMR mM3 mM1).mp hltJ).1 h.symm
  -- `s ≠ []`
  have sne : s ≠ [] := by
    intro hs0
    apply neq
    have hmem : (Mark M (s84x_jm3 M), Mark M (transJm1 M)) ∈ MarkedB := ⟨s, b, dM⟩
    exact (scb_decomposition_triviality hmem).2.mpr ⟨b, hs0 ▸ dM⟩
  -- 左端頭部露出
  obtain ⟨t, Mform⟩ := Mark_leftend_form_proper M (s84x_jm3 M) mM3 hMR jm3lt
  have hflatMark : flatBT (Mark M (s84x_jm3 M))
      = Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: flatBT t := by
    rw [Mform]; simp [Dprin, flatBT, flatBP]
  -- 頭を剥がす
  obtain ⟨s0, s', rfl⟩ := List.exists_cons_of_ne_nil sne
  have hs0 : s0 = Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) := by
    have h := dM.1
    rw [hflatMark] at h
    rw [List.cons_append, List.cons_append] at h
    exact ((List.cons.inj h).1).symm
  subst hs0
  rw [reprP, c1v] at dP
  rw [reprM, rm2] at dM
  exact ⟨s', b, dP, dM⟩

/-- **正しい再設計の discharge**: ltJ ガード付き三つ組 `Exch84_nestScbTriple_ltJ_cr` は、
ltJ 枝の nest エンジン `nestDec2_ltJ_cr`（dP+d2）と d4a 転送残差 `NestScbD4aTransport_ns`
（«8».«8.4-exch84-nest-scb»、Isabelle `cpx_d4a_all`）から充足可能。
すなわち `Exch84_nestScbTriple` を本 Prop に置換すれば隅の反例は消え、ltJ 域は元と同じ nest
エンジンで通る。 -/
theorem exch84_nestScbTriple_ltJ_holds_cr (hD4a : NestScbD4aTransport_ns) :
    Exch84_nestScbTriple_ltJ_cr := by
  intro M hST hmono hp hj1 hcond hltJ
  obtain ⟨u1, v1, dP, d2⟩ := nestDec2_ltJ_cr M hST hmono hp hj1 hltJ
  have d4a := hD4a M u1 v1 hST hmono hp hj1 hcond dP
  exact ⟨u1, v1, dP, d2, d4a⟩

#print axioms exch84_nestScbTriple_ltJ_holds_cr

end PSS
