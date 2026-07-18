import «8».«8.4-exch84-scbdecomp»
import «8».«8.4-exch84-slicepkg»
import «8».«8.4-exch84-mcond»
import «7».«7.4-Mark-nextAdm»
import «7».«7.3-Mark-rightmost2»
import «7».«7.4-Mark-order»
import «7».«7.2-scb-triviality»
import «7».«7.4-RightNodes-Mark»
import «7».«7.4-Mark-Trans-repr»
import «7».«7.4-Adm-nextAdm»
import «6».«6.6-P-condAB»

/-!
# §8.4 交換パッケージ nest-scb エンジンの discharge（`Exch84_nestScbTriple`）

- 原文: `tmp/content.md` §8.4（条件(III)/(IV) の下での `Trans` と基本列の交換関係、
  補題（条件(III)か(IV)の下での各種 scb 分解）content.md 4802 の L6 (1)(2)）。
- 対象: `Exch84_nestScbTriple`（«8».«8.4-exch84-scbdecomp»:362 で def・narrowing 済）
  = `s84x_N`/`s84x_Np` の Pred/生スライスの共通 `(u1, v1)` nest-scb 三つ組。
  逐語 = Isabelle `s84d_dec2_nest_scb` (layerB/pss_wip.thy:58991、dP/d2 の共通 nest 分解) と
  `cpx_d4a_all` (layerB/pss_wip.thy:98511、d4a 転送) を `cpx_various_scb_IIIIV`
  (layerB/pss_wip.thy:98539) 相当で束ねたもの。

## 移植構造

`Exch84_nestScbTriple` の仮定に `ltJ`(`s84x_jm3 M < transJm1 M`) は含まれない。
`ltJ_or_IVadmeq_sp`（«8».«8.4-exch84-slicepkg»、= Isabelle `oi5_ltJ_or_IVadmeq`）で
二分岐する:

* **ltJ 枝** (`s84x_jm3 M < transJm1 M`): `nestDec2_ltJ_ns`（= `s84d_dec2_nest_scb` の
  存在形、完全証明）で dP+d2 を共通 `(u1, v1)` で得、`NestScbD4aTransport_ns`（= `cpx_d4a_all`
  の残差）で dP から d4a を転送。
* **admeq 隅** (`transCondIV M ∧ Adm M (s84x_jm2 M) = transJm1 M`, すなわち
  `s84x_jm3 M = transJm1 M`): `NestScbCornerTriple_ns`（隅エンジンの残差）で三つ組を直接。

### ltJ 枝の nest エンジン（`nestDec2_ltJ_ns`、完全証明）

`Mark_nest_common_marked`（«7».«7.4-Mark-nextAdm», Isabelle `Mark_nest_common_marked`）を
`(s84x_jm3 M, transJm1 M)` で発火し、共通分解 `(s, b)` を得る。値書き換え:
`m_7_3_Mark_rightmost2`（`Mark M (transJm1 M) = transC2 M`）、`transC1 M = Mark (Pred M) (transJm1 M)`
（定義）、`Mark_Trans_repr`（`Mark M (s84x_jm3 M) = Trans (s84x_N M)`; Pred 側は `seg_Pred_eq`＋
`Pred = dropLast` で `Trans (Pred (s84x_N M))`）。非自明性 `Mark M (s84x_jm3 M) ≠ Mark M (transJm1 M)`
は `Mark_order`（«7».«7.4-Mark-order»）、`s ≠ []` は `scb_decomposition_triviality`
（«7».«7.2-scb-triviality»）。左端頭部露出 `Mark_leftend_form_proper`（«7».«7.4-RightNodes-Mark»）で
`s = Dsym(M₁,ⱼ₋₃) :: tl s`、`u1 = tl s`, `v1 = b`。jm3 marked は `Regs_jm3Marked_holds`
（«8».«8.4-exch84-mcond»）、jm1 marked は `marked_transJm1_ns`（本ファイル、`§6.3` 許容化 chain）。

## 残差（named Prop + needs）

Isabelle の深い正則性エンジン `cfbx_reg`（`crx_d4a_dispatch`/`crg_d4a_trunk`/`slx37_regSP_uncond`）
と condIV admeq 隅エンジンは Lean 未移植・単一ファイルの範囲外のため、named Prop として残す:
- `NestScbD4aTransport_ns` = `cpx_d4a_all` (layerB/pss_wip.thy:98511)。
- `NestScbCornerTriple_ns` = condIV admeq 隅 (`s84x_jm3 M = transJm1 M`) の三つ組。

- 依存（すべてビルド済み・committed at main d96fb0b）: «8».«8.4-exch84-scbdecomp»
  （`Exch84_nestScbTriple` def・`s84x_N`/`s84x_Np`/`s84x_jm2`/`s84x_jm3`・`transC1`/`transC2`・
  `STPS_RTPS`/`RTPS_TPS`）、«8».«8.4-exch84-slicepkg»（`ltJ_or_IVadmeq_sp`）、
  «8».«8.4-exch84-mcond»（`Regs_jm3Marked_holds`）、«7».«7.4-Mark-nextAdm»
  （`Mark_nest_common_marked`）、«7».«7.3-Mark-rightmost2»（`m_7_3_Mark_rightmost2`）、
  «7».«7.4-Mark-order»（`Mark_order`）、«7».«7.2-scb-triviality»
  （`scb_decomposition_triviality`）、«7».«7.4-RightNodes-Mark»（`Mark_leftend_form_proper`）、
  «7».«7.4-Mark-Trans-repr»（`Mark_Trans_repr`/`seg_Pred_eq`）、«7».«7.4-Adm-nextAdm»
  （`adm_row1_ancestry`/`row1_implies_row0`）、«6».«6.6-P-condAB»（`mono_hasParent_row0`）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  ltJ 枝の nest エンジン `nestDec2_ltJ_ns` を完全証明。`Exch84_nestScbTriple` を
  `NestScbD4aTransport_ns` + `NestScbCornerTriple_ns` の 2 残差に narrowing
  （house pattern `exch84_nestScbTriple_holds`）。
- 訂正: なし。
- Private helper suffix: `_ns`。
-/

namespace PSS

/-! ## 1. 残差 named Prop（Isabelle `cpx_d4a_all` / condIV admeq 隅） -/

/-- 残差: d4a 転送（Isabelle `cpx_d4a_all` (layerB/pss_wip.thy:98511)）。
共通 `(u1, v1)` を持つ `dP`（`Trans (Pred (s84x_N M))` の scb 分解、頭 `Dsym(M₁,ⱼ₋₃)`）から
`d4a`（`Trans (Pred (s84x_Np M))` の scb 分解、頭 `Dsym(M₁,ⱼ₋₂)`）を作る。
`cfbx_reg` 正則性エンジン（`crx_d4a_dispatch`/`crg_d4a_trunk`/`slx37_regSP_uncond`）消費のため未移植。 -/
def NestScbD4aTransport_ns : Prop :=
  ∀ (M : PS) (u1 v1 : List Sym), STPS M → monoT M = true →
    hasParent M 1 (Lng M - 1) = true → 1 < Lng M - 1 →
    (transCondIII M = true ∨ transCondIV M = true) →
    scb_decomp (Trans (Pred (s84x_N M)))
      (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC1 M)) v1 →
    scb_decomp (Trans (Pred (s84x_Np M)))
      (Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC1 M)) v1

/-- 残差: condIV admeq 隅（`s84x_jm3 M = transJm1 M`、`ltJ_or_IVadmeq_sp` の `Or.inr` 枝）の
三つ組。出力型は `Exch84_nestScbTriple` の結論そのもの。隅エンジン（Isabelle
layerB/pss_wip.thy:78636 近傍の `jm3eq` ルート）は Lean 未移植のため named Prop。 -/
def NestScbCornerTriple_ns : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → transCondIV M = true → Adm M (s84x_jm2 M) = transJm1 M →
    ∃ u1 v1 : List Sym,
      scb_decomp (Trans (Pred (s84x_N M)))
        (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC1 M)) v1 ∧
      scb_decomp (Trans (s84x_N M))
        (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC2 M)) v1 ∧
      scb_decomp (Trans (Pred (s84x_Np M)))
        (Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC1 M)) v1

/-! ## 2. 補助（`s84d_jm1_Marked` / `s84c2_seg_butlast` の Lean 語彙移植、完全証明） -/

/-- Isabelle `s84d_jm1_Marked` (layerB/pss_wip.thy:58808): 第2基点 `j₋₁ = transJm1 M` は
`M` 側でも marked 列であり、最終列より真に左。`§6.3` 許容化 chain の再展開。 -/
private theorem marked_transJm1_ns (M : PS) (hR : RTPS M) (hmono : monoT M = true)
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

/-- Isabelle `s84c2_seg_butlast` (layerB/pss_wip.thy:54216): `dropLast (seg M a b) = seg M a (b-1)`。 -/
private theorem seg_dropLast_ns (M : PS) (a b : ℕ) (hb : 1 ≤ b) :
    (seg M a b).dropLast = seg M a (b - 1) := by
  apply List.ext_getElem
  · simp only [List.length_dropLast, length_seg]; omega
  · intro i h1 h2
    simp only [List.getElem_dropLast, seg, List.getElem_map, List.getElem_range']

/-! ## 3. ltJ 枝の nest エンジン（Isabelle `s84d_dec2_nest_scb` の存在形、完全証明） -/

/-- Isabelle `s84d_dec2_nest_scb` (layerB/pss_wip.thy:58991) の存在形（`ex1` の一意性は
`Exch84_nestScbTriple` に不要）。`ltJ`(`s84x_jm3 M < transJm1 M`) の下で共通 `(u1, v1)` を持つ
dP+d2 を構成する。 -/
private theorem nestDec2_ltJ_ns (M : PS) (hST : STPS M) (hmono : monoT M = true)
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
  -- 基点情報
  obtain ⟨mM3, _jm3le, _jm2lt⟩ := Regs_jm3Marked_holds M hMR hMT hp
  obtain ⟨mM1, jm1lt⟩ := marked_transJm1_ns M hMR hmono hj1
  have jm3lt : s84x_jm3 M < Lng M - 1 := lt_trans hltJ jm1lt
  -- `transT1 M ≠ 0_B`（`m_7_3_Mark_rightmost2` の前提）
  have hLP : Lng (Pred M) = Lng M - 1 := by simp [Pred, Nat.not_le.mpr hlen]
  have nzP : zeroT (Pred M) = false := by simp [zeroT, hLP]; omega
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
  -- reprP: `Mark (Pred M) (s84x_jm3 M) = Trans (Pred (s84x_N M))`
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
    rw [seg_dropLast_ns M (s84x_jm3 M) (Lng M - 1) (by omega), harg]
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
  -- 目的の 2 分解に書き換え
  rw [reprP, c1v] at dP
  rw [reprM, rm2] at dM
  exact ⟨s', b, dP, dM⟩

/-! ## 4. house pattern による `Exch84_nestScbTriple` の discharge -/

/-- house-pattern discharge: `Exch84_nestScbTriple`（«8».«8.4-exch84-scbdecomp»:362）を
2 残差に narrowing。`ltJ_or_IVadmeq_sp` で二分岐し、ltJ 枝は完全証明 `nestDec2_ltJ_ns`＋
d4a 転送残差 `NestScbD4aTransport_ns`、admeq 隅は `NestScbCornerTriple_ns`。 -/
theorem exch84_nestScbTriple_holds
    (hD4a : NestScbD4aTransport_ns) (hCorner : NestScbCornerTriple_ns) :
    Exch84_nestScbTriple := by
  intro M hST hmono hp hj1 hcond
  rcases ltJ_or_IVadmeq_sp M hST hmono hp hj1 hcond with hltJ | ⟨hIV, hadmeq⟩
  · -- ltJ 枝: nest エンジン（dP+d2）＋ d4a 転送
    obtain ⟨u1, v1, dP, d2⟩ := nestDec2_ltJ_ns M hST hmono hp hj1 hltJ
    have d4a := hD4a M u1 v1 hST hmono hp hj1 hcond dP
    exact ⟨u1, v1, dP, d2, d4a⟩
  · -- admeq 隅: 隅エンジン残差から三つ組を直接
    exact hCorner M hST hmono hp hj1 hIV hadmeq

#print axioms exch84_nestScbTriple_holds

end PSS
