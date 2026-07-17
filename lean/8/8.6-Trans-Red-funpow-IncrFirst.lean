import «6».«6.5-Red-IncrFirst-invariance»
import «7».«7.3-Trans-IncrFirst-Red»

/-!
# `Red` / `Trans` の `IncrFirst` 反復不変性（funpow 版）

`IncrFirst`（行 0 の一斉 +1）を `k` 回反復しても、`Red` および `Trans` の値は
変わらない。単段版（`Red_IncrFirst`, `Trans_IncrFirst`）を `IncrFirstN` の反復
（= `IncrFirst^[k]`）に沿った素直な帰納で持ち上げたもの。§8.5 の塔および §8.6
condVI の L-塔事実 (b) が、この funpow 版を共通の前提として要求する。

- Isabelle:
  - `a1_Red_funpow_IncrFirst`  … `isabelle/pss_mechanized.thy:33745`
    （`assumes X ∈ T_PS shows Red ((IncrFirst ^^ k) X) = Red X`）
  - `Trans_funpow_IncrFirst`   … `isabelle/layerB/pss_wip.thy:10992`
    （`assumes M ∈ T_PS, Red M ∈ RT_PS shows Trans ((IncrFirst ^^ k) M) = Trans M`）
- 単段版（本ファイルが持ち上げる土台）:
  - `Red_IncrFirst`   … `lean/6/6.5-Red-IncrFirst-invariance.lean`（`m_6_5_Red_IncrFirst`）
  - `Trans_IncrFirst` … `lean/7/7.3-Trans-IncrFirst-Red.lean`（`m_7_3_Trans_IncrFirst`）
    ※ Lean の単段 `Trans_IncrFirst` は `TPS M` のみで無条件（Isabelle の
      `m_7_3_Trans_IncrFirst` は `Red N ∈ RT_PS` を要するが Lean 版は不要）。
      本 funpow 版は忠実性のため Isabelle と同じ `hRR : RTPS (Red M)` を保持する。
- `IncrFirstN` 定義: `lean/PSS/Red.lean:24`（`IncrFirstN (n+1) M = IncrFirstN n (IncrFirst M)`
  ＝ `IncrFirst^[n+1] M`）。
- 依存: `6.5-Red-IncrFirst-invariance`, `7.3-Trans-IncrFirst-Red`
- 状態: ✅ 証明済（sorry 0, 仮定 0）
-/

namespace PSS

/-- a1: 単段 `Red_IncrFirst` を反復に持ち上げる。`Red ((IncrFirst^[k]) X) = Red X`。
Isabelle `a1_Red_funpow_IncrFirst`（`pss_mechanized.thy:33745`）。 -/
theorem a1_Red_funpow_IncrFirst (M : PS) (k : ℕ) (hM : TPS M) :
    Red (IncrFirstN k M) = Red M := by
  induction k generalizing M with
  | zero => simp [IncrFirstN]
  | succ k ih =>
    have hIF : TPS (IncrFirst M) := by simpa [TPS, IncrFirst] using hM
    calc
      Red (IncrFirstN (k + 1) M) = Red (IncrFirstN k (IncrFirst M)) := by
        simp only [IncrFirstN]
      _ = Red (IncrFirst M) := ih (IncrFirst M) hIF
      _ = Red M := Red_IncrFirst M hM

/-- 単段 `Trans_IncrFirst` を反復に持ち上げる。`Trans ((IncrFirst^[k]) M) = Trans M`。
Isabelle `Trans_funpow_IncrFirst`（`layerB/pss_wip.thy:10992`）。`hRR` は忠実性のため
Isabelle と同じ形で保持する（Lean の単段版は無条件なので帰納の各段でも `hRR` は
IH へ受け渡すためだけに使う）。 -/
theorem Trans_funpow_IncrFirst (M : PS) (k : ℕ) (hM : TPS M) (hRR : RTPS (Red M)) :
    Trans (IncrFirstN k M) = Trans M := by
  induction k generalizing M with
  | zero => simp [IncrFirstN]
  | succ k ih =>
    have hIF : TPS (IncrFirst M) := by simpa [TPS, IncrFirst] using hM
    have hRRI : RTPS (Red (IncrFirst M)) := by
      rw [Red_IncrFirst M hM]; exact hRR
    calc
      Trans (IncrFirstN (k + 1) M) = Trans (IncrFirstN k (IncrFirst M)) := by
        simp only [IncrFirstN]
      _ = Trans (IncrFirst M) := ih (IncrFirst M) hIF hRRI
      _ = Trans M := Trans_IncrFirst M hM

#print axioms a1_Red_funpow_IncrFirst
#print axioms Trans_funpow_IncrFirst

end PSS
