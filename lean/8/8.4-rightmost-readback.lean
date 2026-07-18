import «8».«8.4-rightmost-exists»
import «8».«8.4-oper5-residual»

/-!
# §8.4 補題（右端置き換えと `Trans`）— 自己相似リードバック残差の露出と橋渡し

- 原文: `tmp/content.md` §8.4「補題（条件(III)～(V)の下での右端の置き換えと `Trans`
  の関係）」(4265)。`isabelle/pss_paper.thy`:1945 は本補題ごと **DEFERRED**。
- 目的（本ファイルの寄与、すべて無条件・GREEN）:
  `«8».«8.4-rightmost-exists»` の緑コア橋 `rr84_shared_of_readback` が消費する
  **2 本の自己相似リードバック値**
  * `Trans (s84x_Np M) = D_V (T2 +_B D_{M₁,j₁} 0)`（`β = M_{1,j₁} = M_{1,Lng M−1}`）
  * `Trans (rrLp M)   = D_V (T2 +_B D_{M₁,j₋₂} 0)`（`γ = M_{1,j₋₂} = M_{1,s84x_jm2 M}`）
  を **共有 `V`, `T2`** で束ねた named Prop `Rightmost84ReadbackShared` として露出し、
  それが `Rightmost84ReplaceExists`（`«8».«8.4-rightmost-replace-close»`）へ 1:1
  で還元することを無条件で示す（`rightmost84ReplaceExists_of_readback`）。House pattern:
  橋の 2 前提を named Prop の型に押し込み、存在部フィールド `rm84Exists`（＝
  `Rightmost84ReplaceExists`）を **値リードバック残差 `Rightmost84ReadbackShared`** へ
  置き換える。同時に `Rightmost84ReplaceCorrected` への合成も与える。
  追加で、ブロックされている非単項値 `Trans (rrLp M)` を塔 `s84x_L` の第2段の `Mark`
  として無条件に表す再定式化 `mark_tower2_eq_trans_rrLp` を公開する（下流の攻め口）。

- **なぜ値そのものは閉じないか（残差の核、header of `8.4-rightmost-exists` と整合）**:
  `Trans (s84x_Np M)`（`N' = seg M j₋₂ j₁` は `mono_ancestor_slice` で `monoT`）は
  `Mark_Trans_repr` ＋ `m_7_3_Mark_rightmost2` で読めるが、`Trans (rrLp M)`
  （`L' = rrLp M = s84x_Lp M` は **非単項**：A30 host で行1 = 0,1,2,0）は `Trans` の
  multi 分岐（`P M` による primary-block 分解）に落ち、Lean 側で独立計算を持たない
  `needs` 入力（`nf2x_Lpv`/`exchV_Lp_of_Np` は `Rightmost84ReplaceCorrected` から
  逆に導く循環）。加えて `D_V (T2 +_B ·)` の T2 閉形式は条件 (IV) の入れ子形
  `D_e(t₃ +_B D_{M₁,j'}(t₄ +_B D_β 0))` で崩れ、`Rightmost84ReplaceExists` の域
  （condIII/IV/V を含む）で **大域的には偽**。ゆえに値ルートは atomic であり、真の
  discharge は Isabelle の c2-hole エンジン（`s84d_*`）の移植を要する。本ファイルは
  その atomic 残差を **橋が消費する正確な形**（共有リードバック 2 値）で確定させる。

- 依存（すべてビルド済み・committed）: «8».«8.4-rightmost-exists»
  （`rr84_shared_of_readback`/`Rightmost84ReplaceExists`/`rightmost84ReplaceCorrected_of_exists`/
  `Rightmost84ReplaceCorrected`/`s84x_Np`/`rrLp`/`s84x_jm2`）、
  «8».«8.4-oper5-residual»（`oper5Residual_holds`/`s84x_L`/`s84x_ms`）。
- 状態: 🤖 GREEN（sorry 0、axioms = propext/Classical.choice/Quot.sound）。還元と塔
  再定式化は無条件。値 2 本は atomic 残差（`Rightmost84ReadbackShared`）として露出。
- Private suffix: `_rb`。
-/

namespace PSS

/-! ## 1. 共有リードバック 2 値の named Prop（橋 `rr84_shared_of_readback` の 2 前提） -/

/-- **共有自己相似リードバック残差**。`Rightmost84ReplaceExists` の各 `M` に対し、
外側 `D_V (T2 +_B ·)` を共有し最内 principal だけ `D_β 0` / `D_γ 0` で異なる 2 本の
閉形式リードバックが取れる、という主張。橋 `rr84_shared_of_readback` の 2 前提
`hNp`/`hLp` を `∃ V T2` で束ねたもの。`β = M_{1,Lng M−1}`, `γ = M_{1,s84x_jm2 M}`。 -/
def Rightmost84ReadbackShared : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    s84x_jm2 M + 1 < Lng M - 1 →
    ∃ (V : ℕ∞) (T2 : BT), T2 ∈ T_B ∧
      Trans (s84x_Np M)
          = Dprin V (addBT T2 (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)) ∧
      Trans (rrLp M)
          = Dprin V (addBT T2 (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero))

/-! ## 2. 還元：共有リードバック残差 ⟹ 存在部 `Rightmost84ReplaceExists` -/

/-- **House pattern の還元**。共有リードバック 2 値が取れれば、橋
`rr84_shared_of_readback`（scb 代数のみ・無条件）で共有 scb 文脈が機械的に構成でき、
存在部フィールド `rm84Exists`（＝ `Rightmost84ReplaceExists`）を落とせる。 -/
theorem rightmost84ReplaceExists_of_readback
    (h : Rightmost84ReadbackShared) : Rightmost84ReplaceExists := by
  intro M hST hmono hp hrng
  obtain ⟨V, T2, hT2, hNp, hLp⟩ := h M hST hmono hp hrng
  exact rr84_shared_of_readback M V T2 hT2 hNp hLp

/-- 訂正 A30 形 `Rightmost84ReplaceCorrected` への合成（一意部は既に無条件で閉じている
`rightmost84ReplaceCorrected_of_exists` を通す）。 -/
theorem rightmost84ReplaceCorrected_of_readback
    (h : Rightmost84ReadbackShared) : Rightmost84ReplaceCorrected :=
  rightmost84ReplaceCorrected_of_exists (rightmost84ReplaceExists_of_readback h)

/-! ## 3. 塔再定式化：非単項値 `Trans (rrLp M)` を第2段 `Mark` で無条件に表す

`rrLp M = s84x_Lp M`（定義的に一致）。塔エンジン `oper5Residual_holds` の葉(8)
`s84c1_Mark_L_mstar` により、ブロックされている非単項値は塔 `s84x_L` の第2段の基点
`Mark` に等しい。値ルートを直接計算する代わりの、無条件な下流攻め口。 -/
theorem mark_tower2_eq_trans_rrLp (M : PS)
    (hST : STPS M) (hmono : monoT M = true)
    (hp : hasParent M 1 (Lng M - 1) = true)
    (hrng : s84x_jm2 M + 1 < Lng M - 1) :
    Mark (s84x_L M 2) (s84x_ms M 2) = Trans (rrLp M) := by
  have hj1 : 1 < Lng M - 1 := by omega
  have hres := oper5Residual_holds M 2 hST hmono hp hj1 (by omega)
  exact hres.2.1

#print axioms rightmost84ReplaceExists_of_readback
#print axioms rightmost84ReplaceCorrected_of_readback
#print axioms mark_tower2_eq_trans_rrLp

end PSS
