import «8».«8.4-rightmost-replace-Trans»

/-!
# §8.4 補題（右端置き換えと `Trans`）訂正 A30 形 `Rightmost84ReplaceCorrected` の discharge

- 原文: `tmp/content.md` §8.4「補題（条件(III)～(V)の下での右端の置き換えと `Trans`
  の関係）」(4265)。訂正 A30 後の形は `«8».«8.4-rightmost-replace-Trans»` の
  named Prop `Rightmost84ReplaceCorrected`（同ファイル :105）で露出済み。
- 逐語: **なし**。`isabelle/pss_paper.thy`:1945 は本補題を **DEFERRED**。その内容
  （`Trans(N')` を中心 `D_{M₁,j₁} 0`、`Trans(L')` を中心 `D_{M₁,j₋₂} 0` で
  **同一** scb 文脈 `(s,b)` で分解する）は §8.4 の値クラスタ
  `s84c1_*`/`s84d_*`（`isabelle/layerB/pss_wip.thy`:52658–54005）— とくに
  `s84d_c2hole` / `s84d_corepair_shared` / `s84d_corepair_nested` の入れ子
  c2-hole エンジン — がカバーする。
- 本ファイルの寄与:
  * **一意性の完全 discharge**: `∃!` の一意部を `scb_unique_decomp_unconditional`
    （固定中心 `D_{M₁,j₁} 0` から `(s,b)` は一意）で無条件に閉じる
    (`rightmost84ReplaceCorrected_of_exists`)。存在部 1 本
    (`Rightmost84ReplaceExists`) へ 1:1 還元する。
  * 存在部の**非空虚性**を具体 host `hostM30_rr`（同ファイル）で機械確認。
- 依存（すべてビルド済み・committed at 19dc5fd）:
  «8».«8.4-rightmost-replace-Trans»（`Rightmost84ReplaceCorrected`/`rrLp`/
  `s84x_Np`/`s84x_jm2`/`hostM30_rr`/`rr84_corrected_holds_rr`）、
  «7».«7.2-scb-unique»（`scb_unique_decomp_unconditional`、推移的 import）。
- 数値検証: `python/trans_model.py` + `python/red_model.py`。STPS×monoT×
  hasParent₁(last)×`j₋₂+1<j₁` の下で「`Trans(N')` と `Trans(L')` が中心
  `D_{v₁}0`/`D_{v₂}0` の周りで共有 `(s,b)` を持つ」ことを 280/280 で確認
  （`scratchpad/probe_rr.py`：`share_ok=280/280`）。同 form の上端 `addBT`
  露出は condIII で崩れる（161/280）ため、還元は raw-existence 形で行う。
- ツリー項目: 補題（条件(III)～(V)の下での右端の置き換えと `Trans` の関係）(§8.4)。
- 状態: 🤖 GREEN（sorry 0）。一意部は無条件で閉じ、残差は存在部
  `Rightmost84ReplaceExists` 1 本（Isabelle DEFERRED、§8 停止性の臨界パス外）。
- Private suffix: `_rc`。
-/

namespace PSS

/-! ## 存在部の named Prop（唯一の残差）

`Rightmost84ReplaceCorrected` の `∃!` から一意部を剥がした純存在。中心が固定された
scb 分解の `(s,b)` は `scb_unique_decomp_unconditional` で一意なので、`∃!` はこの
`∃` と論理的に等価（下の `rightmost84ReplaceCorrected_of_exists` が示す）。 -/
def Rightmost84ReplaceExists : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    s84x_jm2 M + 1 < Lng M - 1 →
    ∃ sb : List Sym × List Sym,
      scb_decomp (Trans (s84x_Np M)) sb.1
          (flatBT (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)) sb.2 ∧
      scb_decomp (Trans (rrLp M)) sb.1
          (flatBT (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero)) sb.2

/-! ## 一意部の無条件 discharge

`∃!` の一意性は第 1 連言（中心 `D_{M₁,j₁} 0` が固定）だけで決まる。固定中心の
scb 分解では前置 `s` と右括弧尾 `b` が一意（`scb_unique_decomp_unconditional`）。 -/
theorem rightmost84ReplaceCorrected_of_exists
    (h : Rightmost84ReplaceExists) : Rightmost84ReplaceCorrected := by
  intro M hST hmono hp hrng
  obtain ⟨sb, hconj⟩ := h M hST hmono hp hrng
  refine ⟨sb, hconj, ?_⟩
  intro y hy
  have hu := scb_unique_decomp_unconditional (Trans (s84x_Np M))
    y.1 sb.1 (flatBT (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)) y.2 sb.2 hy.1 hconj.1
  exact Prod.ext hu.1 hu.2

/-- 逆向き（`∃!` から一意部を落とす）は自明。よって残差 `Rightmost84ReplaceExists`
は `Rightmost84ReplaceCorrected` と**論理的に等価**であり、還元で失われた内容は
存在部だけであることが確定する。 -/
theorem rightmost84ReplaceExists_of_corrected
    (h : Rightmost84ReplaceCorrected) : Rightmost84ReplaceExists := by
  intro M hST hmono hp hrng
  obtain ⟨sb, hconj, _⟩ := h M hST hmono hp hrng
  exact ⟨sb, hconj⟩

/-- 残差の正確な特徴づけ: `Rightmost84ReplaceCorrected ↔ Rightmost84ReplaceExists`。 -/
theorem rightmost84ReplaceCorrected_iff_exists :
    Rightmost84ReplaceCorrected ↔ Rightmost84ReplaceExists :=
  ⟨rightmost84ReplaceExists_of_corrected, rightmost84ReplaceCorrected_of_exists⟩

/-! ## 存在部の非空虚性（具体 host での機械確認）

`«8».«8.4-rightmost-replace-Trans»` の `rr84_corrected_holds_rr` が、共有手術対
`(s_rr, b_rr)` で A30 host `hostM30_rr = (0,0)(1,1)(2,2)(2,1)` の両連言を同時に
満たすことを示している。`s84x_Np hostM30_rr = hostM30_rr` かつ `rrLp = s84x_Lp`
なので、これは `Rightmost84ReplaceExists` の witness をそのまま与える。 -/
theorem rightmost84Replace_nonvacuous_rc :
    ∃ sb : List Sym × List Sym,
      scb_decomp (Trans (s84x_Np hostM30_rr)) sb.1
          (flatBT (Dprin (entry hostM30_rr 1 (Lng hostM30_rr - 1) : ℕ∞) BZero)) sb.2 ∧
      scb_decomp (Trans (rrLp hostM30_rr)) sb.1
          (flatBT (Dprin (entry hostM30_rr 1 (s84x_jm2 hostM30_rr) : ℕ∞) BZero)) sb.2 :=
  rr84_corrected_holds_rr

#print axioms rightmost84ReplaceCorrected_of_exists
#print axioms rightmost84ReplaceExists_of_corrected
#print axioms rightmost84ReplaceCorrected_iff_exists
#print axioms rightmost84Replace_nonvacuous_rc

end PSS
