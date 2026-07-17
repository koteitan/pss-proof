import «6».«6.6-reduced-fseq»
import «6».«6.2-P-fseq»
import «5».«5.3-pred-is-oper1»
import PSS.Standard
import PSS.Red
import PSS.Mono
import PSS.Trans

/-!
# §8.4 補題（条件(III)か(IV)の下での基本列の基本性質）part (1)

- 原文: `tmp/content.md` 5000（補題（条件(III)か(IV)の下での基本列の基本性質））の (1)。
  すなわち `j₁ = Lng M - 1`、`j₋₂ = parent M 1 j₁` として
  `M[n] = M[n+1][1]^{j₁-j₋₂}`。
- 訂正: なし。本補題に触れる訂正は存在しない（A30 は §8.4 の別補題
  「条件(III)～(V)の下での右端の置き換えと`Trans`の関係」part (3)、A31 は §8.4 の別補題
  「条件(III)～(VI)の下での展開規則の基本性質」part (5-3) が対象。part (2) に付いていた
  A33 は撤回済みで `corrections.md` に存在しない）。
- Isabelle: 逐語形は `p_8_4_oper_basic`（`isabelle/pss_paper.thy:2017`、`sorry`）。
  本ファイルが移植するのはその第 (1) 主張で、証明は
  `m_8_4_oper_basic_part1`（`isabelle/layerB/pss_wip.thy:13897`）。
  補助は `m_8_4_oper_genform`（同 :13821）＝タイル展開、
  `m_8_4_oper_Suc_append`（同 :13864）＝`M[n+1] = M[n] @ B`、
  `m_8_4_oper1_funpow_take`（同 :13779）＝`[1]` の反復が末尾切り落としであること。
- 依存: `6.6-reduced-fseq`（`oper_tiling_expand`／`length_oper_tiling`
  ＝ Isabelle の `m_8_4_oper_genform` に対応）、`6.2-P-fseq`
  （`hasParent_next_fseq`／`nextR_implies_row0` ＝ `j₋₂ < j₁`）、
  `5.3-pred-is-oper1`（`pred_is_oper1` ＝ `Pred X = X[1]`）。
- 状態: ✅ 証明済（sorry 0）。ただし本ファイルは原文補題の part (1) のみ。
  part (2)/(3) は本ファイルの scope 外（下記注記を参照）。

## scope について

原文補題は (1)(2)(3) の三部からなる。

* (1) — 本ファイルで証明済（`oper_basic_part1`）。
* (2) `Trans(M)[n-1] = Trans(M[n+1][1]^{j₁-1-j₋₂})` — Isabelle でも **未証明**。
  `isabelle/layerC/pss_scratch.thy:15570` 付近に障害が記録されている：part (1) より
  右辺は `M[n]` を付加ブロックの 1 成分だけ延長した列であり、これは `M[m]` の形を
  していないため、`Trans` の閉形式（`cpx_condIII_mnform` 等、すべて基本列 `M[m]`
  で添字される）がどれも評価できない。
* (3) 存在形の scb 分解 — Isabelle では `y3h_p_8_4_oper_basic`
  （`isabelle/layerC/pss_scratch.thy:15526`）で証明済だが、その証明は layerC の
  巨大な §8.4 corpus（`d4vx_core`／`s84x_s1`／`cpx_condIV_exchange_uncond`／
  `y3h_LbaseH_uncond` ほか）に依存しており、単一ファイルへの移植の対象外。

数値検証: `python/_wd84_operbasic_audit.py`（`diagSeq` の `oper` 軌道＝真の
`ST_PS` ホスト 813 例のうち仮定を満たす 48 例、`n = 1..5` の 240 例すべてで part (1)
が成立、反例 0）。

## 証明の構造（Isabelle 版のまま）

`j₁ = Lng M - 1`、`j₀ = j₋₂ = parent M 1 j₁`、`w = j₁ - j₀` とする。条件(III)/(IV)
はいずれも `M_{1,j₁} > 0` を含むので `i₁ = idx1 M j₁ = 1` となり、`oper` のタイル分岐
が確定する。そこで

1. `oper_tiling_expand` を `n` と `n+1` に適用し、`List.range (n+1) = List.range n ++ [n]`
   で分割して `M[n+1] = M[n] ++ Bₙ`、`Lng Bₙ = w` を得る（`oper_succ_append_ob`）。
2. `[1]` は `Pred`（`pred_is_oper1`）なので、その `w` 回反復は末尾 `w` 個の切り落とし
   `X.take (Lng X - w)` に等しい（`oper1_funpow_take_ob`、`k` についての帰納）。
3. `Lng (M[n]) = j₀ + n·w > 0`（`length_oper_tiling`、`n ≥ 1` かつ `w > 0`）なので
   `w < Lng (M[n+1])` であり、1. と 2. を合わせて
   `[1]^{w}(M[n+1]) = (M[n] ++ Bₙ).take (Lng (M[n])) = M[n]`。

仮定 `M ∈ ST_PS`／`M ∈ PT_PS` は原文の主張に合わせて残してあるが、part (1) の証明
自体はこれらを使わない（Isabelle 版は `M[n] ≠ ()` を出すためだけに使っており、
本移植では `length_oper_tiling` の値 `j₀ + n·w` から直接従う）。
-/

namespace PSS

/-! ## 補助 -/

/-- Isabelle `m_8_4_oper1_funpow_take`: `T_PS` の列に `[1]` を `k` 回
（`k < Lng X`）適用すると末尾 `k` 個が落ちる。各段は `Pred` である
（`pred_is_oper1`）。 -/
private theorem oper1_funpow_take_ob :
    ∀ (k : ℕ) (X : PS), TPS X → k < Lng X →
      (fun N => oper N 1)^[k] X = X.take (Lng X - k) := by
  intro k
  induction k with
  | zero => intro X _ _; simp
  | succ k ih =>
    intro X hX hk
    have hlen : 1 < Lng X := by omega
    have hpred : Pred X = X.take (Lng X - 1) := by
      simp [Pred, Nat.not_le_of_lt hlen, List.dropLast_eq_take]
    have hlenP : Lng (Pred X) = Lng X - 1 := by
      rw [hpred]; simp
    have hPT : TPS (Pred X) := by
      have : 0 < Lng (Pred X) := by rw [hlenP]; omega
      exact List.ne_nil_of_length_pos this
    -- `hlenP` を先に書き換える。`hpred` を先にすると `Lng (Pred X)` の中まで
    -- 書き換わって `Lng X` と `X.length` が omega の別原子に割れる。
    rw [Function.iterate_succ_apply, ← pred_is_oper1 X hX hlen,
      ih (Pred X) hPT (by omega), hlenP, hpred, List.take_take]
    congr 1
    omega

/-- Isabelle `m_8_4_oper_Suc_append`: タイル分岐では `M[n+1]` は `M[n]` を長さ
`j₁ - j₀` のブロック 1 枚で延長したものである。`List.range (n+1) = List.range n ++ [n]`
の分割そのもの。 -/
private theorem oper_succ_append_ob (M : PS) (n : ℕ)
    (hlast : 1 < Lng M)
    (hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0))
    (hp : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true) :
    ∃ B : PS, oper M (n + 1) = oper M n ++ B ∧
      Lng B = (Lng M - 1) - parent M (idx1 M (Lng M - 1)) (Lng M - 1) := by
  let j₁ := Lng M - 1
  let i₁ := idx1 M j₁
  let j₀ := parent M i₁ j₁
  let w := j₁ - j₀
  let d₀ := if 0 < i₁ then entry M 0 j₁ - entry M 0 j₀ else 0
  let d₁ := if 1 < i₁ then entry M 1 j₁ - entry M 1 j₀ else 0
  let blk : ℕ → PS := fun k =>
    (List.range' j₀ w).map (fun j => (entry M 0 j + k * d₀, entry M 1 j + k * d₁))
  have hn : oper M n = M.take j₀ ++ (List.range n).flatMap blk := by
    simpa [blk, j₁, i₁, j₀, w, d₀, d₁] using oper_tiling_expand M n hlast hzero hp
  have hsn : oper M (n + 1) = M.take j₀ ++ (List.range (n + 1)).flatMap blk := by
    simpa [blk, j₁, i₁, j₀, w, d₀, d₁] using
      oper_tiling_expand M (n + 1) hlast hzero hp
  refine ⟨blk n, ?_, by simp [blk, w, j₁, i₁, j₀]⟩
  rw [hsn, hn, List.range_succ, List.flatMap_append, ← List.append_assoc]
  simp [blk]

/-! ## 原文補題 part (1) -/

/-- **§8.4 補題（条件(III)か(IV)の下での基本列の基本性質）part (1)**
（原文 `tmp/content.md` 5000、Isabelle `p_8_4_oper_basic` 第 (1) 主張、
`isabelle/pss_paper.thy:2017`）。

`j₁ = Lng M - 1`、`j₋₂ = parent M 1 j₁` として `M[n] = M[n+1][1]^{j₁-j₋₂}`。 -/
theorem oper_basic_part1 (M : PS) (n : ℕ)
    (hST : STPS M) (hR : RTPS M) (hmono : monoT M = true) (hn : 1 ≤ n)
    (hp : hasParent M 1 (Lng M - 1) = true)
    (hj₁ : 1 < Lng M - 1)
    (hcond : transCondIII M = true ∨ transCondIV M = true) :
    oper M n =
      (fun N => oper N 1)^[(Lng M - 1) - parent M 1 (Lng M - 1)] (oper M (n + 1)) := by
  -- 条件(III)/(IV) はいずれも `M_{1,j₁} > 0` を含む
  have he1 : 0 < entry M 1 (Lng M - 1) := by
    rcases hcond with h | h
    · unfold transCondIII at h
      simp only [lastIdx, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1.1
    · unfold transCondIV at h
      simp only [lastIdx, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1.1
  have hi₁ : idx1 M (Lng M - 1) = 1 := by simp [idx1, he1]
  have hlast : 1 < Lng M := by omega
  have hzero : ¬(entry M 0 (Lng M - 1) = 0 ∧ entry M 1 (Lng M - 1) = 0) := by
    rintro ⟨-, h2⟩; omega
  have hp' : hasParent M (idx1 M (Lng M - 1)) (Lng M - 1) = true := by
    rw [hi₁]; exact hp
  -- `j₀ = j₋₂ < j₁`、よって `w > 0`
  have hj₀lt : parent M 1 (Lng M - 1) < Lng M - 1 :=
    (nextR_implies_row0 M 1 (parent M 1 (Lng M - 1)) (Lng M - 1)
      (hasParent_next_fseq M 1 (Lng M - 1) hp)).1
  -- `M[n+1] = M[n] ++ B`、`Lng B = w`
  obtain ⟨B, hB, hBlen⟩ := oper_succ_append_ob M n hlast hzero hp'
  rw [hi₁] at hBlen
  -- `Lng (M[n]) = j₀ + n·w > 0`
  have hlenN : Lng (oper M n) =
      parent M 1 (Lng M - 1) + n * ((Lng M - 1) - parent M 1 (Lng M - 1)) := by
    have := length_oper_tiling M n hlast hzero hp'
    simpa [hi₁] using this
  have hpos : 0 < Lng (oper M n) := by
    have hw : 0 < (Lng M - 1) - parent M 1 (Lng M - 1) := by omega
    have : (Lng M - 1) - parent M 1 (Lng M - 1)
        ≤ n * ((Lng M - 1) - parent M 1 (Lng M - 1)) :=
      Nat.le_mul_of_pos_left _ hn
    omega
  have hlenSn : Lng (oper M (n + 1)) =
      Lng (oper M n) + ((Lng M - 1) - parent M 1 (Lng M - 1)) := by
    rw [hB]; simp [hBlen]
  have hTPS : TPS (oper M (n + 1)) := by
    -- `Lng X` と `X.length` は omega の別原子。defeq 橋を明示する。
    have hlp : 0 < Lng (oper M (n + 1)) := by omega
    exact List.ne_nil_of_length_pos hlp
  have hklt : (Lng M - 1) - parent M 1 (Lng M - 1) < Lng (oper M (n + 1)) := by omega
  -- `[1]^{w}` は末尾 `w` 個の切り落とし
  rw [oper1_funpow_take_ob _ (oper M (n + 1)) hTPS hklt]
  have hsub : Lng (oper M (n + 1)) - ((Lng M - 1) - parent M 1 (Lng M - 1))
      = Lng (oper M n) := by omega
  rw [hsub, hB]
  simp

#print axioms oper_basic_part1

end PSS
