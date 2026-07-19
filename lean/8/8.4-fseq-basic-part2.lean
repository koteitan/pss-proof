import «8».«8.4-fseq-basic-close»

/-!
# §8.4 補題（条件(III)か(IV)の下での基本列の基本性質）part (2) — 残差の operB 側消去

- 原文: `tmp/content.md` 5008（補題（条件(III)か(IV)の下での基本列の基本性質））part (2)。
  `j₁ = Lng M - 1`、`j₋₂ = parent M 1 j₁`、`w' = j₁ - 1 - j₋₂` として
  `Trans(M)[n-1] = Trans(M[n+1][1]^{w'})`（`Trans(M)[k] = operB (Trans M) (numBT k)`）。
- 訂正: part (2) に付いていた **A33（構造的に偽と主張）は撤回済み**で `corrections.md` に
  存在しない（part (2) は真、経験的に 130/130）。A30/A31 は §8.4 の別補題が対象で無関係。
- Isabelle: 逐語形は `p_8_4_oper_basic`（`isabelle/pss_paper.thy:2017`、`sorry`）。証明は
  `y3l_p_8_4_oper_basic_part2`＋`y3m_p_8_4_oper_basic_part2_full`
  （`isabelle/layerC/pss_scratch.thy:18777` / `:19105`）。両者は等式
  `operB (Trans M) (numBT (n-1)) = Trans (s84x_L M n)` を、共通 scb 証人
  `(u0,…,v0)` の下で **operB 側閉形式 `fOp'`（Isabelle `d13x_fseq_condIII`）** と
  **L 切片閉形式 `cL`（Isabelle `y3i_L6_various_scb_IIIIV` → `m_8_4_various_scb_IIIIV_from_slice`）**
  が同一 flat 文字列であること（`feq`）から得る。さらに
  `s84x_L M n = ((λN. N[1])^{w'})(M[n+1])`（Isabelle `y3l_L_eq_op1pow`）。

## 本ファイルの内容（親残差 `Oper84BasicPart2Residual` の operB 側消去）

親（`8.4-fseq-basic-close:223`）は part (2) を **単一の flat 一致残差**
`Oper84BasicPart2Residual`＝
`flatBT (operB (Trans M) (numBT (n-1))) = flatBT (Trans ((λN. oper N 1)^{w'} (oper M (n+1))))`
として括り出している。この一致は
  (A) **operB 側**の閉形式 `flatBT (operB (Trans M) (numBT (n-1)))
        = s₁ ++ flatBP (D e₃ (coreTower ins 0_B n)) ++ b₁`（Isabelle `fOp'`）と、
  (B) **L 切片側**の閉形式 `flatBT (Trans ((λN. oper N 1)^{w'} (oper M (n+1))))
        = s₁ ++ flatBP (D e₃ (coreTower ins 0_B n)) ++ b₁`（Isabelle `cL`）
の二本柱からなる。

本ファイルは **(A) を無条件に消去する**（`Exch84_condIIIIV_producer` を
`8.4-fseq-basic-close` の `oper_basic_part3_uncond` と同一の公開連鎖
`Exch84_condIIIIV_producer_holds (…cornerNpSliceValue_holds_cnv)` から供給し、その `fO`
を index `n-1` で読む。`(n-1)+1 = n` の算術のみ）。残るのは (B) ＝ L 切片の `Trans`
閉形式だけで、これを producer 座標（`ins,e₃,s₁,b₁` を仮定として持つ形）で名前付き残差
`L6TransSliceClosed_p2` に括り出す。これは Isabelle `m_8_4_various_scb_IIIIV_from_slice`
（`isabelle/layerB/pss_wip.thy:60034`）の `flatBT (Trans (s84x_L M n))` 連言そのもの
（`s84x_L M n` を原文 §8.4 の `(λN. oper N 1)^{w'}(M[n+1])` 形で表記、`y3l_L_eq_op1pow` 分
を verbatim に保持）。この L 切片エンジン（core-tower 切片帰納＋scb surgery）は本移植の
単一ファイル外で未移植のため、single named residual として残す。

- 状態: **green（rc=0）、sorry 0**。親残差 `Oper84BasicPart2Residual` を
  `L6TransSliceClosed_p2` modulo で成立（operB 側 (A) は無条件に消去済み、
  producer 座標で L 切片側 (B) だけを残す）。
- 停止性連鎖には不要（`p_8_7_termination` は無条件・独立）。原文カバレッジのための逐語形。
-/

namespace PSS

/-- **L 切片の `Trans` 閉形式**（producer 座標）＝親残差 `Oper84BasicPart2Residual`
から operB 側閉形式を消去した後に残る唯一の brick。

Isabelle `m_8_4_various_scb_IIIIV_from_slice`（`isabelle/layerB/pss_wip.thy:60034`）の
`flatBT (Trans (s84x_L M n)) = u0 @ D e₃ # concat(replicate n …) @ [Z] @ concat(replicate n …) @ v0`
連言に対応する。ここでは producer（`Exch84_condIIIIV_producer`、`8.4-Trans-fseq-condIII-IV`）
の出力 `(ins, A0, e3, ub, s0, b0, s1, b1)` とその全性質（`hflat`/`hb0`/`hb1`/`fO`/`fM`/
`base0`/`base1`/`Lbase`）を仮定として持ち込み、L 切片
`(λN. oper N 1)^{w'}(oper M (n+1))`（`w' = (Lng M - 1) - 1 - parent M 1 (Lng M - 1)`）の
`Trans` flat が operB 側と同一の producer 閉形式
`s1 ++ flatBP (D e3 (coreTower ins 0_B n)) ++ b1` に一致することを主張する
（Isabelle 証明では `cL` と `fOp'` が同一文字列であること＝`feq`）。 -/
def L6TransSliceClosed_p2 : Prop :=
  ∀ (M : PS) (n : ℕ) (ins : BT → BT) (A0 : BT) (e3 ub : ℕ∞)
    (s0 b0 s1 b1 : List Sym),
    STPS M → monoT M = true → 1 ≤ n →
    hasParent M 1 (Lng M - 1) = true → 1 < Lng M - 1 →
    (transCondIII M = true ∨ transCondIV M = true) →
    (∀ X, flatBT (ins X) = s0 ++ Sym.dsym ub :: flatBT X ++ b0) →
    (∀ x ∈ b0, x = Sym.rp) →
    (∀ x ∈ b1, x = Sym.rp) →
    (∀ k, flatBT (operB (Trans M) (numBT k))
      = s1 ++ flatBP (.db e3 (coreTower_e34 ins BZero (k + 1))) ++ b1) →
    (∀ m, 1 ≤ m → flatBT (Trans (oper M m))
      = s1 ++ flatBP (.db e3 (coreTower_e34 ins A0 (m - 1))) ++ b1) →
    lessBT (Dprin ub BZero) A0 = true →
    lessBT A0 (ins (Dprin ub BZero)) = true →
    leBT (Dprin ub BZero) (ins BZero) = true →
    flatBT (Trans ((fun N => oper N 1)^[(Lng M - 1) - 1 - parent M 1 (Lng M - 1)]
        (oper M (n + 1))))
      = s1 ++ flatBP (.db e3 (coreTower_e34 ins BZero n)) ++ b1

/-- **§8.4 補題 part (2)**（原文 `tmp/content.md` 5008、Isabelle
`y3m_p_8_4_oper_basic_part2_full`、`isabelle/layerC/pss_scratch.thy:19105`）を
`L6TransSliceClosed_p2` modulo で供給。

operB 側閉形式は `Exch84_condIIIIV_producer` を `oper_basic_part3_uncond` と同一の公開連鎖で
無条件に供給し、その `fO` を index `n-1`（`(n-1)+1 = n`）で読んで消去する。残るは
producer 座標での L 切片閉形式 `L6TransSliceClosed_p2` だけ。 -/
theorem oper84BasicPart2_holds (hL6 : L6TransSliceClosed_p2) :
    Oper84BasicPart2Residual := by
  intro M n hST hmono hn hp hj₁ hcond
  -- `Exch84_condIIIIV_producer` を無条件公開連鎖から供給（`oper_basic_part3_uncond` と同一）
  have hprod : Exch84_condIIIIV_producer :=
    Exch84_condIIIIV_producer_holds (Exch84_condIIIIV_pkg_holds
      (exch84slicepkg_of_cornerReadouts_nc2
        (cornerCoreReadouts_of_residual cornerNpSliceValue_holds_cnv)))
  obtain ⟨ins, A0, e3, ub, s0, b0, s1, b1,
    hflat, hb0, hb1, fO, fM, base0, base1, Lbase⟩ := hprod M hST hmono hj₁ hcond hp
  -- (A) operB 側閉形式（`fO` at `k = n-1`、`(n-1)+1 = n`）
  have hL : flatBT (operB (Trans M) (numBT (n - 1)))
      = s1 ++ flatBP (.db e3 (coreTower_e34 ins BZero n)) ++ b1 := by
    have h := fO (n - 1)
    rwa [(by omega : (n - 1) + 1 = n)] at h
  rw [hL]
  -- (B) L 切片閉形式（producer 座標の残差）
  exact (hL6 M n ins A0 e3 ub s0 b0 s1 b1 hST hmono hn hp hj₁ hcond
    hflat hb0 hb1 fO fM base0 base1 Lbase).symm

#print axioms oper84BasicPart2_holds

end PSS
