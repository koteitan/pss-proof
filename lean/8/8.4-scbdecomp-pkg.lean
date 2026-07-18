import «8».«8.4-slicepkg-residuals»
import «8».«8.4-d4a-trunk»

/-!
# §8.4 交換パッケージ共通鍵 `Exch84_scbDecompPkg` — 全域は偽・ltJ 域は無条件

- 原文: `tmp/content.md` §8.4（条件(III)/(IV) の下での `Trans` と基本列の交換関係）。
  逐語形 = `p_8_4_Trans_oper_exchange` (isabelle/pss_paper.thy:1909)。
- ミッション: `Exch84_scbDecompPkg`（«8».«8.4-exch84-base1p»:370、= Isabelle
  `cpx_various_scb_IIIIV` の `c2_1`/`c3_1`/`c4_1`/`c5_1`）を **outright** discharge し、
  `Base0_condIIIIV` / `Base1p_condIIIIV` の 2 脚を解禁する。「NOW AVAILABLE: FULL d4a
  transport 無条件（`nestScbD4aTransport_dk`）＋ ltJ engine」で
  `Exch84_scbDecompPkg_of_triple` ＋ ltJ/corner dispatch ＋ `nestScbD4aTransport_dk` が
  合成して pkg を outright に閉じられるか、を CHECK せよ、というもの。

## CHECK の結論（重要・honesty）

**`Exch84_scbDecompPkg`（無ガード）は偽であり、outright には閉じられない。**
これは stale note ではなく、ビルド済み・committed の機械反例に基づく確定事実である:

* `NestScbCornerTriple_ns_refuted_cn : ¬ NestScbCornerTriple_ns`
  （«8».«8.4-exch84-corner»、main 7443c15、witness `M = (0,0)(1,1)(2,2)(2,1)`、公理 propext のみ）。
* 隅（condIV ∧ admeq, `s84x_jm3 M = transJm1 M`）では切片が潰れ
  `Trans (Pred (s84x_N M)) = transC1 M`（collapse, `cornerCollapse_holds_cr`）となるため、
  pkg が要求する `dP = scb_decomp (Trans (Pred (s84x_N M))) (Dsym e₃ :: u1)
  (flatBT (transC1 M)) v1` は非空 prefix `Dsym e₃ :: u1` が inner を自分自身の左に置く形になり
  長さで矛盾する。これは `8.4-corner-redesign` の note にも明記:
  「`Exch84_scbDecompPkg`（base1p:370）— c2/c3 を束ねるため隅で偽」。

`nestScbD4aTransport_dk`（d4a 転送）や ltJ engine がいくら無条件でも、pkg が結論に置く c2/c3
（dP/d2）は隅で退化するので、**転送の可用性とは独立に pkg は偽**である。したがって
ミッションが想定した「`Exch84_scbDecompPkg_of_triple ∘ dispatch ∘ nestScbD4aTransport_dk` で
outright discharge」は原理的に不可能。`Exch84_scbDecompPkg_of_triple` は
`Exch84_nestScbTriple`（同じく隅で偽、`exch84_nestScbTriple_false_cr`）を仮定に取るため、
それ自身は valid だが live な供給者を持たない。

## 本ファイルの成果物

1. **`Exch84_scbDecompPkg_refuted_sp2 : ¬ Exch84_scbDecompPkg`**（無条件）。
   pkg の隅 witness から `NestScbCornerTriple_ns`（= pkg の {dP,d2,c5} と同型の三つ組）を
   組めてしまうことを示し、ビルド済み反例 `NestScbCornerTriple_ns_refuted_cn` に帰着する。
   これでミッションの CHECK に確定的な否定回答を与える。

2. **`Exch84_scbDecompPkg_ltJ_sp2`（def）＋ `exch84ScbDecompPkgLtJ_holds_sp2`（無条件）**。
   pkg に Isabelle `cpx_various_scb_IIIIV` の脱落仮定 `ltJ : s84x_jm3 M < transJm1 M` を
   再付与した「正しい pkg」は、まさにミッションが期待した合成で **無条件に閉じる**:
   ltJ engine `exch84_nestScbTriple_ltJ_holds_cr`（«8».«8.4-corner-redesign»）に
   今や無条件の `nestScbD4aTransport_dk`（«8».«8.4-d4a-trunk»）を渡して dP/d2/c5 を得、
   c4 = `transC2HoleDecomp_holds_sr`（«8».«8.4-slicepkg-residuals»、公開・無条件）、
   `transT1 ≠ 0_B` は `Trans_Mark_invariant` から re-derive。**pkg の「真の部分」全体が
   ltJ 域では無条件に閉じている**ことの証拠（= どこまで合成が効くかのミッション CHECK の
   肯定側）。ただし隅を含む全域には拡張できない（§1 の反例）。

## `Base0_condIIIIV` / `Base1p_condIIIIV` について（配線指示）

pkg が偽なので、`Base0_A0bridge_holds (pkg)` / `Base1p_condIIIIV_holds (pkg …)`
（«8».«8.4-exch84-base1p»）経由の 2 脚解禁は**死路**。両 Prop（値レベルの命題で、
それ自体は真の見込み）は pkg を通さない dispatch ルートで解禁せよ:

* `Base0_condIIIIV` は `Base0_A0bridge`
  （`bpHeadT (Trans (Pred (s84x_N M))) = bpHeadT (Trans (Pred (s84x_Np M)))`）に帰着
  （`Base0_condIIIIV_holds`、既に pkg 非依存）。ltJ 域は本ファイルの ltJ pkg の dP＋c5
  （共通 `(u1,v1)`、inner 共通 `flatBT (transC1 M)`）から flat 一致→`unflatBT` で無条件。
  隅は collapse `cornerCollapse_holds_cr` ＋ `MnformCornerResidual_md` の hPN
  （`flatBT (Trans (Pred (s84x_Np M))) = Dsym e₂ :: flatBT (bpHeadT (transC1 M))`）で両辺
  `bpHeadT (transC1 M)` に潰れる（`MnformCornerResidual_md` は corner-core で更に縮約済、
  slicepkg dispatch が既に要求する残差なので新規負債ゼロ）。
* `Base1p_condIIIIV` は隅で `dP` が退化するため base1' の oy1 論法が効かず、隅専用の
  base1' 順序 fact（`hinner` about `bpHeadT (transC2 M)` から `lessBT (bpHeadT (transC1 M))
  (ins 0_B)`）が要る。ltJ 域は oy1（«8».«8.4-exch84-base1p» の private）＋本 ltJ pkg で通る。

## 依存（すべてビルド済み・committed at main 6739865）

- «8».«8.4-slicepkg-residuals»（推移的に «8».«8.4-mnform-corner-dispatch» →
  «8».«8.4-corner-redesign» → «8».«8.4-exch84-corner» / «8».«8.4-exch84-nest-scb» →
  «8».«8.4-exch84-scbdecomp» → «8».«8.4-exch84-base1p»）:
  `Exch84_scbDecompPkg`・`NestScbCornerTriple_ns`・`NestScbCornerTriple_ns_refuted_cn`・
  `Exch84_nestScbTriple_ltJ_cr`・`exch84_nestScbTriple_ltJ_holds_cr`・
  `NestScbD4aTransport_ns`・`TransC2HoleDecomp_md`・`transC2HoleDecomp_holds_sr`・
  `s84x_N`/`s84x_Np`/`s84x_jm2`/`s84x_jm3`・`transC1`/`transC2`/`transJm1`・`transT1`・
  `STPS_RTPS`/`RTPS_Pred`/`Trans_Mark_invariant`。
- «8».«8.4-d4a-trunk»: `nestScbD4aTransport_dk`（無条件 `NestScbD4aTransport_ns`）。

## 状態

- 🤖 GREEN（sorry 0、axioms = propext/Classical.choice/Quot.sound）。反例本体
  `NestScbCornerTriple_ns_refuted_cn`（«8».«8.4-exch84-corner»）自身は propext のみだが、
  本ファイルの reduction は pkg elaboration 経由で標準 3 公理を拾う。
- 訂正候補（本ファイル外・スコープ外）: corrections.md へ「Lean 移植の §8.4
  `Exch84_scbDecompPkg` 系は Isabelle `cpx_various_scb_IIIIV` の `ltJ` 仮定を落としており
  隅で偽。ltJ ガードを再付与し、隅は collapse/slicepkg へ配線せよ」。
- Private helper suffix: `_sp2`。
-/

namespace PSS

/-! ## 1. `Exch84_scbDecompPkg`（無ガード）の反例 -/

/-- **`Exch84_scbDecompPkg`（«8».«8.4-exch84-base1p»:370）は偽**。
condIV admeq 隅 M では pkg の `transCondIII ∨ transCondIV` 仮定は `Or.inr` で満たされ、
出力の {dP, d2, c5} はそのまま `NestScbCornerTriple_ns` の三つ組 {dP, d2, d4a}
（同一 shape、`c5 = d4a`）を与える。よって pkg があればビルド済み反例
`NestScbCornerTriple_ns_refuted_cn`（«8».«8.4-exch84-corner»）に矛盾する。
ミッションの「pkg を outright discharge」は原理的に不可能である。 -/
theorem Exch84_scbDecompPkg_refuted_sp2 : ¬ Exch84_scbDecompPkg := by
  intro pkg
  apply NestScbCornerTriple_ns_refuted_cn
  intro M hST hmono hp hj1 hIV _hadmeq
  obtain ⟨_hT1, u1, u2, v1, v2, dP, d2, _d4c2, c5⟩ := pkg M hST hmono hp hj1 (Or.inr hIV)
  exact ⟨u1, v1, dP, d2, c5⟩

#print axioms Exch84_scbDecompPkg_refuted_sp2

/-! ## 2. ltJ ガード付き pkg = 「真の部分」の無条件 discharge -/

/-- **正しい pkg**（Isabelle `cpx_various_scb_IIIIV` に忠実）。`Exch84_scbDecompPkg`
（«8».«8.4-exch84-base1p»:370）に脱落仮定 `ltJ : s84x_jm3 M < transJm1 M` を再付与した形。
出力型は無ガード pkg と完全に同一。 -/
def Exch84_scbDecompPkg_ltJ_sp2 : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    1 < Lng M - 1 → (transCondIII M = true ∨ transCondIV M = true) →
    s84x_jm3 M < transJm1 M →
    transT1 M ≠ BZero ∧
    ∃ u1 u2 v1 v2 : List Sym,
      scb_decomp (Trans (Pred (s84x_N M)))
        (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC1 M)) v1 ∧
      scb_decomp (Trans (s84x_N M))
        (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC2 M)) v1 ∧
      scb_decomp (transC2 M) u2
        (flatBT (Dprin ((entry M 1 (Lng M - 1) : ℕ) : ℕ∞) BZero)) v2 ∧
      scb_decomp (Trans (Pred (s84x_Np M)))
        (Sym.dsym ((entry M 1 (s84x_jm2 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC1 M)) v1

/-- **ltJ pkg の無条件 discharge**。ミッションが期待した合成:
ltJ engine `exch84_nestScbTriple_ltJ_holds_cr`（«8».«8.4-corner-redesign»）に
無条件 `nestScbD4aTransport_dk`（«8».«8.4-d4a-trunk»）を渡して dP/d2/c5(=d4a) を得、
c4 = `transC2HoleDecomp_holds_sr`（«8».«8.4-slicepkg-residuals»、公開）、
`transT1 ≠ 0_B` は `Trans_Mark_invariant (Pred M)` から re-derive。ltJ 域では pkg の
すべての束が無条件に閉じることを示す。 -/
theorem exch84ScbDecompPkgLtJ_holds_sp2 : Exch84_scbDecompPkg_ltJ_sp2 := by
  intro M hST hmono hp hj1 hcond hltJ
  have hMR : RTPS M := STPS_RTPS M hST
  have hlen : 1 < Lng M := by omega
  -- `transT1 M = Trans (Pred M) ≠ 0_B`
  have hLP : Lng (Pred M) = Lng M - 1 := by simp [Pred, Nat.not_le.mpr hlen]
  have nzP : zeroT (Pred M) = false := by simp [zeroT, hLP]; omega
  have hT1 : transT1 M ≠ BZero := by
    have T1' : Trans (Pred M) ≠ BZero :=
      (Trans_Mark_invariant (Pred M) (RTPS_Pred M hMR)).2.1 nzP
    simpa [transT1] using T1'
  refine ⟨hT1, ?_⟩
  -- dP/d2/c5: ltJ engine ＋ 無条件 d4a 転送
  obtain ⟨u1, v1, dP, d2, c5⟩ :=
    exch84_nestScbTriple_ltJ_holds_cr nestScbD4aTransport_dk M hST hmono hp hj1 hcond hltJ
  -- c4: 公開 discharge
  obtain ⟨u2, v2, d4c2⟩ := transC2HoleDecomp_holds_sr M hST hmono hp hj1 hcond
  exact ⟨u1, u2, v1, v2, dP, d2, d4c2, c5⟩

#print axioms exch84ScbDecompPkgLtJ_holds_sp2

end PSS
