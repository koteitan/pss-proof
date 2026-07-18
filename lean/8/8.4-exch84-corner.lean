import «8».«8.4-exch84-nest-scb»

/-!
# §8.4 交換パッケージ condIV admeq 隅 (`NestScbCornerTriple_ns`) — REFUTATION

- 対象（ミッション）: «8».«8.4-exch84-nest-scb» の残差 `NestScbCornerTriple_ns`
  （condIV admeq 隅 `s84x_jm3 M = transJm1 M` の nest 三つ組 dP/d2/d4a を共通 `(u1,v1)` で）
  を discharge する予定だった。
- **結論: `NestScbCornerTriple_ns` は偽である**（本ファイルで `¬ NestScbCornerTriple_ns`
  を機械証明）。ミッションの前提「隅では三つ組が nest エンジン＋collapse 恒等式から従う」は
  隅の幾何を取り違えている: collapse 恒等式こそが dP を**退化**させ、証明不能にする。

## 幾何（なぜ dP が隅で偽か）

隅では `s84x_jm3 M = transJm1 M`（admeq）なので切片が潰れる:

  `Trans (Pred (s84x_N M)) = transC1 M`
  （両辺とも `Trans (seg M (transJm1 M) (Lng M - 2))`。Isabelle `w84x_PN_c1_of_admeq`
   layerB/pss_wip.thy:79359 と同じ collapse。）

一方 dP は
  `scb_decomp (Trans (Pred (s84x_N M))) (Dsym e₃ :: u1) (flatBT (transC1 M)) v1`
を要求する（`e₃ = entry M 1 (s84x_jm3 M)`、prefix は必ず**非空** `Dsym e₃ :: u1`）。
`scb_decomp t s c b` の定義（`flatBT t = s ++ c ++ b`）と collapse を合わせると
  `flatBT (transC1 M) = (Dsym e₃ :: u1) ++ flatBT (transC1 M) ++ v1`
となり、長さを取ると `L = 1 + |u1| + L + v1.length`（`L = (flatBT (transC1 M)).length`）、
すなわち `0 = 1 + |u1| + |v1|` で**矛盾**。よって dP を満たす `(u1, v1)` は存在しない。
これは ltJ 枝（`s84x_jm3 M < transJm1 M`）と決定的に異なる: そこでは切片が真に大きく
`Trans (Pred (s84x_N M)) ≠ transC1 M` なので nest エンジンが非退化な分解を与える。

## 隅が空でないこと（機械検証済み）

上の退化は隅 M が実在してはじめて反例になる。隅は condIV で実在する
（condIII では admeq は空虚——`ltJ_or_IVadmeq_sp` の `Or.inl` 強制、Isabelle r28 注も同旨）。
STPS witness（`python/audit_84_corner.py` で全条件を機械確認、`is_standard_wide` でも STPS 確認済み）:

  `M = (0,0)(1,1)(2,2)(2,1)`  （STPS, monoT, hasParent M 1 (Lng M-1),
   1 < Lng M-1, transCondIV, `Adm M (s84x_jm2 M) = transJm1 M`=0 を全て満たす）

本ファイルはこの witness を Lean 内で構成し（`stps_witness_cn`、diagSeq 0 3 の 9 段 oper）、
上の長さ矛盾で `¬ NestScbCornerTriple_ns` を閉じる。

## パーレント向け含意

- `NestScbCornerTriple_ns` は discharge 不能（偽）。`exch84_nestScbTriple_holds`
  （nest-scb:234）はこの残差を仮定に取るので、隅を nest 三つ組で通す経路は**行き止まり**。
- **同じ理由で `Exch84_nestScbTriple`（«8».«8.4-exch84-scbdecomp»:362、同一 shape）自身も
  隅で偽**（dP が退化）。nest 三つ組経路が下流で load-bearing なら再配線が必要。
- 隅の正しい交換は**terminal-slice transport**（Isabelle `w84x_d2_IIIV_dispatch`
  wip:79420 / `w84x_d3_IIIV_dispatch` wip:79495。inner は `flatBT (Dpt e₁ 0_B)`、
  outer は `Trans (s84x_Np M)` / `Trans (Pred (s84x_Np M))`）で、slicepkg 経路の
  `Mnform_condIV_admeq_sp`（«8».«8.4-exch84-slicepkg»:130、出力 `SlicepkgMnformOut_sp`、
  非退化）が既にこれを担う。nest 三つ組ではない。

- 依存（ビルド済み・committed at main 7443c15）: «8».«8.4-exch84-nest-scb»
  （`NestScbCornerTriple_ns`・`s84x_N`/`s84x_jm2`/`s84x_jm3`・`transC1`/`transJm1`・
  `STPS`・`Trans`/`Pred`/`Mark`・`scb_decomp`/`flatBT`/`Sym`）。
- 状態: 🤖 GREEN（sorry 0、axioms = propext のみ；`decide` 由来）。**残差ではなく反例**。
- 訂正候補: corrections.md へ「`NestScbCornerTriple_ns`（および `Exch84_nestScbTriple`）の
  隅 dP は退化」を追記推奨（本ファイル外・スコープ外）。
- Private helper suffix: `_cn`。
-/

namespace PSS

/-! ## 1. 隅退化の一般補題（witness 非依存、長さ論法のみ、無条件 GREEN） -/

/-- collapse `flatBT (Trans (Pred (s84x_N M))) = flatBT (transC1 M)` が成り立つとき、
`NestScbCornerTriple_ns` の第 1 分解 dP は**存在しえない**（非空 prefix `Dsym e₃ :: u1`
が inner `flatBT (transC1 M)` を自分自身の左に置くことを要求し、長さで矛盾）。
これは隅（`s84x_jm3 M = transJm1 M`）の collapse が dP を退化させる幾何そのもの。 -/
private theorem dP_impossible_of_flat_collapse_cn (M : PS) (u1 v1 : List Sym)
    (hcol : flatBT (Trans (Pred (s84x_N M))) = flatBT (transC1 M))
    (hd : scb_decomp (Trans (Pred (s84x_N M)))
            (Sym.dsym ((entry M 1 (s84x_jm3 M) : ℕ) : ℕ∞) :: u1) (flatBT (transC1 M)) v1) :
    False := by
  have h := hd.1
  rw [hcol] at h
  have hlen := congrArg List.length h
  simp only [List.length_append, List.length_cons] at hlen
  omega

/-! ## 2. STPS witness `(0,0)(1,1)(2,2)(2,1)`（diagSeq 0 3 の 9 段 oper、GREEN） -/

/-- 隅 witness `M = (0,0)(1,1)(2,2)(2,1)` は STPS。`python/audit_84_corner.py` が発見した
最短の oper 鎖（`diagSeq 0 3` から 9 段）を `STPS.diag`/`STPS.oper` で再構成する。 -/
private theorem stps_witness_cn : STPS [(0,0),(1,1),(2,2),(2,1)] := by
  have base : STPS (diagSeq 0 3) := STPS.diag 0 3 (by decide)
  have h := (((((((((base.oper 2 (by decide)).oper 2 (by decide)).oper 1
    (by decide)).oper 2 (by decide)).oper 1 (by decide)).oper 1
    (by decide)).oper 2 (by decide)).oper 2 (by decide)).oper 1 (by decide))
  have e : (oper (oper (oper (oper (oper (oper (oper (oper (oper
    (diagSeq 0 3) 2) 2) 1) 2) 1) 1) 2) 2) 1) = [(0,0),(1,1),(2,2),(2,1)] := by decide
  rw [e] at h; exact h

/-! ## 3. 反例本体 -/

/-- **`NestScbCornerTriple_ns` は偽**。condIV admeq 隅 witness
`M = (0,0)(1,1)(2,2)(2,1)` で全前提が成立するが（`decide`）、そこでは
`flatBT (Trans (Pred (s84x_N M))) = flatBT (transC1 M)`（`decide`；collapse）ゆえ
dP が退化して不可能（`dP_impossible_of_flat_collapse_cn`）。 -/
theorem NestScbCornerTriple_ns_refuted_cn : ¬ NestScbCornerTriple_ns := by
  intro h
  obtain ⟨u1, v1, dP, _d2, _d4a⟩ :=
    h [(0,0),(1,1),(2,2),(2,1)] stps_witness_cn (by decide) (by decide)
      (by decide) (by decide) (by decide)
  exact dP_impossible_of_flat_collapse_cn [(0,0),(1,1),(2,2),(2,1)] u1 v1 (by decide) dP

#print axioms NestScbCornerTriple_ns_refuted_cn

end PSS
