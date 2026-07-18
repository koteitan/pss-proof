import «8».«8.4-rm84-head-aware»

/-!
# §8.4 補題（右端置き換えと `Trans`）— 値リードバック残差 `Rm84NpValue` は **偽**（訂正）

- 原文: `tmp/content.md` §8.4「補題（条件(III)～(V)の下での右端の置き換えと `Trans`
  の関係）」(4265)。`isabelle/pss_paper.thy`:1945 は DEFERRED。
- 当初ミッション: `«8».«8.4-rm84-head-aware»` の値リードバック残差
  `Rm84NpValue`（同 :284）を discharge（`theorem rm84NpValue_holds : Rm84NpValue`）。
- **本ファイルの結論: `Rm84NpValue` は偽命題である**（機械反証、下記）。ゆえに
  当初の攻め筋（`condV_terminal_slice_Trans` × 2 適用＋`bridgeA`）は **条件(V)
  でしか正しくない**閉形式を全域（条件(III)～(V)）に主張しており、条件(III) で破綻する。

## 反証の要点（なぜ偽か）

`Rm84NpValue` は「`s84x_Np M` の `Trans` が、外側頭 `D_{M₁,ⱼ₋₂}`（`j₋₂ = s84x_jm2 M`
＝**行1親**）の内側に、`c₂` の頭剥がし `bpHeadT (transC2 M)` を露出する」と主張する:

    Trans (s84x_Np M) = D_{M₁,ⱼ₋₂} (bpHeadT (transC2 M)).

攻め筋は `m = s84x_jm2 M` と `m = transJm1 M` の 2 回の終切片適用で内側を同定するが、
これが成立するには `bpHeadT (Trans (seg M (transJm1 M) (Lng M-1))) = bpHeadT (Trans M)`
（終切片 VE 型の頭一致）が要る。これは **行0親鎖 `j₀ = transJ0 M` が終切片体制に入る
条件(V)** に固有で、条件(V) では `s84x_jm2 M = transJ0 M`（Isabelle
`s85b_condV_bridge(4)`）と併合して正しい。しかし条件(III) では **行1親 `s84x_jm2 M` と
行0親 `transJ0 M` が食い違い**、頭一致が破れる。数値的にも条件(III) の深い host で
`bpHeadT (Trans (seg M transJm1 (Lng-1))) = bpHeadT (Trans M)` は 0/N（`8.4-rm84-head-aware`
の header に既記、Isabelle NFALL3 節でも「terminal-slice VE route REFUTED」と明記）。

条件(III) では正しい内側は頭剥がし前の `transC2 M` そのもの（＝1 段深い principal）で
あり、`bpHeadT` を一段余分に剥がした `Rm84NpValue` の右辺は真の値より 1 レベル浅い。

## 反例（条件(III) の STPS 域要素、2 例）

いずれも `Rm84NpValue` の仮定（`STPS`/`monoT`/`hasParent₁(last)`/`j₋₂+1 < Lng-1`）を
**すべて満たす** STPS 標準形（対角列の正基本列、構成子で `STPS`）でありながら結論が偽:

* `Mcex_nv = (0,0)(1,1)(2,1) = oper (diagSeq 0 2) 2`（最小、`Lng = 3`）。
  行1親 `s84x_jm2 = 0`、行0親 `transJ0 = transJm1 = 1`。
  `Trans (s84x_Np Mcex_nv)` の平坦長 = 4、右辺の平坦長 = 3。
* `Mcex2_nv = (0,0)(1,1)(2,2)(3,2) = oper (diagSeq 0 3) 2`（`Lng = 4`、境界人工物でない）。
  行1親 `s84x_jm2 = 1`、行0親 `transJ0 = 2`。同じく平坦長 4 対 3。

（一方 `rm84HeadValue_nonvacuous_ha` の witness `hostM30_rr` は条件(IV) かつ
`transJm1 = s84x_jm2 = 0` の特殊事情で成り立つ一点にすぎない。）

## 含意（忠実ルートへの示唆）

Wave AA の「値レベル尖鋭化」で導入された値形残差
`Rm84NpValue` / `Rm84LpValue` / 合流 `Rm84HeadValue` は **すべて充足不能**であり、
`«8».«8.4-rm84-head-aware»` の値ルート `rightmost84ReplaceExists_of_value`
（前提 `Rm84HeadValue`）は型検査は通るが discharge 不能な死路である。忠実な残差は
**scb-shared 形** `Rm84HeadShared`（存在量化 `∃ t t' s0 b0`、外側頭は正しく `D_γ`
で `t`/`t'` は任意 BT）または存在部 `Rightmost84ReplaceExists`
（`Trans (s84x_Np M)` を最内中心 `D_{M₁,ⱼ₁} 0` の周りで scb 分解する存在形）であり、
これらは本反証の影響を受けない（内側を `bpHeadT (transC2 M)` と同定しないため）。
親エージェントは値形を放棄し、`Rm84HeadShared` / `Rightmost84ReplaceExists` を
外科手術（`s84d_*` scb 分解 transport、Isabelle `m_8_4_rightend_Trans`）で攻めるべき。

（並走の兄弟ファイル `«8».«8.4-rm84-lp-value»` も独立に同一反例
`(0,0)(1,1)(2,1)` を得て `Rm84LpValue`/`Rm84NpValue`/`Rm84HeadValue` の偽を機械証明済み。
本ファイルは Np 側の焦点付き反証と第2反例（`Lng = 4`）を独立に供給する。）

- 依存（ビルド済み・committed 2766fef）: «8».«8.4-rm84-head-aware»
  （`Rm84NpValue`/`s84x_Np`/`s84x_jm2`/`transC2`/`bpHeadT`）、推移的に
  `Trans`/`STPS`/`diagSeq`/`oper`/`flatBT`/`Dprin`/`entry`/`Lng`/`hasParent`/`monoT`。
- 状態: 🤖 GREEN（sorry 0、axioms = [propext, Classical.choice, Quot.sound]）。
  反証は完全に機械検証済（`decide` による域所属＋平坦長食い違い、構成子による `STPS`）。
- Private 接尾辞: `_nv`。
-/

namespace PSS

/-! ## 反例 1（最小、`Lng = 3`） -/

/-- 条件(III) の最小 STPS 域要素 `(0,0)(1,1)(2,1) = oper (diagSeq 0 2) 2`。
行1親 `s84x_jm2 = 0` ≠ 行0親 `transJ0 = 1`。 -/
abbrev Mcex_nv : PS := [(0,0),(1,1),(2,1)]

/-- `Mcex_nv` は対角列 `diagSeq 0 2` の正基本列（構成子で `STPS`）。 -/
theorem stps_Mcex_nv : STPS Mcex_nv :=
  (by decide : oper (diagSeq 0 2) 2 = Mcex_nv) ▸
    STPS.oper (STPS.diag 0 2 (by decide)) 2 (by decide)

/-- `Mcex_nv` は `Rm84NpValue` の仮定（`monoT`/`hasParent₁(last)`/`j₋₂+1<Lng−1`）を満たす。 -/
theorem domain_Mcex_nv :
    monoT Mcex_nv = true ∧ hasParent Mcex_nv 1 (Lng Mcex_nv - 1) = true ∧
      s84x_jm2 Mcex_nv + 1 < Lng Mcex_nv - 1 :=
  ⟨by decide, by decide, by decide⟩

/-! ## 反例 2（`Lng = 4`、境界人工物でないことの確認） -/

/-- 条件(III) の STPS 域要素 `(0,0)(1,1)(2,2)(3,2) = oper (diagSeq 0 3) 2`。
行1親 `s84x_jm2 = 1` ≠ 行0親 `transJ0 = 2`。 -/
abbrev Mcex2_nv : PS := [(0,0),(1,1),(2,2),(3,2)]

/-- `Mcex2_nv` は対角列 `diagSeq 0 3` の正基本列（構成子で `STPS`）。 -/
theorem stps_Mcex2_nv : STPS Mcex2_nv :=
  (by decide : oper (diagSeq 0 3) 2 = Mcex2_nv) ▸
    STPS.oper (STPS.diag 0 3 (by decide)) 2 (by decide)

/-- `Mcex2_nv` は `Rm84NpValue` の仮定を満たす。 -/
theorem domain_Mcex2_nv :
    monoT Mcex2_nv = true ∧ hasParent Mcex2_nv 1 (Lng Mcex2_nv - 1) = true ∧
      s84x_jm2 Mcex2_nv + 1 < Lng Mcex2_nv - 1 :=
  ⟨by decide, by decide, by decide⟩

/-! ## 主結論: `Rm84NpValue` は偽

反例で結論の等式両辺の平坦長（`flatBT ... |>.length`）が食い違う（4 対 3）。
仮に `Rm84NpValue` が成り立てば両辺は等しく平坦長も一致するはずで矛盾。 -/

/-- **`Rm84NpValue` は偽命題**。最小反例 `Mcex_nv`（条件(III)、行1親 ≠ 行0親）で
`Trans (s84x_Np Mcex_nv)`（平坦長 4）≠ `D_{M₁,ⱼ₋₂} (bpHeadT (transC2 Mcex_nv))`
（平坦長 3）。当初ミッションの `rm84NpValue_holds` は成立しえない。 -/
theorem not_rm84NpValue : ¬ Rm84NpValue := by
  intro h
  have key := h Mcex_nv stps_Mcex_nv
    domain_Mcex_nv.1 domain_Mcex_nv.2.1 domain_Mcex_nv.2.2
  exact absurd (congrArg (fun t => (flatBT t).length) key) (by decide)

/-- 第2反例 `Mcex2_nv`（`Lng = 4`）による独立確認（境界人工物でないことの担保）。 -/
theorem not_rm84NpValue_via_len4 : ¬ Rm84NpValue := by
  intro h
  have key := h Mcex2_nv stps_Mcex2_nv
    domain_Mcex2_nv.1 domain_Mcex2_nv.2.1 domain_Mcex2_nv.2.2
  exact absurd (congrArg (fun t => (flatBT t).length) key) (by decide)

/-! ## 系: 合流残差 `Rm84HeadValue` も偽（値ルート全体が死路であることの記録）

`Rm84HeadValue M` の第1連言が `Rm84NpValue` の等式そのものなので、同じ反例で偽。 -/

/-- **`Rm84HeadValue` も偽**（`rm84HeadValue_of_parts` 経由の値ルート
`rightmost84ReplaceExists_of_value` は充足不能な前提に依存する）。 -/
theorem not_rm84HeadValue : ¬ Rm84HeadValue := by
  intro h
  have key := (h Mcex_nv stps_Mcex_nv
    domain_Mcex_nv.1 domain_Mcex_nv.2.1 domain_Mcex_nv.2.2).1
  exact absurd (congrArg (fun t => (flatBT t).length) key) (by decide)

#print axioms stps_Mcex_nv
#print axioms stps_Mcex2_nv
#print axioms not_rm84NpValue
#print axioms not_rm84NpValue_via_len4
#print axioms not_rm84HeadValue

end PSS
