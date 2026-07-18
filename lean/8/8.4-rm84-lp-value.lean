import «8».«8.4-rm84-head-aware»

/-!
# §8.4 補題（右端置き換えと `Trans`）— 値リードバック残差 `Rm84LpValue` は **偽**（訂正）

- 原文: `tmp/content.md` §8.4「補題（条件(III)～(V)の下での右端の置き換えと `Trans`
  の関係）」(4265)。`isabelle/pss_paper.thy`:1945 は DEFERRED。
- 攻略対象（当初）: `«8».«8.4-rm84-head-aware»` の値リードバック残差
  `Rm84LpValue`（同 :290）を discharge（`theorem rm84LpValue_holds : Rm84LpValue`）。
- 本ファイルの結論: **`Rm84LpValue` は偽命題**である（機械反証済み、下記）。
  したがって当初ミッションの `rm84LpValue_holds` は成立しえない。同根で
  兄弟残差 `Rm84NpValue` も偽、ゆえに合流 `Rm84HeadValue` も偽。

## 反例（条件(III) の最小 STPS 域要素）

`Mcex = (0,0)(1,1)(2,1) = oper (diagSeq 0 2) 2`。これは `Rm84LpValue` の
仮定を **すべて満たす**:
* `STPS Mcex`（対角 `diagSeq 0 2` の正基本列 `oper _ 2`、構成子で証明）。
* `monoT Mcex = true`、`hasParent Mcex 1 (Lng Mcex − 1) = true`、
  `s84x_jm2 Mcex + 1 < Lng Mcex − 1`（＝ `0 + 1 < 2`、いずれも `decide`）。
* 条件判定: `transCondIII Mcex = true`（条件(III)：`0 < β=M₁,₂=1`,
  `β ≤ M₁,ⱼ₀=1`, `adm j₀`）。`s84x_jm2 Mcex = 0`（行1親）だが
  `transJ0 Mcex = transJm1 Mcex = 1`（行0親、許容）——**行1親 ≠ 行0親**。

一方、結論の等式は成立しない:
* `Trans (rrLp Mcex)`（`rrLp Mcex = (0,0)(1,1)(2,0)`）の平坦化長は **4**。
* `Dprin γ (bpHeadT (c2hole_ch Mcex γ))`（`γ = M₁,ⱼ₋₂ = 0`）の平坦化長は **3**。

外側頭は両辺とも `D_0`（`bpHeadV` が一致、`γ = 0`）で正しいが、**内側の
c₂-hole リードバック項が異なる**（長さ 4 対 3）。ゆえに等式は偽。同様に
`Trans (s84x_Np Mcex)`（長 4）≠ `Dprin γ (bpHeadT (transC2 Mcex))`（長 3）で
`Rm84NpValue` も偽。

## 診断（なぜ偽か・忠実ルートへの含意）

`Rm84LpValue`/`Rm84NpValue`（Wave AA の「値レベル尖鋭化」）は c₂-hole エンジンの
閉形式 `bpHeadT (c2hole_ch M ·)` / `bpHeadT (transC2 M)` を `Trans (rrLp M)` /
`Trans (s84x_Np M)` の内側そのものと同一視するが、これは **条件(III) で
行1親 `j₋₂` と行0親 `j₀` が食い違う場合に破綻する**（`Mcex` がその最小例）。
条件(V)+adm では橋 `s84x_jm2 = transJ0`（Isabelle `s85b_condV_bridge(4)`）で
両者が一致し、閉形式 `Trans (s84x_Lp M) = D_e(t₂ +_B D_e 0)`
（Isabelle `m_8_5_scbdec_Lp_condV_adm`）が成り立つが、**その Isabelle 値補題自体が
外科手術 `m_8_4_rightend_Trans` を経由しており**、`c2hole_ch` 閉形式との直接同一視は
一般には偽。ホスト `hostM30_rr`（条件(IV)、`transJm1 = s84x_jm2 = 0`）で
`Rm84LpValue` が成り立つのは、そこでも両親の行1値が一致する特殊事情による
（`rm84HeadValue_nonvacuous_ha` はこの一点のみを確認していた）。

**含意**: `«8».«8.4-rm84-head-aware»` の値ルート
`rightmost84ReplaceExists_of_value`（残差 `Rm84HeadValue`）は
**充足不能な前提に依存する死路**である（型検査は通るが discharge 不能）。
存在部 `Rightmost84ReplaceExists`（＝ Isabelle `m_8_4_rightend_Trans`、真）への
忠実ルートは外科手術（`s84d_*` scb 分解の transport、値ではなく scb 分解）であり、
scb-shared 形 `Rm84HeadShared`（本反証の影響を受けない、外側頭は正しく `D_γ`）で
攻めるべき。値形リードバック（`Rm84NpValue`/`Rm84LpValue`/`Rm84HeadValue`）は放棄。

- 依存（ビルド済み・committed 2766fef）: «8».«8.4-rm84-head-aware»
  （`Rm84LpValue`/`Rm84NpValue`/`Rm84HeadValue`/`rrLp`/`s84x_Np`/`s84x_jm2`/
  `c2hole_ch`/`transC2`/`bpHeadT`）、推移的に `Trans`/`Mark`/`STPS`/`diagSeq`/`oper`。
- 状態: 🤖 GREEN（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  反証は完全に機械検証済（`decide` による域所属＋長さ食い違い、構成子による STPS）。
- Private suffix: `_lv`。
-/

namespace PSS

/-! ## 反例列 -/

/-- 条件(III) の最小 STPS 域要素 `(0,0)(1,1)(2,1) = oper (diagSeq 0 2) 2`。 -/
abbrev Mcex_lv : PS := [(0,0),(1,1),(2,1)]

/-- `Mcex_lv` は対角列の正基本列（構成子で `STPS`）。 -/
theorem stps_Mcex_lv : STPS Mcex_lv :=
  (by decide : oper (diagSeq 0 2) 2 = Mcex_lv) ▸
    STPS.oper (STPS.diag 0 2 (by decide)) 2 (by decide)

/-- `Mcex_lv` は `Rm84LpValue` の仮定（`monoT`/`hasParent`/`j₋₂+1<Lng−1`）をすべて満たす。 -/
theorem domain_Mcex_lv :
    monoT Mcex_lv = true ∧ hasParent Mcex_lv 1 (Lng Mcex_lv - 1) = true ∧
      s84x_jm2 Mcex_lv + 1 < Lng Mcex_lv - 1 :=
  ⟨by decide, by decide, by decide⟩

/-! ## 1. 主結論: `Rm84LpValue` は偽 -/

/-- **`Rm84LpValue` は偽命題**。反例 `Mcex_lv`（条件(III)、行1親 ≠ 行0親）で
`Trans (rrLp Mcex_lv)`（平坦長 4）≠ `Dprin γ (bpHeadT (c2hole_ch Mcex_lv γ))`
（平坦長 3）。当初ミッションの `rm84LpValue_holds` は成立しえない。 -/
theorem rm84LpValue_false : ¬ Rm84LpValue := by
  intro h
  have key := h Mcex_lv stps_Mcex_lv domain_Mcex_lv.1 domain_Mcex_lv.2.1 domain_Mcex_lv.2.2
  exact absurd (congrArg (fun t => (flatBT t).length) key) (by decide)

/-! ## 2. 同根の兄弟残差も偽（値ルート全体が死路であることの記録） -/

/-- **`Rm84NpValue` も偽**。同じ反例で `Trans (s84x_Np Mcex_lv)`（平坦長 4）
≠ `Dprin γ (bpHeadT (transC2 Mcex_lv))`（平坦長 3）。 -/
theorem rm84NpValue_false : ¬ Rm84NpValue := by
  intro h
  have key := h Mcex_lv stps_Mcex_lv domain_Mcex_lv.1 domain_Mcex_lv.2.1 domain_Mcex_lv.2.2
  exact absurd (congrArg (fun t => (flatBT t).length) key) (by decide)

/-- **`Rm84HeadValue` も偽**（`Rm84NpValue ∧ Rm84LpValue` の合流ゆえ）。
`«8».«8.4-rm84-head-aware»` の値ルート `rightmost84ReplaceExists_of_value` は
充足不能な前提に依存する。 -/
theorem rm84HeadValue_false : ¬ Rm84HeadValue := by
  intro h
  have key := (h Mcex_lv stps_Mcex_lv domain_Mcex_lv.1 domain_Mcex_lv.2.1 domain_Mcex_lv.2.2).2
  exact absurd (congrArg (fun t => (flatBT t).length) key) (by decide)

#print axioms rm84LpValue_false
#print axioms rm84NpValue_false
#print axioms rm84HeadValue_false

end PSS
