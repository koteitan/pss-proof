import «8».«8.7-pred-scb-insert»

/-!
# §8.7 補題（`Pred` と `[0]` の関係）— 最後の 2 隅残差の討伐

姉妹ファイル `8.7-pred-scb-insert.lean` は一般形 `PredOper0_pg` を、枝 (I)/(III)/(V)
の master-key 討伐（`p_8_7_Pred_oper0_condIIIV_psi`）に加えて、次の **2 つの名前付き
残差**へ還元済み（`p_8_7_Pred_oper0_of_residuals_psi`）：

* `PredOper0_t1zero_residual_psi`（退化枝 `t₁ = Trans (Pred M) = 0`）
* `PredOper0_nestedCond_residual_psi`（枝 (II)/(IV) の二段ネスト零化）

本ファイルはこの 2 隅を、既存のネスト零化補題
（`trailing_principal_annihilable` / `trailing_principal_annihilable_zero_body`,
`8.6-trailing-principal-annihilable`）と master key（`Trans_c1_c2_decomp`,
`8.3-condII-masterCF`）から討伐する。

## 隅 (a) `PredOper0_t1zero_residual_psi`

`Trans (Pred M) = 0` かつ `monoT M`・`1 < Lng M` のとき、mono 枝の展開
`Trans_Mark_mono_equations`（`7.3-Trans-welldefined`）の `t₁ == 0` 節が発火し

  `Trans M = D_0 (D_{j₁} 0)`（`j₁ = entry M 1 (lastIdx M)`）

となる **top-level 値形**が確定する。ここから
1. `trailing_principal_annihilable_zero_body 0 j₁` で `D_0 (D_{j₁} 0)` を
   `D_0 0` へ（`j₁+1` 歩以内で）零化し、
2. さらに 1 歩 `operB (D_0 0) [0] = 0`（`v = 0` の successor-to-zero 基本列）で
   `Trans M[0]^k = 0 = Trans (Pred M)` に到達する。

`[0]`-軌道は任意有限 `k` を許すので、この 2 段の連結で結論が閉じる。

## 隅 (b) `PredOper0_nestedCond_residual_psi`（枝 (II)/(IV)）

（後述。二段ネスト零化を master key の共有 scb 文脈上で `trailing_principal_annihilable`
を深さごとに 2 回適用して落とす。）

## 依存（ビルド済みのみ import）

`8.7-pred-scb-insert`（残差定義 `PredOper0_*_residual_psi`／全体還元
`p_8_7_Pred_oper0_of_residuals_psi`；推移的に `Trans_Mark_mono_equations`
(7.3)、`trailing_principal_annihilable*` (8.6)、`Trans_c1_c2_decomp`／
`condII_c2_val_holds`／`condII_c1_shape_holds` (8.3)、一般形 `PredOper0_pg`
(8.7-Pred-oper0-general)）。

## private helper suffix: `_pc`
-/

namespace PSS

/-! ## 1. 隅 (a)：退化枝 `t₁ = 0` -/

/-- `operB (D_0 0) [0] = 0`（`v = 0` の successor-to-zero 基本列）。
`bOperCore` の `.princ (.db 0 0)` 節が `b == 0` かつ `v == 0` で `0` を返す。 -/
private theorem operB_D0_zero_pc :
    operB (Dprin (0 : ℕ∞) BZero) (numBT 0) = BZero := by
  show bOperCore (.term (.trm [.db (0 : ℕ∞) BZero]) (numBT 0)) = BZero
  rw [bOperCore.eq_def]
  show bOperCore (.list [.db (0 : ℕ∞) BZero] (numBT 0)) = BZero
  rw [bOperCore.eq_def]
  show bOperCore (.princ (.db (0 : ℕ∞) BZero) (numBT 0)) = BZero
  rw [bOperCore.eq_def]
  simp [BZero]

/-- 隅 (a)：`Trans (Pred M) = 0` の退化枝。 -/
theorem PredOper0_t1zero_residual_holds_pc :
    PredOper0_t1zero_residual_psi := by
  intro M hR hmono hlen ht1
  -- (1) top-level 値形 `Trans M = D_0 (D_{j₁} 0)`
  have hTM : Trans M
      = Dprin 0 (Dprin (entry M 1 (lastIdx M) : ℕ∞) BZero) := by
    have heq := (Trans_Mark_mono_equations M hR hlen hmono).1
    rw [heq]
    simp only [ht1, beq_self_eq_true, if_true]
  -- (2) `D_0 (D_{j₁} 0)` を `D_0 0` へ零化
  obtain ⟨k1, _, _, hk1⟩ :=
    trailing_principal_annihilable_zero_body 0 (entry M 1 (lastIdx M))
  simp only [Nat.cast_zero] at hk1
  -- (3) 連結：`k1 + 1` 歩で `0` に到達
  refine ⟨k1 + 1, ?_⟩
  rw [ht1, hTM, Function.iterate_succ_apply']
  show operB ((fun a => operB a (numBT 0))^[k1]
      (Dprin 0 (Dprin (entry M 1 (lastIdx M) : ℕ∞) BZero))) (numBT 0) = BZero
  rw [hk1]
  exact operB_D0_zero_pc

#print axioms PredOper0_t1zero_residual_holds_pc

/-! ## 2. 隅 (b)：枝 (II)/(IV) の二段ネスト零化 — 共有 scb 文脈への還元

数値監査（`python/audit_87_pred_oper0.py`, `maxlen=6 maxval=4`）は枝 (II)/(IV) の
129 ホスト（II: 65 / IV: 64）を **全通過**、観測最大 `k = 13`（全枝では 18）。
軌道は「二段（`D_{j₁}0` を潰し次に `D_{j'}0` を潰す）」では**なく**、`D_{j'}` ブロック
本体を kind-1 降下で丸ごと 0 まで潰す**カスケード**である（`transC2Core` の
**第 4 枝** `t₂ ≠ 0`：`transC2 M = D_v(t₃ +ᴮ D_{j'}(t₄ +ᴮ D_0 0))`、`transC1 M = D_v t₂`。
`else if t₂ == BZero` の第 3 枝（純二段 `D_v(D_{j'}(D_{j₁}0))`）は条件(II)では
`transT2 M ≠ BZero`（`condII_host_basic`）ゆえ**発火しない**）。

### 例（`M = (0,0)(1,1)(2,2)(2,0)`, 枝 II, `k = 6`）

```
transC2 = D_0(D_2 0 +ᴮ D_1(D_2 0 +ᴮ D_0 0))
  → D_0(D_2 0 +ᴮ D_1(D_2 0))        -- 内側 D_0 0 零化（1 歩）
  → D_0(D_2 0 +ᴮ D_1(D_1 0))        -- D_2 0 → D_1 0（kind-1）
  → D_0(D_2 0 +ᴮ D_1(D_0 0))        -- D_1 0 → D_0 0
  → D_0(D_2 0 +ᴮ D_1 0)             -- 内側 D_0 0 零化
  → D_0(D_2 0 +ᴮ D_0 0)             -- D_1 0 → D_0 0（外 body の末尾）
  → D_0(D_2 0) = transC1            -- 末尾 D_0 0 零化
```

すなわち `D_{j'}` ブロック本体（`t₄ +ᴮ D_0 0`）を **0 まで**潰し、生じた
`D_{j'} 0` を外側 `trailing_principal_annihilable` で除去する。前半（任意 OT_B 本体を
scb 文脈内で末尾から 0 へ潰す）が原文 §8.7 `p_8_7_OT_tail_annihilable`（scb 逐語形）
＝Isabelle も `sorry` の **hard core**。本ファイルはこの核を証明せず、
**共有 scb 文脈上の降下** `PredOper0_scbCtx_residual_pc` として尖鋭に切り出し、
外側 `replaceScb` ラッパを master key `Trans_c1_c2_decomp` で除去して封じ込める。

`Trans_c1_c2_decomp`（`8.3-condII-masterCF`）は条件非依存に共有 `(s, b)` を与える
（RTPS のみ要求。closed form `condII_c2_val`(RTPS)/`Cnv_c2_shape_condIV`(STPS) は
本還元では不要）。 -/

/-- 隅 (b) の**尖鋭化残差**：`Trans M`（`transC2` を占める）が共有 scb 文脈 `(s,b)` の
中で `[0]` 反復により `Trans (Pred M)`（`transC1` を占める）へ降下する、という命題。
外側の `replaceScb` ラッパは除去済みで、残るのは `D_v` 本体の kind-1 カスケード降下
（＝原文 `p_8_7_OT_tail_annihilable` scb 形の内容、Isabelle も `sorry`）のみ。 -/
def PredOper0_scbCtx_residual_pc : Prop :=
  ∀ M : PS, RTPS M → monoT M = true → 1 < Lng M →
    Trans (Pred M) ≠ BZero →
    (transCondII M = true ∨ transCondIV M = true) →
    ∀ s b : List Sym,
      scb_decomp (Trans (Pred M)) s (flatBT (transC1 M)) b →
      scb_decomp (Trans M) s (flatBT (transC2 M)) b →
      ∃ k, ((fun a => operB a (numBT 0))^[k]) (Trans M) = Trans (Pred M)

/-- 隅 (b) の還元：共有 scb 文脈上の降下残差 `PredOper0_scbCtx_residual_pc` から、
名前付き残差 `PredOper0_nestedCond_residual_psi`（`8.7-pred-scb-insert`）が従う。
master key `Trans_c1_c2_decomp` が共有 `(s,b)` を供給する。 -/
theorem nestedCond_of_scbCtx_residual_pc
    (H : PredOper0_scbCtx_residual_pc) :
    PredOper0_nestedCond_residual_psi := by
  intro M hR hmono hlen ht1 hcond
  obtain ⟨s, b, hd1, hd2⟩ := Trans_c1_c2_decomp M hR hmono hlen ht1
  exact H M hR hmono hlen ht1 hcond s b hd1 hd2

#print axioms nestedCond_of_scbCtx_residual_pc

/-! ## 3. 尖鋭 capstone — §8.7 Pred-oper0 全体を単一 scb 残差へ

隅 (a)（`PredOper0_t1zero_residual_holds_pc`, **無条件**）と隅 (b) の還元
（`nestedCond_of_scbCtx_residual_pc`）を全体還元
`p_8_7_Pred_oper0_of_residuals_psi`（`8.7-pred-scb-insert`）に流し込み、原文 §8.7
「補題（`Pred` と `[0]` の関係）」の一般忠実形 `PredOper0_pg` を、**ただ 1 本**の
scb 文脈カスケード降下残差 `PredOper0_scbCtx_residual_pc` へ還元する。

退化隅 (a) は本ファイルで無条件に討伐済みなので、`PredOper0_pg` に残る仮定は
`PredOper0_scbCtx_residual_pc` だけである（＝原文/Isabelle の唯一の hard core）。 -/
theorem p_8_7_Pred_oper0_of_scbCtx_pc
    (H : PredOper0_scbCtx_residual_pc) : PredOper0_pg :=
  p_8_7_Pred_oper0_of_residuals_psi
    (nestedCond_of_scbCtx_residual_pc H)
    PredOper0_t1zero_residual_holds_pc

#print axioms p_8_7_Pred_oper0_of_scbCtx_pc

end PSS
