import «7».«7.2-scb-fseq»
import «7».«7.3-Trans-welldefined»
import «8».«8.3-condII-masterCF»

/-!
# §8.3 条件(II) — 終切片の値 `tailval`、および **`CondII_masterCF` の反証**

- 原文: `tmp/content.md` 3956–4247（§8.3 命題（条件(II)の下での `Trans` と基本列の
  交換関係））。逐語形は `p_8_3_TransCondII_oper_descend`
  (isabelle/pss_paper.thy:1863)。

- 担当（当初）: `y3j_condII_tailval` (isabelle/layerC/pss_scratch.thy:17079) の移植と、
  ビルド済み «8».«8.3-condII-masterCF» が露出した `CondII_TailvalAll` の討伐。

## 🚨🚨🚨 結論: `CondII_masterCF` は**偽**である（本ファイル最大の所見）

ビルド済み «8».«8.3-TransCondII-engine»:211 の `CondII_masterCF`（`RT_PS` 上・
`tailval` 仮定なし）は、**成り立たない**。反例を機械証明した:

    M = (0,0)(1,1)(2,2)(2,0)(2,2)(2,0)      -- 成分 ≤ 2、Lng = 6

`RTPS M` / `monoT M` / `1 < Lng M - 1` / `transCondII M` はすべて `decide` で真
（`condII_RTPS_counterexample`）。しかし `CondII_masterCF` の結論は M で破れる
（`not_CondII_masterCF`）。したがって:

* `CondII_masterCF` は **discharge 不可能**（真でないので証明は存在しない）。
* それは `lean/8/8.7-termination.lean:224` の束 `TerminationResidual` の
  **フィールドの 1 つ**である（`condII : CondII_masterCF`）。よってこの束は
  **充足不能**であり、`p_8_7_termination` は型としては通るが**空虚**である
  （＝「27 本すべて Isabelle で証明済みだから束は充足可能」という
  8.7 ヘッダの主張は、この 1 本については**誤り**）。
* 直し方は 1 行:  engine:212 の `RTPS M` を **`STPS M` に変える**
  （下記「なぜ ST_PS なら無傷か」）。消費者（`FseqDesc_exchII` / `OTdisp_exchII`）は
  **両方とも `STPS N` を渡してくる**ので、`RT_PS` 版は誰も要求していない。
  «8».«8.3-condII-masterCF» は既にその修正後の姿（`condII_exchII_of_ST_residuals`,
  残差 `CondII_step` ＋ `CondII_TailvalAll_ST`）を供給済み。

## 反証の機構（なぜ破れるか）

`Trans M` と `Trans (M[2])` を陽に計算すると（`Trans_eq_lengthAux` ＋ `decide`）、
両者は**同じ前置 `Yps` を持ち、末尾 principal の本体だけが違う**:

    Y = D_2 0 + D_1 (D_2 0 + D_0 0) + D_2 0        -- `Ycex`
    X = D_2 0 + D_0 0 + D_2 0                      -- `Xcex`,  X ≠ Y
    Trans M      = D_0 (Y + D_1 (Y + D_0 0))
    Trans (M[2]) = D_0 (Y + D_1 X)

一方 `operB (Trans M) (numBT k)` は **k に依らず**閉形式に落ちる
（`operB_closed_tv`、`bOperCore` の定義的簡約が概念どおり効く）:

    operB (Trans M) (numBT k) = D_0 (Y + (D_1 Y) * (k+1))

すなわち `operB` 側の本体末尾はどんな `k` でも常に `D_1 Y` であるのに対し、
`Trans (M[2])` 側は `D_1 X` であり、`X ≠ Y`。よって
**`∀ k, Trans (M[2]) ≠ operB (Trans M) (numBT k)`**（`no_operB_step_tv`）。
ところが `CondII_masterCF` の witness からは（`scb_fseq_decomp` ＝
`m_7_2_scb_fseq_scb` 経由で）その `k` が**必ず出る**
（`exch_of_lhs_closed_ex_tv`、engine:191 の private `exch_of_lhs_closed_ex_c2` と同内容。
private は module を跨げないので複製）。矛盾。

同じ `X ≠ Y` が `CondII_tailval M` も殺す（`not_CondII_TailvalAll`）:

    W = Trans (seg M j₀ (Lng M - 2)) = D_1 X    だが    D_{M₁,ⱼ₀} t₄ = D_1 Y

＝ 終切片の値が原文の主張する形に**なっていない**。`tailval` の破れは「経路が死ぬ」
だけだが、上のとおり `masterCF` の**結論自身**も同じ M で破れる。

## なぜ Isabelle は無傷か / なぜ ST_PS なら無傷か

Isabelle の `c2sx_condII_masterCF` (isabelle/layerB/pss_wip.thy:87430) は
**仮定 `TV : c2sx_tailval M` を持つ**。`TV` の無条件供給元は
`y3j_condII_tailval` (layerC/pss_scratch.thy:17079) だが、その仮定は
**`MST : M ∈ ST_PS`** であって `M ∈ RT_PS` ではない（`ljx_TVall_of_fin` (wip:115242)
＋ `ot9_FINRC` (scratch:10032) 経由。両者とも `ST_PS` 束縛）。
`shows "c2sx_tailval"` を**全数 grep して 8 箇所すべての `assumes` を読んだ**（本文 grep、
名前 grep ではない）:

  | 供給元 | 位置 | 仮定 |
  |---|---|---|
  | `y3j_condII_tailval` | scratch:17079 | **ST_PS** |
  | `c2sx_tailval_trunk` | wip:87725 | RT_PS ＋ 追加仮定 `TR` |
  | `c2sx_tailval_of_reg` | wip:87844 | RT_PS ＋ 追加仮定 `¬ldj`, `REG` |
  | `cdx_tailval_notldj` | wip:90430 | **ST_PS** ＋ `notldj`, `DIAG` |
  | `tvx_tailval_of_boundary` | wip:110546 | **ST_PS** ＋ `BR`,`DEQ`,`GUARD`,`FIN` |
  | `tvx_TVall_of_LDJB_fin` | wip:110720 | **ST_PS**（modulo `LDJB`,`FINRC`） |
  | `tvx_TVall_of_residuals` | wip:110954 | **ST_PS** |
  | `ljx_TVall_of_fin` | wip:115242 | **ST_PS** |

すなわち **「`RT_PS` 上で無条件の tailval」は corpus に存在しない**。engine ヘッダ
:32–34 の「`y3j_condII_tailval` が**無条件に**落とすので `CondII_masterCF` は
Isabelle では定理」は**誤り**であり、その誤りがそのまま偽の `Prop` になっていた。
⚠️ **`STPS` への restate が反例に触られないことは、本ファイルでは証明していない**。
`STPS Mcex` は帰納的述語（`PSS/Standard.lean:16`）なので `decide` では落ちず、
`¬ STPS Mcex` は未証明である。傍証は 2 つで、**どちらも本ファイル未検証の伝聞**:
(i) engine ヘッダ :60–74 は `python/audit_83_condII_engine.py` が標準形 32056 本に
条件(II) ホストを **0 本**しか見つけなかったと報告する（もし正しければ条件(II) 系は
`ST_PS` 上で空虚であり、restate 後の `Prop` は真だが空虚）;
(ii) Isabelle は `ST_PS` 上で `y3j_condII_tailval` を**定理として**持つ。
`STPS` 版が空虚か否かの決着は本ファイルの担当外（`needs` 参照）。
いずれにせよ **`RT_PS` 版が偽である以上、restate は不可避**である。

- 🚨 **wave-J の数値監査はなぜ見逃したか**（`python/audit_83_condII_tailval_deep.py`）:
  あれは `PSS_LMAX=5`（`Lng ≤ 5`）で走っており「RT_PS 条件(II) ホスト 144 本で
  tailval 144/144 成立・反例 0 ＝ 真らしい」と結論した。**反例はすべて `Lng = 6`**
  なので、`Lng ≤ 5` のプールは原理的に盲。同じスクリプトを `PSS_LMAX=6` で回すと
  反例が出る（`PSS_CAP=6` で 14 本 / `PSS_CAP=8` で 27 本、成分は最大 7）。
  最小反例は**成分 ≤ 2**＝`memo.md` par.3 の危険帯 6〜9 の**遥か手前**であり、
  したがって今回の見逃しは「成分の上限が低すぎた」のではなく **`Lng` の上限が
  低すぎた**（記録済み 13 件の偽陽性とは別の軸）。反例は `M[0] = (0,0)` なので、
  前任監査の「`M[0]` 釘付け」も原因ではない。
  → **教訓: 監査プールは成分と `Lng` の両軸で危険帯を跨げ。**
- 本ファイルの追加監査 `python/audit_83_condII_masterCF_refute.py`:
  `tailval` の破れが `masterCF` の**結論自身**も殺すことを確認した
  （`exists k, Trans (M[n]) = operB (Trans M) (numBT k)` を `n = 2..4`, `k ≤ 40` で
  全数探索。`operB` は `python/_r15_vx_lib.py` の**訂正済み**版＝脚注[30] の
  転置を修正したもの。[[operB-misread]] の再演を避けるため自前実装はしない）:
  * `PSS_CAP=6 PSS_LMAX=6`: ホスト 452 本、tailval 破れ 14 本、**14/14** で
    masterCF の必要条件も破れる。
  * `PSS_CAP=8 PSS_LMAX=6`: ホスト 1148 本、tailval 破れ 27 本、**27/27** で同様。
  いずれも「経路だけ死んで Prop は生存」は **0 本**＝`tailval` の破れは
  `masterCF` の破れと**同値に振る舞う**。上記 Lean 証明はこの数値所見の
  最小反例 1 本を機械証明に昇格させたものである。

- 訂正: **A36 は取り下げ済み**（`corrections-old.md:138`）＝存在形が原文に忠実。
  本ファイルはその点に依存しない。

- 依存（ビルド済みのみ import）: `7.2-scb-fseq`（`scb_fseq_decomp`
  ＝ `m_7_2_scb_fseq_scb`）、`7.3-Trans-welldefined`（`Trans_eq_lengthAux`,
  `Mark_eq_lengthAux`, `unflatBT_flat`, `Trans_mem_T_B`）、
  `8.3-condII-masterCF`（`CondII_TailvalAll`, `CondII_tailval`, `condII_t4`;
  同ファイル経由で engine の `CondII_masterCF`）。

- 状態:
  - `condII_RTPS_counterexample` … ✅ GREEN・無仮定（反例がホスト条件を満たす）。
  - `not_CondII_TailvalAll` … ✅ GREEN・無仮定（`CondII_TailvalAll` は**偽**）。
  - `not_CondII_masterCF` … ✅ GREEN・無仮定（`CondII_masterCF` は**偽**）。
  - sorry 0、axioms = propext/Classical.choice/Quot.sound。
  - 🚨 本ファイルは残差を**減らさない**。engine の `Prop` が偽であることを確定させ、
    `STPS` への restate（＝ «8».«8.3-condII-masterCF» の
    `condII_exchII_of_ST_residuals` 経路）が**必須**であることを機械証明で示す。
-/

namespace PSS

/-! ## 反例の定義

`M = (0,0)(1,1)(2,2)(2,0)(2,2)(2,0)`。`Lng M = 6`、成分は 2 以下。 -/

private def Mcex_tv : PS := [(0,0),(1,1),(2,2),(2,0),(2,2),(2,0)]

/-- 反例で繰り返し現れる principal リスト（`Trans M` の本体の前置）。 -/
private def Yps_tv : List BP :=
  [.db 2 BZero, .db 1 (.trm [.db 2 BZero, .db 0 BZero]), .db 2 BZero]

/-- `Y = D_2 0 + D_1 (D_2 0 + D_0 0) + D_2 0`。 -/
private def Ycex_tv : BT := .trm Yps_tv

/-- `X = D_2 0 + D_0 0 + D_2 0`。**`X ≠ Y`** が反証の核。 -/
private def Xcex_tv : BT := .trm [.db 2 BZero, .db 0 BZero, .db 2 BZero]

/-- `Trans M = D_0 (Y + D_1 (Y + D_0 0))`。 -/
private def TransMcex_tv : BT :=
  .trm [.db 0 (.trm (Yps_tv ++ [.db 1 (.trm (Yps_tv ++ [.db 0 BZero]))]))]

/-- `Trans (M[2]) = D_0 (Y + D_1 X)`。 -/
private def TransO2cex_tv : BT :=
  .trm [.db 0 (.trm (Yps_tv ++ [.db 1 Xcex_tv]))]

/-! ## ホスト条件（すべて `decide`） -/

private theorem hR_tv : RTPS Mcex_tv := by decide
private theorem hmono_tv : monoT Mcex_tv = true := by decide
private theorem hcond_tv : transCondII Mcex_tv = true := by decide
private theorem hj1_tv : 1 < Lng Mcex_tv - 1 := by decide

/-- 反例 `M = (0,0)(1,1)(2,2)(2,0)(2,2)(2,0)` は `CondII_masterCF` /
`CondII_TailvalAll` の仮定を**すべて**満たす（＝空虚な反例ではない）。 -/
theorem condII_RTPS_counterexample :
    RTPS [((0:ℕ),(0:ℕ)),(1,1),(2,2),(2,0),(2,2),(2,0)] ∧
      monoT [((0:ℕ),(0:ℕ)),(1,1),(2,2),(2,0),(2,2),(2,0)] = true ∧
      1 < Lng [((0:ℕ),(0:ℕ)),(1,1),(2,2),(2,0),(2,2),(2,0)] - 1 ∧
      transCondII [((0:ℕ),(0:ℕ)),(1,1),(2,2),(2,0),(2,2),(2,0)] = true :=
  ⟨hR_tv, hmono_tv, hj1_tv, hcond_tv⟩

/-! ## `Trans` の陽な値（`Trans_eq_lengthAux` ＋ `decide`）

`Trans` は整礎再帰なので `decide` は直接効かない。`Trans_eq_lengthAux`
（簡約形では燃料 = `Lng`）で `TransAux` に落としてから `decide` する。
`BT` に `DecidableEq` は無いが `LawfulBEq` があるので `eq_of_beq` で読む。 -/

private theorem Trans_Mcex_val_tv : Trans Mcex_tv = TransMcex_tv := by
  rw [Trans_eq_lengthAux Mcex_tv hR_tv]
  have hL : Lng Mcex_tv = 6 := by decide
  rw [hL]
  exact eq_of_beq (by decide : (TransAux 6 Mcex_tv == TransMcex_tv) = true)

private theorem hRo2_tv : RTPS (oper Mcex_tv 2) := by decide

private theorem Trans_O2cex_val_tv : Trans (oper Mcex_tv 2) = TransO2cex_tv := by
  rw [Trans_eq_lengthAux (oper Mcex_tv 2) hRo2_tv]
  have hL : Lng (oper Mcex_tv 2) = 9 := by decide
  rw [hL]
  exact eq_of_beq
    (by decide : (TransAux 9 (oper Mcex_tv 2) == TransO2cex_tv) = true)

/-! ## `operB` の閉形式（`k` に依らない）

`bOperCore` の定義的簡約は概念どおりに効く: 外側 `D_0` の本体の末尾 principal は
`D_1 BIG` で `domTag BIG = .zeroOnly`（`BIG` の末尾が `D_0 0`）なので、
`.princ` の `.zeroOnly` 枝が発火して `multBT (D_1 (BIG[0])) (numNat z + 1)` になる。
`BIG[0] = Y` であり、`numNat (numBT k) = k`。 -/

private theorem multBT_rep_tv (p : BP) (n : ℕ) :
    multBT (.trm [p]) n = .trm (List.replicate n p) := by
  induction n with
  | zero => simp [multBT, BZero]
  | succ n ih => rw [multBT, ih, addBT, List.replicate_succ']

private theorem numNat_numBT_tv (k : ℕ) : numNat (numBT k) = k := by
  simp [numNat, numBT]

/-- **`operB (Trans M) (numBT k) = D_0 (Y + (D_1 Y) * (k+1))`、全ての `k` で。** -/
private theorem operB_closed_tv (k : ℕ) :
    operB TransMcex_tv (numBT k)
      = .trm [.db 0 (.trm (Yps_tv ++ List.replicate (k+1) (.db 1 Ycex_tv)))] := by
  simp [operB, TransMcex_tv, bOperCore, Dprin, BZero,
        domTag, domTagList, domTagBP, numNat_numBT_tv, multBT_rep_tv,
        addBT, Ycex_tv, Yps_tv]

/-- 反証の核: `X ≠ Y`。`BT` に `DecidableEq` は無いので `LawfulBEq` 経由。 -/
private theorem Xcex_ne_Ycex_tv : Xcex_tv ≠ Ycex_tv :=
  ne_of_beq_false (by decide : (Xcex_tv == Ycex_tv) = false)

/-- **`Trans (M[2])` は `Trans M` の基本列のどの項でもない。**
`operB` 側の本体末尾は `k` に依らず `D_1 Y`、`Trans (M[2])` 側は `D_1 X`。 -/
private theorem no_operB_step_tv (k : ℕ) :
    Trans (oper Mcex_tv 2) ≠ operB (Trans Mcex_tv) (numBT k) := by
  rw [Trans_O2cex_val_tv, Trans_Mcex_val_tv, operB_closed_tv k]
  intro h
  unfold TransO2cex_tv at h
  -- 外側 `D_0` の本体まで剥がす
  injection h with hl
  injection hl with hp _
  injection hp with _ hb
  injection hb with h2
  -- `Yps ++ [D_1 X] = Yps ++ replicate (k+1) (D_1 Y)`
  have h3 : [BP.db 1 Xcex_tv] = List.replicate (k+1) (.db 1 Ycex_tv) :=
    List.append_cancel_left h2
  -- `replicate (k+1)` は必ず `D_1 Y` で始まる。よって `X = Y` となり矛盾
  rw [List.replicate_succ] at h3
  injection h3 with h4 _
  injection h4 with _ hb2
  exact Xcex_ne_Ycex_tv hb2

/-! ## `CondII_TailvalAll`（`RT_PS` 版 tailval）は**偽**

`W = Trans (seg M j₀ (Lng M - 2)) = D_1 X` だが `D_{M₁,ⱼ₀} t₄ = D_1 Y`。
`t₄` は `transT2 M = bpHeadT (Mark (Pred M) (transJm1 M))` 経由なので、
`Mark_eq_lengthAux` で `MarkAux` に落として計算する。 -/

private theorem hRpred_tv : RTPS (Pred Mcex_tv) := by decide
private theorem hRseg_tv : RTPS (seg Mcex_tv 1 4) := by decide

/-- `transC1 M = Mark (Pred M) 0 = D_0 Y`、ゆえに `transT2 M = Y`。 -/
private theorem transC1_val_tv : transC1 Mcex_tv = Dprin 0 Ycex_tv := by
  have hj : transJm1 Mcex_tv = 0 := by decide
  rw [transC1, hj, Mark_eq_lengthAux (Pred Mcex_tv) 0 hRpred_tv]
  have hL : Lng (Pred Mcex_tv) = 5 := by decide
  rw [hL]
  exact eq_of_beq
    (by decide : (MarkAux 5 (Pred Mcex_tv) 0 == Dprin 0 Ycex_tv) = true)

/-- `W = Trans (seg M j₀ (Lng M - 2)) = D_1 X`。 -/
private theorem W_val_tv :
    Trans (seg Mcex_tv (parent Mcex_tv 0 (Lng Mcex_tv - 1)) (Lng Mcex_tv - 2))
      = Dprin 1 Xcex_tv := by
  have hj : parent Mcex_tv 0 (Lng Mcex_tv - 1) = 1 := by decide
  have hL2 : Lng Mcex_tv - 2 = 4 := by decide
  rw [hj, hL2, Trans_eq_lengthAux (seg Mcex_tv 1 4) hRseg_tv]
  have hL : Lng (seg Mcex_tv 1 4) = 4 := by decide
  rw [hL]
  exact eq_of_beq
    (by decide : (TransAux 4 (seg Mcex_tv 1 4) == Dprin 1 Xcex_tv) = true)

/-- **`CondII_TailvalAll` は偽**（«8».«8.3-condII-masterCF»:739 の残差 2/2）。
これを証明しようとするのは偽命題を追うことに等しい。 -/
theorem not_CondII_TailvalAll : ¬ CondII_TailvalAll := by
  intro h
  have hTV : CondII_tailval Mcex_tv := h Mcex_tv hR_tv hmono_tv hj1_tv hcond_tv
  rw [CondII_tailval, W_val_tv] at hTV
  -- `t₄` を計算: `ldj` は偽なので `t₄ = transT2 M = Y`
  have ht2 : transT2 Mcex_tv = Ycex_tv := by
    rw [transT2, transC1_val_tv]; simp [bpHeadT, Dprin]
  have hldj : condII_ldj Mcex_tv = false := by
    rw [condII_ldj, condII_pj, ht2]; decide
  have ht4 : condII_t4 Mcex_tv = Ycex_tv := by
    simp [condII_t4, hldj, ht2]
  have hv0 : entry Mcex_tv 1 (parent Mcex_tv 0 (Lng Mcex_tv - 1)) = 1 := by decide
  rw [ht4, hv0] at hTV
  -- `D_1 X = D_1 Y` から `X = Y`、矛盾
  unfold Dprin at hTV
  injection hTV with hl
  injection hl with hp _
  injection hp with _ hb
  exact Xcex_ne_Ycex_tv hb

/-! ## `CondII_masterCF` は**偽**

`masterCF` の witness から `∃ k, Trans (M[n]) = operB (Trans M) (numBT k)` が出る
（engine:165/191 の private 2 本と同内容の複製）。それが `no_operB_step_tv` と矛盾。 -/

/-- Isabelle `operB_marked_scb_value` (pss_wip.thy:37100)。engine:165 の複製
（private は module を跨げない）。 -/
private theorem operB_marked_scb_value_tv {t₀ t₁ t : BT} {u v n : ℕ}
    {s b : List Sym}
    (ht₀ : t₀ ∈ T_B) (ht₁ : t₁ ∈ T_B) (ht : t ∈ T_B)
    (hd : scb_decomp t s
      (flatBT (Dprin (u : ℕ∞)
        (addBT t₀ (Dprin (v : ℕ∞) (addBT t₁ (Dprin 0 BZero)))))) b) :
    operB t (numBT n)
      = unflatBT (s ++ flatBT (Dprin (u : ℕ∞)
          (addBT t₀ (multBT (Dprin (v : ℕ∞) t₁) (n + 1)))) ++ b) := by
  have hd2 := scb_fseq_decomp (n := n) ht₀ ht₁ ht hd
  have hfe : flatBT (operB t (numBT n))
      = s ++ flatBT (Dprin (u : ℕ∞)
          (addBT t₀ (multBT (Dprin (v : ℕ∞) t₁) (n + 1)))) ++ b := hd2.1
  calc operB t (numBT n)
      = unflatBT (flatBT (operB t (numBT n))) := (unflatBT_flat _).symm
    _ = _ := by rw [hfe]

/-- Isabelle `c2ex_exch_of_lhs_closed_ex` (pss_wip.thy:70717)。engine:191 の複製。 -/
private theorem exch_of_lhs_closed_ex_tv
    {M : PS} {n u v : ℕ} {t₀ t₁ : BT} {s b : List Sym}
    (ht₀ : t₀ ∈ T_B) (ht₁ : t₁ ∈ T_B) (htT : Trans M ∈ T_B)
    (hd : scb_decomp (Trans M) s
      (flatBT (Dprin (u : ℕ∞)
        (addBT t₀ (Dprin (v : ℕ∞) (addBT t₁ (Dprin 0 BZero)))))) b)
    (hlhs : ∀ m, 1 < m → ∃ c, 1 ≤ c ∧ Trans (oper M m)
      = unflatBT (s ++ flatBT (Dprin (u : ℕ∞)
          (addBT t₀ (multBT (Dprin (v : ℕ∞) t₁) c))) ++ b))
    (hn : 1 < n) :
    ∃ k, Trans (oper M n) = operB (Trans M) (numBT k) := by
  obtain ⟨c, hc1, hlc⟩ := hlhs n hn
  obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
  refine ⟨k, ?_⟩
  rw [hlc, operB_marked_scb_value_tv (n := k) ht₀ ht₁ htT hd]

/-! ## `CondII_masterCF` の **RT_PS 形は偽**（2026-07-17 の発見、史料として機械証明で保存）

発見当時、`«8».«8.3-TransCondII-engine»` の `CondII_masterCF` は **`RTPS M`** 上で
述べられており（Isabelle の `masterCF` の `MR : M ∈ RT_PS` に合わせたため）、
`lean/8/8.7-termination.lean` の `TerminationResidual` はそれをフィールドに持っていた。
下の `not_CondII_masterCF_RTPS_form` が示すとおり **その形は偽**なので、束は充足不能＝
主定理は型検査を通っても空虚だった。

**原因**: Isabelle の `c2sx_condII_masterCF`(87430) は `TV : c2sx_tailval M` を仮定に持ち、
その discharger `y3j_condII_tailval`(layerC:17079) は **`M ∈ ST_PS`** を要求する。
`RT_PS ⟹ tailval` は Isabelle に存在せず、実際 `not_CondII_TailvalAll` のとおり偽。

**対処（親、同日）**: engine の `CondII_masterCF` を **`STPS M`** に restate（消費者は
いずれも `STPS` を持っていて `STPS_RTPS` で弱めていただけなので、そのまま通る）。
その結果、この反例では **STPS 版は反証されない**（＝反例列は `ST_PS` に属さない）。
以下はその当時の RT_PS 形を**ローカルに再現**して反証を保存したもの。 -/

/-- 当時 engine が露出していた `CondII_masterCF` の **RT_PS 形**（史料）。 -/
def CondII_masterCF_RTPS_form : Prop :=
  ∀ M : PS, RTPS M → monoT M = true → 1 < Lng M - 1 → transCondII M = true →
    ∃ (s b : List Sym) (u v : ℕ) (t₀ t₁ : BT), t₀ ∈ T_B ∧ t₁ ∈ T_B ∧
      scb_decomp (Trans M) s
        (flatBT (Dprin (u : ℕ∞)
          (addBT t₀ (Dprin (v : ℕ∞) (addBT t₁ (Dprin 0 BZero)))))) b ∧
      (∀ m, 1 < m → ∃ c, 1 ≤ c ∧ Trans (oper M m)
        = unflatBT (s ++ flatBT (Dprin (u : ℕ∞)
            (addBT t₀ (multBT (Dprin (v : ℕ∞) t₁) c))) ++ b))

/-- 🚨 **`CondII_masterCF` の RT_PS 形は偽**（反例 `Mcex_tv`、非空虚）。 -/
theorem not_CondII_masterCF_RTPS_form : ¬ CondII_masterCF_RTPS_form := by
  intro hCF
  obtain ⟨s, b, u, v, t₀, t₁, ht₀, ht₁, hd, hlhs⟩ :=
    hCF Mcex_tv hR_tv hmono_tv hj1_tv hcond_tv
  have htT : Trans Mcex_tv ∈ T_B := Trans_mem_T_B Mcex_tv hR_tv
  obtain ⟨k, hk⟩ :=
    exch_of_lhs_closed_ex_tv ht₀ ht₁ htT hd hlhs (by norm_num : (1:ℕ) < 2)
  exact no_operB_step_tv k hk

#print axioms condII_RTPS_counterexample
#print axioms not_CondII_TailvalAll
#print axioms not_CondII_masterCF_RTPS_form

end PSS
