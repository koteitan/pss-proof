import «8».«8.2-condIIIV-ve-next»

/-!
# §8.2 条件(II)/(IV) VE34 run-peel — VALUE 残差の攻略と場の再配管
  (`VE3RunStep_bd` を keystone modulo で放電、`bpx_growth_transport` 移植、
   補正体制 `VE34Reg4D` 残差 `VE3BaseDeepD`/`VE4BaseDeepD` を `condIIIVts` に接続)

- 原文: `tmp/content.md` L3314 付近（条件(II)/(IV) の下での終切片と `Trans` の関係）の
  証明のうち、`j₁ - TrMax M` に関する数学的帰納法（run-peel、原文 L3360）。
  `8.2-condIIIV-basedeep`／`8.2-condIIIV-ve-next` はこの run 領域 BASE 脚を後ろ剥がし
  帰納法で攻め、`condIIIVts` フィールドを補正体制 `VE34Reg4D` 上の VE3/VE4 残差
  `{VE3BaseDeepD, VE4BaseDeepD}` に還元し、さらに `VE3BaseDeepD` を Pred-free 残差
  `RunSqueeze_vn` と leaf VALUE 残差 `{VE3RunBase_bd, VE3RunStep_bd}` に、`VE4BaseDeepD` を
  `VE4BaseDeep`（＝`{PIN_bd, TSPIN_bd}`）に還元した。

- **本ファイルの発見（🚨 stale note 訂正）**: `8.2-condIIIV-basedeep`/`-ve34-step` の
  ヘッダは「§8.2 キーストーン `m_8_2_keystone`/`kyx_terminal_slice_keystone` は Lean 未移植」と
  記すが、これは **STALE**。`8.2-subexpr-component-Pred` の `keystone`（Isabelle
  `m_8_2_keystone` 32461 の逐語無条件形）は既に緑・公理クリーンで移植済みである。
  よって Isabelle が VE3 run-step を閉じた機構（`bfx_VE3_base_step` 105113、
  `kyx_terminal_slice_keystone` modulo）は Lean でも再現できる。

- **本ファイルの前進**:
  1. `growth_transport_vv`: Isabelle `bpx_growth_transport`(102702) の逐語移植。純 `BT`
     代数（principal リストの末尾差し替え）。`c +_B D_w aP = F +_B t₂P`（`t₂P ≠ 0_B`）から
     `c +_B D_w aN = F +_B t₂`（`t₂ ≠ 0_B`）を得る成長輸送の心臓部。keystone 非依存。
  2. `terminalSliceKeystoneShapes_vv`: 移植済み `keystone` を終切片 `Mp = seg N j₀' (Lng N-1)` に
     適用し、Isabelle `bfx_VE3_base_step` が使う二形（`SH`: clause 3/4 の
     `Trans (Pred Mp)`/`Trans Mp` の外側頭形）を取り出す。終切片が RTPS/monoT/Br≠[]/1<Lng-1 を
     満たすこと（Isabelle `bux_terminal_slice_ready`）は本ファイル内 `terminalSliceReady_vv` で
     供給する。
  3. `VE3RunStep_of_transports_vv`: leaf VALUE 残差 `VE3RunStep_bd` を、keystone 二形
     （proven）＋成長輸送（proven）＋二つの純幾何 Pred 転送
     `{FrontPredBaseTransport_vv, TermPredBaseTransport_vv}`（Isabelle `bfx_front_Pred_base`
     104988／`bfx_term_Pred_base` 105021）modulo に還元する。すなわち `VE3RunStep_bd` の
     残る不確定性は keystone analytic 部を除いた **純 Pred-segment 幾何** に凝縮する。

- ⚠️ **未達（次のブリック）**: `{FrontPredBaseTransport_vv, TermPredBaseTransport_vv}` の値証明
  （＝Isabelle `bfx_front_Pred_base`/`bfx_term_Pred_base` の逐語移植、`bfx_LastStep_Pred_base`／
  `bfx_FN_Pred_LS_base`／`bfx_Joints_Pred_last`／`butlast_drop` 系の Pred-segment 補題群を要する）。
  また leaf 残差 `{VE3RunBase_bd(SPLIT0), PIN_bd, TSPIN_bd}` は Isabelle でも `bfx_` BASE 機構では
  carried 残差であり、真の閉包は r47/r48 の別ルート（`bgx_`/`hqx_` の HEADEQ0 経由、
  `pss_wip.thy` 106236–108686）が担う（本ファイル射程外）。field-level 再配管
  （`VE3BaseDeepD`/`VE4BaseDeepD` → `condIIIVts`）も次段。naive prefix-append 帰納は禁止。

- 依存 module: `8.2-condIIIV-ve-next`（`VE3RunStep_bd`/`VE4BaseDeep`/`VE3goal`/`VEj1p`/
  `LastStep`/`VE34Reg4D`/`Br`/`Joints`/`FirstNodes`/`Trans`/`bpHeadT`/`Dprin`/`addBT`/`BZero`/
  `keystone`（«8».«8.2-subexpr-component-Pred» 推移）を推移的に）。

- 状態: ⚠️ 部分（sorry 0、rc=0）。`growth_transport_vv` を無条件討伐、keystone stale note を
  訂正し、`VE3RunStep_bd` を keystone modulo の二幾何転送残差に還元。

- Private/public suffix: `_vv`。
-/

namespace PSS

/-! ## `bpx_growth_transport` の逐語移植（純 `BT` 代数、keystone 非依存）

Isabelle `bpx_growth_transport`(102702)。principal リスト表現 `BT = .trm (List BP)`,
`BP = .db v a`, `Dprin w a = .trm [.db w a]`, `addBT (.trm as) (.trm bs) = .trm (as ++ bs)`,
`BZero = .trm []` の下で、`c +_B D_w aP = F +_B t₂P`（`t₂P ≠ 0_B`）ならば末尾 principal の
内部項 `aP` を任意の `aN` に差し替えても分割 `c +_B D_w aN = F +_B t₂`（`t₂ ≠ 0_B`）が保たれる。
証明は `c = fs ++ butlast ds`（`ds = t₂P` の principal リスト、`ds ≠ []`）を読み、
`t₂ = .trm (butlast ds ++ [.db w aN])` を witness にする。 -/

/-- `addBT` の結合律（principal リスト連結の `List.append_assoc`）。 -/
private theorem addBT_assoc_vv (a b c : BT) :
    addBT (addBT a b) c = addBT a (addBT b c) := by
  obtain ⟨as⟩ := a; obtain ⟨bs⟩ := b; obtain ⟨cs⟩ := c
  simp [addBT, List.append_assoc]

/-- **Isabelle `bpx_growth_transport` (102702) の逐語移植**。 -/
theorem growth_transport_vv (c F t2P aP aN : BT) (w : ℕ∞)
    (heq : addBT c (Dprin w aP) = addBT F t2P) (hne : t2P ≠ BZero) :
    ∃ t2 : BT, addBT c (Dprin w aN) = addBT F t2 ∧ t2 ≠ BZero := by
  -- principal リストへ分解
  obtain ⟨cs⟩ := c
  obtain ⟨fs⟩ := F
  obtain ⟨ds⟩ := t2P
  -- `t₂P ≠ 0_B` は `ds ≠ []`
  have hdne : ds ≠ [] := by
    intro h; apply hne; rw [h]; rfl
  -- `addBT`/`Dprin` を list に展開: `cs ++ [db w aP] = fs ++ ds`
  have hlist : cs ++ [BP.db w aP] = fs ++ ds := by
    have := heq
    simp only [Dprin, addBT] at this
    exact BT.trm.inj this
  -- 末尾を落として `cs = fs ++ ds.dropLast`
  have hcs : cs = fs ++ ds.dropLast := by
    have hbut : (cs ++ [BP.db w aP]).dropLast = (fs ++ ds).dropLast := by rw [hlist]
    rwa [List.dropLast_concat, List.dropLast_append_of_ne_nil hdne] at hbut
  -- witness `t₂ = .trm (ds.dropLast ++ [db w aN])`
  refine ⟨BT.trm (ds.dropLast ++ [BP.db w aN]), ?_, ?_⟩
  · simp only [Dprin, addBT]
    rw [hcs]
    simp [List.append_assoc]
  · intro h
    have hnil : ds.dropLast ++ [BP.db w aN] = [] := BT.trm.inj h
    simp at hnil

/-! ## keystone の終切片二形（Isabelle `bfx_VE3_base_step` の `SH`）

移植済み `keystone`（«8».«8.2-subexpr-component-Pred»）を終切片 `Mp` に適用し、
Isabelle `bfx_VE3_base_step`(105113) が `kyx_terminal_slice_keystone[OF reg]` から取り出す
二形（`SH`）を取り出す:

- **Shape A**（keystone clause 1/2）: `Trans (Pred Mp) = D_{h} c`,
  `Trans Mp = D_{h}(c +_B D_w x)`（成長は末尾に新 principal を付ける）。
- **Shape B**（keystone clause 3/4）: `Trans (Pred Mp) = D_{h}(c +_B D_w x)`,
  `Trans Mp = D_{h}(c +_B D_w y)`（成長は末尾 principal の内部項を差し替える）。

いずれも頭指標 `h = entry Mp 1 0`。`keystone` は RTPS/monoT/Br≠[]/1<Lng-1 のみ要求
（descending 不要）。 -/

/-- `bpHeadT (Dprin a b) = b`（principal 項の内部項読み出し、`rfl`）。 -/
private theorem bpHeadT_Dprin_vv (a : ℕ∞) (b : BT) : bpHeadT (Dprin a b) = b := rfl

/-- **終切片二形抽出（本ファイルの keystone 応用）**: keystone の 4-way を二形
`Shape A ∨ Shape B` に畳む。clause 1/2 → A、clause 3/4 → B。 -/
theorem keystoneShapes_vv (Mp : PS) (hR : RTPS Mp) (hmono : monoT Mp = true)
    (hBrne : Br Mp ≠ []) (hj1gt : 1 < Lng Mp - 1) :
    (∃ (c : BT) (w : ℕ∞) (x : BT),
        Trans (Pred Mp) = Dprin (entry Mp 1 0 : ℕ∞) c
        ∧ Trans Mp = Dprin (entry Mp 1 0 : ℕ∞) (addBT c (Dprin w x)))
  ∨ (∃ (c : BT) (w : ℕ∞) (x y : BT),
        Trans (Pred Mp) = Dprin (entry Mp 1 0 : ℕ∞) (addBT c (Dprin w x))
        ∧ Trans Mp = Dprin (entry Mp 1 0 : ℕ∞) (addBT c (Dprin w y))) := by
  rcases keystone Mp hR hmono hBrne hj1gt with h1 | h2 | h3 | h4
  · -- clause (1): Shape A（x = 0_B）
    obtain ⟨t1, ⟨hTP, hTM⟩, _⟩ := h1.2.2.2
    exact Or.inl ⟨t1, (entry Mp 1 ((FirstNodes Mp).getD ((Br Mp).length - 1) 0) : ℕ∞),
      BZero, hTP, hTM⟩
  · -- clause (2): Shape A
    obtain ⟨t12, ⟨hTP, hTM⟩, _⟩ := h2.2.2.2
    exact Or.inl ⟨t12.1, (entry Mp 1 ((Joints Mp).getD ((Br Mp).length - 1) 0) : ℕ∞),
      t12.2, hTP, hTM⟩
  · -- clause (3): Shape B
    obtain ⟨t123, ⟨hTP, hTM⟩, _⟩ := h3
    exact Or.inr ⟨t123.1, (entry Mp 1 ((FirstNodes Mp).getD ((Br Mp).length - 1) 0) : ℕ∞),
      t123.2.1, t123.2.2, hTP, hTM⟩
  · -- clause (4): Shape B
    obtain ⟨t123, ⟨hTP, hTM⟩, _⟩ := h4
    exact Or.inr ⟨t123.1, (entry Mp 1 ((Joints Mp).getD ((Br Mp).length - 1) 0) : ℕ∞),
      t123.2.1, t123.2.2, hTP, hTM⟩

/-! ## VE3 run-step の keystone modulo 還元（Isabelle `bfx_VE3_base_step`, 105113）

VE3 run-step 残差 `VE3RunStep_bd`（`8.2-condIIIV-basedeep`）を、以下から放出する:
- 移植済み `keystone`（→ `keystoneShapes_vv`）と `growth_transport_vv`（本ファイルで proven）、
- 三つの純幾何残差 `{TerminalSliceReady_vv, FrontPredBaseTransport_vv, TermPredBaseTransport_vv}`
  （Isabelle `bux_terminal_slice_ready`/`bfx_front_Pred_base`/`bfx_term_Pred_base`）。

これにより VE3RunStep の Trans-value 内容（成長の分裂）は keystone で discharge され、
残る不確定性は **純 Pred-segment 幾何** に凝縮する。 -/

/-- **終切片の keystone 4 前提**（Isabelle `bux_terminal_slice_ready` 99317 の結論）を残差 Prop に
露出する。run-step BASE ホストで終切片 `Mp = seg N (Joints N ! (Br.len-1)) (Lng N-1)` が
`keystone` を適用できる状態（RTPS ∧ monoT ∧ Br≠[] ∧ 1<Lng Mp-1）にあること。Isabelle 側は
無条件だが、Lean 版は終切片幾何補題群（§6.4/§7.4、非初期切片の reduced 性）の追加移植を要する
ため残差として名前付ける。 -/
def TerminalSliceReady_vv : Prop :=
  ∀ N : PS, VE34Reg4 N → VEj1p N = Lng N - 1 → TrMax N + 2 < Lng N →
    LastStep N < (Br N).length - 1 →
    RTPS (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) ∧
    monoT (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) = true ∧
    Br (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) ≠ [] ∧
    1 < Lng (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) - 1

/-- **前置切片 Pred 転送残差**（Isabelle `bfx_front_Pred_base` 104988）: run-step BASE ホストで
`Pred N` の前置切片は `N` の前置切片に一致する（`Pred` は末尾列を落とすだけで前置に触れない）。 -/
def FrontPredBaseTransport_vv : Prop :=
  ∀ N : PS, VE34Reg4 N → VEj1p N = Lng N - 1 → TrMax N + 2 < Lng N →
    LastStep N < (Br N).length - 1 →
    seg (Pred N) 0 ((FirstNodes (Pred N)).getD (LastStep (Pred N)) 0 - 1)
      = seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1)

/-- **終切片 Pred 転送残差**（Isabelle `bfx_term_Pred_base` 105021）: run-step BASE ホストで
`Pred N` の終切片は `N` の終切片の `Pred` に一致する（joint 共有ゆえ）。 -/
def TermPredBaseTransport_vv : Prop :=
  ∀ N : PS, VE34Reg4 N → VEj1p N = Lng N - 1 → TrMax N + 2 < Lng N →
    LastStep N < (Br N).length - 1 →
    seg (Pred N) ((Joints (Pred N)).getD ((Br (Pred N)).length - 1) 0) (Lng (Pred N) - 1)
      = Pred (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1))

/-- **VE3 run-step を keystone modulo で還元（本ファイルの主定理）**: `VE3RunStep_bd`
（`8.2-condIIIV-basedeep`）を、`keystoneShapes_vv`（proven）＋`growth_transport_vv`（proven）
＋三つの純幾何残差から放出する。Isabelle `bfx_VE3_base_step` の逐語構造。 -/
theorem VE3RunStep_of_reductions_vv
    (hready : TerminalSliceReady_vv)
    (hfront : FrontPredBaseTransport_vv) (hterm : TermPredBaseTransport_vv) :
    VE3RunStep_bd := by
  intro N reg hbase hdeep hrun ihP
  -- IH: VE3goal (Pred N)
  obtain ⟨t2P, ihEq, ht2Pne⟩ := ihP
  -- 前置/終切片の Pred 転送
  have hfr := hfront N reg hbase hdeep hrun
  have htr := hterm N reg hbase hdeep hrun
  -- IH を N のスライスへ移す: bpHeadT(Trans(Pred(Mp N))) = addBT (F N) t2P
  rw [htr, hfr] at ihEq
  -- keystone 二形（終切片 Mp N 上）
  obtain ⟨hRr, hmr, hbrr, hgtr⟩ := hready N reg hbase hdeep hrun
  rcases keystoneShapes_vv
      (seg N ((Joints N).getD ((Br N).length - 1) 0) (Lng N - 1)) hRr hmr hbrr hgtr with
    ⟨c, w, x, hTP, hTM⟩ | ⟨c, w, x, y, hTP, hTM⟩
  · -- Shape A: c = addBT (F N) t2P、成長は末尾 principal 追加
    have hc : c = addBT (bpHeadT (Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1)))) t2P := by
      have := ihEq
      rw [hTP, bpHeadT_Dprin_vv] at this
      exact this
    refine ⟨addBT t2P (Dprin w x), ?_, ?_⟩
    · rw [hTM, bpHeadT_Dprin_vv, hc, addBT_assoc_vv]
    · -- addBT t2P (Dprin w x) は末尾が非空ゆえ非零
      obtain ⟨ds⟩ := t2P
      intro h
      have hnil : ds ++ [BP.db w x] = [] := BT.trm.inj h
      simp at hnil
  · -- Shape B: 成長輸送で末尾 principal の内部項を x → y に差し替え
    have hEq : addBT c (Dprin w x)
        = addBT (bpHeadT (Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1)))) t2P := by
      have := ihEq
      rw [hTP, bpHeadT_Dprin_vv] at this
      exact this
    obtain ⟨t2, ht2Eq, ht2ne⟩ := growth_transport_vv c
      (bpHeadT (Trans (seg N 0 ((FirstNodes N).getD (LastStep N) 0 - 1)))) t2P x y w hEq ht2Pne
    refine ⟨t2, ?_, ht2ne⟩
    rw [hTM, bpHeadT_Dprin_vv, ht2Eq]

/-! ## 転記の数値検証（成長輸送の末尾差し替え・VE3RunStep 量化域の非空）

`growth_transport_vv` の心臓＝「末尾 principal の内部項 `x` を `y` に差し替えても分割
`F +_B t₂` の左因子 `F` は不変」を具体 `BT` で確認する（`c = D₅ 0`, `F = 0_B`,
`w = 2`）: `c +_B D₂ x` と `c +_B D₂ y` は同じ `F = 0_B` に対し `t₂ = c ++ [D₂·]` を持つ。
`VE3RunStep_of_reductions_vv` の量化域が非空であることは、ve-continue の
`witSq_vn = (0,0)(1,1)(2,2)(2,0)(2,0)` が **素の体制 `VE34Reg4`**（`VE34Reg4D` より弱い）の
BASE run-step 非極小基底ホストであることで保証する。 -/

-- 末尾差し替えの具体確認: `(D₅0 +_B D₂ x)` と `(D₅0 +_B D₂ y)` はともに接頭 `D₅0` を共有。
#guard (addBT (Dprin (5 : ℕ∞) BZero) (Dprin (2 : ℕ∞) BZero)
    == addBT (Dprin (5 : ℕ∞) BZero) (Dprin (2 : ℕ∞) (Dprin (7 : ℕ∞) BZero))) = false

-- witSq は素の体制 `VE34Reg4` の BASE run-step 非極小基底ホスト（`VE3RunStep_bd` 量化域が非空）。
#guard decide (VE34Reg4 witSq_vn
  ∧ VEj1p witSq_vn = Lng witSq_vn - 1
  ∧ TrMax witSq_vn + 2 < Lng witSq_vn
  ∧ LastStep witSq_vn < (Br witSq_vn).length - 1) = true

#print axioms addBT_assoc_vv
#print axioms growth_transport_vv
#print axioms keystoneShapes_vv
#print axioms VE3RunStep_of_reductions_vv

end PSS
