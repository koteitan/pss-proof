import «7».«7.3-Trans-welldefined»

/-!
# PSS.«8».«8.7-otint-transport-prims» — OT transport pillar の基礎語彙 (BANK)

`OTdisp_OTint` / `OTdisp_OTmulti`（§8.7 の最重量 leaf）が次 wave で必要とする
transport 定理 `oix_transport` / `oix_transportD` の **base layer** を先取りする。
close ではなく infrastructure BANK。

## 移植元 (isabelle/layerB/pss_wip.thy)

- `d4vx_ins` (definition, wip:63756) — scb ブロック挿入作用素。
- `d4vx_core` (fun, wip:63759) — 挿入の反復タワー（condIV の `M[n]` core）。
- `d4vx_ins_flat` (wip:63768) — 挿入 1 段の flat 法則。
- `b1x_setle` (definition, wip:50305) — [Buc1] §3 の `⊴` (G-part) 集合順序。
- `b1x_setle_subset` / `b1x_setle_widen` / `b1x_setle_union` (wip:50308–50316)。
- `b1x_triG` (definition, wip:50325) — Buchholz `b ◁_z a` の G-control 連言。
- `b1x_triG_I` / `b1x_triG_D` (wip:50331–50340)。

## 既存資産（grep 済・再証明せず import）

- `flatBT` / `flatBP` / `Sym` = `PSS.Scb`（原 primitive）。
- `unflatBT` = `PSS.Trans`；`unflatBT_flat` = `«7».«7.3-Trans-welldefined»`。
- 像存在補題 `scbimg_image_BT` の Lean twin = `principal_replacement_image`
  (`«7».«7.2-scb-replaceable»`)。ただし後述の仮定差あり。
- `GBT`/`GBP`/`leBT`/`T_B`/`TBv`/`Dprin`/`BZero`/`dfree_BP` = `PSS.Buchholz`
  （GBT/GBP は Lean twin あり、再定義不要）。
- `LawfulBEq BT` = `PSS.Buchholz`（`leBT x x = true` に使用）。

## 忠実性の注記（parent への申し送り）

`d4vx_ins_flat` は Isabelle 版が `wrap` + `b0RP`（全 `RP` 末尾）の 2 仮定のみ
（`T_B` 不要）で、その証明は忠実な像補題 `scbimg_image_BT`（`T_B` 不要・全 `RP`
末尾必須）に依存する。この忠実版の Lean twin は `«7».«7.2-scb-outer-surgery-split»`
の **private** `surg_image_sos` (行 197) だけで、import 不可。よって本 BANK では
**public な** `principal_replacement_image`（`T_B` 必須・全 `RP` 末尾不要）を用い、
`d4vx_ins_flat` に `hW : W ∈ T_B` と `hX : X ∈ T_B` を **追加**した（Isabelle より
仮定を増やした＝より弱い＝安全）。下流 condIV 応用では `W`, `X` は真の Buchholz 項
なので `T_B` 条件は常に満たされ、支障はない。`surg_image_sos` を public 化すれば
Isabelle 忠実な（`T_B` 不要）版に置換可能——parent 判断で promote 推奨。

## 状態

defs + `d4vx_ins_flat`（T_B 版）+ `b1x_setle` basics + `b1x_triG` I/D を public 着地。
sorry 0 / axioms = [propext, Classical.choice, Quot.sound]。private helper 接尾辞 `_tp`。
-/

namespace PSS

/-! ## §condIV core tower: `d4vx_ins` / `d4vx_core` -/

/-- Isabelle `d4vx_ins` (layerB/pss_wip.thy:63756):
    `d4vx_ins s0 ub b0 X = unflatBT (s0 @ flatBT (D_{ub} X) @ b0)`。
    scb ブロック挿入作用素（右端の穴 `D_{ub} 0` を `D_{ub} X` で置換する読み戻し）。 -/
def d4vx_ins (s0 : List Sym) (ub : ℕ) (b0 : List Sym) (X : BT) : BT :=
  unflatBT (s0 ++ flatBT (Dprin (ub : ℕ∞) X) ++ b0)

/-- Isabelle `d4vx_core` (layerB/pss_wip.thy:63759): 挿入 `d4vx_ins` の `k` 反復タワー。
    `d4vx_core s0 ub b0 t 0 = t`、`… (k+1) = d4vx_ins s0 ub b0 (… k)`。 -/
def d4vx_core (s0 : List Sym) (ub : ℕ) (b0 : List Sym) (t : BT) : ℕ → BT
  | 0 => t
  | k + 1 => d4vx_ins s0 ub b0 (d4vx_core s0 ub b0 t k)

@[simp] theorem d4vx_core_zero (s0 : List Sym) (ub : ℕ) (b0 : List Sym) (t : BT) :
    d4vx_core s0 ub b0 t 0 = t := rfl

@[simp] theorem d4vx_core_succ (s0 : List Sym) (ub : ℕ) (b0 : List Sym) (t : BT) (k : ℕ) :
    d4vx_core s0 ub b0 t (k + 1) = d4vx_ins s0 ub b0 (d4vx_core s0 ub b0 t k) := rfl

/-- 主項の flat 展開（局所補題）。`flatBT (D_v a) = Dsym v :: flatBT a`。 -/
private theorem flatBT_Dprin_tp (v : ℕ∞) (a : BT) :
    flatBT (Dprin v a) = Sym.dsym v :: flatBT a := by
  simp [Dprin, flatBT, flatBP]

/-- Isabelle `d4vx_ins_flat` (layerB/pss_wip.thy:63768) の **T_B 版**。
    挿入 1 段はその flat 文字列を読み出す。

    Isabelle 忠実版は `wrap` + `b0RP` のみ（`T_B` 不要）だが、その像存在エンジン
    `scbimg_image_BT` の Lean twin は private（module docstring 参照）。本版は public な
    `principal_replacement_image` を用いるため `W`, `X` の `T_B` 所属を追加している。 -/
theorem d4vx_ins_flat {W X : BT} {hole : BP} {s0 b0 : List Sym} {ub : ℕ}
    (hW : W ∈ T_B) (hX : X ∈ T_B)
    (wrap : flatBT W = s0 ++ flatBP hole ++ b0)
    (_b0RP : ∀ x ∈ b0, x = Sym.rp) :
    flatBT (d4vx_ins s0 ub b0 X)
      = s0 ++ Sym.dsym (ub : ℕ∞) :: flatBT X ++ b0 := by
  have hXdf : dfree_BT X = true := hX
  have hpr' : dfree_BP (BP.db (ub : ℕ∞) X) = true := by
    simp [dfree_BP, ENat.coe_ne_top, hXdf]
  -- 像の存在: `hole` を `D_{ub} X` で置換しても `flatBT` の像に留まる。
  obtain ⟨t', _ht'mem, ht'⟩ :=
    principal_replacement_image (pr := hole) (pr' := BP.db (ub : ℕ∞) X) hW hpr' wrap
  -- ht' : flatBT t' = s0 ++ flatBP (D_{ub} X) ++ b0 = s0 ++ Dsym ub :: flatBT X ++ b0
  have harg : s0 ++ flatBT (Dprin (ub : ℕ∞) X) ++ b0 = flatBT t' := by
    rw [ht', flatBT_Dprin_tp]
    simp [flatBP]
  have hins : d4vx_ins s0 ub b0 X = t' := by
    unfold d4vx_ins
    rw [harg, unflatBT_flat]
  rw [hins, ht']
  simp [flatBP]

/-! ## [Buc1] §3 の `⊴_z` (G-part): `b1x_setle` -/

/-- Isabelle `b1x_setle` (layerB/pss_wip.thy:50305):
    `M ⊴ N ⟺ ∀ x∈M. ∃ y∈N. x ≤_BT y`。 -/
def b1x_setle (M N : Set BT) : Prop :=
  ∀ x ∈ M, ∃ y ∈ N, leBT x y = true

/-- Isabelle `b1x_setle_subset` (wip:50308)。 -/
theorem b1x_setle_subset {M N : Set BT} (h : M ⊆ N) : b1x_setle M N := by
  intro x hx
  exact ⟨x, h hx, by simp [leBT]⟩

/-- Isabelle `b1x_setle_widen` (wip:50311)。 -/
theorem b1x_setle_widen {M N N' : Set BT} (h : b1x_setle M N) (hsub : N ⊆ N') :
    b1x_setle M N' := by
  intro x hx
  obtain ⟨y, hy, hle⟩ := h x hx
  exact ⟨y, hsub hy, hle⟩

/-- Isabelle `b1x_setle_union` (wip:50314)。 -/
theorem b1x_setle_union {M1 M2 N : Set BT}
    (h1 : b1x_setle M1 N) (h2 : b1x_setle M2 N) :
    b1x_setle (M1 ∪ M2) N := by
  intro x hx
  rcases hx with hx | hx
  · exact h1 x hx
  · exact h2 x hx

/-! ## [Buc1] `b ◁_z a` の G-control 連言: `b1x_triG` -/

/-- Isabelle `b1x_triG` (layerB/pss_wip.thy:50325):
    `b1x_triG z b a ⟺ ∀ u c. b ≤ c ≤ a → G_u b ⊴ (G_u c ∪ G_u z ∪ {0})`。
    （`G^0_u z = G_u z ∪ {0}`、`{0} = {BZero}`。） -/
def b1x_triG (z b a : BT) : Prop :=
  ∀ (u : ℕ∞) (c : BT), leBT b c = true → leBT c a = true →
    b1x_setle (GBT u b) (GBT u c ∪ GBT u z ∪ {BZero})

/-- Isabelle `b1x_triG_I` (wip:50331)。 -/
theorem b1x_triG_I {z b a : BT}
    (h : ∀ (u : ℕ∞) (c : BT), leBT b c = true → leBT c a = true →
      b1x_setle (GBT u b) (GBT u c ∪ GBT u z ∪ {BZero})) :
    b1x_triG z b a := h

/-- Isabelle `b1x_triG_D` (wip:50336)。 -/
theorem b1x_triG_D {z b a c : BT} {u : ℕ∞}
    (h : b1x_triG z b a) (hbc : leBT b c = true) (hca : leBT c a = true) :
    b1x_setle (GBT u b) (GBT u c ∪ GBT u z ∪ {BZero}) :=
  h u c hbc hca

#print axioms d4vx_ins_flat
#print axioms b1x_setle_subset
#print axioms b1x_setle_widen
#print axioms b1x_setle_union
#print axioms b1x_triG_I
#print axioms b1x_triG_D

end PSS
