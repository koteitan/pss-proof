import «8».«8.7-otdisp-OTint-condIIIIV»

/-!
# §8.7 `OTintIIIIV_transportData` の縮小（`OTA1`/`SETLE1` 残差への絞り込み）

- 原文: `tmp/content.md` §8.7（Trans が OT を保つことの内点ケースの surgery データ）。
- Isabelle:
  * `OTintIIIIV_transportData`（`8.7-otdisp-OTint-condIIIIV`:47）は `oi5_IIIIV_pkg`
    (`isabelle/layerC/pss_scratch.thy`:1213) の出力 4 事実
    ①`A0 ∈ T_B` ②`ins` の `T_B` 保存 ③`OTA1_ltJ` の結論
    `isOT_BP (D_{e₃} (ins A₀))` ④`SETLE1_ltJ` の結論
    `b1x_setle (G_u (ins A₀)) (insert (ins 0_B) (G_u (ins 0_B)))` を束ねる。
  * ③=Isabelle `ot1_OTA1_from_A0OT` (`pss_scratch.thy`:4314) が閉じた census 残差
    `OTA1_ltJ`（`oi7_termination_census`:2650 の第1仮定）。
  * ④=Isabelle `ox10_SETLE1_ltJ` (`pss_scratch.thy`:10995) が閉じた census 残差
    `SETLE1_ltJ`（`oi7_termination_census`:2659 の第2仮定）。
  * ①②=Isabelle では `oi5_IIIIV_pkg` から構造的に出る（`oi5_d4vx_ins_TB`,
    `A0TB`）。Lean の `Exch84_condIIIIV_slicepkg` (`8.4-exch84-producer`:128) は
    `A0 ∈ T_B` を落としている（producer 側未使用のため）。
- 本ファイルの成果（**縮小 = narrowing**）:
  * `OTintIIIIV_transportData` の 4 連言のうち ①`A0 ∈ T_B` と ②`ins` の `T_B` 保存
    を **無条件に放電**する。鍵は flat-dfree 特徴づけ `dfree_flat_BT_td`
    （`dfree_BT t ⟺ flatBT t が Dsym ⊤ を含まない`、Isabelle `dfree_flat_BT` 相当）:
    - ②：`body ∈ T_B`（`hk1` の principal 節から）＋ `hflat` から、挿入は
      Dsym を `Dsym (v₁-1)`（有限）しか増やさないので `T_B` を保つ。
    - ①：`hmn m=2` により `flatBT (Trans (M[2])) = s₁ @ D_{e₃}(ins A₀) @ b₁`、かつ
      `Trans (M[2]) ∈ T_B`（`STPS` 閉性）なので、その部分文字列 `flatBT A₀` も
      Dsym ⊤ を含まず、`A₀ ∈ T_B`。
  * 残差は ③`OTA1_ltJ` ＋ ④`SETLE1_ltJ` の 2 本だけ（`OTintIIIIV_otSetleResidual`）。
    これらは OT 性 / G-統制の surgery 事実であり、抽象 `ins`/`A0` からは導けない
    （Isabelle 側は `ot1_OTA1_from_A0OT` / `ox10_SETLE1_ltJ` で閉じている）。
  * `otIIIIVdata_of_otSetle : OTintIIIIV_otSetleResidual → OTintIIIIV_transportData`。
- 依存（ビルド済みのみ import）:
  `8.7-otdisp-OTint-condIIIIV`（`OTintIIIIV_transportData` の def 元、透過的に
  `Exch84_condIIIIV_slicepkg`・`coreTower_e34`・`b1x_setle`・`GBT`・`Trans_mem_T_B`・
  `STPS_RTPS`・`STPS.oper`・`flatBP_injective`・`dfree_BT`/`flatBT` 等）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  残差 = `OTintIIIIV_otSetleResidual`（③④）。私的接尾辞 `_td`。
-/

namespace PSS

/-! ## 1. flat-dfree 特徴づけ（Isabelle `dfree_flat_BT` の構造版） -/

/-- 1 記号が「`Dsym ⊤` でない」ことの判定。 -/
def symFin_td : Sym → Bool
  | .dsym v => v != (⊤ : ℕ∞)
  | _ => true

/-- flat 文字列が `Dsym ⊤` を一切含まないことの判定。 -/
def flatFin_td (l : List Sym) : Bool := l.all symFin_td

private theorem flatFin_td_append (a b : List Sym) :
    flatFin_td (a ++ b) = (flatFin_td a && flatFin_td b) := by
  simp only [flatFin_td, List.all_append]

private theorem flatFin_td_cons (x : Sym) (l : List Sym) :
    flatFin_td (x :: l) = (symFin_td x && flatFin_td l) := by
  simp only [flatFin_td, List.all_cons]

private theorem symFin_dsym_coe_td (n : ℕ) : symFin_td (Sym.dsym ((n : ℕ) : ℕ∞)) = true := by
  simp [symFin_td]

/-! `dfree_BT t` は flat 文字列の「`Dsym ⊤` を含まない」性と一致（Isabelle `dfree_flat_BT`）。 -/
mutual
  private theorem dfree_flat_BT_td : ∀ t : BT, dfree_BT t = flatFin_td (flatBT t)
    | .trm [] => by rfl
    | .trm [p] => by
        show (dfree_BP p && dfree_BPList []) = flatFin_td (flatBP p)
        rw [dfree_flat_BP_td p]; simp [dfree_BPList]
    | .trm (p :: q :: ps) => by
        show (dfree_BP p && dfree_BPList (q :: ps))
            = flatFin_td (Sym.lp :: (flatBP p ++ flatBPTail (q :: ps)) ++ [Sym.rp])
        rw [flatFin_td_append, flatFin_td_cons, flatFin_td_append,
          dfree_flat_BP_td p, dfree_flat_BPTail_td (q :: ps)]
        simp [symFin_td, flatFin_td]
  private theorem dfree_flat_BP_td : ∀ p : BP, dfree_BP p = flatFin_td (flatBP p)
    | .db u a => by
        show ((u != (⊤ : ℕ∞)) && dfree_BT a) = flatFin_td (Sym.dsym u :: flatBT a)
        rw [flatFin_td_cons, dfree_flat_BT_td a]; rfl
  private theorem dfree_flat_BPTail_td : ∀ ps : List BP, dfree_BPList ps = flatFin_td (flatBPTail ps)
    | [] => by rfl
    | p :: ps => by
        show (dfree_BP p && dfree_BPList ps) = flatFin_td (Sym.cm :: flatBP p ++ flatBPTail ps)
        rw [flatFin_td_append, flatFin_td_cons, dfree_flat_BP_td p, dfree_flat_BPTail_td ps]
        simp [symFin_td]
end

/-- `t ∈ T_B` ⟺ `flatBT t` に `Dsym ⊤` 無し。 -/
private theorem mem_T_B_iff_flatFin_td (t : BT) : t ∈ T_B ↔ flatFin_td (flatBT t) = true := by
  show dfree_BT t = true ↔ flatFin_td (flatBT t) = true
  rw [dfree_flat_BT_td t]

/-! ### flat-fin の分解補助 -/

/-- `flatFin_td (s ++ c ++ b)` から左端 `s` の fin。 -/
private theorem flatFin_left_td {s c b : List Sym}
    (h : flatFin_td (s ++ c ++ b) = true) : flatFin_td s = true := by
  rw [flatFin_td_append, flatFin_td_append] at h
  exact ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp h).1).1

/-- `flatFin_td (s ++ c ++ b)` から右端 `b` の fin。 -/
private theorem flatFin_right_td {s c b : List Sym}
    (h : flatFin_td (s ++ c ++ b) = true) : flatFin_td b = true := by
  rw [flatFin_td_append, flatFin_td_append] at h
  exact ((Bool.and_eq_true _ _).mp h).2

/-- `flatFin_td (flatBP (D_v a))` から body `a` の fin。 -/
private theorem flatFin_dprin_body_td {v : ℕ∞} {a : BT}
    (h : flatFin_td (flatBP (BP.db v a)) = true) : flatFin_td (flatBT a) = true := by
  rw [show flatBP (BP.db v a) = Sym.dsym v :: flatBT a from rfl, flatFin_td_cons] at h
  exact ((Bool.and_eq_true _ _).mp h).2

/-- `flatFin_td (s ++ Dsym v :: mid ++ b)` から中身 `mid` の fin。 -/
private theorem flatFin_ins_mid_td {s mid b : List Sym} {v : ℕ∞}
    (h : flatFin_td (s ++ Sym.dsym v :: mid ++ b) = true) : flatFin_td mid = true := by
  rw [flatFin_td_append, flatFin_td_append, flatFin_td_cons] at h
  have h1 := ((Bool.and_eq_true _ _).mp h).1
  have h2 := ((Bool.and_eq_true _ _).mp h1).2
  exact ((Bool.and_eq_true _ _).mp h2).2

/-! ## 2. 残差 `Prop`（③`OTA1_ltJ` ＋ ④`SETLE1_ltJ`） -/

/-- `OTintIIIIV_transportData` の残差成分。`OTintIIIIV_transportData` と同一の前提の下で、
Isabelle の閉じた census 残差 ③`OTA1_ltJ`（`isOT_BP (D_{e₃} (ins A₀))`）と
④`SETLE1_ltJ`（`ins A₀` vs `ins 0_B` の `b1x_setle` G-統制）だけを主張する。
①`A0 ∈ T_B` と ②`ins` の `T_B` 保存は本ファイルで放電済みのため落としている。 -/
def OTintIIIIV_otSetleResidual : Prop :=
  ∀ (M : PS) (ins : BT → BT) (A0 body : BT) (e3 v1 : ℕ) (s0 b0 s1 b1 : List Sym),
    STPS M → monoT M = true → 1 < Lng M - 1 →
    (transCondIII M = true ∨ transCondIV M = true) →
    hasParent M 1 (Lng M - 1) = true →
    Trans M ∈ OT_B →
    (∀ X, flatBT (ins X) = s0 ++ Sym.dsym ((v1 - 1 : ℕ) : ℕ∞) :: flatBT X ++ b0) →
    (∀ x ∈ b0, x = Sym.rp) → (∀ x ∈ b1, x = Sym.rp) →
    scb_decomp body s0 (flatBT (Dprin (v1 : ℕ∞) BZero)) b0 →
    scb_kind1 (Trans M) s1 (flatBT (Dprin (e3 : ℕ∞) body)) b1 →
    (∀ m, 1 ≤ m → flatBT (Trans (oper M m))
      = s1 ++ flatBP (BP.db (e3 : ℕ∞) (coreTower_e34 ins A0 (m - 1))) ++ b1) →
    lessBT (Dprin ((v1 - 1 : ℕ) : ℕ∞) BZero) A0 = true →
    lessBT A0 (ins BZero) = true →
    isOT_BP (BP.db (e3 : ℕ∞) (ins A0)) = true ∧
    (∀ u : ℕ∞, b1x_setle (GBT u (ins A0)) (insert (ins BZero) (GBT u (ins BZero))))

/-! ## 3. `OTintIIIIV_transportData` を残差へ縮小 -/

/-- **縮小**: 残差 `OTintIIIIV_otSetleResidual`（③④）から
`OTintIIIIV_transportData`（①②③④）を復元する。①`A0 ∈ T_B` と ②`ins` の `T_B`
保存を flat-dfree 特徴づけで放電。 -/
theorem otIIIIVdata_of_otSetle (h : OTintIIIIV_otSetleResidual) : OTintIIIIV_transportData := by
  intro M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono j1gt hcond hp hOT
    hflat hb0 hb1 hinner hk1 hmn base0 base1'
  -- === body ∈ T_B（`hk1` の principal 節から）===
  have hbf : flatBT (Dprin (e3 : ℕ∞) body) = Sym.dsym (e3 : ℕ∞) :: flatBT body := rfl
  have hne : Trans M ≠ BZero := by
    intro hz
    have hlen := congrArg List.length hk1.1.1
    rw [hz, hbf, hinner.1] at hlen
    simp only [BZero, flatBT, flatBP, Dprin, List.length_cons, List.length_append,
      List.length_nil] at hlen
    omega
  obtain ⟨p, hpdf, hpeq⟩ := hk1.1.2.1 hne
  have hpeq2 : flatBP (BP.db (e3 : ℕ∞) body) = flatBP p := hpeq
  have hp_eq : BP.db (e3 : ℕ∞) body = p := flatBP_injective hpeq2
  have hbodyTB : dfree_BT body = true := by
    have hdf : dfree_BP (BP.db (e3 : ℕ∞) body) = true := by rw [hp_eq]; exact hpdf
    simpa [dfree_BP] using hdf
  -- flatBT body の fin（body ∈ T_B より）
  have hbodyfin : flatFin_td (flatBT body) = true := by
    rw [← dfree_flat_BT_td body]; exact hbodyTB
  -- wrap（hinner の flat 等式）
  have hwrap : flatBT body = s0 ++ flatBP (BP.db (v1 : ℕ∞) BZero) ++ b0 := hinner.1
  have hs0fin : flatFin_td s0 = true := flatFin_left_td (by rw [← hwrap]; exact hbodyfin)
  have hb0fin : flatFin_td b0 = true := flatFin_right_td (by rw [← hwrap]; exact hbodyfin)
  -- === ins-closure（②）===
  have hinsTB : ∀ X, X ∈ T_B → ins X ∈ T_B := by
    intro X hX
    have hXfin : flatFin_td (flatBT X) = true := (mem_T_B_iff_flatFin_td X).mp hX
    rw [mem_T_B_iff_flatFin_td]
    rw [hflat X, flatFin_td_append, flatFin_td_append, flatFin_td_cons,
      hs0fin, hXfin, hb0fin]
    simp [symFin_td, Bool.and_true, Bool.true_and]
  -- === A0 ∈ T_B（①）: `hmn m=2` ＋ `Trans (M[2]) ∈ T_B` ===
  have hA0TB : A0 ∈ T_B := by
    have hm2 := hmn 2 (by omega)
    rw [(rfl : coreTower_e34 ins A0 (2 - 1) = ins A0)] at hm2
    have hTr2TB : Trans (oper M 2) ∈ T_B :=
      Trans_mem_T_B _ (STPS_RTPS _ (STPS.oper hST 2 (by omega)))
    have hTr2fin : flatFin_td (flatBT (Trans (oper M 2))) = true :=
      (mem_T_B_iff_flatFin_td _).mp hTr2TB
    rw [hm2] at hTr2fin
    -- 中央 principal `D_{e₃}(ins A₀)` の fin
    have hmidfin : flatFin_td (flatBP (BP.db (e3 : ℕ∞) (ins A0))) = true := by
      rw [flatFin_td_append, flatFin_td_append] at hTr2fin
      exact ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hTr2fin).1).2
    -- body `ins A₀` の fin、さらに `hflat` を剥がして `flatBT A₀` の fin
    have hinsA0fin : flatFin_td (flatBT (ins A0)) = true := flatFin_dprin_body_td hmidfin
    have hA0fin : flatFin_td (flatBT A0) = true := by
      rw [hflat A0] at hinsA0fin
      exact flatFin_ins_mid_td hinsA0fin
    exact (mem_T_B_iff_flatFin_td A0).mpr hA0fin
  -- === 残差から ③④ ===
  obtain ⟨hOTA1, hsetle⟩ := h M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono j1gt hcond hp hOT
    hflat hb0 hb1 hinner hk1 hmn base0 base1'
  exact ⟨hA0TB, hinsTB, hOTA1, hsetle⟩

#print axioms otIIIIVdata_of_otSetle

end PSS
