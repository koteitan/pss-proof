import «8».«8.7-otint-transport-data»
import «8».«8.7-OT-scb-recursive»

/-!
# §8.7 `OTintIIIIV_otSetleResidual` の OTA1 G-条件を放電（`isOT_BT (ins A0)`+setle への縮小）

- 原文: `tmp/content.md` §8.7（Trans が OT を保つことの内点ケースの surgery 残差）。
- Isabelle:
  * ③ `OTA1_ltJ` = `isOT_BP (D_{e₃} (ins A₀))` は `ot1_OTA1_from_A0OT`
    (`isabelle/layerC/pss_scratch.thy`:4314) が `A0OT = isOT_BT (bpHeadT ..)` ＋ `tri0`
    へ還元。`tri0` は Buchholz Lemma 3.4 の G-統制（`b1x_G_control`）で運ぶ。
  * ④ `SETLE1_ltJ` = `∀ u, b1x_setle (G_u (ins A₀)) (insert (ins 0_B) (G_u (ins 0_B)))`
    は `ox10_SETLE1_ltJ` (`pss_scratch.thy`:10995、ox5–ox10 の spine-descent 機械)。
  * A0OT 自体の無条件放電は `ot1_A0OT` (`pss_scratch.thy`:4762、§6 Red/slice ＋ §7 Trans
    ＋ `m_8_7_OT_scb_recursive`)。
- 本ファイルの成果（**縮小 = narrowing**）:
  * 残差 `OTintIIIIV_otSetleResidual`（③④）を、より原子的な残差
    `OTintIIIIV_otSetleCore`（`isOT_BT (ins A₀)` ＋ ④setle）へ縮小する。
    すなわち ③の **主項 G-条件** `∀ x ∈ G_{e₃} (ins A₀), x < ins A₀`
    （= Isabelle `ot1_OTA1_reduce` に相当）を無条件に放電する。
  * 放電の道具立て:
    - 供与項の読み出し `loP`/`hiP`（`isOT_BP (D_{e₃} (ins 0_B))` /
      `isOT_BP (D_{e₃} (ins³ 0_B))`）を `buchholz_fseq_closed` ＋ `OT_scb_recursive`
      ＋ fseq 閉形式（`scb_fseq_kind1`）から再構成（`8.7-otdisp-OTint-condIIIIV`
      の `fO`/`donOT` パターン）。
    - `setle → b1x_triG`（`setle_triG_os`、Isabelle `otx3_setle_triG`）。
    - `b1x_triG` ＝ `triGBC` の defeq を経て `G_control_bc`（[Buc1] Lemma 3.4）で
      中間項 G-条件へ持ち上げ（Isabelle `otx3_pOT` の G-統制部）。
  * `otSetle_holds : OTintIIIIV_otSetleCore → OTintIIIIV_otSetleResidual`。
- 依存（ビルド済みのみ import）:
  * `8.7-otint-transport-data`（`OTintIIIIV_otSetleResidual` の def 元。透過的に
    `b1x_setle`・`b1x_triG`・`GBT`・`buchholz_fseq_closed`・`G_control_bc`/`triGBC`・
    `scb_fseq_kind1`・`coreTower_e34`・`Dprin`・`isOT_BP`・`flatBT`・`scbext_lessBT`・
    `lessBT_linear_trans` 等）。
  * `8.7-OT-scb-recursive`（`OT_scb_recursive`）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  残る原子残差 = `OTintIIIIV_otSetleCore`（`isOT_BT (ins A₀)`＝Isa `ot1_A0OT`/`nub`
  由来、setle＝Isa `ox10_SETLE1_ltJ`）。私的接尾辞 `_os`。
-/

namespace PSS

/-! ## 1. flat-dfree 特徴づけ（`8.7-otint-transport-data` の private twin を再掲） -/

private def symFin_os : Sym → Bool
  | .dsym v => v != (⊤ : ℕ∞)
  | _ => true

private def flatFin_os (l : List Sym) : Bool := l.all symFin_os

private theorem flatFin_append_os (a b : List Sym) :
    flatFin_os (a ++ b) = (flatFin_os a && flatFin_os b) := by
  simp only [flatFin_os, List.all_append]

private theorem flatFin_cons_os (x : Sym) (l : List Sym) :
    flatFin_os (x :: l) = (symFin_os x && flatFin_os l) := by
  simp only [flatFin_os, List.all_cons]

mutual
  private theorem dfree_flat_BT_os : ∀ t : BT, dfree_BT t = flatFin_os (flatBT t)
    | .trm [] => by rfl
    | .trm [p] => by
        show (dfree_BP p && dfree_BPList []) = flatFin_os (flatBP p)
        rw [dfree_flat_BP_os p]; simp [dfree_BPList]
    | .trm (p :: q :: ps) => by
        show (dfree_BP p && dfree_BPList (q :: ps))
            = flatFin_os (Sym.lp :: (flatBP p ++ flatBPTail (q :: ps)) ++ [Sym.rp])
        rw [flatFin_append_os, flatFin_cons_os, flatFin_append_os,
          dfree_flat_BP_os p, dfree_flat_BPTail_os (q :: ps)]
        simp [symFin_os, flatFin_os]
  private theorem dfree_flat_BP_os : ∀ p : BP, dfree_BP p = flatFin_os (flatBP p)
    | .db u a => by
        show ((u != (⊤ : ℕ∞)) && dfree_BT a) = flatFin_os (Sym.dsym u :: flatBT a)
        rw [flatFin_cons_os, dfree_flat_BT_os a]; rfl
  private theorem dfree_flat_BPTail_os : ∀ ps : List BP, dfree_BPList ps = flatFin_os (flatBPTail ps)
    | [] => by rfl
    | p :: ps => by
        show (dfree_BP p && dfree_BPList ps) = flatFin_os (Sym.cm :: flatBP p ++ flatBPTail ps)
        rw [flatFin_append_os, flatFin_cons_os, dfree_flat_BP_os p, dfree_flat_BPTail_os ps]
        simp [symFin_os]
end

private theorem mem_T_B_iff_flatFin_os (t : BT) : t ∈ T_B ↔ flatFin_os (flatBT t) = true := by
  show dfree_BT t = true ↔ flatFin_os (flatBT t) = true
  rw [dfree_flat_BT_os t]

/-- `flatFin_os (s ++ Dsym v :: mid ++ b)` から中身 `mid` の fin。 -/
private theorem flatFin_ins_mid_os {s mid b : List Sym} {v : ℕ∞}
    (h : flatFin_os (s ++ Sym.dsym v :: mid ++ b) = true) : flatFin_os mid = true := by
  rw [flatFin_append_os, flatFin_append_os, flatFin_cons_os] at h
  have h1 := ((Bool.and_eq_true _ _).mp h).1
  have h2 := ((Bool.and_eq_true _ _).mp h1).2
  exact ((Bool.and_eq_true _ _).mp h2).2

/-! ## 2. 順序・`G` 補助（`8.7-otint-transport` の private twin を再掲） -/

private theorem leBT_iff_os (a b : BT) :
    leBT a b = true ↔ (lessBT a b = true ∨ a = b) := by
  simp only [leBT, Bool.or_eq_true, beq_iff_eq]

private theorem leBT_of_lessBT_os {a b : BT} (h : lessBT a b = true) : leBT a b = true := by
  simp [leBT, h]

private theorem less_le_trans_os {a b c : BT}
    (hab : lessBT a b = true) (hbc : leBT b c = true) : lessBT a c = true := by
  rw [leBT_iff_os] at hbc
  rcases hbc with h | h
  · exact lessBT_linear_trans a b c hab h
  · subst h; exact hab

private theorem lessBT_zero_Dprin_os (v : ℕ∞) (a : BT) :
    lessBT BZero (Dprin v a) = true := by
  simp [BZero, Dprin, lessBT, lessBPList]

/-- OT principal `D_w b` からその `G_w` 集合は `b` で strict 下界される。 -/
private theorem GBT_lessBT_of_isOT_BP_os {w : ℕ∞} {b : BT}
    (h : isOT_BP (BP.db w b) = true) : ∀ x ∈ GBT w b, lessBT x b = true := by
  intro x hx
  simp only [isOT_BP, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 x (by simpa [GBT, List.contains_iff_mem] using hx)

/-- `G_u (D_∞ x) = {x} ∪ G_u x`。 -/
private theorem GBT_Dprin_inf_os (u : ℕ∞) (x : BT) :
    GBT u (Dprin (⊤ : ℕ∞) x) = insert x (GBT u x) := by
  ext y
  simp only [GBT, Dprin, gatherBT, gatherBPList, gatherBP, le_top,
    decide_true, if_true, List.append_nil, List.contains_cons, Set.mem_setOf_eq,
    Set.mem_insert_iff, Bool.or_eq_true, beq_iff_eq]

/-- Isabelle `otx3_setle_triG` (layerB/pss_wip.thy:116705)。`setle` 前提は
`a' ◁_{D_∞(aLo)} aHi` に等価。 -/
private theorem setle_triG_os {aLo a' aHi : BT}
    (setle : ∀ u : ℕ∞, b1x_setle (GBT u a') (insert aLo (GBT u aLo))) :
    b1x_triG (Dprin (⊤ : ℕ∞) aLo) a' aHi := by
  apply b1x_triG_I
  intro u c _ _
  have hbase : b1x_setle (GBT u a') (GBT u (Dprin (⊤ : ℕ∞) aLo)) := by
    rw [GBT_Dprin_inf_os]; exact setle u
  refine b1x_setle_widen hbase ?_
  intro z hz
  exact Or.inl (Or.inr hz)

/-! ## 3. fseq 供与項の再構成（`8.7-otdisp-OTint-condIIIIV` の private twin を再掲） -/

private theorem coe_ne_top_os (n : ℕ) : ((n : ℕ) : ℕ∞) ≠ ⊤ := by simp

/-- Isabelle producer `ins_mono_ep` の再掲。 -/
private theorem ins_mono_os {ins : BT → BT} {ub : ℕ∞} {s0 b0 : List Sym}
    (hflat : ∀ X, flatBT (ins X) = s0 ++ Sym.dsym ub :: flatBT X ++ b0)
    (hb0 : ∀ x ∈ b0, x = Sym.rp) {X Y : BT} (h : lessBT X Y = true) :
    lessBT (ins X) (ins Y) = true := by
  refine scbext_lessBT (s := s0) (b := b0) (cp := .db ub X) (cp' := .db ub Y) ?_ ?_ hb0 ?_
  · rw [hflat X]; rfl
  · rw [hflat Y]; rfl
  · simp [lessBP, h]

private theorem flatten_replicate_snoc_os {α : Type} (xs : List α) (n : ℕ) :
    List.flatten (List.replicate (n + 1) xs) =
      List.flatten (List.replicate n xs) ++ xs := by
  rw [List.replicate_add, List.flatten_append]; simp

/-- Isabelle `d4vx_core_flat`（任意底 `C`）。 -/
private theorem coreTower_flat_os {ins : BT → BT} {ub : ℕ∞} {s0 b0 : List Sym}
    (hflat : ∀ X, flatBT (ins X) = s0 ++ Sym.dsym ub :: flatBT X ++ b0) :
    ∀ (C : BT) (j : ℕ), flatBT (coreTower_e34 ins C j)
      = List.flatten (List.replicate j (s0 ++ [Sym.dsym ub])) ++ flatBT C
        ++ List.flatten (List.replicate j b0)
  | C, 0 => by simp [coreTower_e34]
  | C, j + 1 => by
      show flatBT (ins (coreTower_e34 ins C j)) = _
      rw [hflat (coreTower_e34 ins C j), coreTower_flat_os hflat C j,
        flatten_replicate_snoc_os b0 j, List.replicate_succ, List.flatten_cons]
      simp [List.append_assoc]

/-- `flatBT t = s ++ flatBP (D_h C) ++ b`（`b` 全 `RP`, `h ≠ ⊤`, `C` は `D_ω`-free）
から scb 分解を組む。 -/
private theorem scb_of_flat_os {t C : BT} {s b : List Sym} {h : ℕ∞}
    (hf : flatBT t = s ++ flatBP (BP.db h C) ++ b)
    (hdf : dfree_BT C = true) (hnt : h ≠ ⊤)
    (hb : ∀ x ∈ b, x = Sym.rp) :
    scb_decomp t s (flatBT (Dprin h C)) b := by
  refine ⟨?_, ?_, hb⟩
  · rw [hf]; rfl
  · intro _
    refine ⟨BP.db h C, ?_, rfl⟩
    simp only [dfree_BP, Bool.and_eq_true, bne_iff_ne]
    exact ⟨hnt, hdf⟩

/-- `Dprin w x ∈ OT` から `isOT_BP (D_w x)`。 -/
private theorem isOT_BP_of_Dprin_OT_os {w : ℕ∞} {x : BT} (h : Dprin w x ∈ OT) :
    isOT_BP (BP.db w x) = true := by
  have h' : isOT_BT (Dprin w x) = true := h
  simpa [Dprin, isOT_BT, isOT_BPList, descP] using h'

/-! ## 4. 縮小残差 `OTintIIIIV_otSetleCore`（`isOT_BT (ins A₀)` ＋ ④setle） -/

/-- `OTintIIIIV_otSetleResidual` から ③の主項 G-条件を落とした原子残差。前提は同一。
③ `isOT_BP (D_{e₃} (ins A₀))` の代わりに、その `isOT_BT` 部
`isOT_BT (ins A₀)`（Isabelle `nub`/`ot1_A0OT` 由来）と ④setle（Isabelle
`ox10_SETLE1_ltJ`）だけを主張する。 -/
def OTintIIIIV_otSetleCore : Prop :=
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
    isOT_BT (ins A0) = true ∧
    (∀ u : ℕ∞, b1x_setle (GBT u (ins A0)) (insert (ins BZero) (GBT u (ins BZero))))

/-! ## 5. 縮小: `OTintIIIIV_otSetleCore → OTintIIIIV_otSetleResidual` -/

/-- **縮小**: 原子残差 `OTintIIIIV_otSetleCore`（`isOT_BT (ins A₀)`＋setle）から
`OTintIIIIV_otSetleResidual`（③`isOT_BP (D_{e₃} (ins A₀))`＋④setle）を復元する。
③の主項 G-条件を、供与項読み出し ＋ `G_control_bc`（[Buc1] Lemma 3.4）で放電。 -/
theorem otSetle_holds (hcore : OTintIIIIV_otSetleCore) : OTintIIIIV_otSetleResidual := by
  intro M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono j1gt hcond hp hOT
    hflat hb0 hb1 hinner hk1 hmn base0 base1'
  obtain ⟨hinsA0OT, hsetle⟩ :=
    hcore M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono j1gt hcond hp hOT
      hflat hb0 hb1 hinner hk1 hmn base0 base1'
  refine ⟨?_, hsetle⟩
  -- === 供与項 fseq の再構成（`fO`/`donOT` パターン）===
  have hTB : Trans M ∈ T_B := hOT.2
  have hbf : flatBT (Dprin (e3 : ℕ∞) body) = Sym.dsym (e3 : ℕ∞) :: flatBT body := rfl
  have hne : Trans M ≠ BZero := by
    intro hz
    have hlen := congrArg List.length hk1.1.1
    rw [hz, hbf, hinner.1] at hlen
    simp only [BZero, flatBT, flatBP, Dprin, List.length_cons, List.length_append,
      List.length_nil] at hlen
    omega
  have hinner' : scb_decomp (Dprin (e3 : ℕ∞) body) (Sym.dsym (e3 : ℕ∞) :: s0)
      (flatBT (Dprin (v1 : ℕ∞) BZero)) b0 := by
    refine ⟨?_, ?_, hinner.2.2⟩
    · rw [hbf, hinner.1]; simp
    · intro _
      exact ⟨.db (v1 : ℕ∞) BZero, by simp [dfree_BP, BZero, dfree_BT, dfree_BPList], rfl⟩
  have fO : ∀ k, flatBT (operB (Trans M) (numBT k))
      = s1 ++ flatBP (BP.db (e3 : ℕ∞) (coreTower_e34 ins BZero (k + 1))) ++ b1 := by
    intro k
    have hfseq := (scb_fseq_kind1 (n := k) hTB hk1 hinner').2
    rw [hfseq]
    simp only [flatBP]
    rw [coreTower_flat_os hflat BZero (k + 1)]
    simp [BZero, flatBT, List.append_assoc]
  -- === 供与項 (k = 0, 2) の OT と flat ===
  have hdon0 : operB (Trans M) (numBT 0) ∈ OT_B := buchholz_fseq_closed (Trans M) 0 hOT hne
  have hdon2 : operB (Trans M) (numBT 2) ∈ OT_B := buchholz_fseq_closed (Trans M) 2 hOT hne
  have loflat : flatBT (operB (Trans M) (numBT 0))
      = s1 ++ flatBP (BP.db (e3 : ℕ∞) (ins BZero)) ++ b1 := by
    have h := fO 0
    rwa [(rfl : coreTower_e34 ins BZero (0 + 1) = ins BZero)] at h
  have hiflat : flatBT (operB (Trans M) (numBT 2))
      = s1 ++ flatBP (BP.db (e3 : ℕ∞) (ins (ins (ins BZero)))) ++ b1 := by
    have h := fO 2
    rwa [(rfl : coreTower_e34 ins BZero (2 + 1) = ins (ins (ins BZero)))] at h
  -- === 供与項の body の dfree（flat-fin で外周供与項から抽出）===
  have hY1df : ins BZero ∈ T_B := by
    have hfin : flatFin_os (flatBT (operB (Trans M) (numBT 0))) = true :=
      (mem_T_B_iff_flatFin_os _).mp hdon0.2
    rw [loflat, show flatBP (BP.db (e3 : ℕ∞) (ins BZero))
        = Sym.dsym (e3 : ℕ∞) :: flatBT (ins BZero) from rfl] at hfin
    exact (mem_T_B_iff_flatFin_os _).mpr (flatFin_ins_mid_os hfin)
  have hY3df : ins (ins (ins BZero)) ∈ T_B := by
    have hfin : flatFin_os (flatBT (operB (Trans M) (numBT 2))) = true :=
      (mem_T_B_iff_flatFin_os _).mp hdon2.2
    rw [hiflat, show flatBP (BP.db (e3 : ℕ∞) (ins (ins (ins BZero))))
        = Sym.dsym (e3 : ℕ∞) :: flatBT (ins (ins (ins BZero))) from rfl] at hfin
    exact (mem_T_B_iff_flatFin_os _).mpr (flatFin_ins_mid_os hfin)
  have hY1TB : Dprin (e3 : ℕ∞) (ins BZero) ∈ T_B := by
    show dfree_BT (Dprin (e3 : ℕ∞) (ins BZero)) = true
    have hh : dfree_BT (ins BZero) = true := hY1df
    simp [Dprin, dfree_BT, dfree_BPList, dfree_BP, hh]
  have hY3TB : Dprin (e3 : ℕ∞) (ins (ins (ins BZero))) ∈ T_B := by
    show dfree_BT (Dprin (e3 : ℕ∞) (ins (ins (ins BZero)))) = true
    have hh : dfree_BT (ins (ins (ins BZero))) = true := hY3df
    simp [Dprin, dfree_BT, dfree_BPList, dfree_BP, hh]
  -- === 供与項主項の読み出し loP / hiP ===
  have lodec : scb_decomp (operB (Trans M) (numBT 0)) s1
      (flatBT (Dprin (e3 : ℕ∞) (ins BZero))) b1 :=
    scb_of_flat_os loflat hY1df (coe_ne_top_os e3) hb1
  have hidec : scb_decomp (operB (Trans M) (numBT 2)) s1
      (flatBT (Dprin (e3 : ℕ∞) (ins (ins (ins BZero))))) b1 :=
    scb_of_flat_os hiflat hY3df (coe_ne_top_os e3) hb1
  have loOT : Dprin (e3 : ℕ∞) (ins BZero) ∈ OT :=
    OT_scb_recursive _ _ s1 b1 hdon0 hY1TB lodec
  have hiOT : Dprin (e3 : ℕ∞) (ins (ins (ins BZero))) ∈ OT :=
    OT_scb_recursive _ _ s1 b1 hdon2 hY3TB hidec
  have loP : isOT_BP (BP.db (e3 : ℕ∞) (ins BZero)) = true := isOT_BP_of_Dprin_OT_os loOT
  have hiP : isOT_BP (BP.db (e3 : ℕ∞) (ins (ins (ins BZero)))) = true :=
    isOT_BP_of_Dprin_OT_os hiOT
  -- === 順序 ===
  have zA0 : lessBT BZero A0 = true :=
    lessBT_linear_trans _ _ _ (lessBT_zero_Dprin_os _ BZero) base0
  have ordlo_strict : lessBT (ins BZero) (ins A0) = true := ins_mono_os hflat hb0 zA0
  have zltY1 : lessBT BZero (ins BZero) = true :=
    lessBT_linear_trans _ _ _ zA0 base1'
  have Y1ltY2 : lessBT (ins BZero) (ins (ins BZero)) = true := ins_mono_os hflat hb0 zltY1
  have A0ltY2 : lessBT A0 (ins (ins BZero)) = true :=
    lessBT_linear_trans _ _ _ base1' Y1ltY2
  have ordhi : leBT (ins A0) (ins (ins (ins BZero))) = true :=
    leBT_of_lessBT_os (ins_mono_os hflat hb0 A0ltY2)
  -- === setle → b1x_triG → triGBC ===
  have tri : triGBC (Dprin (⊤ : ℕ∞) (ins BZero)) (ins A0) (ins (ins (ins BZero))) :=
    setle_triG_os hsetle
  -- === G-統制で中間項 G-条件を放電（Isabelle `otx3_pOT`）===
  have hGa : ∀ x ∈ GBT (e3 : ℕ∞) (ins (ins (ins BZero))),
      lessBT x (ins (ins (ins BZero))) = true := GBT_lessBT_of_isOT_BP_os hiP
  have hGz : ∀ x ∈ GBT (e3 : ℕ∞) (Dprin (⊤ : ℕ∞) (ins BZero)),
      lessBT x (ins A0) = true := by
    intro x hx
    rw [GBT_Dprin_inf_os, Set.mem_insert_iff] at hx
    rcases hx with hx | hx
    · subst hx; exact ordlo_strict
    · exact less_le_trans_os (GBT_lessBT_of_isOT_BP_os loP x hx)
        (leBT_of_lessBT_os ordlo_strict)
  have Gcond : ∀ x ∈ GBT (e3 : ℕ∞) (ins A0), lessBT x (ins A0) = true :=
    G_control_bc tri ordhi hGa hGz
  -- === ③ `isOT_BP (D_{e₃} (ins A₀))` を組み立て ===
  simp only [isOT_BP, Bool.and_eq_true, List.all_eq_true]
  refine ⟨hinsA0OT, ?_⟩
  intro x hx
  exact Gcond x (by simpa [GBT, List.contains_iff_mem] using hx)

#print axioms otSetle_holds

end PSS
