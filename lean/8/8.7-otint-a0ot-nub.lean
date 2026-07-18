import «8».«8.7-otint-a0ot»

/-!
# §8.7 `A0OTNub`（= census `nub = isOT_BP (D_{v₁-1} A₀)`）を単一の真の未知 `A0OT` へ縮小

- 原文: `tmp/content.md` §8.7（Trans が OT を保つことの内点ケースの surgery 残差）。
- Isabelle: `ot1_nub_from_A0OT` (`isabelle/layerC/pss_scratch.thy`:4188)。
  newOT_body brick `nub = isOT_BP (D_{ub} A₀)`（`ub = v₁-1`）を、**唯一の真の未知**
  `A0OT = isOT_BT A₀`（census では `A₀ = bpHeadT (Trans (Pred (s84x_N N)))`、
  Isabelle `ot1_A0OT` (`pss_scratch.thy`:4762)、§6 Red/slice 未移植）から組む。
  配線 = head `ub` での `otx3_pOT` に core `(X₀=0_B, A₀, X₁=ins 0_B)` を挿す:
  * `loP = isOT_BP (D_{ub} 0_B)` は無条件（`gatherBT` が空）。
  * `hiP = isOT_BP (D_{ub} (ins 0_B))` は供与項読み出し `isOT_BP (D_{e₃} (ins 0_B))`
    （`buchholz_fseq_closed` 供与項 `operB … (numBT 0)` の kind-1 core）を
    **head 反単調性**（`e₃ ≤ ub`）で持ち上げる。
  * 順序 `o1 = 0_B ≤ A₀`（base0 経由）/ `o2 = A₀ ≤ ins 0_B`（base1' 直）。
  * `tri0 = b1x_triG (D_∞ 0_B) A₀ (ins 0_B)` は census 脚 `Tri0Census`
    （`8.7-otint-a0ot`、Isabelle `oy1_tri0Y_census` 相当）。
  * per-level principal guard `otx3_pOT`（[Buc1] Lemma 3.4）。
- 本ファイルの成果（**縮小 = narrowing**）:
  * 抽象残差 `A0OTNub`（`8.7-otint-a0ot`:183）を、より鋭い 3 本の named 脚へ縮小する:
    - `A0OT_an`（= census `A0OT`、`isOT_BT A₀`。§6 Red/slice ＋ §7 Trans ＋
      `OT_scb_recursive` で閉じる**唯一の真の未知**。抽象前提束からは導けない）。
    - `NubRegimeE3_an`（regime `e₃ ≤ v₁-1`、Isabelle `oi5_regime(2)`。census では
      P 成分 entry 単調性。抽象 `e₃`/`v₁` からは導けない）。
    - `NubGControl_an`（= `otx3_pOT` の唯一の generic 残差 [Buc1] `b1x_G_control`
      Lemma 3.4、`8.7-otint-transport` の `OixGControl` と同型。Isabelle 側は証明済み）。
  * ポータブルな糊付けを無条件に閉じる（供与項 `hiP`・自明 `loP`・順序 `o1`/`o2`・
    head 反単調性・`otx3_pOT` inline）。`tri0` は既存 census 脚 `Tri0Census` を再利用。
  * `A0OTNub_of_residuals : NubGControl_an → A0OT_an → NubRegimeE3_an → Tri0Census →
    A0OTNub`。
- 依存（ビルド済みのみ import）:
  * `8.7-otint-a0ot`（`A0OTNub`・`Tri0Census` の def 元、透過的に
    `buchholz_fseq_closed`・`scb_fseq_kind1`・`coreTower_e34`・`operB`・`numBT`・
    `OT_scb_recursive`・`lessBT_linear_trans`・`b1x_triG`・`GBT`・`gatherBT`・
    `Dprin`・`isOT_BP`/`isOT_BT`・`scb_decomp`/`scb_kind1`・`Trans`・`oper` 等）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  残差 = `A0OT_an`（真の未知）/ `NubRegimeE3_an`（regime）/ `NubGControl_an`
  （Lemma 3.4）/ `Tri0Census`（再利用）。私的接尾辞 `_an`。
-/

namespace PSS

/-! ## 1. head 反単調性（`8.7-otdisp-OTint-condV` の `gather*_antitone`/
`oix_isOT_BP_head_antitone` private twin を再掲。Isabelle `b1x_GBT_antitone`） -/

mutual
  private theorem gatherBT_antitone_mem_an {u v : ℕ∞} (huv : u ≤ v)
      (x : BT) : ∀ t : BT, x ∈ gatherBT v t → x ∈ gatherBT u t
    | .trm ps, hx => gatherBPList_antitone_mem_an huv x ps hx
  private theorem gatherBP_antitone_mem_an {u v : ℕ∞} (huv : u ≤ v)
      (x : BT) : ∀ p : BP, x ∈ gatherBP v p → x ∈ gatherBP u p
    | .db w b, hx => by
        have hvw : v ≤ w := by
          by_contra hn
          simp [gatherBP, hn] at hx
        have huw : u ≤ w := huv.trans hvw
        simp only [gatherBP, hvw, huw, decide_true, if_true, List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (gatherBT_antitone_mem_an huv x b hx)
  private theorem gatherBPList_antitone_mem_an {u v : ℕ∞} (huv : u ≤ v)
      (x : BT) : ∀ ps : List BP, x ∈ gatherBPList v ps → x ∈ gatherBPList u ps
    | [], hx => by simp [gatherBPList] at hx
    | p :: ps, hx => by
        simp only [gatherBPList, List.mem_append] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl (gatherBP_antitone_mem_an huv x p hx)
        · exact Or.inr (gatherBPList_antitone_mem_an huv x ps hx)
end

/-- Isabelle `oix_isOT_BP_head_antitone`。`isOT_BP (D_u b)` の head `u` を
`u ≤ v` へ上げても OT principal のまま（`G_v b ⊆ G_u b`）。 -/
private theorem isOT_BP_head_antitone_an {u v : ℕ∞} {b : BT}
    (h : isOT_BP (BP.db u b) = true) (huv : u ≤ v) : isOT_BP (BP.db v b) = true := by
  simp only [isOT_BP, Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨h.1, ?_⟩
  intro x hx
  exact h.2 x (gatherBT_antitone_mem_an huv x b hx)

/-! ## 2. 順序・`G` 補助（`8.7-otint-setle` の private twin を再掲） -/

private theorem leBT_iff_an (a b : BT) :
    leBT a b = true ↔ (lessBT a b = true ∨ a = b) := by
  simp only [leBT, Bool.or_eq_true, beq_iff_eq]

private theorem leBT_of_lessBT_an {a b : BT} (h : lessBT a b = true) : leBT a b = true := by
  simp [leBT, h]

private theorem less_le_trans_an {a b c : BT}
    (hab : lessBT a b = true) (hbc : leBT b c = true) : lessBT a c = true := by
  rw [leBT_iff_an] at hbc
  rcases hbc with h | h
  · exact lessBT_linear_trans a b c hab h
  · subst h; exact hab

private theorem lessBT_zero_Dprin_an (v : ℕ∞) (a : BT) :
    lessBT BZero (Dprin v a) = true := by
  simp [BZero, Dprin, lessBT, lessBPList]

/-- OT principal `D_w b` の `G_w` 集合は `b` で strict 下界される。 -/
private theorem GBT_lessBT_of_isOT_BP_an {w : ℕ∞} {b : BT}
    (h : isOT_BP (BP.db w b) = true) : ∀ x ∈ GBT w b, lessBT x b = true := by
  intro x hx
  simp only [isOT_BP, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 x (by simpa [GBT, List.contains_iff_mem] using hx)

/-- `G_u (D_∞ x) = {x} ∪ G_u x`。 -/
private theorem GBT_Dprin_inf_an (u : ℕ∞) (x : BT) :
    GBT u (Dprin (⊤ : ℕ∞) x) = insert x (GBT u x) := by
  ext y
  simp only [GBT, Dprin, gatherBT, gatherBPList, gatherBP, le_top,
    decide_true, if_true, List.append_nil, List.contains_cons, Set.mem_setOf_eq,
    Set.mem_insert_iff, Bool.or_eq_true, beq_iff_eq]

/-! ## 3. per-level principal guard `otx3_pOT`（`8.7-otint-transport` `pOT_oix` inline、
唯一の generic 残差 `NubGControl_an`） -/

/-- Isabelle `b1x_G_control`（[Buc1] Lemma 3.4, `layerB/pss_wip.thy`:50342）。
`8.7-otint-transport` の `OixGControl` と同型（generic Buchholz machinery、Isabelle 済）。 -/
def NubGControl_an : Prop :=
  ∀ (z b a : BT) (u : ℕ∞), b1x_triG z b a → leBT b a = true →
    (∀ x ∈ GBT u a, lessBT x a = true) →
    (∀ x ∈ GBT u z, lessBT x b = true) →
    (∀ x ∈ GBT u b, lessBT x b = true)

/-- Isabelle `otx3_pOT` (`layerB/pss_wip.thy`:116723)。同 head の 2 OT principal に
挟まれ、LOW body `D_∞ xLo` に対し `◁`-統制された OT body `x'` は、それ自身 head `w` の
OT principal。generic 残差 `NubGControl_an` のみに依存。 -/
private theorem pOT_an (hGC : NubGControl_an)
    {w : ℕ∞} {xLo x' xHi : BT}
    (loP : isOT_BP (BP.db w xLo) = true) (hiP : isOT_BP (BP.db w xHi) = true)
    (xOT : isOT_BT x' = true)
    (o1 : leBT xLo x' = true) (o2 : leBT x' xHi = true)
    (tri : b1x_triG (Dprin (⊤ : ℕ∞) xLo) x' xHi) :
    isOT_BP (BP.db w x') = true := by
  by_cases hx' : x' = xLo
  · subst hx'; exact loP
  · have lo_lt : lessBT xLo x' = true := by
      rw [leBT_iff_an] at o1
      rcases o1 with h | h
      · exact h
      · exact absurd h.symm hx'
    have GLo : ∀ y ∈ GBT w xLo, lessBT y xLo = true := GBT_lessBT_of_isOT_BP_an loP
    have Ga : ∀ x ∈ GBT w xHi, lessBT x xHi = true := GBT_lessBT_of_isOT_BP_an hiP
    have Gz : ∀ x ∈ GBT w (Dprin (⊤ : ℕ∞) xLo), lessBT x x' = true := by
      intro x hx
      rw [GBT_Dprin_inf_an, Set.mem_insert_iff] at hx
      rcases hx with hx | hx
      · subst hx; exact lo_lt
      · exact less_le_trans_an (GLo x hx) o1
    have G : ∀ x ∈ GBT w x', lessBT x x' = true :=
      hGC (Dprin (⊤ : ℕ∞) xLo) x' xHi w tri o2 Ga Gz
    simp only [isOT_BP, Bool.and_eq_true, List.all_eq_true]
    refine ⟨xOT, ?_⟩
    intro x hx
    exact G x (by simpa [GBT, List.contains_iff_mem] using hx)

/-! ## 4. flat-dfree 特徴づけ・供与項再構成（`8.7-otint-a0ot` の private twin を再掲） -/

private def symFin_an : Sym → Bool
  | .dsym v => v != (⊤ : ℕ∞)
  | _ => true

private def flatFin_an (l : List Sym) : Bool := l.all symFin_an

private theorem flatFin_append_an (a b : List Sym) :
    flatFin_an (a ++ b) = (flatFin_an a && flatFin_an b) := by
  simp only [flatFin_an, List.all_append]

private theorem flatFin_cons_an (x : Sym) (l : List Sym) :
    flatFin_an (x :: l) = (symFin_an x && flatFin_an l) := by
  simp only [flatFin_an, List.all_cons]

mutual
  private theorem dfree_flat_BT_an : ∀ t : BT, dfree_BT t = flatFin_an (flatBT t)
    | .trm [] => by rfl
    | .trm [p] => by
        show (dfree_BP p && dfree_BPList []) = flatFin_an (flatBP p)
        rw [dfree_flat_BP_an p]; simp [dfree_BPList]
    | .trm (p :: q :: ps) => by
        show (dfree_BP p && dfree_BPList (q :: ps))
            = flatFin_an (Sym.lp :: (flatBP p ++ flatBPTail (q :: ps)) ++ [Sym.rp])
        rw [flatFin_append_an, flatFin_cons_an, flatFin_append_an,
          dfree_flat_BP_an p, dfree_flat_BPTail_an (q :: ps)]
        simp [symFin_an, flatFin_an]
  private theorem dfree_flat_BP_an : ∀ p : BP, dfree_BP p = flatFin_an (flatBP p)
    | .db u a => by
        show ((u != (⊤ : ℕ∞)) && dfree_BT a) = flatFin_an (Sym.dsym u :: flatBT a)
        rw [flatFin_cons_an, dfree_flat_BT_an a]; rfl
  private theorem dfree_flat_BPTail_an : ∀ ps : List BP, dfree_BPList ps = flatFin_an (flatBPTail ps)
    | [] => by rfl
    | p :: ps => by
        show (dfree_BP p && dfree_BPList ps) = flatFin_an (Sym.cm :: flatBP p ++ flatBPTail ps)
        rw [flatFin_append_an, flatFin_cons_an, dfree_flat_BP_an p, dfree_flat_BPTail_an ps]
        simp [symFin_an]
end

private theorem mem_T_B_iff_flatFin_an (t : BT) : t ∈ T_B ↔ flatFin_an (flatBT t) = true := by
  show dfree_BT t = true ↔ flatFin_an (flatBT t) = true
  rw [dfree_flat_BT_an t]

private theorem flatFin_ins_mid_an {s mid b : List Sym} {v : ℕ∞}
    (h : flatFin_an (s ++ Sym.dsym v :: mid ++ b) = true) : flatFin_an mid = true := by
  rw [flatFin_append_an, flatFin_append_an, flatFin_cons_an] at h
  have h1 := ((Bool.and_eq_true _ _).mp h).1
  have h2 := ((Bool.and_eq_true _ _).mp h1).2
  exact ((Bool.and_eq_true _ _).mp h2).2

private theorem coe_ne_top_an (n : ℕ) : ((n : ℕ) : ℕ∞) ≠ ⊤ := by simp

private theorem flatten_replicate_snoc_an {α : Type} (xs : List α) (n : ℕ) :
    List.flatten (List.replicate (n + 1) xs) =
      List.flatten (List.replicate n xs) ++ xs := by
  rw [List.replicate_add, List.flatten_append]; simp

private theorem coreTower_flat_an {ins : BT → BT} {ub : ℕ∞} {s0 b0 : List Sym}
    (hflat : ∀ X, flatBT (ins X) = s0 ++ Sym.dsym ub :: flatBT X ++ b0) :
    ∀ (C : BT) (j : ℕ), flatBT (coreTower_e34 ins C j)
      = List.flatten (List.replicate j (s0 ++ [Sym.dsym ub])) ++ flatBT C
        ++ List.flatten (List.replicate j b0)
  | C, 0 => by simp [coreTower_e34]
  | C, j + 1 => by
      show flatBT (ins (coreTower_e34 ins C j)) = _
      rw [hflat (coreTower_e34 ins C j), coreTower_flat_an hflat C j,
        flatten_replicate_snoc_an b0 j, List.replicate_succ, List.flatten_cons]
      simp [List.append_assoc]

private theorem scb_of_flat_an {t C : BT} {s b : List Sym} {h : ℕ∞}
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

private theorem isOT_BP_of_Dprin_OT_an {w : ℕ∞} {x : BT} (h : Dprin w x ∈ OT) :
    isOT_BP (BP.db w x) = true := by
  have h' : isOT_BT (Dprin w x) = true := h
  simpa [Dprin, isOT_BT, isOT_BPList, descP] using h'

/-! ## 5. 縮小残差 `A0OT_an`（真の未知）と `NubRegimeE3_an`（regime） -/

/-- **唯一の真の未知** `A0OT`（Isabelle `ot1_A0OT`）の抽象 census 形。前提束は
`A0OTNub`（`8.7-otint-a0ot`:183）と同一。census では
`A₀ = bpHeadT (Trans (Pred (s84x_N M)))`、閉じ方は §6 Red/slice ＋ §7 Trans
（`Trans (Pred RN) ∈ OT_B`）＋ `OT_scb_recursive`（scb-subterm peel）。 -/
def A0OT_an : Prop :=
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
    isOT_BT A0 = true

/-- regime `e₃ ≤ v₁-1`（Isabelle `oi5_regime(2)`）。census では
`e₃ = entry M 1 (s84x_jm3 M)`, `v₁-1 = entry M 1 (Lng M - 1) - 1` の P 成分 entry 単調性。
抽象 `e₃`/`v₁` は無制約なので前提束からは導けない。 -/
def NubRegimeE3_an : Prop :=
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
    e3 ≤ v1 - 1

/-! ## 6. 縮小: `A0OTNub` を `A0OT_an` ＋ regime ＋ Lemma 3.4 ＋ `Tri0Census` へ -/

/-- **縮小**（Isabelle `ot1_nub_from_A0OT`）: 抽象残差 `A0OTNub`
（`nub = isOT_BP (D_{v₁-1} A₀)`）を、唯一の真の未知 `A0OT_an`（`isOT_BT A₀`）と、
generic な `NubGControl_an`（[Buc1] Lemma 3.4）・census regime `NubRegimeE3_an`
（`e₃ ≤ v₁-1`）・既存 census 脚 `Tri0Census`（`tri0`）へ縮小する。供与項読み出しから
`hiP`、自明 `loP`、base0/base1' から順序を無条件に閉じ、head `ub` の `otx3_pOT` で組む
（Isabelle `otx3_pOT[OF loP hiP A0OT o1 o2 tri0]`）。 -/
theorem A0OTNub_of_residuals
    (hGC : NubGControl_an) (a0ot : A0OT_an) (reg : NubRegimeE3_an) (htri0 : Tri0Census) :
    A0OTNub := by
  intro M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcond hp hOT
    hflat hb0 hb1 hinner hk1 hmn base0 base1'
  -- === 唯一の真の未知 A0OT / regime / tri0 ===
  have hA0OT : isOT_BT A0 = true :=
    a0ot M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcond hp hOT
      hflat hb0 hb1 hinner hk1 hmn base0 base1'
  have hreg : e3 ≤ v1 - 1 :=
    reg M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcond hp hOT
      hflat hb0 hb1 hinner hk1 hmn base0 base1'
  have tri0 : b1x_triG (Dprin (⊤ : ℕ∞) BZero) A0 (ins BZero) :=
    htri0 M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcond hp hOT
      hflat hb0 hb1 hinner hk1 hmn base0 base1'
  -- === 供与項 fseq の再構成（`fO`/`donOT` パターン、head `e₃` の donor principal）===
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
    rw [coreTower_flat_an hflat BZero (k + 1)]
    simp [BZero, flatBT, List.append_assoc]
  -- === donor principal at head e₃: isOT_BP (D_{e₃} (ins 0_B)) ===
  have hdon0 : operB (Trans M) (numBT 0) ∈ OT_B := buchholz_fseq_closed (Trans M) 0 hOT hne
  have loflat : flatBT (operB (Trans M) (numBT 0))
      = s1 ++ flatBP (BP.db (e3 : ℕ∞) (ins BZero)) ++ b1 := by
    have h := fO 0
    rwa [(rfl : coreTower_e34 ins BZero (0 + 1) = ins BZero)] at h
  have hY1df : ins BZero ∈ T_B := by
    have hfin : flatFin_an (flatBT (operB (Trans M) (numBT 0))) = true :=
      (mem_T_B_iff_flatFin_an _).mp hdon0.2
    rw [loflat, show flatBP (BP.db (e3 : ℕ∞) (ins BZero))
        = Sym.dsym (e3 : ℕ∞) :: flatBT (ins BZero) from rfl] at hfin
    exact (mem_T_B_iff_flatFin_an _).mpr (flatFin_ins_mid_an hfin)
  have hY1TB : Dprin (e3 : ℕ∞) (ins BZero) ∈ T_B := by
    show dfree_BT (Dprin (e3 : ℕ∞) (ins BZero)) = true
    have hh : dfree_BT (ins BZero) = true := hY1df
    simp [Dprin, dfree_BT, dfree_BPList, dfree_BP, hh]
  have lodec : scb_decomp (operB (Trans M) (numBT 0)) s1
      (flatBT (Dprin (e3 : ℕ∞) (ins BZero))) b1 :=
    scb_of_flat_an loflat hY1df (coe_ne_top_an e3) hb1
  have loOT : Dprin (e3 : ℕ∞) (ins BZero) ∈ OT :=
    OT_scb_recursive _ _ s1 b1 hdon0 hY1TB lodec
  have loP_e3 : isOT_BP (BP.db (e3 : ℕ∞) (ins BZero)) = true := isOT_BP_of_Dprin_OT_an loOT
  -- === hiP at head ub = v₁-1 by head 反単調性 (e₃ ≤ v₁-1) ===
  have hiP : isOT_BP (BP.db ((v1 - 1 : ℕ) : ℕ∞) (ins BZero)) = true :=
    isOT_BP_head_antitone_an loP_e3 (by exact_mod_cast hreg)
  -- === loP at head ub free（`gatherBT` が空）===
  have loP : isOT_BP (BP.db ((v1 - 1 : ℕ) : ℕ∞) BZero) = true := by
    show (isOT_BT BZero
        && (gatherBT ((v1 - 1 : ℕ) : ℕ∞) BZero).all (fun x => lessBT x BZero)) = true
    simp [BZero, gatherBT, gatherBPList, isOT_BT, isOT_BPList, descP]
  -- === 順序 o1 / o2 ===
  have zA0 : lessBT BZero A0 = true :=
    lessBT_linear_trans _ _ _ (lessBT_zero_Dprin_an _ BZero) base0
  have o1 : leBT BZero A0 = true := leBT_of_lessBT_an zA0
  have o2 : leBT A0 (ins BZero) = true := leBT_of_lessBT_an base1'
  -- === head `ub` の otx3_pOT で `nub = isOT_BP (D_{v₁-1} A₀)` を組む ===
  exact pOT_an hGC loP hiP hA0OT o1 o2 tri0

#print axioms A0OTNub_of_residuals

end PSS
