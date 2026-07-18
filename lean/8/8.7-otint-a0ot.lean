import «8».«8.7-otint-transport-data»
import «8».«8.7-OT-scb-recursive»

/-!
# §8.7 `OTintIIIIV_otSetleCore` の原子 (a) `isOT_BT (ins A₀)` を放電（tri-transport への縮小）

- 原文: `tmp/content.md` §8.7（Trans が OT を保つことの内点ケースの surgery 残差）。
- Isabelle:
  * 原子 (a) `isOT_BT (ins A₀)` は census 語彙では `isOT_BT A₁`
    （`A₁ = d4vx_ins s₀ ub b₀ A₀`、`ub = v₁-1`）であり、これは
    `otx3_core_tri` (`isabelle/layerC/pss_scratch.thy`:2517) の結論の第 1 連言
    （`ot1_OTA1_from_bricks`:2597 が `otx3_core_tri[OF fX1 fA1 fX2 b0RP X1OT X2OT
    nub o1 o2 tri0]` で取り出す `A1OT`）である。
  * 深い脚 `nub = isOT_BP (D_ub A₀)` は `ot1_nub_from_A0OT` (`pss_scratch.thy`:4188)、
    その唯一の真の未知 `A0OT = isOT_BT (bpHeadT (Trans (Pred (s84x_N N))))` は
    `ot1_A0OT` (`pss_scratch.thy`:4762、§6 Red/slice ＋ §7 Trans ＋
    `m_8_7_OT_scb_recursive`) が census 前提から無条件に閉じる。
  * 深い脚 `tri0 = b1x_triG (D_∞ 0_B) A₀ (ins 0_B)` は `ot1_tri0_census`
    (`pss_scratch.thy`:4081)、condIII/IV mnform の CRUX。
  * tri-transport 本体 `otx3_core_tri` は setle 版 `otx3_core`（Lean 移植
    `oix_transport`）の tri0 直挿し版（body-level setle が偽なため setle 版は使えない）。
- 本ファイルの成果（**縮小 = narrowing**）:
  * 原子 (a) `isOT_BT (ins A₀)` を、より深い 3 本の named 脚
    `OixCoreTri`（= `otx3_core_tri` の第1連言）/ `A0OTNub`（= `ot1_nub_from_A0OT`
    の census 形）/ `Tri0Census`（= `ot1_tri0_census` の census 形）へ縮小する。
  * ポータブルな糊付けを無条件に閉じる:
    - 供与項の読み出し `loP = isOT_BP (D_{e₃} (ins 0_B))` /
      `hiP = isOT_BP (D_{e₃} (ins² 0_B))`（`buchholz_fseq_closed` ＋
      `OT_scb_recursive` ＋ fseq 閉形式 `scb_fseq_kind1`。`8.7-otint-setle` の
      `fO`/`donOT` パターン）から `X₁OT = isOT_BT (ins 0_B)` /
      `X₂OT = isOT_BT (ins² 0_B)`。
    - flat 形 `fX1`/`fA1`/`fX2`（`hflat` から構造的）。
    - 順序 `o1 = 0_B ≤ A₀`（base0 経由）/ `o2 = A₀ ≤ ins 0_B`（base1' 経由）。
  * `isOT_A0_of_provenance : OixCoreTri → A0OTNub → Tri0Census →
    OTintIIIIV_otSetleCoreA`（原子 (a) の census 版）。
- 依存（ビルド済みのみ import）:
  * `8.7-otint-transport-data`（透過的に `b1x_triG`・`GBT`・`buchholz_fseq_closed`・
    `scb_fseq_kind1`・`coreTower_e34`・`Dprin`・`isOT_BP`/`isOT_BT`・`flatBT`/`flatBP`・
    `leBT`/`lessBT`・`lessBT_linear_trans`・`scb_decomp`/`scb_kind1`・`STPS`・`monoT`・
    `oper`・`Trans`・`transCondIII`/`transCondIV`・`Lng`・`hasParent`・`OT_B` 等）。
  * `8.7-OT-scb-recursive`（`OT_scb_recursive`）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  残る named 脚 = `OixCoreTri`（tri-transport engine、[Buc1] Lemma 3.4/sandwich 系
  modulo）/ `A0OTNub`（← `ot1_A0OT`、§6 Red/slice 未移植）/ `Tri0Census`
  （condIII/IV mnform）。私的接尾辞 `_ao`。
-/

namespace PSS

/-! ## 1. flat-dfree 特徴づけ（`8.7-otint-setle` の private twin を再掲） -/

private def symFin_ao : Sym → Bool
  | .dsym v => v != (⊤ : ℕ∞)
  | _ => true

private def flatFin_ao (l : List Sym) : Bool := l.all symFin_ao

private theorem flatFin_append_ao (a b : List Sym) :
    flatFin_ao (a ++ b) = (flatFin_ao a && flatFin_ao b) := by
  simp only [flatFin_ao, List.all_append]

private theorem flatFin_cons_ao (x : Sym) (l : List Sym) :
    flatFin_ao (x :: l) = (symFin_ao x && flatFin_ao l) := by
  simp only [flatFin_ao, List.all_cons]

mutual
  private theorem dfree_flat_BT_ao : ∀ t : BT, dfree_BT t = flatFin_ao (flatBT t)
    | .trm [] => by rfl
    | .trm [p] => by
        show (dfree_BP p && dfree_BPList []) = flatFin_ao (flatBP p)
        rw [dfree_flat_BP_ao p]; simp [dfree_BPList]
    | .trm (p :: q :: ps) => by
        show (dfree_BP p && dfree_BPList (q :: ps))
            = flatFin_ao (Sym.lp :: (flatBP p ++ flatBPTail (q :: ps)) ++ [Sym.rp])
        rw [flatFin_append_ao, flatFin_cons_ao, flatFin_append_ao,
          dfree_flat_BP_ao p, dfree_flat_BPTail_ao (q :: ps)]
        simp [symFin_ao, flatFin_ao]
  private theorem dfree_flat_BP_ao : ∀ p : BP, dfree_BP p = flatFin_ao (flatBP p)
    | .db u a => by
        show ((u != (⊤ : ℕ∞)) && dfree_BT a) = flatFin_ao (Sym.dsym u :: flatBT a)
        rw [flatFin_cons_ao, dfree_flat_BT_ao a]; rfl
  private theorem dfree_flat_BPTail_ao : ∀ ps : List BP, dfree_BPList ps = flatFin_ao (flatBPTail ps)
    | [] => by rfl
    | p :: ps => by
        show (dfree_BP p && dfree_BPList ps) = flatFin_ao (Sym.cm :: flatBP p ++ flatBPTail ps)
        rw [flatFin_append_ao, flatFin_cons_ao, dfree_flat_BP_ao p, dfree_flat_BPTail_ao ps]
        simp [symFin_ao]
end

private theorem mem_T_B_iff_flatFin_ao (t : BT) : t ∈ T_B ↔ flatFin_ao (flatBT t) = true := by
  show dfree_BT t = true ↔ flatFin_ao (flatBT t) = true
  rw [dfree_flat_BT_ao t]

/-- `flatFin_ao (s ++ Dsym v :: mid ++ b)` から中身 `mid` の fin。 -/
private theorem flatFin_ins_mid_ao {s mid b : List Sym} {v : ℕ∞}
    (h : flatFin_ao (s ++ Sym.dsym v :: mid ++ b) = true) : flatFin_ao mid = true := by
  rw [flatFin_append_ao, flatFin_append_ao, flatFin_cons_ao] at h
  have h1 := ((Bool.and_eq_true _ _).mp h).1
  have h2 := ((Bool.and_eq_true _ _).mp h1).2
  exact ((Bool.and_eq_true _ _).mp h2).2

/-! ## 2. 順序・OT 補助 -/

private theorem leBT_of_lessBT_ao {a b : BT} (h : lessBT a b = true) : leBT a b = true := by
  simp [leBT, h]

private theorem lessBT_zero_Dprin_ao (v : ℕ∞) (a : BT) :
    lessBT BZero (Dprin v a) = true := by
  simp [BZero, Dprin, lessBT, lessBPList]

/-- `Dprin w x ∈ OT` から `isOT_BP (D_w x)`。 -/
private theorem isOT_BP_of_Dprin_OT_ao {w : ℕ∞} {x : BT} (h : Dprin w x ∈ OT) :
    isOT_BP (BP.db w x) = true := by
  have h' : isOT_BT (Dprin w x) = true := h
  simpa [Dprin, isOT_BT, isOT_BPList, descP] using h'

/-- `isOT_BP (D_w b)` から body の `isOT_BT b`。 -/
private theorem isOT_BT_of_isOT_BP_ao {w : ℕ∞} {b : BT}
    (h : isOT_BP (BP.db w b) = true) : isOT_BT b = true := by
  simp only [isOT_BP, Bool.and_eq_true] at h
  exact h.1

/-! ## 3. fseq 供与項の再構成（`8.7-otint-setle` の private twin を再掲） -/

private theorem coe_ne_top_ao (n : ℕ) : ((n : ℕ) : ℕ∞) ≠ ⊤ := by simp

private theorem flatten_replicate_snoc_ao {α : Type} (xs : List α) (n : ℕ) :
    List.flatten (List.replicate (n + 1) xs) =
      List.flatten (List.replicate n xs) ++ xs := by
  rw [List.replicate_add, List.flatten_append]; simp

/-- Isabelle `d4vx_core_flat`（任意底 `C`）。 -/
private theorem coreTower_flat_ao {ins : BT → BT} {ub : ℕ∞} {s0 b0 : List Sym}
    (hflat : ∀ X, flatBT (ins X) = s0 ++ Sym.dsym ub :: flatBT X ++ b0) :
    ∀ (C : BT) (j : ℕ), flatBT (coreTower_e34 ins C j)
      = List.flatten (List.replicate j (s0 ++ [Sym.dsym ub])) ++ flatBT C
        ++ List.flatten (List.replicate j b0)
  | C, 0 => by simp [coreTower_e34]
  | C, j + 1 => by
      show flatBT (ins (coreTower_e34 ins C j)) = _
      rw [hflat (coreTower_e34 ins C j), coreTower_flat_ao hflat C j,
        flatten_replicate_snoc_ao b0 j, List.replicate_succ, List.flatten_cons]
      simp [List.append_assoc]

/-- `flatBT t = s ++ flatBP (D_h C) ++ b`（`b` 全 `RP`, `h ≠ ⊤`, `C` は `D_ω`-free）
から scb 分解を組む。 -/
private theorem scb_of_flat_ao {t C : BT} {s b : List Sym} {h : ℕ∞}
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

/-! ## 4. 深い named 脚 & 縮小残差 -/

/-- tri-transport engine（Isabelle `otx3_core_tri` (`pss_scratch.thy`:2517) の結論
第 1 連言）。共有右端 spine の穴 `(s, b)`（`b` 全 `RP`）で同じ head `D_h` を持つ
3 core `aLo ≤ a' ≤ aHi` を差し替え、両端 `tLo`, `tHi` が `OT`、差し替え core が
`OT` principal `isOT_BP (D_h a')`、かつ hole-level G-統制 `tri0 = b1x_triG (D_∞ aLo)
a' aHi` が成り立てば、中間項 `t'` も `OT`。setle 版 `oix_transport`
（`8.7-otint-transport`）の tri0 直挿し版（condIII/IV body-level setle が偽で使えない）。 -/
def OixCoreTri : Prop :=
  ∀ (tLo t' tHi : BT) (s b : List Sym) (h : ℕ) (aLo a' aHi : BT),
    flatBT tLo = s ++ flatBP (BP.db (h : ℕ∞) aLo) ++ b →
    flatBT t' = s ++ flatBP (BP.db (h : ℕ∞) a') ++ b →
    flatBT tHi = s ++ flatBP (BP.db (h : ℕ∞) aHi) ++ b →
    (∀ x ∈ b, x = Sym.rp) →
    isOT_BT tLo = true → isOT_BT tHi = true →
    isOT_BP (BP.db (h : ℕ∞) a') = true →
    leBT aLo a' = true → leBT a' aHi = true →
    b1x_triG (Dprin (⊤ : ℕ∞) aLo) a' aHi →
    isOT_BT t' = true

/-- census 版 `nub = isOT_BP (D_{v₁-1} A₀)`（Isabelle `ot1_nub_from_A0OT`
(`pss_scratch.thy`:4188)）。唯一の真の未知は `A0OT = isOT_BT A₀`（Isabelle `ot1_A0OT`
(`pss_scratch.thy`:4762)、§6 Red/slice 未移植）で、そこから `otx3_pOT` ＋ 供与項 lift で
`nub` が出る。census データは `OTintIIIIV_otSetleCore` と同一の前提束で与える。 -/
def A0OTNub : Prop :=
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
    isOT_BP (BP.db ((v1 - 1 : ℕ) : ℕ∞) A0) = true

/-- census 版 `tri0 = b1x_triG (D_∞ 0_B) A₀ (ins 0_B)`（Isabelle `ot1_tri0_census`
(`pss_scratch.thy`:4081)、condIII/IV mnform の CRUX）。 -/
def Tri0Census : Prop :=
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
    b1x_triG (Dprin (⊤ : ℕ∞) BZero) A0 (ins BZero)

/-- `OTintIIIIV_otSetleCore` の第 1 連言（原子 (a) `isOT_BT (ins A₀)`）だけを取り出した
Prop。前提束は `OTintIIIIV_otSetleCore`（`8.7-otint-setle`:56）と同一。 -/
def OTintIIIIV_otSetleCoreA : Prop :=
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
    isOT_BT (ins A0) = true

/-! ## 5. 縮小: 原子 (a) を tri-transport ＋ nub ＋ tri0 へ -/

/-- **縮小**: 原子 (a) `isOT_BT (ins A₀)`（`OTintIIIIV_otSetleCoreA`）を、tri-transport
engine `OixCoreTri`（= `otx3_core_tri`）と 2 本の深い census 脚 `A0OTNub`（= nub、
唯一の真の未知は `ot1_A0OT`）/ `Tri0Census`（= tri0）へ縮小する。供与項の読み出しから
`X₁OT`/`X₂OT`、`hflat` から flat 形、base0/base1' から順序を無条件に閉じる
（Isabelle `ot1_OTA1_from_bricks`:2597 の `otx3_core_tri` 適用に対応）。 -/
theorem isOT_A0_of_provenance (coreTri : OixCoreTri) (hnub : A0OTNub) (htri0 : Tri0Census) :
    OTintIIIIV_otSetleCoreA := by
  intro M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcond hp hOT
    hflat hb0 hb1 hinner hk1 hmn base0 base1'
  -- === 深い脚 nub / tri0 ===
  have nub : isOT_BP (BP.db ((v1 - 1 : ℕ) : ℕ∞) A0) = true :=
    hnub M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcond hp hOT
      hflat hb0 hb1 hinner hk1 hmn base0 base1'
  have tri0 : b1x_triG (Dprin (⊤ : ℕ∞) BZero) A0 (ins BZero) :=
    htri0 M ins A0 body e3 v1 s0 b0 s1 b1 hST hmono hj1 hcond hp hOT
      hflat hb0 hb1 hinner hk1 hmn base0 base1'
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
    rw [coreTower_flat_ao hflat BZero (k + 1)]
    simp [BZero, flatBT, List.append_assoc]
  -- === X₁ = ins 0_B（numBT 0 供与項の kind-1 core）===
  have hdon0 : operB (Trans M) (numBT 0) ∈ OT_B := buchholz_fseq_closed (Trans M) 0 hOT hne
  have loflat : flatBT (operB (Trans M) (numBT 0))
      = s1 ++ flatBP (BP.db (e3 : ℕ∞) (ins BZero)) ++ b1 := by
    have h := fO 0
    rwa [(rfl : coreTower_e34 ins BZero (0 + 1) = ins BZero)] at h
  have hY1df : ins BZero ∈ T_B := by
    have hfin : flatFin_ao (flatBT (operB (Trans M) (numBT 0))) = true :=
      (mem_T_B_iff_flatFin_ao _).mp hdon0.2
    rw [loflat, show flatBP (BP.db (e3 : ℕ∞) (ins BZero))
        = Sym.dsym (e3 : ℕ∞) :: flatBT (ins BZero) from rfl] at hfin
    exact (mem_T_B_iff_flatFin_ao _).mpr (flatFin_ins_mid_ao hfin)
  have hY1TB : Dprin (e3 : ℕ∞) (ins BZero) ∈ T_B := by
    show dfree_BT (Dprin (e3 : ℕ∞) (ins BZero)) = true
    have hh : dfree_BT (ins BZero) = true := hY1df
    simp [Dprin, dfree_BT, dfree_BPList, dfree_BP, hh]
  have lodec : scb_decomp (operB (Trans M) (numBT 0)) s1
      (flatBT (Dprin (e3 : ℕ∞) (ins BZero))) b1 :=
    scb_of_flat_ao loflat hY1df (coe_ne_top_ao e3) hb1
  have loOT : Dprin (e3 : ℕ∞) (ins BZero) ∈ OT :=
    OT_scb_recursive _ _ s1 b1 hdon0 hY1TB lodec
  have loP : isOT_BP (BP.db (e3 : ℕ∞) (ins BZero)) = true := isOT_BP_of_Dprin_OT_ao loOT
  have X1OT : isOT_BT (ins BZero) = true := isOT_BT_of_isOT_BP_ao loP
  -- === X₂ = ins² 0_B（numBT 1 供与項の kind-1 core）===
  have hdon1 : operB (Trans M) (numBT 1) ∈ OT_B := buchholz_fseq_closed (Trans M) 1 hOT hne
  have hiflat : flatBT (operB (Trans M) (numBT 1))
      = s1 ++ flatBP (BP.db (e3 : ℕ∞) (ins (ins BZero))) ++ b1 := by
    have h := fO 1
    rwa [(rfl : coreTower_e34 ins BZero (1 + 1) = ins (ins BZero))] at h
  have hY2df : ins (ins BZero) ∈ T_B := by
    have hfin : flatFin_ao (flatBT (operB (Trans M) (numBT 1))) = true :=
      (mem_T_B_iff_flatFin_ao _).mp hdon1.2
    rw [hiflat, show flatBP (BP.db (e3 : ℕ∞) (ins (ins BZero)))
        = Sym.dsym (e3 : ℕ∞) :: flatBT (ins (ins BZero)) from rfl] at hfin
    exact (mem_T_B_iff_flatFin_ao _).mpr (flatFin_ins_mid_ao hfin)
  have hY2TB : Dprin (e3 : ℕ∞) (ins (ins BZero)) ∈ T_B := by
    show dfree_BT (Dprin (e3 : ℕ∞) (ins (ins BZero))) = true
    have hh : dfree_BT (ins (ins BZero)) = true := hY2df
    simp [Dprin, dfree_BT, dfree_BPList, dfree_BP, hh]
  have hidec : scb_decomp (operB (Trans M) (numBT 1)) s1
      (flatBT (Dprin (e3 : ℕ∞) (ins (ins BZero)))) b1 :=
    scb_of_flat_ao hiflat hY2df (coe_ne_top_ao e3) hb1
  have hiOT : Dprin (e3 : ℕ∞) (ins (ins BZero)) ∈ OT :=
    OT_scb_recursive _ _ s1 b1 hdon1 hY2TB hidec
  have hiP : isOT_BP (BP.db (e3 : ℕ∞) (ins (ins BZero))) = true := isOT_BP_of_Dprin_OT_ao hiOT
  have X2OT : isOT_BT (ins (ins BZero)) = true := isOT_BT_of_isOT_BP_ao hiP
  -- === flat 形 fX1 / fA1 / fX2（`hflat` から）===
  have fX1 : flatBT (ins BZero)
      = s0 ++ flatBP (BP.db ((v1 - 1 : ℕ) : ℕ∞) BZero) ++ b0 := by
    rw [hflat BZero]; rfl
  have fA1 : flatBT (ins A0)
      = s0 ++ flatBP (BP.db ((v1 - 1 : ℕ) : ℕ∞) A0) ++ b0 := by
    rw [hflat A0]; rfl
  have fX2 : flatBT (ins (ins BZero))
      = s0 ++ flatBP (BP.db ((v1 - 1 : ℕ) : ℕ∞) (ins BZero)) ++ b0 := by
    rw [hflat (ins BZero)]; rfl
  -- === 順序 o1 / o2 ===
  have zA0 : lessBT BZero A0 = true :=
    lessBT_linear_trans _ _ _ (lessBT_zero_Dprin_ao _ BZero) base0
  have o1 : leBT BZero A0 = true := leBT_of_lessBT_ao zA0
  have o2 : leBT A0 (ins BZero) = true := leBT_of_lessBT_ao base1'
  -- === tri-transport で `isOT_BT (ins A₀)` を組み立て（Isabelle `otx3_core_tri`）===
  exact coreTri (ins BZero) (ins A0) (ins (ins BZero)) s0 b0 (v1 - 1) BZero A0 (ins BZero)
    fX1 fA1 fX2 hb0 X1OT X2OT nub o1 o2 tri0

#print axioms isOT_A0_of_provenance

end PSS
