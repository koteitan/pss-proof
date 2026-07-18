import «8».«8.7-otdisp-OTint»
import «8».«8.7-otint-uncond»
import «8».«8.4-exch84-producer»

/-!
# §8.7 `OTdisp_OTint` — 条件 (III)/(IV) の `hasParent` 脚（transport）

- 原文: `tmp/content.md` §8.7（Trans が OT を保つことの証明の内点ケース）。
- Isabelle:
  * `oi8_OTint_condIII` (`isabelle/layerC/pss_scratch.thy`:3716) /
    `oi8_OTint_condIV` (:3774) の `proof (cases "hasParent N 1 (Lng N - 1)")` の
    **`True` 側**＝`oi8_OTint_IIIIV_hp` (:3432) 経由。
    （`False` 側＝no-parent 隅は既にビルド済み `8.7-otdisp-OTint` の
    `OTint_noParent_oi` が担当。）
  * `oi8_OTint_IIIIV_hp` は `oi5_IIIIV_pkg` の出力 ＝ Lean の
    `Exch84_condIIIIV_slicepkg` (`8.4-exch84-producer`:128) を材料に、
    `oix_transportD[OF otx3_transport lodec ourdec hidec ...]`
    （Lean は `oix_transportD` を無条件版 `oix_transport_uncond`
    (`8.7-otint-uncond`) に適用）で `isOT_BT (Trans (N[m]))` を出す。
    lo/mid/hi の 3 分解は `numBT (k-1)/`(k=1 なら 0) と `numBT (k+1)`/`(k=1 なら 2)`、
    core は固定三つ組 `(Y₁, A₁, Y₃) = (ins 0_B, ins A₀, ins³ 0_B)`。
- 本ファイルの成果:
  * `OTint_hp_condIII_of_slicepkg` / `OTint_hp_condIV_of_slicepkg`:
    残差 = `Exch84_condIIIIV_slicepkg`（そのまま採用）＋ 本ファイルが露出する
    `OTintIIIIV_transportData`（Isabelle の `OTA1_ltJ`/`SETLE1_ltJ` の 2 残差
    ＋ `oi5_IIIIV_pkg` の構造事実 `A₀ ∈ T_B` / `ins` の `T_B` 保存）を仮定に、
    `OTint_hp_condIII` / `OTint_hp_condIV` を出す。
  * transport 本体（fseq 閉形式・順序・2 ケース分解）は無条件に移植し、
    残差は上記 2 本 (slicepkg, transportData) に正確に絞る。
- 依存（ビルド済みのみ import）:
  `8.7-otdisp-OTint`（`OTint_hp_condIII`/`OTint_hp_condIV`/`OTdisp_OTint` の def 元、
  透過的に `OT_B`/`isOT_BT`/`scb_decomp` 等）、
  `8.7-otint-uncond`（`oix_transport_uncond`、透過的に `oix_transportD`・`b1x_setle`・
  `buchholz_fseq_closed`）、`8.4-exch84-producer`（`Exch84_condIIIIV_slicepkg`・
  `coreTower_e34`・`scb_fseq_kind1`・`Trans_mem_T_B`・`STPS_RTPS`）。
- 状態: 🤖 GREEN-MODULO（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  私的接尾辞 `_oc34`。
-/

namespace PSS

/-! ## 1. 残差 `Prop`（Isabelle `OTA1_ltJ` / `SETLE1_ltJ` ＋ 構造 `T_B` 事実） -/

/-- `oi5_IIIIV_pkg`（＝`Exch84_condIIIIV_slicepkg`）の出力データについて、Isabelle の
`OTA1` (`isOT_BP (D_{e₃} (ins A₀))`)・`SETLE1` (`⊴`-支配) ＋ 構造事実
`A₀ ∈ T_B`・`ins` の `T_B` 保存 を主張する残差。前提は slicepkg の本体そのもの。 -/
def OTintIIIIV_transportData : Prop :=
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
    A0 ∈ T_B ∧
    (∀ X, X ∈ T_B → ins X ∈ T_B) ∧
    isOT_BP (BP.db (e3 : ℕ∞) (ins A0)) = true ∧
    (∀ u : ℕ∞, b1x_setle (GBT u (ins A0)) (insert (ins BZero) (GBT u (ins BZero))))

/-! ## 2. 小補題（suffix `_oc34`） -/

private theorem coe_ne_top_oc34 (n : ℕ) : ((n : ℕ) : ℕ∞) ≠ ⊤ := by simp

private theorem leBT_of_lessBT_oc34 {a b : BT} (h : lessBT a b = true) : leBT a b = true := by
  simp [leBT, h]

private theorem lessBT_zero_Dprin_oc34 (v : ℕ∞) (a : BT) :
    lessBT BZero (Dprin v a) = true := by
  simp [BZero, Dprin, lessBT, lessBPList]

/-- Isabelle `c4cx_d4vx_ins_mono`（producer の `ins_mono_ep` の再掲）。 -/
private theorem ins_mono_oc34 {ins : BT → BT} {ub : ℕ∞} {s0 b0 : List Sym}
    (hflat : ∀ X, flatBT (ins X) = s0 ++ Sym.dsym ub :: flatBT X ++ b0)
    (hb0 : ∀ x ∈ b0, x = Sym.rp) {X Y : BT} (h : lessBT X Y = true) :
    lessBT (ins X) (ins Y) = true := by
  refine scbext_lessBT (s := s0) (b := b0) (cp := .db ub X) (cp' := .db ub Y) ?_ ?_ hb0 ?_
  · rw [hflat X]; rfl
  · rw [hflat Y]; rfl
  · simp [lessBP, h]

/-- producer の `flatten_replicate_snoc_ep` の再掲。 -/
private theorem flatten_replicate_snoc_oc34 {α : Type} (xs : List α) (n : ℕ) :
    List.flatten (List.replicate (n + 1) xs) =
      List.flatten (List.replicate n xs) ++ xs := by
  rw [List.replicate_add, List.flatten_append]; simp

/-- Isabelle `c4cx_d4vx_core_compose`（`8.4` の `coreTower_compose_e34` の再掲）。 -/
private theorem coreTower_compose_oc34 (ins : BT → BT) (t : BT) (i : ℕ) :
    ∀ k, coreTower_e34 ins (coreTower_e34 ins t i) k = coreTower_e34 ins t (k + i)
  | 0 => by simp [coreTower_e34]
  | k + 1 => by
      show ins (coreTower_e34 ins (coreTower_e34 ins t i) k) = _
      rw [coreTower_compose_oc34 ins t i k]
      have e : k + 1 + i = (k + i) + 1 := by omega
      rw [e]
      rfl

/-- Isabelle `d4vx_core_flat`（任意底 `C`）。挿入段 flat 則から帰納。 -/
private theorem coreTower_flat_oc34 {ins : BT → BT} {ub : ℕ∞} {s0 b0 : List Sym}
    (hflat : ∀ X, flatBT (ins X) = s0 ++ Sym.dsym ub :: flatBT X ++ b0) :
    ∀ (C : BT) (j : ℕ), flatBT (coreTower_e34 ins C j)
      = List.flatten (List.replicate j (s0 ++ [Sym.dsym ub])) ++ flatBT C
        ++ List.flatten (List.replicate j b0)
  | C, 0 => by simp [coreTower_e34]
  | C, j + 1 => by
      show flatBT (ins (coreTower_e34 ins C j)) = _
      rw [hflat (coreTower_e34 ins C j), coreTower_flat_oc34 hflat C j,
        flatten_replicate_snoc_oc34 b0 j, List.replicate_succ, List.flatten_cons]
      simp [List.append_assoc]

/-- `flatBT t = s ++ flatBP (D_h C) ++ b`（`b` 全 `RP`, `h ≠ ⊤`, `C` は `D_ω`-free）
から scb 分解を組む。 -/
private theorem scb_of_flat_oc34 {t C : BT} {s b : List Sym} {h : ℕ∞}
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

private theorem mem_flatten_replicate_oc34 {α : Type} {x : α} {xs : List α} {n : ℕ}
    (h : x ∈ List.flatten (List.replicate n xs)) : x ∈ xs := by
  rcases List.mem_flatten.mp h with ⟨as, has, hmem⟩
  rw [List.eq_of_mem_replicate has] at hmem
  exact hmem

/-! ## 3. `gatherBT` の反単調性（fseq-closed の private twin の再掲） -/

mutual
  private theorem gatherBT_antitone_oc34 {u v : ℕ∞} (huv : u ≤ v)
      (x : BT) : ∀ t : BT, x ∈ gatherBT v t → x ∈ gatherBT u t
    | .trm ps, hx => gatherBPList_antitone_oc34 huv x ps hx

  private theorem gatherBP_antitone_oc34 {u v : ℕ∞} (huv : u ≤ v)
      (x : BT) : ∀ p : BP, x ∈ gatherBP v p → x ∈ gatherBP u p
    | .db w b, hx => by
        have hvw : v ≤ w := by
          by_contra hn
          simp [gatherBP, hn] at hx
        have huw : u ≤ w := huv.trans hvw
        simp only [gatherBP, hvw, huw, decide_true, if_true, List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (gatherBT_antitone_oc34 huv x b hx)

  private theorem gatherBPList_antitone_oc34 {u v : ℕ∞} (huv : u ≤ v)
      (x : BT) : ∀ ps : List BP, x ∈ gatherBPList v ps → x ∈ gatherBPList u ps
    | [], hx => by simp [gatherBPList] at hx
    | p :: ps, hx => by
        simp only [gatherBPList, List.mem_append] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl (gatherBP_antitone_oc34 huv x p hx)
        · exact Or.inr (gatherBPList_antitone_oc34 huv x ps hx)
end

/-! ## 4. transport 本体（Isabelle `oi8_OTint_IIIIV_hp` の `True` 側） -/

/-- 条件 (III)/(IV) の `hasParent` 脚。core = 固定三つ組 `(ins 0_B, ins A₀, ins³ 0_B)`。 -/
private theorem OTint_hp_core_oc34
    (hpkg : Exch84_condIIIIV_slicepkg) (hres : OTintIIIIV_transportData)
    (N : PS) (m : ℕ) (hST : STPS N) (hmono : monoT N = true) (j1gt : 1 < Lng N - 1)
    (hcond : transCondIII N = true ∨ transCondIV N = true)
    (hp : hasParent N 1 (Lng N - 1) = true) (hOT : Trans N ∈ OT_B) (hm : 1 < m) :
    Trans (oper N m) ∈ OT_B := by
  obtain ⟨ins, A0, body, e3, v1, s0, b0, s1, b1,
    hflat, hb0, hb1, hinner, hk1, hmn, base0, base1'⟩ := hpkg N hST hmono j1gt hcond hp
  obtain ⟨hA0TB, hinsTB, newOTe3, setle⟩ :=
    hres N ins A0 body e3 v1 s0 b0 s1 b1 hST hmono j1gt hcond hp hOT
      hflat hb0 hb1 hinner hk1 hmn base0 base1'
  have hTB : Trans N ∈ T_B := hOT.2
  have hbf : flatBT (Dprin (e3:ℕ∞) body) = Sym.dsym (e3:ℕ∞) :: flatBT body := rfl
  have hne : Trans N ≠ BZero := by
    intro hz
    have hlen := congrArg List.length hk1.1.1
    rw [hz, hbf, hinner.1] at hlen
    simp only [BZero, flatBT, flatBP, Dprin, List.length_cons, List.length_append,
      List.length_nil] at hlen
    omega
  have donOT : ∀ n, isOT_BT (operB (Trans N) (numBT n)) = true :=
    fun n => (buchholz_fseq_closed (Trans N) n hOT hne).1
  have hinner' : scb_decomp (Dprin (e3:ℕ∞) body) (Sym.dsym (e3:ℕ∞) :: s0)
      (flatBT (Dprin (v1:ℕ∞) BZero)) b0 := by
    refine ⟨?_, ?_, hinner.2.2⟩
    · rw [hbf, hinner.1]; simp
    · intro _
      exact ⟨.db (v1:ℕ∞) BZero, by simp [dfree_BP, BZero, dfree_BT, dfree_BPList], rfl⟩
  have fO : ∀ k, flatBT (operB (Trans N) (numBT k))
      = s1 ++ flatBP (BP.db (e3:ℕ∞) (coreTower_e34 ins BZero (k + 1))) ++ b1 := by
    intro k
    have hfseq := (scb_fseq_kind1 (n := k) hTB hk1 hinner').2
    rw [hfseq]
    simp only [flatBP]
    rw [coreTower_flat_oc34 hflat BZero (k + 1)]
    simp [BZero, flatBT, List.append_assoc]
  have huv : e3 < v1 := (scb_fseq_kind1 (n := 0) hTB hk1 hinner').1
  have hBZeroTB : BZero ∈ T_B := by simp [T_B, BZero, dfree_BT, dfree_BPList]
  have hY1TB : dfree_BT (ins BZero) = true := hinsTB BZero hBZeroTB
  have hA1TB : dfree_BT (ins A0) = true := hinsTB A0 hA0TB
  have hY2TB : dfree_BT (ins (ins BZero)) = true := hinsTB _ hY1TB
  have hY3TB : dfree_BT (ins (ins (ins BZero))) = true := hinsTB _ hY2TB
  have zA0 : lessBT BZero A0 = true :=
    lessBT_linear_trans _ _ _ (lessBT_zero_Dprin_oc34 _ BZero) base0
  have ordlo : leBT (ins BZero) (ins A0) = true :=
    leBT_of_lessBT_oc34 (ins_mono_oc34 hflat hb0 zA0)
  have zltY1 : lessBT BZero (ins BZero) = true :=
    lessBT_linear_trans _ _ _ zA0 base1'
  have Y1ltY2 : lessBT (ins BZero) (ins (ins BZero)) = true :=
    ins_mono_oc34 hflat hb0 zltY1
  have A0ltY2 : lessBT A0 (ins (ins BZero)) = true :=
    lessBT_linear_trans _ _ _ base1' Y1ltY2
  have ordhi : leBT (ins A0) (ins (ins (ins BZero))) = true :=
    leBT_of_lessBT_oc34 (ins_mono_oc34 hflat hb0 A0ltY2)
  have e3le : ((e3 : ℕ) : ℕ∞) ≤ ((v1 - 1 : ℕ) : ℕ∞) := by
    have h : e3 ≤ v1 - 1 := by omega
    exact_mod_cast h
  have newOTub : isOT_BP (BP.db ((v1 - 1 : ℕ) : ℕ∞) (ins A0)) = true := by
    simp only [isOT_BP, Bool.and_eq_true, List.all_eq_true] at newOTe3 ⊢
    refine ⟨newOTe3.1, ?_⟩
    intro x hx
    exact newOTe3.2 x (gatherBT_antitone_oc34 e3le x (ins A0) hx)
  have isot : isOT_BT (Trans (oper N m)) = true := by
    rcases m with _ | _ | _ | k2
    · exact absurd hm (by decide)
    · exact absurd hm (by decide)
    · have ourflat : flatBT (Trans (oper N 2))
          = s1 ++ flatBP (BP.db (e3:ℕ∞) (ins A0)) ++ b1 := by
        have h := hmn 2 (by norm_num)
        rwa [(rfl : coreTower_e34 ins A0 (2 - 1) = ins A0)] at h
      have loflat : flatBT (operB (Trans N) (numBT 0))
          = s1 ++ flatBP (BP.db (e3:ℕ∞) (ins BZero)) ++ b1 := by
        have h := fO 0
        rwa [(rfl : coreTower_e34 ins BZero (0 + 1) = ins BZero)] at h
      have hiflat : flatBT (operB (Trans N) (numBT 2))
          = s1 ++ flatBP (BP.db (e3:ℕ∞) (ins (ins (ins BZero)))) ++ b1 := by
        have h := fO 2
        rwa [(rfl : coreTower_e34 ins BZero (2 + 1) = ins (ins (ins BZero)))] at h
      have ourdec := scb_of_flat_oc34 ourflat hA1TB (coe_ne_top_oc34 e3) hb1
      have lodec := scb_of_flat_oc34 loflat hY1TB (coe_ne_top_oc34 e3) hb1
      have hidec := scb_of_flat_oc34 hiflat hY3TB (coe_ne_top_oc34 e3) hb1
      exact oix_transportD oix_transport_uncond lodec ourdec hidec
        (donOT 0) (donOT 2) newOTe3 ordlo ordhi setle
    · have compA : coreTower_e34 ins A0 (k2 + 2) = coreTower_e34 ins (ins A0) (k2 + 1) := by
        have h := coreTower_compose_oc34 ins A0 1 (k2 + 1)
        rw [(rfl : coreTower_e34 ins A0 1 = ins A0), (by omega : k2 + 1 + 1 = k2 + 2)] at h
        exact h.symm
      have compY1 : coreTower_e34 ins BZero (k2 + 2)
          = coreTower_e34 ins (ins BZero) (k2 + 1) := by
        have h := coreTower_compose_oc34 ins BZero 1 (k2 + 1)
        rw [(rfl : coreTower_e34 ins BZero 1 = ins BZero),
          (by omega : k2 + 1 + 1 = k2 + 2)] at h
        exact h.symm
      have compY3 : coreTower_e34 ins BZero (k2 + 4)
          = coreTower_e34 ins (ins (ins (ins BZero))) (k2 + 1) := by
        have h := coreTower_compose_oc34 ins BZero 3 (k2 + 1)
        rw [(rfl : coreTower_e34 ins BZero 3 = ins (ins (ins BZero))),
          (by omega : k2 + 1 + 3 = k2 + 4)] at h
        exact h.symm
      have deepflat : ∀ C : BT, flatBT (coreTower_e34 ins C (k2 + 1))
          = (List.flatten (List.replicate k2 (s0 ++ [Sym.dsym ((v1 - 1 : ℕ) : ℕ∞)])) ++ s0)
            ++ flatBP (BP.db ((v1 - 1 : ℕ) : ℕ∞) C)
            ++ List.flatten (List.replicate (k2 + 1) b0) := by
        intro C
        rw [coreTower_flat_oc34 hflat C (k2 + 1),
          flatten_replicate_snoc_oc34 (s0 ++ [Sym.dsym ((v1 - 1 : ℕ) : ℕ∞)]) k2]
        simp only [flatBP, List.append_assoc, List.cons_append, List.nil_append]
      have mkflat : ∀ (t C : BT),
          flatBT t = s1 ++ flatBP (BP.db (e3:ℕ∞) (coreTower_e34 ins C (k2 + 1))) ++ b1 →
          flatBT t
            = (s1 ++ Sym.dsym (e3:ℕ∞)
                :: (List.flatten (List.replicate k2 (s0 ++ [Sym.dsym ((v1 - 1 : ℕ) : ℕ∞)]))
                    ++ s0))
              ++ flatBP (BP.db ((v1 - 1 : ℕ) : ℕ∞) C)
              ++ (List.flatten (List.replicate (k2 + 1) b0) ++ b1) := by
        intro t C ht
        have key : flatBT (coreTower_e34 ins C (k2 + 1))
            = List.flatten (List.replicate k2 (s0 ++ [Sym.dsym ((v1 - 1 : ℕ) : ℕ∞)])) ++ s0
              ++ (Sym.dsym ((v1 - 1 : ℕ) : ℕ∞) :: flatBT C)
              ++ List.flatten (List.replicate (k2 + 1) b0) := by
          rw [deepflat C]; simp only [flatBP, List.append_assoc, List.cons_append]
        rw [ht]
        simp only [flatBP, key, List.append_assoc, List.cons_append]
      have hBrp : ∀ x ∈ (List.flatten (List.replicate (k2 + 1) b0) ++ b1), x = Sym.rp := by
        intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact hb0 x (mem_flatten_replicate_oc34 h)
        · exact hb1 x h
      have ourflat := mkflat (Trans (oper N (k2 + 3))) (ins A0) (by
        have h := hmn (k2 + 3) (by omega)
        rw [(by omega : k2 + 3 - 1 = k2 + 2), compA] at h
        exact h)
      have loflat := mkflat (operB (Trans N) (numBT (k2 + 1))) (ins BZero) (by
        have h := fO (k2 + 1)
        rw [(by omega : k2 + 1 + 1 = k2 + 2), compY1] at h
        exact h)
      have hiflat := mkflat (operB (Trans N) (numBT (k2 + 3))) (ins (ins (ins BZero))) (by
        have h := fO (k2 + 3)
        rw [(by omega : k2 + 3 + 1 = k2 + 4), compY3] at h
        exact h)
      have ourdec := scb_of_flat_oc34 ourflat hA1TB (coe_ne_top_oc34 (v1 - 1)) hBrp
      have lodec := scb_of_flat_oc34 loflat hY1TB (coe_ne_top_oc34 (v1 - 1)) hBrp
      have hidec := scb_of_flat_oc34 hiflat hY3TB (coe_ne_top_oc34 (v1 - 1)) hBrp
      exact oix_transportD oix_transport_uncond lodec ourdec hidec
        (donOT (k2 + 1)) (donOT (k2 + 3)) newOTub ordlo ordhi setle
  have hMmST : STPS (oper N m) := STPS.oper hST m (by omega)
  have hMmTB : Trans (oper N m) ∈ T_B := Trans_mem_T_B _ (STPS_RTPS _ hMmST)
  exact ⟨isot, hMmTB⟩

/-! ## 5. 主結果（`8.7-otdisp-OTint` の `OTint_hp_condIII` / `OTint_hp_condIV` の drop-in） -/

/-- Isabelle `oi8_OTint_condIII` の `True` 枝。残差 = slicepkg ＋ transportData。 -/
theorem OTint_hp_condIII_of_slicepkg
    (hpkg : Exch84_condIIIIV_slicepkg) (hres : OTintIIIIV_transportData) :
    OTint_hp_condIII := by
  intro N m hST hmono j1gt hc hp hOT hm
  exact OTint_hp_core_oc34 hpkg hres N m hST hmono j1gt (Or.inl hc) hp hOT hm

/-- Isabelle `oi8_OTint_condIV` の `True` 枝。残差 = slicepkg ＋ transportData。 -/
theorem OTint_hp_condIV_of_slicepkg
    (hpkg : Exch84_condIIIIV_slicepkg) (hres : OTintIIIIV_transportData) :
    OTint_hp_condIV := by
  intro N m hST hmono j1gt hc hp hOT hm
  exact OTint_hp_core_oc34 hpkg hres N m hST hmono j1gt (Or.inr hc) hp hOT hm

#print axioms OTint_hp_condIII_of_slicepkg
#print axioms OTint_hp_condIV_of_slicepkg

end PSS
