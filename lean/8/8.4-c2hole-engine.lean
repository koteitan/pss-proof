import «8».«8.4-rightmost-readback»
import «8».«8.5-exchV-props»
import «7».«7.3-Trans-welldefined»

/-!
# §8.4 補題 — `c₂` 右端穴エンジン（`s84d_c2hole` / `s84d_corepair_*`）

- 原文: `tmp/content.md` §8.4「補題（条件(III)～(V)の下での右端の置き換えと `Trans`
  の関係）」(4265)。`isabelle/pss_paper.thy`:1945 は DEFERRED。
- ブループリント: Isabelle `s84d_c2hole` / `s84d_corepair_shared` /
  `s84d_corepair_nested` / `s84d_c2hole_scb`（`isabelle/layerB/pss_wip.thy`
  58412–58657）。**値ルート（`Trans` の閉形式 T2 リードバック）は条件 (IV) の入れ子形
  で崩れ大域的に偽（`«8».«8.4-rightmost-readback»` header 参照）**。忠実ルートは本
  ファイルの穴エンジン: `transC2 M` の最内右端 core `D_{M₁,j₁} 0` をパラメータ `a` の
  `D_a 0` に差し替えた `c2hole_ch M a` について、**すべての `a` を共通の `(w, w')` で
  印付けする**という単一の scb 分解を produce する。これが `transC2 M`（`a = M₁,j₁`）と
  `transC2 L₁`（`a = M₁,j₋₂`）の SHARED scb 分解を与え、`Rightmost84ReplaceExists`
  （＝ `rm84Readback`/`rm84Exists` フィールド）の忠実な攻め口となる。

- 本ファイルの寄与（すべて GREEN・無条件 or 明示仮定 modulo）:
  1. `c2hole_ch`（`transC2Core` を逐語ミラーし最内 core を穴 `a` に）＋
     `c2hole_at_j1_ch`（`transC2 M = c2hole_ch M (entry M 1 (lastIdx M))`、`rfl`）。
  2. scb combinator: `scb_self_ch` / `corepair_shared_ch`（`s84d_corepair_shared`）/
     `corepair_nested_ch`（`s84d_corepair_nested`）。
  3. エンジン `c2hole_scb_ch`（`s84d_c2hole_scb`）: `RTPS M`・`TPS M`・`monoT M`・
     `transJ1 M > 0`・`transT1 M ≠ 0_B` の下で、頭 `D_{transV M}` を露出したまま
     すべての `a` を共有 `(w, w')` で印付ける scb 分解を produce（4 分岐: condI/III/V,
     condVI, `t₂ = 0_B`, 入れ子）。
  4. 橋 `C2HoleSliceTransport_ch` ＋ `rightmost84ReplaceExists_of_transport_ch`
     （さらに `..._corrected_ch`）: 手術による切片リードバック（`Trans (s84x_Np M)` /
     `Trans (rrLp M)` が `c2hole_ch` の scb 分解を継承する）を明示仮定として与えれば、
     エンジンが `Rightmost84ReplaceExists` を落とす（house pattern）。残差 = 手術
     transport（Isabelle L4 part(2)(3) = `p_8_2_condV_terminal_slice_Trans` gate）。

- 依存: `«8».«8.4-rightmost-readback»`（`Rightmost84ReplaceExists`/`s84x_Np`/`rrLp`/
  `s84x_jm2`/`Rightmost84ReplaceCorrected`/`rightmost84ReplaceCorrected_of_exists`）、
  `«8».«8.5-exchV-props»`（`c1_shape_holds : ExchV_scbdec_c1_shape`）、
  `«7».«7.3-Trans-welldefined»`（`Dprin_mem_T_B`/`Trans_Mark_invariant`）、
  `«7».«7.2-add-scb»`（`add_scb_marked`/`add_scb_replace_last`/`addBT_mem_T_B`）、
  `«7».«7.2-scb-compose»`（`scb_compose`/`scb_compose_dprin`）。
- 状態: 🤖 GREEN（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
- Private suffix: `_ch`。
-/

namespace PSS

/-! ## 0. `T_B` 補助（`«7».«7.3-Trans-welldefined»` の private 群の複製） -/

private theorem bzero_mem_ch : BZero ∈ T_B := by
  simp [T_B, BZero, dfree_BT, dfree_BPList]

private theorem dprinNat_mem_ch (a : ℕ) : Dprin (a : ℕ∞) BZero ∈ T_B :=
  Dprin_mem_T_B (by simp) bzero_mem_ch

private theorem dprinP_ch (a : ℕ) : ∃ p, Dprin (a : ℕ∞) BZero = BT.trm [p] :=
  ⟨.db (a : ℕ∞) BZero, rfl⟩

private theorem dprinStr_ch (a : ℕ) :
    isPTB_str (flatBT (Dprin (a : ℕ∞) BZero)) := by
  refine ⟨.db (a : ℕ∞) BZero, ?_, ?_⟩
  · simp [dfree_BP, dfree_BT, dfree_BPList, BZero]
  · simp [Dprin, flatBT]

private theorem dfree_BPList_take_ch (ps : List BP) (n : ℕ)
    (hps : dfree_BPList ps = true) : dfree_BPList (ps.take n) = true := by
  induction n generalizing ps with
  | zero => simp [dfree_BPList]
  | succ n ih =>
      cases ps with
      | nil => simp [dfree_BPList]
      | cons p ps =>
          simp only [dfree_BPList, Bool.and_eq_true] at hps
          simpa [dfree_BPList] using And.intro hps.1 (ih ps hps.2)

private theorem flatMap_untrm_take_map_ch (ps : List BP) (n : ℕ) :
    ((ps.map fun p => BT.trm [p]).take n).flatMap untrm = ps.take n := by
  induction n generalizing ps with
  | zero => simp
  | succ n ih =>
      cases ps with
      | nil => simp
      | cons p ps => simp [ih ps, untrm]

private theorem SigmaB_PB_take_mem_ch (t : BT) (n : ℕ) (ht : t ∈ T_B) :
    SigmaB ((PB t).take n) ∈ T_B := by
  rcases t with ⟨ps⟩
  change dfree_BPList ps = true at ht
  change dfree_BPList (((ps.map fun p => BT.trm [p]).take n).flatMap untrm) = true
  rw [flatMap_untrm_take_map_ch]
  exact dfree_BPList_take_ch ps n ht

private theorem dfree_BP_of_mem_ch {ps : List BP} {p : BP}
    (hps : dfree_BPList ps = true) (hp : p ∈ ps) : dfree_BP p = true := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
      simp only [dfree_BPList, Bool.and_eq_true] at hps
      rcases List.mem_cons.mp hp with hp | hp
      · rw [hp]; exact hps.1
      · exact ih hps.2 hp

private theorem PB_getD_mem_ch (t : BT) (j : ℕ) (ht : t ∈ T_B) :
    (PB t).getD j BZero ∈ T_B := by
  by_cases hj : j < (PB t).length
  · rw [getD_eq_getElem_idx (PB t) BZero hj]
    rcases t with ⟨ps⟩
    change dfree_BPList ps = true at ht
    simp only [PB, List.length_map] at hj
    simp only [PB, List.getElem_map]
    have hmem : ps[j] ∈ ps := List.getElem_mem hj
    have hdf : dfree_BP ps[j] = true := dfree_BP_of_mem_ch ht hmem
    simpa [T_B, dfree_BT, dfree_BPList] using hdf
  · have hget : (PB t).getD j BZero = BZero := by
      simp [List.getD_eq_getElem?_getD, hj]
    rw [hget]; exact bzero_mem_ch

private theorem bpHeadT_mem_ch (t : BT) (ht : t ∈ T_B) : bpHeadT t ∈ T_B := by
  rcases t with ⟨ps⟩
  cases ps with
  | nil => simpa [bpHeadT] using bzero_mem_ch
  | cons p ps =>
      rcases p with ⟨v, b⟩
      change dfree_BPList (.db v b :: ps) = true at ht
      simp only [dfree_BPList, dfree_BP, Bool.and_eq_true] at ht
      simpa [bpHeadT, T_B] using ht.1.2

/-! ## 1. 穴付き `c₂`：`s84d_c2hole` の入れ子成分 `t₃`, `t₄` と穴付き本体 -/

/-- `transC2Core` の入れ子分岐（`t₂ ≠ 0_B`）の `t₃`（`s84d_c2hole` の `t3` と同じ）。 -/
def c2hole_t3_ch (M : PS) : BT :=
  if bpHeadV ((PB (transT2 M)).getD ((PB (transT2 M)).length - 1) BZero)
      == (entry M 1 (lastParent M) : ℕ∞)
  then SigmaB ((PB (transT2 M)).take ((PB (transT2 M)).length - 1))
  else transT2 M

/-- `transC2Core` の入れ子分岐の `t₄`（`s84d_c2hole` の `t4` と同じ）。 -/
def c2hole_t4_ch (M : PS) : BT :=
  if bpHeadV ((PB (transT2 M)).getD ((PB (transT2 M)).length - 1) BZero)
      == (entry M 1 (lastParent M) : ℕ∞)
  then bpHeadT ((PB (transT2 M)).getD ((PB (transT2 M)).length - 1) BZero)
  else transT2 M

private theorem c2hole_t3_mem_ch (M : PS) (ht₂ : transT2 M ∈ T_B) :
    c2hole_t3_ch M ∈ T_B := by
  unfold c2hole_t3_ch; split
  · exact SigmaB_PB_take_mem_ch (transT2 M) ((PB (transT2 M)).length - 1) ht₂
  · exact ht₂

private theorem c2hole_t4_mem_ch (M : PS) (ht₂ : transT2 M ∈ T_B) :
    c2hole_t4_ch M ∈ T_B := by
  unfold c2hole_t4_ch; split
  · exact bpHeadT_mem_ch _ (PB_getD_mem_ch (transT2 M) ((PB (transT2 M)).length - 1) ht₂)
  · exact ht₂

/-- `transC2Core M (transV M) (transT2 M)`（＝ `transC2 M`）の最内右端 core
`D_{M₁,j₁} 0` をパラメータ `a` の `D_a 0` に差し替えたもの。分岐は `transC2Core`
と逐語一致（入れ子成分は `c2hole_t3_ch`/`c2hole_t4_ch`）。
`transC2 M = c2hole_ch M (entry M 1 (lastIdx M))`。 -/
def c2hole_ch (M : PS) (a : ℕ) : BT :=
  if transCondI M || transCondIII M || transCondV M then
    Dprin (transV M) (addBT (transT2 M) (Dprin (a : ℕ∞) BZero))
  else if transCondVI M then
    Dprin (transV M) (Dprin (a : ℕ∞) BZero)
  else if transT2 M == BZero then
    Dprin (transV M) (Dprin (entry M 1 (lastParent M) : ℕ∞) (Dprin (a : ℕ∞) BZero))
  else
    Dprin (transV M) (addBT (c2hole_t3_ch M) (Dprin (entry M 1 (lastParent M) : ℕ∞)
      (addBT (c2hole_t4_ch M) (Dprin (a : ℕ∞) BZero))))

/-- `s84d_c2hole_at_j1`: 穴を `a = M₁,j₁` に埋めると元の `transC2 M`。 -/
theorem c2hole_at_j1_ch (M : PS) :
    transC2 M = c2hole_ch M (entry M 1 (lastIdx M)) := rfl

/-! ## 2. scb combinator（`s84d_corepair_*`） -/

/-- 単一 principal `D_a 0` の自己 scb 分解。 -/
theorem scb_self_ch (a : ℕ) :
    scb_decomp (Dprin (a : ℕ∞) BZero) [] (flatBT (Dprin (a : ℕ∞) BZero)) [] := by
  refine ⟨by simp, ?_, by simp⟩
  intro _
  exact dprinStr_ch a

/-- `s84d_corepair_shared`: `t +_B D_a 0` の末尾 principal `D_a 0` を、**すべての
`a` について**同一の `(w, w')` で印付けする。 -/
theorem corepair_shared_ch (t : BT) (ht : t ∈ T_B) :
    ∃ w w' : List Sym, ∀ a : ℕ,
      scb_decomp (addBT t (Dprin (a : ℕ∞) BZero)) w
        (flatBT (Dprin (a : ℕ∞) BZero)) w' := by
  obtain ⟨w, w', d0⟩ :=
    add_scb_marked t (Dprin (0 : ℕ∞) BZero) ht (dprinNat_mem_ch 0) (dprinP_ch 0)
  refine ⟨w, w', fun a => ?_⟩
  exact add_scb_replace_last t (Dprin (0 : ℕ∞) BZero) (Dprin (a : ℕ∞) BZero) w w'
    ht (dprinNat_mem_ch 0) (dprinP_ch 0) (dprinNat_mem_ch a) (dprinP_ch a) d0

/-- `s84d_corepair_nested`: `t₃ +_B D_u (t₄ +_B D_a 0)` の最内 `D_a 0` を、
**すべての `a` について**同一の `(w, w')` で印付けする。 -/
theorem corepair_nested_ch (t₃ t₄ : BT) (u : ℕ)
    (ht₃ : t₃ ∈ T_B) (ht₄ : t₄ ∈ T_B) :
    ∃ w w' : List Sym, ∀ a : ℕ,
      scb_decomp (addBT t₃ (Dprin (u : ℕ∞) (addBT t₄ (Dprin (a : ℕ∞) BZero)))) w
        (flatBT (Dprin (a : ℕ∞) BZero)) w' := by
  obtain ⟨p4, q4, i4⟩ := corepair_shared_ch t₄ ht₄
  have cTB : ∀ a : ℕ, Dprin (u : ℕ∞) (addBT t₄ (Dprin (a : ℕ∞) BZero)) ∈ T_B :=
    fun a => Dprin_mem_T_B (by simp) (addBT_mem_T_B ht₄ (dprinNat_mem_ch a))
  have cP : ∀ a : ℕ, ∃ p, Dprin (u : ℕ∞) (addBT t₄ (Dprin (a : ℕ∞) BZero)) = BT.trm [p] :=
    fun _ => ⟨_, rfl⟩
  have li : ∀ a : ℕ,
      scb_decomp (Dprin (u : ℕ∞) (addBT t₄ (Dprin (a : ℕ∞) BZero)))
        (Sym.dsym (u : ℕ∞) :: p4) (flatBT (Dprin (a : ℕ∞) BZero)) q4 := by
    intro a
    exact scb_compose_dprin (u : ℕ∞) (addBT t₄ (Dprin (a : ℕ∞) BZero)) p4
      (flatBT (Dprin (a : ℕ∞) BZero)) q4 (i4 a) (dprinStr_ch a)
  obtain ⟨p3, q3, d30⟩ :=
    add_scb_marked t₃ (Dprin (u : ℕ∞) (addBT t₄ (Dprin (0 : ℕ∞) BZero)))
      ht₃ (cTB 0) (cP 0)
  refine ⟨p3 ++ (Sym.dsym (u : ℕ∞) :: p4), q4 ++ q3, fun a => ?_⟩
  have d3a := add_scb_replace_last t₃
    (Dprin (u : ℕ∞) (addBT t₄ (Dprin (0 : ℕ∞) BZero)))
    (Dprin (u : ℕ∞) (addBT t₄ (Dprin (a : ℕ∞) BZero))) p3 q3
    ht₃ (cTB 0) (cP 0) (cTB a) (cP a) d30
  exact scb_compose (addBT t₃ (Dprin (u : ℕ∞) (addBT t₄ (Dprin (a : ℕ∞) BZero))))
    (Dprin (u : ℕ∞) (addBT t₄ (Dprin (a : ℕ∞) BZero))) p3 (Sym.dsym (u : ℕ∞) :: p4)
    (flatBT (Dprin (a : ℕ∞) BZero)) q4 q3 (cP a) d3a (li a)

/-! ## 3. エンジン：`s84d_c2hole_scb` -/

/-- `s84d_c2hole_scb`: `c2hole_ch M a` の穴 `D_a 0` を、頭 `D_{transV M}` を露出した
まま**すべての `a` について**同一の `(w, w')` で印付けする。4 分岐で場合分けし、
各分岐は `s84d_corepair_*` / `scb_self_ch` ＋ 外側 `D_{transV M}` の `scb_compose_dprin`。 -/
theorem c2hole_scb_ch (M : PS) (hR : RTPS M) (hM : TPS M) (hmono : monoT M = true)
    (hj1 : 0 < transJ1 M) (ht1 : transT1 M ≠ BZero) :
    ∃ w w' : List Sym, ∀ a : ℕ,
      scb_decomp (c2hole_ch M a) (Sym.dsym (transV M) :: w)
        (flatBT (Dprin (a : ℕ∞) BZero)) w' := by
  obtain ⟨_hV, _hc₁eq, ht₂TB, _hjm1lt⟩ := c1_shape_holds M hR hM hmono hj1 ht1
  by_cases hA : (transCondI M || transCondIII M || transCondV M) = true
  · -- condI/III/V: 内側 = `t₂ +_B D_a 0`
    obtain ⟨w, w', W⟩ := corepair_shared_ch (transT2 M) ht₂TB
    refine ⟨w, w', fun a => ?_⟩
    have hform : c2hole_ch M a
        = Dprin (transV M) (addBT (transT2 M) (Dprin (a : ℕ∞) BZero)) := by
      simp [c2hole_ch, hA]
    rw [hform]
    exact scb_compose_dprin (transV M) (addBT (transT2 M) (Dprin (a : ℕ∞) BZero)) w
      (flatBT (Dprin (a : ℕ∞) BZero)) w' (W a) (dprinStr_ch a)
  · have hAf : (transCondI M || transCondIII M || transCondV M) = false := by
      simpa using hA
    by_cases hVI : transCondVI M = true
    · -- condVI: 内側 = `D_a 0`
      refine ⟨[], [], fun a => ?_⟩
      have hform : c2hole_ch M a = Dprin (transV M) (Dprin (a : ℕ∞) BZero) := by
        simp [c2hole_ch, hAf, hVI]
      rw [hform]
      exact scb_compose_dprin (transV M) (Dprin (a : ℕ∞) BZero) []
        (flatBT (Dprin (a : ℕ∞) BZero)) [] (scb_self_ch a) (dprinStr_ch a)
    · have hVIf : transCondVI M = false := by simpa using hVI
      by_cases hz : (transT2 M == BZero) = true
      · -- `t₂ = 0_B`: 内側 = `D_{u'} (D_a 0)`
        refine ⟨[Sym.dsym (entry M 1 (lastParent M) : ℕ∞)], [], fun a => ?_⟩
        have hform : c2hole_ch M a
            = Dprin (transV M) (Dprin (entry M 1 (lastParent M) : ℕ∞)
                (Dprin (a : ℕ∞) BZero)) := by
          simp [c2hole_ch, hAf, hVIf, hz]
        rw [hform]
        have inner := scb_compose_dprin (entry M 1 (lastParent M) : ℕ∞)
          (Dprin (a : ℕ∞) BZero) [] (flatBT (Dprin (a : ℕ∞) BZero)) []
          (scb_self_ch a) (dprinStr_ch a)
        exact scb_compose_dprin (transV M)
          (Dprin (entry M 1 (lastParent M) : ℕ∞) (Dprin (a : ℕ∞) BZero))
          [Sym.dsym (entry M 1 (lastParent M) : ℕ∞)] (flatBT (Dprin (a : ℕ∞) BZero)) []
          inner (dprinStr_ch a)
      · have hzf : (transT2 M == BZero) = false := by simpa using hz
        -- 入れ子: 内側 = `t₃ +_B D_{u'} (t₄ +_B D_a 0)`
        obtain ⟨w, w', W⟩ := corepair_nested_ch (c2hole_t3_ch M) (c2hole_t4_ch M)
          (entry M 1 (lastParent M)) (c2hole_t3_mem_ch M ht₂TB) (c2hole_t4_mem_ch M ht₂TB)
        refine ⟨w, w', fun a => ?_⟩
        have hform : c2hole_ch M a
            = Dprin (transV M) (addBT (c2hole_t3_ch M)
                (Dprin (entry M 1 (lastParent M) : ℕ∞)
                  (addBT (c2hole_t4_ch M) (Dprin (a : ℕ∞) BZero)))) := by
          simp [c2hole_ch, hAf, hVIf, hzf]
        rw [hform]
        exact scb_compose_dprin (transV M)
          (addBT (c2hole_t3_ch M) (Dprin (entry M 1 (lastParent M) : ℕ∞)
            (addBT (c2hole_t4_ch M) (Dprin (a : ℕ∞) BZero)))) w
          (flatBT (Dprin (a : ℕ∞) BZero)) w' (W a) (dprinStr_ch a)

/-! ## 4. 橋：エンジン → `Rightmost84ReplaceExists` -/

private theorem setup_sd_ch {N : PS} (hR : RTPS N) (hj1 : 1 < Lng N - 1) :
    transT1 N ≠ BZero := by
  have hlen : 1 < Lng N := by omega
  have hLP : Lng (Pred N) = Lng N - 1 := by
    simp [Pred, Nat.not_le.mpr hlen]
  have nzP : zeroT (Pred N) = false := by
    simp [zeroT, hLP]; omega
  have T1' : Trans (Pred N) ≠ BZero :=
    (Trans_Mark_invariant (Pred N) (RTPS_Pred N hR)).2.1 nzP
  simpa [transT1] using T1'

/-- **切片リードバック transport（残差）**。手術（Isabelle L4 part(2)(3)）により、
`Trans (s84x_Np M)` / `Trans (rrLp M)` は `c2hole_ch M (entry ...)` の scb 分解を
共有 `(s,b)` のまま継承する、という主張。エンジンが両穴を同一 `(s,b)` で印付ける
のを、実際の切片の `Trans` へ移送する部分。Isabelle では
`p_8_2_condV_terminal_slice_Trans`（pss_paper 1604、未証明）に依存。 -/
def C2HoleSliceTransport_ch : Prop :=
  ∀ M : PS, STPS M → monoT M = true → hasParent M 1 (Lng M - 1) = true →
    s84x_jm2 M + 1 < Lng M - 1 →
    ∀ s b : List Sym,
      scb_decomp (c2hole_ch M (entry M 1 (Lng M - 1))) s
          (flatBT (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)) b →
      scb_decomp (c2hole_ch M (entry M 1 (s84x_jm2 M))) s
          (flatBT (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero)) b →
      scb_decomp (Trans (s84x_Np M)) s
          (flatBT (Dprin (entry M 1 (Lng M - 1) : ℕ∞) BZero)) b ∧
      scb_decomp (Trans (rrLp M)) s
          (flatBT (Dprin (entry M 1 (s84x_jm2 M) : ℕ∞) BZero)) b

/-- **House pattern の還元**: 切片 transport が取れれば、エンジンの共有 `(w, w')` を
両穴 `a = M₁,j₁` / `a = M₁,j₋₂` に埋め、`Rightmost84ReplaceExists` を落とす。 -/
theorem rightmost84ReplaceExists_of_transport_ch
    (htr : C2HoleSliceTransport_ch) : Rightmost84ReplaceExists := by
  intro M hST hmono hp hrng
  have hMR : RTPS M := STPS_RTPS M hST
  have hMT : TPS M := RTPS_TPS M hMR
  have hj1' : 1 < Lng M - 1 := by omega
  have hJ1pos : 0 < transJ1 M := by simp only [transJ1, lastIdx]; omega
  have hT1 : transT1 M ≠ BZero := setup_sd_ch hMR hj1'
  obtain ⟨w, w', W⟩ := c2hole_scb_ch M hMR hMT hmono hJ1pos hT1
  have hA1 := W (entry M 1 (Lng M - 1))
  have hA2 := W (entry M 1 (s84x_jm2 M))
  refine ⟨(Sym.dsym (transV M) :: w, w'), ?_⟩
  exact htr M hST hmono hp hrng (Sym.dsym (transV M) :: w) w' hA1 hA2

/-- 訂正 A30 形 `Rightmost84ReplaceCorrected` への合成。 -/
theorem rightmost84ReplaceCorrected_of_transport_ch
    (htr : C2HoleSliceTransport_ch) : Rightmost84ReplaceCorrected :=
  rightmost84ReplaceCorrected_of_exists (rightmost84ReplaceExists_of_transport_ch htr)

#print axioms c2hole_at_j1_ch
#print axioms scb_self_ch
#print axioms corepair_shared_ch
#print axioms corepair_nested_ch
#print axioms c2hole_scb_ch
#print axioms rightmost84ReplaceExists_of_transport_ch
#print axioms rightmost84ReplaceCorrected_of_transport_ch

end PSS
