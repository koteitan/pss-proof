import «8».«8.7-otmulti-notcondI»
import «8».«8.7-otdisp-OTint»
import «8».«8.7-fseq-descend»

/-!
# §8.7 OT 柱 — `OTmulti_interior_intCond_nc1` を条件 (II) だけに絞る

- 原文: `tmp/content.md` 6122（§8.7）。露出 `Prop` `OTmulti_interior_intCond_nc1`
  （`«8».«8.7-otmulti-notcondI»`:192）＝ 複項 host の末尾 mono 成分 `L` が条件
  (II)/(III)/(IV)/(V) のとき、基本列翻訳 `Trans (oper L m)` が `OT_B` に留まり
  （内部 OT ステップ、Isabelle `OTint`）かつ `Trans L` 以下（降下柱の弱化、Isabelle
  `ordIntC`）である、という**両立ち**の主張。訂正: なし。
- 状態: 🤖 GREEN（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  本ファイルは `OTmulti_interior_intCond_nc1` を、条件 (III)/(IV)/(V) を既存の
  無条件／別残差供給から閉じ、**条件 (II) だけ**を要求する narrower Prop
  `OTmulti_interior_condII_on` に還元する（`otMultiIntCond_of_condII_on`）。

## なぜ条件 (III)/(IV)/(V) は落ちるか（`OTdisp_OTint` の観察）

`OTmulti_interior_intCond_nc1` の結論は「OT 所属」＋「順序 `leBT`」の連言だが、
**両者を別々に供給できる**:

* **OT 所属**（`Trans (oper L m) ∈ OT_B`）: 露出 `Prop` `OTdisp_OTint`
  （`«8».«8.7-Trans-preserves-OT»`:95）が条件 (III)/(IV)/(V) 込みで**そのまま**与える
  （`8.7-termination` では `otInt_term` が slicepkg＋transport 残差＋条件 (V) 塔から
  `OTdisp_OTint` を無条件供給しており、`otMultiIntCond` フィールドには依存しない）。
  ただし `OTdisp_OTint` は `1 < Lng L - 1` を要求する。
* **順序**（`leBT (Trans (oper L m)) (Trans L)`）: 降下柱の交換脚
  `FseqDesc_exchIII`/`_exchIV`/`_exchV`（`«8».«8.7-fseq-descend»`）が
  `∃ k, leBT (Trans (oper L m)) (operB (Trans L) (numBT k))` を与え、
  [Buc1] Lemma 3.2(a)（`buchholz_fseq_lt`: `operB (Trans L) (numBT k) <_B Trans L`）と
  連結して `lessBT (Trans (oper L m)) (Trans L)`、よって `leBT`。これらも
  `otMultiIntCond` には依存しない（`exch84producer` / 条件 (V) 塔から供給）。

`OTdisp_OTint` は「OT 所属」しか出さないので **`OTmulti_interior_intCond_nc1` の
obligation を直接には満たさない**（順序脚が要る）。上の 2 供給を合流させて閉じる。

## `1 < Lng L - 1` の隅（`Lng L = 2`）は空虚

`OTdisp_OTint` と交換脚は `1 < Lng L - 1` を課すが、`OTmulti_interior_intCond_nc1`
の仮定は `1 < Lng L` のみ。しかし条件 (III)/(IV)/(V) ＋ `oper L m ≠ Pred L` の下では
`Lng L = 2` は起こらない（降下柱ディスパッチャ `p_8_7_fseq_descend` の condIII/IV/V
枝と同じ論法）:

* 条件 (V): `lastParent + 1 < lastIdx = 1` は不成立（`lastParent + 1 < 1` は偽）。
* 条件 (III)/(IV): `oper L m ≠ Pred L`（＋末尾非零）から `hasParent L 1 1`＝行 1 の親
  `entry L 1 0 < entry L 1 1`。一方 (III)/(IV) は `entry L 1 1 ≤ entry L 1 (lastParent)`
  で、`Lng L = 2` では `lastParent = parent L 0 1 = 0`（`parent_one_zero_fd`）ゆえ
  `entry L 1 1 ≤ entry L 1 0`。両者は矛盾。

## 条件 (II) だけに残る narrower Prop

`OTmulti_interior_condII_on`: 末尾 mono 成分 `L` が**条件 (II)**（`entry L 1 lastIdx = 0`
かつ `¬ adm L (lastParent L)`）のとき `Trans (oper L m) ∈ OT_B ∧ leBT ..`。これは
`8.7-termination` の `condIIIVts`（`CondIIIVterminalSlice`）／condII masterCF に相当し、
無条件には閉じない（本ファイルの scope 外）。

- 依存（ビルド済みのみ import）: `«8».«8.7-otmulti-notcondI»`
  （`OTmulti_interior_intCond_nc1` の def）、`«8».«8.7-otdisp-OTint»`
  （`OTdisp_OTint` の def、透過的に `OT_B`/`Trans`）、`«8».«8.7-fseq-descend»`
  （`FseqDesc_exchIII`/`_exchIV`/`_exchV`・`parent_one_zero_fd`、透過的に
  `buchholz_fseq_lt`・`lessBT_linear_trans`・`Trans_preserves_zeroT`・
  `mono_hasParent_row0`）。
- private helper suffix: `_on`。
-/

namespace PSS

/-! ## 1. 小補題（`«8».«8.7-fseq-descend»` の private helper の再導出＋順序連結） -/

/-- `lessBT` から `leBT`。 -/
private theorem leBT_of_lessBT_on {a b : BT} (h : lessBT a b = true) : leBT a b = true := by
  simp [leBT, h]

/-- `leBT` と `lessBT` の連結（`«8».«8.7-fseq-descend»` の `leBT_lessBT_trans_fd` と同型）。 -/
private theorem leBT_lessBT_trans_on {a b c : BT} (hab : leBT a b = true)
    (hbc : lessBT b c = true) : lessBT a c = true := by
  simp only [leBT, Bool.or_eq_true, beq_iff_eq] at hab
  rcases hab with hab | rfl
  · exact lessBT_linear_trans a b c hab hbc
  · exact hbc

/-- 親が唯一なら `parent` は実際に親辺を張る（`hasParent_nextR_fd` の再導出）。 -/
private theorem hasParent_nextR_on (M : PS) (i j₁ : ℕ)
    (hp : hasParent M i j₁ = true) : nextR M i (parent M i j₁) j₁ = true := by
  have hmem : parent M i j₁ ∈ parents M i j₁ := by
    unfold parent
    cases h : parents M i j₁ with
    | nil => rw [hasParent, h] at hp; simp at hp
    | cons a as => simp [List.headD]
  have hmem' : parent M i j₁ < Lng M ∧ nextR M i (parent M i j₁) j₁ = true := by
    simpa [parents, List.mem_filter] using hmem
  exact hmem'.2

/-- 親が唯一なら親辺は `0 <^Next 1`（`parent_one_nextR_fd` の再導出）。 -/
private theorem parent_one_nextR_on (M : PS) (i : ℕ)
    (hp : hasParent M i 1 = true) : nextR M i 0 1 = true := by
  have h := hasParent_nextR_on M i 1 hp
  rwa [parent_one_zero_fd M i hp] at h

/-- 行 1 の親辺 `0 <^Next 1` は `M_{1,0} < M_{1,1}`（`nextR_row1_lt_fd` の再導出）。 -/
private theorem nextR_row1_lt_on (M : PS) (h : nextR M 1 0 1 = true) :
    entry M 1 0 < entry M 1 1 := by
  rw [nextR, if_neg (by omega)] at h
  simp only [nextrel1, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.2

/-- 条件 (III)/(IV)/(V) はいずれも `0 < L_{1,j₁}`（`cond345_entry1_pos_oi` の再導出）。 -/
private theorem cond345_entry1_pos_on {L : PS}
    (hc : transCondIII L = true ∨ transCondIV L = true ∨ transCondV L = true) :
    0 < entry L 1 (Lng L - 1) := by
  rcases hc with h | h | h
  · simp [transCondIII, lastIdx] at h; omega
  · simp [transCondIV, lastIdx] at h; omega
  · simp [transCondV, lastIdx] at h; omega

/-- `oper L m ≠ Pred L`（末尾非全零・`1 < Lng L`）なら親を持つ
（`hasParent_of_oper_ne_Pred_nc1` の再導出）。 -/
private theorem hasParent_of_oper_ne_Pred_on (L : PS) (m : ℕ) (hLgt : 1 < Lng L)
    (hz : ¬(entry L 0 (Lng L - 1) = 0 ∧ entry L 1 (Lng L - 1) = 0))
    (hpred : oper L m ≠ Pred L) :
    hasParent L (idx1 L (Lng L - 1)) (Lng L - 1) = true := by
  by_contra hnp
  apply hpred
  have hj1ne : Lng L - 1 ≠ 0 := by omega
  have hnpF : hasParent L (idx1 L (Lng L - 1)) (Lng L - 1) = false := by
    cases h : hasParent L (idx1 L (Lng L - 1)) (Lng L - 1) with
    | true => exact absurd h hnp
    | false => rfl
  simp [oper, hj1ne, hz, hnpF]

/-! ## 2. 露出する narrower Prop（条件 (II) だけ） -/

/-- **`OTmulti_interior_intCond_nc1` の条件 (II) 部分**。末尾 mono 成分 `L` が条件 (II)
のとき、基本列翻訳が `OT_B` に留まり（内部 OT ステップ）かつ `Trans L` 以下である
（降下柱の弱化）。`8.7-termination` の `condIIIVts` / condII masterCF に相当。 -/
def OTmulti_interior_condII_on : Prop :=
  ∀ (L : PS) (m : ℕ), STPS L → monoT L = true → 1 < Lng L → 1 < m →
    oper L m ≠ Pred L → Trans L ∈ OT_B →
    transCondII L = true →
    Trans (oper L m) ∈ OT_B ∧ leBT (Trans (oper L m)) (Trans L) = true

/-! ## 3. 主結果 — 条件 (III)/(IV)/(V) を落として条件 (II) だけに絞る -/

/-- **`OTmulti_interior_intCond_nc1` を条件 (II) だけの narrower Prop に還元する**。
条件 (III)/(IV)/(V) は、OT 所属を `OTdisp_OTint` から、順序を降下柱の交換脚
`FseqDesc_exchIII`/`_exchIV`/`_exchV`＋[Buc1] Lemma 3.2(a) から供給して閉じる。
`hOTint` / `hIII` / `hIV` / `hV` はいずれも `otMultiIntCond` に依存せずに供給できる
（`8.7-termination` の `otInt_term` / `exch84producer` / 条件 (V) 塔）。 -/
theorem otMultiIntCond_of_condII_on
    (hOTint : OTdisp_OTint)
    (hIII : FseqDesc_exchIII) (hIV : FseqDesc_exchIV) (hV : FseqDesc_exchV)
    (hII : OTmulti_interior_condII_on) :
    OTmulti_interior_intCond_nc1 := by
  intro L m hLST hLmono hLgt hm hLpred hTL hcond
  have hLR : RTPS L := STPS_RTPS L hLST
  have hLT : TPS L := RTPS_TPS L hLR
  -- `Trans L ≠ 0_B`（mono ゆえ非零項、[Buc1] Lemma 3.2(a) の前提）
  have hnotzT : zeroT L = false := by
    simp only [zeroT, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    exact Or.inl (by omega)
  have hTne : Trans L ≠ BZero := by
    intro h
    have hz := (Trans_preserves_zeroT L hLT).2 h
    rw [hnotzT] at hz
    exact Bool.noConfusion hz
  rcases hcond with cII | cIII | cIV | cV
  · -- 条件 (II): narrower Prop に委譲
    exact hII L m hLST hLmono hLgt hm hLpred hTL cII
  · -- 条件 (III)
    have hpos : 0 < entry L 1 (Lng L - 1) := cond345_entry1_pos_on (Or.inl cIII)
    have hz : ¬(entry L 0 (Lng L - 1) = 0 ∧ entry L 1 (Lng L - 1) = 0) := by
      rintro ⟨_, h2⟩; omega
    have hp : hasParent L (idx1 L (Lng L - 1)) (Lng L - 1) = true :=
      hasParent_of_oper_ne_Pred_on L m hLgt hz hLpred
    have hp0 : hasParent L 0 (Lng L - 1) = true :=
      mono_hasParent_row0 L hLT hLmono (Lng L - 1) (by omega) (by omega)
    have hj1gt : 1 < Lng L - 1 := by
      by_contra hcon
      have hj1one : Lng L - 1 = 1 := by omega
      simp only [transCondIII, Bool.and_eq_true, decide_eq_true_eq, lastIdx,
        lastParent, hj1one] at cIII
      have he1pos : 0 < entry L 1 1 := cIII.1.1
      have hge : entry L 1 1 ≤ entry L 1 (parent L 0 1) := cIII.1.2
      have hi1 : idx1 L 1 = 1 := by simp only [idx1, if_pos he1pos]
      have hp1 : hasParent L 1 1 = true := by rw [hj1one, hi1] at hp; exact hp
      have hlt := nextR_row1_lt_on L (parent_one_nextR_on L 1 hp1)
      have hp0' : hasParent L 0 1 = true := by rw [hj1one] at hp0; exact hp0
      rw [parent_one_zero_fd L 0 hp0'] at hge
      omega
    refine ⟨hOTint L m hLST hLmono hj1gt (Or.inl cIII) hTL hm, ?_⟩
    obtain ⟨k, hke⟩ := hIII L m hLST hLmono hj1gt cIII hm
    exact leBT_of_lessBT_on
      (leBT_lessBT_trans_on hke (buchholz_fseq_lt (Trans L) k hTL hTne))
  · -- 条件 (IV)
    have hpos : 0 < entry L 1 (Lng L - 1) := cond345_entry1_pos_on (Or.inr (Or.inl cIV))
    have hz : ¬(entry L 0 (Lng L - 1) = 0 ∧ entry L 1 (Lng L - 1) = 0) := by
      rintro ⟨_, h2⟩; omega
    have hp : hasParent L (idx1 L (Lng L - 1)) (Lng L - 1) = true :=
      hasParent_of_oper_ne_Pred_on L m hLgt hz hLpred
    have hp0 : hasParent L 0 (Lng L - 1) = true :=
      mono_hasParent_row0 L hLT hLmono (Lng L - 1) (by omega) (by omega)
    have hj1gt : 1 < Lng L - 1 := by
      by_contra hcon
      have hj1one : Lng L - 1 = 1 := by omega
      simp only [transCondIV, Bool.and_eq_true, decide_eq_true_eq, lastIdx,
        lastParent, hj1one] at cIV
      have he1pos : 0 < entry L 1 1 := cIV.1.1
      have hge : entry L 1 1 ≤ entry L 1 (parent L 0 1) := cIV.1.2
      have hi1 : idx1 L 1 = 1 := by simp only [idx1, if_pos he1pos]
      have hp1 : hasParent L 1 1 = true := by rw [hj1one, hi1] at hp; exact hp
      have hlt := nextR_row1_lt_on L (parent_one_nextR_on L 1 hp1)
      have hp0' : hasParent L 0 1 = true := by rw [hj1one] at hp0; exact hp0
      rw [parent_one_zero_fd L 0 hp0'] at hge
      omega
    refine ⟨hOTint L m hLST hLmono hj1gt (Or.inr (Or.inl cIV)) hTL hm, ?_⟩
    obtain ⟨k, hke⟩ := hIV L m hLST hLmono hj1gt cIV hm
    exact leBT_of_lessBT_on
      (leBT_lessBT_trans_on hke (buchholz_fseq_lt (Trans L) k hTL hTne))
  · -- 条件 (V)
    have hj1gt : 1 < Lng L - 1 := by
      simp only [transCondV, Bool.and_eq_true, decide_eq_true_eq, lastIdx,
        lastParent] at cV
      omega
    refine ⟨hOTint L m hLST hLmono hj1gt (Or.inr (Or.inr cV)) hTL hm, ?_⟩
    obtain ⟨k, hke⟩ := hV L m hLST hLmono hj1gt cV hm
    exact leBT_of_lessBT_on
      (leBT_lessBT_trans_on hke (buchholz_fseq_lt (Trans L) k hTL hTne))

#print axioms otMultiIntCond_of_condII_on

end PSS
