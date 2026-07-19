import «8».«8.7-otmulti-narrow»
import «8».«8.7-fseq-descend-props2»
import «8».«8.3-condII-Boundary-close»
import «8».«8.2-condIIIV-close»

/-!
# §8.7 OT 柱 — `OTmulti_interior_condII_on` を無条件で閉じる（Isabelle blueprint）

- 原文: `tmp/content.md` 6122（§8.7）。露出 `Prop` `OTmulti_interior_condII_on`
  （`«8».«8.7-otmulti-narrow»`:137）＝ 複項 host の末尾 mono 成分 `L` が**条件 (II)**
  （`entry L 1 lastIdx = 0` かつ `¬ adm L lastParent`）のとき、基本列翻訳
  `Trans (oper L m)` が `OT_B` に留まり（内部 OT ステップ、Isabelle `OTint`）かつ
  `Trans L` 以下である（降下柱の弱化、Isabelle `ordIntC`）という**両立ち**の主張。
  訂正: なし。
- 状態: 🤖 GREEN（sorry 0、axioms = propext/Classical.choice/Quot.sound）。
  `8.7-otmulti-narrow` の `otMultiIntCond_of_condII_on` は、条件 (III)/(IV)/(V) を
  既存の無条件供給から落とし、**条件 (II) だけ**をこの `Prop` に残した。本ファイルは
  その残った条件 (II) を無条件で閉じ、`8.7-termination` の最後の残差フィールド
  `otMultiIntCond : OTmulti_interior_intCond_nc1` を無条件化する橋になる。

## 証明の骨格（Isabelle `opx_OTmulti` の条件 (II) 脚 = `pss_wip.thy`:115556）

Isabelle は条件 (II) を `TVall`（`CondII_masterCF` の値連鎖）経由の交換脚で捌く。
Lean ではその連鎖が既に**無条件**になっている:

* `CondII_masterCF` は無条件（`condII_masterCF_of_condIIIV condIIIVterminalSlice_holds`、
  `«8».«8.3-condII-Boundary-close»` ＋ `«8».«8.2-condIIIV-close»`）。
* `FseqDesc_exchII_of_CondII`（`«8».«8.7-fseq-descend-props2»`:101）が
  `CondII_masterCF` から交換**等式** `∃ k, Trans (oper L m) = operB (Trans L) (numBT k)`
  を与える（`{STPS, monoT, 1 < Lng L - 1, transCondII, 1 < m}` の下）。

等式が取れれば両 conjunct は落ちる:

* **順序**: `buchholz_fseq_lt (Trans L) k`（[Buc1] Lemma 3.2(a)）で
  `operB (Trans L) (numBT k) <_B Trans L`、`lessBT → leBT`。前提 `Trans L ≠ 0_B` は
  mono ゆえ非零項（`Trans_preserves_zeroT`）から。
* **OT 所属**: `OT_B` は基本列演算 `operB · (numBT k)` で閉じている
  （`OT_B_operB_numBT_bp` ＝ Isabelle `e4x_OT_B_operB_numBT`、零脚は `operB 0_B z = 0_B`
  で埋めて `buchholz_fseq_closed` を無条件化）。

## 唯一の実務 = `Lng L = 2` の隅（guard gap）

`FseqDesc_exchII` は `1 < Lng L - 1`（`Lng L ≥ 3`）を要求するが、この `Prop` の仮定は
`1 < Lng L` のみ。差 `Lng L = 2` の隅は**空虚**（数値監査 `trans_model.py` で
`Lng = 2` に条件 (II) host が 0 件と確認済み）。空虚性の証明:

* `Lng L = 2` なら `lastIdx L = 1`、`lastParent L = parent L 0 1 = 0`
  （行 0 で添字 1 の親候補は 0 しかない＝`parent_row0_one_zero_bp`）。
* 条件 (II) は `¬ adm L (lastParent L)`、すなわち `adm L 0 = false`。
* しかし `adm L 0 = true` は無条件（`adm_zero`、添字 0 は常に許容）。矛盾。

よって `1 < Lng L - 1` が従い、上の等式路が開通する。**空虚性に依存して結論を
飛ばすのではなく**、隅を仮定から矛盾で潰して `1 < Lng L - 1` を得ている
（監査留保 2「STPS 上に条件 (II) の instance が無いかもしれない」への非依存）。

- 依存（ビルド済みのみ import）: `«8».«8.7-otmulti-narrow»`
  （`OTmulti_interior_condII_on` の def、透過的に `adm_zero` / `parent`/`nextR`/
  `transCondII` / `buchholz_fseq_lt` / `STPS_RTPS` / `RTPS_TPS` /
  `Trans_preserves_zeroT` / `buchholz_fseq_closed`）、
  `«8».«8.7-fseq-descend-props2»`（`FseqDesc_exchII_of_CondII`）、
  `«8».«8.3-condII-Boundary-close»`（`condII_masterCF_of_condIIIV`）、
  `«8».«8.2-condIIIV-close»`（`condIIIVterminalSlice_holds`）。
- private helper suffix: `_bp`。
-/

namespace PSS

/-! ## 1. `OT_B` の基本列閉包（`«8».«8.7-otmulti-notcondI»` の private 版を再掲） -/

/-- `0_B ∈ OT_B`。 -/
private theorem BZero_OT_B_bp : BZero ∈ OT_B := by
  simp [OT_B, OT, T_B, BZero, isOT_BT, isOT_BPList, descP, dfree_BT, dfree_BPList]

/-- `operB 0_B z = 0_B`（Isabelle `b1x_operB_zero`）。 -/
private theorem operB_BZero_bp (z : BT) : operB BZero z = BZero := by
  simp [operB, BZero, bOperCore]

/-- Isabelle `e4x_OT_B_operB_numBT`（`layerB/pss_wip.thy`:61390）: 零脚を
`operB_BZero_bp` で埋めて `buchholz_fseq_closed` を無条件化。 -/
private theorem OT_B_operB_numBT_bp {a : BT} (ha : a ∈ OT_B) (n : ℕ) :
    operB a (numBT n) ∈ OT_B := by
  by_cases hz : a = BZero
  · rw [hz, operB_BZero_bp]; exact BZero_OT_B_bp
  · exact buchholz_fseq_closed a n ha hz

/-! ## 2. 順序連結の小補題 -/

/-- `lessBT` から `leBT`（`«8».«8.7-otmulti-narrow»` の `leBT_of_lessBT_on` と同型）。 -/
private theorem leBT_of_lessBT_bp {a b : BT} (h : lessBT a b = true) : leBT a b = true := by
  simp [leBT, h]

/-! ## 3. `Lng L = 2` の隅を潰す小補題 -/

/-- 行 0 で添字 1 の親は 0（親候補は 0 しかない、`hasParent` 不要の無条件版）。
`parent_one_zero_fd`（`hasParent` を要求）の弱前提版。 -/
private theorem parent_row0_one_zero_bp (M : PS) : parent M 0 1 = 0 := by
  unfold parent
  cases h : parents M 0 1 with
  | nil => rfl
  | cons a as =>
      have hmem : a ∈ parents M 0 1 := by rw [h]; exact List.mem_cons_self
      have hnext : nextR M 0 a 1 = true := by
        have h2 : a ∈ (List.range (Lng M)).filter (fun j0 => nextR M 0 j0 1) := by
          rwa [parents] at hmem
        exact (List.mem_filter.mp h2).2
      have ha : a < 1 := by
        rw [nextR, if_pos rfl] at hnext
        simp only [nextrel0, Bool.and_eq_true, decide_eq_true_eq] at hnext
        exact hnext.1.1.2
      have hd : List.headD (a :: as) 0 = a := rfl
      rw [hd]; omega

/-! ## 4. 主結果 — 条件 (II) を無条件で閉じる -/

/-- **`OTmulti_interior_condII_on` を無条件で閉じる**（ROUTE B, Isabelle blueprint）。
`CondII_masterCF` の無条件化 → `FseqDesc_exchII` の交換等式 → 順序は
[Buc1] Lemma 3.2(a)、OT 所属は `OT_B` の `operB · (numBT k)` 閉包。guard gap
`Lng L = 2` は条件 (II) と `adm_zero` の矛盾で空虚化して `1 < Lng L - 1` を得る。 -/
theorem otMultiInteriorCondII_bp : OTmulti_interior_condII_on := by
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
  -- guard gap: `Lng L = 2` の隅は条件 (II) と `adm_zero` の矛盾で空虚
  have hj1gt : 1 < Lng L - 1 := by
    by_contra hcon
    have hL2 : Lng L = 2 := by omega
    have hpar : lastParent L = 0 := by
      unfold lastParent lastIdx
      rw [hL2]; exact parent_row0_one_zero_bp L
    have hc := hcond
    simp only [transCondII, Bool.and_eq_true] at hc
    have h2 : (!adm L (lastParent L)) = true := hc.2
    rw [hpar, adm_zero L] at h2
    simp at h2
  -- `CondII_masterCF` 無条件化 → 交換等式
  have hCF : CondII_masterCF := condII_masterCF_of_condIIIV condIIIVterminalSlice_holds
  have hexch : FseqDesc_exchII := FseqDesc_exchII_of_CondII hCF
  obtain ⟨k, hke⟩ := hexch L m hLST hLmono hj1gt hcond hm
  refine ⟨?_, ?_⟩
  · -- OT 所属: `OT_B` は `operB · (numBT k)` で閉じている
    rw [hke]; exact OT_B_operB_numBT_bp hTL k
  · -- 順序: [Buc1] Lemma 3.2(a) → `lessBT → leBT`
    rw [hke]
    exact leBT_of_lessBT_bp (buchholz_fseq_lt (Trans L) k hTL hTne)

#print axioms otMultiInteriorCondII_bp

end PSS
