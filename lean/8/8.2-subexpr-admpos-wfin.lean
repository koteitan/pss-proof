import «8».«8.2-subexpr-admpos-engine»
import «8».«8.2-subexpr-adm0-full»
import «7».«7.3-Trans-welldefined»
import «7».«7.4-RightAnces-RightNodes»

/-!
# §8.2 `Admpos` body-split の w-同定（有限頭 ＋ `RightNodes` 位置）

`8.2-subexpr-adm0-full` が green-modulo で仮定に取っている名前付き Prop
`TransAdmposBodySplitWfin` の本体。`8.2-subexpr-admpos-engine` の
`trans_admpos_body_split`（Isabelle 26573 の Lean 版、STEP 1）が出す共通末尾
principal の頭 `w : ℕ∞` を、
1. **有限**（`Trans M` は d-free なので `w ≠ ⊤`）、
2. **位置同定** `w = RightNodes (Trans M)₁`、
3. さらに `RightNodes (Trans M)₁ = RightAnces M₁`（§7.4）
の 3 点で書き換える。

- 原文: `tmp/content.md` §8.2 補題（`j₁ - TrMax(M)` 帰納法が使う
  「`RightNodes (Trans M)` の第 2 成分の同定」）の橋渡し部。
- Isabelle 対応（`isabelle/layerB/pss_wip.thy`）:
  - `trans_admpos_body_split_wfin` ← 同名 (26699、~26783 まで)
    - 下請け `trans_admpos_body_split` (26573) は Lean 移植済
      （`«8».«8.2-subexpr-admpos-engine»` の同名公開定理）。
    - Isabelle の `let w' = RightNodes (Trans M) ! 1 in …` は、Lean 側では
      `TransAdmposBodySplitWfin`（`8.2-subexpr-adm0-full`）の本体に合わせて
      `let` を展開した形（`(… : ℕ) : ℕ∞` のキャスト）で書く。
    - Isabelle の `w \<noteq> \<infinity>` は `flatBT` 上に `Dsym w` が現れることを
      示して `dfree_flat_BT` に渡す 30 行の議論だが、Lean には `dfree_flat_BT`
      に相当する補題が未移植なので、**構造的**に取る:
      `dfree_BT (Trans M)` → `dfree_BPList (ps ++ [.db w u3])`
      → `dfree_BP (.db w u3)` → `w ≠ ⊤`（private `dfree_*_wf` 3 本）。
      Isabelle の平坦化経由より短く、同じ結論。
- 依存（すべて built 済）:
  - `8.2-subexpr-admpos-engine`: `ScbOuterSurgerySplit` / `trans_admpos_body_split`。
  - `8.2-subexpr-adm0-full`: `TransAdmposBodySplitWfin`（本ファイルの結論の型）。
  - `7.3-Trans-welldefined`: `Trans_mem_T_B`（`Trans M ∈ T_B` = d-free）。
  - `7.4-RightAnces-RightNodes`: `RightNodes_addBT_Dprin`（simp）/
    `m_7_4_RightAnces_RightNodes`。
- 状態: ✅ sorry 0（本ファイル単独で green）。ただし engine 由来の
  **green-modulo 1 本** `ScbOuterSurgerySplit`（Isabelle
  `scb_outer_surgery_split` 26412、並列 agent が移植中）を仮定に取る。
  この仮定が放電されれば、`8.2-subexpr-adm0-full` の
  `TransAdmposBodySplitWfin` 仮定も同時に落ちる（drop-in）。
-/

namespace PSS

/-! ## d-free の分解（Isabelle の `dfree_flat_BT` 経路の構造版） -/

/-- `dfree_BPList` は連接で分配する。 -/
private theorem dfree_BPList_append_wf (as bs : List BP) :
    dfree_BPList (as ++ bs) = (dfree_BPList as && dfree_BPList bs) := by
  induction as with
  | nil => simp [dfree_BPList]
  | cons a as ih => simp [dfree_BPList, ih, Bool.and_assoc]

/-- 末尾に足した principal `D_w u` の頭は、全体が d-free なら有限。 -/
private theorem dfree_addBT_Dprin_head_wf (pre : BT) (w : ℕ∞) (u : BT)
    (h : dfree_BT (addBT pre (Dprin w u)) = true) : w ≠ ⊤ := by
  rcases pre with ⟨ps⟩
  rw [Dprin, addBT, dfree_BT, dfree_BPList_append_wf] at h
  have h2 : dfree_BPList [BP.db w u] = true := (Bool.and_eq_true _ _ |>.mp h).2
  rw [dfree_BPList, dfree_BP] at h2
  have h3 := (Bool.and_eq_true _ _ |>.mp h2).1
  have h4 := (Bool.and_eq_true _ _ |>.mp h3).1
  simpa using h4

/-- `Trans M = D_{e} (pre +_B D_w u)`（`M ∈ RT_PS`）なら `w` は有限。 -/
private theorem trans_split_head_fin_wf (M : PS) (hR : RTPS M)
    (e w : ℕ∞) (pre u : BT)
    (hT : Trans M = Dprin e (addBT pre (Dprin w u))) : w ≠ ⊤ := by
  have hdf : dfree_BT (Trans M) = true := Trans_mem_T_B M hR
  rw [hT, Dprin, dfree_BT, dfree_BPList, dfree_BP] at hdf
  have hbody : dfree_BT (addBT pre (Dprin w u)) = true := by
    have h1 := (Bool.and_eq_true _ _ |>.mp hdf).1
    exact (Bool.and_eq_true _ _ |>.mp h1).2
  exact dfree_addBT_Dprin_head_wf pre w u hbody

/-! ## STEP 2 bridge（Isabelle `trans_admpos_body_split_wfin`, layerB 26699）

`trans_admpos_body_split` の結論の頭 `w : ℕ∞` を、有限な
`w' = RightNodes (Trans M)₁ : ℕ` で書き換える。`w` が末尾 principal の頭である
ことから `RightNodes`（末尾 principal を辿る）の添字 1 でちょうど `w.toNat` が
読めるので（simp 補題 `RightNodes_addBT_Dprin`）、位置同定は計算で済む。
最後の等式は §7.4 の `RightAnces M = RightNodes (Trans M)`。 -/

theorem trans_admpos_body_split_wfin (hsplit : ScbOuterSurgerySplit) :
    TransAdmposBodySplitWfin := by
  intro M hR hmono hj1gt hAdmpos ht1ne
  -- STEP 1: 共通接頭辞 `pre` と共通末尾 principal 頭 `w`
  obtain ⟨pre, w, u2, u3, hsp1, hsp2⟩ :=
    trans_admpos_body_split hsplit M hR hmono hj1gt hAdmpos ht1ne
  -- 位置同定: `RightNodes (Trans M)₁ = w.toNat`
  have hrn : (RightNodes (Trans M)).getD 1 0 = w.toNat := by
    rw [hsp2]; simp
  -- 有限性: `Trans M` は d-free なので `w ≠ ⊤`
  have hwfin : w ≠ ⊤ := trans_split_head_fin_wf M hR _ w pre u3 hsp2
  -- `w` を有限頭 `w'` の埋め込みとして書き換える
  have hweq : (((RightNodes (Trans M)).getD 1 0 : ℕ) : ℕ∞) = w := by
    rw [hrn]; exact ENat.coe_toNat hwfin
  refine ⟨pre, u2, u3, ?_, ?_, ?_⟩
  · rw [hweq]; exact hsp1
  · rw [hweq]; exact hsp2
  · rw [m_7_4_RightAnces_RightNodes M hR]

/-! ## 公理監査 -/

#print axioms trans_admpos_body_split_wfin

end PSS
