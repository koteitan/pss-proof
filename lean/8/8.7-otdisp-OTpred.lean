import «Buchholz-rel-ord».«Buchholz-rel-ord-6»
import «Buchholz-1986».«Buchholz-1986-2.1-order»

/-!
# §8.7 `OTdisp_OTpred` へ向けた Brick A — 右スパイン un-insertion の `OT` 代数

- Isabelle（設計図）: `isabelle/layerC/pss_scratch.thy` の `r54-od4` 節
  （:25–464、prefix `od4_`）。本ファイルが移植したのは **Brick A**
  （:25–404）＝ `od4_R` の定義と「`od4_R` は `isOT` を逆向きに保つ」:
  * `od4_R`（:37 inductive）→ `od4R_op`
  * `od4_sz`/`od4_szP`（:50 fun）→ `od4sz_op`/`od4szP_op`/`od4szList_op`
  * `od4_GBT_sz`（:72）→ `od4R_GBT_sz`
  * `od4_R_lessBT`（:98）→ `od4R_lessBT`
  * `od4_peel_less`（:121）→ `od4_peel_less_op`
  * `od4_transfer_all`/`od4_transfer`（:155/:241）→ `od4R_transfer`
  * `od4_R_GBT`（:248）→ `od4R_GBT_op`
  * `od4_descP_snoc`（:307）→ `od4_descP_snoc_op`
  * `od4_site_G`（:327）→ `od4_site_G_op`
  * `od4_R_isOT`（:359）→ `od4R_isOT`
  * `od4_R_OT_B`（:394）→ `od4R_OT_B`
- 依存（ビルド済みのみ import）: `Buchholz-1986 および Buchholz-rel-ord`（`BT`/`BP`/`lessBT`/`leBT`/
  `GBT`/`GBP`/`descP`/`isOT_BT`/`isOT_BP`/`OT_B`/`T_B`）、
  `Buchholz-1986-2.1-order`（`lessBT_linear_trans`／`lessBT_linear_irrefl`）。
- 状態: 🤖 GREEN（`sorry` 0、axioms = propext/Classical.choice/Quot.sound）。
  **`OTdisp_OTpred` は本ファイルでは閉じていない**（Brick B–E が未移植）。

## 🚨 まず: `OTdisp_OTpred` は真である（偽命題ではない）

wave-K 事故（Lean `Prop` が Isabelle より真に強くて偽だった）の再発チェックを
仮定束レベルで実施した。結論: **Lean `Prop` は Isabelle より真に弱い**ので安全。

| | Isabelle `od4_OTpred_final`（`layerC/pss_scratch.thy`:874、**無条件**） | Lean `OTdisp_OTpred` |
|---|---|---|
| host | `N ∈ ST_PS` | `STPS N` — 同一 |
| OT | `Trans N ∈ OT_B` | 同一 |
| 長さ | `1 < Lng N` | `2 < Lng N` — **強い仮定＝弱い命題** |
| 除外 3 本 | **不要** | 末尾零列 / condI / condVI-nadm を除外 — **さらに弱い** |
| 結論 | `Trans (Pred N) ∈ OT_B` | 同一 |

数値検証（`python/audit_8_7_otdisp_OTpred.py`、標準形プール 430 本・全て `reduced`）:

* `OTdisp_OTpred` — **発火 315、反例 0**（空虚でない）。
* `od4_OTpred_mono`（STRONG 形、除外なし・`1 < Lng`）— **発火 401、反例 0**。
* `od4_master_R`（`od4_R (Trans (Pred M)) (Trans M)`、下の Brick D）—
  **発火 393、反例 0**。これは `od4_R` の inductive（Isabelle :37）を
  audit 側で**独立に読み直して**判定手続きにしたものなので、本ファイルの
  `od4R_op` への転記が正しいことの裏付けにもなっている。

`od4_OTpred_final` は「census slot の 3 つの corner 除外はいずれも不要」と
明記した STRONG 形（同 :872 の text）。したがって `OTdisp_OTpred` は
`od4_OTpred_final` の単なる弱化であり、移植が完了すれば必ず閉じる。
Isabelle 側の残差 `DEEPOT`/`NOBR` も **既に閉じている**
（`od4_DEEPOT`:849 / `od4_NOBR`:861、どちらも `od4_OTpred_mono`:803 の instance）。
つまり `OTdisp_OTpred` は **残差ではなく未移植**である。

## 残差（次の wave 向け・Isabelle 行番号つき）

`od4_OTpred_mono`（:803）＝ Brick E の分岐は
①`Trans (Pred M) = 0_B`（`otx_OT_B_zero` で自明）②`Lng M = 2`
（`OTdisp_OTpred` は `2 < Lng N` を仮定するので **この corner は不要**）
③その他 ＝ `od4_master_R` ＋ `od4_R_OT_B`（＝本ファイルの `od4R_OT_B`）。
よって未移植は以下の 3 ブロックのみ:

* **Brick B** `od4_scbext_R`（:414）: 共有 scb 文脈を通した `od4R_op` の持ち上げ。
  唯一の障害は `otx2_align3`（`layerB/pss_wip.thy`:114296）が Lean 未移植なこと。
  Brick B が使うのは **2 項 instance**（第 3 スロットは複製）なので、実際に要るのは
  `otx2_top_shape`（同 :114214）1 本＋短い induction。`otx2_top_shape` の依存は
  `otx2_peel`（:113936）/`otx2_BP_prefix`（:113863）/`otx2_flatBP_len`（:113856）。
  Lean 側には `flatBP_injective`/`flatBT_injective`/`flatBP_length_ge_two`
  （`7.2-scb-unique`:149）が既にあるので `otx2_BP_prefix`/`otx2_flatBP_len` は近い。
* **Brick C** `od4_site_c2`（:634）: `od4R_op (transT2 M) (bpHeadT (transC2 M))` を
  `transC2` の 6 分岐すべてで示す。(I)/(III)/(V)＋2 つの else は `drop`/`deep`、
  (VI) 許容枝は `c6gx_condVI_transC1_adm` で `t₂ = 0_B` → `drop`、
  (VI) 非許容枝は **Brick C0**（`od4_condVI_nadm_c1`:479、145 行）で
  `t₂ = D_{M₁,ⱼ₀} 0` → `triv`。**Brick C0 が最重量**
  （`m_7_4_Mark_Trans_repr` ＋ `m_8_1_diagSeq_Trans` ＋ `wnx_run_entries` が要る）。
* **Brick D** `od4_master_R`（:760）: Lean は Isabelle より **短くなる**。
  Isabelle は `trans_surgery_localized` ＋ `scb_replace_principal` ＋
  `unflatBT_flat` で host 側の分解を作り直しているが、Lean の
  `replaceScb_spec`（`7.3-Trans-welldefined`:318）は
  `Trans (Pred M)` 側と `Trans M` 側の scb 分解を **同じ 1 対 `(s,b)` で同時に**
  出す（`8.6-condVI-props`:214 `trans_surgery_localized_v6p` がその形。
  ただし `private` なので複製が要る）。よって Brick D は Brick B ＋ Brick C から
  ほぼ直ちに出る。
* **複項脚** `opx_OTpred_multi_of_mono`（`layerB/pss_wip.thy`、
  `opx_OTpred_of_residuals`:573 の `multiT N` 枝）: `OTdisp_OTpred` は
  dispatcher の `oper N n = Pred N` 枝で mono/multi を分けずに呼ばれるので、
  この脚も要る。
-/

namespace PSS

/-! ## `od4_R`（Isabelle `od4_R`, `layerC/pss_scratch.thy`:37）

`od4R_op a b`: `a` は `b` から、右スパインのある 1 段で、末尾 principal を
落とす（`drop`）か、`lessBP`-より小さい **自明** principal `D_w 0` に
置き換える（`triv`）ことで得られる。これがちょうど `Trans (Pred M)` 対
`Trans M` の手術形を逆向きに読んだもの。 -/

inductive od4R_op : BT → BT → Prop where
  | drop (ps : List BP) (p : BP) : od4R_op (.trm ps) (.trm (ps ++ [p]))
  | triv {w : ℕ∞} {p : BP} (ps : List BP)
      (h : lessBP (.db w BZero) p = true) :
      od4R_op (.trm (ps ++ [.db w BZero])) (.trm (ps ++ [p]))
  | deep {c c' : BT} (h : od4R_op c c') (ps : List BP) (w : ℕ∞) :
      od4R_op (.trm (ps ++ [.db w c])) (.trm (ps ++ [.db w c']))

/-! ## サイズ測度（Isabelle `od4_sz`/`od4_szP`, 同 :50） -/

mutual
  def od4sz_op : BT → ℕ
    | .trm ps => 1 + od4szList_op ps
  def od4szP_op : BP → ℕ
    | .db _ b => 1 + od4sz_op b
  def od4szList_op : List BP → ℕ
    | [] => 0
    | p :: ps => od4szP_op p + od4szList_op ps
end

private theorem od4sz_pos_op (t : BT) : 1 ≤ od4sz_op t := by
  cases t; simp [od4sz_op]

private theorem od4szP_ge2_op (p : BP) : 2 ≤ od4szP_op p := by
  cases p with
  | db u b => have := od4sz_pos_op b; simp [od4szP_op]; omega

private theorem od4szList_append_op (xs ys : List BP) :
    od4szList_op (xs ++ ys) = od4szList_op xs + od4szList_op ys := by
  induction xs with
  | nil => simp [od4szList_op]
  | cons x xs ih => simp [od4szList_op, ih]; omega

private theorem od4szList_mem_le_op {p : BP} {ps : List BP} (h : p ∈ ps) :
    od4szP_op p ≤ od4szList_op ps := by
  induction ps with
  | nil => cases h
  | cons q qs ih =>
      rcases List.mem_cons.mp h with hq | hq
      · subst hq; simp [od4szList_op]
      · have := ih hq; simp [od4szList_op]; omega

/-! ## `G_B`-escape はサイズが真に小さい（Isabelle `od4_GBT_sz`, 同 :72） -/

mutual
  private theorem gsz_BT_op : ∀ (u : ℕ∞) (t y : BT),
      y ∈ gatherBT u t → od4sz_op y < od4sz_op t
    | _, .trm ps, y, h => by
        have := gsz_BPList_op _ ps y (by simpa [gatherBT] using h)
        simp only [od4sz_op]; omega
  private theorem gsz_BP_op : ∀ (u : ℕ∞) (p : BP) (y : BT),
      y ∈ gatherBP u p → od4sz_op y < od4szP_op p
    | u, .db v b, y, h => by
        simp only [gatherBP] at h
        by_cases huv : u ≤ v
        · rw [if_pos (by simpa using huv)] at h
          rcases List.mem_cons.mp h with hy | hy
          · subst hy; simp only [od4szP_op]; omega
          · have := gsz_BT_op u b y hy
            simp only [od4szP_op]; omega
        · rw [if_neg (by simpa using huv)] at h; cases h
  private theorem gsz_BPList_op : ∀ (u : ℕ∞) (ps : List BP) (y : BT),
      y ∈ gatherBPList u ps → od4sz_op y < 1 + od4szList_op ps
    | _, [], _, h => by simp [gatherBPList] at h
    | u, p :: ps, y, h => by
        simp only [gatherBPList, List.mem_append] at h
        rcases h with h | h
        · have := gsz_BP_op u p y h
          simp only [od4szList_op]; omega
        · have := gsz_BPList_op u ps y h
          simp only [od4szList_op]; omega
end

/-- Isabelle `od4_GBT_sz`（同 :72）: `G_u t` の元は `t` より真に小さいサイズ。 -/
theorem od4R_GBT_sz {u : ℕ∞} {t y : BT} (h : y ∈ GBT u t) :
    od4sz_op y < od4sz_op t :=
  gsz_BT_op u t y (by simpa [GBT] using h)

/-! ## `od4_R` は狭義の順序ステップ（Isabelle `od4_R_lessBT`, 同 :98） -/

/-- Isabelle `ddx_lessBT_snoc`（`layerB/pss_wip.thy`:109110）の必要形。 -/
private theorem lessBT_snoc_op (ps : List BP) (p : BP) :
    lessBT (.trm ps) (.trm (ps ++ [p])) = true := by
  induction ps with
  | nil => simp [lessBT, lessBPList]
  | cons q qs ih =>
      simp only [List.cons_append, lessBT, lessBPList] at *
      simp [ih]

/-- Isabelle `otx2_lessBT_snocsnoc`（同 :113874）の必要形（`→` 方向）。 -/
private theorem lessBT_snocsnoc_op (ps : List BP) {p q : BP}
    (h : lessBP p q = true) :
    lessBT (.trm (ps ++ [p])) (.trm (ps ++ [q])) = true := by
  induction ps with
  | nil => simp [lessBT, lessBPList, h]
  | cons r rs ih =>
      simp only [List.cons_append, lessBT, lessBPList] at *
      simp [ih]

theorem od4R_lessBT {a b : BT} (h : od4R_op a b) : lessBT a b = true := by
  induction h with
  | drop ps p => exact lessBT_snoc_op ps p
  | triv ps hlt => exact lessBT_snocsnoc_op ps hlt
  | deep hc ps w ih =>
      refine lessBT_snocsnoc_op ps ?_
      simp only [lessBP, ih]
      simp

/-! ## 順序移送（Isabelle `od4_peel_less`/`od4_transfer_all`, 同 :121/:155） -/

private theorem od4_peel_less_op {X Y : List BP}
    (core : ∀ z : BT, lessBT z (.trm Y) = true → od4sz_op z < od4sz_op (.trm X) →
      lessBT z (.trm X) = true) :
    ∀ (ps : List BP) (y : BT), lessBT y (.trm (ps ++ Y)) = true →
      od4sz_op y < od4sz_op (.trm (ps ++ X)) → lessBT y (.trm (ps ++ X)) = true := by
  intro ps
  induction ps with
  | nil => intro y h1 h2; exact core y (by simpa using h1) (by simpa using h2)
  | cons q ps' ih =>
      intro y h1 h2
      cases y with
      | trm ys =>
        cases ys with
        | nil => simp [lessBT, lessBPList]
        | cons r ys' =>
            simp only [List.cons_append, lessBT, lessBPList, Bool.or_eq_true,
              Bool.and_eq_true] at h1 ⊢
            rcases h1 with hrq | ⟨hrq, htl⟩
            · exact Or.inl hrq
            · have req : r = q := by simpa using hrq
              subst req
              refine Or.inr ⟨by simp, ?_⟩
              refine ih (.trm ys') htl ?_
              simp only [List.cons_append, od4sz_op, od4szList_op] at h2 ⊢
              omega

private theorem od4R_transfer_all_op {a b : BT} (R : od4R_op a b) :
    ∀ y : BT, lessBT y b = true → od4sz_op y < od4sz_op a → lessBT y a = true := by
  induction R with
  | drop ps p =>
      have core : ∀ z : BT, lessBT z (.trm [p]) = true →
          od4sz_op z < od4sz_op (.trm ([] : List BP)) → lessBT z (.trm []) = true := by
        intro z _ hz
        have := od4sz_pos_op z
        simp only [od4sz_op, od4szList_op] at hz
        omega
      intro y h1 h2
      have := od4_peel_less_op (X := []) (Y := [p]) core ps y (by simpa using h1)
        (by simpa using h2)
      simpa using this
  | @triv w p ps hlt =>
      have core : ∀ z : BT, lessBT z (.trm [p]) = true →
          od4sz_op z < od4sz_op (.trm [BP.db w BZero]) →
          lessBT z (.trm [BP.db w BZero]) = true := by
        intro z _ hz
        cases z with
        | trm zs =>
          cases zs with
          | nil => simp [lessBT, lessBPList]
          | cons z0 zs' =>
              exfalso
              have h0 : od4szP_op z0 ≤ od4szList_op (z0 :: zs') :=
                od4szList_mem_le_op (by simp)
              have h2 := od4szP_ge2_op z0
              simp only [od4sz_op, od4szList_op, od4szP_op, BZero] at hz h0 ⊢
              omega
      intro y h1 h2
      exact od4_peel_less_op (X := [BP.db w BZero]) (Y := [p]) core ps y h1 h2
  | @deep c c' hc ps w ih =>
      have core : ∀ z : BT, lessBT z (.trm [BP.db w c']) = true →
          od4sz_op z < od4sz_op (.trm [BP.db w c]) →
          lessBT z (.trm [BP.db w c]) = true := by
        intro z hzl hzsz
        cases z with
        | trm zs =>
          cases zs with
          | nil => simp [lessBT, lessBPList]
          | cons z0 zs' =>
              cases z0 with
              | db u d =>
                  have hnotail : ¬ (lessBPList zs' [] = true) := by
                    cases zs' <;> simp [lessBPList]
                  simp only [lessBT, lessBPList, Bool.or_eq_true, Bool.and_eq_true] at hzl
                  have hhd : lessBP (.db u d) (.db w c') = true := by
                    rcases hzl with h | ⟨_, htl⟩
                    · exact h
                    · exact absurd htl hnotail
                  simp only [lessBP, Bool.or_eq_true, Bool.and_eq_true,
                    decide_eq_true_eq] at hhd
                  simp only [lessBT, lessBPList, Bool.or_eq_true, Bool.and_eq_true,
                    lessBP, decide_eq_true_eq]
                  rcases hhd with huw | ⟨huw, hdc'⟩
                  · exact Or.inl (Or.inl huw)
                  · have hueq : u = w := by simpa using huw
                    subst hueq
                    have hdsz : od4sz_op d < od4sz_op c := by
                      simp only [od4sz_op, od4szList_op, od4szP_op] at hzsz ⊢
                      omega
                    have := ih d hdc' hdsz
                    exact Or.inl (Or.inr ⟨by simp, this⟩)
      intro y h1 h2
      exact od4_peel_less_op (X := [BP.db w c]) (Y := [BP.db w c']) core ps y h1 h2

/-- Isabelle `od4_transfer`（同 :241）。 -/
theorem od4R_transfer {a b y : BT} (R : od4R_op a b) (hy : lessBT y b = true)
    (hsz : od4sz_op y < od4sz_op a) : lessBT y a = true :=
  od4R_transfer_all_op R y hy hsz

/-! ## escape 集合の収縮（Isabelle `od4_R_GBT`, 同 :248） -/

private theorem mem_GBT_trm_snoc_op {u : ℕ∞} {ps : List BP} {p : BP} {y : BT} :
    y ∈ GBT u (.trm (ps ++ [p])) ↔ y ∈ GBT u (.trm ps) ∨ y ∈ GBP u p := by
  simp only [GBT, GBP, Set.mem_setOf_eq, gatherBT, List.contains_iff_mem]
  induction ps with
  | nil => simp [gatherBPList]
  | cons q qs ih => simp only [List.cons_append, gatherBPList, List.mem_append, ih]; tauto

private theorem mem_GBP_db_op {u v : ℕ∞} {b y : BT} :
    y ∈ GBP u (.db v b) ↔ (u ≤ v ∧ (y = b ∨ y ∈ GBT u b)) := by
  simp only [GBP, GBT, Set.mem_setOf_eq, gatherBP, List.contains_iff_mem]
  by_cases h : u ≤ v
  · rw [if_pos (by simpa using h)]; simp [h]
  · rw [if_neg (by simpa using h)]; simp [h]

private theorem od4R_GBT_op {a b : BT} (R : od4R_op a b) :
    ∀ (u : ℕ∞) (y : BT), y ∈ GBT u a →
      y ∈ GBT u b ∨ y = BZero ∨ ∃ y', od4R_op y y' ∧ y' ∈ GBT u b := by
  induction R with
  | drop ps p =>
      intro u y hy
      exact Or.inl (mem_GBT_trm_snoc_op.mpr (Or.inl hy))
  | @triv w p ps hlt =>
      intro u y hy
      rcases mem_GBT_trm_snoc_op.mp hy with h | h
      · exact Or.inl (mem_GBT_trm_snoc_op.mpr (Or.inl h))
      · rcases mem_GBP_db_op.mp h with ⟨_, hz | hz⟩
        · exact Or.inr (Or.inl hz)
        · exfalso; simp [GBT, BZero, gatherBT, gatherBPList] at hz
  | @deep c c' hc ps w ih =>
      intro u y hy
      rcases mem_GBT_trm_snoc_op.mp hy with h | h
      · exact Or.inl (mem_GBT_trm_snoc_op.mpr (Or.inl h))
      · rcases mem_GBP_db_op.mp h with ⟨huw, hz | hz⟩
        · subst hz
          refine Or.inr (Or.inr ⟨c', hc, ?_⟩)
          exact mem_GBT_trm_snoc_op.mpr (Or.inr (mem_GBP_db_op.mpr ⟨huw, Or.inl rfl⟩))
        · rcases ih u y hz with h' | h' | ⟨y', hy', hy'in⟩
          · exact Or.inl (mem_GBT_trm_snoc_op.mpr
              (Or.inr (mem_GBP_db_op.mpr ⟨huw, Or.inr h'⟩)))
          · exact Or.inr (Or.inl h')
          · exact Or.inr (Or.inr ⟨y', hy', mem_GBT_trm_snoc_op.mpr
              (Or.inr (mem_GBP_db_op.mpr ⟨huw, Or.inr hy'in⟩))⟩)

/-! ## `descP` と site の `G`-移送（Isabelle `od4_descP_snoc`/`od4_site_G`, 同 :307/:327） -/

private theorem leBT_trans_op {x y z : BT} (h1 : leBT x y = true) (h2 : leBT y z = true) :
    leBT x z = true := by
  simp only [leBT, Bool.or_eq_true, beq_iff_eq] at h1 h2 ⊢
  rcases h1 with h1 | h1
  · rcases h2 with h2 | h2
    · exact Or.inl (lessBT_linear_trans _ _ _ h1 h2)
    · subst h2; exact Or.inl h1
  · subst h1; exact h2

private theorem od4_descP_snoc_op : ∀ (ps : List BP) {p p' : BP},
    descP (ps ++ [p]) = true → leBT (.trm [p']) (.trm [p]) = true →
    descP (ps ++ [p']) = true := by
  intro ps
  induction ps with
  | nil => intro p p' _ _; simp [descP]
  | cons q qs ih =>
      intro p p' hd hle
      cases qs with
      | nil =>
          simp only [List.nil_append, List.cons_append, descP, Bool.and_eq_true] at hd ⊢
          exact ⟨leBT_trans_op hle hd.1, by simp [descP]⟩
      | cons q1 qs' =>
          simp only [List.cons_append, descP, Bool.and_eq_true] at hd ⊢
          exact ⟨hd.1, ih hd.2 hle⟩

private theorem od4_site_G_op {c c' : BT} {w : ℕ∞} (R : od4R_op c c')
    (host : ∀ y ∈ GBT w c', lessBT y c' = true) :
    ∀ y ∈ GBT w c, lessBT y c = true := by
  intro y hy
  have hsz : od4sz_op y < od4sz_op c := od4R_GBT_sz hy
  rcases od4R_GBT_op R w y hy with h | h | ⟨y', hR', hy'⟩
  · exact od4R_transfer R (host y h) hsz
  · -- `y = 0`: `c` は空でない（`GBT w c` が非空）ので `0 < c`
    subst h
    cases c with
    | trm cs =>
      cases cs with
      | nil => exfalso; simp [GBT, gatherBT, gatherBPList] at hy
      | cons _ _ => simp [lessBT, lessBPList, BZero]
  · have h1 : lessBT y y' = true := od4R_lessBT hR'
    have h2 : lessBT y' c' = true := host y' hy'
    exact od4R_transfer R (lessBT_linear_trans _ _ _ h1 h2) hsz

/-! ## MAIN: `od4_R` は `isOT` を逆向きに保つ（Isabelle `od4_R_isOT`, 同 :359） -/

private theorem descP_append1_op : ∀ (xs ys : List BP),
    descP (xs ++ ys) = true → descP xs = true := by
  intro xs
  induction xs with
  | nil => intro _ _; simp [descP]
  | cons x xs ih =>
      intro ys h
      cases xs with
      | nil => simp [descP]
      | cons x1 xs' =>
          simp only [List.cons_append, descP, Bool.and_eq_true] at h ⊢
          exact ⟨h.1, ih ys h.2⟩

private theorem isOT_BPList_append_op : ∀ (xs ys : List BP),
    isOT_BPList (xs ++ ys) = true ↔ (isOT_BPList xs = true ∧ isOT_BPList ys = true) := by
  intro xs
  induction xs with
  | nil => intro ys; simp [isOT_BPList]
  | cons x xs ih =>
      intro ys
      simp only [List.cons_append, isOT_BPList, Bool.and_eq_true, ih]
      tauto

theorem od4R_isOT {a b : BT} (R : od4R_op a b) (hb : isOT_BT b = true) :
    isOT_BT a = true := by
  induction R with
  | drop ps p =>
      simp only [isOT_BT, Bool.and_eq_true] at hb ⊢
      exact ⟨(isOT_BPList_append_op ps [p]).mp hb.1 |>.1, descP_append1_op ps [p] hb.2⟩
  | @triv w p ps hlt =>
      simp only [isOT_BT, Bool.and_eq_true] at hb ⊢
      have hel : isOT_BPList ps = true := ((isOT_BPList_append_op ps [p]).mp hb.1).1
      have hnew : isOT_BP (.db w BZero) = true := by
        simp [isOT_BP, isOT_BT, isOT_BPList, descP, BZero, gatherBT, gatherBPList]
      refine ⟨(isOT_BPList_append_op ps [.db w BZero]).mpr ⟨hel, by simp [isOT_BPList, hnew]⟩, ?_⟩
      refine od4_descP_snoc_op ps hb.2 ?_
      simp only [leBT, Bool.or_eq_true]
      exact Or.inl (by simp [lessBT, lessBPList, hlt])
  | @deep c c' hc ps w ih =>
      simp only [isOT_BT, Bool.and_eq_true] at hb ⊢
      have hsplit := (isOT_BPList_append_op ps [.db w c']).mp hb.1
      have hel : isOT_BPList ps = true := hsplit.1
      have hlastOT : isOT_BP (.db w c') = true := by
        have := hsplit.2; simp only [isOT_BPList, Bool.and_eq_true] at this; exact this.1
      simp only [isOT_BP, Bool.and_eq_true] at hlastOT
      have hc'OT : isOT_BT c' = true := hlastOT.1
      have hostG : ∀ y ∈ GBT w c', lessBT y c' = true := by
        intro y hy
        have := List.all_eq_true.mp hlastOT.2 y (by simpa [GBT, List.contains_iff_mem] using hy)
        simpa using this
      have hcOT : isOT_BT c = true := ih hc'OT
      have hcG : ∀ y ∈ GBT w c, lessBT y c = true := od4_site_G_op hc hostG
      have hnew : isOT_BP (.db w c) = true := by
        simp only [isOT_BP, Bool.and_eq_true]
        refine ⟨hcOT, List.all_eq_true.mpr ?_⟩
        intro y hy
        simpa using hcG y (by simpa [GBT, List.contains_iff_mem] using hy)
      refine ⟨(isOT_BPList_append_op ps [.db w c]).mpr ⟨hel, by simp [isOT_BPList, hnew]⟩, ?_⟩
      refine od4_descP_snoc_op ps hb.2 ?_
      have : lessBT c c' = true := od4R_lessBT hc
      simp only [leBT, Bool.or_eq_true]
      refine Or.inl ?_
      simp [lessBT, lessBPList, lessBP, this]

/-- Isabelle `od4_R_OT_B`（同 :394）: `od4_R` は `OT_B` を逆向きに保つ。 -/
theorem od4R_OT_B {a b : BT} (R : od4R_op a b) (hb : b ∈ OT_B) (ha : a ∈ T_B) :
    a ∈ OT_B := by
  refine ⟨?_, ha⟩
  show isOT_BT a = true
  exact od4R_isOT R hb.1

/-! ## 回帰ベクトル -/

private def bOP : BT := .trm [.db 2 BZero, .db 1 BZero]
private def aOP : BT := .trm [.db 2 BZero]

example : od4R_op aOP bOP := by
  show od4R_op (.trm [.db 2 BZero]) (.trm ([.db 2 BZero] ++ [.db 1 BZero]))
  exact od4R_op.drop _ _

#guard isOT_BT bOP
#guard isOT_BT aOP

#print axioms od4R_GBT_sz
#print axioms od4R_lessBT
#print axioms od4R_transfer
#print axioms od4R_isOT
#print axioms od4R_OT_B

end PSS
