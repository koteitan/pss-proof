import «8».«8.7-otdisp-OTpred»
import «8».«8.6-condVI-props»
import «7».«7.3-Trans-welldefined»

/-!
# §8.7 `OTdisp_OTpred` へ向けた Brick D — MASTER un-insertion

- Isabelle（設計図）: `isabelle/layerC/pss_scratch.thy` の Brick D
  `od4_master_R`（:760）＝「`Trans (Pred M)` は `Trans M` の un-insertion」。
  本ファイルは Brick D の**構造糊**を移植する:
  * scb 文脈の un-insertion lift `od4_scbext_R`（同 :414）→ `od4R_scbext`（PUBLIC、無条件）
  * その土台の 1 段整列（Isabelle `otx2_top_shape`/`otx2_join3`/`otx2_align3`,
    `layerB/pss_wip.thy`:114214/:114017/:114296）を **2 項版**に縮約
    （`align_single_bD`/`align_join_bD`/`align2_bD`）。
    Lean には `PSS.Flat` の flatinj 原始（`flatBP_cancel`/`flatBP_injective`/
    `flatBT_injective`/`flatBP_localize_append`/`flatBP_length_ge_two`）が既にあるので
    重み計算を全て再利用でき、Isabelle より遥かに短い。
  * MASTER `od4_master_R` は **site 前提付き**で配線（`od4_master_R_of_site`）。
    Isabelle が `scb_replace_principal`＋`unflatBT_flat` で組み直す host 側分解は
    Lean の `trans_surgery_localized_v6p`（`8.6-condVI-props`:214）が 1 対 `(s,b)` で
    直接くれる。残る唯一の未移植は Brick C `od4_site_c2`（同 :634、`od4R_op (transT2 M)
    (bpHeadT (transC2 M))`）で、これを仮定にとる。
- 依存（ビルド済みのみ import）: Brick A（`od4R_op`/`od4sz_op`）,
  `8.6-condVI-props`（`trans_surgery_localized_v6p`; 推移的に `c1_shape_holds`,
  `PSS.Flat`/`PSS.Scb`/`PSS.Trans`）, `7.3-Trans-welldefined`（`replaceScb_spec`）。
- 状態: 🤖 GREEN（`sorry` 0、axioms = propext/Classical.choice/Quot.sound）。
  `od4R_scbext` は無条件で閉じた。`od4_master_R` は Brick C（`od4_site_c2`）を仮定に
  残す（未移植）。詳細は末尾 needs。
- 統合メモ（親向け）: 並行 wave-M が `8.7-otpred-brickB.lean` に同一の
  `od4_scbext_R`（本ファイルの `od4R_scbext` と同型・同名 Isabelle 由来）を、
  `8.7-otpred-brickC0.lean` に Brick C0（`od4_condVI_nadm_c1`）を移植中。
  committed でないため import できず、本ファイルは Brick B を自前再導出して
  self-contained に閉じた。統合時は `od4R_scbext` を brickB の `od4_scbext_R` に
  差し替えて整列補題群（`align*_bD`）を削除してよい。
-/

namespace PSS

/-! ## サイズ測度の append 補題（Brick A の private を複製） -/

private theorem od4szList_append_bD (xs ys : List BP) :
    od4szList_op (xs ++ ys) = od4szList_op xs + od4szList_op ys := by
  induction xs with
  | nil => simp [od4szList_op]
  | cons x xs ih => simp [od4szList_op, ih]; omega

/-! ## 先頭記号による項の形（`flatBT` の頭を読む） -/

/-- `flatBT t` が `Dsym w` で始まるなら `t` は単項 `D_w a`。 -/
private theorem flatBT_head_dsym_bD {t : BT} {w : ℕ∞} {rest : List Sym}
    (h : flatBT t = .dsym w :: rest) :
    ∃ a, t = .trm [.db w a] ∧ flatBT a = rest := by
  rcases t with ⟨ps⟩
  match ps with
  | [] => simp [flatBT] at h
  | [.db u a] =>
      refine ⟨a, ?_, ?_⟩
      · have : Sym.dsym u = Sym.dsym w := by
          simpa [flatBT, flatBP] using congrArg List.head? h
        simp_all
      · have hu : Sym.dsym u = Sym.dsym w := by
          simpa [flatBT, flatBP] using congrArg List.head? h
        have : u = w := by simpa using hu
        subst this
        simpa [flatBT, flatBP] using congrArg List.tail h
  | p :: q :: qs => simp [flatBT] at h

/-- `flatBT t` が `LP` で始まるなら `t` は 2 成分以上のタプル。 -/
private theorem flatBT_head_lp_bD {t : BT} {rest : List Sym}
    (h : flatBT t = .lp :: rest) :
    ∃ p q qs, t = .trm (p :: q :: qs) := by
  rcases t with ⟨ps⟩
  match ps with
  | [] => simp [flatBT] at h
  | [.db u a] => simp [flatBT, flatBP] at h
  | p :: q :: qs => exact ⟨p, q, qs, rfl⟩

/-! ## 単一 principal レベルの 2 項整列（Isabelle `otx2_top_shape` の principal 枝） -/

private theorem align_single_bD {r1 r2 cp1 cp2 : BP} {s bc : List Sym}
    (h1 : flatBP r1 = s ++ flatBP cp1 ++ bc)
    (h2 : flatBP r2 = s ++ flatBP cp2 ++ bc) :
    (s = [] ∧ bc = [] ∧ r1 = cp1 ∧ r2 = cp2) ∨
      (∃ (w : ℕ∞) (a1 a2 : BT) (s2 : List Sym), r1 = .db w a1 ∧ r2 = .db w a2 ∧
        s = .dsym w :: s2 ∧ flatBT a1 = s2 ++ flatBP cp1 ++ bc ∧
        flatBT a2 = s2 ++ flatBP cp2 ++ bc) := by
  rcases r1 with ⟨w1, a1⟩
  rcases r2 with ⟨w2, a2⟩
  cases s with
  | nil =>
      simp only [List.nil_append] at h1 h2
      have c1 : flatBP (.db w1 a1) ++ [] = flatBP cp1 ++ bc := by simpa using h1
      have c2 : flatBP (.db w2 a2) ++ [] = flatBP cp2 ++ bc := by simpa using h2
      obtain ⟨he1, hbc1⟩ := flatBP_cancel c1
      obtain ⟨he2, _⟩ := flatBP_cancel c2
      refine Or.inl ⟨rfl, hbc1.symm, flatBP_injective he1, flatBP_injective he2⟩
  | cons x s2 =>
      have hx1 : x = .dsym w1 := by
        have := congrArg List.head? h1
        simpa [flatBP] using this.symm
      have hx2 : x = .dsym w2 := by
        have := congrArg List.head? h2
        simpa [flatBP] using this.symm
      have hw : w1 = w2 := by
        have := hx1.symm.trans hx2; simpa using this
      subst hw
      have hf1 : flatBT a1 = s2 ++ flatBP cp1 ++ bc := by
        have := congrArg List.tail h1
        simpa [flatBP, hx1] using this
      have hf2 : flatBT a2 = s2 ++ flatBP cp2 ++ bc := by
        have := congrArg List.tail h2
        simpa [flatBP, hx2] using this
      exact Or.inr ⟨w1, a1, a2, s2, rfl, rfl, by rw [hx1], hf1, hf2⟩

/-! ## タプル tail の 2 項整列（Isabelle `otx2_join3` の 2 項版） -/

private theorem align_join_bD (cp1 cp2 : BP) :
    ∀ (rs1 rs2 : List BP) (s b : List Sym),
      flatBPTail rs1 ++ [Sym.rp] = s ++ flatBP cp1 ++ b →
      flatBPTail rs2 ++ [Sym.rp] = s ++ flatBP cp2 ++ b →
      (∀ x ∈ b, x = Sym.rp) →
      (∃ qs, rs1 = qs ++ [cp1] ∧ rs2 = qs ++ [cp2]) ∨
        (∃ (w : ℕ∞) (lb1 lb2 : BT) (qs : List BP) (sc bc : List Sym),
          rs1 = qs ++ [.db w lb1] ∧ rs2 = qs ++ [.db w lb2] ∧
          flatBT lb1 = sc ++ flatBP cp1 ++ bc ∧
          flatBT lb2 = sc ++ flatBP cp2 ++ bc ∧ (∀ x ∈ bc, x = Sym.rp)) := by
  intro rs1
  induction rs1 with
  | nil =>
      intro rs2 s b h1 _ _
      exfalso
      have hlen := congrArg List.length h1
      simp only [flatBPTail, List.nil_append, List.length_cons, List.length_nil,
        List.length_append] at hlen
      have := flatBP_length_ge_two cp1
      omega
  | cons r1 rest1 ih =>
      intro rs2 s b h1 h2 hb
      -- `s` は `.cm` で始まる
      obtain ⟨s1, rfl⟩ : ∃ s1, s = .cm :: s1 := by
        have hsne : s ≠ [] := by
          intro hs; subst hs
          have hh := congrArg List.head? h1
          rcases cp1 with ⟨u, a⟩
          simp [flatBPTail, flatBP] at hh
        obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hsne
        have hx : x = Sym.cm := by
          have hh := congrArg List.head? h1
          simp only [flatBPTail, List.cons_append, List.head?_cons,
            Option.some.injEq] at hh
          exact hh.symm
        exact ⟨xs, by rw [hx]⟩
      have hj1 : flatBP r1 ++ (flatBPTail rest1 ++ [Sym.rp]) = s1 ++ flatBP cp1 ++ b := by
        have h1' := h1
        simp only [flatBPTail, List.cons_append, List.cons.injEq, true_and] at h1'
        simpa [List.append_assoc] using h1'
      -- `rs2` も非空
      obtain ⟨r2, rest2, rfl⟩ : ∃ r2 rest2, rs2 = r2 :: rest2 := by
        rcases rs2 with _ | ⟨r2, rest2⟩
        · exfalso
          have hh := congrArg List.head? h2
          simp [flatBPTail, List.cons_append] at hh
        · exact ⟨r2, rest2, rfl⟩
      have hj2 : flatBP r2 ++ (flatBPTail rest2 ++ [Sym.rp]) = s1 ++ flatBP cp2 ++ b := by
        have h2' := h2
        simp only [flatBPTail, List.cons_append, List.cons.injEq, true_and] at h2'
        simpa [List.append_assoc] using h2'
      rcases flatBP_localize_append hj1 with
        ⟨inside, hr1eq, hbeq⟩ | ⟨after, hs1eq, hJ1⟩
      · -- IN: core は r1 の内部 → rest1 = []
        have hrest1nil : rest1 = [] := by
          by_contra hne
          obtain ⟨r, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
          have hcm : Sym.cm ∈ b := by rw [hbeq]; simp [flatBPTail]
          exact absurd (hb Sym.cm hcm) (by simp)
        subst hrest1nil
        simp only [flatBPTail, List.nil_append] at hbeq
        have hins_rp : ∀ x ∈ inside, x = Sym.rp := by
          intro x hx; exact hb x (by rw [hbeq]; exact List.mem_append_left _ hx)
        rcases flatBP_localize_append hj2 with
          ⟨inside2, hr2eq, hbeq2⟩ | ⟨after2, hs1eq2, _⟩
        · -- rs2 側も IN
          have hrest2nil : rest2 = [] := by
            by_contra hne
            obtain ⟨r, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
            have hcm : Sym.cm ∈ b := by rw [hbeq2]; simp [flatBPTail]
            exact absurd (hb Sym.cm hcm) (by simp)
          subst hrest2nil
          simp only [flatBPTail, List.nil_append] at hbeq2
          have hins_eq : inside = inside2 :=
            List.append_cancel_right (hbeq.symm.trans hbeq2)
          rw [← hins_eq] at hr2eq
          rcases align_single_bD hr1eq hr2eq with
            ⟨_, _, hr1cp, hr2cp⟩ | ⟨w, la1, la2, s2, hr1db, hr2db, _, hla1, hla2⟩
          · exact Or.inl ⟨[], by simp [hr1cp], by simp [hr2cp]⟩
          · exact Or.inr ⟨w, la1, la2, [], s2, inside, by simp [hr1db], by simp [hr2db],
              hla1, hla2, hins_rp⟩
        · -- rs2 が BEYOND: `mixed` により矛盾
          exfalso
          have hchain : flatBP r1 ++ ([] : List Sym) =
              flatBP r2 ++ (after2 ++ flatBP cp1 ++ inside) := by
            rw [List.append_nil, hr1eq, hs1eq2]; simp [List.append_assoc]
          obtain ⟨_, hnil⟩ := flatBP_cancel hchain
          have hlen := congrArg List.length hnil
          simp only [List.length_nil, List.length_append] at hlen
          have hge := flatBP_length_ge_two cp1
          omega
      · -- BEYOND: core は r1 より後 → r2 = r1、tail を IH に回す
        have hchain : flatBP r2 ++ (flatBPTail rest2 ++ [Sym.rp]) =
            flatBP r1 ++ (after ++ flatBP cp2 ++ b) := by
          rw [hj2, hs1eq]; simp [List.append_assoc]
        obtain ⟨hr21, hJ2⟩ := flatBP_cancel hchain
        have hr21e : r2 = r1 := flatBP_injective hr21
        rcases ih rest2 after b hJ1 hJ2 hb with
          ⟨qs, hr1', hr2'⟩ | ⟨w, lb1, lb2, qs, sc, bc, hr1', hr2', f1, f2, bcR⟩
        · exact Or.inl ⟨r1 :: qs, by simp [hr1'], by simp [hr21e, hr2']⟩
        · exact Or.inr ⟨w, lb1, lb2, r1 :: qs, sc, bc, by simp [hr1'], by simp [hr21e, hr2'],
            f1, f2, bcR⟩

/-! ## トップレベルの 2 項整列（Isabelle `otx2_align3` の 2 項版） -/

private theorem align2_bD (t1 t2 : BT) (s b : List Sym) (cp1 cp2 : BP)
    (e1 : flatBT t1 = s ++ flatBP cp1 ++ b)
    (e2 : flatBT t2 = s ++ flatBP cp2 ++ b)
    (bR : ∀ x ∈ b, x = Sym.rp) :
    (∃ qs, t1 = .trm (qs ++ [cp1]) ∧ t2 = .trm (qs ++ [cp2])) ∨
      (∃ (w : ℕ∞) (lb1 lb2 : BT) (qs : List BP) (sc bc : List Sym),
        t1 = .trm (qs ++ [.db w lb1]) ∧ t2 = .trm (qs ++ [.db w lb2]) ∧
        flatBT lb1 = sc ++ flatBP cp1 ++ bc ∧ flatBT lb2 = sc ++ flatBP cp2 ++ bc ∧
        (∀ x ∈ bc, x = Sym.rp)) := by
  rcases t1 with ⟨ps1⟩
  rcases ps1 with _ | ⟨p1, tail1⟩
  · exfalso
    have hlen := congrArg List.length e1
    simp only [flatBT, List.length_cons, List.length_nil, List.length_append] at hlen
    have := flatBP_length_ge_two cp1
    omega
  · rcases tail1 with _ | ⟨q1, rest1⟩
    · -- 単項 `t1 = D_? _`
      simp only [flatBT] at e1
      cases s with
      | nil =>
          -- `p1 = cp1`, `b = []`, `t2 = .trm [cp2]`
          have hc : flatBP p1 ++ ([] : List Sym) = flatBP cp1 ++ b := by simpa using e1
          obtain ⟨hpe, hbe⟩ := flatBP_cancel hc
          have hp1cp : p1 = cp1 := flatBP_injective hpe
          subst hbe
          have ht2 : t2 = .trm [cp2] := by
            apply flatBT_injective
            rw [e2]; simp [flatBT]
          exact Or.inl ⟨[], by simp [hp1cp], by simp [ht2]⟩
      | cons x s' =>
          rcases p1 with ⟨w1, a1⟩
          have hx : x = .dsym w1 := by
            have := congrArg List.head? e1
            simpa [flatBP] using this.symm
          have ha1 : flatBT a1 = s' ++ flatBP cp1 ++ b := by
            have := congrArg List.tail e1
            simpa [flatBP, hx] using this
          have hlp : flatBT t2 = .dsym w1 :: (s' ++ flatBP cp2 ++ b) := by
            rw [e2, hx]; simp
          obtain ⟨a2, ht2, ha2⟩ := flatBT_head_dsym_bD hlp
          exact Or.inr ⟨w1, a1, a2, [], s', b, by simp, by simp [ht2], ha1, ha2, bR⟩
    · -- タプル `t1 = .trm (p1 :: q1 :: rest1)`
      obtain ⟨s1, rfl⟩ : ∃ s1, s = .lp :: s1 := by
        have hsne : s ≠ [] := by
          intro hs; subst hs
          have hh := congrArg List.head? e1
          rcases cp1 with ⟨u, a⟩
          simp [flatBT, flatBP] at hh
        obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hsne
        have hx : x = Sym.lp := by
          have hh := congrArg List.head? e1
          simp only [flatBT, List.cons_append, List.head?_cons, Option.some.injEq] at hh
          exact hh.symm
        exact ⟨xs, by rw [hx]⟩
      have hp1 : flatBP p1 ++ (flatBPTail (q1 :: rest1) ++ [Sym.rp]) =
          s1 ++ flatBP cp1 ++ b := by
        have e1' := e1
        simp only [flatBT, List.cons_append, List.cons.injEq, true_and] at e1'
        simpa [List.append_assoc] using e1'
      rcases flatBP_localize_append hp1 with ⟨inside, _, hbeq⟩ | ⟨after, hs1eq, hJ1⟩
      · exfalso
        have hcm : Sym.cm ∈ b := by rw [hbeq]; simp [flatBPTail]
        exact absurd (bR Sym.cm hcm) (by simp)
      · -- `t2` もタプルで先頭 `p1` 一致
        have hlp2 : flatBT t2 = Sym.lp :: (s1 ++ flatBP cp2 ++ b) := by
          rw [e2]; simp [List.append_assoc]
        obtain ⟨p2, q2, rest2, ht2⟩ := flatBT_head_lp_bD hlp2
        have hp2 : flatBP p2 ++ (flatBPTail (q2 :: rest2) ++ [Sym.rp]) =
            s1 ++ flatBP cp2 ++ b := by
          have e2' := e2
          rw [ht2] at e2'
          simp only [flatBT, List.cons_append, List.cons.injEq, true_and] at e2'
          simpa [List.append_assoc] using e2'
        have hchain : flatBP p2 ++ (flatBPTail (q2 :: rest2) ++ [Sym.rp]) =
            flatBP p1 ++ (after ++ flatBP cp2 ++ b) := by
          rw [hp2, hs1eq]; simp [List.append_assoc]
        obtain ⟨hp21, hJ2⟩ := flatBP_cancel hchain
        have hp21e : p2 = p1 := flatBP_injective hp21
        rcases align_join_bD cp1 cp2 (q1 :: rest1) (q2 :: rest2) after b hJ1 hJ2 bR with
          ⟨qs, hq1, hq2⟩ | ⟨w, lb1, lb2, qs, sc, bc, hq1, hq2, f1, f2, bcR'⟩
        · exact Or.inl ⟨p1 :: qs, by simp [hq1], by rw [ht2]; simp [hp21e, hq2]⟩
        · exact Or.inr ⟨w, lb1, lb2, p1 :: qs, sc, bc, by simp [hq1],
            by rw [ht2]; simp [hp21e, hq2], f1, f2, bcR'⟩

/-! ## Brick B: scb 文脈越しの `od4_R` lift（Isabelle `od4_scbext_R`, :414、無条件） -/

private theorem od4sz_snoc_lt_bD (qs : List BP) (w : ℕ∞) (lb : BT) :
    od4sz_op lb < od4sz_op (.trm (qs ++ [.db w lb])) := by
  show od4sz_op lb < 1 + od4szList_op (qs ++ [.db w lb])
  rw [od4szList_append_bD]
  show od4sz_op lb < 1 + (od4szList_op qs + (od4szP_op (.db w lb) + od4szList_op []))
  show od4sz_op lb < 1 + (od4szList_op qs + ((1 + od4sz_op lb) + 0))
  omega

private theorem scbext_aux_bD :
    ∀ n : ℕ, ∀ (t1 t2 : BT) (v : ℕ∞) (ca ca' : BT) (s b : List Sym),
      od4sz_op t1 = n →
      flatBT t1 = s ++ flatBP (.db v ca) ++ b →
      flatBT t2 = s ++ flatBP (.db v ca') ++ b →
      (∀ x ∈ b, x = Sym.rp) →
      od4R_op ca ca' →
      od4R_op t1 t2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro t1 t2 v ca ca' s b hn e1 e2 bR site
      rcases align2_bD t1 t2 s b (.db v ca) (.db v ca') e1 e2 bR with
        ⟨qs, ht1, ht2⟩ | ⟨w, lb1, lb2, qs, sc, bc, ht1, ht2, f1, f2, bcR⟩
      · rw [ht1, ht2]
        exact od4R_op.deep site qs v
      · rw [ht1, ht2]
        refine od4R_op.deep (ih (od4sz_op lb1) ?_ lb1 lb2 v ca ca' sc bc rfl f1 f2 bcR site) qs w
        rw [← hn, ht1]
        exact od4sz_snoc_lt_bD qs w lb1

/-- Isabelle `od4_scbext_R`（`layerC/pss_scratch.thy`:414、無条件）: 共有 scb 文脈
`(s, b)`（`b` は全て `RP`）を通した `od4_R` の持ち上げ。site の `od4R_op ca ca'` が
文脈越しに `od4R_op t1 t2` へ伝播する。 -/
theorem od4R_scbext {t1 t2 : BT} {v : ℕ∞} {ca ca' : BT} {s b : List Sym}
    (e1 : flatBT t1 = s ++ flatBP (.db v ca) ++ b)
    (e2 : flatBT t2 = s ++ flatBP (.db v ca') ++ b)
    (bR : ∀ x ∈ b, x = Sym.rp)
    (site : od4R_op ca ca') : od4R_op t1 t2 :=
  scbext_aux_bD (od4sz_op t1) t1 t2 v ca ca' s b rfl e1 e2 bR site

/-! ## `transC2` の principal 形（無条件：`transC2Core` は全枝 `D_v(·)`） -/

private theorem transC2_eq_Dprin_bD (M : PS) :
    ∃ body, transC2 M = Dprin (transV M) body := by
  unfold transC2 transC2Core
  split_ifs <;> exact ⟨_, rfl⟩

/-- `transC2 M` は必ず先頭指標 `transV M` の principal。 -/
private theorem transC2_head_bD (M : PS) :
    transC2 M = Dprin (transV M) (bpHeadT (transC2 M)) := by
  obtain ⟨body, hb⟩ := transC2_eq_Dprin_bD M
  rw [hb]; simp [bpHeadT, Dprin]

private theorem transC2_principal_bD (M : PS) : ∃ p, transC2 M = .trm [p] := by
  obtain ⟨body, hb⟩ := transC2_eq_Dprin_bD M
  exact ⟨.db (transV M) body, by rw [hb]; rfl⟩

/-! ## Brick D の MASTER 配線（Brick C = `od4_site_c2` を site 前提に残す）

Isabelle `od4_master_R`（`layerC/pss_scratch.thy`:760）そのもの。ただし
Brick C（surgery-site un-insertion `od4_site_c2`, 同 :634）は未移植なので
`site` 仮定として受け取る。`trans_surgery_localized_v6p`（`8.6-condVI-props`:214）が
Isabelle の `scb_replace_principal`＋`unflatBT_flat` の host 側組み直しを一括で
くれるので、そこから Brick B `od4R_scbext` を一発で叩く。 -/
theorem od4_master_R_of_site (M : PS) (hR : RTPS M) (hmono : monoT M = true)
    (hj1gt : 1 < Lng M - 1) (ht₁ : transT1 M ≠ BZero)
    (site : od4R_op (transT2 M) (bpHeadT (transC2 M))) :
    od4R_op (Trans (Pred M)) (Trans M) := by
  have hM : TPS M := RTPS_TPS M hR
  have hj₁ : 0 < transJ1 M := by simp only [transJ1, lastIdx]; omega
  obtain ⟨s, b, hd1, hd2⟩ :=
    trans_surgery_localized_v6p M hR hmono hj₁ ht₁ (transC2_principal_bD M)
  obtain ⟨hV, hc₁eq, _ht₂TB, _hjm1lt⟩ := c1_shape_holds M hR hM hmono hj₁ ht₁
  have hc1P : transC1 M = Dprin (transV M) (transT2 M) := by rw [hV]; exact hc₁eq
  have hf1 : flatBT (transC1 M) = flatBP (.db (transV M) (transT2 M)) := by
    rw [hc1P]; simp [Dprin, flatBT]
  have hf2 : flatBT (transC2 M) = flatBP (.db (transV M) (bpHeadT (transC2 M))) := by
    conv_lhs => rw [transC2_head_bD M]
    simp [Dprin, flatBT]
  have e1 : flatBT (Trans (Pred M)) = s ++ flatBP (.db (transV M) (transT2 M)) ++ b := by
    rw [← hf1]; exact hd1.1
  have e2 : flatBT (Trans M) = s ++ flatBP (.db (transV M) (bpHeadT (transC2 M))) ++ b := by
    rw [← hf2]; exact hd2.1
  exact od4R_scbext e1 e2 hd1.2.2 site

#print axioms od4R_scbext
#print axioms od4_master_R_of_site

end PSS
