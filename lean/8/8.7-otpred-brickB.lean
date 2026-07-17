import «8».«8.7-otdisp-OTpred»
import «7».«7.2-scb-unique»

/-!
# §8.7 `OTdisp_OTpred` へ向けた Brick B — 共有 scb 文脈を通した `od4_R` の持ち上げ

- Isabelle（設計図）:
  * `od4_scbext_R`（`isabelle/layerC/pss_scratch.thy`:414）＝本ファイルの主題。
    2 項の項 `t`, `t'` が同じ scb ホール `(s,b)`（`b` 全 `RP`）に同頭 principal
    core `D_v ca` / `D_v ca'` を持ち、body が un-insertion `od4_R ca ca'` で
    関係するとき、`od4_R t t'`。Isabelle は `otx2_align3` を第 3 スロット複製で
    使う。ここでは 2 項版なので `otx2_top_shape` ＋ 2 項 join parse ＋
    `od4sz_op`-降下帰納で直接組む。
  * `otx2_flatBP_len`（`layerB/pss_wip.thy`:113856）→ 既存 `flatBP_length_ge_two`
    （`7.2-scb-unique`:150）で代替（restate せず）。
  * `otx2_BP_prefix`（:113863）→ `otx2_BP_prefix`（`flatBP_cancel`+`flatBP_injective`）。
  * `otx2_peel`（:113936）→ `otx2_peel`（`List.append_eq_append_iff` ＋
    `flatSum` 重み不変量）。本ファイルの新規本体。
  * `otx2_top_shape`（:114214）→ `otx2_top_shape`。
  * 2 項 join parse（Isabelle `otx2_join3`:114051 の 2 スロット版）→ `otx2_join2`。
  * 2 項 alignment（Isabelle `otx2_align3`:114296 の 2 スロット版）→ `otx2_align2`。
- 依存（ビルド済みのみ import）: `8.7-otdisp-OTpred`（Brick A: `od4R_op`/`od4sz_op`/
  `od4szP_op`/`od4szList_op`/`od4R_isOT`）、`7.2-scb-unique`（`flatBP_length_ge_two`；
  推移的に `PSS.Flat` の `flatBP_cancel`/`flatBP_injective`/`flatBP_sum`/
  `flatBP_properPrefix_nonneg`/`flatSum_append`、`PSS.Scb` の
  `flatBT`/`flatBP`/`flatBPTail`）。
- 状態: 🤖 進行中。`otx2_BP_prefix`/`otx2_peel`/`otx2_top_shape` は PUBLIC
  （Brick C 再利用）。`od4_scbext_R` は 2 項 align 経由。
- private helper suffix: `_bB`。
-/

namespace PSS

/-! ## `otx2_BP_prefix`（Isabelle `otx2_BP_prefix`, `layerB/pss_wip.thy`:113863）

`flatBP` は prefix-free：完全 principal 文字列 ＋ 残りの分解は一意。 -/

theorem otx2_BP_prefix {p q : BP} {xs ys : List Sym}
    (h : flatBP p ++ xs = flatBP q ++ ys) : p = q ∧ xs = ys := by
  obtain ⟨hpq, hxy⟩ := flatBP_cancel h
  exact ⟨flatBP_injective hpq, hxy⟩

/-! ## join 文字列は core になれない（Isabelle `otx2_join_no_core`, :113928）

`concat (map (λr. CM # flatBP r) xs) @ [RP]`（= `flatBPTail xs ++ [.rp]`）の
先頭は `CM`/`RP`。完全 principal 文字列の先頭 `Dsym` にはならない。 -/

private theorem otx2_join_no_core_bB {xs : List BP} {cp : BP} {ys : List Sym}
    (h : flatBPTail xs ++ [.rp] = flatBP cp ++ ys) : False := by
  rcases cp with ⟨uc, ac⟩
  cases xs with
  | nil => simpa [flatBPTail, flatBP] using congrArg List.head? h
  | cons p ps => simpa [flatBPTail, flatBP] using congrArg List.head? h

/-! ## `otx2_peel`（Isabelle `otx2_peel`, :113936）

単一成分 peel：`flatBP r ⌢ join ⌢ ")" = s₁ ⌢ flatBP cp ⌢ b`（`b` 全 `RP`）で、
core は `r` の外（`flatBP r` が `s₁` の真の prefix）か、`r` が最後の成分で core が
`flatBP r` 内に全 `RP` の余白付きで入るかのいずれか。重なりは flatinj 重みで排除。 -/

theorem otx2_peel {r : BP} {rest : List BP} {s1 b : List Sym} {cp : BP}
    (eq : flatBP r ++ (flatBPTail rest ++ [.rp]) = s1 ++ flatBP cp ++ b)
    (bR : ∀ x ∈ b, x = .rp) :
    (∃ us, flatBP r ++ us = s1 ∧ us ≠ [] ∧
        flatBPTail rest ++ [.rp] = us ++ flatBP cp ++ b)
    ∨ (rest = [] ∧ ∃ vs, flatBP r = s1 ++ flatBP cp ++ vs ∧
        b = vs ++ [.rp] ∧ (∀ x ∈ vs, x = .rp)) := by
  have eq' : flatBP r ++ (flatBPTail rest ++ [.rp]) = s1 ++ (flatBP cp ++ b) := by
    simpa [List.append_assoc] using eq
  rcases List.append_eq_append_iff.mp eq' with ⟨us, hs1, hJ⟩ | ⟨us, hr, hcpb⟩
  · -- BEYOND: s1 = flatBP r ++ us, J = us ++ (flatBP cp ++ b)
    have usne : us ≠ [] := by
      rintro rfl
      simp only [List.nil_append] at hJ
      exact otx2_join_no_core_bB hJ
    refine Or.inl ⟨us, hs1.symm, usne, ?_⟩
    simpa [List.append_assoc] using hJ
  · -- IN: flatBP r = s1 ++ us, flatBP cp ++ b = us ++ J
    have usne : us ≠ [] := by
      rintro rfl
      simp only [List.nil_append] at hcpb
      exact otx2_join_no_core_bB hcpb.symm
    have hsplit2 : us ++ (flatBPTail rest ++ [.rp]) = flatBP cp ++ b := hcpb.symm
    rcases List.append_eq_append_iff.mp hsplit2 with ⟨vs, hcp, hJb⟩ | ⟨vs, husvs, hbvs⟩
    · -- B1: flatBP cp = us ++ vs, J = vs ++ b
      by_cases hvs : vs = []
      · subst vs
        simp only [List.append_nil] at hcp
        simp only [List.nil_append] at hJb
        have hrestnil : rest = [] := by
          cases rest with
          | nil => rfl
          | cons p ps =>
              exfalso
              have hcm : Sym.cm ∈ b := by rw [← hJb]; simp [flatBPTail]
              exact absurd (bR _ hcm) (by simp)
        subst rest
        refine Or.inr ⟨rfl, [], ?_, ?_, by simp⟩
        · rw [hcp]; simpa using hr
        · simpa [flatBPTail] using hJb.symm
      · exfalso
        have hs1nn : 0 ≤ flatSum s1 := flatBP_properPrefix_nonneg hr usne
        have husnn : 0 ≤ flatSum us := flatBP_properPrefix_nonneg hcp hvs
        have hrsum := flatBP_sum r
        rw [hr, flatSum_append] at hrsum
        omega
    · -- B2: us = flatBP cp ++ vs, b = vs ++ J  → RIGHT
      have hball : ∀ x ∈ vs ++ flatBPTail rest, x = .rp := by
        intro x hx
        apply bR
        rw [hbvs, ← List.append_assoc]
        exact List.mem_append.mpr (Or.inl hx)
      have hrestnil : rest = [] := by
        cases rest with
        | nil => rfl
        | cons p ps =>
            exfalso
            have hcm : Sym.cm ∈ vs ++ flatBPTail (p :: ps) :=
              List.mem_append.mpr (Or.inr (by simp [flatBPTail]))
            exact absurd (hball _ hcm) (by simp)
      subst rest
      have hbeq : b = vs ++ [.rp] := by simpa [flatBPTail] using hbvs
      have hvsRP : ∀ x ∈ vs, x = .rp := by
        intro x hx
        apply bR
        rw [hbeq]
        exact List.mem_append.mpr (Or.inl hx)
      refine Or.inr ⟨rfl, vs, ?_, hbeq, hvsRP⟩
      rw [hr, husvs]
      simp [List.append_assoc]

/-! ## `otx2_top_shape`（Isabelle `otx2_top_shape`, :114214）

1 項の `(s,b)` に対する頂点分類：`s` の先頭（または空）で、項が core そのものか、
単一 principal を通って降りるか、第 1 成分が `s` の真の prefix である tuple か。 -/

theorem otx2_top_shape {t : BT} {s b : List Sym} {cp : BP}
    (eq : flatBT t = s ++ flatBP cp ++ b)
    (bR : ∀ x ∈ b, x = .rp) :
    (s = [] ∧ b = [] ∧ t = .trm [cp])
    ∨ (∃ w s1 lb, s = .dsym w :: s1 ∧ t = .trm [.db w lb]
        ∧ flatBT lb = s1 ++ flatBP cp ++ b)
    ∨ (∃ s1 p0 q0 rest us, s = .lp :: s1 ∧ t = .trm (p0 :: q0 :: rest)
        ∧ flatBP p0 ++ us = s1 ∧ us ≠ []
        ∧ flatBPTail (q0 :: rest) ++ [.rp] = us ++ flatBP cp ++ b) := by
  rcases t with ⟨ps⟩
  cases ps with
  | nil =>
      exfalso
      have hlen := congrArg List.length eq
      have hge := flatBP_length_ge_two cp
      simp [flatBT] at hlen
      omega
  | cons p0 ps1 =>
      cases ps1 with
      | nil =>
          have fe : flatBP p0 = s ++ flatBP cp ++ b := by simpa [flatBT] using eq
          cases s with
          | nil =>
              simp only [List.nil_append] at fe
              obtain ⟨hpc, hb⟩ :=
                otx2_BP_prefix (xs := []) (ys := b) (by simpa using fe)
              subst hpc
              exact Or.inl ⟨rfl, hb.symm, rfl⟩
          | cons x s1 =>
              rcases p0 with ⟨w, lb⟩
              simp only [flatBP, List.cons_append] at fe
              injection fe with hx htl
              subst x
              exact Or.inr (Or.inl ⟨w, s1, lb, rfl, rfl, htl⟩)
      | cons q0 rest =>
          simp only [flatBT] at eq
          have sne : s ≠ [] := by
            rintro rfl
            rcases cp with ⟨uc, ac⟩
            simp only [List.nil_append, List.cons_append, flatBP] at eq
            injection eq with h
            simp at h
          cases s with
          | nil => exact absurd rfl sne
          | cons x s1 =>
              simp only [List.cons_append] at eq
              injection eq with hx heqin
              subst x
              rw [List.append_assoc] at heqin
              rcases otx2_peel heqin bR with ⟨us, hp0, husne, hJ⟩ | ⟨hnil, _⟩
              · exact Or.inr (Or.inr ⟨s1, p0, q0, rest, us, rfl, rfl, hp0, husne, hJ⟩)
              · exact absurd hnil (by simp)

/-! ## 2 項 join parse の補助（Isabelle `otx2_join3`, :114051 の 2 スロット版） -/

/-- 先頭成分を持つ join 文字列は `s = CM # s₁` から始まり、残りは peel 方程式。 -/
private theorem otx2_join_head_bB {r : BP} {rest : List BP} {s b : List Sym} {cp : BP}
    (h : flatBPTail (r :: rest) ++ [.rp] = s ++ flatBP cp ++ b) :
    ∃ s1, s = .cm :: s1 ∧
      flatBP r ++ (flatBPTail rest ++ [.rp]) = s1 ++ flatBP cp ++ b := by
  have hcons : flatBPTail (r :: rest) ++ [.rp]
      = .cm :: (flatBP r ++ (flatBPTail rest ++ [.rp])) := by
    simp [flatBPTail, List.cons_append, List.append_assoc]
  rw [hcons] at h
  cases s with
  | nil =>
      exfalso
      rcases cp with ⟨uc, ac⟩
      rw [List.nil_append] at h
      simp only [flatBP, List.cons_append] at h
      injection h with hhead
      simp at hhead
  | cons x s1 =>
      simp only [List.cons_append] at h
      injection h with hx htl
      subst x
      exact ⟨s1, rfl, htl⟩

/-- BEYOND/IN 混在は共有 prefix `s₁` の重なりで矛盾（Isabelle `mixed`, :114110）。 -/
private theorem otx2_mixed_bB {ra rb cpb : BP} {usa s1 vsb : List Sym}
    (A : flatBP ra ++ usa = s1) (B : usa ≠ [])
    (C : flatBP rb = s1 ++ flatBP cpb ++ vsb) : False := by
  have hEq : flatBP ra ++ (usa ++ (flatBP cpb ++ vsb)) = flatBP rb := by
    rw [← List.append_assoc, A, C, List.append_assoc]
  obtain ⟨_, hnil⟩ :=
    otx2_BP_prefix (xs := usa ++ (flatBP cpb ++ vsb)) (ys := []) (by simpa using hEq)
  cases usa with
  | nil => exact B rfl
  | cons a as => simp at hnil

/-- 2 項 join parse（Isabelle `otx2_join3`, :114051 の 2 スロット版）。 -/
private theorem otx2_join2_bB {cp1 cp2 : BP} (rs1 : List BP) :
    ∀ (rs2 : List BP) (s b : List Sym),
      flatBPTail rs1 ++ [.rp] = s ++ flatBP cp1 ++ b →
      flatBPTail rs2 ++ [.rp] = s ++ flatBP cp2 ++ b →
      (∀ x ∈ b, x = .rp) →
      (∃ qs, rs1 = qs ++ [cp1] ∧ rs2 = qs ++ [cp2])
      ∨ (∃ qs w lb1 lb2 sc bc,
          rs1 = qs ++ [.db w lb1] ∧ rs2 = qs ++ [.db w lb2]
          ∧ flatBT lb1 = sc ++ flatBP cp1 ++ bc ∧ flatBT lb2 = sc ++ flatBP cp2 ++ bc
          ∧ (∀ x ∈ bc, x = .rp)) := by
  induction rs1 with
  | nil =>
      intro rs2 s b h1 _ _
      exfalso
      have hlen := congrArg List.length h1
      have hge := flatBP_length_ge_two cp1
      simp [flatBPTail] at hlen
      omega
  | cons r1 rest1 ih =>
      intro rs2 s b h1 h2 hb
      obtain ⟨s1, hs, hpeel1⟩ := otx2_join_head_bB h1
      cases rs2 with
      | nil =>
          exfalso
          have hlen := congrArg List.length h2
          have hge := flatBP_length_ge_two cp2
          simp [flatBPTail] at hlen
          omega
      | cons r2 rest2 =>
          obtain ⟨s1', hs', hpeel2⟩ := otx2_join_head_bB h2
          rw [hs] at hs'
          injection hs' with _ hs1eq
          subst hs1eq
          rcases otx2_peel hpeel1 hb with
            ⟨us, hr1, husne, hJ1⟩ | ⟨hr1nil, vs1, hr1eq, hbeq1, hvs1⟩
          · rcases otx2_peel hpeel2 hb with
              ⟨us2, hr2, hus2ne, hJ2⟩ | ⟨_, vs2, hr2eq, _, _⟩
            · have hrr : flatBP r1 ++ us = flatBP r2 ++ us2 := by rw [hr1, hr2]
              obtain ⟨hr12, huseq⟩ := otx2_BP_prefix hrr
              subst hr12
              subst huseq
              rcases ih rest2 us b hJ1 hJ2 hb with
                ⟨qs, hq1, hq2⟩ | ⟨qs, w, lb1, lb2, sc, bc, hq1, hq2, F1, F2, hbc⟩
              · exact Or.inl ⟨r1 :: qs, by simp [hq1], by simp [hq2]⟩
              · exact Or.inr ⟨r1 :: qs, w, lb1, lb2, sc, bc,
                  by simp [hq1], by simp [hq2], F1, F2, hbc⟩
            · exact (otx2_mixed_bB hr1 husne hr2eq).elim
          · rcases otx2_peel hpeel2 hb with
              ⟨us2, hr2, hus2ne, _⟩ | ⟨hr2nil, vs2, hr2eq, hbeq2, hvs2⟩
            · exact (otx2_mixed_bB hr2 hus2ne hr1eq).elim
            · subst hr1nil
              subst hr2nil
              have hvv : vs1 = vs2 :=
                List.append_cancel_right (hbeq1.symm.trans hbeq2)
              subst hvv
              cases s1 with
              | nil =>
                  simp only [List.nil_append] at hr1eq hr2eq
                  obtain ⟨hrc1, hvnil⟩ :=
                    otx2_BP_prefix (xs := []) (ys := vs1) (by simpa using hr1eq)
                  subst hvnil
                  rw [List.append_nil] at hr2eq
                  have hrc2 : r2 = cp2 := flatBP_injective hr2eq
                  exact Or.inl ⟨[], by simp [hrc1], by simp [hrc2]⟩
              | cons x s2 =>
                  rcases r1 with ⟨w1, lb1⟩
                  rcases r2 with ⟨w2, lb2⟩
                  simp only [flatBP, List.cons_append] at hr1eq hr2eq
                  injection hr1eq with hx1 hlb1
                  injection hr2eq with hx2 hlb2
                  have hw : w2 = w1 := by
                    have h := hx2.trans hx1.symm
                    injection h
                  subst w2
                  exact Or.inr ⟨[], w1, lb1, lb2, s2, vs1, rfl, rfl, hlb1, hlb2, hvs1⟩

/-- 2 項 alignment（Isabelle `otx2_align3`, :114296 の 2 スロット版）: 共有ホール
`(s,b)` で 2 項が同頭 core を持つとき、共有 prefix `qs` 上で core が最終成分（case A）
か、共有最終成分 `D_w` を通ってより深い共有ホール `(sc,bc)` へ降りる（case B）。 -/
private theorem otx2_align2_bB {t t' : BT} {s b : List Sym} {cp1 cp2 : BP}
    (e1 : flatBT t = s ++ flatBP cp1 ++ b)
    (e2 : flatBT t' = s ++ flatBP cp2 ++ b)
    (bR : ∀ x ∈ b, x = .rp) :
    (∃ qs, t = .trm (qs ++ [cp1]) ∧ t' = .trm (qs ++ [cp2]))
    ∨ (∃ qs w lb1 lb2 sc bc,
        t = .trm (qs ++ [.db w lb1]) ∧ t' = .trm (qs ++ [.db w lb2])
        ∧ flatBT lb1 = sc ++ flatBP cp1 ++ bc ∧ flatBT lb2 = sc ++ flatBP cp2 ++ bc
        ∧ (∀ x ∈ bc, x = .rp)) := by
  rcases otx2_top_shape e1 bR with
    ⟨hsnil, _, ht⟩ | ⟨w, s1, lb1, hs, ht, hlb1⟩
      | ⟨s1, p0, q0, rest, us, hs, ht, hp0, husne, hJ1⟩
  · subst hsnil
    rcases otx2_top_shape e2 bR with
      ⟨_, _, ht'⟩ | ⟨_, _, _, hs', _, _⟩ | ⟨_, _, _, _, _, hs', _, _, _, _⟩
    · exact Or.inl ⟨[], by simp [ht], by simp [ht']⟩
    · simp at hs'
    · simp at hs'
  · subst hs
    rcases otx2_top_shape e2 bR with
      ⟨hs', _, _⟩ | ⟨w2, s1', lb2, hs', ht', hlb2⟩
        | ⟨_, _, _, _, _, hs', _, _, _, _⟩
    · simp at hs'
    · injection hs' with hw hs1
      injection hw with hww
      subst hww
      subst hs1
      exact Or.inr ⟨[], w, lb1, lb2, s1, b, by simp [ht], by simp [ht'], hlb1, hlb2, bR⟩
    · simp at hs'
  · subst hs
    rcases otx2_top_shape e2 bR with
      ⟨hs', _, _⟩ | ⟨_, _, _, hs', _, _⟩
        | ⟨s1', p0', q0', rest', us', hs', ht', hp0', husne', hJ2⟩
    · simp at hs'
    · simp at hs'
    · injection hs' with _ hs1eq
      subst hs1eq
      have hpp : flatBP p0 ++ us = flatBP p0' ++ us' := hp0.trans hp0'.symm
      obtain ⟨hp0eq, huseq⟩ := otx2_BP_prefix hpp
      subst hp0eq
      subst huseq
      rcases otx2_join2_bB (q0 :: rest) (q0' :: rest') us b hJ1 hJ2 bR with
        ⟨qs, hq1, hq2⟩ | ⟨qs, w, l1, l2, sc, bc, hq1, hq2, F1, F2, hbc⟩
      · exact Or.inl ⟨p0 :: qs, by simp [ht, hq1], by simp [ht', hq2]⟩
      · exact Or.inr ⟨p0 :: qs, w, l1, l2, sc, bc,
          by simp [ht, hq1], by simp [ht', hq2], F1, F2, hbc⟩

/-! ## MAIN Brick B: `od4_scbext_R`（Isabelle `od4_scbext_R`, `layerC`:414）

共有 scb 文脈を通した `od4R_op` の持ち上げ。2 項 align ＋ `od4sz_op`-降下帰納で、
最終成分に降りる各段を `od4R_op.deep` で組む。 -/

theorem od4_scbext_R {t t' : BT} {s b : List Sym} {v : ℕ∞} {ca ca' : BT}
    (e1 : flatBT t = s ++ flatBP (.db v ca) ++ b)
    (e2 : flatBT t' = s ++ flatBP (.db v ca') ++ b)
    (bR : ∀ x ∈ b, x = .rp)
    (site : od4R_op ca ca') : od4R_op t t' := by
  have key : ∀ n, ∀ (t t' : BT) (s b : List Sym),
      od4sz_op t = n →
      flatBT t = s ++ flatBP (.db v ca) ++ b →
      flatBT t' = s ++ flatBP (.db v ca') ++ b →
      (∀ x ∈ b, x = .rp) → od4R_op t t' := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t t' s b hn e1 e2 bR
      rcases otx2_align2_bB e1 e2 bR with
        ⟨qs, hqt, hqt'⟩ | ⟨qs, w, lb1, lb2, sc, bc, hqt, hqt', F1, F2, hbc⟩
      · subst hqt
        subst hqt'
        exact od4R_op.deep site qs v
      · subst hqt
        subst hqt'
        have happ : ∀ (xs ys : List BP),
            od4szList_op (xs ++ ys) = od4szList_op xs + od4szList_op ys := by
          intro xs ys
          induction xs with
          | nil => simp [od4szList_op]
          | cons z zs ihz => simp only [List.cons_append, od4szList_op, ihz]; omega
        have hlt : od4sz_op lb1 < n := by
          rw [← hn]
          show od4sz_op lb1 < od4sz_op (BT.trm (qs ++ [BP.db w lb1]))
          simp only [od4sz_op]
          rw [happ]
          simp only [od4szList_op, od4szP_op]
          omega
        exact od4R_op.deep (ih (od4sz_op lb1) hlt lb1 lb2 sc bc rfl F1 F2 hbc) qs w
  exact key (od4sz_op t) t t' s b rfl e1 e2 bR

#print axioms otx2_BP_prefix
#print axioms otx2_peel
#print axioms otx2_top_shape
#print axioms od4_scbext_R

end PSS
