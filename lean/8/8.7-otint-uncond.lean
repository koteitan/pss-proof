import «8».«8.7-otint-transport»
import «8».«8.7-otpred-brickB»
import «7».«7.1-buchholz-fseq-closed»

/-!
# PSS.«8».«8.7-otint-uncond» — `oix_transport` の無条件化

ビルド済み `8.7-otint-transport` は
`oix_transport_holds : OixAlign3 → OixGControl → OixSandwichPrefix → OixSandwichDpt →
oix_transport` を証明する。本ファイルはその 4 本の generic Buchholz residual を
discharge し、無条件版 `oix_transport_uncond : oix_transport` を得る。

## 移植元 (isabelle/layerB/pss_wip.thy)

- `OixGControl`       ＝ Isa `b1x_G_control`（[Buc1] Lemma 3.4, wip:50342）。
- `OixSandwichPrefix` ＝ Isa `b1x_sandwich_prefix` (wip:50424)。
- `OixSandwichDpt`    ＝ Isa `b1x_sandwich_Dpt` (wip:50455)。
- `OixAlign3`         ＝ Isa `otx2_align3` (wip:114296)、`otx2_join3` (wip:114051) 経由。

## 討伐の手段

3 本の sandwich/G-control residual は `7.1-buchholz-fseq-closed` の PUBLIC twin
`G_control_bc`(:254) / `sandwich_prefix_bc`(:334) / `sandwich_Dprin_bc`(:379) と
verbatim 一致（`b1x_triG` は `triGBC` と defeq、`b1x_setle` は `setLeBC` と defeq）。
`OixAlign3` のみ本ファイルで flatinj toolkit を用いて移植: `8.7-otpred-brickB` の
PUBLIC な `otx2_BP_prefix`/`otx2_peel`/`otx2_top_shape` の上に 3 スロット版 join/align
（Isabelle `otx2_join3`/`otx2_align3` の逐語移植、私的 `_ou`）を組む。

## 依存（ビルド済みのみ import）

- `8.7-otint-transport`: `oix_transport`/`oix_transport_holds` と 4 residual の `def`。
  透過的に `8.7-otint-transport-prims`（`b1x_triG`/`b1x_setle`）。
- `8.7-otpred-brickB`: `otx2_BP_prefix`/`otx2_peel`/`otx2_top_shape`（PUBLIC）。
  透過的に `PSS.Flat`（`flatBP_injective`/`flatBP_length_ge_two`）。
- `7.1-buchholz-fseq-closed`: `triGBC`/`G_control_bc`/`sandwich_prefix_bc`/`sandwich_Dprin_bc`。

## 状態

🤖 GREEN 目標（sorry 0、axioms = propext/Classical.choice/Quot.sound）。私的接尾辞 `_ou`。
-/

namespace PSS

/-! ## 1. flatinj toolkit: 3 スロット join/align（Isabelle `otx2_join3`/`otx2_align3`） -/

/-- join 文字列の先頭剥がし（Isabelle 内部補題; `8.7-otpred-brickB` の private
`otx2_join_head_bB` の本ファイル用複製）。 -/
private theorem otx2_join_head_ou {r : BP} {rest : List BP} {s b : List Sym} {cp : BP}
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

/-- BEYOND/IN 混在は共有 prefix の重なりで矛盾（`otx2_mixed_bB` の複製）。 -/
private theorem otx2_mixed_ou {ra rb cpb : BP} {usa s1 vsb : List Sym}
    (A : flatBP ra ++ usa = s1) (B : usa ≠ [])
    (C : flatBP rb = s1 ++ flatBP cpb ++ vsb) : False := by
  have hEq : flatBP ra ++ (usa ++ (flatBP cpb ++ vsb)) = flatBP rb := by
    rw [← List.append_assoc, A, C, List.append_assoc]
  obtain ⟨_, hnil⟩ :=
    otx2_BP_prefix (xs := usa ++ (flatBP cpb ++ vsb)) (ys := []) (by simpa using hEq)
  cases usa with
  | nil => exact B rfl
  | cons a as => simp at hnil

/-- Isabelle `otx2_join3` (layerB/pss_wip.thy:114051)。3 スロット join parse。 -/
private theorem otx2_join3_ou {cp1 cp2 cp3 : BP} (rs1 : List BP) :
    ∀ (rs2 rs3 : List BP) (s b : List Sym),
      flatBPTail rs1 ++ [.rp] = s ++ flatBP cp1 ++ b →
      flatBPTail rs2 ++ [.rp] = s ++ flatBP cp2 ++ b →
      flatBPTail rs3 ++ [.rp] = s ++ flatBP cp3 ++ b →
      (∀ x ∈ b, x = .rp) →
      (∃ qs, rs1 = qs ++ [cp1] ∧ rs2 = qs ++ [cp2] ∧ rs3 = qs ++ [cp3])
      ∨ (∃ qs w lb1 lb2 lb3 sc bc,
          rs1 = qs ++ [.db w lb1] ∧ rs2 = qs ++ [.db w lb2] ∧ rs3 = qs ++ [.db w lb3]
          ∧ flatBT lb1 = sc ++ flatBP cp1 ++ bc ∧ flatBT lb2 = sc ++ flatBP cp2 ++ bc
          ∧ flatBT lb3 = sc ++ flatBP cp3 ++ bc
          ∧ (∀ x ∈ bc, x = .rp)) := by
  induction rs1 with
  | nil =>
      intro rs2 rs3 s b h1 h2 h3 hb
      exfalso
      have hlen := congrArg List.length h1
      have hge := flatBP_length_ge_two cp1
      simp [flatBPTail] at hlen
      omega
  | cons r1 rest1 ih =>
      intro rs2 rs3 s b h1 h2 h3 hb
      obtain ⟨s1, hs, hpeel1⟩ := otx2_join_head_ou h1
      cases rs2 with
      | nil =>
          exfalso
          have hlen := congrArg List.length h2
          have hge := flatBP_length_ge_two cp2
          simp [flatBPTail] at hlen
          omega
      | cons r2 rest2 =>
          cases rs3 with
          | nil =>
              exfalso
              have hlen := congrArg List.length h3
              have hge := flatBP_length_ge_two cp3
              simp [flatBPTail] at hlen
              omega
          | cons r3 rest3 =>
              obtain ⟨s1', hs', hpeel2⟩ := otx2_join_head_ou h2
              obtain ⟨s1'', hs'', hpeel3⟩ := otx2_join_head_ou h3
              rw [hs] at hs' hs''
              injection hs' with _ hs1eq2
              injection hs'' with _ hs1eq3
              subst hs1eq2
              subst hs1eq3
              rcases otx2_peel hpeel1 hb with
                ⟨us, hr1, husne, hJ1⟩ | ⟨hr1nil, vs1, hr1eq, hbeq1, hvs1⟩
              · -- BEYOND for r1: r2, r3 must be BEYOND too
                rcases otx2_peel hpeel2 hb with
                  ⟨us2, hr2, hus2ne, hJ2⟩ | ⟨_, vs2, hr2eq, _, _⟩
                · rcases otx2_peel hpeel3 hb with
                    ⟨us3, hr3, hus3ne, hJ3⟩ | ⟨_, vs3, hr3eq, _, _⟩
                  · -- BEYOND^3: peel shared component and recurse
                    have hrr12 : flatBP r1 ++ us = flatBP r2 ++ us2 := by rw [hr1, hr2]
                    obtain ⟨hr12, huseq12⟩ := otx2_BP_prefix hrr12
                    subst hr12
                    subst huseq12
                    have hrr13 : flatBP r1 ++ us = flatBP r3 ++ us3 := by rw [hr1, hr3]
                    obtain ⟨hr13, huseq13⟩ := otx2_BP_prefix hrr13
                    subst hr13
                    subst huseq13
                    rcases ih rest2 rest3 us b hJ1 hJ2 hJ3 hb with
                      ⟨qs, hq1, hq2, hq3⟩ |
                      ⟨qs, w, lb1, lb2, lb3, sc, bc, hq1, hq2, hq3, F1, F2, F3, hbc⟩
                    · exact Or.inl ⟨r1 :: qs, by simp [hq1], by simp [hq2], by simp [hq3]⟩
                    · exact Or.inr ⟨r1 :: qs, w, lb1, lb2, lb3, sc, bc,
                        by simp [hq1], by simp [hq2], by simp [hq3], F1, F2, F3, hbc⟩
                  · exact (otx2_mixed_ou hr1 husne hr3eq).elim
                · exact (otx2_mixed_ou hr1 husne hr2eq).elim
              · -- IN for r1 (rest1 = []): r2, r3 must be IN too
                rcases otx2_peel hpeel2 hb with
                  ⟨us2, hr2, hus2ne, _⟩ | ⟨hr2nil, vs2, hr2eq, hbeq2, hvs2⟩
                · exact (otx2_mixed_ou hr2 hus2ne hr1eq).elim
                · rcases otx2_peel hpeel3 hb with
                    ⟨us3, hr3, hus3ne, _⟩ | ⟨hr3nil, vs3, hr3eq, hbeq3, hvs3⟩
                  · exact (otx2_mixed_ou hr3 hus3ne hr1eq).elim
                  · -- IN^3: the peeled components are the LAST ones; bottom out
                    subst hr1nil
                    subst hr2nil
                    subst hr3nil
                    have hvv2 : vs1 = vs2 :=
                      List.append_cancel_right (hbeq1.symm.trans hbeq2)
                    have hvv3 : vs1 = vs3 :=
                      List.append_cancel_right (hbeq1.symm.trans hbeq3)
                    subst hvv2
                    subst hvv3
                    cases s1 with
                    | nil =>
                        simp only [List.nil_append] at hr1eq hr2eq hr3eq
                        obtain ⟨hrc1, hvnil⟩ :=
                          otx2_BP_prefix (xs := []) (ys := vs1) (by simpa using hr1eq)
                        subst hvnil
                        rw [List.append_nil] at hr2eq hr3eq
                        have hrc2 : r2 = cp2 := flatBP_injective hr2eq
                        have hrc3 : r3 = cp3 := flatBP_injective hr3eq
                        exact Or.inl ⟨[], by simp [hrc1], by simp [hrc2], by simp [hrc3]⟩
                    | cons x s2 =>
                        rcases r1 with ⟨w1, lb1⟩
                        rcases r2 with ⟨w2, lb2⟩
                        rcases r3 with ⟨w3, lb3⟩
                        simp only [flatBP, List.cons_append] at hr1eq hr2eq hr3eq
                        injection hr1eq with hx1 hlb1
                        injection hr2eq with hx2 hlb2
                        injection hr3eq with hx3 hlb3
                        have hw2 : w2 = w1 := by
                          have h := hx2.trans hx1.symm; injection h
                        have hw3 : w3 = w1 := by
                          have h := hx3.trans hx1.symm; injection h
                        subst w2
                        subst w3
                        exact Or.inr ⟨[], w1, lb1, lb2, lb3, s2, vs1, rfl, rfl, rfl,
                          hlb1, hlb2, hlb3, hvs1⟩

/-- Isabelle `otx2_align3` (layerB/pss_wip.thy:114296)。共有ホール `(s,b)` で 3 項が
同頭 core を持つとき、共有 prefix `qs` 上で core が最終成分（case A）か、共有最終成分
`D_w` を通ってより深い共有ホール `(sc,bc)` へ降りる（case B）。 -/
private theorem otx2_align3_ou {t1 t2 t3 : BT} {s b : List Sym} {cp1 cp2 cp3 : BP}
    (e1 : flatBT t1 = s ++ flatBP cp1 ++ b)
    (e2 : flatBT t2 = s ++ flatBP cp2 ++ b)
    (e3 : flatBT t3 = s ++ flatBP cp3 ++ b)
    (bR : ∀ x ∈ b, x = .rp) :
    (∃ qs, t1 = .trm (qs ++ [cp1]) ∧ t2 = .trm (qs ++ [cp2]) ∧ t3 = .trm (qs ++ [cp3]))
    ∨ (∃ qs w lb1 lb2 lb3 sc bc,
        t1 = .trm (qs ++ [.db w lb1]) ∧ t2 = .trm (qs ++ [.db w lb2])
        ∧ t3 = .trm (qs ++ [.db w lb3])
        ∧ flatBT lb1 = sc ++ flatBP cp1 ++ bc ∧ flatBT lb2 = sc ++ flatBP cp2 ++ bc
        ∧ flatBT lb3 = sc ++ flatBP cp3 ++ bc
        ∧ (∀ x ∈ bc, x = .rp)) := by
  rcases otx2_top_shape e1 bR with
    ⟨hsnil, _, ht1⟩ | ⟨w, s1, lb1, hs, ht1, hlb1⟩
      | ⟨s1, p0, q0, rest, us, hs, ht1, hp0, husne, hJ1⟩
  · -- s = []: all three are bare cores
    subst hsnil
    rcases otx2_top_shape e2 bR with
      ⟨_, _, ht2⟩ | ⟨_, _, _, hs2, _, _⟩ | ⟨_, _, _, _, _, hs2, _, _, _, _⟩
    · rcases otx2_top_shape e3 bR with
        ⟨_, _, ht3⟩ | ⟨_, _, _, hs3, _, _⟩ | ⟨_, _, _, _, _, hs3, _, _, _, _⟩
      · exact Or.inl ⟨[], by simp [ht1], by simp [ht2], by simp [ht3]⟩
      · simp at hs3
      · simp at hs3
    · simp at hs2
    · simp at hs2
  · -- s = Dsym w :: s1: all three descend through a single principal
    subst hs
    rcases otx2_top_shape e2 bR with
      ⟨hs2, _, _⟩ | ⟨w2, s1', lb2, hs2, ht2, hlb2⟩
        | ⟨_, _, _, _, _, hs2, _, _, _, _⟩
    · simp at hs2
    · injection hs2 with hw2 hs1eq2
      injection hw2 with hww2
      subst hww2
      subst hs1eq2
      rcases otx2_top_shape e3 bR with
        ⟨hs3, _, _⟩ | ⟨w3, s1'', lb3, hs3, ht3, hlb3⟩
          | ⟨_, _, _, _, _, hs3, _, _, _, _⟩
      · simp at hs3
      · injection hs3 with hw3 hs1eq3
        injection hw3 with hww3
        subst hww3
        subst hs1eq3
        exact Or.inr ⟨[], w, lb1, lb2, lb3, s1, b,
          by simp [ht1], by simp [ht2], by simp [ht3], hlb1, hlb2, hlb3, bR⟩
      · simp at hs3
    · simp at hs2
  · -- s = LP :: s1: all three are tuples; peel shared first component, hand to join3
    subst hs
    rcases otx2_top_shape e2 bR with
      ⟨hs2, _, _⟩ | ⟨_, _, _, hs2, _, _⟩
        | ⟨s1', p0', q0', rest', us', hs2, ht2, hp0', husne', hJ2⟩
    · simp at hs2
    · simp at hs2
    · injection hs2 with _ hs1eq2
      subst hs1eq2
      rcases otx2_top_shape e3 bR with
        ⟨hs3, _, _⟩ | ⟨_, _, _, hs3, _, _⟩
          | ⟨s1'', p0'', q0'', rest'', us'', hs3, ht3, hp0'', husne'', hJ3⟩
      · simp at hs3
      · simp at hs3
      · injection hs3 with _ hs1eq3
        subst hs1eq3
        have hpp12 : flatBP p0 ++ us = flatBP p0' ++ us' := hp0.trans hp0'.symm
        obtain ⟨hp0eq12, huseq12⟩ := otx2_BP_prefix hpp12
        subst hp0eq12
        subst huseq12
        have hpp13 : flatBP p0 ++ us = flatBP p0'' ++ us'' := hp0.trans hp0''.symm
        obtain ⟨hp0eq13, huseq13⟩ := otx2_BP_prefix hpp13
        subst hp0eq13
        subst huseq13
        rcases otx2_join3_ou (q0 :: rest) (q0' :: rest') (q0'' :: rest'') us b
            hJ1 hJ2 hJ3 bR with
          ⟨qs, hq1, hq2, hq3⟩ |
          ⟨qs, w, l1, l2, l3, sc, bc, hq1, hq2, hq3, F1, F2, F3, hbc⟩
        · exact Or.inl ⟨p0 :: qs, by simp [ht1, hq1], by simp [ht2, hq2],
            by simp [ht3, hq3]⟩
        · exact Or.inr ⟨p0 :: qs, w, l1, l2, l3, sc, bc,
            by simp [ht1, hq1], by simp [ht2, hq2], by simp [ht3, hq3], F1, F2, F3, hbc⟩

/-! ## 2. 4 residual の discharge（house pattern: Prop を型に据える） -/

/-- `OixAlign3` を discharge（Isabelle `otx2_align3`）。 -/
theorem OixAlign3_holds : OixAlign3 := by
  intro t1 t2 t3 s b cp1 cp2 cp3 e1 e2 e3 bR
  exact otx2_align3_ou e1 e2 e3 bR

/-- `OixGControl` を discharge（`7.1` の `G_control_bc`；`b1x_triG` は `triGBC` と defeq）。 -/
theorem OixGControl_holds : OixGControl := by
  intro z b a u htri hba hGa hGz
  have htri' : triGBC z b a := htri
  exact G_control_bc htri' hba hGa hGz

/-- `OixSandwichPrefix` を discharge（`7.1` の `sandwich_prefix_bc` と verbatim 一致）。 -/
theorem OixSandwichPrefix_holds : OixSandwichPrefix := by
  intro ps xs ys c h1 h2
  exact sandwich_prefix_bc ps xs ys c h1 h2

/-- `OixSandwichDpt` を discharge（`7.1` の `sandwich_Dprin_bc` と verbatim 一致）。 -/
theorem OixSandwichDpt_holds : OixSandwichDpt := by
  intro v x y c h1 h2
  exact sandwich_Dprin_bc h1 h2

/-! ## 3. 無条件版 `oix_transport` -/

/-- **`oix_transport` 無条件化**。`8.7-otint-transport` の
`oix_transport_holds` に 4 residual の `_holds` を供給。 -/
theorem oix_transport_uncond : oix_transport :=
  oix_transport_holds OixAlign3_holds OixGControl_holds
    OixSandwichPrefix_holds OixSandwichDpt_holds

#print axioms OixAlign3_holds
#print axioms OixGControl_holds
#print axioms OixSandwichPrefix_holds
#print axioms OixSandwichDpt_holds
#print axioms oix_transport_uncond

end PSS
