import PSS.Trans

/-!
# §8.2 部分表現の単項成分と `Pred` — clause (3)/(4) assembly from the witness

- 原文: `tmp/content.md` L3360 付近（§8.2 補題「部分表現の単項成分と Pred の関係」、
  4 clause 場合分けの clause (3)/(4)）。訂正: なし。
- Isabelle (`isabelle/layerB/pss_wip.thy`):
  - `ex1_Dpt_addBT_triple` (25249) → 私的 `ex1_Dprin_addBT_triple_s34`
  - `m_8_2_subexpr_component_Pred_clause34_of_witness` (25365)
    → `subexpr_component_Pred_clause34_of_witness`
- 公開定理: `subexpr_component_Pred_clause34_of_witness`。
- 内容: Admpos 枝の witness 消費。witness の 2 等式
  `Trans (Pred M) = D_{M_{1,0}}(t₁ + D_w t₂)`,
  `Trans M = D_{M_{1,0}}(t₁ + D_w t₃)`
  （`w ∈ {M_{1,j₁'}, M_{1,j₀'}}`, `j₁' = FirstNodes(M)_{J₁}`,
  `j₀' = Joints(M)_{J₁}`, `J₁ = Lng(Br M) - 1`）から keystone の
  4-clause 選言が従う（`w = M_{1,j₁'}` なら clause (3)、`w = M_{1,j₀'}` なら
  clause (4)）。一意性の三つ組 packager は `Dprin` 単射＋`addBT` 末尾
  principal 単射（`List.append_inj'`）による BT 上の純代数（domain 仮定なし）。
- 依存: PSS core（`PSS.Trans` 経由）のみ。
- 私的補助（suffix `_s34`）: `Dprin_inj_s34` / `addBT_snoc_Dprin_inj_s34`
  （8.2-subexpr-adm0-cores の `_sc` 版の複製、あちらは private のため）,
  `ex1_Dprin_addBT_triple_s34`。
- 状態: ✅ sorry 0（本ファイル単独で green）。
-/

namespace PSS

/-! ## 私的補助: `Dprin`/`addBT` の単射性（Isabelle は `Dpt` 単射＋
`append_eq_append_conv`; 8.2-subexpr-adm0-cores の `_sc` パターンの複製） -/

private theorem Dprin_inj_s34 {v w : ℕ∞} {a b : BT}
    (h : Dprin v a = Dprin w b) : v = w ∧ a = b := by
  simp only [Dprin, BT.trm.injEq, List.cons.injEq, BP.db.injEq, and_true] at h
  exact h

private theorem addBT_snoc_Dprin_inj_s34 {t t' : BT} {v v' : ℕ∞} {b b' : BT}
    (h : addBT t (Dprin v b) = addBT t' (Dprin v' b')) :
    t = t' ∧ v = v' ∧ b = b' := by
  rcases t with ⟨as⟩
  rcases t' with ⟨bs⟩
  simp only [addBT, Dprin, BT.trm.injEq] at h
  obtain ⟨h1, h2⟩ := List.append_inj' h rfl
  simp only [List.cons.injEq, BP.db.injEq, and_true] at h2
  exact ⟨congrArg BT.trm h1, h2.1, h2.2⟩

/-! ## 私的補助: ∃!-triple packager（Isabelle `ex1_Dpt_addBT_triple`,
layerB 25249）

witness の 2 等式 `TP = D_v(t₁ + D_w t₂)`, `TM = D_v(t₁ + D_w t₃)`（同じ外側
head `v`・同じ共有 body-prefix `t₁`・同じ split head `w`）から、三つ組
`t₁₂₃ = (t₁, t₂, t₃)` は一意。各 split-head principal `D_w …` は body の
単一末尾成分なので、`addBT` 末尾 principal 単射で共有 prefix `t₁` と
body `t₂`/`t₃` が読み取れる。 -/

private theorem ex1_Dprin_addBT_triple_s34 {TP TM : BT} {v w : ℕ∞}
    {t1 t2 t3 : BT}
    (hP : TP = Dprin v (addBT t1 (Dprin w t2)))
    (hM : TM = Dprin v (addBT t1 (Dprin w t3))) :
    ∃! t123 : BT × BT × BT,
      TP = Dprin v (addBT t123.1 (Dprin w t123.2.1)) ∧
      TM = Dprin v (addBT t123.1 (Dprin w t123.2.2)) := by
  refine ⟨(t1, t2, t3), ⟨hP, hM⟩, ?_⟩
  rintro ⟨a, b, c⟩ ⟨haP, haM⟩
  -- `a = t₁`, `b = t₂` from `TP`
  have h1 := (Dprin_inj_s34 (haP.symm.trans hP)).2
  obtain ⟨ha, -, hb⟩ := addBT_snoc_Dprin_inj_s34 h1
  -- `c = t₃` from `TM`
  have h2 := (Dprin_inj_s34 (haM.symm.trans hM)).2
  obtain ⟨-, -, hc⟩ := addBT_snoc_Dprin_inj_s34 h2
  simp only [Prod.mk.injEq]
  exact ⟨ha, hb, hc⟩

/-! ## 公開定理: clause (3)/(4) の witness からの組み立て
（Isabelle `m_8_2_subexpr_component_Pred_clause34_of_witness`, layerB 25365）

`j₁ = Lng M - 1`, `J₁ = Lng(Br M) - 1`, `j₀' = Joints(M)_{J₁}`,
`j₁' = FirstNodes(M)_{J₁}` について、witness 選言 `w = M_{1,j₁'} ∨ w = M_{1,j₀'}`
と witness 等式 2 本から keystone の 4-clause 選言が従う。 -/

theorem subexpr_component_Pred_clause34_of_witness (M : PS) (w : ℕ)
    (t1 t2 t3 : BT)
    (wsplit : w = entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)
            ∨ w = entry M 1 ((Joints M).getD ((Br M).length - 1) 0))
    (witP : Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞)
        (addBT t1 (Dprin (w : ℕ∞) t2)))
    (witM : Trans M = Dprin (entry M 1 0 : ℕ∞)
        (addBT t1 (Dprin (w : ℕ∞) t3))) :
    ((FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1
      ∧ (TrMax M = 0 ∨ (Joints M).getD ((Br M).length - 1) 0 < TrMax M)
      ∧ (entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0)
            = entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)
          ∨ adm M ((Joints M).getD ((Br M).length - 1) 0) = true)
      ∧ ∃! t₁ : BT,
          Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) t₁ ∧
          Trans M = Dprin (entry M 1 0 : ℕ∞)
            (addBT t₁ (Dprin
              (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
              BZero)))
    ∨ ((FirstNodes M).getD ((Br M).length - 1) 0 = Lng M - 1
      ∧ entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0)
          < entry M 0 ((FirstNodes M).getD ((Br M).length - 1) 0)
      ∧ adm M ((Joints M).getD ((Br M).length - 1) 0) = false
      ∧ ∃! t12 : BT × BT,
          Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞) t12.1 ∧
          Trans M = Dprin (entry M 1 0 : ℕ∞)
            (addBT t12.1 (Dprin
              (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
              t12.2)))
    ∨ (∃! t123 : BT × BT × BT,
        Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞)
          (addBT t123.1 (Dprin
            (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
            t123.2.1)) ∧
        Trans M = Dprin (entry M 1 0 : ℕ∞)
          (addBT t123.1 (Dprin
            (entry M 1 ((FirstNodes M).getD ((Br M).length - 1) 0) : ℕ∞)
            t123.2.2)))
    ∨ (∃! t123 : BT × BT × BT,
        Trans (Pred M) = Dprin (entry M 1 0 : ℕ∞)
          (addBT t123.1 (Dprin
            (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
            t123.2.1)) ∧
        Trans M = Dprin (entry M 1 0 : ℕ∞)
          (addBT t123.1 (Dprin
            (entry M 1 ((Joints M).getD ((Br M).length - 1) 0) : ℕ∞)
            t123.2.2))) := by
  rcases wsplit with w1 | w0
  · -- `w = M_{1,j₁'}` → clause (3)
    subst w1
    exact Or.inr (Or.inr (Or.inl
      (ex1_Dprin_addBT_triple_s34 witP witM)))
  · -- `w = M_{1,j₀'}` → clause (4)
    subst w0
    exact Or.inr (Or.inr (Or.inr
      (ex1_Dprin_addBT_triple_s34 witP witM)))

#print axioms subexpr_component_Pred_clause34_of_witness

end PSS
