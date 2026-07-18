import «7».«7.4-Mark-Trans-repr»

/-!
# §7.3 命題（右端第2基点の `Mark` の基本性質）— content.md 2334

- 原文: `tmp/content.md` の同名命題（右端第2基点 `m = j₋₁ = transJm1 M`）
- Isabelle: `m_7_3_Mark_rightmost2`（`isabelle/layerB/pss_wip.thy:6229`）
- 依存: `Mark_transJm1_eq_transC2`（`lean/7/7.4-Mark-Trans-repr.lean:231`。
  §7.4 側に置かれているが実体は本 §7.3 命題の内容）を、原文の
  `RT_PS / PT_PS / transJ1 / transT1` 仮定に 1:1 で読み替えて公開する。
- 状態: ✅（`sorry` 0、公理は `propext, Classical.choice, Quot.sound` のみ）

第2基点 `m = j₋₁ = transJm1 M = Adm M (transJ0 M)` では、外科手術（surgery）
分岐で置換される成分 `c₀ = Mark (Pred M) m` が、照合対象の `c₁ = Mark (Pred M)
(Adm M j')` とちょうど一致する（`j' = lastParent M = transJ0 M`）。よって scb
自己分解は自明な `([], [])` となり、外科手術は `c₂ = transC2 M` を逐語で返す。
この論法は `Mark_transJm1_eq_transC2` が既に実行済み。

Isabelle 仮定 → Lean 綴り（PT_PS = T_PS ∩ monoT の慣例）:
* `MR : M ∈ RT_PS`   → `MR : RTPS M`
* `MP : M ∈ PT_PS`   → `MP : monoT M = true`（T_PS 部は `RTPS M` から出る）
* `J1pos : transJ1 M > 0` → `J1pos : 0 < transJ1 M`（`transJ1 M = lastIdx M = Lng M - 1`）
* `T1 : transT1 M ≠ 0_B`  → `T1 : transT1 M ≠ BZero`（`transT1 M = Trans (Pred M)`）
-/

namespace PSS

/-- §7.3 命題（右端第2基点の `Mark` の基本性質）。
Isabelle `m_7_3_Mark_rightmost2`（`layerB/pss_wip.thy:6229`）の逐語移植。
第2基点 `transJm1 M` での印付き翻訳は外科手術成分 `transC2 M` に一致する。 -/
theorem m_7_3_Mark_rightmost2 (M : PS)
    (MR : RTPS M) (MP : monoT M = true)
    (J1pos : 0 < transJ1 M) (T1 : transT1 M ≠ BZero) :
    Mark M (transJm1 M) = transC2 M := by
  -- `transJ1 M = lastIdx M = Lng M - 1`、ゆえに `0 < transJ1 M ⟹ 1 < Lng M`
  have hlen : 1 < Lng M := by
    have h : 0 < Lng M - 1 := by simpa [transJ1, lastIdx] using J1pos
    omega
  -- `transT1 M = Trans (Pred M)`
  have hT1 : Trans (Pred M) ≠ BZero := by simpa [transT1] using T1
  exact Mark_transJm1_eq_transC2 M MR MP hlen hT1

#print axioms m_7_3_Mark_rightmost2

end PSS
