import PSS.Defs

/-!
# §5.4 命題（ペア数列システム `F` の well-defined 性）

- 原文: `isabelle/pss_paper.thy` の `p_5_4_F_oper_dom`, `_val`
- 訂正: A1（再帰先の第 2 引数は `n` ではなく `f n`）
- Isabelle: `m_5_4_F_oper_dom`, `_val`
- 依存: `PSS.Defs`
- 状態: ✅ 証明済（sorry 0）
-/

namespace PSS

private theorem ftrace_value_unique
    {f : ℕ → ℕ} {M : PS} {n : ℕ} (s t : FTrace f M n) :
    FvalFromTrace s = FvalFromTrace t := by
  induction s with
  | base hs =>
      cases t with
      | base => rfl
      | step ht _ => omega
  | step hs s ih =>
      cases t with
      | base ht => omega
      | step _ t => exact ih t

private theorem Fval_eq_trace
    {f : ℕ → ℕ} {M : PS} {n : ℕ} (t : FTrace f M n) :
    Fval f M n = FvalFromTrace t := by
  unfold Fval
  rw [dif_pos (show Fdom f M n from ⟨t⟩)]
  exact ftrace_value_unique _ _

theorem F_oper_dom
    (f : ℕ → ℕ) (M : PS) (n : ℕ)
    (hM : TPS M) (hn : 1 ≤ n) (hlen : 1 < Lng M) :
    Fdom f M n ↔ Fdom f (oper M n) (f n) := by
  constructor
  · rintro ⟨t⟩
    cases t with
    | base hbase => omega
    | step _ t => exact ⟨t⟩
  · exact Fdom.step hlen

theorem F_oper_val
    (f : ℕ → ℕ) (M : PS) (n : ℕ)
    (hM : TPS M) (hn : 1 ≤ n) (hlen : 1 < Lng M)
    (hdom : Fdom f M n) :
    Fval f M n = Fval f (oper M n) (f n) := by
  obtain ⟨t⟩ := hdom
  cases t with
  | base hbase => omega
  | step _ t =>
      rw [Fval_eq_trace (.step hlen t), Fval_eq_trace t]
      rfl

#print axioms F_oper_dom
#print axioms F_oper_val

end PSS
