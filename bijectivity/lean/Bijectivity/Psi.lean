import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Aleph
import «Buchholz-1986».«Buchholz-1986-2.2»

/-!
# Buchholz の順序数崩壊関数 \(ψ_u\)（構成中）

原文が [4]（= [Buc1]）から引く \(ψ_u\)、\(Ω_u\)、評価写像 \(o\) を、引用ではなく
**順序数として定義**するためのファイル。目的は主定理の値域
\(\{α\midα<ψ_0ψ_ω0\}\) の \(ψ_0ψ_ω0\) を、こちらで構成した順序型ではなく
Buchholz の \(ψ_0(ψ_ω(0))\) そのものにすること。

[Buc1] §2 の定義:

\[
C_u^0(α)=Ω_u\cup\{0\},\qquad
C_u^{n+1}(α)=C_u^n(α)\cup\{γ+δ\midγ,δ\in C_u^n(α)\}
\cup\{ψ_v(ξ)\midξ\in C_u^n(α)\capα,\ v\leω\}
\]
\[
C_u(α)=\bigcup_{n<ω}C_u^n(α),\qquad ψ_u(α)=\min\{β\midβ\notin C_u(α)\}
\]

ここでは \(C_u(α)\) を段階の合併ではなく、同じものを生成する帰納的述語
`CGen` として定める（`add` と `psi` の閉包規則が段階を吸収する）。

## 残りの工程

| | 内容 | 状態 |
|---|---|---|
| (1) | \(ψ_u(α)\) の存在（\(C_u(α)\neq\mathrm{Ord}\)、基数評価 \(|C_u(α)|<Ω_{u+1}\)） | `sorry` |
| (2) | \(C_u(α)\cap Ω_{u+1}=ψ_u(α)\)（崩壊の要） | `sorry` |
| (3) | [Buc1] Lemma 2.1（評価 \(o\) が順序を保つ） | 未着手 |
| (4) | [Buc1] Lemma 2.2(c)（像が \(ψ_0ψ_ω0\) の始切片） | 未着手 |

(1)(2) が済むと、単調性・\(Ω_u\leψ_u(α)<Ω_{u+1}\) 等はここから出る。
-/

namespace Bijectivity

open Ordinal Cardinal

/-! ## \(Ω_u\) -/

/-- \(Ω_0=1\)、\(Ω_u=ℵ_u\)（\(u>0\)）、\(Ω_ω=ℵ_ω\)。 -/
noncomputable def Om (u : ℕ∞) : Ordinal.{0} :=
  match u with
  | ⊤ => (ℵ_ Ordinal.omega0).ord
  | (n : ℕ) => if n = 0 then 1 else (ℵ_ (n : Ordinal)).ord

@[simp] theorem Om_zero : Om 0 = 1 := rfl

@[simp] theorem Om_top : Om ⊤ = (ℵ_ Ordinal.omega0).ord := rfl

/-- \(Ω_{u+1}\)。`ℕ∞` では `⊤ + 1 = ⊤` なので `Om (u + 1)` では書けない。 -/
noncomputable def OmSucc (u : ℕ∞) : Ordinal.{0} :=
  match u with
  | ⊤ => (ℵ_ (Ordinal.omega0 + 1)).ord
  | (n : ℕ) => (ℵ_ ((n : Ordinal) + 1)).ord

theorem Om_lt_OmSucc (u : ℕ∞) : Om u < OmSucc u := by
  have mono : ∀ x y : Ordinal, x < y → (ℵ_ x).ord < (ℵ_ y).ord :=
    fun _ _ h => Cardinal.ord_lt_ord.2 (Cardinal.aleph_lt_aleph.2 h)
  have one_lt : ∀ x : Ordinal, (1 : Ordinal) < (ℵ_ x).ord := by
    intro x
    refine lt_of_lt_of_le ?_ (Cardinal.ord_le_ord.2 (Cardinal.aleph0_le_aleph x))
    simp [Cardinal.ord_aleph0]
  cases u with
  | top =>
    exact mono _ _ (by simp)
  | coe n =>
    by_cases h : n = 0
    · subst h
      simpa [Om, OmSucc] using one_lt ((0 : ℕ) + 1 : Ordinal)
    · simp only [Om, OmSucc, if_neg h]
      exact mono _ _ (by simp)

/-! ## \(C_u(α)\) -/

/-- \(C_u(α)\) を生成する帰納的述語。`f` は「\(α\) 未満の引数での \(ψ\)」。 -/
inductive CGen (u : ℕ∞) (a : Ordinal.{0})
    (f : ∀ x : Ordinal.{0}, x < a → ℕ∞ → Ordinal.{0}) : Ordinal.{0} → Prop
  | lt_Om {b} : b < Om u → CGen u a f b
  | zero : CGen u a f 0
  | add {x y} : CGen u a f x → CGen u a f y → CGen u a f (x + y)
  | psi {x} (hx : x < a) (v : ℕ∞) : CGen u a f x → CGen u a f (f x hx v)

/-- \(ψ\) の本体。`a` に関する整礎再帰。 -/
noncomputable def psiStep (a : Ordinal.{0})
    (f : ∀ x : Ordinal.{0}, x < a → ℕ∞ → Ordinal.{0}) : ℕ∞ → Ordinal.{0} :=
  fun u => sInf {b | ¬ CGen u a f b}

/-- \(ψ_u(α)\)。 -/
noncomputable def psi (u : ℕ∞) (a : Ordinal.{0}) : Ordinal.{0} :=
  Ordinal.lt_wf.fix psiStep a u

/-- \(C_u(α)\)。 -/
def CSet (u : ℕ∞) (a : Ordinal.{0}) : Set Ordinal.{0} :=
  {b | CGen u a (fun x _ v => psi v x) b}

theorem psi_eq (u : ℕ∞) (a : Ordinal.{0}) :
    psi u a = sInf {b | b ∉ CSet u a} := by
  rw [psi, Ordinal.lt_wf.fix_eq]
  rfl

/-! ## (1) 存在 -/

/-- \(C_u(α)\) は順序数全体ではない。基数評価 \(|C_u(α)|<Ω_{u+1}\) から。 -/
theorem CSet_ne_univ (u : ℕ∞) (a : Ordinal.{0}) : ∃ b, b ∉ CSet u a := by
  sorry

theorem psi_not_mem (u : ℕ∞) (a : Ordinal.{0}) : psi u a ∉ CSet u a := by
  rw [psi_eq]
  exact csInf_mem (CSet_ne_univ u a)

theorem lt_psi_mem {u : ℕ∞} {a b : Ordinal.{0}} (h : b < psi u a) : b ∈ CSet u a := by
  by_contra hb
  rw [psi_eq] at h
  exact absurd (csInf_le' hb) (not_le.2 h)

/-! ## (2) 崩壊の要 -/

/-- \(C_u(α)\cap Ω_{u+1}=ψ_u(α)\)。 -/
theorem CSet_inter_OmSucc (u : ℕ∞) (a : Ordinal.{0}) :
    CSet u a ∩ {b | b < OmSucc u} = {b | b < psi u a} := by
  sorry

/-! ## ここから先（未着手）

- 評価写像 \(o:BT\to\mathrm{Ord}\)、\(o(D_ua)=ψ_u(o(a))\)、\(o(t_0+t_1)=o(t_0)+o(t_1)\)
- [Buc1] Lemma 2.1: `s ∈ OT → t ∈ OT → (lessBT s t = true ↔ o s < o t)`
- [Buc1] Lemma 2.2(c): `o '' {t ∈ OT | lessBT t DzeroDomegaZero} = {α | α < psi 0 (psi ⊤ 0)}`
-/

end Bijectivity
