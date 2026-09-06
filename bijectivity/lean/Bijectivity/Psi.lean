import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Ordinal.Principal
import «Buchholz-1986».«Buchholz-1986-2.1-order»
import «Buchholz-1986».«Buchholz-1986-2.2»
import «Buchholz-rel-ord».«Buchholz-rel-ord-6»

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
| (1) | \(ψ_u(α)\) の存在（\(C_u(α)\neq\mathrm{Ord}\)、基数評価 \(|C_u(α)|<Ω_{u+1}\)） | **済** |
| (2) | \(C_u(α)\cap Ω_{u+1}=ψ_u(α)\)（崩壊の要） | **済** |
| (3) | 評価写像 \(o\) の定義と \(G_u\to C_u\) の橋渡し | **済** |
| (4) | [Buc1] Lemma 2.1（\(o\) が順序を保つ、単射性つき） | **済** |
| (5) | [Buc1] Lemma 2.2(c) の還元と易しい向き | **済** |
| (6) | 加法標準形（項の正規化和 `naddBT`） | **済** |
| (7) | `surj_core` の `0` と `+` の場合（`surj_core_of_psi`） | **済** |
| (8) | `surj_core` の \(ψ\) の場合 | `sorry`（残り 1 本） |

閉包は [Buc1] の条件つき定義（`psi` 生成規則に \(ξ\in C_u(ξ)\)）を採っている。

(1)(2) から出たもの: \(Ω_u\leψ_u(α)<Ω_{u+1}\)、\(ψ\) の広義・狭義単調性、
\(ψ_u(α)\) が加法的 principal であること。
-/

namespace Bijectivity

open Ordinal Cardinal PSS

/-! ## \(Ω_u\) -/

/-- \(Ω_0=1\)、\(Ω_u=ℵ_u\)（\(u>0\)）、\(Ω_ω=ℵ_ω\)。 -/
noncomputable def Om (u : ℕ∞) : Ordinal.{0} :=
  match u with
  | ⊤ => (ℵ_ Ordinal.omega0).ord
  | (n : ℕ) => if n = 0 then 1 else (ℵ_ (n : Ordinal)).ord

@[simp] theorem Om_zero : Om 0 = 1 := rfl

@[simp] theorem Om_top : Om ⊤ = (ℵ_ Ordinal.omega0).ord := rfl

@[simp] theorem Om_coe (n : ℕ) :
    Om (n : ℕ∞) = if n = 0 then 1 else (ℵ_ (n : Ordinal)).ord := rfl

/-- \(Ω_{u+1}\)。`ℕ∞` では `⊤ + 1 = ⊤` なので `Om (u + 1)` では書けない。 -/
noncomputable def OmSucc (u : ℕ∞) : Ordinal.{0} :=
  match u with
  | ⊤ => (ℵ_ (Ordinal.omega0 + 1)).ord
  | (n : ℕ) => (ℵ_ ((n : Ordinal) + 1)).ord

@[simp] theorem OmSucc_top : OmSucc ⊤ = (ℵ_ (Ordinal.omega0 + 1)).ord := rfl

@[simp] theorem OmSucc_coe (n : ℕ) :
    OmSucc (n : ℕ∞) = (ℵ_ ((n : Ordinal) + 1)).ord := rfl

theorem Om_pos (u : ℕ∞) : 0 < Om u := by
  have key : ∀ x : Ordinal, 0 < (ℵ_ x).ord := fun x =>
    Cardinal.ord_pos.2 (Cardinal.aleph_pos x)
  cases u with
  | top => simpa [Om] using key _
  | coe n =>
    by_cases h : n = 0
    · simp [Om, h]
    · simpa [Om, h] using key ((n : ℕ) : Ordinal)

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

/-! ## \(C_u(α)\)

[Buc1] §1 の定義をそのまま写す。

\[
C_v(α)=\bigcup_{n\lt\omega}C_v^n(α),\qquad C_v^0(α)=Ω_v,
\]
\[
C_v^{n+1}(α)=C_v^n(α)\cup\{γ\mid P(γ)\subseteq C_v^n(α)\}
\cup\{\psi_uξ\midξ\inα\cap C_v^n(α)\ \land\ ξ\in C_u(ξ)\ \land\ u\leω\}
\]

段階の合併の代わりに、[Buc1] が同値として挙げる「(C1)(C2)(C3) を満たす最小の集合」
の形を採る（\(P(γ)\subseteq X\) による閉包は加法についての閉包と同値。[Buc1] 1.2(e)）。
最小性は「条件を満たす集合すべての共通部分」として書く。帰納的述語にしないのは、
\(ξ\in C_u(ξ)\) が「\(ξ\) 未満の引数での \(\psi\)」を参照するため、帰納的述語では
関数を添字に持つことになって扱えないからである。
-/

/-- 閉包の条件。`nf x hx v` が \(x\in C_v(x)\)、`pv x hx v` が \(\psi_v(x)\) にあたる。 -/
structure IsCClosed (u : ℕ∞) (a : Ordinal.{0})
    (nf : ∀ x : Ordinal.{0}, x < a → ℕ∞ → Prop)
    (pv : ∀ x : Ordinal.{0}, x < a → ℕ∞ → Ordinal.{0})
    (X : Set Ordinal.{0}) : Prop where
  lt_Om : ∀ b, b < Om u → b ∈ X
  zero : (0 : Ordinal.{0}) ∈ X
  add : ∀ x ∈ X, ∀ y ∈ X, x + y ∈ X
  psi : ∀ x ∈ X, ∀ (hx : x < a) (v : ℕ∞), nf x hx v → pv x hx v ∈ X

/-- 条件を満たす最小の集合。 -/
def CSetOf (u : ℕ∞) (a : Ordinal.{0})
    (nf : ∀ x : Ordinal.{0}, x < a → ℕ∞ → Prop)
    (pv : ∀ x : Ordinal.{0}, x < a → ℕ∞ → Ordinal.{0}) : Set Ordinal.{0} :=
  {b | ∀ X : Set Ordinal.{0}, IsCClosed u a nf pv X → b ∈ X}

theorem isCClosed_CSetOf (u : ℕ∞) (a : Ordinal.{0}) (nf) (pv) :
    IsCClosed u a nf pv (CSetOf u a nf pv) where
  lt_Om _ h := fun _ hX => hX.lt_Om _ h
  zero := fun _ hX => hX.zero
  add _ hx _ hy := fun X hX => hX.add _ (hx X hX) _ (hy X hX)
  psi _ hx hxa v hnf := fun X hX => hX.psi _ (hx X hX) hxa v hnf

/-- \(C\) と \(ψ\) を \(α\) に関する整礎再帰で同時に定める。 -/
noncomputable def cpsiStep (a : Ordinal.{0})
    (F : ∀ y : Ordinal.{0}, y < a → (ℕ∞ → Set Ordinal.{0}) × (ℕ∞ → Ordinal.{0})) :
    (ℕ∞ → Set Ordinal.{0}) × (ℕ∞ → Ordinal.{0}) :=
  (fun u => CSetOf u a (fun x hx v => x ∈ (F x hx).1 v) (fun x hx v => (F x hx).2 v),
   fun u => sInf {b | b ∉ CSetOf u a (fun x hx v => x ∈ (F x hx).1 v)
                        (fun x hx v => (F x hx).2 v)})

noncomputable def cpsi : Ordinal.{0} → (ℕ∞ → Set Ordinal.{0}) × (ℕ∞ → Ordinal.{0}) :=
  Ordinal.lt_wf.fix cpsiStep

/-- \(C_u(α)\)。 -/
def CSet (u : ℕ∞) (a : Ordinal.{0}) : Set Ordinal.{0} := (cpsi a).1 u

/-- \(ψ_u(α)\)。 -/
noncomputable def psi (u : ℕ∞) (a : Ordinal.{0}) : Ordinal.{0} := (cpsi a).2 u

theorem cpsi_eq (a : Ordinal.{0}) : cpsi a = cpsiStep a (fun y _ => cpsi y) :=
  Ordinal.lt_wf.fix_eq cpsiStep a

theorem CSet_eq (u : ℕ∞) (a : Ordinal.{0}) :
    CSet u a = CSetOf u a (fun x _ v => x ∈ CSet v x) (fun x _ v => psi v x) := by
  rw [CSet, cpsi_eq]; rfl

theorem psi_eq (u : ℕ∞) (a : Ordinal.{0}) : psi u a = sInf {b | b ∉ CSet u a} := by
  conv_rhs => rw [CSet_eq]
  rw [psi, cpsi_eq]
  rfl

/-! ### 閉包の規則と帰納法 -/

theorem CSet_lt_Om {u : ℕ∞} {a b : Ordinal.{0}} (h : b < Om u) : b ∈ CSet u a := by
  rw [CSet_eq]; exact (isCClosed_CSetOf u a _ _).lt_Om b h

theorem CSet_zero {u : ℕ∞} {a : Ordinal.{0}} : (0 : Ordinal.{0}) ∈ CSet u a := by
  rw [CSet_eq]; exact (isCClosed_CSetOf u a _ _).zero

theorem CSet_add {u : ℕ∞} {a x y : Ordinal.{0}} (hx : x ∈ CSet u a) (hy : y ∈ CSet u a) :
    x + y ∈ CSet u a := by
  rw [CSet_eq] at hx hy ⊢
  exact (isCClosed_CSetOf u a _ _).add x hx y hy

theorem CSet_psi {u : ℕ∞} {a x : Ordinal.{0}} (hx : x ∈ CSet u a) (hxa : x < a) (v : ℕ∞)
    (hnf : x ∈ CSet v x) : psi v x ∈ CSet u a := by
  rw [CSet_eq] at hx ⊢
  exact (isCClosed_CSetOf u a _ _).psi x hx hxa v hnf

/-- 閉包に関する帰納法。4 規則を満たす述語は \(C_u(α)\) を含む。 -/
theorem CSet_induction {u : ℕ∞} {a : Ordinal.{0}} {P : Ordinal.{0} → Prop}
    (hOm : ∀ b, b < Om u → P b)
    (hzero : P 0)
    (hadd : ∀ x, x ∈ CSet u a → P x → ∀ y, y ∈ CSet u a → P y → P (x + y))
    (hpsi : ∀ x, x ∈ CSet u a → P x → ∀ (hxa : x < a) (v : ℕ∞), x ∈ CSet v x → P (psi v x))
    {b : Ordinal.{0}} (hb : b ∈ CSet u a) : P b := by
  have hb' : b ∈ CSet u a ∧ P b := by
    rw [CSet_eq] at hb
    refine hb {c | c ∈ CSet u a ∧ P c} ⟨?_, ?_, ?_, ?_⟩
    · exact fun c hc => ⟨CSet_lt_Om hc, hOm c hc⟩
    · exact ⟨CSet_zero, hzero⟩
    · rintro x ⟨hx, px⟩ y ⟨hy, py⟩
      exact ⟨CSet_add hx hy, hadd x hx px y hy py⟩
    · rintro x ⟨hx, px⟩ hxa v hnf
      exact ⟨CSet_psi hx hxa v hnf, hpsi x hx px hxa v hnf⟩
  exact hb'.2

/-! ### 段階表現 -/

/-- \(C_u^n(α)\)。`CGen` が生成するものを段階に分けたもの（上界評価用なので
`CGen ⊆ ⋃ n` の向きだけを使う）。 -/
noncomputable def CStage (u : ℕ∞) (a : Ordinal.{0}) : ℕ → Set Ordinal.{0}
  | 0 => Set.Iio (Om u) ∪ {0}
  | n + 1 =>
      CStage u a n
      ∪ {b | ∃ x ∈ CStage u a n, ∃ y ∈ CStage u a n, b = x + y}
      ∪ {b | ∃ v : ℕ∞, ∃ x ∈ CStage u a n, x < a ∧ b = psi v x}

theorem CStage_mono {u : ℕ∞} {a : Ordinal.{0}} {m n : ℕ} (h : m ≤ n) :
    CStage u a m ⊆ CStage u a n := by
  induction n with
  | zero => rw [Nat.le_zero.mp h]
  | succ k ih =>
    rcases Nat.lt_or_ge m (k + 1) with hm | hm
    · exact fun x hx => Or.inl (Or.inl (ih (Nat.lt_succ_iff.mp hm) hx))
    · rw [le_antisymm h hm]

theorem CGen_stage {u : ℕ∞} {a b : Ordinal.{0}} (h : b ∈ CSet u a) :
    ∃ n, b ∈ CStage u a n := by
  refine CSet_induction (P := fun c => ∃ n, c ∈ CStage u a n) ?_ ?_ ?_ ?_ h
  · exact fun b hb => ⟨0, Or.inl hb⟩
  · exact ⟨0, Or.inr rfl⟩
  · rintro x _ ⟨n, hn⟩ y _ ⟨m, hm⟩
    exact ⟨max n m + 1, Or.inl (Or.inr ⟨_, CStage_mono (le_max_left n m) hn,
      _, CStage_mono (le_max_right n m) hm, rfl⟩)⟩
  · rintro x _ ⟨n, hn⟩ hxa v _
    exact ⟨n + 1, Or.inr ⟨v, _, hn, hxa, rfl⟩⟩

/-! ### 基数評価 -/

/-- 上界 \(\max(|Ω_u|,ℵ_0)\)。 -/
noncomputable def CBound (u : ℕ∞) : Cardinal.{1} :=
  max (Cardinal.lift.{1} (Om u).card) Cardinal.aleph0

theorem aleph0_le_CBound (u : ℕ∞) : Cardinal.aleph0 ≤ CBound u := le_max_right _ _

theorem lift_card_le_CBound (u : ℕ∞) :
    Cardinal.lift.{1} (Om u).card ≤ CBound u := le_max_left _ _

theorem CBound_add_self (u : ℕ∞) : CBound u + CBound u = CBound u :=
  Cardinal.add_eq_self (aleph0_le_CBound u)

theorem CBound_mul_self (u : ℕ∞) : CBound u * CBound u = CBound u :=
  Cardinal.mul_eq_self (aleph0_le_CBound u)

theorem mk_CStage_le (u : ℕ∞) (a : Ordinal.{0}) (n : ℕ) :
    Cardinal.mk (CStage u a n) ≤ CBound u := by
  induction n with
  | zero =>
      refine le_trans (Cardinal.mk_union_le _ _) ?_
      rw [Cardinal.mk_Iio_ordinal, Cardinal.mk_singleton]
      refine le_trans (add_le_add (lift_card_le_CBound u)
        (le_trans Cardinal.one_le_aleph0 (aleph0_le_CBound u))) ?_
      exact le_of_eq (CBound_add_self u)
  | succ k ih =>
      set S := CStage u a k with hS
      have haddset :
          {b : Ordinal.{0} | ∃ x ∈ S, ∃ y ∈ S, b = x + y}
            = Set.range (fun p : S × S => (p.1 : Ordinal.{0}) + (p.2 : Ordinal.{0})) := by
        ext b
        constructor
        · rintro ⟨x, hx, y, hy, rfl⟩
          exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
        · rintro ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, rfl⟩
          exact ⟨x, hx, y, hy, rfl⟩
      have hpsiset :
          {b : Ordinal.{0} | ∃ v : ℕ∞, ∃ x ∈ S, x < a ∧ b = psi v x}
            = Set.range (fun p : ℕ∞ × (S ∩ Set.Iio a : Set Ordinal.{0}) =>
                psi p.1 (p.2 : Ordinal.{0})) := by
        ext b
        constructor
        · rintro ⟨v, x, hx, hxa, rfl⟩
          exact ⟨(v, ⟨x, hx, hxa⟩), rfl⟩
        · rintro ⟨⟨v, ⟨x, hx, hxa⟩⟩, rfl⟩
          exact ⟨v, x, hx, hxa, rfl⟩
      have hadd : Cardinal.mk {b : Ordinal.{0} | ∃ x ∈ S, ∃ y ∈ S, b = x + y} ≤ CBound u := by
        rw [haddset]
        refine le_trans Cardinal.mk_range_le ?_
        rw [Cardinal.mk_prod]
        simpa using le_trans (mul_le_mul' ih ih) (le_of_eq (CBound_mul_self u))
      have hsubT : (S ∩ Set.Iio a : Set Ordinal.{0}) ⊆ S := Set.inter_subset_left
      have hpsi : Cardinal.mk {b : Ordinal.{0} | ∃ v : ℕ∞, ∃ x ∈ S, x < a ∧ b = psi v x}
          ≤ CBound u := by
        rw [hpsiset]
        refine le_trans Cardinal.mk_range_le ?_
        rw [Cardinal.mk_prod]
        have h1 : Cardinal.lift.{1} (Cardinal.mk ℕ∞) ≤ CBound u := by
          have : Cardinal.mk ℕ∞ ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
          simpa using le_trans (Cardinal.lift_le.2 this) (by
            simpa using aleph0_le_CBound u)
        have h2 : Cardinal.lift.{0} (Cardinal.mk (S ∩ Set.Iio a : Set Ordinal.{0}))
            ≤ CBound u := by
          simpa using le_trans (Cardinal.mk_le_mk_of_subset hsubT) ih
        exact le_trans (mul_le_mul' h1 h2) (le_of_eq (CBound_mul_self u))
      refine le_trans (Cardinal.mk_union_le _ _) ?_
      refine le_trans (add_le_add (le_trans (Cardinal.mk_union_le _ _)
        (le_trans (add_le_add ih hadd) (le_of_eq (CBound_add_self u)))) hpsi) ?_
      exact le_of_eq (CBound_add_self u)

theorem mk_CSet_le (u : ℕ∞) (a : Ordinal.{0}) :
    Cardinal.mk (CSet u a) ≤ CBound u := by
  have hsub : CSet u a ⊆ ⋃ n : ULift.{1} ℕ, CStage u a n.down := by
    intro b hb
    obtain ⟨n, hn⟩ := CGen_stage hb
    exact Set.mem_iUnion.2 ⟨⟨n⟩, hn⟩
  refine le_trans (Cardinal.mk_le_mk_of_subset hsub) ?_
  refine le_trans (Cardinal.mk_iUnion_le _) ?_
  have h1 : Cardinal.mk (ULift.{1} ℕ) ≤ CBound u := by
    simpa using aleph0_le_CBound u
  have h2 : (⨆ n : ULift.{1} ℕ, Cardinal.mk (CStage u a n.down)) ≤ CBound u :=
    ciSup_le fun n => mk_CStage_le u a n.down
  exact le_trans (mul_le_mul' h1 h2) (le_of_eq (CBound_mul_self u))

theorem CBound_lt (u : ℕ∞) : CBound u < Cardinal.lift.{1} (OmSucc u).card := by
  have key : ∀ x : Ordinal, (0 : Ordinal) < x → Cardinal.aleph0 < ℵ_ x := by
    intro x hx
    have h := Cardinal.aleph_lt_aleph.2 hx
    rwa [Cardinal.aleph_zero] at h
  have hsucc : ∀ x : Ordinal, (0 : Ordinal) < x + 1 := fun x =>
    lt_of_lt_of_le zero_lt_one le_add_self
  have hcard : (Om u).card < (OmSucc u).card ∧ Cardinal.aleph0 < (OmSucc u).card := by
    cases u with
    | top =>
        rw [Om_top, OmSucc_top, Cardinal.card_ord, Cardinal.card_ord]
        exact ⟨Cardinal.aleph_lt_aleph.2 (by simp), key _ (hsucc _)⟩
    | coe n =>
        rw [OmSucc_coe, Cardinal.card_ord, Om_coe]
        by_cases h : n = 0
        · subst h
          rw [if_pos rfl, Ordinal.card_one]
          exact ⟨lt_of_lt_of_le Cardinal.one_lt_aleph0 (Cardinal.aleph0_le_aleph _),
            key _ (hsucc _)⟩
        · rw [if_neg h, Cardinal.card_ord]
          exact ⟨Cardinal.aleph_lt_aleph.2 (by simp), key _ (hsucc _)⟩
  refine max_lt (Cardinal.lift_lt.2 hcard.1) ?_
  have h2 : Cardinal.lift.{1, 0} Cardinal.aleph0
      < Cardinal.lift.{1, 0} (OmSucc u).card := Cardinal.lift_lt.2 hcard.2
  simpa [Cardinal.lift_aleph0] using h2

/-! ## (1) 存在 -/

/-- \(Ω_{u+1}\) 未満に \(C_u(α)\) の外の元がある。基数評価 \(|C_u(α)|<ℵ_{u+1}\) から。 -/
theorem exists_not_mem_lt_OmSucc (u : ℕ∞) (a : Ordinal.{0}) :
    ∃ b, b < OmSucc u ∧ b ∉ CSet u a := by
  by_contra hcon
  have hsub : Set.Iio (OmSucc u) ⊆ CSet u a := by
    intro b hb
    by_contra hb'
    exact hcon ⟨b, hb, hb'⟩
  have hle := (Cardinal.mk_le_mk_of_subset hsub).trans (mk_CSet_le u a)
  rw [Cardinal.mk_Iio_ordinal] at hle
  exact absurd hle (not_le.2 (CBound_lt u))

/-- \(C_u(α)\) は順序数全体ではないので、\(ψ_u(α)\) の最小元が実在する。 -/
theorem CSet_ne_univ (u : ℕ∞) (a : Ordinal.{0}) : ∃ b, b ∉ CSet u a := by
  obtain ⟨b, _, hb⟩ := exists_not_mem_lt_OmSucc u a
  exact ⟨b, hb⟩

theorem psi_not_mem (u : ℕ∞) (a : Ordinal.{0}) : psi u a ∉ CSet u a := by
  rw [psi_eq]
  exact csInf_mem (CSet_ne_univ u a)

theorem lt_psi_mem {u : ℕ∞} {a b : Ordinal.{0}} (h : b < psi u a) : b ∈ CSet u a := by
  by_contra hb
  rw [psi_eq] at h
  exact absurd (csInf_le' hb) (not_le.2 h)

/-- \(ψ_u(α)<Ω_{u+1}\)。 -/
theorem psi_lt_OmSucc (u : ℕ∞) (a : Ordinal.{0}) : psi u a < OmSucc u := by
  obtain ⟨b, hblt, hb⟩ := exists_not_mem_lt_OmSucc u a
  rw [psi_eq]
  exact lt_of_le_of_lt (csInf_le' hb) hblt

/-- \(Ω_u\leψ_u(α)\)。 -/
theorem Om_le_psi (u : ℕ∞) (a : Ordinal.{0}) : Om u ≤ psi u a := by
  by_contra hcon
  exact psi_not_mem u a (CSet_lt_Om (not_le.1 hcon))

/-! ### \(Ω\) の単調性 -/

theorem alephOrd_le {x y : Ordinal} (h : x ≤ y) : (ℵ_ x).ord ≤ (ℵ_ y).ord :=
  Cardinal.ord_le_ord.2 (Cardinal.aleph_le_aleph.2 h)

theorem OmSucc_le_Om {u v : ℕ∞} (h : u < v) : OmSucc u ≤ Om v := by
  cases u with
  | top => exact absurd h (not_lt_of_ge le_top)
  | coe n =>
    cases v with
    | top =>
        rw [OmSucc_coe, Om_top]
        refine alephOrd_le (le_of_lt ?_)
        have := Ordinal.natCast_lt_omega0 (n + 1)
        push_cast at this
        exact this
    | coe m =>
        have hnm : n < m := by exact_mod_cast h
        have hm : m ≠ 0 := by omega
        rw [OmSucc_coe, Om_coe, if_neg hm]
        refine alephOrd_le ?_
        have : ((n + 1 : ℕ) : Ordinal) ≤ ((m : ℕ) : Ordinal) := by
          exact_mod_cast Nat.succ_le_of_lt hnm
        push_cast at this
        exact this

theorem Om_le_Om {u v : ℕ∞} (h : u ≤ v) : Om u ≤ Om v := by
  rcases lt_or_eq_of_le h with hlt | rfl
  · exact le_trans (le_of_lt (Om_lt_OmSucc u)) (OmSucc_le_Om hlt)
  · exact le_rfl

theorem le_of_Om_lt_OmSucc {u v : ℕ∞} (h : Om v < OmSucc u) : v ≤ u := by
  by_contra hc
  exact absurd (OmSucc_le_Om (not_le.1 hc)) (not_le.2 h)

/-! ### \(C_u(α)\) の \(α\) についての単調性 -/

theorem CGen_mono_arg {u : ℕ∞} {x y : Ordinal.{0}} (h : x ≤ y) {b : Ordinal.{0}}
    (hb : b ∈ CSet u x) : b ∈ CSet u y := by
  refine CSet_induction (P := fun c => c ∈ CSet u y) ?_ ?_ ?_ ?_ hb
  · exact fun _ hb' => CSet_lt_Om hb'
  · exact CSet_zero
  · exact fun _ _ hx _ _ hy => CSet_add hx hy
  · exact fun z _ hz hza v hnf => CSet_psi hz (lt_of_lt_of_le hza h) v hnf

theorem psi_mono {u : ℕ∞} {x y : Ordinal.{0}} (h : x ≤ y) : psi u x ≤ psi u y := by
  rw [psi_eq]
  exact csInf_le' (fun hmem => psi_not_mem u y (CGen_mono_arg h hmem))

/-- \(x<y\) かつ \(x\in C_u(y)\) なら \(ψ_u(x)<ψ_u(y)\)（狭義単調性）。 -/
theorem psi_lt_psi {u : ℕ∞} {x y : Ordinal.{0}} (hxy : x < y) (hx : x ∈ CSet u y)
    (hnf : x ∈ CSet u x) : psi u x < psi u y := by
  rcases lt_or_eq_of_le (psi_mono (le_of_lt hxy)) with h | h
  · exact h
  · exact absurd (h ▸ CSet_psi hx hxy u hnf) (psi_not_mem u y)

/-! ### \(ψ_u(α)\) は加法的principal -/

theorem add_lt_psi {u : ℕ∞} {a x y : Ordinal.{0}} (hx : x < psi u a) (hy : y < psi u a) :
    x + y < psi u a := by
  by_contra hc
  have hle : psi u a ≤ x + y := not_lt.1 hc
  have hxle : x ≤ psi u a := le_of_lt hx
  have hsplit : x + (psi u a - x) = psi u a := Ordinal.add_sub_cancel_of_le hxle
  have hey : psi u a - x ≤ y := by
    have : x + (psi u a - x) ≤ x + y := by rw [hsplit]; exact hle
    exact (add_le_add_iff_left x).1 this
  have hmem : psi u a ∈ CSet u a := by
    have := CSet_add (lt_psi_mem hx) (lt_psi_mem (lt_of_le_of_lt hey hy))
    rwa [hsplit] at this
  exact psi_not_mem u a hmem

/-- \(ψ_u(α)\) は加法的 principal（Mathlib の `IsPrincipal`）。 -/
theorem isPrincipal_add_psi (u : ℕ∞) (a : Ordinal.{0}) :
    Ordinal.IsPrincipal (· + ·) (psi u a) := fun {_ _} hx hy => add_lt_psi hx hy

/-- 吸収律: \(β\ltψ_u(α)\) なら \(β+ψ_u(α)=ψ_u(α)\)。加法標準形に使う。 -/
theorem add_psi_eq (u : ℕ∞) (a : Ordinal.{0}) {b : Ordinal.{0}} (h : b < psi u a) :
    b + psi u a = psi u a := (isPrincipal_add_psi u a).add_eq_right h

/-! ### (2) 崩壊の要 -/

theorem mem_CSet_lt_psi (u : ℕ∞) (a : Ordinal.{0}) {c : Ordinal.{0}}
    (hc : c ∈ CSet u a) : c < OmSucc u → c < psi u a := by
  refine CSet_induction (P := fun c => c < OmSucc u → c < psi u a) ?_ ?_ ?_ ?_ hc
  · exact fun _ h => fun _ => lt_of_lt_of_le h (Om_le_psi u a)
  · exact fun _ => lt_of_lt_of_le (Om_pos u) (Om_le_psi u a)
  · intro x _ ihx y _ ihy h
    have hxlt : x < OmSucc u := lt_of_le_of_lt (le_self_add : x ≤ x + y) h
    have hylt : y < OmSucc u := lt_of_le_of_lt (le_add_self : y ≤ x + y) h
    exact add_lt_psi (ihx hxlt) (ihy hylt)
  · intro x hx _ hxa v hnf h
    have hvu : v ≤ u := le_of_Om_lt_OmSucc (lt_of_le_of_lt (Om_le_psi v x) h)
    rcases lt_or_eq_of_le hvu with hv | hv
    · exact lt_of_lt_of_le (psi_lt_OmSucc v x)
        (le_trans (OmSucc_le_Om hv) (Om_le_psi u a))
    · subst hv
      exact psi_lt_psi hxa hx hnf

/-! ### [Buc1] Lemma 1.4 -/

/-- [Buc1] Lemma 1.4(b)。\(C_u(α)\) の元で \(Ω_u\) 以上の加法的 principal は、
標準形の引数をもつ \(\psi\) 値である。閉包が「4 規則を満たす最小の集合」なので、
主張そのものが 4 規則で閉じていることを見ればよい。 -/
theorem CSet_inversion {u : ℕ∞} {a γ : Ordinal.{0}} (hγ : γ ∈ CSet u a)
    (hprin : Ordinal.IsPrincipal (· + ·) γ) (hOm : Om u ≤ γ) :
    ∃ (v : ℕ∞) (x : Ordinal.{0}), x < a ∧ x ∈ CSet u a ∧ x ∈ CSet v x ∧ γ = psi v x := by
  refine CSet_induction
    (P := fun c => Ordinal.IsPrincipal (· + ·) c → Om u ≤ c →
      ∃ (v : ℕ∞) (x : Ordinal.{0}), x < a ∧ x ∈ CSet u a ∧ x ∈ CSet v x ∧ c = psi v x)
    ?_ ?_ ?_ ?_ hγ hprin hOm
  · exact fun b hb _ hb' => absurd (lt_of_lt_of_le hb hb') (lt_irrefl _)
  · exact fun _ h0 => absurd (lt_of_lt_of_le (Om_pos u) h0) (lt_irrefl _)
  · intro x _ ihx y _ ihy hp hle
    rcases lt_or_eq_of_le (le_self_add : x ≤ x + y) with hxl | hxe
    · rcases lt_or_eq_of_le (le_add_self : y ≤ x + y) with hyl | hye
      · exact absurd (hp hxl hyl) (lt_irrefl _)
      · rw [← hye] at hp hle ⊢
        exact ihy hp hle
    · have hy0 : y = 0 := by
        have : x + 0 = x + y := by simpa using hxe
        exact ((add_right_inj x).1 this).symm
      rw [hy0, add_zero] at hp hle ⊢
      exact ihx hp hle
  · intro x hx _ hxa v hnf _ _
    exact ⟨v, x, hxa, hx, hnf, rfl⟩

/-- [Buc1] Lemma 1.4(a)。標準形の引数をもつ \(\psi\) 値の表示は一意。 -/
theorem psi_inj {u v : ℕ∞} {x y : Ordinal.{0}}
    (hx : x ∈ CSet u x) (hy : y ∈ CSet v y) (h : psi u x = psi v y) : u = v ∧ x = y := by
  have huv : u = v := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h1 : psi u x < Om v :=
        lt_of_lt_of_le (psi_lt_OmSucc u x) (OmSucc_le_Om hlt)
      rw [h] at h1
      exact absurd (lt_of_lt_of_le h1 (Om_le_psi v y)) (lt_irrefl _)
    · have h1 : psi v y < Om u :=
        lt_of_lt_of_le (psi_lt_OmSucc v y) (OmSucc_le_Om hlt)
      rw [← h] at h1
      exact absurd (lt_of_lt_of_le h1 (Om_le_psi u x)) (lt_irrefl _)
  subst huv
  refine ⟨rfl, ?_⟩
  rcases lt_trichotomy x y with hlt | heq | hlt
  · exact absurd (psi_lt_psi hlt (CGen_mono_arg (le_of_lt hlt) hx) hx) (by rw [h]; exact lt_irrefl _)
  · exact heq
  · exact absurd (psi_lt_psi hlt (CGen_mono_arg (le_of_lt hlt) hy) hy)
      (by rw [← h]; exact lt_irrefl _)

/-- 順序数側の逆向き橋渡し。\(\psi_v(x)\in C_w(b)\) かつ \(w\leq v\) なら
\(x\lt b\) かつ \(x\in C_w(b)\)。 -/
theorem lt_of_psi_mem {v w : ℕ∞} {x b : Ordinal.{0}} (hwv : w ≤ v)
    (hnf : x ∈ CSet v x) (hmem : psi v x ∈ CSet w b) : x < b ∧ x ∈ CSet w b := by
  have hOm : Om w ≤ psi v x := le_trans (Om_le_Om hwv) (Om_le_psi v x)
  obtain ⟨v', x', hx'b, hx'mem, hx'nf, heq⟩ :=
    CSet_inversion hmem (isPrincipal_add_psi v x) hOm
  obtain ⟨rfl, rfl⟩ := psi_inj hx'nf hnf heq.symm
  exact ⟨hx'b, hx'mem⟩

/-! ## (2) 崩壊の要 -/

/-- \(C_u(α)\cap Ω_{u+1}=ψ_u(α)\)。 -/
theorem CSet_inter_OmSucc (u : ℕ∞) (a : Ordinal.{0}) :
    CSet u a ∩ {b | b < OmSucc u} = {b | b < psi u a} := by
  ext b
  constructor
  · rintro ⟨hb, hlt⟩
    exact mem_CSet_lt_psi u a hb hlt
  · intro hb
    exact ⟨lt_psi_mem hb, lt_trans hb (psi_lt_OmSucc u a)⟩

/-! ## 評価写像 \(o\)

[Buc1] の \(o\) は項の構造に沿った再帰である。

\[
o(0)=0,\qquad o(D_ua)=\psi_u(o(a)),\qquad o(t_0+t_1)=o(t_0)+o(t_1)
\]

`BT` は principal 項の列なので、列の評価を先頭から順に足したものとして定める。
-/

mutual
  /-- \(o:T_{\textrm{B}\omega}\to\mathrm{Ord}\)。 -/
  noncomputable def oval : BT → Ordinal.{0}
    | BT.trm ps => ovalList ps
  /-- principal 項の評価 \(o(D_va)=\psi_v(o(a))\)。 -/
  noncomputable def ovalBP : BP → Ordinal.{0}
    | BP.db v a => psi v (oval a)
  /-- principal 項の列の評価（先頭から順に加える）。 -/
  noncomputable def ovalList : List BP → Ordinal.{0}
    | [] => 0
    | p :: ps => ovalBP p + ovalList ps
end

@[simp] theorem oval_trm_nil : oval (BT.trm []) = 0 := rfl

@[simp] theorem oval_zero : oval BZero = 0 := rfl

@[simp] theorem ovalBP_db (v : ℕ∞) (a : BT) : ovalBP (BP.db v a) = psi v (oval a) := rfl

@[simp] theorem oval_trm_cons (p : BP) (ps : List BP) :
    oval (BT.trm (p :: ps)) = ovalBP p + oval (BT.trm ps) := rfl

@[simp] theorem oval_Dprin (v : ℕ∞) (a : BT) : oval (Dprin v a) = psi v (oval a) := by
  show ovalBP (BP.db v a) + oval (BT.trm []) = _
  simp

/-- principal 項の評価は正。 -/
theorem ovalBP_pos (p : BP) : 0 < ovalBP p := by
  cases p with
  | db v a => exact lt_of_lt_of_le (Om_pos v) (Om_le_psi v (oval a))

/-- 列の評価は連結について加法的（\(o(t_0+t_1)=o(t_0)+o(t_1)\)）。 -/
theorem oval_append (as bs : List BP) :
    oval (BT.trm (as ++ bs)) = oval (BT.trm as) + oval (BT.trm bs) := by
  induction as with
  | nil => simp
  | cons p ps ih => simp [ih, add_assoc]

/-! ### Lemma 2.1 の部品 -/

/-- \(\psi_v(x)\) は加法的 principal なので、principal 成分がすべてそれ未満の列の
評価もそれ未満。 -/
theorem oval_trm_lt_psi {v : ℕ∞} {x : Ordinal.{0}} :
    ∀ {ps : List BP}, (∀ p ∈ ps, ovalBP p < psi v x) → oval (BT.trm ps) < psi v x
  | [], _ => by
      simpa using lt_of_lt_of_le (Om_pos v) (Om_le_psi v x)
  | p :: ps, h => by
      have hp := h p (List.mem_cons_self)
      have hps : oval (BT.trm ps) < psi v x :=
        oval_trm_lt_psi (fun q hq => h q (List.mem_cons_of_mem _ hq))
      simpa using add_lt_psi hp hps

/-- 添字が小さい principal は値も小さい（\(\psi_u(x)\lt Ω_{u+1}\leq Ω_v\leq\psi_v(y)\)）。 -/
theorem ovalBP_lt_of_index {u v : ℕ∞} (huv : u < v) (a b : BT) :
    ovalBP (BP.db u a) < ovalBP (BP.db v b) := by
  simpa using lt_of_lt_of_le (psi_lt_OmSucc u (oval a))
    (le_trans (OmSucc_le_Om huv) (Om_le_psi v (oval b)))

/-- `descP` の各成分は先頭以下。 -/
theorem descP_le_head : ∀ (p : BP) (ps : List BP), descP (p :: ps) = true →
    ∀ q ∈ ps, leBT (BT.trm [q]) (BT.trm [p]) = true
  | _, [], _, _, hq => absurd hq (by simp)
  | p, q :: qs, h, r, hr => by
      simp only [descP, Bool.and_eq_true] at h
      rcases List.mem_cons.1 hr with rfl | hr'
      · exact h.1
      · have := descP_le_head q qs h.2 r hr'
        -- leBT の推移律
        simp only [leBT, Bool.or_eq_true, beq_iff_eq] at this h ⊢
        rcases this with hlt | heqr
        · rcases h.1 with hlt' | heq
          · exact Or.inl (lessBT_linear_trans _ _ _ hlt hlt')
          · exact Or.inl (heq ▸ hlt)
        · rw [heqr]
          exact h.1

/-! ### `OT` は部分項について閉じている -/

mutual
  theorem isOT_of_mem_gatherBT : ∀ (u : ℕ∞) (t : BT), isOT_BT t = true →
      ∀ x ∈ gatherBT u t, isOT_BT x = true
    | u, .trm ps, h, x, hx => by
        simp only [isOT_BT, Bool.and_eq_true] at h
        exact isOT_of_mem_gatherBPList u ps h.1 x (by simpa [gatherBT] using hx)

  theorem isOT_of_mem_gatherBP : ∀ (u : ℕ∞) (p : BP), isOT_BP p = true →
      ∀ x ∈ gatherBP u p, isOT_BT x = true
    | u, .db v b, h, x, hx => by
        simp only [isOT_BP, Bool.and_eq_true] at h
        by_cases huv : u ≤ v
        · simp only [gatherBP, huv, decide_true, if_true, List.mem_cons] at hx
          rcases hx with rfl | hx'
          · exact h.1
          · exact isOT_of_mem_gatherBT u b h.1 x hx'
        · simp [gatherBP, huv] at hx

  theorem isOT_of_mem_gatherBPList : ∀ (u : ℕ∞) (ps : List BP), isOT_BPList ps = true →
      ∀ x ∈ gatherBPList u ps, isOT_BT x = true
    | _, [], _, _, hx => absurd hx (by simp [gatherBPList])
    | u, p :: ps, h, x, hx => by
        simp only [isOT_BPList, Bool.and_eq_true] at h
        simp only [gatherBPList, List.mem_append] at hx
        rcases hx with hx | hx
        · exact isOT_of_mem_gatherBP u p h.1 x hx
        · exact isOT_of_mem_gatherBPList u ps h.2 x hx
end

/-! ### 重さ: \(G_u(t)\) の元は \(t\) より軽い

`G_u a` の元は Lean から見て `a` の構造的部分項ではないので、主帰納法は
[Buchholz-rel-ord] の項の重さ `btWeight` に関する整礎再帰で回す。
-/

theorem bpWeight_le_of_mem : ∀ {p : BP} {ps : List BP}, p ∈ ps → bpWeight p ≤ bpListWeight ps
  | _, [], h => absurd h (by simp)
  | p, q :: qs, h => by
      rcases List.mem_cons.1 h with rfl | h'
      · simp only [bpListWeight]
        omega
      · have := bpWeight_le_of_mem h'
        simp only [bpListWeight]
        omega

mutual
  theorem weight_of_mem_gatherBT : ∀ (u : ℕ∞) (t : BT),
      ∀ x ∈ gatherBT u t, btWeight x < btWeight t
    | u, .trm ps, x, hx => by
        have := weight_of_mem_gatherBPList u ps x (by simpa [gatherBT] using hx)
        simp only [btWeight]
        omega

  theorem weight_of_mem_gatherBP : ∀ (u : ℕ∞) (p : BP),
      ∀ x ∈ gatherBP u p, btWeight x < bpWeight p
    | u, .db v b, x, hx => by
        by_cases huv : u ≤ v
        · simp only [gatherBP, huv, decide_true, if_true, List.mem_cons] at hx
          rcases hx with rfl | hx'
          · simp [bpWeight]
          · have := weight_of_mem_gatherBT u b x hx'
            simp only [bpWeight]
            omega
        · simp [gatherBP, huv] at hx

  theorem weight_of_mem_gatherBPList : ∀ (u : ℕ∞) (ps : List BP),
      ∀ x ∈ gatherBPList u ps, btWeight x < bpListWeight ps
    | _, [], x, hx => absurd hx (by simp [gatherBPList])
    | u, p :: ps, x, hx => by
        simp only [gatherBPList, List.mem_append] at hx
        rcases hx with hx | hx
        · have := weight_of_mem_gatherBP u p x hx
          simp only [bpListWeight]
          omega
        · have := weight_of_mem_gatherBPList u ps x hx
          simp only [bpListWeight]
          omega
end

/-! ### `OT` の補助 -/

theorem isOT_of_mem_list : ∀ {p : BP} {ps : List BP}, isOT_BPList ps = true → p ∈ ps →
    isOT_BP p = true
  | _, [], _, h => absurd h (by simp)
  | p, q :: qs, hl, h => by
      simp only [isOT_BPList, Bool.and_eq_true] at hl
      rcases List.mem_cons.1 h with rfl | h'
      · exact hl.1
      · exact isOT_of_mem_list hl.2 h'

theorem descP_tail : ∀ {p : BP} {ps : List BP}, descP (p :: ps) = true → descP ps = true
  | _, [], _ => by simp [descP]
  | _, _ :: _, h => by
      simp only [descP, Bool.and_eq_true] at h
      exact h.2

theorem lessBT_single (p q : BP) : lessBT (BT.trm [p]) (BT.trm [q]) = lessBP p q := by
  simp [lessBT, lessBPList]

/-! ### [Buc1] Lemma 2.1 の順方向 -/

mutual
  theorem oval_lt_of_lessBT : ∀ (s t : BT), isOT_BT s = true → isOT_BT t = true →
      lessBT s t = true → oval s < oval t
    | .trm as, .trm bs, hs, ht, h => by
        simp only [isOT_BT, Bool.and_eq_true] at hs ht
        exact oval_lt_of_lessBPList as bs hs.1 hs.2 ht.1 ht.2 (by simpa [lessBT] using h)
  termination_by s => btWeight s
  decreasing_by simp only [btWeight]; omega

  theorem oval_lt_of_lessBP : ∀ (p q : BP), isOT_BP p = true → isOT_BP q = true →
      lessBP p q = true → ovalBP p < ovalBP q
    | .db u a, .db v b, hp, hq, h => by
        simp only [lessBP, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
          beq_iff_eq] at h
        rcases h with huv | ⟨rfl, hab⟩
        · exact ovalBP_lt_of_index huv a b
        · simp only [isOT_BP, Bool.and_eq_true] at hp hq
          have hlt : oval a < oval b := oval_lt_of_lessBT a b hp.1 hq.1 hab
          have hsmall : ∀ x ∈ gatherBT u a, oval x < oval a := by
            intro x hx
            have hxa : lessBT x a = true := by
              simpa using List.all_eq_true.1 hp.2 x hx
            have hxOT : isOT_BT x = true := isOT_of_mem_gatherBT u a hp.1 x hx
            have hwx : btWeight x < btWeight a := weight_of_mem_gatherBT u a x hx
            exact oval_lt_of_lessBT x a hxOT hp.1 hxa
          have hmem : oval a ∈ CSet u (oval b) :=
            mem_CSet_of_gatherBT u (oval b) a hp.1 (fun x hx => lt_trans (hsmall x hx) hlt)
          have hnf : oval a ∈ CSet u (oval a) :=
            mem_CSet_of_gatherBT u (oval a) a hp.1 hsmall
          simpa using psi_lt_psi hlt hmem hnf
  termination_by p => bpWeight p
  decreasing_by
    all_goals
      first
        | omega
        | (simp only [btWeight]; omega)
        | (simp only [bpWeight]; omega)
        | (simp only [bpListWeight]; omega)
        | (simp only [btWeight, bpWeight, bpListWeight]; omega)

  theorem oval_lt_of_lessBPList : ∀ (as bs : List BP),
      isOT_BPList as = true → descP as = true →
      isOT_BPList bs = true → descP bs = true →
      lessBPList as bs = true → oval (BT.trm as) < oval (BT.trm bs)
    | [], [], _, _, _, _, h => by simp [lessBPList] at h
    | [], b :: bs', _, _, _, _, _ => by
        have hpos : (0 : Ordinal) < ovalBP b + oval (BT.trm bs') :=
          lt_of_lt_of_le (ovalBP_pos b) le_self_add
        simpa using hpos
    | _ :: _, [], _, _, _, _, h => by simp [lessBPList] at h
    | a :: as', b :: bs', ha, hda, hb, hdb, h => by
        simp only [lessBPList, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
        simp only [isOT_BPList, Bool.and_eq_true] at ha hb
        rcases h with hab | ⟨rfl, htail⟩
        · obtain ⟨v, c, rfl⟩ : ∃ v c, b = BP.db v c := by
            cases b with | db v c => exact ⟨v, c, rfl⟩
          have hab' : ovalBP a < ovalBP (BP.db v c) :=
            oval_lt_of_lessBP a (BP.db v c) ha.1 hb.1 hab
          have hall : ∀ p ∈ a :: as', ovalBP p < psi v (oval c) := by
            intro p hp
            rcases List.mem_cons.1 hp with rfl | hp'
            · simpa using hab'
            · have hple := descP_le_head a as' hda p hp'
              have hpOT : isOT_BP p = true := isOT_of_mem_list ha.2 hp'
              have hwp : bpWeight p ≤ bpListWeight as' := bpWeight_le_of_mem hp'
              have hple' : ovalBP p ≤ ovalBP a := by
                simp only [leBT, Bool.or_eq_true, beq_iff_eq, lessBT_single] at hple
                rcases hple with hlt | heq
                · exact le_of_lt (oval_lt_of_lessBP p a hpOT ha.1 hlt)
                · have hpa : p = a := by simpa using heq
                  rw [hpa]
              exact lt_of_le_of_lt hple' (by simpa using hab')
          have hsum : oval (BT.trm (a :: as')) < psi v (oval c) := oval_trm_lt_psi hall
          show ovalBP a + oval (BT.trm as') < ovalBP (BP.db v c) + oval (BT.trm bs')
          calc ovalBP a + oval (BT.trm as') = oval (BT.trm (a :: as')) := rfl
            _ < psi v (oval c) := hsum
            _ = ovalBP (BP.db v c) := by simp
            _ ≤ ovalBP (BP.db v c) + oval (BT.trm bs') := le_self_add
        · have hrec := oval_lt_of_lessBPList as' bs' ha.2 (descP_tail hda) hb.2
            (descP_tail hdb) htail
          simpa using (add_lt_add_iff_left (ovalBP a)).2 hrec
  termination_by as => bpListWeight as
  decreasing_by
    all_goals
      first
        | omega
        | (simp only [btWeight]; omega)
        | (simp only [bpWeight]; omega)
        | (simp only [bpListWeight]; omega)
        | (simp only [btWeight, bpWeight, bpListWeight]; omega)
  theorem mem_CSet_of_gatherBT : ∀ (u : ℕ∞) (b : Ordinal.{0}) (t : BT), isOT_BT t = true →
      (∀ x ∈ gatherBT u t, oval x < b) → oval t ∈ CSet u b
    | u, b, .trm ps, ht, h => by
        simp only [isOT_BT, Bool.and_eq_true] at ht
        exact mem_CSet_of_gatherBPList u b ps ht.1 (by simpa [gatherBT] using h)
  termination_by _ _ t => btWeight t
  decreasing_by simp only [btWeight]; omega

  theorem mem_CSet_of_gatherBP : ∀ (u : ℕ∞) (b : Ordinal.{0}) (p : BP), isOT_BP p = true →
      (∀ x ∈ gatherBP u p, oval x < b) → ovalBP p ∈ CSet u b
    | u, b, .db v a, hp, h => by
        simp only [isOT_BP, Bool.and_eq_true] at hp
        by_cases huv : u ≤ v
        · have hmem : ∀ x ∈ gatherBP u (.db v a), oval x < b := h
          simp only [gatherBP, huv, decide_true, if_true, List.mem_cons] at hmem
          have hab : oval a < b := hmem a (Or.inl rfl)
          have hrest : ∀ x ∈ gatherBT u a, oval x < b := fun x hx => hmem x (Or.inr hx)
          have hmemb : oval a ∈ CSet u b := mem_CSet_of_gatherBT u b a hp.1 hrest
          have hnf : oval a ∈ CSet v (oval a) := by
            refine mem_CSet_of_gatherBT v (oval a) a hp.1 (fun x hx => ?_)
            have hxa : lessBT x a = true := by
              simpa using List.all_eq_true.1 hp.2 x hx
            have hxOT : isOT_BT x = true := isOT_of_mem_gatherBT v a hp.1 x hx
            have hwx : btWeight x < btWeight a := weight_of_mem_gatherBT v a x hx
            exact oval_lt_of_lessBT x a hxOT hp.1 hxa
          simpa using CSet_psi hmemb hab v hnf
        · have hlt : psi v (oval a) < Om u :=
            lt_of_lt_of_le (psi_lt_OmSucc v (oval a)) (OmSucc_le_Om (not_le.1 huv))
          simpa using CSet_lt_Om hlt
  termination_by _ _ p => bpWeight p
  decreasing_by
    all_goals
      first
        | omega
        | (simp only [btWeight]; omega)
        | (simp only [bpWeight]; omega)
        | (simp only [bpListWeight]; omega)
        | (simp only [btWeight, bpWeight, bpListWeight]; omega)

  theorem mem_CSet_of_gatherBPList : ∀ (u : ℕ∞) (b : Ordinal.{0}) (ps : List BP),
      isOT_BPList ps = true →
      (∀ x ∈ gatherBPList u ps, oval x < b) → oval (BT.trm ps) ∈ CSet u b
    | _, _, [], _, _ => by simpa using CSet_zero
    | u, b, p :: ps, hl, h => by
        simp only [isOT_BPList, Bool.and_eq_true] at hl
        simp only [gatherBPList, List.mem_append] at h
        have hp : ovalBP p ∈ CSet u b :=
          mem_CSet_of_gatherBP u b p hl.1 (fun x hx => h x (Or.inl hx))
        have hps : oval (BT.trm ps) ∈ CSet u b :=
          mem_CSet_of_gatherBPList u b ps hl.2 (fun x hx => h x (Or.inr hx))
        simpa using CSet_add hp hps
  termination_by _ _ ps => bpListWeight ps
  decreasing_by
    all_goals
      first
        | omega
        | (simp only [btWeight]; omega)
        | (simp only [bpWeight]; omega)
        | (simp only [bpListWeight]; omega)
        | (simp only [btWeight, bpWeight, bpListWeight]; omega)
end

/-! ### 加法標準形

順序数の和 \(x+y\) を表す項は、単なる連結ではない。\(x\) の principal 成分のうち
\(y\) の先頭 principal より小さいものは和で吸収されるので落とす必要がある。
-/

/-- principal の三分律。 -/
theorem lessBP_trichotomy (p q : BP) : lessBP p q = true ∨ p = q ∨ lessBP q p = true := by
  rcases lessBT_linear_trichotomy (BT.trm [p]) (BT.trm [q]) with h | h | h
  · exact Or.inl (by simpa [lessBT_single] using h)
  · exact Or.inr (Or.inl (by simpa using h))
  · exact Or.inr (Or.inr (by simpa [lessBT_single] using h))

theorem leBT_single_of_not_lessBP {p q : BP} (h : lessBP p q = false) :
    leBT (BT.trm [q]) (BT.trm [p]) = true := by
  rcases lessBP_trichotomy p q with h1 | rfl | h1
  · exact absurd h1 (by simp [h])
  · simp [leBT]
  · simp [leBT, lessBT_single, h1]

/-- `descP` は接頭辞に遺伝する。 -/
theorem descP_prefix : ∀ (ps qs : List BP), descP (ps ++ qs) = true → descP ps = true
  | [], _, _ => by simp [descP]
  | [_], _, _ => by simp [descP]
  | p :: q :: ps', qs, h => by
      simp only [List.cons_append, descP, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, descP_prefix (q :: ps') qs h.2⟩

/-- `descP` は接尾辞に遺伝する。 -/
theorem descP_suffix : ∀ (ps qs : List BP), descP (ps ++ qs) = true → descP qs = true
  | [], _, h => by simpa using h
  | p :: ps', qs, h => by
      have : descP (ps' ++ qs) = true := by
        cases ps' with
        | nil => cases qs with
                 | nil => simp [descP]
                 | cons r rs =>
                     simp only [List.nil_append, List.cons_append, descP,
                       Bool.and_eq_true] at h ⊢
                     exact h.2
        | cons r rs =>
            simp only [List.cons_append, descP, Bool.and_eq_true] at h
            exact h.2
      exact descP_suffix ps' qs this

/-- `isOT_BPList` は連結について分配する。 -/
theorem isOT_BPList_append : ∀ (ps qs : List BP),
    isOT_BPList ps = true → isOT_BPList qs = true → isOT_BPList (ps ++ qs) = true
  | [], _, _, h => by simpa using h
  | p :: ps', qs, hp, hq => by
      simp only [List.cons_append, isOT_BPList, Bool.and_eq_true] at hp ⊢
      exact ⟨hp.1, isOT_BPList_append ps' qs hp.2 hq⟩

/-- 境界条件つきの `descP` の連結。 -/
theorem descP_append : ∀ (ps : List BP) (q : BP) (qs : List BP),
    descP ps = true → descP (q :: qs) = true →
    (∀ p ∈ ps, leBT (BT.trm [q]) (BT.trm [p]) = true) →
    descP (ps ++ q :: qs) = true
  | [], _, _, _, hq, _ => by simpa using hq
  | [p], q, qs, _, hq, hb => by
      simp only [List.cons_append, List.nil_append, descP, Bool.and_eq_true]
      exact ⟨hb p (by simp), hq⟩
  | p :: r :: ps', q, qs, hp, hq, hb => by
      simp only [List.cons_append, descP, Bool.and_eq_true] at hp ⊢
      refine ⟨hp.1, ?_⟩
      have := descP_append (r :: ps') q qs hp.2 hq (fun x hx => hb x (by simp [hx]))
      simpa using this

theorem mem_takeWhile_prop : ∀ {f : BP → Bool} {l : List BP} {x : BP},
    x ∈ l.takeWhile f → f x = true
  | _, [], _, h => by simp at h
  | f, a :: l, x, h => by
      by_cases hfa : f a = true
      · rw [List.takeWhile_cons_of_pos hfa] at h
        rcases List.mem_cons.1 h with rfl | h'
        · exact hfa
        · exact mem_takeWhile_prop h'
      · rw [List.takeWhile_cons_of_neg (by simp [hfa])] at h
        simp at h

theorem isOT_BPList_prefix : ∀ (ps qs : List BP),
    isOT_BPList (ps ++ qs) = true → isOT_BPList ps = true
  | [], _, _ => by simp [isOT_BPList]
  | p :: ps', qs, h => by
      simp only [List.cons_append, isOT_BPList, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, isOT_BPList_prefix ps' qs h.2⟩

theorem oval_trm_lt_ovalBP {ps : List BP} {q : BP}
    (h : ∀ p ∈ ps, ovalBP p < ovalBP q) : oval (BT.trm ps) < ovalBP q := by
  cases q with
  | db v c => exact oval_trm_lt_psi (by simpa using h)

/-- 落とす部分（`t` の先頭より小さい成分）の評価は先頭 principal 未満。 -/
theorem oval_dropWhile_lt : ∀ (as : List BP) (q : BP), descP as = true →
    isOT_BPList as = true → isOT_BP q = true →
    oval (BT.trm (as.dropWhile (fun p => !lessBP p q))) < ovalBP q
  | [], q, _, _, _ => by
      cases q with
      | db v c => simpa using lt_of_lt_of_le (Om_pos v) (Om_le_psi v (oval c))
  | p :: ps, q, hd, hl, hq => by
      simp only [isOT_BPList, Bool.and_eq_true] at hl
      by_cases hpq : lessBP p q = true
      · rw [List.dropWhile_cons_of_neg (by simp [hpq])]
        refine oval_trm_lt_ovalBP (fun r hr => ?_)
        rcases List.mem_cons.1 hr with rfl | hr'
        · exact oval_lt_of_lessBP r q hl.1 hq hpq
        · have hple := descP_le_head p ps hd r hr'
          simp only [leBT, Bool.or_eq_true, beq_iff_eq, lessBT_single] at hple
          have hrp : ovalBP r ≤ ovalBP p := by
            rcases hple with hlt | heq
            · exact le_of_lt (oval_lt_of_lessBP r p (isOT_of_mem_list hl.2 hr') hl.1 hlt)
            · have : r = p := by simpa using heq
              rw [this]
          exact lt_of_le_of_lt hrp (oval_lt_of_lessBP p q hl.1 hq hpq)
      · rw [List.dropWhile_cons_of_pos (by simp [hpq])]
        exact oval_dropWhile_lt ps q (descP_tail hd) hl.2 hq

/-- 加法標準形の連結。`s` の principal 成分のうち `t` の先頭より小さいものは
順序数の和で吸収されるので落とす。 -/
def naddBT : BT → BT → BT
  | s, .trm [] => s
  | .trm as, .trm (q :: qs) => .trm (as.takeWhile (fun p => !lessBP p q) ++ q :: qs)

theorem isOT_naddBT : ∀ (s t : BT), isOT_BT s = true → isOT_BT t = true →
    isOT_BT (naddBT s t) = true
  | s, .trm [], hs, _ => by simpa [naddBT] using hs
  | .trm as, .trm (q :: qs), hs, ht => by
      simp only [isOT_BT, Bool.and_eq_true] at hs ht
      have hsplit := List.takeWhile_append_dropWhile
        (p := fun p => !lessBP p q) (l := as)
      have hlpre : isOT_BPList (as.takeWhile (fun p => !lessBP p q)) = true :=
        isOT_BPList_prefix _ _ (by rw [hsplit]; exact hs.1)
      have hdpre : descP (as.takeWhile (fun p => !lessBP p q)) = true :=
        descP_prefix _ _ (by rw [hsplit]; exact hs.2)
      simp only [naddBT, isOT_BT, Bool.and_eq_true]
      refine ⟨isOT_BPList_append _ _ hlpre ht.1, descP_append _ q qs hdpre ht.2 ?_⟩
      intro p hp
      have := mem_takeWhile_prop hp
      exact leBT_single_of_not_lessBP (by simpa using this)

theorem oval_naddBT : ∀ (s t : BT), isOT_BT s = true → isOT_BT t = true →
    oval (naddBT s t) = oval s + oval t
  | s, .trm [], _, _ => by simp [naddBT]
  | .trm as, .trm (q :: qs), hs, ht => by
      simp only [isOT_BT, Bool.and_eq_true] at hs ht
      have hsplit := List.takeWhile_append_dropWhile
        (p := fun p => !lessBP p q) (l := as)
      have hdrop : oval (BT.trm (as.dropWhile (fun p => !lessBP p q))) < ovalBP q :=
        oval_dropWhile_lt as q hs.2 hs.1 (by
          simp only [isOT_BPList, Bool.and_eq_true] at ht; exact ht.1.1)
      have habs : oval (BT.trm (as.dropWhile (fun p => !lessBP p q))) + ovalBP q = ovalBP q := by
        cases q with
        | db v c => exact add_psi_eq v (oval c) (by simpa using hdrop)
      have hasplit : oval (BT.trm as)
          = oval (BT.trm (as.takeWhile (fun p => !lessBP p q)))
            + oval (BT.trm (as.dropWhile (fun p => !lessBP p q))) := by
        conv_lhs => rw [← hsplit]
        exact oval_append _ _
      simp only [naddBT]
      rw [oval_append, hasplit, oval_trm_cons]
      have key : oval (BT.trm (as.dropWhile (fun p => !lessBP p q)))
            + (ovalBP q + oval (BT.trm qs)) = ovalBP q + oval (BT.trm qs) := by
        rw [← add_assoc, habs]
      rw [add_assoc, key]

/-! ## 残り: [Buc1] Lemma 2.1 と 2.2(c) -/

/-- \(D_0D_\omega0\)。主定理の値域の上界にあたる項。 -/
def DzeroDomegaZeroP : BT := Dprin 0 (Dprin ⊤ BZero)

@[simp] theorem oval_DzeroDomegaZeroP :
    oval DzeroDomegaZeroP = psi 0 (psi ⊤ 0) := by
  simp [DzeroDomegaZeroP]

/-- [Buc1] Lemma 2.1: \(o\) は \(OT\) 上で順序を保つ。 -/
theorem oval_lt_iff {s t : BT} (hs : s ∈ OT) (ht : t ∈ OT) :
    lessBT s t = true ↔ oval s < oval t := by
  constructor
  · exact fun h => oval_lt_of_lessBT s t hs ht h
  · intro h
    rcases lessBT_linear_trichotomy s t with h1 | rfl | h1
    · exact h1
    · exact absurd h (lt_irrefl _)
    · exact absurd (lt_trans h (oval_lt_of_lessBT t s ht hs h1)) (lt_irrefl _)

/-- \(o\) は \(OT\) 上で単射。 -/
theorem oval_injOn {s t : BT} (hs : s ∈ OT) (ht : t ∈ OT) (h : oval s = oval t) : s = t := by
  rcases lessBT_linear_trichotomy s t with h1 | h1 | h1
  · exact absurd ((oval_lt_iff hs ht).1 h1) (by rw [h]; exact lt_irrefl _)
  · exact h1
  · exact absurd ((oval_lt_iff ht hs).1 h1) (by rw [h]; exact lt_irrefl _)

/-- [Buc1] Lemma 2.2(c): \(D_0D_\omega0\) 未満の順序数項の像はちょうど
\(\psi_0\psi_\omega0\) の始切片。 -/
theorem isOT_DzeroDomegaZeroP : isOT_BT DzeroDomegaZeroP = true := by decide

theorem mem_OT_DzeroDomegaZeroP : DzeroDomegaZeroP ∈ OT := isOT_DzeroDomegaZeroP

/-- 全射性の核。\(C_0(\psi_\omega0)\) の元はすべて順序数項で表される。

閉包に関する帰納法で示す。生成規則ごとに:

- \(b\lt Ω_0=1\) と \(0\) は `BZero`
- \(x+y\) は加法標準形（principal 成分の降順列）への正規化が要る
- \(\psi_v(ξ)\) は \(ξ\) を表す項 \(s\) から \(D_vs\) を作る。ここで \(D_vs\) が
  順序数項であるためには \(ξ\in C_v(ξ)\)（標準形条件）が要り、そのために
  \(\psi_v(ξ)=\psi_v(ξ')\) なる最小の \(ξ'\) を取り直す段が入る
-/
def SurjCore : Prop :=
  ∀ a ∈ CSet 0 (psi ⊤ 0), ∃ t : BT, isOT_BT t = true ∧ oval t = a

/-- \(ψ\) の場合だけを残した形。`0` と `+` の場合はここで閉じる。 -/
theorem surj_core_of_psi
    (hpsi : ∀ (v : ℕ∞) (x : Ordinal.{0}), x < psi ⊤ 0 →
      (∃ s : BT, isOT_BT s = true ∧ oval s = x) →
      ∃ t : BT, isOT_BT t = true ∧ oval t = psi v x) : SurjCore := by
  intro a ha
  refine CSet_induction (P := fun c => ∃ t : BT, isOT_BT t = true ∧ oval t = c) ?_ ?_ ?_ ?_ ha
  · intro b h
    have hb : b = 0 := by
      rw [Om_zero] at h
      exact Order.lt_one_iff.1 h
    exact ⟨BZero, by decide, by simp [hb]⟩
  · exact ⟨BZero, by decide, by simp⟩
  · rintro x _ ⟨s, hs, hsv⟩ y _ ⟨t, ht, htv⟩
    exact ⟨naddBT s t, isOT_naddBT s t hs ht, by
      rw [oval_naddBT s t hs ht, hsv, htv]⟩
  · rintro x _ ih hx v _
    exact hpsi v x hx ih

/-- 残る唯一の穴。`surj_core_of_psi` により、示すべきは \(ψ\) の場合だけである。

\(x\ltψ_ω0\) が項 \(s\) で表されるとき、\(\psi_v(x)\) を表す項が要る。素直な候補
\(D_vs\) が順序数項であるためには \(G_v(s)\) の元がすべて \(\lt_Bs\)、すなわち
\(x\in C_v(x)\) が要る。これは一般には成り立たないので、\(\psi_v\) の値が同じ引数の
うち適切なものを取り直すことになる。

[Buc1] §1 の定義では、この条件が閉包の生成規則そのものに入っている。

\[
C_v^{n+1}(α)=C_v^n(α)\cup\{γ\mid P(γ)\subseteq C_v^n(α)\}
\cup\{\psi_uξ\midξ\inα\cap C_v^n(α)\ \land\ ξ\in C_u(ξ)\ \land\ u\leω\}
\]

この `CGen` は条件を落とした形（[Buc1] の (C1)(C2)(C3) による特徴づけ）で、
[Buc1] の Remark によれば集合としては一致する。ただし全射性に効くのは条件つきの
ほうで、[Buc1] Lemma 1.4(b) が

\[
γ\in C_v(α)\ \land\ Ω_v\leγ\in P\ \Longrightarrow\
\exists u,ξ\ (γ=\psi_uξ\ \land\ ξ\inα\cap C_v(α)\cap C_u(ξ))
\]

を与える。ここで得られる \(ξ\in C_u(ξ)\) がそのまま \(D_us\) の標準形条件になる。

したがって残る作業は、`CGen` の `psi` 生成規則に \(x\in C_v(x)\) を足して [Buc1] の
定義に揃えることである。その際:

- `psi_lt_psi` は仮定 \(x\in C_u(x)\) つきになる（[Buc1] Lemma 1.3 と同じ形）
- `mem_CSet_of_gatherBT` は順序数項限定に直し、Lemma 2.1 と相互再帰にする
- `CStage` は上界評価にしか使わないので条件なしのままでよい -/
theorem surj_core : SurjCore := by
  sorry

/-- [Buc1] Lemma 2.2(c) のうち易しい向き。 -/
theorem oval_image_subset :
    oval '' {t : BT | t ∈ OT ∧ lessBT t DzeroDomegaZeroP = true}
      ⊆ {a : Ordinal.{0} | a < psi 0 (psi ⊤ 0)} := by
  rintro a ⟨t, ⟨htOT, htlt⟩, rfl⟩
  have := (oval_lt_iff htOT mem_OT_DzeroDomegaZeroP).1 htlt
  simpa using this

theorem oval_surjOn_below :
    oval '' {t : BT | t ∈ OT ∧ lessBT t DzeroDomegaZeroP = true}
      = {a : Ordinal.{0} | a < psi 0 (psi ⊤ 0)} := by
  refine Set.Subset.antisymm oval_image_subset ?_
  intro a ha
  simp only [Set.mem_setOf_eq] at ha
  obtain ⟨t, htOT, rfl⟩ := surj_core a (lt_psi_mem ha)
  refine ⟨t, ⟨htOT, ?_⟩, rfl⟩
  refine (oval_lt_iff htOT mem_OT_DzeroDomegaZeroP).2 ?_
  simpa using ha

/-! ## ここから先（未着手）

- 評価写像 \(o:BT\to\mathrm{Ord}\)、\(o(D_ua)=ψ_u(o(a))\)、\(o(t_0+t_1)=o(t_0)+o(t_1)\)
- [Buc1] Lemma 2.1: `s ∈ OT → t ∈ OT → (lessBT s t = true ↔ o s < o t)`
- [Buc1] Lemma 2.2(c): `o '' {t ∈ OT | lessBT t DzeroDomegaZero} = {α | α < psi 0 (psi ⊤ 0)}`
-/

end Bijectivity
