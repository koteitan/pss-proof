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
| (1) | \(ψ_u(α)\) の存在（\(C_u(α)\neq\mathrm{Ord}\)、基数評価 \(|C_u(α)|<Ω_{u+1}\)） | **済** |
| (2) | \(C_u(α)\cap Ω_{u+1}=ψ_u(α)\)（崩壊の要） | **済** |
| (3) | [Buc1] Lemma 2.1（評価 \(o\) が順序を保つ） | 未着手 |
| (4) | [Buc1] Lemma 2.2(c)（像が \(ψ_0ψ_ω0\) の始切片） | 未着手 |

(1)(2) から出たもの: \(Ω_u\leψ_u(α)<Ω_{u+1}\)、\(ψ\) の広義・狭義単調性、
\(ψ_u(α)\) が加法的 principal であること。
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

theorem CGen_stage {u : ℕ∞} {a b : Ordinal.{0}}
    (h : CGen u a (fun x _ v => psi v x) b) : ∃ n, b ∈ CStage u a n := by
  induction h with
  | lt_Om hb => exact ⟨0, Or.inl hb⟩
  | zero => exact ⟨0, Or.inr rfl⟩
  | add _ _ ihx ihy =>
      obtain ⟨n, hn⟩ := ihx
      obtain ⟨m, hm⟩ := ihy
      exact ⟨max n m + 1, Or.inl (Or.inr ⟨_, CStage_mono (le_max_left n m) hn,
        _, CStage_mono (le_max_right n m) hm, rfl⟩)⟩
  | psi hx v _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, Or.inr ⟨v, _, hn, hx, rfl⟩⟩

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
  exact psi_not_mem u a (CGen.lt_Om (not_le.1 hcon))

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

theorem le_of_Om_lt_OmSucc {u v : ℕ∞} (h : Om v < OmSucc u) : v ≤ u := by
  by_contra hc
  exact absurd (OmSucc_le_Om (not_le.1 hc)) (not_le.2 h)

/-! ### \(C_u(α)\) の \(α\) についての単調性 -/

theorem CGen_mono_arg {u : ℕ∞} {x y : Ordinal.{0}} (h : x ≤ y) {b : Ordinal.{0}}
    (hb : CGen u x (fun z _ v => psi v z) b) : CGen u y (fun z _ v => psi v z) b := by
  induction hb with
  | lt_Om h' => exact CGen.lt_Om h'
  | zero => exact CGen.zero
  | add _ _ ihx ihy => exact CGen.add ihx ihy
  | psi hz v _ ih => exact CGen.psi (lt_of_lt_of_le hz h) v ih

theorem psi_mono {u : ℕ∞} {x y : Ordinal.{0}} (h : x ≤ y) : psi u x ≤ psi u y := by
  rw [psi_eq]
  exact csInf_le' (fun hmem => psi_not_mem u y (CGen_mono_arg h hmem))

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
    have := CGen.add (lt_psi_mem hx) (lt_psi_mem (lt_of_le_of_lt hey hy))
    rwa [hsplit] at this
  exact psi_not_mem u a hmem

/-! ### (2) 崩壊の要 -/

theorem mem_CSet_lt_psi (u : ℕ∞) (a : Ordinal.{0}) {c : Ordinal.{0}}
    (hc : c ∈ CSet u a) : c < OmSucc u → c < psi u a := by
  induction hc with
  | lt_Om h => exact fun _ => lt_of_lt_of_le h (Om_le_psi u a)
  | zero => exact fun _ => lt_of_lt_of_le (Om_pos u) (Om_le_psi u a)
  | @add x y _ _ ihx ihy =>
      intro h
      have hxlt : x < OmSucc u := lt_of_le_of_lt (le_self_add : x ≤ x + y) h
      have hylt : y < OmSucc u := lt_of_le_of_lt (le_add_self : y ≤ x + y) h
      exact add_lt_psi (ihx hxlt) (ihy hylt)
  | @psi x hxa v hx _ =>
      intro h
      have hvu : v ≤ u := le_of_Om_lt_OmSucc (lt_of_le_of_lt (Om_le_psi v x) h)
      rcases lt_or_eq_of_le hvu with hv | hv
      · exact lt_of_lt_of_le (psi_lt_OmSucc v x)
          (le_trans (OmSucc_le_Om hv) (Om_le_psi u a))
      · subst hv
        rcases lt_or_eq_of_le (psi_mono (le_of_lt hxa) : psi v x ≤ psi v a) with hlt | heq
        · exact hlt
        · exact absurd (heq ▸ CGen.psi hxa v hx) (psi_not_mem v a)

/-- \(x<y\) かつ \(x\in C_u(y)\) なら \(ψ_u(x)<ψ_u(y)\)（狭義単調性）。 -/
theorem psi_lt_psi {u : ℕ∞} {x y : Ordinal.{0}} (hxy : x < y) (hx : x ∈ CSet u y) :
    psi u x < psi u y := by
  rcases lt_or_eq_of_le (psi_mono (le_of_lt hxy)) with h | h
  · exact h
  · exact absurd (h ▸ CGen.psi hxy u hx) (psi_not_mem u y)

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

/-! ## ここから先（未着手）

- 評価写像 \(o:BT\to\mathrm{Ord}\)、\(o(D_ua)=ψ_u(o(a))\)、\(o(t_0+t_1)=o(t_0)+o(t_1)\)
- [Buc1] Lemma 2.1: `s ∈ OT → t ∈ OT → (lessBT s t = true ↔ o s < o t)`
- [Buc1] Lemma 2.2(c): `o '' {t ∈ OT | lessBT t DzeroDomegaZero} = {α | α < psi 0 (psi ⊤ 0)}`
-/

end Bijectivity
