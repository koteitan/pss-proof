import Bijectivity.«22-pair-sequence-analysis»
import Bijectivity.Psi

/-!
# 構成した順序型と Buchholz の \(ψ_0ψ_ω0\) の一致

`Cited.lean` の \(o\) は \((OT_{\textrm{B}},<_{\textrm{B}})\) の順序型として構成した
写像で、`psi0psiOmega0` はその \(D_0D_\omega0\) 未満の部分の順序型である。
一方 `Psi.lean` の `oval` は [Buc1] の評価写像そのもの、`psi 0 (psi ⊤ 0)` は
Buchholz の \(\psi_0(\psi_\omega(0))\) そのものである。

この 2 つが一致することをここで示す。どちらも
\(S=\{t\in OT_{\textrm{B}}\mid t<_{\textrm{B}}D_0D_\omega0\}\) から順序数の始切片への
順序同型なので、始切片への順序同型の一意性から一致する。証明は \(<_{\textrm{B}}\) の
整礎性による超限帰納法で、両者が同じ上限表示

\[
o(t)=\sup\{o(u)+1\mid u\in S,\ u<_{\textrm{B}}t\}
\]

を満たすことを使う。
-/

namespace Bijectivity

open PSS

/-- \(D_0D_\omega0\) 未満の順序数項全体。 -/
def Below : Set BT := {t : BT | t ∈ OT_B ∧ lessBT t DzeroDomegaZero = true}

theorem DzeroDomegaZeroP_eq : DzeroDomegaZeroP = DzeroDomegaZero := rfl

theorem mem_OT_of_below {t : BT} (h : t ∈ Below) : t ∈ OT := h.1.1

/-- `Below` は \(<_{\textrm{B}}\) について下に閉じている。 -/
theorem below_of_lt {t u : BT} (ht : t ∈ Below) (huOTB : u ∈ OT_B)
    (h : lessBT u t = true) : u ∈ Below :=
  ⟨huOTB, lessBT_linear_trans _ _ _ h ht.2⟩

/-! ## `oval` の側 -/

theorem oval_lt_of_below {t : BT} (h : t ∈ Below) : oval t < psi 0 (psi ⊤ 0) := by
  have := (oval_lt_iff (mem_OT_of_below h) mem_OT_DzeroDomegaZeroP).1
    (by rw [DzeroDomegaZeroP_eq]; exact h.2)
  simpa using this

theorem oval_surj_below {α : Ordinal.{0}} (h : α < psi 0 (psi ⊤ 0)) :
    ∃ t : BT, t ∈ Below ∧ oval t = α := by
  have hmem : α ∈ oval '' {t : BT | t ∈ OT ∧ lessBT t DzeroDomegaZeroP = true} := by
    rw [oval_surjOn_below]; exact h
  obtain ⟨t, ⟨htOT, htlt⟩, hto⟩ := hmem
  rw [DzeroDomegaZeroP_eq] at htlt
  exact ⟨t, ⟨(OT_iff_OT_B_of_lt htlt).mp htOT, htlt⟩, hto⟩

/-- `oval` も同じ上限表示を満たす。 -/
theorem oval_eq_iSup_below {t : BT} (ht : t ∈ Below) :
    oval t = ⨆ u : {u : BT // u ∈ OT_B ∧ lessBT u t = true}, (oval u.1 + 1) := by
  refine le_antisymm (le_of_forall_lt fun a ha => ?_) (Ordinal.iSup_le_iff.mpr ?_)
  · obtain ⟨u, hu, huo⟩ := oval_surj_below (lt_trans ha (oval_lt_of_below ht))
    have hult : lessBT u t = true :=
      (oval_lt_iff (mem_OT_of_below hu) (mem_OT_of_below ht)).2 (by rw [huo]; exact ha)
    have hle := Ordinal.le_iSup
      (fun u : {u : BT // u ∈ OT_B ∧ lessBT u t = true} => oval u.1 + 1) ⟨u, hu.1, hult⟩
    exact lt_of_lt_of_le (by rw [huo] at hle ⊢; exact Order.lt_succ_iff.mpr le_rfl) hle
  · rintro ⟨u, huOTB, hult⟩
    have hu : u ∈ Below := below_of_lt ht huOTB hult
    have := Order.succ_le_of_lt
      ((oval_lt_iff (mem_OT_of_below hu) (mem_OT_of_below ht)).1 hult)
    rwa [Order.succ_eq_add_one] at this

/-! ## 一致 -/

/-- \(D_0D_\omega0\) 未満では構成した \(o\) と [Buc1] の評価写像は一致する。 -/
theorem o_eq_oval : ∀ t : BT, t ∈ Below → o t = oval t := by
  intro t
  induction t using OT_B_wellFounded.induction with
  | _ t ih =>
      intro ht
      rw [o_eq_iSup_below ht.1, oval_eq_iSup_below ht]
      refine iSup_congr fun u => ?_
      rw [ih u.1 ⟨u.2.1, ht.1, u.2.2⟩ (below_of_lt ht u.2.1 u.2.2)]

/-- **構成した順序型は Buchholz の \(\psi_0(\psi_\omega(0))\) そのものである。** -/
theorem psi0psiOmega0_eq : psi0psiOmega0 = psi 0 (psi ⊤ 0) := by
  refine le_antisymm (le_of_forall_lt fun a ha => ?_) (le_of_forall_lt fun a ha => ?_)
  · obtain ⟨t, htOTB, htlt, hto⟩ := o_surj_below_psi ha
    have ht : t ∈ Below := ⟨htOTB, htlt⟩
    rw [← hto, o_eq_oval t ht]
    exact oval_lt_of_below ht
  · obtain ⟨t, ht, hto⟩ := oval_surj_below ha
    rw [← hto, ← o_eq_oval t ht]
    exact o_lt_psi ht.1 ht.2

/-! ## 原文の言明そのもの

原文の命題（変換写像の順序数への全単射性）は Buchholz の \(\psi_0\psi_\omega0\) を
値域の上界に置く。`psi0psiOmega0_eq` によりそれがそのまま書ける。
-/

/-- 原文の命題（変換写像の順序数への全単射性）。上界は Buchholz の
\(\psi_0(\psi_\omega(0))\) そのものである。 -/
theorem oTrans_bijOn_psi :
    Set.BijOn (fun M => o (PSS.Trans M)) {M : PS | CTPS M}
      {α : Ordinal.{0} | α < psi 0 (psi ⊤ 0)} := by
  rw [← psi0psiOmega0_eq]
  exact oTrans_bijOn

/-- 原文の系（ペア数列の解析）(1)。上界は Buchholz の評価写像の値そのもの。 -/
theorem analysis_ordinal_oval {M : PS} (hM : CTPS M) :
    Set.BijOn (fun N => oval (PSS.Trans N)) {N : PS | CTPS N ∧ N <ₚ M}
      {α : Ordinal.{0} | α < oval (PSS.Trans M)} := by
  have hbelow : ∀ N : PS, CTPS N → PSS.Trans N ∈ Below := fun N hN =>
    ⟨OTB_Trans_of_CTPS hN, trans_lt_bound hN⟩
  have hEq : ∀ N : PS, CTPS N → o (PSS.Trans N) = oval (PSS.Trans N) := fun N hN =>
    o_eq_oval _ (hbelow N hN)
  have hfun : Set.EqOn (fun N => o (PSS.Trans N)) (fun N => oval (PSS.Trans N))
      {N : PS | CTPS N ∧ N <ₚ M} := fun N hN => hEq N hN.1
  rw [← hEq M hM]
  exact (analysis_ordinal hM).congr hfun

end Bijectivity
