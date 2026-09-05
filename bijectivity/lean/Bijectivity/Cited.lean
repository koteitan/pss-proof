import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Family
import Bijectivity.Defs
import «Buchholz-1986».«Buchholz-1986-2.1-order»
import «Buchholz-1986».«Buchholz-1986-3.2»
import «Buchholz-rel-ord».«Buchholz-rel-ord-6»
import «OTB-well-founded-syntactic».«OTB-well-founded-syntactic-main»

/-!
# 順序数側の評価写像 \(o\)

原文は「表記」節で \(\psi_ua\)、\(D_ua\)、\(G_ua\)、\(o\) を [Buc1] から引くと明記している。
本ファイルはそのうち \(o\) と \(\psi_0\psi_\omega0\) を**引用ではなく構成**し、
原文が使う性質のうち構成から出るものは定理として与える。**残る `axiom` は 2 本だけ**。

引用元:
* [Buc1] W. Buchholz, “A new system of proof-theoretic ordinal functions”,
  Annals of Pure and Applied Logic 32 (1986), pp. 195–207 — 評価写像 \(o\)、
  \(\psi_u\)、Lemma 2.1 / 2.2(c) / 2.3(b)。
* [Buc2] W. Buchholz, “Relating ordinals to proofs in a perspicuous way”,
  unpublished — Theorem 1.4(a) / Lemma 1.6。
* [3] p進大好きbot,「変換写像による解析」, 巨大数研究 Wiki ユーザーブログ — 命題 10 / 命題 11。

## 構成

\((OT_{\textrm{B}},<_{\textrm{B}})\) は

* 整礎（`OT_B_wellFounded`、`OTB-well-founded-syntactic` が**仮定ゼロ**で証明）
* 三分律（`lessBT_linear_trichotomy`）と推移律（`lessBT_linear_trans`）

を満たすので整列順序である。そこで \(o\) をその**順序型への順序同型**
（`Ordinal.typein`）として定め、\(\psi_0\psi_\omega0\) を
\(\{t\in OT_{\textrm{B}}\mid t<_{\textrm{B}}D_0D_\omega0\}\) の順序型として定める。
\(D_0D_\omega0\) 自身は \(D_\omega\) を含むので \(OT_{\textrm{B}}\) の外にあり、
そこだけ \(o\) の値を \(\psi_0\psi_\omega0\) と置く。

これで [Buc1] Lemma 2.1 / 2.2(c) にあたる性質（順序を保つこと・初期切片への全射性・
\(o(0)=0\)・\(o(D_00)=1\)）は**すべて定理**になる。

## 残る 2 本の `axiom`

| axiom | 出典 | 検証 |
|---|---|---|
| `o_addBT` | [Buc1] の加法標準形 | — |
| `o_iSup_operB` | [Buc2] Theorem 1.4(a) / Lemma 1.6 | `Audit-operB.lean` で小 \(OT_{\textrm{B}}\) プール全数検証 |

どちらも \(OT_{\textrm{B}}\) 上でしか主張していない。`o_iSup_operB`（基本列の共終性）は
本リポジトリの `operB` が訂正 A23 入りなので引用だけでは済まず、`Audit-operB.lean` が
小さなプール上で全数検証している。

## 🚨 `OT_B` の仮定は落とせない

`BT` 全体では \(<_{\textrm{B}}\) は**整礎ではない**（下の `descChain`）。
\(o\) の単調性を `BT` 全体で述べると順序数の無限降下列ができて矛盾する。
-/

namespace Bijectivity

open PSS

/-- \(D_0D_\omega0\)（原文の \(\textrm{Trans}\) の像の上界にあたる項）。 -/
def DzeroDomegaZero : BT := Dprin 0 (Dprin ⊤ (BT.trm []))

/-! ## `BT` 全体では \(<_{\textrm{B}}\) が整礎でないことの証拠（機械検証） -/

/-- \(x_0=D_10\)、\(x_{n+1}=D_0x_n\)。 -/
def descChain : ℕ → BT
  | 0 => Dprin 1 BZero
  | n + 1 => Dprin 0 (descChain n)

private theorem lessBT_Dprin_zero (a b : BT) :
    lessBT (Dprin 0 a) (Dprin 0 b) = lessBT a b := by
  simp [Dprin, lessBT, lessBPList, lessBP]

/-- `descChain` は \(<_{\textrm{B}}\) について狭義降下する。したがって \(o\) の単調性から
`OT` の仮定を落とすと順序数の無限降下列ができてしまう。 -/
theorem descChain_lt : ∀ n : ℕ, lessBT (descChain (n + 1)) (descChain n) = true
  | 0 => by decide
  | n + 1 => by
      show lessBT (Dprin 0 (descChain (n + 1))) (Dprin 0 (descChain n)) = true
      rw [lessBT_Dprin_zero]
      exact descChain_lt n

/-- その列は \(n\geq2\) で順序数項から外れる（だから \(OT_{\textrm{B}}\) 上では矛盾しない）。 -/
theorem descChain_not_OT : isOT_BT (descChain 2) = false := by decide

/-! ## \((OT_{\textrm{B}},<_{\textrm{B}})\) は整列順序 -/

/-- \(OT_{\textrm{B}}\) の元の型。 -/
abbrev OTBsub : Type := {t : BT // t ∈ OT_B}

/-- その上の \(<_{\textrm{B}}\)。 -/
def rOTB (a b : OTBsub) : Prop := lessBT a.1 b.1 = true

instance : IsWellFounded OTBsub rOTB :=
  ⟨Subrelation.wf (r := InvImage (fun a b : BT => a ∈ OT_B ∧ b ∈ OT_B ∧ lessBT a b = true)
      (fun x : OTBsub => x.1))
    (fun {a b} h => ⟨a.2, b.2, h⟩)
    (InvImage.wf (fun x : OTBsub => x.1) OT_B_wellFounded)⟩

instance : Std.Trichotomous rOTB :=
  ⟨fun a b hab hba => by
    rcases lessBT_linear_trichotomy a.1 b.1 with h | h | h
    · exact absurd h hab
    · exact Subtype.ext h
    · exact absurd h hba⟩

instance : IsTrans OTBsub rOTB :=
  ⟨fun _ _ _ hab hbc => lessBT_linear_trans _ _ _ hab hbc⟩

instance : IsWellOrder OTBsub rOTB := IsWellOrder.mk

/-! ## 評価写像 \(o\) -/

/-- \(OT_{\textrm{B}}\) の順序型への順序同型（[Buc1] の \(o\) の \(OT_{\textrm{B}}\) 部分）。 -/
noncomputable def tpOTB (a : OTBsub) : Ordinal.{0} :=
  (Ordinal.typein rOTB).toRelEmbedding a

open Classical in
private noncomputable def oOTB (t : BT) : Ordinal.{0} :=
  if h : t ∈ OT_B then tpOTB ⟨t, h⟩ else 0

/-- \(\psi_0\psi_\omega0\)。原文の \(o\circ\textrm{Trans}\) の値域の上界＝
\(\{t\in OT_{\textrm{B}}\mid t<_{\textrm{B}}D_0D_\omega0\}\) の順序型。 -/
noncomputable def psi0psiOmega0 : Ordinal.{0} :=
  ⨆ t : {t : BT // t ∈ OT_B ∧ lessBT t DzeroDomegaZero = true}, (oOTB t.1 + 1)

open Classical in
/-- [Buc1] の評価写像 \(o\)。 -/
noncomputable def o (t : BT) : Ordinal.{0} :=
  if t = DzeroDomegaZero then psi0psiOmega0 else oOTB t

theorem DzeroDomegaZero_not_OTB : DzeroDomegaZero ∉ OT_B := by
  intro h
  have : dfree_BT DzeroDomegaZero = true := h.2
  simp [DzeroDomegaZero, Dprin, dfree_BT, dfree_BP, dfree_BPList] at this

theorem o_eq_tpOTB {t : BT} (h : t ∈ OT_B) : o t = tpOTB ⟨t, h⟩ := by
  have hne : t ≠ DzeroDomegaZero := by
    intro he; exact DzeroDomegaZero_not_OTB (he ▸ h)
  unfold o oOTB
  rw [if_neg hne, dif_pos h]

/-- \(o(D_0D_\omega0)=\psi_0\psi_\omega0\)。 -/
theorem o_DzeroDomegaZero : o DzeroDomegaZero = psi0psiOmega0 := by
  unfold o; rw [if_pos rfl]

/-! ## [Buc1] Lemma 2.1 / 2.2(c) にあたる性質（すべて定理） -/

/-- \(o\) は \(OT_{\textrm{B}}\) 上で \(<_{\textrm{B}}\) を保つ。 -/
theorem o_lt_of_lessBT {s t : BT} (hs : s ∈ OT_B) (ht : t ∈ OT_B)
    (h : lessBT s t = true) : o s < o t := by
  rw [o_eq_tpOTB hs, o_eq_tpOTB ht]
  exact (Ordinal.typein_lt_typein rOTB).mpr h

/-- \(D_0D_\omega0\) 未満の項は \(\psi_0\psi_\omega0\) 未満へ写る。 -/
theorem o_lt_psi {s : BT} (hs : s ∈ OT_B) (h : lessBT s DzeroDomegaZero = true) :
    o s < psi0psiOmega0 := by
  have hle : oOTB s + 1 ≤ psi0psiOmega0 :=
    Ordinal.le_iSup (fun t : {t : BT // t ∈ OT_B ∧ lessBT t DzeroDomegaZero = true} =>
      oOTB t.1 + 1) ⟨s, hs, h⟩
  have hos : o s = oOTB s := by rw [o_eq_tpOTB hs]; unfold oOTB; rw [dif_pos hs]
  rw [hos]
  exact lt_of_lt_of_le (Order.lt_succ _)
    (by rwa [← Order.succ_eq_add_one] at hle)

/-- \(o\) は \(OT_{\textrm{B}}\) の初期切片へ全射（[Buc1] Lemma 2.2(c)）。 -/
theorem o_surj_below {t₀ : BT} (h₀ : t₀ ∈ OT_B) {α : Ordinal} (h : α < o t₀) :
    ∃ t : BT, t ∈ OT_B ∧ lessBT t t₀ = true ∧ o t = α := by
  rw [o_eq_tpOTB h₀] at h
  have hlt : α < Ordinal.type rOTB :=
    lt_trans h (Ordinal.typein_lt_type rOTB ⟨t₀, h₀⟩)
  obtain ⟨s, hs⟩ := Ordinal.typein_surj rOTB hlt
  refine ⟨s.1, s.2, ?_, ?_⟩
  · have hr : rOTB s ⟨t₀, h₀⟩ := by
      refine (Ordinal.typein_lt_typein rOTB).mp ?_
      show tpOTB s < tpOTB ⟨t₀, h₀⟩
      rw [show tpOTB s = α from hs]
      exact h
    exact hr
  · rw [o_eq_tpOTB s.2]
    exact hs

/-- \(\psi_0\psi_\omega0\) 未満の順序数はすべて \(D_0D_\omega0\) 未満の項の値。 -/
theorem o_surj_below_psi {α : Ordinal} (h : α < psi0psiOmega0) :
    ∃ t : BT, t ∈ OT_B ∧ lessBT t DzeroDomegaZero = true ∧ o t = α := by
  obtain ⟨u, hu⟩ := Ordinal.lt_iSup_iff.mp h
  have huOTB : u.1 ∈ OT_B := u.2.1
  have hou : o u.1 = oOTB u.1 := by
    rw [o_eq_tpOTB huOTB]; unfold oOTB; rw [dif_pos huOTB]
  rcases lt_or_eq_of_le (Order.lt_succ_iff.mp (by rwa [Order.succ_eq_add_one]) :
      α ≤ oOTB u.1) with hlt | heq
  · obtain ⟨t, htOTB, htlt, hto⟩ := o_surj_below huOTB (by rw [hou]; exact hlt)
    exact ⟨t, htOTB, lessBT_linear_trans _ _ _ htlt u.2.2, hto⟩
  · exact ⟨u.1, huOTB, u.2.2, by rw [hou, heq]⟩

private theorem BZero_mem_OTB : BZero ∈ OT_B :=
  ⟨by show isOT_BT BZero = true; decide, by show dfree_BT BZero = true; decide⟩

private theorem DzeroZero_mem_OTB : (Dprin 0 BZero : BT) ∈ OT_B :=
  ⟨by show isOT_BT (Dprin 0 BZero) = true; decide,
   by show dfree_BT (Dprin 0 BZero) = true; decide⟩

/-- \(0\) 未満の項は無い。 -/
private theorem not_lessBT_BZero (t : BT) : lessBT t BZero = false := by
  rcases t with ⟨ps⟩; cases ps <;> simp [BZero, lessBT, lessBPList]

/-- \(D_00\) 未満の項は \(0\) だけ。 -/
private theorem eq_BZero_of_lessBT_DzeroZero {t : BT}
    (h : lessBT t (Dprin 0 BZero) = true) : t = BZero := by
  rcases t with ⟨ps⟩
  cases ps with
  | nil => rfl
  | cons p rest =>
      exfalso
      rcases p with ⟨v, b⟩
      simp only [Dprin, BZero, lessBT, lessBPList, lessBP, Bool.or_eq_true,
        Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      rcases h with (hv | ⟨-, hb⟩) | ⟨-, hnil⟩
      · exact absurd hv (by simp)
      · rcases b with ⟨cs⟩; cases cs <;> simp [BZero, lessBT, lessBPList] at hb
      · cases rest <;> simp [lessBPList] at hnil

/-- \(o(0)=0\)。 -/
theorem o_BZero : o BZero = 0 := by
  by_contra hne
  have hpos : (0 : Ordinal) < o BZero :=
    lt_of_le_of_ne zero_le' (Ne.symm hne)
  obtain ⟨t, -, hlt, -⟩ := o_surj_below BZero_mem_OTB hpos
  rw [not_lessBT_BZero t] at hlt
  exact Bool.noConfusion hlt

/-- \(o(D_00)=1\)。 -/
theorem o_DzeroZero : o (Dprin 0 BZero) = 1 := by
  have hzd : lessBT BZero (Dprin 0 BZero) = true := by decide
  have h0 : (0 : Ordinal) < o (Dprin 0 BZero) := by
    have := o_lt_of_lessBT BZero_mem_OTB DzeroZero_mem_OTB hzd
    rwa [o_BZero] at this
  refine le_antisymm ?_ ?_
  · by_contra hgt
    push_neg at hgt
    obtain ⟨t, -, hlt, hto⟩ := o_surj_below DzeroZero_mem_OTB hgt
    rw [eq_BZero_of_lessBT_DzeroZero hlt, o_BZero] at hto
    exact absurd hto.symm (by simp)
  · have := Order.succ_le_of_lt h0
    rwa [Order.succ_eq_add_one, zero_add] at this

/-! ## 残る 2 本の外部引用 -/

/-- [Buc1] の加法標準形: \(o\) は項の加法を順序数の加法に写す。 -/
axiom o_addBT {s t : BT} (hs : s ∈ OT_B) (ht : t ∈ OT_B) (hst : addBT s t ∈ OT_B) :
    o (addBT s t) = o s + o t

/-- [Buc2] Theorem 1.4(a) 及び Lemma 1.6: \(\textrm{dom}(t)=\omega\) のとき
\(t\) の基本列は \(o(t)\) に収束する。`Audit-operB.lean` が小さな
\(OT_{\textrm{B}}\) プール上で全数検証している。 -/
axiom o_iSup_operB {t : BT} (ht : t ∈ OT_B) (h : domTag t = BDom.naturals) :
    ⨆ m : ℕ, o (operB t (numBT m)) = o t

/-! ## `dom` の記法 -/

/-- 原文の \(\textrm{dom}(t)=1\)（後続）。 -/
def domIsOne (t : BT) : Prop := domTag t = BDom.zeroOnly

/-- 原文の \(\textrm{dom}(t)=\omega\)。 -/
def domIsOmega (t : BT) : Prop := domTag t = BDom.naturals

end Bijectivity
