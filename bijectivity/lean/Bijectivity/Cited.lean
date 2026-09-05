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

## 残る 1 本の `axiom`

| axiom | 出典 | 検証 |
|---|---|---|
| `fseq_cofinal` | [Buc2] Theorem 1.4(a) / Lemma 1.6 | `Audit-operB.lean` で小 \(OT_{\textrm{B}}\) プール全数検証 |

[Buc1] の加法標準形のうち原文が使う分（\(o(s+_{\textrm{B}}D_00)=o(s)+1\)）は
`o_addBT_DzeroZero` として定理にしてある。残る `fseq_cofinal` は
**順序数を含まない純粋に構文的な主張**（基本列が初期切片で共終であること）なので、
`Audit-operB.lean` がその形のまま小さなプール上で全数検証できる。
本リポジトリの `operB` は訂正 A23 入りなので、引用だけでは済まないため。

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

/-! ## \(+_{\textrm{B}}D_00\) は \(OT_{\textrm{B}}\) の直後者（[Buc1] の加法標準形のうち使う分） -/

/-- `lessBP` は単項項の `lessBT` そのもの。 -/
private theorem lessBP_eq_lessBT (p q : BP) :
    lessBP p q = lessBT (BT.trm [p]) (BT.trm [q]) := by
  simp [lessBT, lessBPList]

private theorem lessBP_irrefl (p : BP) : lessBP p p = false := by
  rw [lessBP_eq_lessBT]; exact lessBT_linear_irrefl _

/-- \(D_00\) より小さい principal は無い。 -/
private theorem not_lessBP_D00 (p : BP) : lessBP p (.db 0 BZero) = false := by
  rcases p with ⟨v, b⟩
  simp only [lessBP, Bool.or_eq_false_iff, Bool.and_eq_false_imp,
    decide_eq_false_iff_not, not_lt, beq_iff_eq]
  refine ⟨by simp, ?_⟩
  intro _
  rcases b with ⟨cs⟩
  cases cs <;> simp [BZero, lessBT, lessBPList]

/-- \(s<_{\textrm{B}}s+_{\textrm{B}}D_00\)。 -/
private theorem lessBPList_snoc_self :
    ∀ as : List BP, lessBPList as (as ++ [BP.db 0 BZero]) = true
  | [] => by simp [lessBPList]
  | a :: as => by
      have ih := lessBPList_snoc_self as
      simp only [List.cons_append, lessBPList, Bool.or_eq_true, Bool.and_eq_true,
        beq_self_eq_true, true_and]
      exact Or.inr ih

theorem lessBT_addBT_D00_self (s : BT) :
    lessBT s (addBT s (Dprin 0 BZero)) = true := by
  rcases s with ⟨as⟩
  show lessBPList as (as ++ [BP.db 0 BZero]) = true
  exact lessBPList_snoc_self as

/-- \(s\) と \(s+_{\textrm{B}}D_00\) の間には何も無い。 -/
private theorem no_between_snoc_D00 :
    ∀ (as cs : List BP), lessBPList as cs = true →
      lessBPList cs (as ++ [BP.db 0 BZero]) = true → False
  | [], cs, h1, h2 => by
      cases cs with
      | nil => simp [lessBPList] at h1
      | cons c rest =>
          simp only [List.nil_append, lessBPList, Bool.or_eq_true, Bool.and_eq_true,
            beq_iff_eq] at h2
          rcases h2 with h | ⟨-, h⟩
          · rw [not_lessBP_D00 c] at h; exact Bool.noConfusion h
          · cases rest <;> simp [lessBPList] at h
  | a :: as, cs, h1, h2 => by
      cases cs with
      | nil => simp [lessBPList] at h1
      | cons c rest =>
          simp only [lessBPList, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h1
          simp only [List.cons_append, lessBPList, Bool.or_eq_true, Bool.and_eq_true,
            beq_iff_eq] at h2
          rcases h1 with hac | ⟨hac, has⟩
          · rcases h2 with hca | ⟨hca, -⟩
            · have := lessBT_linear_trans _ _ _
                ((lessBP_eq_lessBT a c) ▸ hac) ((lessBP_eq_lessBT c a) ▸ hca)
              rw [lessBT_linear_irrefl] at this
              exact Bool.noConfusion this
            · rw [hca, lessBP_irrefl] at hac; exact Bool.noConfusion hac
          · rcases h2 with hca | ⟨-, hrest⟩
            · rw [← hac, lessBP_irrefl] at hca; exact Bool.noConfusion hca
            · exact no_between_snoc_D00 as rest has hrest

/-- **[Buc1] の加法標準形のうち原文が使う分**: \(D_00\) を足すのは
\(OT_{\textrm{B}}\) の直後者を取ることなので \(o(s+_{\textrm{B}}D_00)=o(s)+1\)。 -/
theorem o_addBT_DzeroZero {s : BT} (hs : s ∈ OT_B)
    (hx : addBT s (Dprin 0 BZero) ∈ OT_B) :
    o (addBT s (Dprin 0 BZero)) = o s + 1 := by
  have hlt : lessBT s (addBT s (Dprin 0 BZero)) = true := lessBT_addBT_D00_self s
  have h1 : o s < o (addBT s (Dprin 0 BZero)) := o_lt_of_lessBT hs hx hlt
  refine le_antisymm ?_ ?_
  · by_contra hgt
    push_neg at hgt
    obtain ⟨u, huOTB, hulx, huo⟩ := o_surj_below hx hgt
    have hsu : o s < o u := by
      rw [huo]
      exact lt_of_lt_of_le (Order.lt_succ _) (le_of_eq (Order.succ_eq_add_one _))
    have hsub : lessBT s u = true := by
      rcases lessBT_linear_trichotomy s u with h | h | h
      · exact h
      · rw [h] at hsu; exact absurd hsu (lt_irrefl _)
      · exact absurd (o_lt_of_lessBT huOTB hs h) (asymm hsu)
    rcases s with ⟨as⟩
    rcases u with ⟨cs⟩
    exact no_between_snoc_D00 as cs hsub hulx
  · have := Order.succ_le_of_lt h1
    rwa [Order.succ_eq_add_one] at this

/-! ## \(o(t)\) は初期切片の上限 -/

/-- \(o(t)=\sup_{u<_{\textrm{B}}t}(o(u)+1)\)。`o_lt_of_lessBT` と `o_surj_below` だけで出る。 -/
theorem o_eq_iSup_below {t : BT} (ht : t ∈ OT_B) :
    o t = ⨆ u : {u : BT // u ∈ OT_B ∧ lessBT u t = true}, (o u.1 + 1) := by
  refine le_antisymm ?_ ?_
  · by_contra hgt
    push_neg at hgt
    obtain ⟨w, hwOTB, hwlt, hwo⟩ := o_surj_below ht hgt
    have hle := Ordinal.le_iSup
      (fun u : {u : BT // u ∈ OT_B ∧ lessBT u t = true} => o u.1 + 1) ⟨w, hwOTB, hwlt⟩
    rw [hwo] at hle
    exact absurd hle (by simp)
  · refine Ordinal.iSup_le_iff.mpr ?_
    rintro ⟨u, huOTB, hult⟩
    have := Order.succ_le_of_lt (o_lt_of_lessBT huOTB ht hult)
    rwa [Order.succ_eq_add_one] at this

/-! ## 残る 1 本の外部引用 — 基本列の共終性 -/

/-- [Buc2] Theorem 1.4(a) の**構文的な中身**: \(\textrm{dom}(t)=\omega\) のとき
基本列 \(t[0],t[1],\dots\) は \(\{u\in OT_{\textrm{B}}\mid u<_{\textrm{B}}t\}\) で共終。

順序数を含まない純粋に構文的な主張なので、`Audit-operB.lean` が小さな
\(OT_{\textrm{B}}\) プール上でこの形のまま全数検証している。 -/
def FseqCofinal : Prop :=
  ∀ t : BT, t ∈ OT_B → domTag t = BDom.naturals →
    ∀ u : BT, u ∈ OT_B → lessBT u t = true →
      ∃ m : ℕ, leBT u (operB t (numBT m)) = true

/-- [Buc2] Theorem 1.4(a) / Lemma 1.6。**本形式化に残る唯一の `axiom`**。 -/
axiom fseq_cofinal : FseqCofinal

/-! ## `dom` の記法 -/

/-- 原文の \(\textrm{dom}(t)=1\)（後続）。 -/
def domIsOne (t : BT) : Prop := domTag t = BDom.zeroOnly

/-- 原文の \(\textrm{dom}(t)=\omega\)。 -/
def domIsOmega (t : BT) : Prop := domTag t = BDom.naturals

end Bijectivity
