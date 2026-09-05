import Bijectivity.«17-fseq-convergence»
import Bijectivity.«18-trans-preserves-order»
import Bijectivity.«20-term-upper-bound»
import Bijectivity.«15-successor-fseq»

/-!
# 命題（変換写像の順序数への全単射性）

原文: \(o\circ\textrm{Trans}\) は \(CT_{\textrm{PS}}\to\psi_0\psi_\omega0\) 上で
全域かつ全単射である。

原文の証明:
> 対応する項の上界未満の字母、対応する項の上界 (1)(2) 及び [1] の \(\textrm{Trans}\) が
> 標準形を保つことより \(\{\textrm{Trans}(M)\}\) は
> \(\{t\mid t\in OT_{\textrm{B}\omega}\land t<_{\textrm{B}}D_0D_\omega0\}\) の
> \(<_{\textrm{B}}\) に対して非有界な部分集合である。
> [4] Lemma 2.2(c) より \(\{o(\textrm{Trans}(M))\}\) は \(\psi_0\psi_\omega0\) の
> 非有界な部分集合である。
> [4] Lemma 2.3(b) 及び [5] Lemma 1.6 より \(\textrm{dom}(t)=\textrm{cof}(o(t))\)。
> 後続な項の基本列 より \(\textrm{cof}=1\) の場合、基本列の収束性 より
> \(\textrm{cof}=\omega\) の場合が押さえられ、[3] の命題 11 より全射。
> \(\textrm{Trans}\) が順序を保つこと、[4] Lemma 2.1 及び 2.2(c) より単射。□

## 状態

**全域性（`MapsTo`）と単射性（`InjOn`）は証明済み**。どちらも新たな外部引用を
必要とせず、既に証明した 命題（対応する項の上界）(1) と
命題（\(\textrm{Trans}\) が順序を保つこと）、および `Cited.lean` に既にある
[4] Lemma 2.2(c)（`o_lt_of_lessBT`）だけで閉じる。

**全射性（`SurjOn`）も証明済み**。原文の証明どおり 命題（後続な項の基本列）と
命題（基本列の収束性）を使う。ただし原文が引く [3] の命題 11 は公理化せず、
非有界性と上の 2 命題から超限帰納で直接示している（`oTrans_surjOn`）。
-/

namespace Bijectivity

open PSS

/-! ## 順序数項であること（`o` の外部引用は `OT` の上でしか使えない） -/

/-- 上界の項は順序数項。 -/
theorem OT_DzeroDomegaZero : DzeroDomegaZero ∈ OT := by
  show isOT_BT DzeroDomegaZero = true
  decide

/-- \(D_00\) は \(D_\omega\) を含まない順序数項。 -/
theorem OTB_DzeroZero : DzeroZero ∈ OT_B := by
  constructor
  · show isOT_BT DzeroZero = true
    decide
  · show dfree_BT DzeroZero = true
    decide

theorem OT_DzeroZero : DzeroZero ∈ OT := OTB_DzeroZero.1

theorem o_DzeroZero' : o DzeroZero = 1 := by rw [DzeroZero]; exact o_DzeroZero

/-- \(\textrm{Trans}\) の値は順序数項（`8.7-termination` の OT 柱）。 -/
theorem OTB_Trans_of_CTPS {M : PS} (hM : CTPS M) : PSS.Trans M ∈ OT_B :=
  Trans_STPS_OT_B M hM.1

theorem OT_Trans_of_CTPS {M : PS} (hM : CTPS M) : PSS.Trans M ∈ OT :=
  (OTB_Trans_of_CTPS hM).1

/-! ## 全域性 -/

/-- 原文の全域性: \(o(\textrm{Trans}(M))<\psi_0\psi_\omega0\)。 -/
theorem oTrans_mapsTo :
    Set.MapsTo (fun M => o (PSS.Trans M)) {M : PS | CTPS M}
      {α : Ordinal | α < psi0psiOmega0} := by
  intro M hM
  show o (PSS.Trans M) < psi0psiOmega0
  exact o_lt_psi (OTB_Trans_of_CTPS hM) (trans_lt_bound hM)

/-! ## 単射性 -/

/-- 原文の単射性: \(\textrm{Trans}\) が順序を保つこと と \(<_{\textrm{PS}}\) の
三分律（[4] Lemma 2.1 にあたる \(<_{\textrm{B}}\) の線形性）から従う。 -/
theorem trans_injOn : Set.InjOn PSS.Trans {M : PS | CTPS M} := by
  intro M hM N hN h
  rcases ltPS_trichotomy M N with h1 | h1 | h1
  · have hb := trans_lessBT_of_ltPS hM hN h1
    rw [h, lessBT_linear_irrefl] at hb
    exact absurd hb (by simp)
  · exact h1
  · have hb := trans_lessBT_of_ltPS hN hM h1
    rw [h, lessBT_linear_irrefl] at hb
    exact absurd hb (by simp)

/-- \(o\circ\textrm{Trans}\) の単射性（[4] Lemma 2.2(c) を追加で使う）。 -/
theorem oTrans_injOn : Set.InjOn (fun M => o (PSS.Trans M)) {M : PS | CTPS M} := by
  intro M hM N hN h
  simp only at h
  rcases ltPS_trichotomy M N with h1 | h1 | h1
  · exact absurd (o_lt_of_lessBT (OTB_Trans_of_CTPS hM) (OTB_Trans_of_CTPS hN)
      (trans_lessBT_of_ltPS hM hN h1))
      (by rw [h]; exact lt_irrefl _)
  · exact h1
  · exact absurd (o_lt_of_lessBT (OTB_Trans_of_CTPS hN) (OTB_Trans_of_CTPS hM)
      (trans_lessBT_of_ltPS hN hM h1))
      (by rw [← h]; exact lt_irrefl _)

/-! ## 全射性 -/

/-- \(CT_{\textrm{PS}}\) は基本列で閉じている。 -/
theorem ctps_oper {M : PS} (hM : CTPS M) {n : ℕ} (hn : 1 ≤ n) : CTPS (oper M n) := by
  obtain ⟨v, hv⟩ := (ctps_iff_leExpPS M).mp hM
  exact (ctps_iff_leExpPS _).mpr ⟨v, leExpPS_trans (oper_leExpPS M hn) hv⟩

/-- 原文「\(\{o(\textrm{Trans}(M))\}\) は \(\psi_0\psi_\omega0\) の非有界な部分集合」。
対応する項の上界未満の字母 と 対応する項の上界 (2) と [4] Lemma 2.2(c) から従う。 -/
theorem oTrans_unbounded {α : Ordinal} (hα : α < psi0psiOmega0) :
    ∃ M : PS, CTPS M ∧ α < o (PSS.Trans M) := by
  obtain ⟨t, htOTB, htlt, hto⟩ := o_surj_below_psi hα
  obtain ⟨M, hM, hMlt⟩ := exists_trans_gt htOTB.2 htlt
  exact ⟨M, hM, by rw [← hto]; exact o_lt_of_lessBT htOTB (OTB_Trans_of_CTPS hM) hMlt⟩

/-- 原文の全射性。原文は [3] の命題 11 を引くが、ここでは
非有界性・後続な項の基本列・基本列の収束性から超限帰納で直接示す。 -/
theorem oTrans_surjOn :
    Set.SurjOn (fun M => o (PSS.Trans M)) {M : PS | CTPS M}
      {α : Ordinal | α < psi0psiOmega0} := by
  intro α hα
  simp only [Set.mem_setOf_eq] at hα
  have hTne : {β : Ordinal | α ≤ β ∧ ∃ M : PS, CTPS M ∧ o (PSS.Trans M) = β}.Nonempty := by
    obtain ⟨M, hM, hlt⟩ := oTrans_unbounded hα
    exact ⟨o (PSS.Trans M), le_of_lt hlt, ⟨M, hM, rfl⟩⟩
  obtain ⟨β, hβmem, hβmin⟩ :=
    (wellFounded_lt (α := Ordinal)).has_min
      {β : Ordinal | α ≤ β ∧ ∃ M : PS, CTPS M ∧ o (PSS.Trans M) = β} hTne
  obtain ⟨hαβ, M, hM, hMβ⟩ := hβmem
  rcases eq_or_lt_of_le hαβ with heq | hlt
  · exact ⟨M, hM, hMβ.trans heq.symm⟩
  exfalso
  have hTz : PSS.Trans M ≠ BZero := by
    intro hz
    rw [hz, o_BZero] at hMβ
    rw [← hMβ] at hlt
    exact absurd hlt (by simp)
  have hOTM : PSS.Trans M ∈ OT := (Trans_STPS_OT_B M hM.1).1
  have hbnd : lessBT (PSS.Trans M) DzeroDomegaZero = true := trans_lt_bound hM
  rcases domTag_cases_of_bound hOTM hbnd hTz with hd | hd
  · -- 後続の場合: 命題（後続な項の基本列）
    have hM1 : CTPS (oper M 1) := ctps_oper hM (le_refl 1)
    have hstep := successor_fseq (M := M) (STPS_RTPS M hM.1) (n := 1) (le_refl 1) hd
    refine hβmin (o (PSS.Trans (oper M 1))) ⟨?_, ⟨oper M 1, hM1, rfl⟩⟩ ?_
    · rcases hstep with ⟨h1, h2⟩ | h2
      · rw [h2, o_BZero]
        rw [← hMβ, h1, o_DzeroZero'] at hlt
        exact le_of_eq (Ordinal.lt_one_iff_zero.mp hlt)
      · by_contra hc
        push_neg at hc
        have hβeq : β = o (PSS.Trans (oper M 1)) + 1 := by
          rw [← hMβ, ← h2, DzeroZero, o_addBT_DzeroZero (OTB_Trans_of_CTPS hM1)
            (h2 ▸ OTB_Trans_of_CTPS hM)]
        have : β ≤ α := by
          rw [hβeq, Ordinal.add_one_eq_succ]
          exact Order.succ_le_of_lt hc
        exact absurd hlt (not_lt.mpr this)
    · rcases hstep with ⟨h1, h2⟩ | h2
      · rw [h2, o_BZero, ← hMβ, h1, o_DzeroZero']
        exact zero_lt_one
      · have hβeq : β = o (PSS.Trans (oper M 1)) + 1 := by
          rw [← hMβ, ← h2, DzeroZero, o_addBT_DzeroZero (OTB_Trans_of_CTPS hM1)
            (h2 ▸ OTB_Trans_of_CTPS hM)]
        rw [hβeq, Ordinal.add_one_eq_succ]
        exact Order.lt_succ _
  · -- 極限の場合: 命題（基本列の収束性）
    have hlen : 1 < Lng M := one_lt_lng_of_domIsOmega (STPS_RTPS M hM.1) hd
    have hconv := fseq_convergence hM.1 hd
    have hex : ∃ n : {n : ℕ // 1 ≤ n}, α < o (PSS.Trans (oper M n.1)) := by
      by_contra hc
      push_neg at hc
      have hle : (⨆ n : {n : ℕ // 1 ≤ n}, o (PSS.Trans (oper M n.1))) ≤ α :=
        Ordinal.iSup_le_iff.mpr hc
      rw [hconv, hMβ] at hle
      exact absurd hlt (not_lt.mpr hle)
    obtain ⟨⟨n, hn⟩, hnlt⟩ := hex
    refine hβmin (o (PSS.Trans (oper M n))) ⟨le_of_lt hnlt, ⟨oper M n, ctps_oper hM hn, rfl⟩⟩ ?_
    rw [← hMβ]
    exact o_lt_of_lessBT (OTB_Trans_of_CTPS (ctps_oper hM hn)) (OTB_Trans_of_CTPS hM)
      (Trans_fseq_descend M n hM.1 hn hlen)

/-- 原文の命題（変換写像の順序数への全単射性）。 -/
theorem oTrans_bijOn :
    Set.BijOn (fun M => o (PSS.Trans M)) {M : PS | CTPS M}
      {α : Ordinal | α < psi0psiOmega0} :=
  ⟨oTrans_mapsTo, oTrans_injOn, oTrans_surjOn⟩

end Bijectivity
