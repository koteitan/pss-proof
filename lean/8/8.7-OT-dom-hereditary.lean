import «7».«7.2-scb-unique»
import «Buchholz-1986».«Buchholz-1986-3.2-descent»

/-!
# §8.7 補題（順序数項の共終数の遺伝性）

- 原文: `tmp/content.md` 5962 付近
- 訂正: なし
- Isabelle: `p_8_7_OT_dom_hereditary` (isabelle/pss_paper.thy:2273) の証明は
             `m_8_7_OT_dom_hereditary` (isabelle/layerB/pss_wip.thy:17802)
- 依存: `7.2-scb-unique`（右端 pinning）、`Buchholz-1986-3.2-descent`（`domTag_snoc_bf`）、
  `PSS.Flat`（`flatBT_injective`）
- 状態: ✅ 証明済（sorry 0）

`dom` は右スパインで決まる（multi 項の `dom` は末尾 principal の `dom`、
principal `D_v b`（`b ≠ 0`）の `dom` は `dom(b) = ℕ` なら `ℕ`）。したがって
右端成分への pinning（`scb_last_dichotomy`）の descent で `dom(t') = ℕ` が
外側へ遺伝する。`8.7-OT-scb-recursive` と同一の帰納骨格。
-/

namespace PSS

private theorem flatBT_ne_nil_odh : ∀ c : BT, flatBT c ≠ []
  | .trm [] => by simp [flatBT]
  | .trm [p] => by
      cases p with
      | db u a => simp [flatBT, flatBP]
  | .trm (p :: q :: ps) => by simp [flatBT]

private theorem nestedD0_not_nat_odh :
    Dprin 0 (Dprin 0 BZero) ∉ NatSet := by
  rintro ⟨n, hn⟩
  have hn1 : n = 1 := by
    have hlen := congrArg numNat hn
    simp [Dprin, BZero, numBT, numNat] at hlen
    omega
  subst n
  simp [Dprin, BZero, numBT] at hn

/-- 四種類の `BDom` タグのうち、集合として `NatSet` になるのは `naturals` だけ
（`7.2-scb-unique` の private 補題の複製）。 -/
private theorem BDom_toSet_eq_NatSet_iff_odh (d : BDom) :
    d.toSet = NatSet ↔ d = .naturals := by
  cases d with
  | empty =>
      constructor
      · intro h
        have hz : BZero ∈ NatSet := ⟨0, by simp [numBT, BZero]⟩
        rw [← h] at hz
        simp [BDom.toSet] at hz
      · simp
  | zeroOnly =>
      constructor
      · intro h
        have h₁ : numBT 1 ∈ NatSet := ⟨1, rfl⟩
        rw [← h] at h₁
        simp [BDom.toSet, numBT, BZero] at h₁
      · simp
  | naturals => simp [BDom.toSet]
  | below u =>
      constructor
      · intro h
        have hx : Dprin 0 (Dprin 0 BZero) ∈ (BDom.below u).toSet := by
          simp [BDom.toSet, TBv, Dprin]
        rw [h] at hx
        exact (nestedD0_not_nat_odh hx).elim
      · simp

/-- descent: 右括弧尾部つき principal occurrence の `domTag` が `naturals` なら、
外側の項の `domTag` も `naturals`（Isabelle `domB_hereditary_aux` の Lean 版）。 -/
private theorem dom_hereditary_odh {t : BT} {pp : BP} {s b : List Sym}
    (hocc : flatBT t = s ++ flatBP pp ++ b)
    (hb : ∀ x ∈ b, x = .rp)
    (hpp : domTagBP pp = .naturals) :
    domTag t = .naturals := by
  generalize hn : (flatBT t).length = n
  induction n using Nat.strong_induction_on generalizing t s pp b with
  | h n ih =>
      rcases t with ⟨ys⟩
      cases ys with
      | nil =>
          have hlen := congrArg List.length hocc
          have hge := flatBP_length_ge_two pp
          simp [flatBT] at hlen
          omega
      | cons y ys =>
          let full : List BP := y :: ys
          have hfull : full ≠ [] := by simp [full]
          let init := full.dropLast
          let q := full.getLast hfull
          have hsnoc : init ++ [q] = full :=
            List.dropLast_append_getLast hfull
          have hlist : init ++ [q] = y :: ys := by
            simpa [full] using hsnoc
          have hocc' : flatBT (.trm (init ++ [q])) = s ++ flatBP pp ++ b := by
            rw [hsnoc]
            simpa [full] using hocc
          have hn' : (flatBT (.trm (init ++ [q]))).length = n := by
            rw [hsnoc]
            simpa [full] using hn
          cases hi : init with
          | nil =>
              have hlistSingle : [q] = y :: ys := by
                simpa [hi] using hlist
              have hoccSingle : flatBT (.trm [q]) = s ++ flatBP pp ++ b := by
                simpa [hi] using hocc'
              have hnSingle : (flatBT (.trm [q])).length = n := by
                simpa [hi] using hn'
              have hd := scb_last_dichotomy
                (pre := []) (post := []) (q := q) (pp := pp)
                (h := by simpa [flatBT, List.append_assoc] using hoccSingle)
                hb (by simp) (by simp)
              rw [← hlistSingle]
              rcases hd with hmax | ⟨u, a, s₂, b₂, hq, haocc, hb₂, _⟩
              · have hpq : pp = q := flatBP_injective hmax.2.1
                rw [← hpq]
                simpa [domTag, domTagList] using hpp
              · have hane : a ≠ BZero := by
                  intro hz
                  subst hz
                  have hlen := congrArg List.length haocc
                  have hge := flatBP_length_ge_two pp
                  simp [BZero, flatBT] at hlen
                  omega
                have hbeq : (a == BZero) = false := by
                  simpa using hane
                have hlt : (flatBT a).length < n := by
                  rw [← hnSingle, hq]
                  simp [flatBT, flatBP]
                have hta : domTag a = .naturals :=
                  ih (flatBT a).length hlt (t := a) (s := s₂)
                    (pp := pp) (b := b₂) haocc hb₂ hpp rfl
                rw [hq]
                simp [domTag, domTagList, domTagBP, hbeq, hta]
          | cons p ps =>
              have hlistMulti : (p :: ps) ++ [q] = y :: ys := by
                simpa [hi] using hlist
              have hoccMulti : flatBT (.trm ((p :: ps) ++ [q])) =
                  s ++ flatBP pp ++ b := by
                simpa [hi] using hocc'
              have hnMulti : (flatBT (.trm ((p :: ps) ++ [q]))).length = n := by
                simpa [hi] using hn'
              have hshape := flatBT_multi_snoc p ps q
              have hsplit :
                  (.lp :: flatComponentRun (p :: ps)) ++ flatBP q ++ [.rp] =
                    s ++ flatBP pp ++ b := by
                simpa [List.append_assoc] using hshape.symm.trans hoccMulti
              have hcut := scb_cut_reaches_last p ps q pp s b hoccMulti hb
              have hcut' : (.lp :: flatComponentRun (p :: ps)).length ≤ s.length := by
                simp
                omega
              have hd := scb_last_dichotomy
                (pre := .lp :: flatComponentRun (p :: ps))
                (post := [.rp]) (q := q) (pp := pp)
                hsplit hb (by simp) hcut'
              rw [← hlistMulti]
              rcases hd with hmax | ⟨u, a, s₂, b₂, hq, haocc, hb₂, _⟩
              · have hpq : pp = q := flatBP_injective hmax.2.1
                rw [domTag_snoc_bf, ← hpq]
                exact hpp
              · have hane : a ≠ BZero := by
                  intro hz
                  subst hz
                  have hlen := congrArg List.length haocc
                  have hge := flatBP_length_ge_two pp
                  simp [BZero, flatBT] at hlen
                  omega
                have hbeq : (a == BZero) = false := by
                  simpa using hane
                have hlt : (flatBT a).length < n := by
                  rw [← hnMulti, flatBT_multi_snoc, hq]
                  simp [flatBP]
                  omega
                have hta : domTag a = .naturals :=
                  ih (flatBT a).length hlt (t := a) (s := s₂)
                    (pp := pp) (b := b₂) haocc hb₂ hpp rfl
                rw [domTag_snoc_bf, hq]
                simp [domTagBP, hbeq, hta]

/-- 補題（順序数項の共終数の遺伝性）: `dom(t') = ℕ` は scb 分解を通じて外側へ遺伝する。 -/
theorem OT_dom_hereditary (t t' : BT) (s b : List Sym)
    (_ht : t ∈ T_B) (_ht' : t' ∈ T_B)
    (hdom : domB t' = NatSet)
    (hdec : scb_decomp t s (flatBT t') b) :
    domB t = NatSet := by
  obtain ⟨hflat, hptb, hrp⟩ := hdec
  have htag' : domTag t' = .naturals :=
    (BDom_toSet_eq_NatSet_iff_odh (domTag t')).mp hdom
  by_cases htz : t = BZero
  · -- `t = 0` は不可能: 長さ勘定で `t' = 0` になり `dom(0) = ∅ ≠ ℕ`
    exfalso
    subst htz
    have hlen := congrArg List.length hflat
    have hcne : flatBT t' ≠ [] := flatBT_ne_nil_odh t'
    have hcge : 1 ≤ (flatBT t').length := by
      cases hcc : flatBT t' with
      | nil => exact absurd hcc hcne
      | cons x xs => simp
    have hs0 : s = [] := by
      simp [BZero, flatBT] at hlen
      cases s with
      | nil => rfl
      | cons x xs => simp at hlen; omega
    have hb0 : b = [] := by
      simp [BZero, flatBT] at hlen
      cases b with
      | nil => rfl
      | cons x xs => simp at hlen; omega
    have hcz : flatBT t' = flatBT BZero := by
      simpa [hs0, hb0, BZero] using hflat.symm
    have ht'z : t' = BZero := flatBT_injective hcz
    subst ht'z
    rw [show domTag BZero = BDom.empty from rfl] at htag'
    exact absurd htag' (by decide)
  · obtain ⟨p, _hpdf, hpfl⟩ := hptb htz
    have hcp : t' = .trm [p] := by
      apply flatBT_injective
      rw [hpfl]
      rfl
    have hppTag : domTagBP p = .naturals := by
      rw [hcp] at htag'
      simpa [domTag, domTagList] using htag'
    have hocc : flatBT t = s ++ flatBP p ++ b := by
      rw [hflat, hpfl]
    have htag : domTag t = .naturals := dom_hereditary_odh hocc hrp hppTag
    rw [domB, htag]
    rfl

/-! ## 回帰ベクトル: `t = D₂(D₀(D₀ 0))`, `t' = D₀(D₀ 0)`（`dom = ℕ`） -/

private def tODH : BT := Dprin 2 (Dprin 0 (Dprin 0 BZero))
private def cODH : BT := Dprin 0 (Dprin 0 BZero)

#guard domTag cODH == .naturals
#guard domTag tODH == .naturals
#guard flatBT tODH == [.dsym 2] ++ flatBT cODH ++ []

example : domB tODH = NatSet :=
  OT_dom_hereditary tODH cODH [.dsym 2] []
    (show dfree_BT tODH = true by decide)
    (show dfree_BT cODH = true by decide)
    (by rw [domB, show domTag cODH = BDom.naturals from by decide]; rfl)
    ⟨by decide, fun _ => ⟨.db 0 (Dprin 0 BZero), by decide, by decide⟩, by simp⟩

#print axioms OT_dom_hereditary

end PSS
