import «7».«7.2-scb-unique»

/-!
# §8.7 補題（順序数項の再帰構造）

- 原文: `tmp/content.md` 5953 付近
- 訂正: なし
- Isabelle: `p_8_7_OT_scb_recursive` (isabelle/pss_paper.thy:2263) の証明は
             `m_8_7_OT_scb_recursive` (isabelle/layerB/pss_wip.thy:17915)
- 依存: `7.2-scb-unique`（`scb_cut_reaches_last`/`scb_last_dichotomy`/
  `flatBT_multi_snoc`/`flatBP_length_ge_two`）、`PSS.Flat`（`flatBT_injective`）
- 状態: ✅ 証明済（sorry 0）

scb 分解の核 `c` は右スパイン上の principal 部分項。`isOT` は下方遺伝
（OT 項の各 principal 成分と principal の本体は OT）なので、右端成分への
pinning（`scb_last_dichotomy`）で降りる長さ帰納だけで閉じる。
-/

namespace PSS

private theorem flatBT_ne_nil_osr : ∀ c : BT, flatBT c ≠ []
  | .trm [] => by simp [flatBT]
  | .trm [p] => by
      cases p with
      | db u a => simp [flatBT, flatBP]
  | .trm (p :: q :: ps) => by simp [flatBT]

private theorem isOT_BP_of_mem_osr {ps : List BP} {p : BP}
    (h : isOT_BPList ps = true) (hp : p ∈ ps) : isOT_BP p = true := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
      simp only [isOT_BPList, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact h.1
      · exact ih h.2 hp

/-- 右端成分への pinning で降りる descent: 右括弧尾部つき principal occurrence は
`isOT` を受け継ぐ（Isabelle `OT_hereditary_aux` の Lean 版。帰納骨格は
`scb_occurrence_rightNodes_suffix` と同一）。 -/
private theorem OT_hereditary_osr {t : BT} {pp : BP} {s b : List Sym}
    (hocc : flatBT t = s ++ flatBP pp ++ b)
    (hb : ∀ x ∈ b, x = .rp)
    (hOT : isOT_BT t = true) :
    isOT_BP pp = true := by
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
              have hOTq : isOT_BP q = true := by
                have hOT' : isOT_BT (.trm [q]) = true := by
                  rw [hlistSingle]; exact hOT
                simp only [isOT_BT, isOT_BPList, Bool.and_eq_true] at hOT'
                exact hOT'.1.1
              have hd := scb_last_dichotomy
                (pre := []) (post := []) (q := q) (pp := pp)
                (h := by simpa [flatBT, List.append_assoc] using hoccSingle)
                hb (by simp) (by simp)
              rcases hd with hmax | ⟨u, a, s₂, b₂, hq, haocc, hb₂, _⟩
              · have hpq : pp = q := flatBP_injective hmax.2.1
                rw [hpq]
                exact hOTq
              · have hOTa : isOT_BT a = true := by
                  rw [hq] at hOTq
                  simp only [isOT_BP, Bool.and_eq_true] at hOTq
                  exact hOTq.1
                have hlt : (flatBT a).length < n := by
                  rw [← hnSingle, hq]
                  simp [flatBT, flatBP]
                exact ih (flatBT a).length hlt (t := a) (s := s₂)
                  (pp := pp) (b := b₂) haocc hb₂ hOTa rfl
          | cons p ps =>
              have hlistMulti : (p :: ps) ++ [q] = y :: ys := by
                simpa [hi] using hlist
              have hoccMulti : flatBT (.trm ((p :: ps) ++ [q])) =
                  s ++ flatBP pp ++ b := by
                simpa [hi] using hocc'
              have hnMulti : (flatBT (.trm ((p :: ps) ++ [q]))).length = n := by
                simpa [hi] using hn'
              have hqmem : q ∈ y :: ys := by
                rw [← hlistMulti]; simp
              have hOTq : isOT_BP q = true := by
                simp only [isOT_BT, Bool.and_eq_true] at hOT
                exact isOT_BP_of_mem_osr hOT.1 hqmem
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
              rcases hd with hmax | ⟨u, a, s₂, b₂, hq, haocc, hb₂, _⟩
              · have hpq : pp = q := flatBP_injective hmax.2.1
                rw [hpq]
                exact hOTq
              · have hOTa : isOT_BT a = true := by
                  rw [hq] at hOTq
                  simp only [isOT_BP, Bool.and_eq_true] at hOTq
                  exact hOTq.1
                have hlt : (flatBT a).length < n := by
                  rw [← hnMulti, flatBT_multi_snoc, hq]
                  simp [flatBP]
                  omega
                exact ih (flatBT a).length hlt (t := a) (s := s₂)
                  (pp := pp) (b := b₂) haocc hb₂ hOTa rfl

/-- 補題（順序数項の再帰構造）: scb 分解の核は順序数項。 -/
theorem OT_scb_recursive (t c : BT) (s b : List Sym)
    (ht : t ∈ OT_B) (_hc : c ∈ T_B) (hdec : scb_decomp t s (flatBT c) b) :
    c ∈ OT := by
  obtain ⟨hflat, hptb, hrp⟩ := hdec
  by_cases htz : t = BZero
  · -- `t = 0`: 長さ勘定で `c = 0`
    subst htz
    have hlen := congrArg List.length hflat
    have hcne : flatBT c ≠ [] := flatBT_ne_nil_osr c
    have hcge : 1 ≤ (flatBT c).length := by
      cases hcc : flatBT c with
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
    have hcz : flatBT c = flatBT BZero := by
      simpa [hs0, hb0, BZero] using hflat.symm
    have : c = BZero := flatBT_injective hcz
    subst this
    show isOT_BT BZero = true
    rfl
  · -- `t ≠ 0`: 核は principal 文字列 → 右スパイン descent
    obtain ⟨p, hpdf, hpfl⟩ := hptb htz
    have hcp : c = .trm [p] := by
      apply flatBT_injective
      rw [hpfl]
      rfl
    have hocc : flatBT t = s ++ flatBP p ++ b := by
      rw [hflat, hpfl]
    have htOT : isOT_BT t = true := ht.1
    have hp : isOT_BP p = true := OT_hereditary_osr hocc hrp htOT
    rw [hcp]
    show isOT_BT (.trm [p]) = true
    simp [isOT_BT, isOT_BPList, descP, hp]

/-! ## 回帰ベクトル: `t = D₂(D₁ 0)`, `(s,c,b) = ([D₂], D₁ 0, [])` -/

private def tOSR : BT := Dprin 2 (Dprin 1 BZero)
private def cOSR : BT := Dprin 1 BZero

example : cOSR ∈ OT :=
  OT_scb_recursive tOSR cOSR [.dsym 2] []
    ⟨show isOT_BT tOSR = true by decide, show dfree_BT tOSR = true by decide⟩
    (show dfree_BT cOSR = true by decide)
    ⟨by decide, fun _ => ⟨.db 1 BZero, by decide, by decide⟩, by simp⟩

#guard isOT_BT tOSR
#guard isOT_BT cOSR

#print axioms OT_scb_recursive

end PSS
