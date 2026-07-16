import PSS.Red
import «5».«5.1-ancestor-basic»
import «6».«6.2-P-fseq»
import «6».«6.8-standard-slice-Br-descending»

/-!
# §6.8 d1pos regime-A アンカー一致層（anchor-regA brick 族）

- 原文: `tmp/content.md` L1516–1620 付近（§6.8 命題の証明本体の `i₁ = 1`（d1pos）
  ¬brle 跨りスライス、regime A（`j'₀ < j₋₂`）のアンカー幾何と周期床）
- 訂正: なし（タイル読み出しは A7/A8 適用済みの `*_68` 資産に依拠）
- Isabelle (isabelle/pss_mechanized.thy):
  `oper_d1pos_seg_low_verbatim` (15460), `oper_d1pos_branch_lowshift_regA` (15654),
  `oper_d1pos_anchor_coincide_regA` (15714), `oper_d1pos_cNlt_of_Ajm2` (15902),
  `oper_d1pos_period_row0_floor` (15971), `oper_d1pos_strict_period_floor` (16017),
  `oper_d1pos_clt_regA` (16068)
- 依存: «6».«6.8-standard-slice-Br-descending»（`entry_oper_d1pos_*_68` 読み出し・
  `P_last_anchor_68` / `P_dropLast_seg_zero_after_anchor_68` /
  `last_anchor_eq_sum_dropLast_68` / `seg_of_seg_68` / `seg_getElem_68`）,
  «5».«5.1-ancestor-basic»（`ancestor_basic_1`）,
  «6».«6.2-P-fseq»（`hasParent_next_fseq` / `nextR_implies_row0`）,
  PSS.Red（`IncrFirstN`）
- 状態: ✅ 証明済（sorry 0）

Isabelle の `oper_d1pos_nth_low_verbatim`（並行 agent 範囲 14393–15459）は
entry 読み出し（`entry_oper_d1pos_{prefix,zero,one}_68`）による private 版
`entry0/1_oper_d1pos_low_verbatim_ra` として再証明。Isabelle の
`anchor_lt_of_uniform_witness`（同 15864 付近）・`P_butlast_take_at_anchor` 相当は
それぞれ private `anchor_lt_of_uniform_witness_ra`・既存
`P_dropLast_seg_zero_after_anchor_68` を使用。Isabelle 版の周期床は
`monoT`＋`entry0_ge_min` 経由だが、Lean では `ancestor_basic_1`（値特徴付け）で
直接得られる（le0 持ち上げの勝ち筋、memo.md §4.5）。
-/

namespace PSS

/-! ## 補助: 行 1 の親ステップから行 0 到達性（`poper_nextR_imp_le0` 相当） -/

/-- The row-1 parent step at the last column yields row-0 reachability
`j₋₂ ≤₀ Lng N - 1`. -/
private theorem leR_base_ra (N : PS)
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1) :
    leR N 0 (parent N 1 (Lng N - 1)) (Lng N - 1) = true := by
  have hnext := hasParent_next_fseq N (idx1 N (Lng N - 1)) (Lng N - 1) hp
  rw [hi] at hnext
  exact (nextR_implies_row0 N 1 (parent N 1 (Lng N - 1)) (Lng N - 1) hnext).2

/-! ## LOW verbatim（Isabelle `oper_d1pos_nth_low_verbatim` の entry 版、private） -/

/-- Row-0 verbatim readout strictly below the last boundary: prefix region by
`entry_oper_d1pos_prefix_68`, block 0 (`q = 0`, shift `0·δ = 0`) by
`entry_oper_d1pos_zero_68`. -/
private theorem entry0_oper_d1pos_low_verbatim_ra
    (N : PS) (n x : ℕ) (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (hj₀lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hn1 : 1 ≤ n) (hx : x < Lng N - 1) :
    entry (oper N n) 0 x = entry N 0 x := by
  by_cases hpre : x < parent N 1 (Lng N - 1)
  · exact entry_oper_d1pos_prefix_68 N n 0 x hlen hzero hp hi hpre
  · have hs : x - parent N 1 (Lng N - 1) <
        Lng N - 1 - parent N 1 (Lng N - 1) := by omega
    have hread := entry_oper_d1pos_zero_68 N n 0 (x - parent N 1 (Lng N - 1))
      hlen hzero hp hi (by omega) hs
    simp only [Nat.zero_mul, Nat.add_zero] at hread
    rw [show parent N 1 (Lng N - 1) + (x - parent N 1 (Lng N - 1)) = x from
      by omega] at hread
    exact hread

/-- Row-1 verbatim readout strictly below the last boundary. -/
private theorem entry1_oper_d1pos_low_verbatim_ra
    (N : PS) (n x : ℕ) (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (hj₀lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hn1 : 1 ≤ n) (hx : x < Lng N - 1) :
    entry (oper N n) 1 x = entry N 1 x := by
  by_cases hpre : x < parent N 1 (Lng N - 1)
  · exact entry_oper_d1pos_prefix_68 N n 1 x hlen hzero hp hi hpre
  · have hs : x - parent N 1 (Lng N - 1) <
        Lng N - 1 - parent N 1 (Lng N - 1) := by omega
    have hread := entry_oper_d1pos_one_68 N n 0 (x - parent N 1 (Lng N - 1))
      hlen hzero hp hi (by omega) hs
    simp only [Nat.zero_mul, Nat.add_zero] at hread
    rw [show parent N 1 (Lng N - 1) + (x - parent N 1 (Lng N - 1)) = x from
      by omega] at hread
    exact hread

/-! ## §6.8 d1pos LOW verbatim seg（conc-A, regime A） -/

/-- §6.8 d1pos LOW verbatim seg (conc-A, regime A).  When the right endpoint
`b` of a slice stays STRICTLY below the last boundary `Lng N - 1`, the
periodic `N[n]`-extension reads off `N` verbatim on the whole window `[a,b]`:
`seg (N[n]) a b = seg N a b`.  (Isabelle: `oper_d1pos_seg_low_verbatim`.) -/
theorem oper_d1pos_seg_low_verbatim
    (N : PS) (n a b : ℕ) (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (hj₀lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hn1 : 1 ≤ n)
    (hb : b < Lng N - 1) :
    seg (oper N n) a b = seg N a b := by
  apply List.ext_getElem
  · simp
  · intro r hrL hrR
    have hx : a + r < Lng N - 1 := by
      simp only [length_seg] at hrL
      omega
    rw [seg_getElem_68 (oper N n) a b r hrL, seg_getElem_68 N a b r hrR,
      entry0_oper_d1pos_low_verbatim_ra N n (a + r) hlen hzero hp hi hj₀lt hn1 hx,
      entry1_oper_d1pos_low_verbatim_ra N n (a + r) hlen hzero hp hi hj₀lt hn1 hx]

/-! ## §6.8 d1pos ¬brle REGIME A lowshift（conc-A, `shamt = 0`） -/

/-- §6.8 d1pos ¬brle regime-A lowshift (`shamt = 0`): with coinciding starts
(`A = AN`) and anchors (`cc = cN`), and the anchor prefix strictly below the
boundary, both LOW prefixes reduce to `seg N A (A + (cc-1))` and the
`IncrFirstN 0` shift is the identity.
(Isabelle: `oper_d1pos_branch_lowshift_regA`.) -/
theorem oper_d1pos_branch_lowshift_regA
    (N : PS) (n A AN cc cN E EN : ℕ) (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (hj₀lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hn1 : 1 ≤ n)
    (hAeq : A = AN) (hccN : cc = cN)
    (hAbnd : A + (cc - 1) < Lng N - 1)
    (hEle : A ≤ E) (hccle : cc - 1 ≤ E - A)
    (hANle : AN ≤ EN) (hcNle : cN - 1 ≤ EN - AN) :
    seg (seg (oper N n) A E) 0 (cc - 1) =
      IncrFirstN 0 (seg (seg N AN EN) 0 (cN - 1)) := by
  subst hAeq
  subst hccN
  rw [seg_of_seg_68 (oper N n) A E 0 (cc - 1) hEle hccle,
    seg_of_seg_68 N A EN 0 (cc - 1) hANle hcNle,
    show IncrFirstN 0 (seg N (A + 0) (A + (cc - 1))) =
      seg N (A + 0) (A + (cc - 1)) from rfl]
  exact oper_d1pos_seg_low_verbatim N n (A + 0) (A + (cc - 1))
    hlen hzero hp hi hj₀lt hn1 (by omega)

/-! ## アンカー < k の橋（Isabelle `anchor_lt_of_uniform_witness`、private） -/

/-- The anchor-below-`k` bridge: if one index `jj < k` strictly undercuts the
row-0 value of EVERY tail index `x ∈ [k, Lng S - 1]`, then the last
`FirstNodes` anchor sits strictly below `k` (the anchor is a row-0 left
minimum, contradiction at `x = c`). -/
private theorem anchor_lt_of_uniform_witness_ra
    (S : PS) (jj k : ℕ) (hS : TPS S) (hmulti : 1 < (P S).length)
    (hjjk : jj < k)
    (hwit : ∀ x, k ≤ x → x ≤ Lng S - 1 → entry S 0 jj < entry S 0 x) :
    (IdxSum (P S)).getD ((P S).length - 1) 0 < k := by
  by_contra hcon
  obtain ⟨_, hcle, hlmin, _, _⟩ := P_last_anchor_68 S hS hmulti
  have ha := hlmin jj (by omega)
  have hb := hwit ((IdxSum (P S)).getD ((P S).length - 1) 0) (by omega) hcle
  omega

/-! ## §6.8 geomA アンカー一致（regime A の `c = cN` / `F8end` / `F9end`） -/

/-- Core of the anchor coincidence: two sequences that agree verbatim on the
common prefix `[0, m-1]`, with both anchors strictly below `m`, have equal
`dropLast` P-decompositions, hence coinciding anchors and coinciding
row-0/row-1 entries at the anchor. -/
private theorem anchor_coincide_core_ra
    (S Sn : PS) (m : ℕ) (hS : TPS S) (hSn : TPS Sn)
    (hmulti : 1 < (P S).length) (hmultiN : 1 < (P Sn).length)
    (hmS : m ≤ Lng S) (hmSn : m ≤ Lng Sn)
    (hclt : (IdxSum (P S)).getD ((P S).length - 1) 0 < m)
    (hcNlt : (IdxSum (P Sn)).getD ((P Sn).length - 1) 0 < m)
    (hQeq : seg S 0 (m - 1) = seg Sn 0 (m - 1)) :
    (IdxSum (P S)).getD ((P S).length - 1) 0 =
        (IdxSum (P Sn)).getD ((P Sn).length - 1) 0 ∧
      entry S 0 ((IdxSum (P S)).getD ((P S).length - 1) 0) =
        entry Sn 0 ((IdxSum (P Sn)).getD ((P Sn).length - 1) 0) ∧
      entry S 1 ((IdxSum (P S)).getD ((P S).length - 1) 0) ≤
        entry Sn 1 ((IdxSum (P Sn)).getD ((P Sn).length - 1) 0) := by
  have hbutS := P_dropLast_seg_zero_after_anchor_68 S m hS hmulti hclt hmS
  have hbutSn := P_dropLast_seg_zero_after_anchor_68 Sn m hSn hmultiN hcNlt hmSn
  have hbutEq : (P S).dropLast = (P Sn).dropLast := by
    rw [← hbutS, hQeq, hbutSn]
  have hceq : (IdxSum (P S)).getD ((P S).length - 1) 0 =
      (IdxSum (P Sn)).getD ((P Sn).length - 1) 0 := by
    rw [last_anchor_eq_sum_dropLast_68 S, last_anchor_eq_sum_dropLast_68 Sn,
      hbutEq]
  have hcm : (IdxSum (P S)).getD ((P S).length - 1) 0 <
      Lng (seg S 0 (m - 1)) := by
    rw [length_seg]; omega
  have hcmN : (IdxSum (P S)).getD ((P S).length - 1) 0 <
      Lng (seg Sn 0 (m - 1)) := by
    rw [length_seg]; omega
  have h0 : entry S 0 ((IdxSum (P S)).getD ((P S).length - 1) 0) =
      entry Sn 0 ((IdxSum (P S)).getD ((P S).length - 1) 0) := by
    have hh : entry (seg S 0 (m - 1)) 0
          ((IdxSum (P S)).getD ((P S).length - 1) 0) =
        entry (seg Sn 0 (m - 1)) 0
          ((IdxSum (P S)).getD ((P S).length - 1) 0) := by
      rw [hQeq]
    rw [entry_seg S 0 (m - 1) 0 _ hcm, entry_seg Sn 0 (m - 1) 0 _ hcmN] at hh
    simpa using hh
  have h1 : entry S 1 ((IdxSum (P S)).getD ((P S).length - 1) 0) =
      entry Sn 1 ((IdxSum (P S)).getD ((P S).length - 1) 0) := by
    have hh : entry (seg S 0 (m - 1)) 1
          ((IdxSum (P S)).getD ((P S).length - 1) 0) =
        entry (seg Sn 0 (m - 1)) 1
          ((IdxSum (P S)).getD ((P S).length - 1) 0) := by
      rw [hQeq]
    rw [entry_seg S 0 (m - 1) 1 _ hcm, entry_seg Sn 0 (m - 1) 1 _ hcmN] at hh
    simpa using hh
  refine ⟨hceq, ?_, ?_⟩
  · rw [← hceq]; exact h0
  · rw [← hceq]; exact h1.le

/-- §6.8 geomA ANCHOR COINCIDENCE (regime A).  The `M`-side branch region
`S = seg (N[n]) A E` (`E ≥ Lng N - 1`) and the `N`-side region
`Snside = seg N A (Lng N - 1)` start at the SAME index `A` and agree verbatim
on `[A, Lng N - 2]`; with both anchors strictly below the boundary index
`m = Lng Snside - 1`, the `dropLast` P-decompositions coincide, hence
`c = cN`, `F8end` (`entry S 0 c = entry Snside 0 cN`, `shamt = 0`) and
`F9end` (`entry S 1 c ≤ entry Snside 1 cN`).
(Isabelle: `oper_d1pos_anchor_coincide_regA`.) -/
theorem oper_d1pos_anchor_coincide_regA
    (N : PS) (A E n : ℕ) (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (hj₀lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hn1 : 1 ≤ n)
    (hAbnd : A < Lng N - 1)
    (hEle : Lng N - 1 ≤ E)
    (hmulti : 1 < (P (seg (oper N n) A E)).length)
    (hmultiN : 1 < (P (seg N A (Lng N - 1))).length)
    (hclt : (IdxSum (P (seg (oper N n) A E))).getD
        ((P (seg (oper N n) A E)).length - 1) 0 <
      Lng (seg N A (Lng N - 1)) - 1)
    (hcNlt : (IdxSum (P (seg N A (Lng N - 1)))).getD
        ((P (seg N A (Lng N - 1))).length - 1) 0 <
      Lng (seg N A (Lng N - 1)) - 1) :
    let S := seg (oper N n) A E
    let Snside := seg N A (Lng N - 1)
    let c := (IdxSum (P S)).getD ((P S).length - 1) 0
    let cN := (IdxSum (P Snside)).getD ((P Snside).length - 1) 0
    c = cN ∧ entry S 0 c = entry Snside 0 cN ∧
      entry S 1 c ≤ entry Snside 1 cN := by
  have hLS : Lng (seg (oper N n) A E) = E + 1 - A := length_seg _ _ _
  have hLSn : Lng (seg N A (Lng N - 1)) = Lng N - A := by
    rw [length_seg]; omega
  have hST : TPS (seg (oper N n) A E) := by
    apply List.ne_nil_of_length_pos
    show 0 < Lng (seg (oper N n) A E)
    omega
  have hSnT : TPS (seg N A (Lng N - 1)) := by
    apply List.ne_nil_of_length_pos
    show 0 < Lng (seg N A (Lng N - 1))
    omega
  have hQeq : seg (seg (oper N n) A E) 0 (Lng (seg N A (Lng N - 1)) - 1 - 1) =
      seg (seg N A (Lng N - 1)) 0 (Lng (seg N A (Lng N - 1)) - 1 - 1) := by
    rw [seg_of_seg_68 (oper N n) A E 0 (Lng (seg N A (Lng N - 1)) - 1 - 1)
        (by omega) (by omega),
      seg_of_seg_68 N A (Lng N - 1) 0 (Lng (seg N A (Lng N - 1)) - 1 - 1)
        (by omega) (by omega)]
    exact oper_d1pos_seg_low_verbatim N n (A + 0)
      (A + (Lng (seg N A (Lng N - 1)) - 1 - 1)) hlen hzero hp hi hj₀lt hn1
      (by omega)
  exact anchor_coincide_core_ra (seg (oper N n) A E) (seg N A (Lng N - 1))
    (Lng (seg N A (Lng N - 1)) - 1) hST hSnT hmulti hmultiN
    (by omega) (by omega) hclt hcNlt hQeq

/-! ## §6.8 geomA — `cN < m` from `A ≤ j₋₂`（Nサイド、逐語） -/

/-- §6.8 geomA `cNlt` from `A ≤ j₋₂`: for `Snside = seg N A (Lng N - 1)` the
last index `m` reads `entry N 0 (Lng N - 1)` and the witness `jj = j₋₂ - A`
reads `entry N 0 j₋₂` verbatim; with `δ > 0` the strict undercut holds at the
ONLY tail index `m`, so the uniform-witness bridge gives `cN < m`.
(Isabelle: `oper_d1pos_cNlt_of_Ajm2`.) -/
theorem oper_d1pos_cNlt_of_Ajm2
    (N : PS) (A : ℕ) (hlen : 1 < Lng N)
    (hAbnd : A < Lng N - 1)
    (hmultiN : 1 < (P (seg N A (Lng N - 1))).length)
    (hAjm2 : A ≤ parent N 1 (Lng N - 1))
    (hjm2lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hdpos : entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1)) :
    (IdxSum (P (seg N A (Lng N - 1)))).getD
        ((P (seg N A (Lng N - 1))).length - 1) 0 <
      Lng (seg N A (Lng N - 1)) - 1 := by
  have hLSn : Lng (seg N A (Lng N - 1)) = Lng N - A := by
    rw [length_seg]; omega
  have hSnT : TPS (seg N A (Lng N - 1)) := by
    apply List.ne_nil_of_length_pos
    show 0 < Lng (seg N A (Lng N - 1))
    omega
  rw [show Lng (seg N A (Lng N - 1)) - 1 = Lng N - 1 - A from by omega]
  refine anchor_lt_of_uniform_witness_ra (seg N A (Lng N - 1))
    (parent N 1 (Lng N - 1) - A) (Lng N - 1 - A) hSnT hmultiN (by omega) ?_
  intro x hxlo hxhi
  have hxeq : x = Lng N - 1 - A := by omega
  subst hxeq
  have hjjS : parent N 1 (Lng N - 1) - A < Lng (seg N A (Lng N - 1)) := by
    omega
  have hmS : Lng N - 1 - A < Lng (seg N A (Lng N - 1)) := by omega
  rw [entry_seg N A (Lng N - 1) 0 _ hjjS, entry_seg N A (Lng N - 1) 0 _ hmS,
    show A + (parent N 1 (Lng N - 1) - A) = parent N 1 (Lng N - 1) from
      by omega,
    show A + (Lng N - 1 - A) = Lng N - 1 from by omega]
  exact hdpos

/-! ## §6.8 geomA/geomB — 周期内 行 0 床 -/

/-- §6.8 geomA WITHIN-PERIOD row-0 floor: the period base `j₋₂` carries the
row-0 minimum of the closed period window `[j₋₂, Lng N - 1]`.  In Lean this
is a direct value characterization: `leR N 0 j₋₂ (Lng N - 1)` (row-1 parent
step) plus `ancestor_basic_1`.  (Isabelle: `oper_d1pos_period_row0_floor`.) -/
theorem oper_d1pos_period_row0_floor
    (N : PS) (s : ℕ)
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (_hj₀lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hs : s ≤ Lng N - 1 - parent N 1 (Lng N - 1)) :
    entry N 0 (parent N 1 (Lng N - 1)) ≤
      entry N 0 (parent N 1 (Lng N - 1) + s) := by
  rcases Nat.eq_zero_or_pos s with hs0 | hs0
  · subst hs0
    simp
  · have hT : TPS N := by
      apply List.ne_nil_of_length_pos
      show 0 < Lng N
      omega
    exact (ancestor_basic_1 N (parent N 1 (Lng N - 1))
      (parent N 1 (Lng N - 1) + s) (Lng N - 1) hT (by omega) (by omega)
      (leR_base_ra N hp hi)).le

/-- §6.8 geomB STRICT within-period row-0 floor: sharpens the `≤` floor to
`<` for a non-trivial offset `0 < s ≤ w`.
(Isabelle: `oper_d1pos_strict_period_floor`.) -/
theorem oper_d1pos_strict_period_floor
    (N : PS) (s : ℕ)
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (_hj₀lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hs0 : 0 < s)
    (hs : s ≤ Lng N - 1 - parent N 1 (Lng N - 1)) :
    entry N 0 (parent N 1 (Lng N - 1)) <
      entry N 0 (parent N 1 (Lng N - 1) + s) := by
  have hT : TPS N := by
    apply List.ne_nil_of_length_pos
    show 0 < Lng N
    omega
  exact ancestor_basic_1 N (parent N 1 (Lng N - 1))
    (parent N 1 (Lng N - 1) + s) (Lng N - 1) hT (by omega) (by omega)
    (leR_base_ra N hp hi)

/-! ## §6.8 geomA — REGIME A の `clt` brick（`c < m`） -/

/-- §6.8 geomA regime-A `clt` brick: for `S = seg (N[n]) A E` with
`A < j₋₂` (regime A), the last `FirstNodes` anchor sits STRICTLY below the
boundary index `m = Lng (seg N A (Lng N - 1)) - 1`.  Witness `jj = j₋₂ - A`
reads `entry N 0 j₋₂` (block 0); every tail index `x ∈ [m, Lng S - 1]` reads
a HIGHER block (`q ≥ 1`) so its row-0 value is `≥ entry N 0 j₋₂ + δ`; the
uniform-witness bridge closes.  (Isabelle: `oper_d1pos_clt_regA`.) -/
theorem oper_d1pos_clt_regA
    (N : PS) (A E n : ℕ) (hlen : 1 < Lng N)
    (hzero : ¬(entry N 0 (Lng N - 1) = 0 ∧ entry N 1 (Lng N - 1) = 0))
    (hp : hasParent N (idx1 N (Lng N - 1)) (Lng N - 1) = true)
    (hi : idx1 N (Lng N - 1) = 1)
    (hj₀lt : parent N 1 (Lng N - 1) < Lng N - 1)
    (hn1 : 1 ≤ n)
    (hAbnd : A < parent N 1 (Lng N - 1))
    (hEle : Lng N - 1 ≤ E)
    (hEub : E < Lng (oper N n))
    (hdpos : entry N 0 (parent N 1 (Lng N - 1)) < entry N 0 (Lng N - 1))
    (hmulti : 1 < (P (seg (oper N n) A E)).length) :
    (IdxSum (P (seg (oper N n) A E))).getD
        ((P (seg (oper N n) A E)).length - 1) 0 <
      Lng (seg N A (Lng N - 1)) - 1 := by
  have hlenMn : Lng (oper N n) = parent N 1 (Lng N - 1) +
      n * (Lng N - 1 - parent N 1 (Lng N - 1)) :=
    length_oper_d1pos_68 N n hlen hzero hp hi
  have hLS : Lng (seg (oper N n) A E) = E + 1 - A := length_seg _ _ _
  have hST : TPS (seg (oper N n) A E) := by
    apply List.ne_nil_of_length_pos
    show 0 < Lng (seg (oper N n) A E)
    omega
  have hw0 : 0 < Lng N - 1 - parent N 1 (Lng N - 1) := by omega
  -- block-0 readout of the witness value
  have hblk0 := entry_oper_d1pos_zero_68 N n 0 0 hlen hzero hp hi
    (by omega) hw0
  simp only [Nat.zero_mul, Nat.add_zero] at hblk0
  rw [show Lng (seg N A (Lng N - 1)) - 1 = Lng N - 1 - A from by
    rw [length_seg]; omega]
  refine anchor_lt_of_uniform_witness_ra (seg (oper N n) A E)
    (parent N 1 (Lng N - 1) - A) (Lng N - 1 - A) hST hmulti (by omega) ?_
  intro x hxlo hxhi
  -- the witness reads `entry N 0 j₋₂` verbatim
  have hjjS : parent N 1 (Lng N - 1) - A < Lng (seg (oper N n) A E) := by
    omega
  have heSjj := entry_seg (oper N n) A E 0 (parent N 1 (Lng N - 1) - A) hjjS
  rw [show A + (parent N 1 (Lng N - 1) - A) = parent N 1 (Lng N - 1) from
    by omega] at heSjj
  -- the tail index `A + x` lies in block `q ∈ [1, n)` at offset `s`
  have hxS : x < Lng (seg (oper N n) A E) := by omega
  have heSx := entry_seg (oper N n) A E 0 x hxS
  have hxA_ge : Lng N - 1 ≤ A + x := by omega
  have hxA_le : A + x ≤ E := by omega
  obtain ⟨q, s, hxsplit, hslt, hq1, hqn⟩ :
      ∃ q s, A + x = parent N 1 (Lng N - 1) +
          q * (Lng N - 1 - parent N 1 (Lng N - 1)) + s ∧
        s < Lng N - 1 - parent N 1 (Lng N - 1) ∧ 1 ≤ q ∧ q < n := by
    refine ⟨(A + x - parent N 1 (Lng N - 1)) /
        (Lng N - 1 - parent N 1 (Lng N - 1)),
      (A + x - parent N 1 (Lng N - 1)) %
        (Lng N - 1 - parent N 1 (Lng N - 1)),
      ?_, Nat.mod_lt _ hw0, ?_, ?_⟩
    · have hdm := Nat.div_add_mod (A + x - parent N 1 (Lng N - 1))
        (Lng N - 1 - parent N 1 (Lng N - 1))
      have hcm := Nat.mul_comm (Lng N - 1 - parent N 1 (Lng N - 1))
        ((A + x - parent N 1 (Lng N - 1)) /
          (Lng N - 1 - parent N 1 (Lng N - 1)))
      omega
    · rw [Nat.one_le_div_iff hw0]
      omega
    · rw [Nat.div_lt_iff_lt_mul hw0]
      omega
  have hblkx := entry_oper_d1pos_zero_68 N n q s hlen hzero hp hi hqn hslt
  rw [← hxsplit] at hblkx
  -- within-period floor and the `q·δ ≥ δ > 0` undercut
  have hfloor : entry N 0 (parent N 1 (Lng N - 1)) ≤
      entry N 0 (parent N 1 (Lng N - 1) + s) :=
    oper_d1pos_period_row0_floor N s hp hi hj₀lt (by omega)
  have hqd : entry N 0 (Lng N - 1) - entry N 0 (parent N 1 (Lng N - 1)) ≤
      q * (entry N 0 (Lng N - 1) - entry N 0 (parent N 1 (Lng N - 1))) :=
    Nat.le_mul_of_pos_left _ (by omega)
  rw [heSjj, heSx, hblk0, hblkx]
  omega

end PSS

#print axioms PSS.oper_d1pos_seg_low_verbatim
#print axioms PSS.oper_d1pos_branch_lowshift_regA
#print axioms PSS.oper_d1pos_anchor_coincide_regA
#print axioms PSS.oper_d1pos_cNlt_of_Ajm2
#print axioms PSS.oper_d1pos_period_row0_floor
#print axioms PSS.oper_d1pos_strict_period_floor
#print axioms PSS.oper_d1pos_clt_regA
