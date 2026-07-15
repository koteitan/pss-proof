import PSS.Flat

/-!
# §7.2 命題（scb 分解の一意性）

- Isabelle: `m_7_2_scb_unique_sb`, `m_7_2_scb_unique_decomp`
- 状態: 第 1 主張（固定した `c` に対する `(s,b)` の一意性）を証明済
-/

namespace PSS

/-- 文字列末尾の連続した右括弧の個数。 -/
private def trailRP (xs : List Sym) : ℕ :=
  (xs.reverse.takeWhile (· = .rp)).length

private theorem takeWhile_append_of_all {α : Type} (p : α → Prop)
    [DecidablePred p] (xs ys : List α) (h : ∀ x ∈ xs, p x) :
    (xs ++ ys).takeWhile p = xs ++ ys.takeWhile p := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx : p x := h x (by simp)
      have hxs : ∀ y ∈ xs, p y := by
        intro y hy
        exact h y (by simp [hy])
      simp [hx, ih hxs]

private theorem takeWhile_append_of_exists_not {α : Type} (p : α → Prop)
    [DecidablePred p] (xs ys : List α) (h : ∃ x ∈ xs, ¬p x) :
    (xs ++ ys).takeWhile p = xs.takeWhile p := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      by_cases hx : p x
      · have hxs : ∃ y ∈ xs, ¬p y := by
          rcases h with ⟨y, hy, hny⟩
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact (hny hx).elim
          · exact ⟨y, hy, hny⟩
        simp [hx, ih hxs]
      · simp [hx]

private theorem trailRP_append (xs b : List Sym)
    (hb : ∀ x ∈ b, x = .rp) :
    trailRP (xs ++ b) = b.length + trailRP xs := by
  have hrev : ∀ x ∈ b.reverse, x = .rp := by
    intro x hx
    exact hb x (List.mem_reverse.mp hx)
  simp only [trailRP, List.reverse_append]
  rw [takeWhile_append_of_all (fun x : Sym => x = .rp) b.reverse xs.reverse hrev]
  simp

private theorem trailRP_prefix (s c : List Sym)
    (hc : ∃ x ∈ c, x ≠ .rp) :
    trailRP (s ++ c) = trailRP c := by
  have hrev : ∃ x ∈ c.reverse, x ≠ .rp := by
    rcases hc with ⟨x, hx, hne⟩
    exact ⟨x, List.mem_reverse.mpr hx, hne⟩
  simp only [trailRP, List.reverse_append]
  rw [takeWhile_append_of_exists_not (fun x : Sym => x = .rp)
    c.reverse s.reverse hrev]

private theorem isPTB_str_has_nonRP {c : List Sym} (hc : isPTB_str c) :
    ∃ x ∈ c, x ≠ .rp := by
  rcases hc with ⟨⟨u, a⟩, _, rfl⟩
  exact ⟨.dsym u, by simp [flatBP]⟩

private theorem allRP_eq_of_length_eq {b₀ b₁ : List Sym}
    (h₀ : ∀ x ∈ b₀, x = .rp) (h₁ : ∀ x ∈ b₁, x = .rp)
    (hlen : b₀.length = b₁.length) : b₀ = b₁ := by
  induction b₀ generalizing b₁ with
  | nil =>
      cases b₁ with
      | nil => rfl
      | cons y ys => simp at hlen
  | cons x xs ih =>
      cases b₁ with
      | nil => simp at hlen
      | cons y ys =>
          have hx : x = .rp := h₀ x (by simp)
          have hy : y = .rp := h₁ y (by simp)
          have hxs : ∀ z ∈ xs, z = .rp := by
            intro z hz
            exact h₀ z (by simp [hz])
          have hys : ∀ z ∈ ys, z = .rp := by
            intro z hz
            exact h₁ z (by simp [hz])
          have hlens : xs.length = ys.length := Nat.succ.inj hlen
          simp [hx, hy, ih hxs hys hlens]

private theorem scb_unique_nonzero {t : BT} {s₀ s₁ c b₀ b₁ : List Sym}
    (h₀ : scb_decomp t s₀ c b₀) (h₁ : scb_decomp t s₁ c b₁)
    (ht : t ≠ BZero) :
    s₀ = s₁ ∧ b₀ = b₁ := by
  rcases h₀ with ⟨e₀, hp₀, hrp₀⟩
  rcases h₁ with ⟨e₁, _, hrp₁⟩
  have hnon := isPTB_str_has_nonRP (hp₀ ht)
  have trail₀ : trailRP (flatBT t) = b₀.length + trailRP c := by
    rw [e₀]
    simpa only [List.append_assoc] using
      trailRP_append (s₀ ++ c) b₀ hrp₀ |>.trans
        (congrArg (b₀.length + ·) (trailRP_prefix s₀ c hnon))
  have trail₁ : trailRP (flatBT t) = b₁.length + trailRP c := by
    rw [e₁]
    simpa only [List.append_assoc] using
      trailRP_append (s₁ ++ c) b₁ hrp₁ |>.trans
        (congrArg (b₁.length + ·) (trailRP_prefix s₁ c hnon))
  have hlen : b₀.length = b₁.length := Nat.add_right_cancel (trail₀.symm.trans trail₁)
  have hb : b₀ = b₁ := allRP_eq_of_length_eq hrp₀ hrp₁ hlen
  have heq : s₀ ++ (c ++ b₀) = s₁ ++ (c ++ b₀) := by
    simpa [List.append_assoc, hb] using e₀.symm.trans e₁
  exact ⟨List.append_cancel_right heq, hb⟩

/-- 固定した中央文字列 `c` を持つ scb 分解では、前置部 `s` と右括弧尾部 `b` が一意。
原文の一意性命題の第 1 主張。 -/
theorem scb_unique_decomp (t : BT) (s₀ s₁ c b₀ b₁ : List Sym)
    (_htb : t ∈ T_B)
    (h₀ : scb_decomp t s₀ c b₀) (h₁ : scb_decomp t s₁ c b₁) :
    s₀ = s₁ ∧ b₀ = b₁ := by
  by_cases ht : t = BZero
  · subst t
    rcases h₀ with ⟨e₀, _, hrp₀⟩
    rcases h₁ with ⟨e₁, _, hrp₁⟩
    have emptyTail (s c b : List Sym)
        (e : flatBT BZero = s ++ c ++ b) (hrp : ∀ x ∈ b, x = .rp) : b = [] := by
      by_contra hb
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil b hb
      have hxrp : x = .rp := hrp x hx
      have hxflat : x ∈ flatBT BZero := by
        rw [e]
        simp [hx]
      subst x
      simpa [BZero, flatBT] using hxflat
    have hb₀ := emptyTail s₀ c b₀ e₀ hrp₀
    have hb₁ := emptyTail s₁ c b₁ e₁ hrp₁
    subst b₀
    subst b₁
    simp only [List.append_nil] at e₀ e₁
    exact ⟨List.append_cancel_right (e₀.symm.trans e₁), rfl⟩
  · exact scb_unique_nonzero h₀ h₁ ht

/-! ## 第 0 種・第 1 種の排他性 -/

/-- 反転した flatten 文字列から、末尾の右括弧列を飛ばして最深部の
`zero` 直前にある `D` の添字を読む。 -/
private def scanBottom : List Sym → Option ℕ
  | .rp :: xs => scanBottom xs
  | .zero :: .dsym u :: _ => some u.toNat
  | _ => none

private def bottomIndex (xs : List Sym) : Option ℕ :=
  scanBottom xs.reverse

private theorem scanBottom_append_of_some {xs : List Sym} {n : ℕ}
    (h : scanBottom xs = some n) (ys : List Sym) :
    scanBottom (xs ++ ys) = some n := by
  induction xs with
  | nil => simp [scanBottom] at h
  | cons x xs ih =>
      cases x with
      | lp => simp [scanBottom] at h
      | cm => simp [scanBottom] at h
      | rp =>
          simp only [scanBottom] at h ⊢
          exact ih h
      | zero =>
          cases xs with
          | nil => simp [scanBottom] at h
          | cons y xs =>
              cases y <;> simp_all [scanBottom]
      | dsym u => simp [scanBottom] at h

private theorem scanBottom_allRP_prefix (b xs : List Sym)
    (hb : ∀ x ∈ b, x = .rp) :
    scanBottom (b ++ xs) = scanBottom xs := by
  induction b with
  | nil => rfl
  | cons x b ih =>
      have hx : x = .rp := hb x (by simp)
      have htail : ∀ y ∈ b, y = .rp := by
        intro y hy
        exact hb y (by simp [hy])
      subst x
      simpa [scanBottom] using ih htail

private theorem bottomIndex_append_allRP (xs b : List Sym)
    (hb : ∀ x ∈ b, x = .rp) :
    bottomIndex (xs ++ b) = bottomIndex xs := by
  have hrev : ∀ x ∈ b.reverse, x = .rp := by
    intro x hx
    exact hb x (List.mem_reverse.mp hx)
  simpa [bottomIndex, List.reverse_append] using
    scanBottom_allRP_prefix b.reverse xs.reverse hrev

private theorem bottomIndex_prefix_of_some (pre xs : List Sym) {n : ℕ}
    (h : bottomIndex xs = some n) :
    bottomIndex (pre ++ xs) = some n := by
  unfold bottomIndex at h ⊢
  rw [List.reverse_append]
  exact scanBottom_append_of_some h pre.reverse

private theorem bottomIndex_prefix_of_ne_none (pre xs : List Sym)
    (h : bottomIndex xs ≠ none) :
    bottomIndex (pre ++ xs) = bottomIndex xs := by
  cases hx : bottomIndex xs with
  | none => exact (h hx).elim
  | some n => exact bottomIndex_prefix_of_some pre xs hx

private theorem rightNodesBP_ne_nil (p : BP) : rightNodesBP p ≠ [] := by
  cases p
  simp [rightNodesBP]

private theorem rightNodesList_ne_nil : ∀ ps : List BP,
    ps ≠ [] → rightNodesList ps ≠ []
  | [], h => (h rfl).elim
  | [p], _ => by simp [rightNodesList, rightNodesBP_ne_nil]
  | p :: q :: ps, _ => by
      simpa [rightNodesList] using
        rightNodesList_ne_nil (q :: ps) (by simp)

private theorem getLast?_ne_none_of_ne_nil {α : Type} {xs : List α}
    (h : xs ≠ []) : xs.getLast? ≠ none := by
  intro hn
  exact h (List.getLast?_eq_none_iff.mp hn)

private theorem getLast?_cons_of_ne_nil {α : Type} (x : α) {xs : List α}
    (h : xs ≠ []) : (x :: xs).getLast? = xs.getLast? := by
  cases xs with
  | nil => exact (h rfl).elim
  | cons y ys => simp [List.getLast?_cons]

private def BPBottom (p : BP) : Prop :=
  bottomIndex (flatBP p) = (rightNodesBP p).getLast?

private def AllBPBottom : List BP → Prop
  | [] => True
  | p :: ps => BPBottom p ∧ AllBPBottom ps

private theorem flatBPTail_bottom (ps : List BP) (hps : AllBPBottom ps) :
    bottomIndex (flatBPTail ps) = (rightNodesList ps).getLast? := by
  induction ps with
  | nil => simp [flatBPTail, rightNodesList, bottomIndex, scanBottom]
  | cons p ps ih =>
      rcases hps with ⟨hp, hps⟩
      cases ps with
      | nil =>
          have hn : bottomIndex (flatBP p) ≠ none := by
            rw [hp]
            exact getLast?_ne_none_of_ne_nil (rightNodesBP_ne_nil p)
          simpa [flatBPTail, rightNodesList] using
            (bottomIndex_prefix_of_ne_none [.cm] (flatBP p) hn).trans hp
      | cons q qs =>
          have htail := ih hps
          have hrn : rightNodesList (q :: qs) ≠ [] :=
            rightNodesList_ne_nil (q :: qs) (by simp)
          have hn : bottomIndex (flatBPTail (q :: qs)) ≠ none := by
            rw [htail]
            exact getLast?_ne_none_of_ne_nil hrn
          simpa [flatBPTail, rightNodesList, List.append_assoc] using
            (bottomIndex_prefix_of_ne_none (.cm :: flatBP p)
              (flatBPTail (q :: qs)) hn).trans htail

private theorem flatBT_bottom (t : BT) :
    bottomIndex (flatBT t) = (RightNodes t).getLast? := by
  exact BT.rec
    (motive_1 := fun t => bottomIndex (flatBT t) = (RightNodes t).getLast?)
    (motive_2 := BPBottom)
    (motive_3 := AllBPBottom)
    (fun ps hps => by
      cases ps with
      | nil => simp [flatBT, RightNodes, rightNodesList, bottomIndex, scanBottom]
      | cons p ps =>
          rcases hps with ⟨hp, hps⟩
          cases ps with
          | nil => simpa [flatBT, RightNodes, rightNodesList] using hp
          | cons q qs =>
              have htail := flatBPTail_bottom (q :: qs) hps
              have hrn : rightNodesList (q :: qs) ≠ [] :=
                rightNodesList_ne_nil (q :: qs) (by simp)
              have hn : bottomIndex (flatBPTail (q :: qs)) ≠ none := by
                rw [htail]
                exact getLast?_ne_none_of_ne_nil hrn
              calc
                bottomIndex (flatBT (.trm (p :: q :: qs))) =
                    bottomIndex (((.lp :: flatBP p) ++ flatBPTail (q :: qs)) ++ [.rp]) := by
                      simp [flatBT, List.append_assoc]
                _ = bottomIndex ((.lp :: flatBP p) ++ flatBPTail (q :: qs)) :=
                      bottomIndex_append_allRP _ _ (by simp)
                _ = bottomIndex (flatBPTail (q :: qs)) :=
                      bottomIndex_prefix_of_ne_none _ _ hn
                _ = (rightNodesList (q :: qs)).getLast? := htail
                _ = (RightNodes (.trm (p :: q :: qs))).getLast? := by
                      simp [RightNodes, rightNodesList])
    (fun u a ih => by
      cases a with
      | trm ps =>
          cases ps with
          | nil =>
              simp [BPBottom, flatBP, flatBT, rightNodesBP, RightNodes,
                rightNodesList, bottomIndex, scanBottom]
          | cons p ps =>
              have hrn : RightNodes (.trm (p :: ps)) ≠ [] := by
                simpa [RightNodes] using
                  rightNodesList_ne_nil (p :: ps) (by simp)
              have hn : bottomIndex (flatBT (.trm (p :: ps))) ≠ none := by
                rw [ih]
                exact getLast?_ne_none_of_ne_nil hrn
              calc
                bottomIndex (flatBP (.db u (.trm (p :: ps)))) =
                    bottomIndex ([.dsym u] ++ flatBT (.trm (p :: ps))) := by
                      simp [flatBP]
                _ = bottomIndex (flatBT (.trm (p :: ps))) :=
                      bottomIndex_prefix_of_ne_none _ _ hn
                _ = (RightNodes (.trm (p :: ps))).getLast? := ih
                _ = (rightNodesBP (.db u (.trm (p :: ps)))).getLast? := by
                      simpa [rightNodesBP] using
                        (getLast?_cons_of_ne_nil u.toNat hrn).symm)
    trivial
    (fun _ _ hp hps => ⟨hp, hps⟩)
    t

private theorem flatBP_bottom (p : BP) :
    bottomIndex (flatBP p) = (rightNodesBP p).getLast? := by
  simpa [flatBT, RightNodes, rightNodesList] using
    flatBT_bottom (.trm [p])

/-- scb-shaped occurrence of a principal has the same deepest right-spine index
as the ambient term. -/
theorem scb_occurrence_bottom {t : BT} {p : BP} {s b : List Sym}
    (hflat : flatBT t = s ++ flatBP p ++ b)
    (hb : ∀ x ∈ b, x = .rp) :
    (RightNodes t).getLast? = (rightNodesBP p).getLast? := by
  have hp := flatBP_bottom p
  have hpn : bottomIndex (flatBP p) ≠ none := by
    rw [hp]
    exact getLast?_ne_none_of_ne_nil (rightNodesBP_ne_nil p)
  calc
    (RightNodes t).getLast? = bottomIndex (flatBT t) := (flatBT_bottom t).symm
    _ = bottomIndex ((s ++ flatBP p) ++ b) := by
      exact congrArg bottomIndex (by simpa [List.append_assoc] using hflat)
    _ = bottomIndex (s ++ flatBP p) := bottomIndex_append_allRP _ _ hb
    _ = bottomIndex (flatBP p) := bottomIndex_prefix_of_ne_none _ _ hpn
    _ = (rightNodesBP p).getLast? := hp

private theorem getLast?_eq_some_getD_last {α : Type} (xs : List α) (d : α)
    (hxs : xs ≠ []) :
    xs.getLast? = some (xs.getD (xs.length - 1) d) := by
  have hlt : xs.length - 1 < xs.length := by
    have : 0 < xs.length := by
      cases xs with
      | nil => exact (hxs rfl).elim
      | cons x xs => simp
    omega
  rw [List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hlt]
  rfl

private theorem getD_drop (R : List ℕ) (k j d : ℕ) :
    (R.drop k).getD j d = R.getD (k + j) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

private theorem getD_drop_last (R : List ℕ) (k d : ℕ)
    (hk : k < R.length) :
    (R.drop k).getD ((R.drop k).length - 1) d =
      R.getD (R.length - 1) d := by
  rw [getD_drop]
  congr 2
  simp only [List.length_drop]
  omega

/-- 同じリストの二つの suffix がとも第 1 種の形なら、開始位置は一致する。
記事の kind-1 maximality に対応する純リスト核。 -/
theorem scb_kind1_drop_index_pin (R : List ℕ) (k₀ k₁ : ℕ)
    (hk₀ : k₀ < R.length) (hk₁ : k₁ < R.length)
    (hlen₀ : 2 ≤ (R.drop k₀).length) (hlen₁ : 2 ≤ (R.drop k₁).length)
    (hhead₀ : (R.drop k₀).getD 0 0 <
      (R.drop k₀).getD ((R.drop k₀).length - 1) 0)
    (hinner₀ : ∀ j, 0 < j → j < (R.drop k₀).length - 1 →
      (R.drop k₀).getD ((R.drop k₀).length - 1) 0 ≤
        (R.drop k₀).getD j 0)
    (hhead₁ : (R.drop k₁).getD 0 0 <
      (R.drop k₁).getD ((R.drop k₁).length - 1) 0)
    (hinner₁ : ∀ j, 0 < j → j < (R.drop k₁).length - 1 →
      (R.drop k₁).getD ((R.drop k₁).length - 1) 0 ≤
        (R.drop k₁).getD j 0) :
    k₀ = k₁ := by
  let L := R.length - 1
  let U := R.getD L 0
  have hlast₀ : (R.drop k₀).getD ((R.drop k₀).length - 1) 0 = U := by
    simpa [L, U] using getD_drop_last R k₀ 0 hk₀
  have hlast₁ : (R.drop k₁).getD ((R.drop k₁).length - 1) 0 = U := by
    simpa [L, U] using getD_drop_last R k₁ 0 hk₁
  have hk₀L : k₀ < L := by
    simp [L, List.length_drop] at hlen₀ ⊢
    omega
  have hk₁L : k₁ < L := by
    simp [L, List.length_drop] at hlen₁ ⊢
    omega
  have hheadR₀ : R.getD k₀ 0 < U := by
    have h := hhead₀
    rw [hlast₀, getD_drop] at h
    simpa using h
  have hheadR₁ : R.getD k₁ 0 < U := by
    have h := hhead₁
    rw [hlast₁, getD_drop] at h
    simpa using h
  have hinterR₀ : ∀ i, k₀ < i → i < L → U ≤ R.getD i 0 := by
    intro i hi₀ hiL
    have hjpos : 0 < i - k₀ := by omega
    have hjlt : i - k₀ < (R.drop k₀).length - 1 := by
      simp [L, List.length_drop] at hiL ⊢
      omega
    have h := hinner₀ (i - k₀) hjpos hjlt
    rw [hlast₀, getD_drop] at h
    have : k₀ + (i - k₀) = i := by omega
    simpa [this] using h
  have hinterR₁ : ∀ i, k₁ < i → i < L → U ≤ R.getD i 0 := by
    intro i hi₁ hiL
    have hjpos : 0 < i - k₁ := by omega
    have hjlt : i - k₁ < (R.drop k₁).length - 1 := by
      simp [L, List.length_drop] at hiL ⊢
      omega
    have h := hinner₁ (i - k₁) hjpos hjlt
    rw [hlast₁, getD_drop] at h
    have : k₁ + (i - k₁) = i := by omega
    simpa [this] using h
  rcases lt_trichotomy k₀ k₁ with hlt | heq | hgt
  · exact (not_lt_of_ge (hinterR₀ k₁ hlt hk₁L) hheadR₁).elim
  · exact heq
  · exact (not_lt_of_ge (hinterR₁ k₀ hgt hk₀L) hheadR₀).elim

/-- 訂正 A14 後の第 3 主張。非零項は第 0 種と第 1 種の両方には分解できない。 -/
theorem scb_kinds_exclusive {t : BT} (ht : t ≠ BZero) :
    ¬scb_kind0_able t ∨ ¬scb_kind1_able t := by
  by_contra hboth
  have hk0 : scb_kind0_able t := by tauto
  have hk1 : scb_kind1_able t := by tauto
  rcases hk0 with ⟨s₀, c₀, b₀, hkind0⟩
  rcases hk1 with ⟨s₁, c₁, b₁, hkind1⟩
  rcases hkind0.1.2.1 ht with ⟨p₀, _, hc₀⟩
  rcases hkind1.1.2.1 ht with ⟨p₁, _, hc₁⟩
  have hbottom : (rightNodesBP p₀).getLast? = (rightNodesBP p₁).getLast? := by
    have hf₀ : flatBT t = s₀ ++ flatBP p₀ ++ b₀ := by
      simpa [hc₀] using hkind0.1.1
    have hf₁ : flatBT t = s₁ ++ flatBP p₁ ++ b₁ := by
      simpa [hc₁] using hkind1.1.1
    rw [← scb_occurrence_bottom hf₀ hkind0.1.2.2,
      ← scb_occurrence_bottom hf₁ hkind1.1.2.2]
  have hzero := hkind0.2 p₀ hc₀
  have hlast0 : (rightNodesBP p₀).getLast? = some 0 := by
    let r := rightNodesBP p₀
    have hzero' : r.length = 2 ∧ r.getD 1 0 = 0 := by
      simpa [r, RightNodes, rightNodesList] using hzero
    have hrne : r ≠ [] := by
      intro hr
      simp [hr] at hzero'
    have hlast := getLast?_eq_some_getD_last r 0 hrne
    rw [hzero'.1] at hlast
    norm_num at hlast
    have hvalopt : r[1]?.getD 0 = 0 := by
      rw [← List.getD_eq_getElem?_getD]
      exact hzero'.2
    rw [hvalopt] at hlast
    simpa [r] using hlast
  have hone := hkind1.2 p₁ hc₁
  let r := rightNodesBP p₁
  let j := r.length - 1
  have hone' : 1 ≤ j ∧ r.getD 0 0 < r.getD j 0 ∧
      ∀ k, 0 < k → k < j → r.getD j 0 ≤ r.getD k 0 := by
    simpa [r, j, RightNodes, rightNodesList] using hone
  have hj : 1 ≤ j := hone'.1
  have hlt : r.getD 0 0 < r.getD j 0 := hone'.2.1
  have hrne : r ≠ [] := by
    intro hr
    simp [r, j, hr] at hj
  have hpos : 0 < r.getD j 0 := lt_of_le_of_lt (Nat.zero_le _) hlt
  have hlast1 : r.getLast? = some (r.getD j 0) := by
    simpa [j] using getLast?_eq_some_getD_last r 0 hrne
  have hbottom' : (rightNodesBP p₀).getLast? = r.getLast? := by
    simpa [r] using hbottom
  have hs : some (0 : ℕ) = some (r.getD j 0) :=
    hlast0.symm.trans (hbottom'.trans hlast1)
  have hz : 0 = r.getD j 0 := Option.some.inj hs
  exact (Nat.ne_of_gt hpos) hz.symm

/-- A14 の零項反例。`c = []` は principal 文字列ではないが、零項ではその条件が
免除されるため、第 0 種・第 1 種の条件がともに空虚に成立する。 -/
theorem scb_kinds_exclusive_original_false :
    scb_kind0_able BZero ∧ scb_kind1_able BZero := by
  have hdecomp : scb_decomp BZero [.zero] [] [] := by
    simp [scb_decomp, BZero, flatBT]
  constructor
  · refine ⟨[.zero], [], [], hdecomp, ?_⟩
    intro p hp
    cases p with
    | db u a => simp [flatBP] at hp
  · refine ⟨[.zero], [], [], hdecomp, ?_⟩
    intro p hp
    cases p with
    | db u a => simp [flatBP] at hp

#print axioms scb_unique_decomp
#print axioms scb_occurrence_bottom
#print axioms scb_kind1_drop_index_pin
#print axioms scb_kinds_exclusive
#print axioms scb_kinds_exclusive_original_false

end PSS
