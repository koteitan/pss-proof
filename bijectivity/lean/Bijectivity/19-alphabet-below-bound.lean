import Bijectivity.Cited
import Bijectivity.«18-trans-preserves-order»

/-!
# 補題（対応する項の上界未満の字母）

原文: 任意の \(t\in T_{\textrm{B}\omega}\) に対して、\(t<_{\textrm{B}}D_0D_\omega0\) ならば
\(t\in OT_{\textrm{B}\omega}\) は \(t\in OT_{\textrm{B}}\) と同値である。

すなわち上界 \(D_0D_\omega0\) 未満では \(D_\omega\) を許すかどうかが結論に影響しない。

原文の証明:
> (⇒) 任意の \(t'\in OT_{\textrm{B}\omega}\) をとり、\(t'<_{\textrm{B}}D_\omega0\) かつ
> \(D_0t'\in OT_{\textrm{B}\omega}\) とする。仮定及び \(OT_{\textrm{B}\omega}\) の定義より
> 任意の \(x\in G_0t'\) に対して \(x<_{\textrm{B}}D_\omega0\) である。
> \(t'\) が字母 \(D_\omega\) を含むとすると、\(t'=D_ua\) の場合は \(u=\omega\)（これは
> \(t'<_{\textrm{B}}D_\omega0\) に反する）か、\(D_\omega\) が \(a\) 側に現れる場合で、
> \(a\in G_0t'\) より \(a<_{\textrm{B}}D_\omega0\) となり内側に帰着する。複項の場合は
> \(OT_{\textrm{B}\omega}\) の定義より各主項が先頭以下なので同様。
> よって \(t'\) は字母 \(D_\omega\) を含まない。
> \(t=0\) なら \(t\in T_{\textrm{B}}\)。\(t\) が単項なら \(t=D_0a\) で \(a<_{\textrm{B}}D_\omega0\)
> なので上より \(a\) は \(D_\omega\) を含まず \(t\in T_{\textrm{B}}\)。
> \(t\) が複項なら各 \(a_i\leq_{\textrm{B}}a_0<_{\textrm{B}}D_\omega0\) より同様。
> よって \(t\in OT_{\textrm{B}}=OT_{\textrm{B}\omega}\cap T_{\textrm{B}}\)。
> (⇐) \(OT_{\textrm{B}}\subset OT_{\textrm{B}\omega}\) より即座に従う。□

形式化では原文の (⇒) の内側の議論を、\(G_0\) 有界性を仮定として持ち回る
`dfree_of_bounded_BT` / `dfree_of_bounded_BPList` の相互再帰にした。
原文が「\(t'\) が \(D_\omega\) を含む」と背理法で書いている部分を、
「\(D_\omega\) を含まない」を直接構成する向きに読み替えたものである
（\(a\in G_0t'\) と \(G_0a\subseteq G_0t'\) を使う点は原文どおり）。
-/

namespace Bijectivity

open PSS

/-! ## 記法と小道具 -/

/-- \(D_\omega0\)。 -/
def DomegaZero : BT := Dprin ⊤ BZero

/-- 主項の崩壊記号の水準。 -/
def dbIndex : BP → ℕ∞
  | .db v _ => v

/-- 主項の本体。 -/
def dbBody : BP → BT
  | .db _ b => b

theorem lessBPList_nil_right' : ∀ ps : List BP, lessBPList ps [] = false
  | [] => rfl
  | _ :: _ => rfl

theorem lessBT_BZero : ∀ a : BT, lessBT a BZero = false
  | .trm ps => lessBPList_nil_right' ps

/-- 単一主項との比較は主項の比較。 -/
theorem lessBPList_single_cons {p q : BP} {rest : List BP}
    (h : lessBPList (p :: rest) [q] = true) : lessBP p q = true := by
  simp only [lessBPList, lessBPList_nil_right', Bool.and_false, Bool.or_false] at h
  exact h

/-- 主項の比較の分解。 -/
theorem lessBP_split {w v : ℕ∞} {a b : BT} (h : lessBP (.db w a) (.db v b) = true) :
    w < v ∨ (w = v ∧ lessBT a b = true) := by
  simp only [lessBP, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
    beq_iff_eq] at h
  exact h

/-- 主項の広義比較の分解。 -/
theorem prin_leBT_split {w v : ℕ∞} {a b : BT}
    (h : leBT (BT.trm [BP.db w a]) (BT.trm [BP.db v b]) = true) :
    w < v ∨ (w = v ∧ leBT a b = true) := by
  simp only [leBT, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · rcases lessBP_split (lessBPList_single_cons (rest := []) h) with h' | ⟨h1, h2⟩
    · exact Or.inl h'
    · exact Or.inr ⟨h1, by simp [leBT, h2]⟩
  · have h' : w = v ∧ a = b := by simpa using h
    obtain ⟨rfl, rfl⟩ := h'
    exact Or.inr ⟨rfl, leBT_refl a⟩

/-- 広義降順なら各主項は先頭以下。 -/
theorem descP_head_bound : ∀ (p : BP) (ps : List BP), descP (p :: ps) = true →
    ∀ q ∈ ps, leBT (BT.trm [q]) (BT.trm [p]) = true
  | _, [], _ => by simp
  | p, q :: ps, h => by
      simp only [descP, Bool.and_eq_true] at h
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr'
      · exact h.1
      · exact leBT_trans (descP_head_bound q ps h.2 r hr') h.1

/-- 上界 \(D_\omega0\) 未満なら、広義降順な主項列の添字はすべて \(\omega\) と異なる。 -/
theorem index_ne_top_of_lt : ∀ (ps : List BP), descP ps = true →
    lessBPList ps [BP.db ⊤ BZero] = true → ∀ p ∈ ps, dbIndex p ≠ ⊤
  | [], _, _ => by simp
  | .db w a :: rest, hdesc, hlt => by
      have hw : w ≠ ⊤ := by
        rcases lessBP_split (lessBPList_single_cons hlt) with h | ⟨_, h2⟩
        · exact ne_of_lt h
        · rw [lessBT_BZero] at h2; exact absurd h2 (by simp)
      have hwtop : w < ⊤ := lt_top_iff_ne_top.mpr hw
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact hw
      · cases p with
        | db w' a' =>
            have hle := descP_head_bound _ _ hdesc _ hp'
            rcases prin_leBT_split hle with h | ⟨h1, _⟩
            · exact ne_of_lt (lt_trans h hwtop)
            · exact h1 ▸ hw

/-! ## \(G_0\) の展開 -/

theorem gatherBP_zero (w : ℕ∞) (a : BT) :
    gatherBP 0 (.db w a) = a :: gatherBT 0 a := by
  simp [gatherBP]

/-! ## 原文 (⇒) の内側の議論 -/

mutual

/-- \(G_0\) 有界性のもとで \(D_\omega\) を含まないこと（項側）。 -/
theorem dfree_of_bounded_BT : ∀ (t : BT), isOT_BT t = true →
    lessBT t DomegaZero = true →
    (∀ x ∈ gatherBT 0 t, lessBT x DomegaZero = true) →
    dfree_BT t = true
  | .trm ps, hOT, hlt, hG => by
      have hOT' : isOT_BPList ps = true ∧ descP ps = true := by
        simpa [isOT_BT, Bool.and_eq_true] using hOT
      exact dfree_of_bounded_BPList ps hOT'.1
        (index_ne_top_of_lt ps hOT'.2 hlt) hG

/-- \(G_0\) 有界性のもとで \(D_\omega\) を含まないこと（主項列側）。 -/
theorem dfree_of_bounded_BPList : ∀ (ps : List BP), isOT_BPList ps = true →
    (∀ p ∈ ps, dbIndex p ≠ ⊤) →
    (∀ x ∈ gatherBPList 0 ps, lessBT x DomegaZero = true) →
    dfree_BPList ps = true
  | [], _, _, _ => rfl
  | .db w a :: rest, hOT, hidx, hG => by
      have hOT' : isOT_BP (.db w a) = true ∧ isOT_BPList rest = true := by
        simpa [isOT_BPList, Bool.and_eq_true] using hOT
      have hOTa : isOT_BT a = true := by
        have hp := hOT'.1
        simp only [isOT_BP, Bool.and_eq_true] at hp
        exact hp.1
      have hGsplit : gatherBPList 0 (BP.db w a :: rest)
          = (a :: gatherBT 0 a) ++ gatherBPList 0 rest := by
        simp [gatherBPList, gatherBP_zero]
      have hGa : ∀ x ∈ gatherBT 0 a, lessBT x DomegaZero = true := by
        intro x hx
        exact hG x (by rw [hGsplit]; simp [hx])
      have hlta : lessBT a DomegaZero = true := hG a (by rw [hGsplit]; simp)
      have hrec := dfree_of_bounded_BT a hOTa hlta hGa
      have hrest := dfree_of_bounded_BPList rest hOT'.2
        (fun p hp => hidx p (by simp [hp]))
        (fun x hx => hG x (by rw [hGsplit]; simp [hx]))
      have hw : w ≠ ⊤ := by
        have := hidx (BP.db w a) (by simp)
        simpa [dbIndex] using this
      simp [dfree_BPList, dfree_BP, hw, hrec, hrest]

end

/-! ## 主張 -/

/-- 添字がすべて 0 で本体が上界未満なら、\(G_0\) 全体が上界未満。 -/
theorem gather_bound_all_zero : ∀ (ps : List BP), isOT_BPList ps = true →
    (∀ p ∈ ps, dbIndex p = 0 ∧ lessBT (dbBody p) DomegaZero = true) →
    ∀ x ∈ gatherBPList 0 ps, lessBT x DomegaZero = true
  | [], _, _ => by simp [gatherBPList]
  | .db w a :: rest, hOT, hb => by
      intro x hx
      have hOT' : isOT_BP (.db w a) = true ∧ isOT_BPList rest = true := by
        simpa [isOT_BPList, Bool.and_eq_true] using hOT
      have hw : w = 0 := by
        have := (hb (BP.db w a) (by simp)).1
        simpa [dbIndex] using this
      subst hw
      have hlta : lessBT a DomegaZero = true := by
        have := (hb (BP.db (0 : ℕ∞) a) (by simp)).2
        simpa [dbBody] using this
      have hall : (gatherBT 0 a).all (fun y => lessBT y a) = true := by
        have hp := hOT'.1
        simp only [isOT_BP, Bool.and_eq_true] at hp
        exact hp.2
      have hGsplit : gatherBPList 0 (BP.db 0 a :: rest)
          = (a :: gatherBT 0 a) ++ gatherBPList 0 rest := by
        simp [gatherBPList, gatherBP_zero]
      rw [hGsplit] at hx
      rcases List.mem_append.mp hx with hx' | hx'
      · rcases List.mem_cons.mp hx' with rfl | hx''
        · exact hlta
        · exact lessBT_linear_trans _ _ _ (List.all_eq_true.mp hall x hx'') hlta
      · exact gather_bound_all_zero rest hOT'.2 (fun p hp => hb p (by simp [hp])) x hx'

/-- 原文の補題（対応する項の上界未満の字母）。 -/
theorem OT_iff_OT_B_of_lt {t : BT} (h : lessBT t DzeroDomegaZero = true) :
    t ∈ OT ↔ t ∈ OT_B := by
  constructor
  · intro hOT
    refine ⟨hOT, ?_⟩
    show dfree_BT t = true
    cases t with
    | trm ps =>
      cases ps with
      | nil => rfl
      | cons p rest =>
        cases p with
        | db w a =>
          have hOTt : isOT_BT (BT.trm (BP.db w a :: rest)) = true := hOT
          have hOT' : isOT_BPList (BP.db w a :: rest) = true ∧
              descP (BP.db w a :: rest) = true := by
            simpa [isOT_BT, Bool.and_eq_true] using hOTt
          -- 先頭の添字は 0、本体は D_ω0 未満
          have hhead : w = 0 ∧ lessBT a DomegaZero = true := by
            rcases lessBP_split (lessBPList_single_cons h) with hlt | ⟨h1, h2⟩
            · exact absurd hlt (by simp)
            · exact ⟨h1, h2⟩
          obtain ⟨hw0, hlta⟩ := hhead
          subst hw0
          -- 各主項も添字 0 で本体は先頭以下
          have hb : ∀ p ∈ BP.db (0 : ℕ∞) a :: rest,
              dbIndex p = 0 ∧ lessBT (dbBody p) DomegaZero = true := by
            intro p hp
            rcases List.mem_cons.mp hp with rfl | hp'
            · exact ⟨rfl, hlta⟩
            · cases p with
              | db w' a' =>
                  have hle := descP_head_bound _ _ hOT'.2 _ hp'
                  rcases prin_leBT_split hle with hlt' | ⟨h1, h2⟩
                  · exact absurd hlt' (by simp)
                  · exact ⟨h1, leBT_lessBT_trans h2 hlta⟩
          exact dfree_of_bounded_BPList _ hOT'.1
            (fun p hp => by rw [(hb p hp).1]; simp)
            (gather_bound_all_zero _ hOT'.1 hb)
  · exact fun h => h.1

end Bijectivity
