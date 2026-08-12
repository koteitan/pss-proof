import Mathlib.Data.ENat.Basic
import Mathlib.Tactic

/-!
# Buchholz (1986) §2.1 — 項と辞書式順序

出典: W. Buchholz, “A new system of proof-theoretic ordinal functions”,
Annals of Pure and Applied Logic 32 (1986), §2, Lemma 2.1。

旧配置 `PSS/Buchholz.lean` のうち、項、principal 項、構造的等値判定、
辞書式順序、および principal 成分分解を収録する。
-/

namespace PSS

/-! ## 項と順序 -/

/- Buchholz 項と principal 項。`Trm []` が `0`、`Trm [DB v b]` が `D_v b`。 -/
mutual
  inductive BT where
    | trm : List BP → BT
  inductive BP where
    | db : ℕ∞ → BT → BP
end

mutual
  private def beqBT : BT → BT → Bool
    | .trm as, .trm bs => beqBPList as bs
  private def beqBP : BP → BP → Bool
    | .db u a, .db v b => u == v && beqBT a b
  private def beqBPList : List BP → List BP → Bool
    | [], [] => true
    | [], _ :: _ => false
    | _ :: _, [] => false
    | a :: as, b :: bs => beqBP a b && beqBPList as bs
end

instance : BEq BT := ⟨beqBT⟩
instance : BEq BP := ⟨beqBP⟩

mutual
  private theorem beqBT_refl : ∀ a : BT, beqBT a a = true
    | .trm as => by simp [beqBT, beqBPList_refl as]
  private theorem beqBP_refl : ∀ p : BP, beqBP p p = true
    | .db u a => by simp [beqBP, beqBT_refl a]
  private theorem beqBPList_refl : ∀ ps : List BP, beqBPList ps ps = true
    | [] => rfl
    | p :: ps => by simp [beqBPList, beqBP_refl p, beqBPList_refl ps]
end

mutual
  private theorem beqBT_eq : ∀ {a b : BT}, beqBT a b = true → a = b
    | .trm as, .trm bs, h => by
        have hab : as = bs := beqBPList_eq (xs := as) (ys := bs) h
        exact congrArg BT.trm hab
  private theorem beqBP_eq : ∀ {p q : BP}, beqBP p q = true → p = q
    | .db u a, .db v b, h => by
        simp only [beqBP, Bool.and_eq_true] at h
        have huv : u = v := eq_of_beq h.1
        have hab : a = b := beqBT_eq h.2
        subst v
        subst b
        rfl
  private theorem beqBPList_eq : ∀ {xs ys : List BP},
      beqBPList xs ys = true → xs = ys
    | [], [], _ => rfl
    | x :: xs, y :: ys, h => by
        simp only [beqBPList, Bool.and_eq_true] at h
        have hxy : x = y := beqBP_eq h.1
        have hxys : xs = ys := beqBPList_eq h.2
        subst y
        subst ys
        rfl
end

instance : LawfulBEq BT where
  rfl := beqBT_refl _
  eq_of_beq := beqBT_eq

instance : LawfulBEq BP where
  rfl := beqBP_refl _
  eq_of_beq := beqBP_eq

/-- Buchholz の零項。 -/
def BZero : BT := .trm []

/-- principal 項 `D_v a` を通常の項として包む。 -/
def Dprin (v : ℕ∞) (a : BT) : BT := .trm [.db v a]

/- principal リストの辞書式順序と principal 項の順序。 -/
mutual
  def lessBT : BT → BT → Bool
    | .trm as, .trm bs => lessBPList as bs
  def lessBP : BP → BP → Bool
    | .db u a, .db v b => decide (u < v) || (u == v && lessBT a b)
  def lessBPList : List BP → List BP → Bool
    | [], [] => false
    | [], _ :: _ => true
    | _ :: _, [] => false
    | a :: as, b :: bs => lessBP a b || (a == b && lessBPList as bs)
end

/-- Buchholz 項の広義順序。 -/
def leBT (a b : BT) : Bool := lessBT a b || a == b

/-! ## principal 成分分解 -/

/-- `Trm` の principal リストを取り出す。 -/
def untrm : BT → List BP
  | .trm ps => ps

/-- 項を principal 項のリストへ分解する。 -/
def PB (t : BT) : List BT := (untrm t).map (fun p => .trm [p])

/-- principal 成分リストを再合成する。 -/
def SigmaB (ts : List BT) : BT := .trm (ts.flatMap untrm)

end PSS
