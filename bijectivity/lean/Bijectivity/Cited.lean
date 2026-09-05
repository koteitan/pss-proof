import Mathlib.SetTheory.Ordinal.Arithmetic
import Bijectivity.Defs
import «Buchholz-1986».«Buchholz-1986-3.2»
import «Buchholz-rel-ord».«Buchholz-rel-ord-6»

/-!
# 外部引用（順序数側）

原文が **外部文献から引用して用いる** 対象を、ここに隔離して宣言する。
証明はせず `axiom` として置くので、これらに依存する定理は `#print axioms` に
そのまま現れ、何を仮定しているかが機械的に追跡できる。

引用元:
* [Buc1] W. Buchholz, “A new system of proof-theoretic ordinal functions”,
  Annals of Pure and Applied Logic 32 (1986), pp. 195–207 — 評価写像 \(o\)、
  \(\psi_u\)、Lemma 2.1 / 2.2(c) / 2.3(b)。
* [Buc2] W. Buchholz, “Relating ordinals to proofs in a perspicuous way”,
  unpublished — Theorem 1.4(a) / Lemma 1.6。
* [3] p進大好きbot,「変換写像による解析」, 巨大数研究 Wiki ユーザーブログ — 命題 10 / 命題 11。

原文は「表記」節で \(\psi_ua\)、\(D_ua\)、\(G_ua\)、\(o\) を [Buc1] から引くと明記している。

## 🚨 すべての公理は \(OT_{\textrm{B}\omega}\) の上でしか主張していない

`BT` 全体では \(<_{\textrm{B}}\) は**整礎ではない**。実際
`lessBT (Dprin 0 t) (Dprin 0 t') = lessBT t t'` かつ任意の \(t\) に対して
\(D_0t<_{\textrm{B}}D_10\) なので、\(x_0=D_10\)、\(x_{n+1}=D_0x_n\) は
無限降下列である（`isOT_BT (x n) = false` は \(n\geq2\)）。
したがって \(o\) の単調性を `BT` 全体で主張すると順序数の無限降下列が作れて
**公理系が矛盾する**。下の公理はすべて `OT` の仮定を付けてある。

この形の公理系には模型がある: \((OT_{\textrm{B}\omega},<_{\textrm{B}})\) は
[Buc1] により整礎な線形順序なので順序型 \(\gamma\) を持ち、\(o\) をその順序同型
（`OT` の外では \(0\)）、\(\psi_0\psi_\omega0=o(D_0D_\omega0)\) と取ればよい。
`o_addBT` は [Buc1] の加法標準形、`o_iSup_operB` は [Buc2] Theorem 1.4(a) である
（この 2 本は使う場所がすべて \(OT_{\textrm{B}}\)＝\(D_\omega\) を含まない順序数項なので、
仮定もそちらに絞ってある。`o_iSup_operB`＝基本列の共終性は
`Audit-operB.lean` で小さな \(OT_{\textrm{B}}\) プール上を全数検証してある）。
-/

namespace Bijectivity

open PSS

/-- [Buc1] の評価写像 \(o\): Buchholz 項を順序数へ送る。 -/
axiom o : BT → Ordinal.{0}

/-- \(\psi_0\psi_\omega0\)。原文の \(o\circ\textrm{Trans}\) の値域の上界。 -/
axiom psi0psiOmega0 : Ordinal.{0}

/-- \(D_0D_\omega0\)（原文の \(\textrm{Trans}\) の像の上界にあたる項）。 -/
def DzeroDomegaZero : BT := Dprin 0 (Dprin ⊤ (BT.trm []))

/-- [Buc1] Lemma 2.2(c): \(o\) は \(OT_{\textrm{B}\omega}\) 上で
\(<_{\textrm{B}}\) を保つ。

🚨 **`OT` の仮定は落とせない**。`BT` 全体では \(<_{\textrm{B}}\) は整礎ではなく
（\(x_n=D_0^n(D_10)\) が無限降下列: `lessBT (Dprin 0 t) (Dprin 0 t') = lessBT t t'`
かつ任意の \(t\) に対し \(D_0t<_{\textrm{B}}D_10\)）、制限を外すと順序数の
無限降下列が作れてしまって公理系が矛盾する。原文の \(o\) も [Buc1] の
\(OT_{\textrm{B}\omega}\) 上の写像である。 -/
axiom o_lt_of_lessBT {s t : BT} (hs : s ∈ OT) (ht : t ∈ OT) :
    lessBT s t = true → o s < o t

/-- \(o(D_0D_\omega0)=\psi_0\psi_\omega0\)。 -/
axiom o_DzeroDomegaZero : o DzeroDomegaZero = psi0psiOmega0

/-- \(o(0)=0\)。 -/
axiom o_BZero : o BZero = 0

/-- \(o(D_00)=1\)。 -/
axiom o_DzeroZero : o (Dprin 0 BZero) = 1

/-- [Buc1] の加法標準形: \(o\) は項の加法を順序数の加法に写す。

`addBT s t ∈ OT`（＝連結が降順のまま）も要る。これを落とすと
`s = D_00`, `t = D_10` で `addBT s t` が順序数項でなくなり、`o` の値が
どの模型でも決まらない。 -/
axiom o_addBT {s t : BT} (hs : s ∈ OT_B) (ht : t ∈ OT_B) (hst : addBT s t ∈ OT_B) :
    o (addBT s t) = o s + o t

/-- [Buc1] Lemma 2.2(c): \(o\) は \((OT_{\textrm{B}\omega},<_{\textrm{B}})\) から
順序数への同型。ここでは**初期切片への全射性**の形で使う。 -/
axiom o_surj_below {t₀ : BT} (h₀ : t₀ ∈ OT) {α : Ordinal} (h : α < o t₀) :
    ∃ t : BT, t ∈ OT ∧ lessBT t t₀ = true ∧ o t = α

/-- [Buc2] Theorem 1.4(a) 及び Lemma 1.6: \(\textrm{dom}(t)=\omega\) のとき
\(t\) の基本列は \(o(t)\) に収束する。 -/
axiom o_iSup_operB {t : BT} (ht : t ∈ OT_B) (h : domTag t = BDom.naturals) :
    ⨆ m : ℕ, o (operB t (numBT m)) = o t

/-! ## `BT` 全体では \(<_{\textrm{B}}\) が整礎でないことの証拠（機械検証） -/

/-- \(x_0=D_10\)、\(x_{n+1}=D_0x_n\)。 -/
def descChain : ℕ → BT
  | 0 => Dprin 1 BZero
  | n + 1 => Dprin 0 (descChain n)

/-- `descChain` は \(<_{\textrm{B}}\) について狭義降下する。したがって
`o_lt_of_lessBT` から `OT` の仮定を落とすと順序数の無限降下列ができてしまう。 -/
private theorem lessBT_Dprin_zero (a b : BT) :
    lessBT (Dprin 0 a) (Dprin 0 b) = lessBT a b := by
  simp [Dprin, lessBT, lessBPList, lessBP]

theorem descChain_lt : ∀ n : ℕ, lessBT (descChain (n + 1)) (descChain n) = true
  | 0 => by decide
  | n + 1 => by
      show lessBT (Dprin 0 (descChain (n + 1))) (Dprin 0 (descChain n)) = true
      rw [lessBT_Dprin_zero]
      exact descChain_lt n

/-- その列は \(n\geq2\) で順序数項から外れる（だから `OT` 上では矛盾しない）。 -/
theorem descChain_not_OT : isOT_BT (descChain 2) = false := by decide

/-- 原文の \(\textrm{dom}(t)=1\)（後続）。 -/
def domIsOne (t : BT) : Prop := domTag t = BDom.zeroOnly

/-- 原文の \(\textrm{dom}(t)=\omega\)。 -/
def domIsOmega (t : BT) : Prop := domTag t = BDom.naturals

end Bijectivity
