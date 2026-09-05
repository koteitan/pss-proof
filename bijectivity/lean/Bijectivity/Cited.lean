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
-/

namespace Bijectivity

open PSS

/-- [Buc1] の評価写像 \(o\): Buchholz 項を順序数へ送る。 -/
axiom o : BT → Ordinal.{0}

/-- \(\psi_0\psi_\omega0\)。原文の \(o\circ\textrm{Trans}\) の値域の上界。 -/
axiom psi0psiOmega0 : Ordinal.{0}

/-- \(D_0D_\omega0\)（原文の \(\textrm{Trans}\) の像の上界にあたる項）。 -/
def DzeroDomegaZero : BT := Dprin 0 (Dprin ⊤ (BT.trm []))

/-- [Buc1] Lemma 2.2(c): \(o\) は \(<_{\textrm{B}}\) を保つ。 -/
axiom o_lt_of_lessBT {s t : BT} : lessBT s t = true → o s < o t

/-- \(o(D_0D_\omega0)=\psi_0\psi_\omega0\)。 -/
axiom o_DzeroDomegaZero : o DzeroDomegaZero = psi0psiOmega0

/-- \(o(0)=0\)。 -/
axiom o_BZero : o BZero = 0

/-- \(o(D_00)=1\)。 -/
axiom o_DzeroZero : o (Dprin 0 BZero) = 1

/-- [Buc1] の加法標準形: \(o\) は項の加法を順序数の加法に写す。 -/
axiom o_addBT (s t : BT) : o (addBT s t) = o s + o t

/-- [Buc1] Lemma 2.2(c): \(o\) は \((OT_{\textrm{B}\omega},<_{\textrm{B}})\) から
順序数への同型。ここでは**初期切片への全射性**の形で使う。 -/
axiom o_surj_below {t₀ : BT} (h₀ : t₀ ∈ OT) {α : Ordinal} (h : α < o t₀) :
    ∃ t : BT, t ∈ OT ∧ lessBT t t₀ = true ∧ o t = α

/-- [Buc2] Theorem 1.4(a) 及び Lemma 1.6: \(\textrm{dom}(t)=\omega\) のとき
\(t\) の基本列は \(o(t)\) に収束する。 -/
axiom o_iSup_operB {t : BT} (h : domTag t = BDom.naturals) :
    ⨆ m : ℕ, o (operB t (numBT m)) = o t

/-- 原文の \(\textrm{dom}(t)=1\)（後続）。 -/
def domIsOne (t : BT) : Prop := domTag t = BDom.zeroOnly

/-- 原文の \(\textrm{dom}(t)=\omega\)。 -/
def domIsOmega (t : BT) : Prop := domTag t = BDom.naturals

end Bijectivity
