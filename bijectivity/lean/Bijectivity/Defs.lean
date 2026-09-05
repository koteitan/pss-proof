import PSS.Defs
import PSS.Standard

/-!
# Naruyoko (2022) — 表記

出典: Naruyoko,「ペア数列システムの停止性証明に用いられた変換写像の全単射性」,
巨大数研究 Wiki ユーザーブログ, 2022-07-27.
<https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Naruyoko/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E3%82%B7%E3%82%B9%E3%83%86%E3%83%A0%E3%81%AE%E5%81%9C%E6%AD%A2%E6%80%A7%E8%A8%BC%E6%98%8E%E3%81%AB%E7%94%A8%E3%81%84%E3%82%89%E3%82%8C%E3%81%9F%E5%A4%89%E6%8F%9B%E5%86%99%E5%83%8F%E3%81%AE%E5%85%A8%E5%8D%98%E5%B0%84%E6%80%A7>

原文の「表記」節のうち、この記事で**新たに導入される**もののみを置く。
`T_PS`、`Lng`、`Pred`、`P`、`M[n]`、`ST_PS`、`Trans`、`T_B`、`OT_B` 等は
既存の `PSS` 名前空間のものをそのまま用いる。
-/

namespace Bijectivity

open PSS

/-! ## 辞書式的順序 `<_PS` -/

/-- 原文の \(<_{\textrm{PS}}\)（再帰的定義、逐語形）。

原文は \(T_{\textrm{PS}}^2\) 上で、任意の \(M,N\) に対し \(M<_{\textrm{PS}}N\) を
次のいずれかと同値に定める:

1. \(M_{0,0}<N_{0,0}\)
2. \(M_{0,0}=N_{0,0}\) かつ \(M_{1,0}<N_{1,0}\)
3. \(M_{0,0}=N_{0,0}\) かつ \(M_{1,0}=N_{1,0}\) かつ
   \((M_i)_{i=1}^{\textrm{Lng}(M)-1}<_{\textrm{PS}}(N_i)_{i=1}^{\textrm{Lng}(N)-1}\)

再帰の末尾では空列が現れるため、空列の場合を辞書式順序の規約で補う
（この補い方が原文の系「辞書式的順序が辞書式順序であること」と整合する）。 -/
def ltPS : PS → PS → Prop
  | [], [] => False
  | [], _ :: _ => True
  | _ :: _, [] => False
  | p :: M, q :: N =>
      p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2) ∨ (p.1 = q.1 ∧ p.2 = q.2 ∧ ltPS M N)

@[inherit_doc] infix:50 " <ₚ " => ltPS

/-- 原文の \(\leq_{\textrm{PS}}\)（\(M=N\lor M<_{\textrm{PS}}N\) の略記）。 -/
def lePS (M N : PS) : Prop := M = N ∨ M <ₚ N

@[inherit_doc] infix:50 " ≤ₚ " => lePS

/-! ## 基本列的順序 `<_PS[]` -/

/-- 添字列 `a` に沿った反復展開 \(N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]\)。 -/
def expand (N : PS) : List ℕ → PS
  | [] => N
  | n :: a => expand (oper N n) a

/-- 原文の \(\leq_{\textrm{PS}[]}\): ある \(a\in\mathbb{N}_+^{<\omega}\) が存在して
\(M=N[a_0]\cdots[a_{\textrm{Lng}(a)-1}]\)。 -/
def leExpPS (M N : PS) : Prop :=
  ∃ a : List ℕ, (∀ n ∈ a, 1 ≤ n) ∧ M = expand N a

@[inherit_doc] infix:50 " ≤ₚ[] " => leExpPS

/-- 原文の \(<_{\textrm{PS}[]}\): 上の `a` が空でない場合。 -/
def ltExpPS (M N : PS) : Prop :=
  ∃ a : List ℕ, a ≠ [] ∧ (∀ n ∈ a, 1 ≤ n) ∧ M = expand N a

@[inherit_doc] infix:50 " <ₚ[] " => ltExpPS

/-! ## `CT_PS` -/

/-- 原文の \(CT_{\textrm{PS}}=\{M\mid M\in ST_{\textrm{PS}}\land M_0=(0,0)\}\)。 -/
def CTPS (M : PS) : Prop := STPS M ∧ M.headD (0, 0) = (0, 0)

end Bijectivity
