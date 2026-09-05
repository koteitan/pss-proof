import Bijectivity.Cited
import PSS.Trans
import «Buchholz-rel-ord».«Buchholz-rel-ord-6»

/-!
# 補題（基本列の関係）

原文: 任意の \(M\in ST_{\textrm{PS}}\) と \(m\in\mathbb{N}\) に対して、
\(\textrm{dom}(\textrm{Trans}(M))=\omega\) ならばある \(n\in\mathbb{N}_+\) が存在して
\(\textrm{Trans}(M)[m]\leq_{\textrm{B}}\textrm{Trans}(M[n])\) である。

**本ファイルが本形式化に残る唯一の未証明命題**である。これが証明されると
`17`（基本列の収束性）→ `21`（変換写像の順序数への全単射性）→ `22`（ペア数列の解析）
→ `23`（主定理の全射性）が順に閉じる（帰着はすべて証明済み）。

## 原文の証明の構造

\(M\) が単項のとき、\(t_1=0\) なら \(M=((0,0),(1,0))\) か \(M=((0,0),(1,1))\) の
2 例を直接計算する。\(t_1\neq0\) なら条件 (I)–(VI) で場合分けし、それぞれ [1] の
交換関係を引く。\(M\) が複項のときは \(P(M)_{J_1}\) へ帰着する。

## 必要な [1] の交換関係と、その現状

| 条件 | 原文が引く結論 | Lean | Isabelle |
|---|---|---|---|
| (I) | (1) \(\textrm{Trans}(M[n])=\textrm{Trans}(M)[n-1]\) | **済** `8/8.1-Trans-fseq-condI.lean` の `p_8_1_Trans_fseq_condI` | `scx_condI_exchange1` |
| (II) | (2) \(m_n\geq0\Rightarrow\textrm{Trans}(M[n])=\textrm{Trans}(M)[m_n]\) | **未** | `y3j_p_8_3_condII_exchange_2` (`8/Support_8_C.thy`:15272) |
| (III)/(IV) | (3) \(\textrm{Trans}(M)[n-1]<_{\textrm{B}}\textrm{Trans}(M[n+1])\) | **未** | `p_8_4_Trans_oper_exchange` (`8/P_8_4_Trans_oper_exchange.thy`:262) の第 2 結論 |
| (V) | (3) \(\textrm{Trans}(M)[m_n]\leq_{\textrm{B}}\textrm{Trans}(M[n+1])\) | **未** | `8/P_8_5_Trans_oper_exchange.thy`:51 |
| (VI) | (2) \(m_n\geq0\Rightarrow\textrm{Trans}(M[n])=\textrm{Trans}(M)[m_n]\) | **未** | `d6x_exchange2_condVI` (`8/Support_8_B.thy`:44850) |

Lean 側の §8 は停止性に必要な**降下側だけ**を移植しており（`8/8.3-Trans-fseq-condII.lean`
の MODELLING NOTE）、条件 (I) 以外は結論 (1)–(3) が deferred のままである。
`8/8.7-fseq-descend.lean` の `FseqDesc_exchI`〜`exchVI` は無条件に証明済みだが
向きが逆（\(\textrm{Trans}(M[n])\leq\textrm{Trans}(M)[k]\)）なので本命題には使えない。

## 残作業

1. 上表の 4 本を Isabelle から移植する。
2. `8/8.7-fseq-descend.lean` の `m_8_7_fseq_descend_dispatcher` と同じ形の
   **共終性版ディスパッチャ**（複項の \(P\) ブロック帰着＋条件 (I)–(VI) の場合分け）を書く。
3. `operB` の単調性（Isabelle `8/Support_8_C.thy`:11926
   `leBT (operB a (numBT m)) (operB a (numBT n))`）も併せて要る。
-/

namespace Bijectivity

open PSS

/-- 原文の補題（基本列の関係）。 -/
theorem fseq_relation {M : PS} (hM : STPS M) (m : ℕ)
    (hdom : domIsOmega (PSS.Trans M)) :
    ∃ n : ℕ, 1 ≤ n ∧ leBT (operB (PSS.Trans M) (numBT m)) (PSS.Trans (oper M n)) = true := by
  sorry

end Bijectivity
