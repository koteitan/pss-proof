import Bijectivity.«16d-condII-fseq-rel»

/-!
# 補題（基本列の関係）

原文: 任意の \(M\in ST_{\textrm{PS}}\) と \(m\in\mathbb{N}\) に対して、
\(\textrm{dom}(\textrm{Trans}(M))=\omega\) ならばある \(n\in\mathbb{N}_+\) が存在して
\(\textrm{Trans}(M)[m]\leq_{\textrm{B}}\textrm{Trans}(M[n])\) である。

## 原文の証明の構成と、その分担

| 原文の段 | Lean |
|---|---|
| \(j_1>0\)（`dom(0)=0`, `dom(D_u0)=Ω_u`） | `one_lt_lng_of_domIsOmega`（`15-successor-fseq`） |
| 単項・\(t_1=0\)（2 例の直接計算） | `mono_fseq_rel` の 条件 (I)/(VI) の `Lng M = 2` 枝（`16b`） |
| 単項・\(t_1\neq0\)（条件 (I)–(VI)） | `mono_fseq_rel`（`16b`） |
| 複項（最終 \(P\) 成分への帰着） | `fseq_relation_of_mono`（`16a`） |

原文が引く [1] の 5 つの交換関係のうち、条件 (I)/(III)/(IV)/(V)/(VI) は
`lean/8/` の無条件版がそのまま使え、条件 (II) は `16d` が
`condII_masterCF_exact_of_tailval` から数え上げを逆に解いて供給する。

## 原文との差

* 複項の場合の末尾の計算は原文では等号 \(\textrm{Trans}(M)[m]=\textrm{Trans}(M[m])\)
  と書かれているが、単項の場合の結論は添字 \(n\) が \(m\) とは限らない \(\leq\) なので、
  正しくは \(\leq_{\textrm{B}}\textrm{Trans}(M[n])\) である（訂正 Y-10）。
* 条件 (V) の非許容枝では [1] の交換関係 (3) が \(m\geq1\) しか与えないので、
  \(m=0\) は `operB` の添字単調性（`16c`、Isabelle `y4_N_mono_le`）を経由する
  （訂正 W-34）。

## 状態

✅ 無条件（`sorry` 0、公理は `propext` / `Classical.choice` / `Quot.sound` のみ）。
-/

namespace Bijectivity

open PSS

/-- 原文の補題（基本列の関係）。 -/
theorem fseq_relation {M : PS} (hM : STPS M) (m : ℕ)
    (hdom : domIsOmega (PSS.Trans M)) :
    ∃ n : ℕ, 1 ≤ n ∧ leBT (operB (PSS.Trans M) (numBT m)) (PSS.Trans (oper M n)) = true :=
  fseq_relation_of_mono (mono_fseq_rel condII_fseq_rel_holds operB_numBT_mono_holds)
    M m hM hdom

#print axioms fseq_relation

end Bijectivity
