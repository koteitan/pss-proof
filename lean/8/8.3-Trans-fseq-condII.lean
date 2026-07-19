import «8».«8.7-termination»

/-!
# §8.3 命題（条件(II)の下での `Trans` と基本列の交換関係）

原文: `tmp/content.md` 3958「命題（条件(II)の下での\(\textrm{Trans}\)と基本列の
交換関係）」(article 3958)。逐語形は `p_8_3_TransCondII_oper_descend`
(`isabelle/pss_paper.thy:1863`)。

## 原文の主張（4 結論）

任意の \(M \in ST_{\textrm{PS}} \cap PT_{\textrm{PS}}\) と \(n \in \mathbb{N}_{+}\)
に対し、\(\textrm{Trans}\) の再帰的定義中に導入した記号を用い
\(L := \textrm{Red}((M_j)_{j=j_{-1}}^{j_1})\) と置くと、\(j_1 > 1\) かつ \(M\) が
条件 (II) を満たすならば、\(P_B(t_2)_{J_1}\) の左端が \(D_{M_{1,j_0}}\) であるか
否かに従って \(m_n := n-1\) または \(m_n := n-2\) と置くと、以下が成り立つ：

- (1) \(m_n = -1\) ならば \(\textrm{Trans}(M[n]) = s_1 D_{M_{1,j_{-1}}} t_2 b_1\)。
- (2) \(m_n \ge 0\) ならば \(\textrm{Trans}(M[n]) = \textrm{Trans}(M)[m_n]\)。
- (3) \(\textrm{Mark}(M[n],j_{-1})
      = D_{M_{1,j_{-1}}}(t_3 + (D_{M_{1,j_0}} t_4) \times (m_n+1))\)。
- (4) \(\textrm{Trans}(M[n]) < \textrm{Trans}(M)\)。

## MODELLING NOTE（Isabelle の注記どおり）

結論 (1)–(3) は `Trans` の再帰の内部局所記号 \(s_1, b_1, t_2, t_3, t_4, c_1,
c_2, v, J_1\) と整数値添字 \(m_n \in \mathbb{N} \cup \{-1\}\) を用いて述べられて
いる。これらは `Trans` / `Mark` が別関数として露出しない量である（§7.3 の
deferred な命題（\(c_1\) と \(c_2\) の大小関係）と同じ事情）ため、機械化では
deferred とし、自己完結する降下結論 (4) のみを転記する（Isabelle 側 `p_8_3_
TransCondII_oper_descend` と同じ扱い）。

`M \in PT_{\textrm{PS}}` は `PT_PS = {M. M ∈ T_PS ∧ monoT M}`
(`pss_defs.thy:240`) で展開する（Lean 側に `PTPS` は無い。`8.7-Pred-oper0` の
先例と同じ）。

## 訂正

- **A36**（§8.3 本命題の基本列 lhs に関する訂正案）は **取り下げ済み**
  (`corrections-old.md:138`)。原文は正しく、著者自身が \(m_n := n-1\) / \(n-2\) の
  場合分けを明示しており、我々の「存在量化が要る」という指摘は再要求だった。
  よって本命題は原文どおりに述べる。
- **A22**（`corrections.md:838`, [軽微]）は「補題（第\(0\)種型基本列の基本
  不等式）」への訂正であって本命題への訂正ではない（対象は `p_8_3_kind0_base_
  ineq`、既に `8.3-kind0-base-ineq` で訂正形を証明済み）。

## 供給（無条件）

本命題 (4) は降下柱 `Trans_fseq_descend`（`8.7-termination`、仮定 0）の**系**で
ある。memo のツリー `8.3-Trans-fseq-condII ⛔8.7-fseq-descend` および 8.3 項目の
記述どおり、dispatcher の条件 (II) 枝そのものであり同じ仮定から出る。降下柱の
条件 (II) 枝の内実は
`CondII_masterCF`（`condII_masterCF_of_condIIIV condIIIVterminalSlice_holds`,
`8.2-condIIIV-close` ＋ `8.3-condII-Boundary-close`）
→ `FseqDesc_exchII_of_CondII` の等式形
→ 降下エンジン `m_8_3_TransCondII_oper_descend_engine`（`8.3-TransCondII-engine`）
＋ 第 0 種型基本列補題群（`8.3-kind0-*`）
の連鎖で、いずれも無条件化済みである。ここではその合流点 `Trans_fseq_descend`
を 1 行で適用する。

## 状態

✅ 無条件（sorry 0、axioms = propext/Classical.choice/Quot.sound）。仮定は原文の
仮定（\(ST_{\textrm{PS}} \cap PT_{\textrm{PS}}\)・\(n \in \mathbb{N}_+\)・\(j_1 > 1\)・
条件 (II)）のみで、残差 `Prop` はゼロ。
-/

namespace PSS

/-- **命題（条件(II)の下での `Trans` と基本列の交換関係）(4)** (§8.3, 原文 3958)。

Isabelle 逐語形 `p_8_3_TransCondII_oper_descend` (`pss_paper.thy:1863`)。
仮定 `hPT : TPS M ∧ monoT M = true` は原文の `M ∈ PT_PS` を
`PT_PS = {M. M ∈ T_PS ∧ monoT M}` で展開したもの。仮定 `hj1 : 1 < Lng M - 1` は
原文の \(j_1 = \textrm{Lng}(M)-1 > 1\)。

結論 (1)–(3) は `Trans` 再帰の内部記号依存で deferred（上の MODELLING NOTE 参照）。
自己完結する降下結論 (4) のみを述べる。無条件な降下柱 `Trans_fseq_descend`
（`8.7-termination`）の系。`hPT`（＝\(M \in PT_{\textrm{PS}}\) の monoT 成分）と
`hCII`（条件 (II)）は原文の仮定として掲げるが、降下柱は全枝を無条件に含むため
本証明では使用しない。 -/
theorem p_8_3_Trans_fseq_condII (M : PS) (n : ℕ)
    (hST : STPS M) (hPT : TPS M ∧ monoT M = true) (hn : 0 < n)
    (hj1 : 1 < Lng M - 1) (hCII : transCondII M = true) :
    lessBT (Trans (oper M n)) (Trans M) = true := by
  have _ := hPT
  have _ := hCII
  exact Trans_fseq_descend M n hST (by omega) (by omega)

#print axioms p_8_3_Trans_fseq_condII

end PSS
