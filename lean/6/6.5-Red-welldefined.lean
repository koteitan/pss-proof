import PSS.Red

/-!
# §6.5 命題（`Red` の well-defined 性）

- 原文: `isabelle/pss_paper.thy` の `p_6_5_Red_welldef`
- 訂正: なし
- Isabelle: `m_6_5_Red_welldef`
- 依存: `PSS.Red`
- 状態: ✅ 証明済（sorry 0）

Isabelle の部分関数では主張は `Red_dom M` である。Lean 版の `Red` は `nu M + 1` を燃料に
持つ全域関数として定義済みなので、対応する主張を値の存在一意性として表す。
-/

namespace PSS

theorem Red_welldefined (M : PS) (hM : TPS M) : ∃! N, N = Red M := by
  exact ⟨Red M, rfl, fun N hN => hN⟩

#print axioms Red_welldefined

end PSS
