import Lake
open Lake DSL

package pss where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"

/-- Shared definitions: the article's §5 formalization (ported from `pss_defs.thy`). -/
@[default_target] lean_lib PSS

/-- §5 定式化 — one file per proposition of chapter 5. -/
@[default_target] lean_lib «5» where
  srcDir := "."
  globs := #[Glob.andSubmodules `«5»]

/-- §6 ペア数列の基本性質 -/
@[default_target] lean_lib «6» where
  srcDir := "."
  globs := #[Glob.andSubmodules `«6»]

/-- §7 Buchholz の表記系への翻訳 -/
@[default_target] lean_lib «7» where
  srcDir := "."
  globs := #[Glob.andSubmodules `«7»]

/-- §8 停止性 -/
@[default_target] lean_lib «8» where
  srcDir := "."
  globs := #[Glob.andSubmodules `«8»]
