[← Back](../README.md) | [English](README-en.md) | [Japanese](README.md)

# lean/ — file layout of the Lean 4 port

The Lean 4 version of the termination proof of the pair sequence system.
**One article proposition = one file.** Status: **active** (the main termination theorem
`p_8_7_termination` is already unconditional and `sorry`-free; its `#print axioms` is
`propext / Classical.choice / Quot.sound` only).

## Directory layout

```
lean/
├── lakefile.lean           package definition
├── lean-toolchain          leanprover/lean4:v4.30.0
├── PSS/                     shared layer: definitions + reusable helpers
│   ├── Defs.lean            §5 definitions
│   ├── Mono.lean            monotonicity / IncrFirst
│   ├── Adm.lean             admissibility
│   ├── Red.lean             §6.5 Red reduction
│   ├── Standard.lean        ST_PS / RT_PS
│   ├── Scb.lean             scb (subexpressions)
│   ├── Flat.lean            flattening
│   └── Trans.lean           Trans (translation to Buchholz notation)
├── PSS.lean                 aggregate import of PSS/
├── Buchholz-1986/           [Buc1] definitions and lemmas, split by subsection
├── Buchholz-1987/           the W_v construction from the 1987 paper, §2
├── Buchholz-rel-ord/        unpublished [Buc2], p. 6, Definition 6
├── OTB-well-founded-syntactic/
│                            syntactic well-foundedness proof without ordinal semantics
├── Buchholz-1986.lean
├── Buchholz-1987.lean
├── Buchholz-rel-ord.lean    aggregate imports for the three literature dirs
├── OTB-well-founded-syntactic.lean
│                            aggregate import for the syntactic well-foundedness proof
├── 5/ 6/ 7/ 8/              chapter dirs (one proposition per file)
│                            e.g. 8/8.7-termination.lean (main theorem)
├── 5.lean 6.lean 7.lean 8.lean  per-chapter aggregate imports
├── spec.md                  layout spec
├── step.md                  procedure (definition of "green")
├── task.md                  progress tree
├── memo.md                  design / dead ends
├── kimina.md                how to use the Lean check server
└── workflow.md              wave plan
```

## Scale of the chapter dirs

| chapter | files |
|---|---|
| `5/` | 6 |
| `6/` | 65 |
| `7/` | 32 |
| `8/` | 250 |

More files than propositions because large proofs are decomposed across several files.

## Naming

- File names `<§>.<sub>-<slug>.lean` (e.g. `7.2-scb-unique.lean`, `8.7-termination.lean`).
- Module names are wrapped in guillemets: `«8».«8.7-termination»` (to allow dots and a
  leading digit).
- Literature files use `<source>-<subsection>.lean`, paired with a same-named Japanese
  MathJax `<source>-<subsection>.md`.

## Build & verification

- Full build: `cd lean && lake build` (all `default_target`s).
- But `lake build` only reports `sorry` as a warning. A proposition's green check follows
  [step.md](step.md): `python3 python/check_lean.py <file>` (via the kimina server; rc=0,
  no `sorryAx` in `#print axioms`, and the statement matches the (corrected) article).
