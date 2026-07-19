[← Back](../README.md) | [English](README-en.md) | [Japanese](README.md)

# isabelle/ — file layout of the Isabelle/HOL formalization

The Isabelle/HOL version of the termination proof of the pair sequence system.
**Termination is proved with zero hypotheses and zero `sorry`** (enforced at build time
by an ML audit block). Status: **done / frozen**.

## Directory layout

```
isabelle/
├── ROOT                    nested session definitions PSS_A ← PSS_B ← PSS_C
├── pss_defs.thy            formalized definitions of §4–§6 (shared)          542 lines
├── pss_paper.thy           article statements only, transcribed as sorry   2,334 lines
├── pss_mechanized.thy      our machine-checked proofs (discharge pss_paper) 65,913 lines
├── layerB/
│   └── pss_wip.thy         earlier campaign's proven body (frozen)         119,055 lines
├── layerC/
│   └── pss_scratch.thy     active top layer + termination finish + ML audit 25,102 lines
├── docs/                   design notes (red-termination, buchholz, thy-toc …)
├── task.md                 progress tree (all ✅)
├── memo.md                 design notes / dead ends
└── agent-workflow.md       sub-agent conventions
```

## Layered sessions (ROOT)

The huge proven body sits in pre-built heaps; only the active top layer is rebuilt each round.

| session | dir | theory | role | green check |
|---|---|---|---|---|
| `PSS_A` | `.` | `pss_defs`＋`pss_paper`＋`pss_mechanized` | frozen base | `Finished PSS_A` |
| `PSS_B` | `layerB` | `pss_wip` | frozen base | `Finished PSS_B` |
| `PSS_C` | `layerC` | `pss_scratch` | active top | `Finished PSS_C` |

Import chain: `pss_defs ← pss_paper ← pss_mechanized ← pss_wip ← pss_scratch`
(the last two imported session-qualified).

## Naming

- `p_<§>_<slug>` = article claims (`pss_paper.thy`); `m_<§>_<slug>` = our proofs
  (`pss_mechanized.thy`).
- Auxiliary lemmas carry a content prefix (`idxsum_`, `poper_`, `seg_`, `adm_`, `scb_`,
  `Lng_`, …).

## Build

See the build section of the root [../README.md](../README.md). Full build:
`cd isabelle && isbman build -d . -v PSS_A PSS_B PSS_C`. Green = `Finished PSS_C` exactly
one line, zero lines starting with `***`, zero `AUDIT FAILED`.

## Planned reorganization (mirror lean/)

Work is planned / in progress to reorganize this layered monolith into the same shape as
`lean/` — chapter dirs `5/ 6/ 7/ 8/` + one proposition per file + a shared `PSS/` layer.
The ~128 propositions and ~4,400 auxiliary lemmas are partitioned mechanically by
usage-chapter set (a helper used by ≥2 chapters → shared `PSS/`; used by one chapter →
chapter-local).
