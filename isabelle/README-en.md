[← Back](../README.md) | [English](README-en.md) | [Japanese](README.md)

# isabelle/ — file layout of the Isabelle/HOL formalization

The Isabelle/HOL side of the pair-sequence-system termination proof. **Termination is
proven with zero hypotheses and zero `sorry`**, enforced at build time by an ML audit block.

The reorganization into the same layout as `lean/` (chapter directories, one proposition
per file, a shared `PSS/` layer) is **complete**.

## Directory layout

```
isabelle/
├── ROOT                    session definitions (PSS_A ← PSS_B ← PSS_C)
├── pss_defs.thy            definitions of §4–§6
├── PSS/                    shared layer, 154: cross-chapter helpers
│   ├── Pre_5.thy           material preceding §5
│   ├── Frontier_NNN.thy    numbered shared helpers (148)
│   └── After_5/6/7.thy     nodes exposing the chapter boundaries
├── 5/                      §5: 13 propositions + 1 chapter-local helper
├── 6/                      §6: 55 propositions + 73 chapter-local helpers
├── 7/                      §7: 27 propositions + 51 chapter-local helpers
├── 8/                      §8: 33 propositions + 3 chapter-local helpers + audit
│   ├── P_8_7_termination.thy   the main theorem
│   ├── Support_8_A/B/C.thy     large helpers shared within §8
│   └── audit.thy               ML audit (last theory of PSS_A)
├── pss_paper.thy           transcription of the external reference [Buc1]
├── pss_mechanized.thy      compatibility shim after the relocation
├── layerB/pss_wip.thy      frozen layer
└── layerC/pss_scratch.thy  active layer
```

Naming convention: `P_<section>_<slug>.thy` holds one article proposition together with its
proof, `Support_*.thy` holds helpers used within a single chapter, and
`PSS/Frontier_*.thy` holds helpers used by more than one chapter.

## How helpers are assigned

Each auxiliary lemma is placed mechanically by its **usage-chapter set**: **used
(transitively) by ≥2 chapters → shared `PSS/`**, **by exactly one chapter → that chapter's
directory**. The dependency-DAG analysis (reorg Phase 0, `phase0/REPORT.md`) extracted an
acyclic DAG over 4,353 facts and split it into 2,288 shared and 1,283 chapter-local.

## Sessions

| Session | Directory | Contents | Role |
|---|---|---|---|
| `PSS_A` | `.` | `pss_defs` + `PSS/` + `5/`–`8/` + `pss_paper` + `8/audit` | frozen base |
| `PSS_B` | `layerB` | `pss_wip` | frozen base |
| `PSS_C` | `layerC` | `pss_scratch` | active layer |

`8/audit.thy` is the last theory of `PSS_A`, so **a green `PSS_A` IS the audit passing**:
the build fails with `error` if any termination theorem reaches a `sorry`-carrying statement.

## Build

Full build:

```
cd isabelle && isbman build -d . -v PSS_A PSS_B PSS_C
```

Per round, only the active top layer:

```
cd isabelle && isbman build -d . -v PSS_C
```

Green means exactly one `Finished PSS_C` line, zero lines starting with `***`, and zero
`AUDIT FAILED`.

## The remaining 8 `sorry` (none reachable from the termination proof)

- 3 in `pss_paper.thy` — lemmas cited from the external reference [Buc1] (2.2 / 3.2a / 3.3);
  for 3.2a and 3.3 we additionally have our own proofs `m_buc1_*` under `7/`
- 5 in `8/` — article propositions left unproven. `P_8_1_condI_III_c1_around` is false as
  printed (corrections A20 / A21); the other four are true but unproven
