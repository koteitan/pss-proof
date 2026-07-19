[← Back](../README.md) | [English](README-en.md) | [Japanese](README.md)

# isabelle/ — file layout of the Isabelle/HOL formalization

The Isabelle/HOL version of the termination proof of the pair sequence system.
**Termination is proved with zero hypotheses and zero `sorry`** (enforced at build time by
an ML audit block).

> **Status**: being **reorganized** into the same shape as `lean/` (chapter dirs + one
> proposition per file + a shared `PSS/` layer). The layout below is the **target**. The
> exact shared/chapter-local boundary and the session structure are fixed by the dependency
> DAG analysis (reorg Phase 0).

## Directory layout (target)

```
isabelle/
├── ROOT                    session definitions (DAG order: PSS ← §5 ← §6 ← §7 ← §8)
├── PSS/                    shared layer: definitions + cross-chapter helpers (≥2 chapters, ~482)
│   ├── Defs.thy            §4–§6 definitions
│   ├── Seg.thy             seg_* entry_* le0_*
│   ├── Idxsum.thy          idxsum_* oper_* poper_*
│   ├── Mono.thy            monotonicity / IncrFirst
│   ├── Adm.thy             adm_* (admissibility)
│   ├── Red.thy             §6.5 Red reduction
│   ├── Standard.thy        ST_PS / RT_PS
│   ├── Scb.thy             scb_*
│   ├── Buchholz.thy        §7 [Buc1] notation (operB_* domB_* TrMax_* …)
│   └── Trans.thy           Trans (tran* repr_* rnsub_* …)
├── 5/                      §5: 13 propositions (+5 local helpers)
│   ├── p_5_1_parent_exists_1.thy
│   │   …
│   └── p_5_4_F_oper_val.thy
├── 6/                      §6: 55 propositions (+636 local helpers)
├── 7/                      §7: 27 propositions (+199 local helpers)
└── 8/                      §8: 33 propositions + 2,171 local helpers
    ├── p_8_7_termination.thy   proposition (main theorem)
    ├── aux_8_4_corner.thy      local helper (topic-grouped; shared within the chapter)
    │   …
    └── audit.thy               ML audit (build-time check of sorry dependencies)
```

## Helper partition

Each auxiliary lemma is placed mechanically by its **usage-chapter set**: **used
(transitively) by ≥2 chapters → shared `PSS/`**; **used by one chapter → that chapter's
dir**. Of the ~4,400 auxiliary lemmas, ~482 (13%) are shared; the rest are chapter-local
(§8 has the most, 2,171).

## Where chapter-local helpers live

A chapter-local helper stays **inside its own chapter directory**, in one of two ways:

- **used by a single proposition** → inlined in that proposition's file
  `p_<§>_<slug>.thy` (proposition + its private lemmas).
- **shared by several propositions of the chapter** → grouped into a **topic-based local
  helper theory** (the analogue of `lean`'s `8/8.4-corner-core.lean`; an Isabelle-valid
  name such as `aux_8_4_corner.thy`), imported by the proposition files that use it.

Which case applies (inlined vs. its own file) is decided by the intra-chapter usage
(Phase 0 DAG).

## Sessions (ROOT)

Layered along the dependency DAG: `PSS` (shared, frozen) ← `PSS_5` ← `PSS_6` ← `PSS_7` ←
`PSS_8`. Each session is built once, so no frozen heap is reprocessed. The ML audit lives
at the end of the top session's `8/audit.thy`.

## Naming

- File name = proposition name `p_<§>_<slug>.thy` (e.g. `p_8_7_termination.thy`); the
  theory name is the same. Our proofs use `m_<§>_<slug>`; auxiliary lemmas carry a content
  prefix (`seg_`, `idxsum_`, `adm_`, `scb_`, …).
- **Isabelle theory names cannot contain dots or hyphens and cannot start with a digit**,
  so `lean`'s `8.7-termination.lean` becomes `p_8_7_termination.thy` (directory names
  `5/`…`8/` are fine).

## Build

A full build builds the top session (its ancestors `PSS` and §5–§7 build as dependencies):
`cd isabelle && isbman build -d . -v PSS_8`. Green = the target session's `Finished` exactly
one line, zero lines starting with `***`, zero `AUDIT FAILED`.
