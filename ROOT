session PSS_A = HOL +
  description "
    Termination of the Pair Sequence System (ペア数列システムの停止性).
    Formalization based on P進大好きbot's article on the Googology Wiki.

    LAYER a (stable, pre-built heap; rebuilt only when wip graduates into mechanized):
      pss_defs       formalized definitions of the article (shared)
      pss_paper      faithful transcription of the article's statements (all sorry)
      pss_mechanized own machine-checked proofs discharging those statements
  "
  options [document = false, quick_and_dirty]
  sessions
    "HOL-Library"
  theories
    pss_defs
    pss_paper
    pss_mechanized

session PSS_B in "layerB" = PSS_A +
  description "
    LAYER b (main-agent consolidation; rebuilt once per integration, on top of the
    PSS_A heap so pss_mechanized is NOT reprocessed):
      pss_wip        active work-in-progress, proven this campaign (graduates into mechanized)
  "
  options [document = false, quick_and_dirty]
  theories
    pss_wip

session PSS_C in "layerC" = PSS_B +
  description "
    LAYER c (sub-agent scratch; the ONLY session sub-agents build, on top of the
    PSS_B heap so pss_wip is NOT reprocessed after the first build):
      pss_scratch    this round's in-progress lemmas; results graduate into pss_wip
  "
  options [document = false, quick_and_dirty]
  theories
    pss_scratch
