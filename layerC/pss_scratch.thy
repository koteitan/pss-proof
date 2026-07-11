theory pss_scratch
  imports "PSS_B.pss_wip"
begin

text \<open>LAYER c — sub-agent scratch theory.  Sub-agents add this round's in-progress
  lemmas here and build session PSS_C, which sits on top of the pre-built PSS_B heap
  (pss_wip) so only this file is processed.  Proven lemmas ACCUMULATE here round after
  round; when the file fattens (per-round build minutes), the parent folds the whole
  body down into pss_wip (LAYER b, one-time PSS_B rebuild) and resets this file
  (last fold: 2026-07-11, 78k lines of rounds up to r54).  Topic-level orientation
  for the folded body: grep docs/thy-toc.md (regenerate: python3 tools/make_toc.py).\<close>

end
