theory pss_scratch
  imports "PSS_B.pss_wip"
begin

text \<open>LAYER c — sub-agent scratch theory.  Sub-agents add this round's in-progress
  lemmas here and build session PSS_C, which sits on top of the pre-built PSS_B heap
  (pss_wip) so only this file is processed.  When a job is verified green, the parent
  moves the proven lemmas into pss_wip (LAYER b) and rebuilds PSS_B, then resets this
  file to empty for the next round.\<close>

end
