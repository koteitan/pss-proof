theory Support_7_030
  imports Frontier_7_035
begin

\<comment> \<open>§7.4 monoT interior (A): shift lemmas transJ0/transJm1/entry1 done.\<close>


section \<open>§7.4 monoT-interior identity (2): \<open>transC1 M = transC1 N\<close> (B)\<close>

text \<open>Identity (2): \<open>transC1 M = transC1 N\<close>, where \<open>N = Red(seg M m j\<^sub>1)\<close>.
  \<open>transC1 M = Mark (Pred M) (transJm1 M)\<close> and
  \<open>transC1 N = Mark (Pred N) (transJm1 N)\<close>.  By (A.2) \<open>transJm1 N = transJm1 M - m\<close>;
  the marked indices satisfy \<open>transJm1 M = m + transJm1 N\<close> (the \<open>M\<close>-anchoring
  \<open>m \<le> transJm1 M\<close> holds in the assembly).  Reduce to the \<open>Mark\<close>-on-\<open>Pred\<close>
  index-shift \<open>Mark (Pred N) j = Mark (Pred M) (m + j)\<close> at \<open>j = transJm1 N\<close>,
  empirically exact (repr5: 9 monoT-interior cases, 0 violations).

  This \<open>Mark\<close>-shift is the \<open>Mark\<close> companion of the keystone (a reduced backward
  slice's \<open>Mark\<close> = the parent's \<open>Mark\<close> at the shifted index), itself an
  inductive sub-keystone.  Stated here as an explicit hypothesis \<open>markShift\<close>
  (induction-ready, mirroring how @{thm [source] m_7_4_interior_id1} takes
  \<open>ihPred\<close>), so id2 is a callable green lemma; the assembly discharges
  \<open>markShift\<close> from the strong-induction hypothesis.\<close>

lemma m_7_4_interior_id2:
  assumes MR: "M \<in> RT_PS" and mint: "m < Lng M - 2"
    and leM: "leR M 0 m (Lng M - 1)"
    and hp: "hasParent M 0 (Lng M - 1)"
    and anc0: "m \<le> parent M 0 (Lng M - 1)"
    and j0lt: "parent M 0 (Lng M - 1) < Lng M - 1"
    and mM: "(M, m) \<in> Marked"
    and ancJm1: "m \<le> transJm1 M"
    and markShift: "Mark (Pred (Red (seg M m (Lng M - 1)))) (transJm1 M - m)
                    = Mark (Pred M) (transJm1 M)"
  shows "transC1 M = transC1 (Red (seg M m (Lng M - 1)))"
proof -
  let ?j1 = "Lng M - 1"  let ?N = "Red (seg M m ?j1)"
  \<comment> \<open>(A.2): \<open>transJm1 N = transJm1 M - m\<close>\<close>
  have jm1N: "transJm1 ?N = transJm1 M - m"
    by (rule repr_transJm1_shift[OF mM MR mint leM hp anc0 j0lt])
  \<comment> \<open>unfold both \<open>transC1\<close> and apply the \<open>Mark\<close>-shift\<close>
  have "transC1 ?N = Mark (Pred ?N) (transJm1 ?N)" by (simp add: transC1_def)
  also have "\<dots> = Mark (Pred ?N) (transJm1 M - m)" using jm1N by simp
  also have "\<dots> = Mark (Pred M) (transJm1 M)" by (rule markShift)
  also have "\<dots> = transC1 M" by (simp add: transC1_def)
  finally show ?thesis ..
qed

\<comment> \<open>§7.4 monoT interior (B): id2 green (reduces to the Mark-on-Pred index-shift).\<close>


section \<open>§7.4 monoT-interior identity (3): \<open>transC2 M = transC2 N\<close> (C)\<close>

text \<open>\<open>transC2 M\<close> (the article proposition transcription 1203-1217) references \<open>M\<close> only through six atoms
  — \<open>transJ1 M\<close>, \<open>transJ0 M\<close>, \<open>transV M\<close>, \<open>transT2 M\<close>, \<open>entry M 1 (transJ0 M)\<close>,
  \<open>entry M 1 (transJ1 M)\<close> — and the four predicates \<open>transCondI/III/V/VI M\<close>.
  All correspond to their \<open>N\<close>-counterparts (\<open>N = Red(seg M m j\<^sub>1)\<close>):
  \<^item> \<open>transV/transT2\<close> agree because \<open>transC1 M = transC1 N\<close> (id2, B);
  \<^item> the two row-1 entries agree by (A.3) at the shifted indices
    (\<open>entry N 1 (transJ0 N) = entry M 1 (transJ0 M)\<close> since \<open>transJ0 N = transJ0 M - m\<close>
     and \<open>m + (transJ0 M - m) = transJ0 M\<close> as \<open>m \<le> transJ0 M\<close>;
     \<open>entry N 1 (transJ1 N) = entry M 1 (transJ1 M)\<close> since \<open>transJ1 N = j\<^sub>1 - m\<close>);
  \<^item> the four \<open>transCond\<close> predicates correspond — empirically exact (repr5: 9
    monoT-interior cases, 0 viol).
  Given those, \<open>transC2 M\<close> and \<open>transC2 N\<close> are the SAME \<open>let\<close>-expression, hence
  equal.  Stated with the atom/condition correspondences as explicit hypotheses
  (the structural collapse is unconditional); the \<open>transCond\<close>-correspondence and
  the entry/transV/transT2 facts are discharged in the assembly from (A)/(B).\<close>

lemma m_7_4_interior_id3:
  fixes M N :: pairseq
  assumes c1eq: "transC1 M = transC1 N"
    and ej0:  "entry N 1 (transJ0 N) = entry M 1 (transJ0 M)"
    and ej1:  "entry N 1 (transJ1 N) = entry M 1 (transJ1 M)"
    and cI:   "transCondI N   = transCondI M"
    and cIII: "transCondIII N = transCondIII M"
    and cV:   "transCondV N   = transCondV M"
    and cVI:  "transCondVI N  = transCondVI M"
  shows "transC2 M = transC2 N"
proof -
  \<comment> \<open>\<open>transV/transT2\<close> from \<open>transC1\<close>\<close>
  have vEq: "transV N = transV M" using c1eq by (simp add: transV_def)
  have t2Eq: "transT2 N = transT2 M" using c1eq by (simp add: transT2_def)
  \<comment> \<open>expand both \<open>let\<close>-bodies, then rewrite every composite \<open>N\<close>-atom to its
     \<open>M\<close>-counterpart (\<open>transV/transT2\<close>, the two \<open>entry\<close>s, the four conditions)\<close>
  show ?thesis
    unfolding transC2_def Let_def
    by (simp only: vEq t2Eq ej0 ej1 cI cIII cV cVI)
qed

end
