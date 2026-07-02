"""r14-B1 notes: proving the [Buc1] citation lemmas (Lemma 3.2a descent /
Lemma 3.3 OT_B-closure) for THIS repo's operB (pss_paper.thy 737-780).

TARGETS (statements exactly matching pss_paper.thy 805-835, names m_buc1_*):
  (a) m_buc1_3_2_OT_B_closed : a:OT_B ==> a~=0 ==> operB a (numBT n) : OT_B
  (b) m_buc1_3_2a_fseq_lt    : a:OT_B ==> a~=0 ==> lessBT (operB a (numBT n)) a
(buc1_2_2_OT_B_wf well-foundedness stays out of scope / external.)

EMPIRICAL (python/_r14_b1_buc1_checks.py, buchholz.py model = A23-fixed (ii)):
  pool = ALL 46948 terms with <=5 D-symbols, indices <=3 (11649 in OT_B).
  DESC 46596/46596, CLOS 46596/46596 (11649 OT_B terms x n in 0..3),
  MONO (3.2b, NO OT hyp) 1421940/1421940, LB (z <= a[z], OT host) 186672/186672,
  DW0LT (D_w 0 < b) 3565/3565, TOWER (increase/OT/G_v-control) 608/608,
  TRI (3.6 sandwich, general z in dom(a)) 6708/6708, NONZERO 67098/67098.

PROOF ARCHITECTURE (mirrors Buchholz 1986 Section 3; [Buc2]-tower adaptation):
  0. b1x_operB_dom_all / b1x_xseq_dom_all: UNCONDITIONAL totality of the whole
     domB/operB/xseq mutual recursion (strong induction on size of the first
     argument; the xseq tower obligation is xseq_dom_TBv_body whose hypothesis
     is exactly the guard of that branch).  Unconditional unfold
     b1x_operB_unfold + per-branch shape lemmas b1x_operB_{D0,Dinf,Dsucc,
     case_i,case_iii,multi}, b1x_domB_{case_iii,Dsucc}.  This subsumes the old
     branch-wise dom lemmas and is reusable downstream.
  1. b1x_descent (= Buchholz 3.2(a), needs only isOT for descP):
     z in domB a UNION NatSet ==> operB a z < a.  Kind-1 case: x_0 = D_w 0 < b
     via head-index bound (b1x_TBv_head_gt + descP chain b1x_descP_last_hd);
     x_{i+1} = b[D_w x_i] < b directly by IH (D_w x_i in T_w always).
     ==> TARGET (b).
  2. b1x_mono (= 3.2(b), no OT): dom a = T_w, z1<z2 in T_w ==> a[z1]<a[z2].
     b1x_lowerbound: z <= a[z] on T_w domains (OT host; head index > w).
  3. G-machinery: b1x_GBT_size (G_u elements are smaller), b1x_GBT_trans
     (x in G_u t ==> G_u x <= G_u t), b1x_GBT_antitone, b1x_GBT_numBT (<= {0}),
     b1x_GBT_multBT, b1x_GBT_TBv_small_empty (z in T_w, w<v ==> G_v z = {}).
  4. b1x_triG z b a := ALL u c. b<=c<=a --> setle (G_u b) (G_u c U G_u z U {0})
     -- the G-part of Buchholz's  b <|_z a  (the <-part is b1x_descent).
     b1x_G_control (=3.4): triG + b<=a + G_u a < a + G_u z < b ==> G_u b < b,
     by minimal-SIZE counterexample choice (uses GBT_size/GBT_trans).
     b1x_triG_addBT / b1x_triG_Dpt (=3.5) via sandwich decompositions
     b1x_sandwich_prefix / b1x_sandwich_Dpt (uses lessBP asymmetry).
  5. b1x_master (=3.6 G-part + 3.3 closure, simultaneous, strong induction on
     size a): TRI: triG z (operB a z) a; CLOS: isOT z & dfree z ==>
     isOT/dfree (operB a z).  Case (ii) tower adaptation (the actual novelty
     vs the 1986 paper, whose (ii) is the unmodified one-step form):
       T1  strict increase x_i < x_{i+1}: base x_0 < D_w x_0 <= b[D_w x_0]
           (lowerbound); step via mono.  NOTE x_i < D_w x_i is FALSE in
           general for i>=1 (e.g. dom(b)=T_w via D_5 c, x_1 = D_5(...) >
           D_w x_1) -- the increase must go through mono, not through the
           naive z <= D_w z chain.
       TI  tower G-invariant: for x_i <= c' <= b:
           setle (G_u x_i) ({c'} U G_u c' U {0}).  The insert c' is the key:
           Buchholz's outer c_0 absorbs the tower elements (x_i <= x_n <= c_0).
       CL  x_i in OT, dfree, G_v x_i < x_i: z_i = D_w x_i in OT needs
           G_w x_i <= G_v x_i (antitone, v<=w); step by 3.4 with
           G_v z_i = {x_i} U G_v x_i < x_{i+1} (T1 + CL(i)).
     Case (iii) closure needs G_v z < b[z]: dom(b)=N ==> G_v z <= {0} and
     b[z] ~= 0 (b1x_operB_NatSet_nonzero); dom(b)=T_w', w'<v ==> G_v z = {}
     (b1x_GBT_TBv_small_empty).  ==> TARGET (a).

ISABELLE PITFALLS HIT (for future rounds):
  - blast with a quantified transitivity fact (leBT_trans/lessBT_trans in the
    `using ... by blast` style) DIVERGES (>500 s) when goal/facts are the
    leBT disjunctions.  Fix: explicit leBT_trans[OF a b] / helper lemmas
    b1x_le_less_trans, b1x_less_le_trans.  Two builds lost to this.
  - simp cannot evaluate the operB/domB if-guards from negated hypotheses:
    v ~= oo gets normalized to (EX i. v = enat i) and then `v = oo` cannot
    rewrite; ~(EX u. ...) similar.  Fix: turn each guard into an explicit
    equation ((v = oo) = False) etc. and simp add those.
  - order.le_less_trans (locale-qualified) does not resolve; use the global
    le_less_trans / less_le_trans with the chained-fact ORDER matching the
    premise order.
"""
