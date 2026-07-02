#!/usr/bin/env python3
"""r16b-E4 MAP: the §8.7 OT-membership pillar dependency graph, re-mapped onto the
NEW closed-form / [Buc1]-closure basis.  Documentation, not an executable check
(the empirical numbers below come from _r16_e4_check.py / _r16_e4_condv_deep.py).

===================================================================================
GOAL of the OT pillar:   M \in ST_PS  ==>  Trans M \in OT_B         (§8.7,
   補題（Trans が標準形を保つこと）, content.md 6122; article name = "Trans preserves
   standard form" = OT-membership).  This is one of the 3 factors of termination:
      termination = descent (fseq dispatcher)  x  OT-membership (THIS)  x  wf (buc1_2_2).

===================================================================================
(A) THE EXISTING (OUR) REDUCTION -- Pred-recursion skeleton, in FROZEN layerB +
    active layerC.  What still gates isOT(Trans M):
-----------------------------------------------------------------------------------
  m_8_7_Trans_preserves_OT           (layerC 4825)  strong-Lng induction, needs
    |                                                 TWO hypotheses:
    |-- resid   (monoT keystone case)  -- 4-case dispatcher obligation
    |     via  m_8_7_Trans_OT_step_keystone (layerB 38553)
    |          -> m_8_7_OT_keystone_step (layerB 38364)  [4-case, on m_8_2_keystone]
    |             each case reduces to  resid(x,q,ps,r):
    |               R3.newOT : isOT_BP (DB x q)                      [appended principal is OT]
    |               R2.dstep : ps<>[] --> leBT (Dpt x q) (Trm[last ps])
    |               R3.gbt   : GBT-cofinality of the body
    |     STATUS of the pieces (all in place, NOT assembled into resid):
    |       R2.dstep : m_8_7_dstep_wholebody (layerC 1579) GREEN -- reduces dstep to
    |                  the equal-head `tail` (leBT q qb when heads equal), via
    |                  m_8_2_wid_step head-pin + m_8_7_dstep_assemble.
    |                  tail  -> m_8_7_eqhead_tail_from_branch_prefix (layerC 5032)
    |                           reduces to consecutive-branch Trans-prefix descent
    |                           (Trans_take_lessBT).  << shares value residual w/ §8.5 >>
    |       R3.gbt   : m_8_7_gbt_outer_reduce (layerB 8518) GREEN -- reduces to the
    |                  appended principal's own cofinality `appg`.
    |       R3.newOT : NOT reduced to a green brick here (isOT_BP of the appended
    |                  principal = the "newOT" residual).
    |
    |-- multiD  (multiT case)          -- m_8_7_multiD_junction (layerC 5443) GREEN
          reduces multiD to `comple`: leBT (Trans blockJ) (Trans blockJ-1)
          (consecutive P-component Trans descent). << shares value residual w/ surgC >>

  NET (old route): isOT(Trans M) is gated by
      { R3.newOT (appended-principal OT) , R2.tail (equal-head branch descent) ,
        R3.gbt.appg (appended cofinality) , multiD.comple (component descent) }
  i.e. 3 keystone sub-residuals + 1 multiT residual, all value-level Trans facts.
  The deprecated §8.5 keystone route tried to supply these via a netfold bridge
  (r15 N3: uninstantiable in-regime) -- DO NOT re-attempt that bridge.

===================================================================================
(B) THE ARTICLE ROUTE -- generation-rank induction (content.md 6122/6216).  THIS
    front's re-map + green bricks (layerC, r16b-E4 commits 6f7e35a, 5c18470):
-----------------------------------------------------------------------------------
  The article does NOT use the Pred-recursion/keystone at all.  It inducts on the
  ST_PS GENERATION (ST_PS.induct: diag base + oper step) and, for an oper step
  M = N[n] with Trans N \in OT_B (IH), uses the VALUE IDENTITY (art. 6216):

      Trans (N[n])  =  ( Trans N [m_n] ) [0]^k          -- some m_n, k
                    =  ((\x. operB x (numBT 0))^^k) (operB (Trans N) (numBT m_n))

  Then OT-membership flows through the [Buc1] closure ALONE -- no G_B, no descP,
  no newOT:

     m_buc1_3_2_OT_B_closed (layerC 11287, GREEN r14):  a\in OT_B, a<>0_B
                                              ==> operB a (numBT m) \in OT_B.

  NEW GREEN BRICKS (this front) that realise the transport unconditionally:
     e4x_Zero_OT_B                : Trm [] \in OT_B.
     e4x_OT_B_operB_numBT         : a\in OT_B ==> operB a (numBT m) \in OT_B  (NO a<>0_B
                                    side cond; a=0_B via b1x_operB_zero).
     e4x_OT_B_op0_iter            : a\in OT_B ==> [0]^k a \in OT_B  (funpow ind).
     m_8_7_OT_via_exchange_value  : a\in OT_B, b=[0]^k(operB a (numBT m)) ==> b\in OT_B.
     m_8_7_Trans_OT_step_via_exchange : Trans N\in OT_B + EXISTS m k. (value id)
                                        ==> Trans(N[n])\in OT_B.       [the OT STEP]
     m_8_7_Trans_preserves_OT_via_closure : ST_PS.induct capstone --
                                        BASE = m_8_7_Trans_preserves_OT_base,
                                        STEP = the brick above, modulo the SINGLE
                                        hypothesis `stepval` (the value identity for
                                        every ST_PS oper step).

  DISCHARGE/BYPASS TABLE (does the NEW material kill each old gate?):
     old gate            | article route
     --------------------+------------------------------------------------------
     R3.newOT            | BYPASSED (no per-principal isOT_BP obligation at all;
                         |   OT-ness is a closure property, not re-derived per node)
     R2.tail             | BYPASSED (no leBT descent; the [0]^k tower is applied
                         |   to an ALREADY-OT object)
     R3.gbt.appg         | BYPASSED (no GBT-cofinality obligation)
     multiD.comple       | BYPASSED (multiT M = N[n] is just another oper step)
     --------------------+------------------------------------------------------
     NEW single gate     | stepval : the §8.5 exchange VALUE identity
                         |   Trans(N[n]) = [0]^k (operB (Trans N) (numBT m_n)).
                         |   (A28-corrected index; = the descent pillar's own
                         |    operB(Trans N)(numBT k) frame, here EQ not <=.)

  So the article route replaces {newOT, tail, gbt, multiD} by ONE value identity.
  That identity is the genuine open content -- as hard as (and shared with) the
  §8.5 exchange / descent-pillar work; it is NOT discharged by this front.

===================================================================================
(C) PER-BRANCH EMPIRICAL COVERAGE  (python/_r16_e4_check.py, genuine ST_PS pool of
    210 hosts via oper-BFS from diagSeq seeds; buchholz.py OT oracle):
-----------------------------------------------------------------------------------
  isOT(Trans M)      per transC2 branch:  ALL 0-fail --
     condI-adm 19/19, condIII-adm 108/108, condIII-adm-j1eq1 4/4, condV-adm 3/3,
     condVI-adm 44/44, condVI-adm-j1eq1 4/4, condVI-nadm 13/13, multi 11/11,
     t1zero 4/4.
  isOT(Trans(M[n])) per branch (n=1..3): ALL 0-fail --
     condI-adm 57/57, condIII-adm 299/299, condV-adm 9/9, condVI-adm 132/132,
     condVI-nadm 39/39, multi 33/33, t1zero 12/12  (+ the j1eq1 variants).
  => isOT(Trans _) itself is EMPIRICALLY UNIVERSAL on ST_PS (no branch is the
     obstruction to the CONCLUSION -- the obstruction is only the PROOF route).

  The value-identity `stepval` (the op0-tower presentation) coverage, naive small
  window (m in {n-2..n+1}, k<=14/30):
     condV-adm  : 9/9   at (m-n,k)=(0,2)      -- CLEAN (k=2, A28 shift)
     condI-adm  : 57/57 (mixed (0,1)/(-1,0)/(0,2))
     condVI-nadm: 39/39 at (m-n,k)=(-1,0)     -- CLEAN (k=0)
     condIII-adm: 245/299 fit ((0,2)/(0,1)/(0,3)); 54 outside the small window
     condVI-adm : 113/132 fit ((0,2)/(-2,0));   19 outside the small window
  => the op0-tower form of stepval is confirmed for condV/condI/condVI-nadm; the
     condIII-adm / condVI-adm residue needs a WIDER (m,k) or the A28-corrected m_n
     (see _r16_e4_condv_deep.py for the KMAX=30 diagnosis).  NOT a counterexample
     to isOT (which is 0-fail everywhere) -- only to the naive tower presentation.

  DEEP-PROBE SHARPENING (_r16_e4_condv_deep.py, KMAX=30, m in {n-2..n+1}):
     the condIII-adm / condVI-adm residue PERSISTS at k<=30 -- so it is NOT a
     too-small-k artifact.  The residue hosts are long strictly-increasing-then-
     plateau shapes, e.g. row-0 = [3,4,5,6,7,8,9,10] with row-1 = [3,4,5,6,7,7,7,7]
     (condIII-adm) -- for these the op0-tower value id in the tested m-offset window
     {n-2..n+1} has NO fit at ANY k<=30.  CONCLUSION: the open piece of stepval for
     condIII-adm/condVI-adm is an m-INDEX / presentation-FORM question (need m beyond
     n+1, or the A28-corrected m_n, or a genuinely non-op0-tower presentation), NOT a
     k-depth question.  condV-adm/condI-adm/condVI-nadm remain clean (small (m,k)).
     The capstone lemma m_8_7_Trans_preserves_OT_via_closure isolates exactly this as
     its single `stepval` hypothesis -- so it is honest about what is still open.

Re-run: python3 _r16_e4_check.py 200 20260702 4242
        python3 _r16_e4_condv_deep.py 300 11 222 3333
"""
