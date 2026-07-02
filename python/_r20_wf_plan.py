"""
r20 WFSCOUT — decomposition of [Buc1] Lemma 2.2 (well-foundedness of (OT_B, <)).

TARGET (pss_paper.thy:814, the SOLE remaining external-citation `sorry` that the
whole termination result rests on):

    buc1_2_2_OT_B_wf : wf {(a, b). a : OT_B & b : OT_B & lessBT a b}

The other two external citations are already MECHANIZED (no longer sorry-backed):
    m_buc1_3_2a_fseq_lt        (Lemma 3.2a:  a in OT_B, a != 0 ==> a[n] < a)
    m_buc1_3_2_OT_B_closed     (OT_B closed under a[n])

========================================================================
WHAT BUCHHOLZ 1986 ACTUALLY PROVES  (PDF pp. 200-202, section 2)
========================================================================
The article calls the WF fact "[Buc1] Lemma 2.2", but in the PAPER the numbering
is different; the well-foundedness is a COROLLARY of Buchholz's Lemma 2.2(c):

  Lemma 2.1 (paper): "<" is a linear ordering on T.        [proof: "Straightforward"]
        --> in Isabelle: ALREADY PROVEN as lessBT_irrefl / lessBT_trans /
            lessBT_total (m_7_1_lessBT_linord). Strict LINEAR order on ALL of T.

  o(.) : T -> On   (ordinal value):  o(0)=0 ; o((a0..ak))=o(a0)#..#o(ak)
                                     (natural / Hessenberg sum) ; o(Dv b)=psi_v o(b).

  Lemma 2.2 (paper), for a,c in OT, by induction on length of a:
     (a) o(a) in C_0(eps_{Omega_omega+1})          [o lands in the collapse]
     (b) G_u o(a) = { o(x) : x in G_u a }           [G-norm commutes with o]
     (c) a < c  ==>  o(a) < o(c)                     [o is STRICTLY ORDER-PRESERVING]

  Lemma 2.3 (paper): C_0(eps_{Omega_omega+1}) = { o(x) : x in OT }  [o is ONTO],
                     and ({x in OT : x < a}, <) has order type o(a).

==> WELL-FOUNDEDNESS of (OT,<) (hence of (OT_B,<) since OT_B = OT ∩ T_B ⊆ OT):
    o : OT -> On is a STRICTLY ORDER-PRESERVING map into the ordinals (2.2c).
    The ordinals On are well-ordered.  WF pulls back along an order embedding
    (Isabelle: wf_inv_image + wf_subset).  So (OT,<) is WF, and any subset of a
    WF relation is WF, so (OT_B,<) is WF.

    Classification of the argument (per the task's a/b/c question):
      (a) order-preserving norm into a known-WF structure  <-- THIS ONE (via o).
    NOT a G_u coefficient bound alone, and NOT a purely-impredicative argument at
    the OT level: the impredicativity is hidden inside CONSTRUCTING o / psi and
    proving C_0(eps_{Omega_omega+1}) is a set of ordinals (Lemma 1.x, the psi
    collapsing machinery).  That construction is the genuinely external-grade part.

========================================================================
ISABELLE DECOMPOSITION  (named sub-lemmas; exact statement shapes)
========================================================================
Let  R := {(a, b). a : OT_B & b : OT_B & lessBT a b}.

[PROVEN this round, GREEN, no assumptions]  --- the equivalence backbone ---
  wfsx_downchain_forms_iff :
     (EX f::nat=>BT. ALL i. (f (Suc i), f i) : R)
     <-> (EX f::nat=>BT. (ALL n. f n : OT_B) & (ALL n. lessBT (f (Suc n)) (f n)))
  m_buc1_2_2_chain_iff :
     wf R <-> ~(EX f::nat=>BT. (ALL n. f n : OT_B) & (ALL n. lessBT (f(Suc n)) (f n)))
        [= wf_iff_no_infinite_down_chain specialised to R; SHARP -- both directions]

[PROVEN this round, GREEN]  --- two reduction skeletons ---
  m_buc1_2_2_via_chain :        (task deliverable #2)
     assumes  ~(EX f. (ALL n. f n : OT_B) & (ALL n. lessBT (f(Suc n)) (f n)))
     shows    wf R
  m_buc1_2_2_via_embed :        (faithful mirror of Buchholz 2.2c: pullback along o)
     fixes rankf :: "BT => 'b"  and  R_ord :: "'b rel"
     assumes  wf R_ord
          and  (!!a b. a:OT_B ==> b:OT_B ==> lessBT a b ==> (rankf a, rankf b) : R_ord)
     shows    wf R
        [= wf_inv_image + wf_subset; the residual is "such an order embedding exists"]

[PROVEN this round, GREEN]  --- the exact target, modulo the named residual ---
  m_buc1_2_2_OT_B_wf :
     assumes noDescChain:
             ~(EX f::nat=>BT. (ALL n. f n : OT_B) & (ALL n. lessBT (f(Suc n)) (f n)))
     shows   wf {(a, b). a : OT_B & b : OT_B & lessBT a b}     [EXACT conclusion]
     proof:  by (rule m_buc1_2_2_via_chain[OF noDescChain])

[PROVEN this round, GREEN]  --- trivial base facts a rank argument would use ---
  wfsx_lessBT_Zero_least :  a ~= Trm [] ==> lessBT (Trm []) a   (0 is <-least)
  wfsx_not_lessBT_Zero   :  ~ lessBT a (Trm [])                 (nothing below 0)
  wfsx_Zero_in_OT_B      :  Trm [] : OT_B                       (via e4x_Zero_OT_B)

========================================================================
THE EXACT RESIDUAL (what remains external-grade after this round)
========================================================================
Exactly ONE of the following two EQUIVALENT sharp sub-facts closes buc1_2_2:

  (RES-chain)  ~(EX f::nat=>BT. (ALL n. f n : OT_B)
                                & (ALL n. lessBT (f (Suc n)) (f n)))
        "no infinite strictly-descending <-chain stays inside OT_B"
        <-- combinatorial form; equivalent to wf R by m_buc1_2_2_chain_iff.

  (RES-embed)  EX (rankf::BT=>'b) (R_ord::'b rel).
                  wf R_ord
                  & (ALL a b. a:OT_B --> b:OT_B --> lessBT a b --> (rankf a,rankf b):R_ord)
        "OT_B order-embeds into some well-founded structure"
        <-- Buchholz's actual route: rankf = o (ordinal value), R_ord = (On,<).

Feasibility to discharge in Isabelle/HOL WITHOUT importing an ordinal library:
  Genuinely hard.  (OT_B,<) has order type psi_0(eps_{Omega_omega+1}) (the
  Takeuti-Feferman-Buchholz ordinal); its well-foundedness is proof-theoretically
  strong (not provable in ACA_0; needs Pi^1_1-CA_0-level reflection).  A native
  HOL proof would have to build the psi collapsing functions and their fixed-point
  theory -- a standalone formalization project, which is exactly why [Buc1] is
  cited rather than reproved.  The honest deliverable is the reduction above +
  the sharp named residual; the residual is NOT to be `sorry`-ed but carried as a
  named `assumes`.

EMPIRICAL sanity (python/buchholz.py): "<" validated as a strict linear order on
enumerated OT terms (0 failures), so RES-chain is at least not obviously false on
finite prefixes; genuine WF is an infinitary statement no finite enumeration decides.
"""
