import BEDC.Derived.SheafUp
import BEDC.Derived.SheafUp.CoverDescent

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SheafBHistTripleOverlapRouteLedger
    (ambient memberA memberB memberC pairAB triple routeA routeB routeC germA germB germC :
      BHist) : Prop :=
  SheafBHistCoverNerveLedger ambient memberA pairAB routeA germA ∧
    SheafBHistCoverNerveLedger ambient memberB pairAB routeB germB ∧
      Cont pairAB memberC triple ∧ SheafBHistPointGermLedger ambient triple routeC germC ∧
        hsame routeA routeB

theorem SheafBHistCoverNerveLedger_triple_overlap_route_coherence
    {ambient member pairOverlap pairRoute pairGerm tripleOverlap tripleRoute
      tripleGerm : BHist} :
    SheafBHistCoverNerveLedger ambient member pairOverlap pairRoute pairGerm ->
      Cont pairOverlap BHist.Empty tripleOverlap -> hsame pairRoute tripleRoute ->
        Cont tripleOverlap tripleRoute tripleGerm ->
          SheafBHistCoverNerveLedger ambient member tripleOverlap tripleRoute tripleGerm ∧
            hsame tripleOverlap pairOverlap ∧ hsame pairGerm tripleGerm := by
  intro ledger tripleOverlapRow sameRoute tripleRow
  have sameTripleOverlap : hsame tripleOverlap pairOverlap :=
    Iff.mp cont_right_unit_iff tripleOverlapRow
  have tripleOverlapUnary : UnaryHistory tripleOverlap :=
    unary_transport ledger.right.right.left (hsame_symm sameTripleOverlap)
  have sameGerm : hsame pairGerm tripleGerm :=
    cont_respects_hsame (hsame_symm sameTripleOverlap) sameRoute
      ledger.right.right.right.right tripleRow
  exact And.intro
    (And.intro ledger.left
      (And.intro ledger.right.left
        (And.intro tripleOverlapUnary
          (And.intro (hsame_trans sameTripleOverlap ledger.right.right.right.left) tripleRow))))
    (And.intro sameTripleOverlap sameGerm)

theorem SheafBHistTripleOverlapRoute_coherence
    {ambient member pair triple pairRoute pairGerm tripleRoute tripleGerm directRoute
      directGerm : BHist} :
    SheafBHistCoverNerveLedger ambient member pair pairRoute pairGerm ->
      hsame pair triple ->
        Cont triple tripleRoute tripleGerm ->
          Cont member directRoute directGerm ->
            hsame tripleRoute directRoute ->
              SheafBHistPointGermLedger ambient triple tripleRoute tripleGerm ∧
                SheafBHistPointGermLedger ambient member directRoute directGerm ∧
                  hsame tripleGerm directGerm := by
  intro ledger samePairTriple tripleRow directRow sameRoute
  have tripleUnary : UnaryHistory triple :=
    unary_transport ledger.right.right.left samePairTriple
  have tripleLedger :
      SheafBHistPointGermLedger ambient triple tripleRoute tripleGerm :=
    And.intro ledger.left (And.intro tripleUnary tripleRow)
  have directLedger :
      SheafBHistPointGermLedger ambient member directRoute directGerm :=
    And.intro ledger.left (And.intro ledger.right.left directRow)
  have sameTripleMember : hsame triple member :=
    hsame_trans (hsame_symm samePairTriple) ledger.right.right.right.left
  have sameGerm : hsame tripleGerm directGerm :=
    cont_respects_hsame sameTripleMember sameRoute tripleRow directRow
  exact And.intro tripleLedger (And.intro directLedger sameGerm)

theorem SheafBHistTripleOverlapRoute_downstream_exactness
    {ambient member pair triple pairRoute pairGerm tripleRoute tripleGerm directRoute
      directGerm restrictedOpen restrictedGermA restrictedGermB finalOpen finalGermA
      finalGermB : BHist} :
    SheafBHistCoverNerveLedger ambient member pair pairRoute pairGerm ->
      hsame pair triple ->
        Cont triple tripleRoute tripleGerm ->
          Cont member directRoute directGerm ->
            hsame tripleRoute directRoute ->
              hsame triple restrictedOpen ->
                Cont restrictedOpen tripleRoute restrictedGermA ->
                  Cont restrictedOpen directRoute restrictedGermB ->
                    hsame restrictedOpen finalOpen ->
                      Cont finalOpen tripleRoute finalGermA ->
                        Cont finalOpen directRoute finalGermB ->
                          SheafRootFaceRead member pair .coverMembership ∧
                            SheafRootFaceRead pair pairGerm .restrictionRoute ∧
                              SheafBHistPointGermComparison ambient restrictedOpen
                                  tripleRoute restrictedGermA restrictedOpen directRoute
                                  restrictedGermB restrictedOpen ∧
                                SheafBHistPointGermComparison ambient finalOpen tripleRoute
                                    finalGermA finalOpen directRoute finalGermB finalOpen ∧
                                  hsame tripleGerm directGerm ∧
                                    hsame restrictedGermA restrictedGermB ∧
                                      hsame finalGermA finalGermB := by
  intro ledger samePairTriple tripleRow directRow sameRoute sameTripleRestricted
    restrictedA restrictedB sameRestrictedFinal finalA finalB
  have coverRows :=
    SheafRootCoverDescent_carrier_exactness ledger
  have coherence :=
    SheafBHistTripleOverlapRoute_coherence ledger samePairTriple tripleRow directRow sameRoute
  have samePairRestricted : hsame pair restrictedOpen :=
    hsame_trans samePairTriple sameTripleRestricted
  have restrictedUnary : UnaryHistory restrictedOpen :=
    unary_transport ledger.right.right.left samePairRestricted
  have sameRestrictedGerms : hsame restrictedGermA restrictedGermB :=
    cont_respects_hsame (hsame_refl restrictedOpen) sameRoute restrictedA restrictedB
  have restrictedComparison :
      SheafBHistPointGermComparison ambient restrictedOpen tripleRoute restrictedGermA
        restrictedOpen directRoute restrictedGermB restrictedOpen :=
    And.intro ledger.left
      (And.intro restrictedUnary
        (And.intro restrictedUnary
          (And.intro restrictedUnary
            (And.intro (hsame_refl restrictedOpen)
              (And.intro (hsame_refl restrictedOpen)
                (And.intro restrictedA
                  (And.intro restrictedB sameRestrictedGerms)))))))
  have finalUnary : UnaryHistory finalOpen :=
    unary_transport restrictedUnary sameRestrictedFinal
  have sameFinalGerms : hsame finalGermA finalGermB :=
    cont_respects_hsame (hsame_refl finalOpen) sameRoute finalA finalB
  have finalComparison :
      SheafBHistPointGermComparison ambient finalOpen tripleRoute finalGermA finalOpen
        directRoute finalGermB finalOpen :=
    And.intro ledger.left
      (And.intro finalUnary
        (And.intro finalUnary
          (And.intro finalUnary
            (And.intro (hsame_refl finalOpen)
              (And.intro (hsame_refl finalOpen)
                (And.intro finalA
                  (And.intro finalB sameFinalGerms)))))))
  exact And.intro coverRows.left
    (And.intro coverRows.right.left
      (And.intro restrictedComparison
        (And.intro finalComparison
          (And.intro coherence.right.right
            (And.intro sameRestrictedGerms sameFinalGerms)))))

end BEDC.Derived.SheafUp
