import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

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

end BEDC.Derived.SheafUp
