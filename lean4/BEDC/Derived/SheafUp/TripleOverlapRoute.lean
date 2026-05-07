import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

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
