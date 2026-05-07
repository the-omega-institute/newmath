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

end BEDC.Derived.SheafUp
