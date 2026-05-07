import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SheafBHistCoverNerveLedger_base_change_cover_pullback
    {ambient member overlap route germ sourceMember sourceOverlap sourceGerm : BHist} :
    SheafBHistCoverNerveLedger ambient member overlap route germ ->
      hsame member sourceMember -> hsame overlap sourceOverlap ->
        Cont sourceOverlap route sourceGerm ->
          SheafBHistCoverNerveLedger ambient sourceMember sourceOverlap route sourceGerm ∧
            hsame germ sourceGerm := by
  intro ledger sameMember sameOverlap sourceRow
  have sourceMemberUnary : UnaryHistory sourceMember :=
    unary_transport ledger.right.left sameMember
  have sourceOverlapUnary : UnaryHistory sourceOverlap :=
    unary_transport ledger.right.right.left sameOverlap
  have sourceOverlapMember : hsame sourceOverlap sourceMember :=
    hsame_trans (hsame_symm sameOverlap)
      (hsame_trans ledger.right.right.right.left sameMember)
  have sameGerm : hsame germ sourceGerm :=
    cont_respects_hsame sameOverlap (hsame_refl route) ledger.right.right.right.right sourceRow
  exact And.intro
    (And.intro ledger.left
      (And.intro sourceMemberUnary
        (And.intro sourceOverlapUnary
          (And.intro sourceOverlapMember sourceRow))))
    sameGerm

theorem SheafBHistCoverNerveLedger_refinement_pullback
    {ambient member overlap route germ refinedMember refinedOverlap refinedRoute refinedGerm :
      BHist} :
    SheafBHistCoverNerveLedger ambient member overlap route germ ->
      hsame refinedMember member -> hsame refinedOverlap refinedMember ->
        hsame refinedRoute route -> Cont refinedOverlap refinedRoute refinedGerm ->
          SheafBHistCoverNerveLedger ambient refinedMember refinedOverlap refinedRoute
              refinedGerm ∧
            hsame germ refinedGerm := by
  intro ledger sameMember sameOverlap sameRoute refinedRow
  have refinedMemberUnary : UnaryHistory refinedMember :=
    unary_transport_symm ledger.right.left sameMember
  have refinedOverlapUnary : UnaryHistory refinedOverlap :=
    unary_transport_symm refinedMemberUnary sameOverlap
  have overlapRefinedOverlap : hsame overlap refinedOverlap :=
    hsame_trans ledger.right.right.right.left
      (hsame_trans (hsame_symm sameMember) (hsame_symm sameOverlap))
  have sameGerm : hsame germ refinedGerm :=
    cont_respects_hsame overlapRefinedOverlap (hsame_symm sameRoute)
      ledger.right.right.right.right refinedRow
  exact And.intro
    (And.intro ledger.left
      (And.intro refinedMemberUnary
        (And.intro refinedOverlapUnary
          (And.intro sameOverlap refinedRow))))
    sameGerm

end BEDC.Derived.SheafUp
