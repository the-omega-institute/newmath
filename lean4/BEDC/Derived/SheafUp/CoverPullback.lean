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

theorem SheafBHistCoverNerveLedger_base_change_composition
    {ambient member overlap route germ midMember midOverlap midGerm finalMember finalOverlap
      finalGerm : BHist} :
    SheafBHistCoverNerveLedger ambient member overlap route germ ->
      hsame member midMember -> hsame overlap midOverlap -> Cont midOverlap route midGerm ->
        hsame midMember finalMember -> hsame midOverlap finalOverlap ->
          Cont finalOverlap route finalGerm ->
            SheafBHistCoverNerveLedger ambient finalMember finalOverlap route finalGerm ∧
              hsame germ finalGerm ∧ hsame midGerm finalGerm := by
  intro ledger sameMemberMid sameOverlapMid midRow sameMemberFinal sameOverlapFinal finalRow
  have midPullback :
      SheafBHistCoverNerveLedger ambient midMember midOverlap route midGerm ∧
        hsame germ midGerm :=
    SheafBHistCoverNerveLedger_base_change_cover_pullback
      ledger sameMemberMid sameOverlapMid midRow
  have finalPullback :
      SheafBHistCoverNerveLedger ambient finalMember finalOverlap route finalGerm ∧
        hsame midGerm finalGerm :=
    SheafBHistCoverNerveLedger_base_change_cover_pullback
      midPullback.left sameMemberFinal sameOverlapFinal finalRow
  exact And.intro finalPullback.left
    (And.intro (hsame_trans midPullback.right finalPullback.right) finalPullback.right)

theorem SheafBHistCoverNerveLedger_base_change_cover_pullback_composition
    {ambient member overlap route germ memberMid overlapMid routeMid germMid memberOut
      overlapOut routeOut germOut directGerm : BHist} :
    SheafBHistCoverNerveLedger ambient member overlap route germ ->
      hsame member memberMid -> hsame overlap overlapMid -> hsame route routeMid ->
        Cont overlapMid routeMid germMid ->
          hsame memberMid memberOut -> hsame overlapMid overlapOut ->
            hsame routeMid routeOut -> Cont overlapOut routeOut germOut ->
              Cont overlapOut routeOut directGerm ->
                SheafBHistCoverNerveLedger ambient memberOut overlapOut routeOut directGerm ∧
                  hsame germOut directGerm ∧ hsame germ directGerm := by
  intro ledger sameMemberMid sameOverlapMid sameRouteMid midRow sameMemberOut
    sameOverlapOut sameRouteOut outRow directRow
  have overlapMidMemberMid : hsame overlapMid memberMid :=
    hsame_trans (hsame_symm sameOverlapMid)
      (hsame_trans ledger.right.right.right.left sameMemberMid)
  have midPullback :
      SheafBHistCoverNerveLedger ambient memberMid overlapMid routeMid germMid ∧
        hsame germ germMid :=
    SheafBHistCoverNerveLedger_refinement_pullback ledger (hsame_symm sameMemberMid)
      overlapMidMemberMid (hsame_symm sameRouteMid) midRow
  have overlapOutMemberOut : hsame overlapOut memberOut :=
    hsame_trans (hsame_symm sameOverlapOut)
      (hsame_trans midPullback.left.right.right.right.left sameMemberOut)
  have outPullback :
      SheafBHistCoverNerveLedger ambient memberOut overlapOut routeOut germOut ∧
        hsame germMid germOut :=
    SheafBHistCoverNerveLedger_refinement_pullback midPullback.left
      (hsame_symm sameMemberOut) overlapOutMemberOut (hsame_symm sameRouteOut) outRow
  have sameDirect : hsame germOut directGerm :=
    cont_deterministic outRow directRow
  have directLedger :
      SheafBHistCoverNerveLedger ambient memberOut overlapOut routeOut directGerm :=
    And.intro outPullback.left.left
      (And.intro outPullback.left.right.left
        (And.intro outPullback.left.right.right.left
          (And.intro outPullback.left.right.right.right.left directRow)))
  exact And.intro directLedger
    (And.intro sameDirect
      (hsame_trans midPullback.right (hsame_trans outPullback.right sameDirect)))

end BEDC.Derived.SheafUp
