import BEDC.Derived.SheafUp.CoverNerveRouteTransport

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem SheafBHistCoverNerveLedger_restriction_hsame_transport_obligation
    {ambient member overlap route germ member' overlap' route' localRoute localGerm : BHist} :
    SheafBHistCoverNerveLedger ambient member overlap route germ -> hsame member member' ->
      hsame overlap overlap' -> hsame route route' -> Cont member' localRoute localGerm ->
        hsame route' localRoute ->
          SheafBHistCoverNerveLedger ambient member' overlap' route' germ ∧
            SheafBHistPointGermLedger ambient member' localRoute localGerm ∧
              hsame germ localGerm := by
  intro ledger sameMember sameOverlap sameRoute localRow sameLocalRoute
  have transported :
      SheafBHistCoverNerveLedger ambient member' overlap' route' germ ∧
        Cont overlap' route' germ :=
    SheafBHistCoverNerveLedger_route_hsame_transport
      ledger sameMember sameOverlap sameRoute (hsame_refl germ)
  have readback :
      SheafBHistPointGermLedger ambient member' localRoute localGerm ∧
        hsame germ localGerm :=
    SheafBHistCoverNerveLedger_gluing_readback transported.left localRow sameLocalRoute
  exact And.intro transported.left readback

end BEDC.Derived.SheafUp
