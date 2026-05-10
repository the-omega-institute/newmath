import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem SheafBHistCoverNerveLedger_route_hsame_transport
    {ambient member overlap route germ member' overlap' route' germ' : BHist} :
    SheafBHistCoverNerveLedger ambient member overlap route germ ->
      hsame member member' -> hsame overlap overlap' -> hsame route route' ->
        hsame germ germ' ->
          SheafBHistCoverNerveLedger ambient member' overlap' route' germ' ∧
            Cont overlap' route' germ' := by
  intro ledger sameMember sameOverlap sameRoute sameGerm
  cases sameMember
  cases sameOverlap
  cases sameRoute
  cases sameGerm
  exact And.intro ledger ledger.right.right.right.right

end BEDC.Derived.SheafUp
