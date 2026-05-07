import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SheafRootRouteExactness_membership_transport
    {ambient member overlap route germ nextRoute nextGerm localRoute localGerm : BHist} :
    SheafBHistCoverNerveLedger ambient member overlap route germ ->
      UnaryHistory nextRoute ->
        Cont member nextRoute nextGerm ->
          Cont member localRoute localGerm ->
            hsame nextRoute localRoute ->
              SheafBHistCoverNerveLedger ambient member member nextRoute nextGerm ∧
                SheafBHistPointGermLedger ambient member localRoute localGerm ∧
                  UnaryHistory nextGerm ∧ hsame nextGerm localGerm := by
  intro ledger nextRouteUnary nextRow localRow sameRoute
  have membership :
      SheafBHistCoverNerveLedger ambient member member nextRoute nextGerm ∧
        UnaryHistory nextGerm :=
    SheafRootCoverNerve_membership_exhaustion ledger nextRouteUnary nextRow
  have localLedger : SheafBHistPointGermLedger ambient member localRoute localGerm :=
    And.intro ledger.left (And.intro ledger.right.left localRow)
  have sameGerm : hsame nextGerm localGerm :=
    cont_respects_hsame (hsame_refl member) sameRoute nextRow localRow
  exact And.intro membership.left
    (And.intro localLedger (And.intro membership.right sameGerm))

end BEDC.Derived.SheafUp
