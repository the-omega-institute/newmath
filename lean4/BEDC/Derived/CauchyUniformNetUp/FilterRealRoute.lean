import BEDC.Derived.CauchyUniformNetUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyUniformNetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CauchyUniformNetCarrier_filter_real_route
    {I F U W R E H C P N filterRead toleranceRead windowRead readbackRead sealRead : BHist} :
    UnaryHistory I -> UnaryHistory F -> UnaryHistory U -> UnaryHistory W -> UnaryHistory R ->
      UnaryHistory E -> Cont I F filterRead -> Cont filterRead U toleranceRead ->
        Cont toleranceRead W windowRead -> Cont windowRead R readbackRead ->
          Cont readbackRead E sealRead ->
            cauchyUniformNetFromEventFlow
                (cauchyUniformNetToEventFlow (CauchyUniformNetUp.mk I F U W R E H C P N)) =
              some (CauchyUniformNetUp.mk I F U W R E H C P N) ∧
              UnaryHistory filterRead ∧ UnaryHistory toleranceRead ∧ UnaryHistory windowRead ∧
              UnaryHistory readbackRead ∧ UnaryHistory sealRead ∧ Cont I F filterRead ∧
              Cont filterRead U toleranceRead ∧ Cont toleranceRead W windowRead ∧
              Cont windowRead R readbackRead ∧ Cont readbackRead E sealRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro indexUnary filterUnary toleranceUnary windowUnary readbackUnary sealUnary filterRoute
    toleranceRoute windowRoute readbackRoute sealRoute
  have roundTrip :
      cauchyUniformNetFromEventFlow
          (cauchyUniformNetToEventFlow (CauchyUniformNetUp.mk I F U W R E H C P N)) =
        some (CauchyUniformNetUp.mk I F U W R E H C P N) :=
    CauchyUniformNetTasteGate_single_carrier_alignment.right.left
      (CauchyUniformNetUp.mk I F U W R E H C P N)
  have filterReadUnary : UnaryHistory filterRead :=
    unary_cont_closed indexUnary filterUnary filterRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed filterReadUnary toleranceUnary toleranceRoute
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed toleranceReadUnary windowUnary windowRoute
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowReadUnary readbackUnary readbackRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackReadUnary sealUnary sealRoute
  exact ⟨roundTrip, filterReadUnary, toleranceReadUnary, windowReadUnary, readbackReadUnary,
    sealReadUnary, filterRoute, toleranceRoute, windowRoute, readbackRoute, sealRoute⟩

end BEDC.Derived.CauchyUniformNetUp
