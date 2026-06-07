import BEDC.Derived.RegularCauchyProductCriterionUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyProductCriterionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RegularCauchyProductCriterionCarrier_window_budget_exactness
    {A B WA WB D P K R E H C L N leftWindow rightWindow productRead criterionRead
      readbackRead : BHist} :
    UnaryHistory A ->
      UnaryHistory B ->
        UnaryHistory WA ->
          UnaryHistory WB ->
            UnaryHistory D ->
              UnaryHistory P ->
                UnaryHistory K ->
                  UnaryHistory R ->
                  Cont A WA leftWindow ->
                    Cont B WB rightWindow ->
                      Cont D P productRead ->
                        Cont productRead K criterionRead ->
                          Cont criterionRead R readbackRead ->
                            regularCauchyProductCriterionFromEventFlow
                                (regularCauchyProductCriterionToEventFlow
                                  (RegularCauchyProductCriterionUp.mk
                                    A B WA WB D P K R E H C L N)) =
                              some
                                (RegularCauchyProductCriterionUp.mk
                                  A B WA WB D P K R E H C L N) ∧
                              UnaryHistory leftWindow ∧ UnaryHistory rightWindow ∧
                                UnaryHistory productRead ∧ UnaryHistory criterionRead ∧
                                  UnaryHistory readbackRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro leftUnary rightUnary leftWindowUnary rightWindowUnary dyadicUnary productUnary
    criterionUnary readbackUnary leftWindowRoute rightWindowRoute productRoute criterionRoute
    readbackRoute
  have leftWindowReadUnary : UnaryHistory leftWindow :=
    unary_cont_closed leftUnary leftWindowUnary leftWindowRoute
  have rightWindowReadUnary : UnaryHistory rightWindow :=
    unary_cont_closed rightUnary rightWindowUnary rightWindowRoute
  have productReadUnary : UnaryHistory productRead :=
    unary_cont_closed dyadicUnary productUnary productRoute
  have criterionReadUnary : UnaryHistory criterionRead :=
    unary_cont_closed productReadUnary criterionUnary criterionRoute
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed criterionReadUnary readbackUnary readbackRoute
  have roundTrip :
      ∀ x : RegularCauchyProductCriterionUp,
        regularCauchyProductCriterionFromEventFlow
            (regularCauchyProductCriterionToEventFlow x) =
          some x :=
    RegularCauchyProductCriterionTasteGate_single_carrier_alignment.right.left
  exact
    ⟨roundTrip (RegularCauchyProductCriterionUp.mk A B WA WB D P K R E H C L N),
      leftWindowReadUnary, rightWindowReadUnary, productReadUnary, criterionReadUnary,
      readbackReadUnary⟩

end BEDC.Derived.RegularCauchyProductCriterionUp
