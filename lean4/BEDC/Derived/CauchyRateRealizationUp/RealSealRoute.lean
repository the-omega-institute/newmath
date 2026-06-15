import BEDC.Derived.CauchyRateRealizationUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyRateRealizationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CauchyRateRealizationRealSealRoute
    {p r d s q m e H C P N rateRead windowRead toleranceRead readbackRead modulusRead
      sealRead : BHist} :
    UnaryHistory p →
      UnaryHistory r →
        UnaryHistory s →
          UnaryHistory d →
            UnaryHistory q →
              UnaryHistory m →
                UnaryHistory e →
                  Cont p r rateRead →
                    Cont rateRead s windowRead →
                      Cont windowRead d toleranceRead →
                        Cont toleranceRead q readbackRead →
                          Cont readbackRead m modulusRead →
                            Cont modulusRead e sealRead →
                              UnaryHistory rateRead ∧ UnaryHistory windowRead ∧
                                UnaryHistory toleranceRead ∧ UnaryHistory readbackRead ∧
                                  UnaryHistory modulusRead ∧ UnaryHistory sealRead ∧
                                    Cont p r rateRead ∧ Cont rateRead s windowRead ∧
                                      Cont windowRead d toleranceRead ∧
                                        Cont toleranceRead q readbackRead ∧
                                          Cont readbackRead m modulusRead ∧
                                            Cont modulusRead e sealRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro pUnary rUnary sUnary dUnary qUnary mUnary eUnary rateRoute windowRoute
    toleranceRoute readbackRoute modulusRoute sealRoute
  have rateUnary : UnaryHistory rateRead :=
    unary_cont_closed pUnary rUnary rateRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed rateUnary sUnary windowRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowUnary dUnary toleranceRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed toleranceUnary qUnary readbackRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed readbackUnary mUnary modulusRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed modulusUnary eUnary sealRoute
  exact
    ⟨rateUnary, windowUnary, toleranceUnary, readbackUnary, modulusUnary, sealUnary,
      rateRoute, windowRoute, toleranceRoute, readbackRoute, modulusRoute, sealRoute⟩

end BEDC.Derived.CauchyRateRealizationUp
