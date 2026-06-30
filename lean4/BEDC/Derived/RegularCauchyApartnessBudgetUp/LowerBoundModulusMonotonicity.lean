import BEDC.Derived.RegularCauchyApartnessBudgetUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyApartnessBudgetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RegularCauchyApartnessBudgetCarrier_lower_bound_modulus_monotonicity
    {A M M' W W' D R lowerRead refinedLower readbackRead refinedReadback : BHist} :
    UnaryHistory A ->
      UnaryHistory M ->
        UnaryHistory M' ->
          UnaryHistory W ->
            UnaryHistory W' ->
              UnaryHistory D ->
                UnaryHistory R ->
                  Cont W D lowerRead ->
                    Cont W' D refinedLower ->
                      Cont lowerRead R readbackRead ->
                        Cont refinedLower R refinedReadback ->
                          hsame lowerRead refinedLower ->
                            hsame readbackRead refinedReadback ∧
                              UnaryHistory refinedLower ∧ UnaryHistory refinedReadback := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro _apartnessUnary _modulusUnary _refinedModulusUnary _windowUnary refinedWindowUnary
    dyadicUnary regularUnary _lowerRoute refinedLowerRoute readbackRoute
    refinedReadbackRoute sameLower
  have sameReadback : hsame readbackRead refinedReadback := by
    cases sameLower
    exact cont_deterministic readbackRoute refinedReadbackRoute
  have refinedLowerUnary : UnaryHistory refinedLower :=
    unary_cont_closed refinedWindowUnary dyadicUnary refinedLowerRoute
  have refinedReadbackUnary : UnaryHistory refinedReadback :=
    unary_cont_closed refinedLowerUnary regularUnary refinedReadbackRoute
  exact ⟨sameReadback, refinedLowerUnary, refinedReadbackUnary⟩

end BEDC.Derived.RegularCauchyApartnessBudgetUp
