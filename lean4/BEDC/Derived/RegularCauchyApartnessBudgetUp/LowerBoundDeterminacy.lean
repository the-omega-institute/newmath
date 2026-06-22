import BEDC.Derived.RegularCauchyApartnessBudgetUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyApartnessBudgetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RegularCauchyApartnessBudgetCarrier_lower_bound_determinacy
    {A M W D R E H lowerRead lowerReadPrime readbackRead readbackReadPrime realRead
      realReadPrime : BHist} :
    UnaryHistory A →
      UnaryHistory M →
        UnaryHistory W →
          UnaryHistory D →
            UnaryHistory R →
              UnaryHistory E →
                UnaryHistory H →
                  Cont W D lowerRead →
                    Cont W D lowerReadPrime →
                      Cont lowerRead R readbackRead →
                        Cont lowerReadPrime R readbackReadPrime →
                          Cont readbackRead E realRead →
                            Cont readbackReadPrime E realReadPrime →
                              hsame lowerRead lowerReadPrime ∧
                                hsame readbackRead readbackReadPrime ∧
                                  hsame realRead realReadPrime ∧
                                    UnaryHistory lowerRead ∧
                                      UnaryHistory readbackRead ∧ UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro _apartnessUnary _modulusUnary windowUnary dyadicUnary regularUnary realUnary
    _headerUnary lowerRoute lowerRoutePrime readbackRoute readbackRoutePrime realRoute
    realRoutePrime
  have sameLower : hsame lowerRead lowerReadPrime :=
    cont_deterministic lowerRoute lowerRoutePrime
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed windowUnary dyadicUnary lowerRoute
  have sameReadback : hsame readbackRead readbackReadPrime := by
    cases sameLower
    exact cont_deterministic readbackRoute readbackRoutePrime
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed lowerUnary regularUnary readbackRoute
  have sameReal : hsame realRead realReadPrime := by
    cases sameReadback
    exact cont_deterministic realRoute realRoutePrime
  have realResultUnary : UnaryHistory realRead :=
    unary_cont_closed readbackUnary realUnary realRoute
  exact ⟨sameLower, sameReadback, sameReal, lowerUnary, readbackUnary, realResultUnary⟩

end BEDC.Derived.RegularCauchyApartnessBudgetUp
