import BEDC.Derived.RegularCauchyApartnessBudgetUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyApartnessBudgetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RegularCauchyApartnessBudgetCarrier_positive_window_determinacy
    {A M W D R H lowerRead lowerRead' readbackRead readbackRead' : BHist} :
    UnaryHistory A →
      UnaryHistory M →
        UnaryHistory W →
          UnaryHistory D →
            UnaryHistory R →
              UnaryHistory H →
                Cont W D lowerRead →
                  Cont W D lowerRead' →
                    Cont lowerRead R readbackRead →
                      Cont lowerRead' R readbackRead' →
                        hsame lowerRead lowerRead' ∧ hsame readbackRead readbackRead' ∧
                          UnaryHistory lowerRead ∧ UnaryHistory readbackRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro _apartnessUnary _modulusUnary windowUnary dyadicUnary regularUnary _headerUnary
    lowerRoute lowerRoute' readbackRoute readbackRoute'
  have sameLower : hsame lowerRead lowerRead' :=
    cont_deterministic lowerRoute lowerRoute'
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed windowUnary dyadicUnary lowerRoute
  have sameReadback : hsame readbackRead readbackRead' := by
    cases sameLower
    exact cont_deterministic readbackRoute readbackRoute'
  have readbackResultUnary : UnaryHistory readbackRead :=
    unary_cont_closed lowerUnary regularUnary readbackRoute
  exact ⟨sameLower, sameReadback, lowerUnary, readbackResultUnary⟩

end BEDC.Derived.RegularCauchyApartnessBudgetUp
