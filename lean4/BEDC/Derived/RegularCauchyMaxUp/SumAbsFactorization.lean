import BEDC.Derived.RegularCauchyMaxUp.TasteGate
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RegularCauchyMaxUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem RegularCauchyMaxCarrier_sum_abs_factorization
    {A B WA WB DA DB S Delta V T Q R E H C P N sourceRead sumRead absRead scaledRead
      readback : BHist} :
    regularCauchyMaxFields (RegularCauchyMaxUp.mk A B WA WB DA DB S Delta V T Q R E H C P N) =
        [A, B, WA, WB, DA, DB, S, Delta, V, T, Q, R, E, H, C, P, N] →
      UnaryHistory A →
      UnaryHistory B →
      UnaryHistory S →
      UnaryHistory V →
      UnaryHistory Q →
      UnaryHistory R →
      Cont A B sourceRead →
      Cont sourceRead S sumRead →
      Cont sumRead V absRead →
      Cont absRead Q scaledRead →
      Cont scaledRead R readback →
      UnaryHistory sourceRead ∧
        UnaryHistory sumRead ∧
          UnaryHistory absRead ∧
            UnaryHistory scaledRead ∧
              UnaryHistory readback ∧
                Cont A B sourceRead ∧
                  Cont sourceRead S sumRead ∧
                    Cont sumRead V absRead ∧
                      Cont absRead Q scaledRead ∧ Cont scaledRead R readback := by
  -- BEDC touchpoint anchor: BHist Cont
  intro hfields hA hB hS hV hQ hR hSource hSum hAbs hScaled hReadback
  cases hfields
  have hSourceUnary : UnaryHistory sourceRead := unary_cont_closed hA hB hSource
  have hSumUnary : UnaryHistory sumRead := unary_cont_closed hSourceUnary hS hSum
  have hAbsUnary : UnaryHistory absRead := unary_cont_closed hSumUnary hV hAbs
  have hScaledUnary : UnaryHistory scaledRead := unary_cont_closed hAbsUnary hQ hScaled
  have hReadbackUnary : UnaryHistory readback :=
    unary_cont_closed hScaledUnary hR hReadback
  exact
    ⟨hSourceUnary,
      hSumUnary,
      hAbsUnary,
      hScaledUnary,
      hReadbackUnary,
      hSource,
      hSum,
      hAbs,
      hScaled,
      hReadback⟩

end BEDC.Derived.RegularCauchyMaxUp
