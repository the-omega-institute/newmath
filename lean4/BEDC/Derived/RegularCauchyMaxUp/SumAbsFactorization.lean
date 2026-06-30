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

theorem RegularCauchyMaxCarrier_real_seal_boundary
    {A B WA WB DA DB S Delta V T Q R E H C P N sourceRead sumRead absRead scaledRead
      readback sealRead : BHist} :
    regularCauchyMaxFields (RegularCauchyMaxUp.mk A B WA WB DA DB S Delta V T Q R E H C P N) =
        [A, B, WA, WB, DA, DB, S, Delta, V, T, Q, R, E, H, C, P, N] →
      UnaryHistory A →
      UnaryHistory B →
      UnaryHistory S →
      UnaryHistory V →
      UnaryHistory Q →
      UnaryHistory R →
      UnaryHistory E →
      Cont A B sourceRead →
      Cont sourceRead S sumRead →
      Cont sumRead V absRead →
      Cont absRead Q scaledRead →
      Cont scaledRead R readback →
      Cont readback E sealRead →
      UnaryHistory readback ∧ UnaryHistory sealRead ∧ Cont readback E sealRead := by
  -- BEDC touchpoint anchor: BHist Cont
  intro hfields hA hB hS hV hQ hR hE hSource hSum hAbs hScaled hReadback hSeal
  have hfactor :=
    RegularCauchyMaxCarrier_sum_abs_factorization
      (A := A) (B := B) (WA := WA) (WB := WB) (DA := DA) (DB := DB) (S := S)
      (Delta := Delta) (V := V) (T := T) (Q := Q) (R := R) (E := E) (H := H)
      (C := C) (P := P) (N := N) (sourceRead := sourceRead) (sumRead := sumRead)
      (absRead := absRead) (scaledRead := scaledRead) (readback := readback)
      hfields hA hB hS hV hQ hR hSource hSum hAbs hScaled hReadback
  have hReadbackUnary : UnaryHistory readback := hfactor.2.2.2.2.1
  have hSealUnary : UnaryHistory sealRead := unary_cont_closed hReadbackUnary hE hSeal
  exact ⟨hReadbackUnary, hSealUnary, hSeal⟩

end BEDC.Derived.RegularCauchyMaxUp
