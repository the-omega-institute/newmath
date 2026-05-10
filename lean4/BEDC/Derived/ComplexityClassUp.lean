import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.ComplexityClassUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ComplexityClassBoundedAcceptanceCarrier_bounded_acceptance_surface
    {input length acceptor trace modulus budget verdict accepted : BHist} :
    UnaryHistory input -> UnaryHistory length -> UnaryHistory acceptor -> UnaryHistory modulus ->
      Cont input length trace -> Cont acceptor trace budget -> Cont budget modulus verdict ->
        Cont input verdict accepted ->
          UnaryHistory trace ∧ UnaryHistory budget ∧ UnaryHistory verdict ∧
            UnaryHistory accepted ∧ hsame trace (append input length) ∧
              hsame budget (append acceptor trace) ∧ hsame verdict (append budget modulus) ∧
                hsame accepted (append input verdict) := by
  intro inputUnary lengthUnary acceptorUnary modulusUnary traceRow budgetRow verdictRow acceptedRow
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed inputUnary lengthUnary traceRow
  have budgetUnary : UnaryHistory budget :=
    unary_cont_closed acceptorUnary traceUnary budgetRow
  have verdictUnary : UnaryHistory verdict :=
    unary_cont_closed budgetUnary modulusUnary verdictRow
  have acceptedUnary : UnaryHistory accepted :=
    unary_cont_closed inputUnary verdictUnary acceptedRow
  exact
    ⟨traceUnary, budgetUnary, verdictUnary, acceptedUnary, traceRow, budgetRow, verdictRow,
      acceptedRow⟩

end BEDC.Derived.ComplexityClassUp
