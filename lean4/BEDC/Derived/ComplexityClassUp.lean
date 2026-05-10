import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.ComplexityClassUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ComplexityClassBoundedAcceptanceCarrier_bounded_trace_surface
    {input length modulus acceptor trace verdict resource accepted : BHist} :
    UnaryHistory input -> UnaryHistory length -> UnaryHistory modulus -> UnaryHistory acceptor ->
      Cont input length resource -> Cont acceptor resource trace -> Cont trace modulus verdict ->
        Cont verdict input accepted ->
          UnaryHistory resource ∧ UnaryHistory trace ∧ UnaryHistory verdict ∧
            UnaryHistory accepted ∧ hsame resource (append input length) ∧
              hsame trace (append acceptor resource) ∧ hsame verdict (append trace modulus) ∧
                hsame accepted (append verdict input) := by
  intro inputUnary lengthUnary modulusUnary acceptorUnary resourceRow traceRow verdictRow
    acceptedRow
  have resourceUnary : UnaryHistory resource :=
    unary_cont_closed inputUnary lengthUnary resourceRow
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed acceptorUnary resourceUnary traceRow
  have verdictUnary : UnaryHistory verdict :=
    unary_cont_closed traceUnary modulusUnary verdictRow
  have acceptedUnary : UnaryHistory accepted :=
    unary_cont_closed verdictUnary inputUnary acceptedRow
  exact
    ⟨resourceUnary, traceUnary, verdictUnary, acceptedUnary, resourceRow, traceRow, verdictRow,
      acceptedRow⟩

end BEDC.Derived.ComplexityClassUp
