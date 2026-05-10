import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.ComplexityClassUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ComplexityClassBoundedAcceptanceCarrier_bounded_surface
    {input length acceptor trace modulus verdict resource package : BHist} :
    UnaryHistory input -> UnaryHistory length -> UnaryHistory acceptor -> UnaryHistory modulus ->
      Cont input length resource -> Cont acceptor resource trace -> Cont trace modulus verdict ->
        Cont input verdict package ->
          UnaryHistory resource ∧ UnaryHistory trace ∧ UnaryHistory verdict ∧
            UnaryHistory package ∧ hsame resource (append input length) ∧
              hsame trace (append acceptor resource) ∧ hsame verdict (append trace modulus) ∧
                hsame package (append input verdict) := by
  intro inputUnary lengthUnary acceptorUnary modulusUnary resourceRow traceRow verdictRow
    packageRow
  have resourceUnary : UnaryHistory resource :=
    unary_cont_closed inputUnary lengthUnary resourceRow
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed acceptorUnary resourceUnary traceRow
  have verdictUnary : UnaryHistory verdict :=
    unary_cont_closed traceUnary modulusUnary verdictRow
  have packageUnary : UnaryHistory package :=
    unary_cont_closed inputUnary verdictUnary packageRow
  exact
    ⟨resourceUnary, traceUnary, verdictUnary, packageUnary, resourceRow, traceRow, verdictRow,
      packageRow⟩

end BEDC.Derived.ComplexityClassUp
