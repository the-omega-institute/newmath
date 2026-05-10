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
