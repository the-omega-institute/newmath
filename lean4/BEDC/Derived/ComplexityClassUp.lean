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

theorem ComplexityClassBoundedAcceptance_carrier
    {input length acceptor modulus trace budget verdict package : BHist} :
    UnaryHistory input -> UnaryHistory length -> UnaryHistory acceptor -> UnaryHistory modulus ->
      Cont input length trace -> Cont length modulus budget -> Cont trace budget verdict ->
        Cont acceptor verdict package ->
          UnaryHistory trace ∧ UnaryHistory budget ∧ UnaryHistory verdict ∧
            UnaryHistory package ∧ hsame trace (append input length) ∧
              hsame budget (append length modulus) ∧ hsame verdict (append trace budget) ∧
                hsame package (append acceptor verdict) := by
  intro inputUnary lengthUnary acceptorUnary modulusUnary
  intro traceRow budgetRow verdictRow packageRow
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed inputUnary lengthUnary traceRow
  have budgetUnary : UnaryHistory budget :=
    unary_cont_closed lengthUnary modulusUnary budgetRow
  have verdictUnary : UnaryHistory verdict :=
    unary_cont_closed traceUnary budgetUnary verdictRow
  have packageUnary : UnaryHistory package :=
    unary_cont_closed acceptorUnary verdictUnary packageRow
  exact
    ⟨traceUnary, budgetUnary, verdictUnary, packageUnary, traceRow, budgetRow, verdictRow,
      packageRow⟩

end BEDC.Derived.ComplexityClassUp
