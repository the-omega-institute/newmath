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

theorem ComplexityClassBoundedAcceptanceCarrier_finite_surface
    {input length acceptor budget trace modulus verdict acceptance : BHist} :
    UnaryHistory input -> UnaryHistory length -> UnaryHistory acceptor -> UnaryHistory modulus ->
      Cont input length budget -> Cont acceptor budget trace -> Cont trace modulus verdict ->
        Cont input verdict acceptance ->
          UnaryHistory budget ∧ UnaryHistory trace ∧ UnaryHistory verdict ∧
            UnaryHistory acceptance ∧ hsame budget (append input length) ∧
              hsame trace (append acceptor budget) ∧ hsame verdict (append trace modulus) ∧
                hsame acceptance (append input verdict) := by
  intro inputUnary lengthUnary acceptorUnary modulusUnary budgetRow traceRow verdictRow
  intro acceptanceRow
  have budgetUnary : UnaryHistory budget :=
    unary_cont_closed inputUnary lengthUnary budgetRow
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed acceptorUnary budgetUnary traceRow
  have verdictUnary : UnaryHistory verdict :=
    unary_cont_closed traceUnary modulusUnary verdictRow
  have acceptanceUnary : UnaryHistory acceptance :=
    unary_cont_closed inputUnary verdictUnary acceptanceRow
  exact
    ⟨budgetUnary, traceUnary, verdictUnary, acceptanceUnary, budgetRow, traceRow, verdictRow,
      acceptanceRow⟩

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

theorem ComplexityClassBoundedSimulation_soundness
    {input length acceptor resource trace budget verdict accepted endpoint : BHist} :
    UnaryHistory input -> UnaryHistory length -> UnaryHistory acceptor -> UnaryHistory resource ->
      Cont input length trace -> Cont acceptor trace budget -> Cont budget resource verdict ->
        Cont input verdict accepted -> Cont accepted resource endpoint ->
          UnaryHistory trace ∧ UnaryHistory budget ∧ UnaryHistory verdict ∧
            UnaryHistory accepted ∧ UnaryHistory endpoint ∧ hsame trace (append input length) ∧
              hsame budget (append acceptor trace) ∧ hsame verdict (append budget resource) ∧
                hsame accepted (append input verdict) ∧
                  hsame endpoint (append accepted resource) := by
  intro inputUnary lengthUnary acceptorUnary resourceUnary traceRow budgetRow verdictRow
    acceptedRow endpointRow
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed inputUnary lengthUnary traceRow
  have budgetUnary : UnaryHistory budget :=
    unary_cont_closed acceptorUnary traceUnary budgetRow
  have verdictUnary : UnaryHistory verdict :=
    unary_cont_closed budgetUnary resourceUnary verdictRow
  have acceptedUnary : UnaryHistory accepted :=
    unary_cont_closed inputUnary verdictUnary acceptedRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed acceptedUnary resourceUnary endpointRow
  exact
    ⟨traceUnary, budgetUnary, verdictUnary, acceptedUnary, endpointUnary, traceRow, budgetRow,
      verdictRow, acceptedRow, endpointRow⟩

theorem ComplexityClassNameCertObligationSurface_public_rows
    {input length acceptor modulus resource trace verdict accepted ledger publicSurface : BHist} :
    UnaryHistory input -> UnaryHistory length -> UnaryHistory acceptor -> UnaryHistory modulus ->
      Cont input length resource -> Cont acceptor resource trace -> Cont trace modulus verdict ->
        Cont input verdict accepted -> Cont accepted trace ledger ->
          Cont ledger modulus publicSurface ->
            UnaryHistory resource ∧ UnaryHistory trace ∧ UnaryHistory verdict ∧
              UnaryHistory accepted ∧ UnaryHistory ledger ∧ UnaryHistory publicSurface ∧
                hsame publicSurface (append ledger modulus) := by
  intro inputUnary lengthUnary acceptorUnary modulusUnary resourceRow traceRow verdictRow acceptedRow
  intro ledgerRow publicSurfaceRow
  have resourceUnary : UnaryHistory resource :=
    unary_cont_closed inputUnary lengthUnary resourceRow
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed acceptorUnary resourceUnary traceRow
  have verdictUnary : UnaryHistory verdict :=
    unary_cont_closed traceUnary modulusUnary verdictRow
  have acceptedUnary : UnaryHistory accepted :=
    unary_cont_closed inputUnary verdictUnary acceptedRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed acceptedUnary traceUnary ledgerRow
  have publicSurfaceUnary : UnaryHistory publicSurface :=
    unary_cont_closed ledgerUnary modulusUnary publicSurfaceRow
  exact
    ⟨resourceUnary, traceUnary, verdictUnary, acceptedUnary, ledgerUnary, publicSurfaceUnary,
      publicSurfaceRow⟩

end BEDC.Derived.ComplexityClassUp
