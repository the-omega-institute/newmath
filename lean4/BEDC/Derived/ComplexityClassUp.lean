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

theorem ComplexityClassResourceModulusMonotonicity_budget_transport
    {input length length' acceptor trace trace' modulus budget budget' verdict verdict' accepted
      accepted' : BHist} :
    UnaryHistory input -> UnaryHistory length -> UnaryHistory acceptor -> UnaryHistory modulus ->
      hsame length length' -> Cont input length trace -> Cont input length' trace' ->
        Cont trace modulus budget -> Cont trace' modulus budget' -> Cont acceptor budget verdict ->
          Cont acceptor budget' verdict' -> Cont input verdict accepted ->
            Cont input verdict' accepted' ->
              UnaryHistory length' ∧ UnaryHistory trace' ∧ UnaryHistory budget' ∧
                UnaryHistory verdict' ∧ UnaryHistory accepted' ∧ hsame trace trace' ∧
                  hsame budget budget' ∧ hsame verdict verdict' ∧
                    hsame accepted accepted' := by
  intro inputUnary lengthUnary acceptorUnary modulusUnary sameLength traceRow traceRow'
  intro budgetRow budgetRow' verdictRow verdictRow' acceptedRow acceptedRow'
  have lengthUnary' : UnaryHistory length' :=
    unary_transport lengthUnary sameLength
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed inputUnary lengthUnary traceRow
  have traceUnary' : UnaryHistory trace' :=
    unary_cont_closed inputUnary lengthUnary' traceRow'
  have budgetUnary : UnaryHistory budget :=
    unary_cont_closed traceUnary modulusUnary budgetRow
  have budgetUnary' : UnaryHistory budget' :=
    unary_cont_closed traceUnary' modulusUnary budgetRow'
  have verdictUnary : UnaryHistory verdict :=
    unary_cont_closed acceptorUnary budgetUnary verdictRow
  have verdictUnary' : UnaryHistory verdict' :=
    unary_cont_closed acceptorUnary budgetUnary' verdictRow'
  have acceptedUnary' : UnaryHistory accepted' :=
    unary_cont_closed inputUnary verdictUnary' acceptedRow'
  have traceSame : hsame trace trace' :=
    cont_respects_hsame (hsame_refl input) sameLength traceRow traceRow'
  have budgetSame : hsame budget budget' :=
    cont_respects_hsame traceSame (hsame_refl modulus) budgetRow budgetRow'
  have verdictSame : hsame verdict verdict' :=
    cont_respects_hsame (hsame_refl acceptor) budgetSame verdictRow verdictRow'
  have acceptedSame : hsame accepted accepted' :=
    cont_respects_hsame (hsame_refl input) verdictSame acceptedRow acceptedRow'
  exact
    ⟨lengthUnary', traceUnary', budgetUnary', verdictUnary', acceptedUnary', traceSame,
      budgetSame, verdictSame, acceptedSame⟩

theorem ComplexityClassResourceModulusMonotonicity_bound_enlargement
    {input length length' acceptor budget budget' trace trace' verdict verdict' accepted
      accepted' : BHist} :
    UnaryHistory input -> UnaryHistory length -> UnaryHistory acceptor -> hsame length length' ->
      Cont input length budget -> Cont input length' budget' -> Cont acceptor budget trace ->
        Cont acceptor budget' trace' -> Cont trace budget verdict ->
          Cont trace' budget' verdict' -> Cont input verdict accepted ->
            Cont input verdict' accepted' ->
              UnaryHistory length' ∧ UnaryHistory budget' ∧ UnaryHistory trace' ∧
                UnaryHistory verdict' ∧ UnaryHistory accepted' ∧ hsame budget budget' ∧
                  hsame trace trace' ∧ hsame verdict verdict' ∧ hsame accepted accepted' := by
  intro inputUnary lengthUnary acceptorUnary sameLength budgetRow budgetRow'
  intro traceRow traceRow' verdictRow verdictRow' acceptedRow acceptedRow'
  have lengthUnary' : UnaryHistory length' :=
    unary_transport lengthUnary sameLength
  have budgetUnary : UnaryHistory budget :=
    unary_cont_closed inputUnary lengthUnary budgetRow
  have budgetUnary' : UnaryHistory budget' :=
    unary_cont_closed inputUnary lengthUnary' budgetRow'
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed acceptorUnary budgetUnary traceRow
  have traceUnary' : UnaryHistory trace' :=
    unary_cont_closed acceptorUnary budgetUnary' traceRow'
  have verdictUnary : UnaryHistory verdict :=
    unary_cont_closed traceUnary budgetUnary verdictRow
  have verdictUnary' : UnaryHistory verdict' :=
    unary_cont_closed traceUnary' budgetUnary' verdictRow'
  have acceptedUnary' : UnaryHistory accepted' :=
    unary_cont_closed inputUnary verdictUnary' acceptedRow'
  have sameBudget : hsame budget budget' :=
    cont_respects_hsame (hsame_refl input) sameLength budgetRow budgetRow'
  have sameTrace : hsame trace trace' :=
    cont_respects_hsame (hsame_refl acceptor) sameBudget traceRow traceRow'
  have sameVerdict : hsame verdict verdict' :=
    cont_respects_hsame sameTrace sameBudget verdictRow verdictRow'
  have sameAccepted : hsame accepted accepted' :=
    cont_respects_hsame (hsame_refl input) sameVerdict acceptedRow acceptedRow'
  exact
    ⟨lengthUnary', budgetUnary', traceUnary', verdictUnary', acceptedUnary', sameBudget,
      sameTrace, sameVerdict, sameAccepted⟩

theorem ComplexityClassResourceModulusMonotonicity_bound_transport
    {input length length' acceptor trace trace' modulus modulus' budget budget' verdict verdict'
      accepted accepted' : BHist} :
    UnaryHistory input -> UnaryHistory length -> UnaryHistory acceptor -> UnaryHistory modulus ->
      hsame length length' -> hsame modulus modulus' -> Cont input length trace ->
        Cont input length' trace' -> Cont trace modulus budget ->
          Cont trace' modulus' budget' -> Cont acceptor budget verdict ->
            Cont acceptor budget' verdict' -> Cont input verdict accepted ->
              Cont input verdict' accepted' ->
                UnaryHistory length' ∧ UnaryHistory modulus' ∧ UnaryHistory trace ∧
                  UnaryHistory trace' ∧ UnaryHistory budget ∧ UnaryHistory budget' ∧
                    hsame trace trace' ∧ hsame budget budget' ∧ hsame verdict verdict' ∧
                      hsame accepted accepted' := by
  intro inputUnary lengthUnary acceptorUnary modulusUnary sameLength sameModulus traceRow traceRow'
  intro budgetRow budgetRow' verdictRow verdictRow' acceptedRow acceptedRow'
  have lengthUnary' : UnaryHistory length' :=
    unary_transport lengthUnary sameLength
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport modulusUnary sameModulus
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed inputUnary lengthUnary traceRow
  have traceUnary' : UnaryHistory trace' :=
    unary_cont_closed inputUnary lengthUnary' traceRow'
  have budgetUnary : UnaryHistory budget :=
    unary_cont_closed traceUnary modulusUnary budgetRow
  have budgetUnary' : UnaryHistory budget' :=
    unary_cont_closed traceUnary' modulusUnary' budgetRow'
  have traceSame : hsame trace trace' :=
    cont_respects_hsame (hsame_refl input) sameLength traceRow traceRow'
  have budgetSame : hsame budget budget' :=
    cont_respects_hsame traceSame sameModulus budgetRow budgetRow'
  have verdictSame : hsame verdict verdict' :=
    cont_respects_hsame (hsame_refl acceptor) budgetSame verdictRow verdictRow'
  have acceptedSame : hsame accepted accepted' :=
    cont_respects_hsame (hsame_refl input) verdictSame acceptedRow acceptedRow'
  exact
    ⟨lengthUnary', modulusUnary', traceUnary, traceUnary', budgetUnary, budgetUnary',
      traceSame, budgetSame, verdictSame, acceptedSame⟩

theorem ComplexityClassResourceLedger_membership_exactness
    {left right : List BHist}
    {input length acceptor modulus resource trace verdict accepted ledger publicSurface : BHist} :
    List.Mem input (left ++ right) ->
      (forall x : BHist, List.Mem x left -> UnaryHistory x) ->
        (forall x : BHist, List.Mem x right -> UnaryHistory x) ->
          UnaryHistory length ->
            UnaryHistory acceptor ->
              UnaryHistory modulus ->
                Cont input length resource ->
                  Cont acceptor resource trace ->
                    Cont trace modulus verdict ->
                      Cont input verdict accepted ->
                        Cont accepted trace ledger ->
                          Cont ledger modulus publicSurface ->
                            UnaryHistory input ∧ UnaryHistory resource ∧ UnaryHistory trace ∧
                              UnaryHistory verdict ∧ UnaryHistory accepted ∧ UnaryHistory ledger ∧
                                UnaryHistory publicSurface ∧
                                  hsame resource (append input length) ∧
                                    hsame trace (append acceptor resource) ∧
                                      hsame verdict (append trace modulus) ∧
                                        hsame accepted (append input verdict) ∧
                                          hsame ledger (append accepted trace) ∧
                                            hsame publicSurface (append ledger modulus) := by
  intro inputMem leftCoverage rightCoverage lengthUnary acceptorUnary modulusUnary resourceRow
  intro traceRow verdictRow acceptedRow ledgerRow publicSurfaceRow
  have inputUnary : UnaryHistory input := by
    induction left with
    | nil =>
        exact rightCoverage input inputMem
    | cons head tail ih =>
        cases inputMem with
        | head =>
            exact leftCoverage input (List.Mem.head tail)
        | tail _ tailMem =>
            have tailCoverage : forall x : BHist, List.Mem x tail -> UnaryHistory x := by
              intro x memTail
              exact leftCoverage x (List.Mem.tail head memTail)
            exact ih tailMem tailCoverage
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
    ⟨inputUnary, resourceUnary, traceUnary, verdictUnary, acceptedUnary, ledgerUnary,
      publicSurfaceUnary, resourceRow, traceRow, verdictRow, acceptedRow, ledgerRow,
      publicSurfaceRow⟩

end BEDC.Derived.ComplexityClassUp
