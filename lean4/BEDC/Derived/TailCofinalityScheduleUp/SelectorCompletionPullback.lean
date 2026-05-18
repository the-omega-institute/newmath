import BEDC.Derived.DiagonalTailSelectorUp
import BEDC.Derived.TailCofinalityScheduleUp

namespace BEDC.Derived.TailCofinalityScheduleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.DiagonalTailSelectorUp

theorem TailCofinalityScheduleCarrier_selector_completion_pullback [AskSetup]
    [PackageSetup]
    {precision window dyadic regseq sealRow transport route provenance localCert endpoint
      selectorBudget selectorRead selectorSeal completionRead completionSeal
      pullback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailCofinalityScheduleCarrier precision window dyadic regseq sealRow transport route
        provenance localCert endpoint bundle pkg →
      DiagonalTailSelectorCarrier selectorBudget precision window dyadic regseq sealRow
        selectorRead selectorSeal transport route provenance localCert bundle pkg →
        Cont selectorBudget window selectorRead →
          Cont selectorRead sealRow selectorSeal →
            Cont dyadic regseq completionRead →
              Cont completionRead sealRow completionSeal →
                Cont selectorSeal completionSeal pullback →
                  PkgSig bundle pullback pkg →
                    UnaryHistory window ∧ UnaryHistory dyadic ∧ UnaryHistory regseq ∧
                      UnaryHistory sealRow ∧ UnaryHistory selectorRead ∧
                        UnaryHistory selectorSeal ∧ UnaryHistory completionRead ∧
                          UnaryHistory completionSeal ∧ UnaryHistory pullback ∧
                            Cont selectorBudget window selectorRead ∧
                              Cont selectorRead sealRow selectorSeal ∧
                                Cont dyadic regseq completionRead ∧
                                  Cont completionRead sealRow completionSeal ∧
                                    Cont selectorSeal completionSeal pullback ∧
                                      PkgSig bundle endpoint pkg ∧
                                        PkgSig bundle pullback pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro schedule selector selectorBudgetWindow selectorSealRoute dyadicRegseqCompletion
    completionSealRoute selectorCompletionPullback pullbackPkg
  obtain ⟨_precisionUnary, windowUnary, dyadicUnary, regseqUnary, sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
    _precisionWindowDyadic, _dyadicRegseqSeal, _sealTransportRoute, _routeProvenanceEndpoint,
    _endpointLocalCert, endpointPkg⟩ := schedule
  obtain ⟨_selectorBudgetUnary, _precisionUnary', _windowUnary', _dyadicUnary',
    _regseqUnary', _sealUnary', selectorReadUnary, _selectorSealUnary, _transportUnary',
    _routeUnary', _provenanceUnary', _localCertUnary', _precisionWindowDyadic',
    _dyadicRegseqSeal', _provenancePkg⟩ := selector
  have selectorSealUnary : UnaryHistory selectorSeal :=
    unary_cont_closed selectorReadUnary sealUnary selectorSealRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed dyadicUnary regseqUnary dyadicRegseqCompletion
  have completionSealUnary : UnaryHistory completionSeal :=
    unary_cont_closed completionReadUnary sealUnary completionSealRoute
  have pullbackUnary : UnaryHistory pullback :=
    unary_cont_closed selectorSealUnary completionSealUnary selectorCompletionPullback
  exact
    ⟨windowUnary, dyadicUnary, regseqUnary, sealUnary, selectorReadUnary, selectorSealUnary,
      completionReadUnary, completionSealUnary, pullbackUnary, selectorBudgetWindow,
      selectorSealRoute, dyadicRegseqCompletion, completionSealRoute,
      selectorCompletionPullback, endpointPkg, pullbackPkg⟩

end BEDC.Derived.TailCofinalityScheduleUp
