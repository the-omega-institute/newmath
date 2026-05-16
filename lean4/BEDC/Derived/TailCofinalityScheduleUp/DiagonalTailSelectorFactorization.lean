import BEDC.Derived.DiagonalTailSelectorUp
import BEDC.Derived.TailCofinalityScheduleUp

namespace BEDC.Derived.TailCofinalityScheduleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TailCofinalityScheduleCarrier_diagonal_tail_selector_factorization [AskSetup]
    [PackageSetup]
    {precision window dyadic regseq sealRow transport route provenance localCert endpoint
      selectorBudget selectorRead selectorSeal factorRead selectorAux selectorCert selectorPkgRow
      selectorName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailCofinalityScheduleCarrier precision window dyadic regseq sealRow transport route
        provenance localCert endpoint bundle pkg →
      BEDC.Derived.DiagonalTailSelectorUp.DiagonalTailSelectorCarrier selectorBudget window
        dyadic selectorRead transport route provenance localCert selectorAux selectorCert
        selectorPkgRow selectorName bundle pkg →
        Cont selectorBudget window selectorRead →
          Cont selectorRead sealRow selectorSeal →
            Cont selectorSeal endpoint factorRead →
              PkgSig bundle factorRead pkg →
                UnaryHistory selectorBudget ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
                  UnaryHistory selectorRead ∧ UnaryHistory selectorSeal ∧
                    UnaryHistory factorRead ∧ Cont selectorBudget window selectorRead ∧
                      Cont selectorRead sealRow selectorSeal ∧ Cont selectorSeal endpoint
                        factorRead ∧ PkgSig bundle endpoint pkg ∧
                          PkgSig bundle factorRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro schedule selector selectorBudgetWindow selectorSealRoute selectorEndpointFactor
    factorPkg
  obtain ⟨_precisionUnary, windowUnary, dyadicUnary, _regseqUnary, sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, endpointUnary,
    _precisionWindowDyadic, _dyadicRegseqSeal, _sealTransportRoute, _routeProvenanceEndpoint,
    _endpointLocalCert, endpointPkg⟩ := schedule
  obtain ⟨selectorBudgetUnary, _windowUnary, _dyadicUnary, selectorReadUnary,
    _transportUnary', _routeUnary', _provenanceUnary', _localCertUnary', _selectorAuxUnary,
    _selectorCertUnary, _selectorPkgRowUnary, _selectorNameUnary, _windowDyadicSelector,
    _transportRouteProvenance, _selectorPkg⟩ := selector
  have selectorSealUnary : UnaryHistory selectorSeal :=
    unary_cont_closed selectorReadUnary sealUnary selectorSealRoute
  have factorReadUnary : UnaryHistory factorRead :=
    unary_cont_closed selectorSealUnary endpointUnary selectorEndpointFactor
  exact
    ⟨selectorBudgetUnary, windowUnary, dyadicUnary, selectorReadUnary, selectorSealUnary,
      factorReadUnary, selectorBudgetWindow, selectorSealRoute, selectorEndpointFactor,
      endpointPkg, factorPkg⟩

end BEDC.Derived.TailCofinalityScheduleUp
