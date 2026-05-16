import BEDC.Derived.TailCofinalityScheduleUp

namespace BEDC.Derived.TailCofinalityScheduleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TailCofinalityScheduleCarrier_selector_residue_exhaustion [AskSetup] [PackageSetup]
    {precision budget window dyadic regseq sealRow transport route provenance localCert endpoint
      selectorRead sealRead pullback completionRead agreementRows completionSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailCofinalityScheduleCarrier precision window dyadic regseq sealRow transport route
        provenance localCert endpoint bundle pkg →
      UnaryHistory budget →
        UnaryHistory agreementRows →
          Cont budget window selectorRead →
            Cont selectorRead regseq sealRead →
              Cont sealRead endpoint pullback →
                Cont dyadic agreementRows completionRead →
                  Cont completionRead sealRow completionSeal →
                    PkgSig bundle pullback pkg →
                      PkgSig bundle completionSeal pkg →
                        UnaryHistory budget ∧ UnaryHistory selectorRead ∧
                          UnaryHistory sealRead ∧ UnaryHistory pullback ∧
                            UnaryHistory completionRead ∧ UnaryHistory completionSeal ∧
                              Cont budget window selectorRead ∧
                                Cont selectorRead regseq sealRead ∧
                                  Cont sealRead endpoint pullback ∧
                                    Cont dyadic agreementRows completionRead ∧
                                      Cont completionRead sealRow completionSeal ∧
                                        PkgSig bundle endpoint pkg ∧
                                          PkgSig bundle pullback pkg ∧
                                            PkgSig bundle completionSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory ProbeBundle
  intro carrier budgetUnary agreementRowsUnary budgetWindowSelector selectorRegseqSeal
    sealEndpointPullback dyadicAgreementCompletion completionSealRow completionPullbackPkg
    completionSealPkg
  obtain ⟨_precisionUnary, windowUnary, dyadicUnary, regseqUnary, sealRowUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, endpointUnary,
    _precisionWindowDyadic, _dyadicRegseqSeal, _sealTransportRoute, _routeProvenanceEndpoint,
    _endpointLocalCert, endpointPkg⟩ := carrier
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed budgetUnary windowUnary budgetWindowSelector
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed selectorReadUnary regseqUnary selectorRegseqSeal
  have pullbackUnary : UnaryHistory pullback :=
    unary_cont_closed sealReadUnary endpointUnary sealEndpointPullback
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed dyadicUnary agreementRowsUnary dyadicAgreementCompletion
  have completionSealUnary : UnaryHistory completionSeal :=
    unary_cont_closed completionReadUnary sealRowUnary completionSealRow
  exact
    ⟨budgetUnary, selectorReadUnary, sealReadUnary, pullbackUnary, completionReadUnary,
      completionSealUnary, budgetWindowSelector, selectorRegseqSeal, sealEndpointPullback,
      dyadicAgreementCompletion, completionSealRow, endpointPkg, completionPullbackPkg,
      completionSealPkg⟩

end BEDC.Derived.TailCofinalityScheduleUp
