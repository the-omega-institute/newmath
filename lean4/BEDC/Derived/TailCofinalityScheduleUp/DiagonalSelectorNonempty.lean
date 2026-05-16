import BEDC.Derived.TailCofinalityScheduleUp

namespace BEDC.Derived.TailCofinalityScheduleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TailCofinalityScheduleCarrier_diagonal_selector_nonempty [AskSetup] [PackageSetup]
    {precision window dyadic regseq sealRow transport route provenance localCert endpoint
      selector completion : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailCofinalityScheduleCarrier precision window dyadic regseq sealRow transport route
        provenance localCert endpoint bundle pkg →
      Cont precision endpoint selector →
        Cont selector sealRow completion →
          PkgSig bundle completion pkg →
            UnaryHistory precision ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
              UnaryHistory regseq ∧ UnaryHistory sealRow ∧ UnaryHistory endpoint ∧
                UnaryHistory selector ∧ UnaryHistory completion ∧
                  Cont precision window dyadic ∧ Cont dyadic regseq sealRow ∧
                    Cont route provenance endpoint ∧ Cont precision endpoint selector ∧
                      Cont selector sealRow completion ∧ PkgSig bundle endpoint pkg ∧
                        PkgSig bundle completion pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory TailCofinalityScheduleCarrier
  intro carrier precisionEndpointSelector selectorSealCompletion completionPkg
  obtain ⟨precisionUnary, windowUnary, dyadicUnary, regseqUnary, sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, endpointUnary,
    precisionWindowDyadic, dyadicRegseqSeal, _sealTransportRoute, routeProvenanceEndpoint,
    _endpointLocalCert, endpointPkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed precisionUnary endpointUnary precisionEndpointSelector
  have completionUnary : UnaryHistory completion :=
    unary_cont_closed selectorUnary sealUnary selectorSealCompletion
  exact
    ⟨precisionUnary, windowUnary, dyadicUnary, regseqUnary, sealUnary, endpointUnary,
      selectorUnary, completionUnary, precisionWindowDyadic, dyadicRegseqSeal,
      routeProvenanceEndpoint, precisionEndpointSelector, selectorSealCompletion,
      endpointPkg, completionPkg⟩

end BEDC.Derived.TailCofinalityScheduleUp
