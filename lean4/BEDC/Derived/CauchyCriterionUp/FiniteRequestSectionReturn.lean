import BEDC.Derived.CauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_finite_request_section_return [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      request returnSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      Cont window endpoint request ->
        Cont request realSeal returnSeal ->
          PkgSig bundle returnSeal pkg ->
            UnaryHistory request ∧ UnaryHistory returnSeal ∧ Cont window endpoint request ∧
              Cont request realSeal returnSeal ∧ PkgSig bundle endpoint pkg ∧
                PkgSig bundle returnSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier windowEndpointRequest requestRealSealReturn returnSealPkg
  rcases carrier with
    ⟨windowUnary, _modulusUnary, _toleranceUnary, _ledgerUnary, _regseqUnary,
      realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
      endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
      _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
      endpointPkg⟩
  have requestUnary : UnaryHistory request :=
    unary_cont_closed windowUnary endpointUnary windowEndpointRequest
  have returnSealUnary : UnaryHistory returnSeal :=
    unary_cont_closed requestUnary realSealUnary requestRealSealReturn
  exact
    ⟨requestUnary, returnSealUnary, windowEndpointRequest, requestRealSealReturn, endpointPkg,
      returnSealPkg⟩

end BEDC.Derived.CauchyCriterionUp
