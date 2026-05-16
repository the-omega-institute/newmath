import BEDC.Derived.CauchyCriterionUp
import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_completion_uniform_family_factorization
    [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      uniformIndex uniformWindows uniformSeal uniformTransports uniformRoutes uniformProvenance
      uniformName sharedRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      BEDC.Derived.UniformCauchyCriterionUp.UniformCauchyCriterionPacket uniformIndex
          uniformWindows modulus tolerance ledger uniformSeal uniformTransports uniformRoutes
          uniformProvenance uniformName bundle pkg ->
        hsame regseq uniformIndex ->
          hsame realSeal uniformSeal ->
            Cont endpoint uniformSeal sharedRead ->
              Cont sharedRead realSeal completionRead ->
                PkgSig bundle sharedRead pkg ->
                  PkgSig bundle completionRead pkg ->
                    UnaryHistory endpoint ∧ UnaryHistory sharedRead ∧
                      UnaryHistory completionRead ∧ Cont route provenance endpoint ∧
                        Cont endpoint uniformSeal sharedRead ∧
                          Cont sharedRead realSeal completionRead ∧
                            PkgSig bundle endpoint pkg ∧ PkgSig bundle sharedRead pkg ∧
                              PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier uniformPacket _sameRegseq _sameRealSeal endpointUniformShared
    sharedRealCompletion sharedPkg completionPkg
  obtain ⟨_windowUnary, _modulusUnary, _toleranceUnary, _ledgerUnary, _regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
    endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
    _regseqRealSealTransport, _transportLocalCertRoute, routeProvenanceEndpoint,
    endpointPkg⟩ := carrier
  obtain ⟨_uniformIndexUnary, _uniformWindowsUnary, _uniformModulusUnary,
    _uniformToleranceUnary, _uniformLedgerUnary, uniformSealUnary, _uniformTransportsUnary,
    _uniformRoutesUnary, _uniformProvenanceUnary, _uniformNameUnary,
    _uniformIndexWindowsModulus, _uniformModulusToleranceLedger,
    _uniformLedgerSealTransports, _uniformTransportsRoutesProvenance, _uniformNamePkg⟩ :=
    uniformPacket
  have sharedUnary : UnaryHistory sharedRead :=
    unary_cont_closed endpointUnary uniformSealUnary endpointUniformShared
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed sharedUnary realSealUnary sharedRealCompletion
  exact
    ⟨endpointUnary, sharedUnary, completionUnary, routeProvenanceEndpoint,
      endpointUniformShared, sharedRealCompletion, endpointPkg, sharedPkg, completionPkg⟩

end BEDC.Derived.CauchyCriterionUp
