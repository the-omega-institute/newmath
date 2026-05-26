import BEDC.Derived.CauchyCriterionUp
import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_completion_uniform_family_downstream_coverage
    [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      uniformIndex uniformWindows uniformSeal uniformTransports uniformRoutes uniformProvenance
      uniformName sharedRead completionRead sealRead : BHist}
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
                Cont ledger realSeal sealRead ->
                  PkgSig bundle sharedRead pkg ->
                    PkgSig bundle completionRead pkg ->
                      PkgSig bundle sealRead pkg ->
                        UnaryHistory sharedRead ∧ UnaryHistory completionRead ∧
                          UnaryHistory sealRead ∧ Cont endpoint uniformSeal sharedRead ∧
                            Cont sharedRead realSeal completionRead ∧
                              Cont ledger realSeal sealRead ∧ hsame realSeal uniformSeal ∧
                                PkgSig bundle completionRead pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier uniformPacket _sameRegseq sameRealSeal endpointUniformShared
    sharedRealCompletion ledgerRealSeal _sharedPkg completionPkg sealPkg
  obtain ⟨_windowUnary, _modulusUnary, _toleranceUnary, ledgerUnary, _regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
    endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
    _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
    _endpointPkg⟩ := carrier
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
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed ledgerUnary realSealUnary ledgerRealSeal
  exact
    ⟨sharedUnary, completionUnary, sealUnary, endpointUniformShared, sharedRealCompletion,
      ledgerRealSeal, sameRealSeal, completionPkg, sealPkg⟩

end BEDC.Derived.CauchyCriterionUp
