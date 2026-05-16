import BEDC.Derived.CauchyCriterionUp
import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.Derived.UniformCauchyCriterionUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_selector_seal_synchronizer_totality
    [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      uniformIndex uniformWindow uniformModulus uniformTolerance uniformTail uniformSeal
      uniformTransports uniformRoutes uniformProvenance uniformName selectorRead uniformRead
      synchronizer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      UniformCauchyCriterionPacket uniformIndex uniformWindow uniformModulus uniformTolerance
        uniformTail uniformSeal uniformTransports uniformRoutes uniformProvenance uniformName
        bundle pkg ->
        Cont window endpoint selectorRead ->
          Cont uniformTail uniformSeal uniformRead ->
            Cont selectorRead uniformRead synchronizer ->
              PkgSig bundle synchronizer pkg ->
                UnaryHistory selectorRead ∧ UnaryHistory uniformRead ∧
                  UnaryHistory synchronizer ∧ Cont window endpoint selectorRead ∧
                    Cont uniformTail uniformSeal uniformRead ∧
                      Cont selectorRead uniformRead synchronizer ∧
                        PkgSig bundle endpoint pkg ∧ PkgSig bundle uniformName pkg ∧
                          PkgSig bundle synchronizer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier uniform selectorRoute uniformRoute synchronizerRoute synchronizerPkg
  obtain ⟨windowUnary, _modulusUnary, _toleranceUnary, _ledgerUnary, _regseqUnary,
    _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
    endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq, _regseqRealSealTransport,
    _transportLocalCertRoute, _routeProvenanceEndpoint, endpointPkg⟩ := carrier
  obtain ⟨_uniformIndexUnary, _uniformWindowUnary, _uniformModulusUnary,
    _uniformToleranceUnary, uniformTailUnary, uniformSealUnary, _uniformTransportsUnary,
    _uniformRoutesUnary, _uniformProvenanceUnary, _uniformNameUnary, _uniformIndexWindowModulus,
    _uniformModulusToleranceTail, _uniformTailSealTransports,
    _uniformTransportsRoutesProvenance, uniformNamePkg⟩ := uniform
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed windowUnary endpointUnary selectorRoute
  have uniformReadUnary : UnaryHistory uniformRead :=
    unary_cont_closed uniformTailUnary uniformSealUnary uniformRoute
  have synchronizerUnary : UnaryHistory synchronizer :=
    unary_cont_closed selectorUnary uniformReadUnary synchronizerRoute
  exact
    ⟨selectorUnary, uniformReadUnary, synchronizerUnary, selectorRoute, uniformRoute,
      synchronizerRoute, endpointPkg, uniformNamePkg, synchronizerPkg⟩

end BEDC.Derived.CauchyCriterionUp
