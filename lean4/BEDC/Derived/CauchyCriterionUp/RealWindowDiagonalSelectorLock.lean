import BEDC.Derived.CauchyCriterionUp
import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_real_window_diagonal_selector_lock [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      uniformIndex uniformWindow uniformModulus uniformTolerance uniformTail uniformSeal
      uniformTransports uniformRoutes uniformProvenance uniformName diagonalSource selectorRead
      uniformRead diagonalRead terminalPacket : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      BEDC.Derived.UniformCauchyCriterionUp.UniformCauchyCriterionPacket uniformIndex
        uniformWindow uniformModulus uniformTolerance uniformTail uniformSeal uniformTransports
        uniformRoutes uniformProvenance uniformName bundle pkg ->
        UnaryHistory diagonalSource ->
          Cont endpoint realSeal selectorRead ->
            Cont uniformTail uniformSeal uniformRead ->
              Cont selectorRead diagonalSource diagonalRead ->
                Cont diagonalRead uniformRead terminalPacket ->
                  PkgSig bundle terminalPacket pkg ->
                    UnaryHistory selectorRead ∧ UnaryHistory uniformRead ∧
                      UnaryHistory diagonalRead ∧ UnaryHistory terminalPacket ∧
                        Cont endpoint realSeal selectorRead ∧
                          Cont uniformTail uniformSeal uniformRead ∧
                            Cont selectorRead diagonalSource diagonalRead ∧
                              Cont diagonalRead uniformRead terminalPacket ∧
                                PkgSig bundle endpoint pkg ∧
                                  PkgSig bundle uniformName pkg ∧
                                    PkgSig bundle terminalPacket pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier uniformPacket diagonalSourceUnary endpointRealSelector uniformTailSealRead
    selectorDiagonalRead diagonalUniformTerminal terminalPkg
  obtain ⟨_windowUnary, _modulusUnary, _toleranceUnary, _ledgerUnary, _regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
    endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
    _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
    endpointPkg⟩ := carrier
  obtain ⟨_uniformIndexUnary, _uniformWindowUnary, _uniformModulusUnary,
    _uniformToleranceUnary, uniformTailUnary, uniformSealUnary, _uniformTransportsUnary,
    _uniformRoutesUnary, _uniformProvenanceUnary, _uniformNameUnary,
    _uniformIndexWindowModulus, _uniformModulusToleranceTail,
    _uniformTailSealTransports, _uniformTransportsRoutesProvenance, uniformNamePkg⟩ :=
    uniformPacket
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed endpointUnary realSealUnary endpointRealSelector
  have uniformReadUnary : UnaryHistory uniformRead :=
    unary_cont_closed uniformTailUnary uniformSealUnary uniformTailSealRead
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed selectorReadUnary diagonalSourceUnary selectorDiagonalRead
  have terminalPacketUnary : UnaryHistory terminalPacket :=
    unary_cont_closed diagonalReadUnary uniformReadUnary diagonalUniformTerminal
  exact
    ⟨selectorReadUnary, uniformReadUnary, diagonalReadUnary, terminalPacketUnary,
      endpointRealSelector, uniformTailSealRead, selectorDiagonalRead, diagonalUniformTerminal,
      endpointPkg, uniformNamePkg, terminalPkg⟩

end BEDC.Derived.CauchyCriterionUp
