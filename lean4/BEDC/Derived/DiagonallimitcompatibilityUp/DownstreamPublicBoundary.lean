import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityDownstreamPublicBoundary [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      routeLedger routeEndpoint consumer sealGate terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal triangle routeLedger ->
        Cont routeLedger dyadic routeEndpoint ->
          Cont routeEndpoint windows consumer ->
            Cont consumer readback sealGate ->
              Cont sealGate realSeal terminal ->
                PkgSig bundle terminal pkg ->
                  UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory dyadic ∧
                    UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
                      UnaryHistory routeLedger ∧ UnaryHistory routeEndpoint ∧
                        UnaryHistory consumer ∧ UnaryHistory sealGate ∧ UnaryHistory terminal ∧
                          Cont diagonal triangle routeLedger ∧
                            Cont routeLedger dyadic routeEndpoint ∧
                              Cont routeEndpoint windows consumer ∧
                                Cont consumer readback sealGate ∧
                                  Cont sealGate realSeal terminal ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier diagonalTriangleLedger ledgerDyadicEndpoint endpointWindowsConsumer
    consumerReadbackSealGate sealGateRealTerminal terminalPkg
  obtain ⟨diagonalUnary, triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have routeLedgerUnary : UnaryHistory routeLedger :=
    unary_cont_closed diagonalUnary triangleUnary diagonalTriangleLedger
  have routeEndpointUnary : UnaryHistory routeEndpoint :=
    unary_cont_closed routeLedgerUnary dyadicUnary ledgerDyadicEndpoint
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeEndpointUnary windowsUnary endpointWindowsConsumer
  have sealGateUnary : UnaryHistory sealGate :=
    unary_cont_closed consumerUnary readbackUnary consumerReadbackSealGate
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed sealGateUnary realSealUnary sealGateRealTerminal
  exact
    ⟨diagonalUnary, triangleUnary, dyadicUnary, windowsUnary, readbackUnary, realSealUnary,
      routeLedgerUnary, routeEndpointUnary, consumerUnary, sealGateUnary, terminalUnary,
      diagonalTriangleLedger, ledgerDyadicEndpoint, endpointWindowsConsumer,
      consumerReadbackSealGate, sealGateRealTerminal, provenancePkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
