import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRouteLedgerTotality [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      routeLedger routeEndpoint consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal triangle routeLedger ->
        Cont routeLedger dyadic routeEndpoint ->
          Cont routeEndpoint windows consumer ->
            PkgSig bundle consumer pkg ->
              UnaryHistory routeLedger ∧ UnaryHistory routeEndpoint ∧ UnaryHistory consumer ∧
                Cont diagonal triangle routeLedger ∧ Cont routeLedger dyadic routeEndpoint ∧
                  Cont routeEndpoint windows consumer ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier diagonalTriangleLedger ledgerDyadicEndpoint endpointWindowsConsumer consumerPkg
  obtain ⟨diagonalUnary, triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    _readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have routeLedgerUnary : UnaryHistory routeLedger :=
    unary_cont_closed diagonalUnary triangleUnary diagonalTriangleLedger
  have routeEndpointUnary : UnaryHistory routeEndpoint :=
    unary_cont_closed routeLedgerUnary dyadicUnary ledgerDyadicEndpoint
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeEndpointUnary windowsUnary endpointWindowsConsumer
  exact
    ⟨routeLedgerUnary, routeEndpointUnary, consumerUnary, diagonalTriangleLedger,
      ledgerDyadicEndpoint, endpointWindowsConsumer, provenancePkg, consumerPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
