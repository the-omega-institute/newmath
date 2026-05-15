import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilitySourceLedger [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic ledger ->
        PkgSig bundle ledger pkg ->
          UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory sealRow ∧
            UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
              UnaryHistory realSeal ∧ UnaryHistory ledger ∧ Cont diagonal triangle sealRow ∧
                Cont diagonal dyadic ledger ∧ Cont dyadic windows readback ∧
                  Cont readback realSeal route ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle ledger pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle UnaryHistory
  intro carrier diagonalDyadicLedger ledgerPkg
  obtain ⟨diagonalUnary, triangleUnary, sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, diagonalTriangleSeal, dyadicWindowsReadback, readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicLedger
  exact
    ⟨diagonalUnary, triangleUnary, sealUnary, dyadicUnary, windowsUnary, readbackUnary,
      realSealUnary, ledgerUnary, diagonalTriangleSeal, diagonalDyadicLedger,
      dyadicWindowsReadback, readbackRealSealRoute, provenancePkg, ledgerPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
