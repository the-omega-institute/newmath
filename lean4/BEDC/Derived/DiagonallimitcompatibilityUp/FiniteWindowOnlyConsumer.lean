import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_finite_window_only_consumer [AskSetup]
    [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      finiteWindow consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont dyadic windows finiteWindow →
        Cont finiteWindow readback consumer →
          PkgSig bundle consumer pkg →
            UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory sealRow ∧
              UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
                UnaryHistory realSeal ∧ UnaryHistory finiteWindow ∧ UnaryHistory consumer ∧
                  Cont diagonal triangle sealRow ∧ Cont dyadic windows finiteWindow ∧
                    Cont finiteWindow readback consumer ∧ Cont dyadic windows readback ∧
                      Cont readback realSeal route ∧ Cont route cert transport ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier dyadicWindowsFinite finiteReadbackConsumer consumerPkg
  obtain ⟨diagonalUnary, triangleUnary, sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, diagonalTriangleSeal, dyadicWindowsReadback, readbackRealSealRoute,
    routeCertTransport, provenancePkg⟩ := carrier
  have finiteWindowUnary : UnaryHistory finiteWindow :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsFinite
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed finiteWindowUnary readbackUnary finiteReadbackConsumer
  exact
    ⟨diagonalUnary, triangleUnary, sealUnary, dyadicUnary, windowsUnary, readbackUnary,
      realSealUnary, finiteWindowUnary, consumerUnary, diagonalTriangleSeal,
      dyadicWindowsFinite, finiteReadbackConsumer, dyadicWindowsReadback,
      readbackRealSealRoute, routeCertTransport, provenancePkg, consumerPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
