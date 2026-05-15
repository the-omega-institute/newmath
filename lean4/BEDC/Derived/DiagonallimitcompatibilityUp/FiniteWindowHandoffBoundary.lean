import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_finite_window_handoff_boundary [AskSetup]
    [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      finiteWindow publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont dyadic windows finiteWindow ->
        Cont finiteWindow realSeal publicRead ->
          PkgSig bundle publicRead pkg ->
            UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory finiteWindow ∧
              UnaryHistory realSeal ∧ UnaryHistory publicRead ∧
                Cont dyadic windows finiteWindow ∧ Cont finiteWindow realSeal publicRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier dyadicWindowsFinite finiteRealPublic publicPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    _readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have finiteWindowUnary : UnaryHistory finiteWindow :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsFinite
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed finiteWindowUnary realSealUnary finiteRealPublic
  exact
    ⟨dyadicUnary, windowsUnary, finiteWindowUnary, realSealUnary, publicReadUnary,
      dyadicWindowsFinite, finiteRealPublic, provenancePkg, publicPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
