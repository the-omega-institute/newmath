import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_seal_source_scope_row [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      scope : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic scope ->
        Cont scope windows readback ->
          PkgSig bundle scope pkg ->
            UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory scope ∧
              UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
                Cont diagonal dyadic scope ∧ Cont scope windows readback ∧
                  Cont readback realSeal route ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle scope pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle
  intro carrier diagonalDyadicScope scopeWindowsReadback scopePkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    _readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have scopeUnary : UnaryHistory scope :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicScope
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed scopeUnary windowsUnary scopeWindowsReadback
  exact
    ⟨diagonalUnary, dyadicUnary, scopeUnary, windowsUnary, readbackUnary, realSealUnary,
      diagonalDyadicScope, scopeWindowsReadback, readbackRealSealRoute, provenancePkg,
      scopePkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
