import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilitySourceGate [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance
      cert sourceGate sealGate : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback
        realSeal transport route provenance cert bundle pkg ->
      Cont diagonal windows sourceGate ->
        Cont sourceGate readback sealGate ->
          PkgSig bundle sealGate pkg ->
            UnaryHistory diagonal ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
              UnaryHistory sourceGate ∧ UnaryHistory sealGate ∧
                Cont diagonal windows sourceGate ∧ Cont sourceGate readback sealGate ∧
                  Cont readback realSeal route ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle sealGate pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier diagonalWindowsSource sourceReadbackSeal sealPkg
  obtain
    ⟨diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, windowsUnary,
      readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
      _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, readbackRealSealRoute,
      _routeCertTransport, provenancePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceGate :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSource
  have sealUnary : UnaryHistory sealGate :=
    unary_cont_closed sourceUnary readbackUnary sourceReadbackSeal
  exact
    ⟨diagonalUnary, windowsUnary, readbackUnary, sourceUnary, sealUnary,
      diagonalWindowsSource, sourceReadbackSeal, readbackRealSealRoute, provenancePkg,
      sealPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
