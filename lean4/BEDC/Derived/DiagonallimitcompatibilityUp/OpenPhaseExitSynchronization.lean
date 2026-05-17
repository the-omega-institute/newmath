import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityOpenPhaseExitSynchronization [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      threshold regularRead realExit uniformExit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont windows dyadic threshold →
        Cont threshold readback regularRead →
          Cont regularRead realSeal realExit →
            Cont realExit route uniformExit →
              PkgSig bundle uniformExit pkg →
                UnaryHistory windows ∧ UnaryHistory dyadic ∧ UnaryHistory threshold ∧
                  UnaryHistory readback ∧ UnaryHistory regularRead ∧ UnaryHistory realSeal ∧
                    UnaryHistory realExit ∧ UnaryHistory uniformExit ∧
                      Cont windows dyadic threshold ∧ Cont threshold readback regularRead ∧
                        Cont regularRead realSeal realExit ∧ Cont realExit route uniformExit ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle uniformExit pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro carrier windowsDyadicThreshold thresholdReadbackRegular regularRealSealExit
    exitRouteUniform uniformPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, routeUnary, _provenanceUnary, _certUnary,
    _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have thresholdUnary : UnaryHistory threshold :=
    unary_cont_closed windowsUnary dyadicUnary windowsDyadicThreshold
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed thresholdUnary readbackUnary thresholdReadbackRegular
  have realExitUnary : UnaryHistory realExit :=
    unary_cont_closed regularUnary realSealUnary regularRealSealExit
  have uniformExitUnary : UnaryHistory uniformExit :=
    unary_cont_closed realExitUnary routeUnary exitRouteUniform
  exact
    ⟨windowsUnary, dyadicUnary, thresholdUnary, readbackUnary, regularUnary, realSealUnary,
      realExitUnary, uniformExitUnary, windowsDyadicThreshold, thresholdReadbackRegular,
      regularRealSealExit, exitRouteUniform, provenancePkg, uniformPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
