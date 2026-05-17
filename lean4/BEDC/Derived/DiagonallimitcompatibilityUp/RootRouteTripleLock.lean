import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootRouteTripleLock [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      threshold uniformExit monotoneTail locked : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      UnaryHistory threshold →
        UnaryHistory uniformExit →
          UnaryHistory monotoneTail →
            Cont windows dyadic threshold →
              Cont threshold realSeal uniformExit →
                Cont uniformExit monotoneTail locked →
                  PkgSig bundle locked pkg →
                    UnaryHistory windows ∧ UnaryHistory dyadic ∧ UnaryHistory threshold ∧
                      UnaryHistory realSeal ∧ UnaryHistory uniformExit ∧
                        UnaryHistory monotoneTail ∧ UnaryHistory locked ∧
                          Cont windows dyadic threshold ∧
                            Cont threshold realSeal uniformExit ∧
                              Cont uniformExit monotoneTail locked ∧
                                PkgSig bundle provenance pkg ∧ PkgSig bundle locked pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro carrier thresholdUnary uniformExitUnary monotoneTailUnary windowsDyadicThreshold
    thresholdRealSealUniformExit uniformExitMonotoneTailLocked lockedPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    _readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have thresholdUnaryFromRoute : UnaryHistory threshold :=
    unary_cont_closed windowsUnary dyadicUnary windowsDyadicThreshold
  have uniformExitUnaryFromRoute : UnaryHistory uniformExit :=
    unary_cont_closed thresholdUnaryFromRoute realSealUnary thresholdRealSealUniformExit
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed uniformExitUnaryFromRoute monotoneTailUnary uniformExitMonotoneTailLocked
  exact
    ⟨windowsUnary, dyadicUnary, thresholdUnary, realSealUnary, uniformExitUnary,
      monotoneTailUnary, lockedUnary, windowsDyadicThreshold, thresholdRealSealUniformExit,
      uniformExitMonotoneTailLocked, provenancePkg, lockedPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
