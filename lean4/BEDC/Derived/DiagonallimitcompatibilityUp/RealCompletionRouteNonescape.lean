import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_real_completion_route_nonescape
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      synchronizer limitSeal completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont windows readback synchronizer ->
        Cont synchronizer realSeal limitSeal ->
          Cont limitSeal cert completionRead ->
            PkgSig bundle completionRead pkg ->
              UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory synchronizer ∧
                UnaryHistory realSeal ∧ UnaryHistory limitSeal ∧ UnaryHistory completionRead ∧
                  Cont windows readback synchronizer ∧ Cont synchronizer realSeal limitSeal ∧
                    Cont limitSeal cert completionRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier windowsReadbackSynchronizer synchronizerRealSealLimitSeal
    limitSealCertCompletionRead completionReadPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, _dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, certUnary,
    _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have synchronizerUnary : UnaryHistory synchronizer :=
    unary_cont_closed windowsUnary readbackUnary windowsReadbackSynchronizer
  have limitSealUnary : UnaryHistory limitSeal :=
    unary_cont_closed synchronizerUnary realSealUnary synchronizerRealSealLimitSeal
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed limitSealUnary certUnary limitSealCertCompletionRead
  exact
    ⟨windowsUnary, readbackUnary, synchronizerUnary, realSealUnary, limitSealUnary,
      completionReadUnary, windowsReadbackSynchronizer, synchronizerRealSealLimitSeal,
      limitSealCertCompletionRead, provenancePkg, completionReadPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
