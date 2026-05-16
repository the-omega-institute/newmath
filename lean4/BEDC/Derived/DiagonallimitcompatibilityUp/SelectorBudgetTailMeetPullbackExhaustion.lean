import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_selector_budget_tail_meet_pullback_exhaustion
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance
      cert threshold filterRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont windows readback threshold ->
        Cont threshold realSeal filterRead ->
          Cont filterRead cert completionRead ->
            PkgSig bundle completionRead pkg ->
              UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
                UnaryHistory threshold ∧ UnaryHistory filterRead ∧
                  UnaryHistory completionRead ∧ Cont dyadic windows readback ∧
                    Cont windows readback threshold ∧ Cont threshold realSeal filterRead ∧
                      Cont filterRead cert completionRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory ProbeBundle
  intro carrier windowsReadbackThreshold thresholdRealSealFilter filterCertCompletion
    completionPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have thresholdUnary : UnaryHistory threshold :=
    unary_cont_closed windowsUnary readbackUnary windowsReadbackThreshold
  have filterReadUnary : UnaryHistory filterRead :=
    unary_cont_closed thresholdUnary realSealUnary thresholdRealSealFilter
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed filterReadUnary certUnary filterCertCompletion
  exact
    ⟨windowsUnary, readbackUnary, realSealUnary, thresholdUnary, filterReadUnary,
      completionReadUnary, dyadicWindowsReadback, windowsReadbackThreshold,
      thresholdRealSealFilter, filterCertCompletion, provenancePkg, completionPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
