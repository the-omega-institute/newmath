import BEDC.Derived.FormalBallUp

namespace BEDC.Derived.FormalBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FormalBallCarrier_located_radius_window [AskSetup] [PackageSetup]
    {M R D W H C P N locatedRead completionExport cauchyExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FormalBallCarrier M R D W H C P N bundle pkg →
      Cont M R D →
        Cont D W locatedRead →
          Cont locatedRead C completionExport →
            Cont locatedRead C cauchyExport →
              PkgSig bundle completionExport pkg →
                PkgSig bundle cauchyExport pkg →
                  UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory W ∧
                    UnaryHistory C ∧ UnaryHistory locatedRead ∧
                      UnaryHistory completionExport ∧ UnaryHistory cauchyExport ∧
                        Cont M R D ∧ Cont D W locatedRead ∧
                          Cont locatedRead C completionExport ∧
                            Cont locatedRead C cauchyExport ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle completionExport pkg ∧
                                PkgSig bundle cauchyExport pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier metricRadiusDyadic dyadicWindowLocated completionRoute cauchyRoute
    completionPkg cauchyPkg
  obtain ⟨metricUnary, radiusUnary, dyadicUnary, windowUnary, _transportUnary,
    replayUnary, _provenanceUnary, _nameCertUnary, _metricRadius, _dyadicWindowReplay,
    _transportReplay, provenancePkg⟩ := carrier
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed dyadicUnary windowUnary dyadicWindowLocated
  have completionUnary : UnaryHistory completionExport :=
    unary_cont_closed locatedUnary replayUnary completionRoute
  have cauchyUnary : UnaryHistory cauchyExport :=
    unary_cont_closed locatedUnary replayUnary cauchyRoute
  exact
    ⟨metricUnary, radiusUnary, dyadicUnary, windowUnary, replayUnary, locatedUnary,
      completionUnary, cauchyUnary, metricRadiusDyadic, dyadicWindowLocated,
      completionRoute, cauchyRoute, provenancePkg, completionPkg, cauchyPkg⟩

end BEDC.Derived.FormalBallUp
