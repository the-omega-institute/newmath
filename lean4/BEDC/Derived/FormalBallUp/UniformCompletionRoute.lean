import BEDC.Derived.FormalBallUp

namespace BEDC.Derived.FormalBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FormalBallCarrier_uniform_completion_route [AskSetup] [PackageSetup]
    {M R D W H C P N radiusRead windowRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FormalBallCarrier M R D W H C P N bundle pkg →
      Cont R D radiusRead →
        Cont radiusRead W windowRead →
          Cont windowRead C uniformRead →
            PkgSig bundle uniformRead pkg →
              UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory W ∧
                UnaryHistory C ∧ UnaryHistory radiusRead ∧ UnaryHistory windowRead ∧
                  UnaryHistory uniformRead ∧ Cont R D radiusRead ∧
                    Cont radiusRead W windowRead ∧ Cont windowRead C uniformRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier radiusRoute windowRoute uniformRoute uniformPkg
  obtain ⟨metricUnary, radiusUnary, dyadicUnary, windowUnary, _transportUnary,
    replayUnary, _provenanceUnary, _nameCertUnary, _metricRadius, _dyadicWindowReplay,
    _transportReplay, provenancePkg⟩ := carrier
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiusUnary dyadicUnary radiusRoute
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed radiusReadUnary windowUnary windowRoute
  have uniformReadUnary : UnaryHistory uniformRead :=
    unary_cont_closed windowReadUnary replayUnary uniformRoute
  exact
    ⟨metricUnary, radiusUnary, dyadicUnary, windowUnary, replayUnary, radiusReadUnary,
      windowReadUnary, uniformReadUnary, radiusRoute, windowRoute, uniformRoute, provenancePkg,
      uniformPkg⟩

end BEDC.Derived.FormalBallUp
