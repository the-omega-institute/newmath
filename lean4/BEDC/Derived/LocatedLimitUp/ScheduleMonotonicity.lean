import BEDC.Derived.LocatedLimitUp.RealSealRoute

namespace BEDC.Derived.LocatedLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedLimitCarrier_schedule_monotonicity [AskSetup] [PackageSetup]
    {sequence modulus schedule readback sealRow transport replay provenance name request
      refinedRequest scheduleRead refinedScheduleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedLimitCarrier sequence modulus schedule readback sealRow transport replay provenance
        name bundle pkg →
      Cont request modulus scheduleRead →
        Cont refinedRequest modulus refinedScheduleRead →
          UnaryHistory request →
            UnaryHistory refinedRequest →
              UnaryHistory scheduleRead ∧ UnaryHistory refinedScheduleRead ∧
                Cont request modulus scheduleRead ∧
                  Cont refinedRequest modulus refinedScheduleRead ∧
                    PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier requestRoute refinedRoute requestUnary refinedRequestUnary
  obtain ⟨_sequenceUnary, modulusUnary, _scheduleUnary, _readbackUnary, _sealRowUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, provenancePkg⟩ := carrier
  have scheduleReadUnary : UnaryHistory scheduleRead :=
    unary_cont_closed requestUnary modulusUnary requestRoute
  have refinedScheduleReadUnary : UnaryHistory refinedScheduleRead :=
    unary_cont_closed refinedRequestUnary modulusUnary refinedRoute
  exact
    ⟨scheduleReadUnary, refinedScheduleReadUnary, requestRoute, refinedRoute, provenancePkg⟩

end BEDC.Derived.LocatedLimitUp
