import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ChoiceFreeLimitScheduleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ChoiceFreeLimitSchedulePacket [AskSetup] [PackageSetup]
    (request schedule windows dyadic handoff sealRow transports routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory request ∧ UnaryHistory schedule ∧ UnaryHistory windows ∧
    UnaryHistory dyadic ∧ UnaryHistory handoff ∧ UnaryHistory sealRow ∧
      UnaryHistory transports ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont request schedule windows ∧ Cont windows dyadic handoff ∧
          Cont handoff sealRow transports ∧ Cont transports routes provenance ∧
            PkgSig bundle name pkg

theorem ChoiceFreeLimitSchedulePacket_namecert_obligations [AskSetup] [PackageSetup]
    {request schedule windows dyadic handoff sealRow transports routes provenance name consumer :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ChoiceFreeLimitSchedulePacket request schedule windows dyadic handoff sealRow transports routes
        provenance name bundle pkg ->
      Cont request handoff consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory request /\ UnaryHistory schedule /\ UnaryHistory windows /\
            UnaryHistory dyadic /\ UnaryHistory handoff /\ UnaryHistory sealRow /\
              UnaryHistory consumer /\ Cont request schedule windows /\
                Cont windows dyadic handoff /\ Cont request handoff consumer /\
                  PkgSig bundle name pkg /\ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet requestHandoffConsumer consumerPkg
  obtain ⟨requestUnary, scheduleUnary, windowsUnary, dyadicUnary, handoffUnary, sealUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, requestScheduleWindows,
    windowsDyadicHandoff, _handoffSealTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed requestUnary handoffUnary requestHandoffConsumer
  exact
    ⟨requestUnary, scheduleUnary, windowsUnary, dyadicUnary, handoffUnary, sealUnary,
      consumerUnary, requestScheduleWindows, windowsDyadicHandoff, requestHandoffConsumer,
      namePkg, consumerPkg⟩

end BEDC.Derived.ChoiceFreeLimitScheduleUp
