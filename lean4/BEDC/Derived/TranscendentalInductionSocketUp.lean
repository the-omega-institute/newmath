import BEDC.Derived.TranscendentalInductionSocketUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TranscendentalInductionSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TranscendentalInductionSocketPacket [AskSetup] [PackageSetup]
    (source trace request gap handoff transports routes provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  UnaryHistory source ∧ UnaryHistory trace ∧ UnaryHistory request ∧ UnaryHistory gap ∧
    UnaryHistory handoff ∧ UnaryHistory transports ∧ UnaryHistory routes ∧
      UnaryHistory provenance ∧ UnaryHistory nameCert ∧ Cont trace request gap ∧
        Cont gap handoff routes ∧ Cont routes transports provenance ∧
          PkgSig bundle nameCert pkg

theorem TranscendentalInductionSocketPacket_gap_boundary [AskSetup] [PackageSetup]
    {source trace request gap handoff transports routes provenance nameCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TranscendentalInductionSocketPacket source trace request gap handoff transports routes
        provenance nameCert bundle pkg →
      Cont request gap consumer →
        PkgSig bundle consumer pkg →
          UnaryHistory trace ∧ UnaryHistory request ∧ UnaryHistory gap ∧
            UnaryHistory consumer ∧ Cont trace request gap ∧ Cont request gap consumer ∧
              PkgSig bundle nameCert pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro packet requestGapConsumer consumerPkg
  obtain ⟨_sourceUnary, traceUnary, requestUnary, gapUnary, _handoffUnary, _transportsUnary,
    _routesUnary, _provenanceUnary, _nameCertUnary, traceRequestGap, _gapHandoffRoutes,
    _routesTransportProvenance, nameCertPkg⟩ := packet
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed requestUnary gapUnary requestGapConsumer
  exact
    ⟨traceUnary, requestUnary, gapUnary, consumerUnary, traceRequestGap, requestGapConsumer,
      nameCertPkg, consumerPkg⟩

theorem TranscendentalInductionSocketPacket_inscription_handoff [AskSetup] [PackageSetup]
    {source trace request gap handoff transports routes provenance nameCert handoffConsumer
      exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TranscendentalInductionSocketPacket source trace request gap handoff transports routes
        provenance nameCert bundle pkg →
      Cont gap handoff handoffConsumer →
        Cont handoff handoffConsumer exported →
          PkgSig bundle exported pkg →
            UnaryHistory gap ∧ UnaryHistory handoff ∧ UnaryHistory handoffConsumer ∧
              UnaryHistory exported ∧ Cont gap handoff handoffConsumer ∧
                Cont handoff handoffConsumer exported ∧ PkgSig bundle nameCert pkg ∧
                  PkgSig bundle exported pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro packet gapHandoffConsumer handoffConsumerExport exportedPkg
  obtain ⟨_sourceUnary, _traceUnary, _requestUnary, gapUnary, handoffUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameCertUnary, _traceRequestGap,
    _gapHandoffRoutes, _routesTransportProvenance, nameCertPkg⟩ := packet
  have handoffConsumerUnary : UnaryHistory handoffConsumer :=
    unary_cont_closed gapUnary handoffUnary gapHandoffConsumer
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed handoffUnary handoffConsumerUnary handoffConsumerExport
  exact
    ⟨gapUnary, handoffUnary, handoffConsumerUnary, exportedUnary, gapHandoffConsumer,
      handoffConsumerExport, nameCertPkg, exportedPkg⟩

end BEDC.Derived.TranscendentalInductionSocketUp
