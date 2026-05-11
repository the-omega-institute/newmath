import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LyapunovStabilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LyapunovStabilityPacket [AskSetup] [PackageSetup]
    (state transition base energy level comparison descent transports routes provenance name
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory state ∧ UnaryHistory transition ∧ UnaryHistory base ∧ UnaryHistory energy ∧
    UnaryHistory level ∧ UnaryHistory comparison ∧ UnaryHistory transports ∧
      UnaryHistory routes ∧ UnaryHistory provenance ∧ Cont state transition descent ∧
        Cont base energy level ∧ Cont level comparison transports ∧ Cont descent routes endpoint ∧
          Cont endpoint provenance name ∧ PkgSig bundle name pkg

theorem LyapunovStabilityPacket_level_set_containment [AskSetup] [PackageSetup]
    {state transition base energy level comparison descent transports routes provenance name endpoint
      successorLevel consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LyapunovStabilityPacket state transition base energy level comparison descent transports routes
        provenance name endpoint bundle pkg ->
      Cont descent level successorLevel ->
        Cont successorLevel provenance consumer ->
          PkgSig bundle consumer pkg ->
            UnaryHistory descent ∧ UnaryHistory level ∧ UnaryHistory successorLevel ∧
              UnaryHistory consumer ∧ Cont state transition descent ∧
                Cont descent level successorLevel ∧ Cont successorLevel provenance consumer ∧
                  PkgSig bundle consumer pkg := by
  intro packet successorRow consumerRow consumerSig
  obtain ⟨stateUnary, transitionUnary, _baseUnary, _energyUnary, levelUnary, _comparisonUnary,
    _transportsUnary, _routesUnary, provenanceUnary, descentRow, _levelRow, _transportRow,
    _endpointRow, _nameRow, _nameSig⟩ := packet
  have descentUnary : UnaryHistory descent :=
    unary_cont_closed stateUnary transitionUnary descentRow
  have successorUnary : UnaryHistory successorLevel :=
    unary_cont_closed descentUnary levelUnary successorRow
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed successorUnary provenanceUnary consumerRow
  exact
    ⟨descentUnary, levelUnary, successorUnary, consumerUnary, descentRow, successorRow,
      consumerRow, consumerSig⟩

end BEDC.Derived.LyapunovStabilityUp
