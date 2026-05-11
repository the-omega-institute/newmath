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

def LyapunovStabilityCarrier [AskSetup] [PackageSetup]
    (state transition energy level descent successorEnergy comparison provenance
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory state ∧ UnaryHistory transition ∧ UnaryHistory energy ∧ UnaryHistory level ∧
    UnaryHistory descent ∧ UnaryHistory successorEnergy ∧ UnaryHistory comparison ∧
      UnaryHistory provenance ∧ UnaryHistory endpoint ∧ Cont state transition descent ∧
        Cont energy descent successorEnergy ∧ Cont successorEnergy level comparison ∧
          Cont comparison provenance endpoint ∧ PkgSig bundle endpoint pkg

theorem LyapunovStabilityCarrier_level_set_containment [AskSetup] [PackageSetup]
    {state transition energy level descent successorEnergy comparison provenance endpoint state'
      transition' energy' level' descent' successorEnergy' comparison' provenance'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LyapunovStabilityCarrier state transition energy level descent successorEnergy comparison
        provenance endpoint bundle pkg ->
      hsame state state' ->
        hsame transition transition' ->
          hsame energy energy' ->
            hsame level level' ->
              hsame provenance provenance' ->
                Cont state' transition' descent' ->
                  Cont energy' descent' successorEnergy' ->
                    Cont successorEnergy' level' comparison' ->
                      Cont comparison' provenance' endpoint' ->
                        PkgSig bundle endpoint' pkg ->
                          LyapunovStabilityCarrier state' transition' energy' level' descent'
                              successorEnergy' comparison' provenance' endpoint' bundle pkg ∧
                            hsame descent descent' ∧ hsame successorEnergy successorEnergy' ∧
                              hsame comparison comparison' ∧ hsame endpoint endpoint' := by
  intro carrier sameState sameTransition sameEnergy sameLevel sameProvenance descentCont'
    successorEnergyCont' comparisonCont' endpointCont' pkg'
  have stateUnary' : UnaryHistory state' :=
    unary_transport carrier.left sameState
  have transitionUnary' : UnaryHistory transition' :=
    unary_transport carrier.right.left sameTransition
  have energyUnary' : UnaryHistory energy' :=
    unary_transport carrier.right.right.left sameEnergy
  have levelUnary' : UnaryHistory level' :=
    unary_transport carrier.right.right.right.left sameLevel
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport carrier.right.right.right.right.right.right.right.left sameProvenance
  have sameDescent : hsame descent descent' :=
    cont_respects_hsame sameState sameTransition
      carrier.right.right.right.right.right.right.right.right.right.left descentCont'
  have descentUnary' : UnaryHistory descent' :=
    unary_cont_closed stateUnary' transitionUnary' descentCont'
  have sameSuccessorEnergy : hsame successorEnergy successorEnergy' :=
    cont_respects_hsame sameEnergy sameDescent
      carrier.right.right.right.right.right.right.right.right.right.right.left successorEnergyCont'
  have successorEnergyUnary' : UnaryHistory successorEnergy' :=
    unary_cont_closed energyUnary' descentUnary' successorEnergyCont'
  have sameComparison : hsame comparison comparison' :=
    cont_respects_hsame sameSuccessorEnergy sameLevel
      carrier.right.right.right.right.right.right.right.right.right.right.right.left
      comparisonCont'
  have comparisonUnary' : UnaryHistory comparison' :=
    unary_cont_closed successorEnergyUnary' levelUnary' comparisonCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameComparison sameProvenance
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.left
      endpointCont'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed comparisonUnary' provenanceUnary' endpointCont'
  exact
    And.intro
      (And.intro stateUnary'
        (And.intro transitionUnary'
          (And.intro energyUnary'
            (And.intro levelUnary'
              (And.intro descentUnary'
                (And.intro successorEnergyUnary'
                  (And.intro comparisonUnary'
                    (And.intro provenanceUnary'
                      (And.intro endpointUnary'
                        (And.intro descentCont'
                          (And.intro successorEnergyCont'
                            (And.intro comparisonCont'
                              (And.intro endpointCont' pkg')))))))))))))
      (And.intro sameDescent
        (And.intro sameSuccessorEnergy (And.intro sameComparison sameEndpoint)))

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
