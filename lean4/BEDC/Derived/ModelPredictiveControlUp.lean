import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ModelPredictiveControlUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ModelPredictiveControlPacket [AskSetup] [PackageSetup]
    (state input horizon dynamics cost rollout provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory state ∧ UnaryHistory input ∧ UnaryHistory horizon ∧
    UnaryHistory dynamics ∧ UnaryHistory cost ∧ UnaryHistory nameRow ∧
      Cont state dynamics rollout ∧ Cont rollout horizon provenance ∧
        PkgSig bundle provenance pkg

theorem ModelPredictiveControlPacket_finite_horizon_obligation [AskSetup] [PackageSetup]
    {state input horizon dynamics cost rollout provenance nameRow rollout' provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModelPredictiveControlPacket state input horizon dynamics cost rollout provenance nameRow
        bundle pkg ->
      Cont state dynamics rollout' ->
        Cont rollout' horizon provenance' ->
          PkgSig bundle provenance' pkg ->
            UnaryHistory state ∧ UnaryHistory input ∧ UnaryHistory horizon ∧
              UnaryHistory dynamics ∧ UnaryHistory cost ∧ UnaryHistory rollout' ∧
                UnaryHistory provenance' ∧ Cont state dynamics rollout' ∧
                  Cont rollout' horizon provenance' ∧ PkgSig bundle provenance' pkg := by
  intro packet rolloutRow provenanceRow provenancePkg
  obtain ⟨stateUnary, inputUnary, horizonUnary, dynamicsUnary, costUnary, _nameRowUnary,
    _packetRollout, _packetProvenance, _packetPkg⟩ := packet
  have rolloutUnary : UnaryHistory rollout' :=
    unary_cont_closed stateUnary dynamicsUnary rolloutRow
  have provenanceUnary : UnaryHistory provenance' :=
    unary_cont_closed rolloutUnary horizonUnary provenanceRow
  exact
    ⟨stateUnary, inputUnary, horizonUnary, dynamicsUnary, costUnary, rolloutUnary,
      provenanceUnary, rolloutRow, provenanceRow, provenancePkg⟩

theorem ModelPredictiveControlPacket_consumer_boundary [AskSetup] [PackageSetup]
    {state input horizon dynamics cost rollout provenance nameRow exportedControl consumer :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModelPredictiveControlPacket state input horizon dynamics cost rollout provenance nameRow
        bundle pkg ->
      Cont rollout provenance exportedControl ->
        Cont exportedControl nameRow consumer ->
          PkgSig bundle exportedControl pkg ->
            PkgSig bundle consumer pkg ->
              UnaryHistory state ∧ UnaryHistory input ∧ UnaryHistory horizon ∧
                UnaryHistory rollout ∧ UnaryHistory exportedControl ∧ UnaryHistory consumer ∧
                  Cont rollout provenance exportedControl ∧
                    Cont exportedControl nameRow consumer ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle exportedControl pkg ∧ PkgSig bundle consumer pkg := by
  intro packet rolloutProvenanceExported exportedNameConsumer exportedPkg consumerPkg
  obtain ⟨stateUnary, inputUnary, horizonUnary, dynamicsUnary, _costUnary, nameUnary,
    stateDynamicsRollout, rolloutHorizonProvenance, provenancePkg⟩ := packet
  have rolloutUnary : UnaryHistory rollout :=
    unary_cont_closed stateUnary dynamicsUnary stateDynamicsRollout
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed rolloutUnary horizonUnary rolloutHorizonProvenance
  have exportedUnary : UnaryHistory exportedControl :=
    unary_cont_closed rolloutUnary provenanceUnary rolloutProvenanceExported
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed exportedUnary nameUnary exportedNameConsumer
  exact
    ⟨stateUnary, inputUnary, horizonUnary, rolloutUnary, exportedUnary, consumerUnary,
      rolloutProvenanceExported, exportedNameConsumer, provenancePkg, exportedPkg,
      consumerPkg⟩

end BEDC.Derived.ModelPredictiveControlUp
