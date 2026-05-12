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

theorem ModelPredictiveControlPacket_receding_horizon_boundary [AskSetup] [PackageSetup]
    {state input horizon dynamics cost rollout provenance nameRow firstControl : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModelPredictiveControlPacket state input horizon dynamics cost rollout provenance nameRow
        bundle pkg ->
      Cont rollout horizon firstControl ->
        PkgSig bundle firstControl pkg ->
          UnaryHistory state ∧ UnaryHistory input ∧ UnaryHistory horizon ∧
            UnaryHistory dynamics ∧ UnaryHistory cost ∧ UnaryHistory rollout ∧
              UnaryHistory provenance ∧ UnaryHistory firstControl ∧
                Cont state dynamics rollout ∧ Cont rollout horizon provenance ∧
                  Cont rollout horizon firstControl ∧ hsame provenance firstControl ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle firstControl pkg := by
  intro packet firstControlRow firstControlPkg
  obtain ⟨stateUnary, inputUnary, horizonUnary, dynamicsUnary, costUnary, _nameRowUnary,
    rolloutRow, provenanceRow, provenancePkg⟩ := packet
  have rolloutUnary : UnaryHistory rollout :=
    unary_cont_closed stateUnary dynamicsUnary rolloutRow
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed rolloutUnary horizonUnary provenanceRow
  have firstControlUnary : UnaryHistory firstControl :=
    unary_cont_closed rolloutUnary horizonUnary firstControlRow
  have sameFirstControl : hsame provenance firstControl :=
    cont_deterministic provenanceRow firstControlRow
  exact
    ⟨stateUnary, inputUnary, horizonUnary, dynamicsUnary, costUnary, rolloutUnary,
      provenanceUnary, firstControlUnary, rolloutRow, provenanceRow, firstControlRow,
      sameFirstControl, provenancePkg, firstControlPkg⟩

end BEDC.Derived.ModelPredictiveControlUp
