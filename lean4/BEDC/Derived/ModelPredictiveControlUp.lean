import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ModelPredictiveControlUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem ModelPredictiveControlPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {state input horizon dynamics cost rollout provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModelPredictiveControlPacket state input horizon dynamics cost rollout provenance nameRow
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist => hsame row provenance ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
        (fun row : BHist => Cont rollout horizon row ∧ UnaryHistory state ∧
          UnaryHistory input ∧ UnaryHistory cost)
        (fun row : BHist => PkgSig bundle row pkg ∧ Cont state dynamics rollout ∧
          Cont rollout horizon provenance)
        (fun row row' : BHist => hsame row row') := by
  intro packet
  obtain ⟨stateUnary, inputUnary, horizonUnary, dynamicsUnary, costUnary, _nameRowUnary,
    stateDynamicsRollout, rolloutHorizonProvenance, provenancePkg⟩ := packet
  have rolloutUnary : UnaryHistory rollout :=
    unary_cont_closed stateUnary dynamicsUnary stateDynamicsRollout
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed rolloutUnary horizonUnary rolloutHorizonProvenance
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro provenance ⟨hsame_refl provenance, provenanceUnary, provenancePkg⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' classified
        exact hsame_symm classified
      equiv_trans := by
        intro _row _row' _row'' leftClassified rightClassified
        exact hsame_trans leftClassified rightClassified
      carrier_respects_equiv := by
        intro _row _row' classified sourceRow
        cases classified
        exact sourceRow
    }
    pattern_sound := by
      intro row sourceRow
      exact
        ⟨cont_result_hsame_transport rolloutHorizonProvenance (hsame_symm sourceRow.left),
          stateUnary, inputUnary, costUnary⟩
    ledger_sound := by
      intro row sourceRow
      exact ⟨sourceRow.right.right, stateDynamicsRollout, rolloutHorizonProvenance⟩
  }

end BEDC.Derived.ModelPredictiveControlUp
