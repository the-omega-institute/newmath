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

theorem ModelPredictiveControlPacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {state input horizon dynamics cost rollout provenance nameRow constraint admissibility : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModelPredictiveControlPacket state input horizon dynamics cost rollout provenance nameRow
        bundle pkg ->
      Cont horizon cost constraint ->
        Cont rollout constraint admissibility ->
          PkgSig bundle admissibility pkg ->
            SemanticNameCert
              (fun row : BHist => hsame row admissibility ∧ UnaryHistory row ∧
                PkgSig bundle row pkg)
              (fun row : BHist =>
                UnaryHistory state ∧ UnaryHistory input ∧ UnaryHistory horizon ∧
                  UnaryHistory dynamics ∧ UnaryHistory cost ∧ UnaryHistory rollout ∧
                    UnaryHistory constraint ∧ UnaryHistory row ∧
                      Cont state dynamics rollout ∧ Cont horizon cost constraint ∧
                        Cont rollout constraint row)
              (fun row : BHist => PkgSig bundle provenance pkg ∧ PkgSig bundle row pkg)
              (fun row row' : BHist => psame bundle pkg pkg ∧ hsame row row') := by
  intro packet horizonCostConstraint rolloutConstraintAdmissibility admissibilityPkg
  obtain ⟨stateUnary, inputUnary, horizonUnary, dynamicsUnary, costUnary, nameRowUnary,
    stateDynamicsRollout, rolloutHorizonProvenance, provenancePkg⟩ := packet
  have rolloutUnary : UnaryHistory rollout :=
    unary_cont_closed stateUnary dynamicsUnary stateDynamicsRollout
  have constraintUnary : UnaryHistory constraint :=
    unary_cont_closed horizonUnary costUnary horizonCostConstraint
  have admissibilityUnary : UnaryHistory admissibility :=
    unary_cont_closed rolloutUnary constraintUnary rolloutConstraintAdmissibility
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro admissibility
          ⟨hsame_refl admissibility, admissibilityUnary, admissibilityPkg⟩
      equiv_refl := by
        intro row sourceRow
        exact
          ⟨PkgSig_psame_intro sourceRow.right.right sourceRow.right.right
            (hsame_refl row), hsame_refl row⟩
      equiv_symm := by
        intro _row _row' classified
        exact ⟨classified.left, hsame_symm classified.right⟩
      equiv_trans := by
        intro _row _row' _row'' leftClassified rightClassified
        exact ⟨leftClassified.left, hsame_trans leftClassified.right rightClassified.right⟩
      carrier_respects_equiv := by
        intro _row _row' classified sourceRow
        cases classified.right
        exact sourceRow
    }
    pattern_sound := by
      intro row sourceRow
      cases sourceRow.left
      exact
        ⟨stateUnary, inputUnary, horizonUnary, dynamicsUnary, costUnary, rolloutUnary,
          constraintUnary, admissibilityUnary, stateDynamicsRollout, horizonCostConstraint,
          rolloutConstraintAdmissibility⟩
    ledger_sound := by
      intro row sourceRow
      cases sourceRow.left
      exact ⟨provenancePkg, admissibilityPkg⟩
  }

end BEDC.Derived.ModelPredictiveControlUp
