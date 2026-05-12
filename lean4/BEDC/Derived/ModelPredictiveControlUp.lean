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

def ModelPredictiveControlConstraintLedger [AskSetup] [PackageSetup]
    (state input horizon dynamics cost rollout provenance nameRow constraintWindow terminal :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  ModelPredictiveControlPacket state input horizon dynamics cost rollout provenance nameRow
      bundle pkg ∧
    Cont horizon cost constraintWindow ∧ Cont constraintWindow rollout terminal ∧
      PkgSig bundle terminal pkg

theorem ModelPredictiveControlConstraintLedger_semantic_name_certificate
    [AskSetup] [PackageSetup]
    {state input horizon dynamics cost rollout provenance nameRow constraintWindow terminal :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModelPredictiveControlConstraintLedger state input horizon dynamics cost rollout provenance
        nameRow constraintWindow terminal bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          ModelPredictiveControlConstraintLedger state input horizon dynamics cost rollout
            provenance nameRow constraintWindow terminal bundle pkg ∧ hsame row terminal)
        (fun row : BHist =>
          ModelPredictiveControlConstraintLedger state input horizon dynamics cost rollout
            provenance nameRow constraintWindow terminal bundle pkg ∧ hsame row terminal)
        (fun row : BHist =>
          ModelPredictiveControlConstraintLedger state input horizon dynamics cost rollout
            provenance nameRow constraintWindow terminal bundle pkg ∧ hsame row terminal)
        hsame := by
  intro ledger
  have ledgerSource := ledger
  obtain ⟨packet, horizonCostWindow, windowRolloutTerminal, _terminalPkg⟩ := ledger
  obtain ⟨stateUnary, _inputUnary, horizonUnary, dynamicsUnary, costUnary, _nameUnary,
    stateDynamicsRollout, _rolloutHorizonProvenance, _provenancePkg⟩ := packet
  have rolloutUnary : UnaryHistory rollout :=
    unary_cont_closed stateUnary dynamicsUnary stateDynamicsRollout
  have constraintWindowUnary : UnaryHistory constraintWindow :=
    unary_cont_closed horizonUnary costUnary horizonCostWindow
  have _terminalUnary : UnaryHistory terminal :=
    unary_cont_closed constraintWindowUnary rolloutUnary windowRolloutTerminal
  exact {
    core := {
      carrier_inhabited := Exists.intro terminal (And.intro ledgerSource (hsame_refl terminal))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

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
