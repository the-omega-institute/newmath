import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_shared_budget_meet [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      synchronizerBudget tailRoute realTailAgreement sharedSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule synchronizerBudget →
        Cont synchronizerBudget ledger tailRoute →
          Cont tailRoute trap realTailAgreement →
            Cont realTailAgreement sealRow sharedSeal →
              PkgSig bundle sharedSeal pkg →
                SemanticNameCert
                  (fun row : BHist =>
                    hsame row sharedSeal ∧
                      BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger
                        trap sealRow transport route provenance localCert bundle pkg)
                  (fun row : BHist =>
                    Cont source schedule synchronizerBudget ∧
                      Cont synchronizerBudget ledger tailRoute ∧
                        Cont tailRoute trap realTailAgreement ∧
                          Cont realTailAgreement sealRow row)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle sharedSeal pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier sourceScheduleSync syncLedgerTail tailTrapAgreement agreementSeal sharedPkg
  have carrierPacket :
      BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg :=
    carrier
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, _witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, _provenancePkg⟩ := carrier
  have syncUnary : UnaryHistory synchronizerBudget :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleSync
  have tailUnary : UnaryHistory tailRoute :=
    unary_cont_closed syncUnary ledgerUnary syncLedgerTail
  have agreementUnary : UnaryHistory realTailAgreement :=
    unary_cont_closed tailUnary trapUnary tailTrapAgreement
  have sharedUnary : UnaryHistory sharedSeal :=
    unary_cont_closed agreementUnary sealUnary agreementSeal
  exact {
    core := {
      carrier_inhabited := Exists.intro sharedSeal ⟨hsame_refl sharedSeal, carrierPacket⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
    }
    pattern_sound := by
      intro row source
      exact
        ⟨sourceScheduleSync, syncLedgerTail, tailTrapAgreement,
          cont_result_hsame_transport agreementSeal (hsame_symm source.left)⟩
    ledger_sound := by
      intro row source
      exact ⟨unary_transport sharedUnary (hsame_symm source.left), sharedPkg⟩
  }

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
