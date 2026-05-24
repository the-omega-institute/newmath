import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_minimal_convergence_seal_witness
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      convergenceRead completionRead synchronizerBudget tailRoute realTailAgreement
      sharedSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont sealRow provenance convergenceRead →
        Cont convergenceRead regular completionRead →
          Cont source schedule synchronizerBudget →
            Cont synchronizerBudget ledger tailRoute →
              Cont tailRoute trap realTailAgreement →
                Cont realTailAgreement sealRow sharedSeal →
                  PkgSig bundle completionRead pkg →
                    PkgSig bundle sharedSeal pkg →
                      SemanticNameCert
                        (fun row : BHist =>
                          hsame row completionRead ∧
                            BoundedMonotoneCauchyWitnessCarrier source regular schedule witness
                              ledger trap sealRow transport route provenance localCert bundle pkg)
                        (fun row : BHist =>
                          Cont sealRow provenance convergenceRead ∧
                            Cont convergenceRead regular row ∧
                              Cont source schedule synchronizerBudget ∧
                                Cont synchronizerBudget ledger tailRoute ∧
                                  Cont tailRoute trap realTailAgreement)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle completionRead pkg ∧
                            PkgSig bundle sharedSeal pkg)
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier sealProvenanceConvergence convergenceRegularCompletion sourceScheduleSync
    syncLedgerTail tailTrapAgreement agreementSealShared completionPkg sharedPkg
  have carrierPacket :
      BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg :=
    carrier
  obtain ⟨_sourceUnary, regularUnary, _scheduleUnary, _witnessUnary, _ledgerUnary, _trapUnary,
    sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, _provenancePkg⟩ := carrier
  have convergenceUnary : UnaryHistory convergenceRead :=
    unary_cont_closed sealUnary provenanceUnary sealProvenanceConvergence
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed convergenceUnary regularUnary convergenceRegularCompletion
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead
          (And.intro (hsame_refl completionRead) carrierPacket)
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
        ⟨sealProvenanceConvergence,
          cont_result_hsame_transport convergenceRegularCompletion (hsame_symm source.left),
          sourceScheduleSync, syncLedgerTail, tailTrapAgreement⟩
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport completionUnary (hsame_symm source.left), completionPkg, sharedPkg⟩
  }

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
