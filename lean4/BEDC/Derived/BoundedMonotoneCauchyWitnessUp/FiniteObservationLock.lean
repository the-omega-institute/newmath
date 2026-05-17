import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_finite_observation_lock [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      observationRead extractionRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont schedule ledger observationRead →
        Cont schedule witness extractionRead →
          Cont observationRead trap sealRead →
            PkgSig bundle sealRead pkg →
              SemanticNameCert
                (fun row : BHist =>
                  hsame row sealRead ∧
                    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger
                      trap sealRow transport route provenance localCert bundle pkg)
                (fun row : BHist =>
                  Cont schedule ledger observationRead ∧
                    Cont schedule witness extractionRead ∧
                      Cont observationRead trap row ∧ PkgSig bundle sealRead pkg)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle sealRead pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier scheduleLedgerObservation scheduleWitnessExtraction observationTrapSeal sealPkg
  have carrierFull :
      BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg :=
    carrier
  obtain ⟨_sourceUnary, _regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    _sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, _provenancePkg⟩ := carrier
  have observationUnary : UnaryHistory observationRead :=
    unary_cont_closed scheduleUnary ledgerUnary scheduleLedgerObservation
  have _extractionUnary : UnaryHistory extractionRead :=
    unary_cont_closed scheduleUnary witnessUnary scheduleWitnessExtraction
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed observationUnary trapUnary observationTrapSeal
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead (And.intro (hsame_refl sealRead) carrierFull)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left) source.right
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨scheduleLedgerObservation, scheduleWitnessExtraction,
          cont_result_hsame_transport observationTrapSeal (hsame_symm source.left), sealPkg⟩
    ledger_sound := by
      intro _row source
      exact And.intro (unary_transport sealUnary (hsame_symm source.left)) sealPkg
  }

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
