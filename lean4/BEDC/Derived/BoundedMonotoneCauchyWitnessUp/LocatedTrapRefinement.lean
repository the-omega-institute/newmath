import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_located_trap_refinement
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance
      localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap
              sealRow transport route provenance localCert bundle pkg ∧
            hsame row trap)
        (fun row : BHist => UnaryHistory source ∧ UnaryHistory ledger ∧ hsame row trap)
        (fun _row : BHist =>
          Cont source schedule regular ∧ Cont regular witness trap ∧
            Cont trap sealRow route ∧ PkgSig bundle provenance pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier
  rcases carrier with
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
      sealUnary, provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
      transportLocalCertRoute, routeProvenanceSeal, provenancePkg⟩
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro trap
          (And.intro
            ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
              sealUnary, provenanceUnary, sourceScheduleRegular, regularWitnessTrap,
              trapSealRoute, transportLocalCertRoute, routeProvenanceSeal, provenancePkg⟩
            (hsame_refl trap))
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact ⟨sourceUnary, ledgerUnary, source.right⟩
    ledger_sound := by
      intro _row _source
      exact ⟨sourceScheduleRegular, regularWitnessTrap, trapSealRoute, provenancePkg⟩
  }

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
