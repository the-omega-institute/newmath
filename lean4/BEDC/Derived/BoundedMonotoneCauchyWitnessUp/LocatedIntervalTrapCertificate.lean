import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_located_interval_trap_certificate
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      locatedRead certifiedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont ledger trap locatedRead ->
        Cont locatedRead transport certifiedRead ->
          PkgSig bundle certifiedRead pkg ->
            SemanticNameCert
              (fun row : BHist =>
                BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap
                    sealRow transport route provenance localCert bundle pkg ∧
                  Cont ledger trap locatedRead ∧ Cont locatedRead transport certifiedRead ∧
                    hsame row certifiedRead)
              (fun row : BHist =>
                Cont regular witness trap ∧ Cont ledger trap locatedRead ∧
                  Cont locatedRead transport row)
              (fun row : BHist =>
                UnaryHistory ledger ∧ UnaryHistory trap ∧ UnaryHistory row ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle certifiedRead pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier ledgerTrapLocated locatedTransportCertified certifiedPkg
  have sourceWitness :
      BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
          transport route provenance localCert bundle pkg ∧
        Cont ledger trap locatedRead ∧ Cont locatedRead transport certifiedRead ∧
          hsame certifiedRead certifiedRead :=
    ⟨carrier, ledgerTrapLocated, locatedTransportCertified, hsame_refl certifiedRead⟩
  obtain ⟨_sourceUnary, regularUnary, _scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    transportLocalRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed trapUnary sealUnary trapSealRoute
  have transportUnary : UnaryHistory transport :=
    (unary_cont_factors_from_result transportLocalRoute routeUnary).left
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed ledgerUnary trapUnary ledgerTrapLocated
  have certifiedUnary : UnaryHistory certifiedRead :=
    unary_cont_closed locatedUnary transportUnary locatedTransportCertified
  exact {
    core := {
      carrier_inhabited := Exists.intro certifiedRead sourceWitness
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
        exact
          ⟨source.left, source.right.left, source.right.right.left,
            hsame_trans (hsame_symm sameRows) source.right.right.right⟩
    }
    pattern_sound := by
      intro row source
      exact
        ⟨regularWitnessTrap, source.right.left,
          cont_result_hsame_transport source.right.right.left
            (hsame_symm source.right.right.right)⟩
    ledger_sound := by
      intro row source
      exact
        ⟨ledgerUnary, trapUnary,
          unary_transport certifiedUnary (hsame_symm source.right.right.right),
          provenancePkg, certifiedPkg⟩
  }

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
