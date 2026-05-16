import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_scoped_dependency_package [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      dependencyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont regular witness trap ->
        Cont trap sealRow route ->
          Cont route provenance dependencyRead ->
            PkgSig bundle dependencyRead pkg ->
              SemanticNameCert
                (fun row : BHist =>
                  BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap
                    sealRow transport route provenance localCert bundle pkg ∧
                    hsame row dependencyRead)
                (fun row : BHist =>
                  Cont regular witness trap ∧ Cont trap sealRow route ∧
                    Cont route provenance row ∧ PkgSig bundle dependencyRead pkg)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle dependencyRead pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier regularWitnessTrap trapSealRoute routeProvenanceRead dependencyPkg
  rcases carrier with
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
      sealUnary, provenanceUnary, sourceScheduleRegular, _carrierRegularWitnessTrap,
      _carrierTrapSealRoute, transportLocalCertRoute, routeProvenanceSeal,
      provenancePkg⟩
  have routeUnary : UnaryHistory route :=
    unary_cont_closed trapUnary sealUnary trapSealRoute
  have dependencyUnary : UnaryHistory dependencyRead :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceRead
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro dependencyRead
          (And.intro
            ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
              sealUnary, provenanceUnary, sourceScheduleRegular, regularWitnessTrap,
              trapSealRoute, transportLocalCertRoute, routeProvenanceSeal, provenancePkg⟩
            (hsame_refl dependencyRead))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact
        ⟨regularWitnessTrap, trapSealRoute,
          cont_result_hsame_transport routeProvenanceRead (hsame_symm source.right),
          dependencyPkg⟩
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport dependencyUnary (hsame_symm source.right), provenancePkg,
          dependencyPkg⟩
  }

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
