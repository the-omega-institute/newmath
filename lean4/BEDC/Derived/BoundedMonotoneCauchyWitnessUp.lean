import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BoundedMonotoneCauchyWitnessCarrier [AskSetup] [PackageSetup]
    (source regular schedule witness ledger trap sealRow transport route provenance
      localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
    UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
      UnaryHistory sealRow ∧ UnaryHistory provenance ∧ Cont source schedule regular ∧
        Cont regular witness trap ∧ Cont trap sealRow route ∧ Cont transport localCert route ∧
          Cont route provenance sealRow ∧ PkgSig bundle provenance pkg

theorem BoundedMonotoneCauchyWitnessCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance
      localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row sealRow ∧
              BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap
                sealRow transport route provenance localCert bundle pkg)
          (fun row : BHist =>
            hsame row sealRow ∧ UnaryHistory regular ∧ UnaryHistory witness ∧ UnaryHistory trap)
          (fun row : BHist => hsame row sealRow ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
          UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧ UnaryHistory sealRow ∧
            Cont source schedule regular ∧ Cont regular witness trap ∧ Cont trap sealRow route ∧
              PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont PkgSig SemanticNameCert hsame
  intro carrier
  have carrierFull :
      BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg :=
    carrier
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, pkgSig⟩ := carrier
  have sourceAtSeal :
      hsame sealRow sealRow ∧
        BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
          transport route provenance localCert bundle pkg :=
    And.intro (hsame_refl sealRow) carrierFull
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row sealRow ∧
              BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap
                sealRow transport route provenance localCert bundle pkg)
          (fun row : BHist =>
            hsame row sealRow ∧ UnaryHistory regular ∧ UnaryHistory witness ∧ UnaryHistory trap)
          (fun row : BHist => hsame row sealRow ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRow sourceAtSeal
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
        constructor
        · exact hsame_trans (hsame_symm sameRows) source.left
        · exact source.right
    }
    pattern_sound := by
      intro row source
      exact And.intro source.left
        (And.intro regularUnary (And.intro witnessUnary trapUnary))
    ledger_sound := by
      intro row source
      exact And.intro source.left pkgSig
  }
  exact And.intro cert
    (And.intro sourceUnary
      (And.intro regularUnary
        (And.intro scheduleUnary
          (And.intro witnessUnary
            (And.intro ledgerUnary
              (And.intro trapUnary
                (And.intro sealUnary
                  (And.intro sourceScheduleRegular
                    (And.intro regularWitnessTrap
                      (And.intro trapSealRoute pkgSig))))))))))

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
