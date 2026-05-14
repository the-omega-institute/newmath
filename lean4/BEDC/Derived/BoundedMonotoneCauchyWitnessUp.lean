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

theorem BoundedMonotoneCauchyWitnessCarrier_convergence_seal_source [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance
      localCert convergenceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont sealRow provenance convergenceRead ->
        PkgSig bundle convergenceRead pkg ->
          UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
            UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
              UnaryHistory sealRow ∧ UnaryHistory provenance ∧
                UnaryHistory convergenceRead ∧ Cont source schedule regular ∧
                  Cont regular witness trap ∧ Cont trap sealRow route ∧
                    Cont sealRow provenance convergenceRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle convergenceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier convergenceRoute convergencePkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have convergenceUnary : UnaryHistory convergenceRead :=
    unary_cont_closed sealUnary provenanceUnary convergenceRoute
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      provenanceUnary, convergenceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
      convergenceRoute, provenancePkg, convergencePkg⟩

theorem BoundedMonotoneCauchyWitnessCarrier_completion_consumer_nonescape [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      envelopeRead finiteRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule envelopeRead →
        Cont envelopeRead regular finiteRead →
          Cont finiteRead sealRow completionRead →
            PkgSig bundle completionRead pkg →
              UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
                UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                  UnaryHistory sealRow ∧ UnaryHistory provenance ∧ UnaryHistory envelopeRead ∧
                    UnaryHistory finiteRead ∧ UnaryHistory completionRead ∧
                      Cont source schedule envelopeRead ∧
                        Cont envelopeRead regular finiteRead ∧
                          Cont finiteRead sealRow completionRead ∧
                            Cont source schedule regular ∧ Cont regular witness trap ∧
                              Cont trap sealRow route ∧ PkgSig bundle provenance pkg ∧
                                PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier envelopeRoute finiteRoute completionRoute completionPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have envelopeUnary : UnaryHistory envelopeRead :=
    unary_cont_closed sourceUnary scheduleUnary envelopeRoute
  have finiteUnary : UnaryHistory finiteRead :=
    unary_cont_closed envelopeUnary regularUnary finiteRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed finiteUnary sealUnary completionRoute
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      provenanceUnary, envelopeUnary, finiteUnary, completionUnary, envelopeRoute, finiteRoute,
      completionRoute, sourceScheduleRegular, regularWitnessTrap, trapSealRoute, provenancePkg,
      completionPkg⟩

theorem BoundedMonotoneCauchyWitnessCarrier_root_extraction [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source regular rootRead →
        Cont rootRead witness sealRow →
          PkgSig bundle rootRead pkg →
            UnaryHistory source ∧ UnaryHistory regular ∧ UnaryHistory schedule ∧
              UnaryHistory witness ∧ UnaryHistory ledger ∧ UnaryHistory trap ∧
                UnaryHistory sealRow ∧ UnaryHistory provenance ∧ UnaryHistory rootRead ∧
                  Cont source regular rootRead ∧ Cont rootRead witness sealRow ∧
                    Cont trap sealRow route ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceRegularRoot rootWitnessSeal rootPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed sourceUnary regularUnary sourceRegularRoot
  exact
    ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary, sealUnary,
      provenanceUnary, rootUnary, sourceRegularRoot, rootWitnessSeal, trapSealRoute,
      provenancePkg, rootPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
