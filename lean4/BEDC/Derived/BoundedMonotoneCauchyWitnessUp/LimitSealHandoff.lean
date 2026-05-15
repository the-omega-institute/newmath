import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_limit_seal_handoff [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      windowRead tailRead sealRead limitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule windowRead →
        Cont windowRead witness tailRead →
          Cont tailRead trap sealRead →
            Cont sealRead provenance limitRead →
              PkgSig bundle limitRead pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row sealRow ∧
                        BoundedMonotoneCauchyWitnessCarrier source regular schedule witness
                          ledger trap sealRow transport route provenance localCert bundle pkg)
                    (fun row : BHist => hsame row sealRow ∧ UnaryHistory row)
                    (fun _row : BHist =>
                      Cont source schedule windowRead ∧ Cont sealRead provenance limitRead ∧
                        PkgSig bundle provenance pkg)
                    hsame ∧
                  UnaryHistory windowRead ∧ UnaryHistory tailRead ∧ UnaryHistory sealRead ∧
                    UnaryHistory limitRead ∧ Cont source schedule windowRead ∧
                      Cont windowRead witness tailRead ∧ Cont tailRead trap sealRead ∧
                        Cont sealRead provenance limitRead ∧ PkgSig bundle limitRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier sourceScheduleWindow windowWitnessTail tailTrapSeal sealProvenanceLimit
    limitPkg
  have carrierFull :
      BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg :=
    carrier
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, _ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleWindow
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed windowUnary witnessUnary windowWitnessTail
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary trapUnary tailTrapSeal
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed sealReadUnary provenanceUnary sealProvenanceLimit
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
          (fun row : BHist => hsame row sealRow ∧ UnaryHistory row)
          (fun _row : BHist =>
            Cont source schedule windowRead ∧ Cont sealRead provenance limitRead ∧
              PkgSig bundle provenance pkg)
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
      exact And.intro source.left (unary_transport_symm sealUnary source.left)
    ledger_sound := by
      intro _row _source
      exact And.intro sourceScheduleWindow
        (And.intro sealProvenanceLimit provenancePkg)
  }
  exact
    ⟨cert, windowUnary, tailUnary, sealReadUnary, limitUnary, sourceScheduleWindow,
      windowWitnessTail, tailTrapSeal, sealProvenanceLimit, limitPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
