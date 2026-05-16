import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_window_seal_readback_completeness
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      windowRead tailRead criterionRead realRead completionRead finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule windowRead →
        Cont windowRead ledger tailRead →
          Cont tailRead witness criterionRead →
            Cont criterionRead sealRow realRead →
              Cont realRead provenance completionRead →
                Cont completionRead localCert finalRead →
                  PkgSig bundle finalRead pkg →
                    SemanticNameCert
                        (fun row : BHist =>
                          hsame row finalRead ∧
                            BoundedMonotoneCauchyWitnessCarrier source regular schedule witness
                              ledger trap sealRow transport route provenance localCert bundle pkg)
                        (fun row : BHist =>
                          Cont source schedule windowRead ∧
                            Cont windowRead ledger tailRead ∧
                              Cont tailRead witness criterionRead ∧
                                Cont criterionRead sealRow realRead ∧
                                  Cont realRead provenance completionRead ∧
                                    Cont completionRead localCert row ∧
                                      PkgSig bundle finalRead pkg)
                        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle finalRead pkg)
                        hsame ∧
                      UnaryHistory windowRead ∧ UnaryHistory tailRead ∧
                        UnaryHistory criterionRead ∧ UnaryHistory realRead ∧
                          UnaryHistory completionRead ∧ UnaryHistory finalRead ∧
                            Cont source schedule windowRead ∧
                              Cont windowRead ledger tailRead ∧
                                Cont tailRead witness criterionRead ∧
                                  Cont criterionRead sealRow realRead ∧
                                    Cont realRead provenance completionRead ∧
                                      Cont completionRead localCert finalRead ∧
                                        PkgSig bundle finalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro carrier sourceScheduleWindow windowLedgerTail tailWitnessCriterion criterionSealReal
    realProvenanceCompletion completionLocalFinal finalPkg
  have carrierFull :
      BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg :=
    carrier
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, trapSealRoute,
    transportLocalRoute, _routeProvenanceSeal, _provenancePkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleWindow
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed windowUnary ledgerUnary windowLedgerTail
  have criterionUnary : UnaryHistory criterionRead :=
    unary_cont_closed tailUnary witnessUnary tailWitnessCriterion
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed criterionUnary sealUnary criterionSealReal
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed realUnary provenanceUnary realProvenanceCompletion
  have routeUnary : UnaryHistory route :=
    unary_cont_closed trapUnary sealUnary trapSealRoute
  have localCertUnary : UnaryHistory localCert :=
    (unary_cont_factors_from_result transportLocalRoute routeUnary).right
  have finalUnary : UnaryHistory finalRead :=
    unary_cont_closed completionUnary localCertUnary completionLocalFinal
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row finalRead ∧
              BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap
                sealRow transport route provenance localCert bundle pkg)
          (fun row : BHist =>
            Cont source schedule windowRead ∧
              Cont windowRead ledger tailRead ∧
                Cont tailRead witness criterionRead ∧
                  Cont criterionRead sealRow realRead ∧
                    Cont realRead provenance completionRead ∧
                      Cont completionRead localCert row ∧
                        PkgSig bundle finalRead pkg)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle finalRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro finalRead
          (And.intro (hsame_refl finalRead) carrierFull)
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
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left) source.right
    }
    pattern_sound := by
      intro row source
      exact
        ⟨sourceScheduleWindow, windowLedgerTail, tailWitnessCriterion, criterionSealReal,
          realProvenanceCompletion,
          cont_result_hsame_transport completionLocalFinal (hsame_symm source.left), finalPkg⟩
    ledger_sound := by
      intro row source
      exact And.intro (unary_transport finalUnary (hsame_symm source.left)) finalPkg
  }
  exact
    ⟨cert, windowUnary, tailUnary, criterionUnary, realUnary, completionUnary, finalUnary,
      sourceScheduleWindow, windowLedgerTail, tailWitnessCriterion, criterionSealReal,
      realProvenanceCompletion, completionLocalFinal, finalPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
