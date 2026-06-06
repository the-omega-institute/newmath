import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundarySubstitutionRecognizerNonescape [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit recognizer tupleImage tupleReadback
      consumer terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution →
      Cont shift substitution ledger →
        Cont substitution depth audit →
          Cont source value recognizer →
            Cont recognizer ledger tupleImage →
              Cont tupleImage audit tupleReadback →
                Cont tupleReadback substitution consumer →
                  Cont consumer audit terminal →
                    PkgSig bundle terminal pkg →
                      SemanticNameCert (fun row : BHist => hsame row terminal)
                          (fun row : BHist =>
                            Cont consumer audit row ∧ PkgSig bundle terminal pkg)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle terminal pkg)
                          hsame ∧
                        UnaryHistory recognizer ∧ UnaryHistory tupleImage ∧
                          UnaryHistory tupleReadback ∧ UnaryHistory consumer ∧
                            UnaryHistory terminal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro classifier shiftSubstitutionLedger substitutionDepthAudit sourceValueRecognizer
    recognizerLedgerTuple tupleAuditReadback readbackSubstitutionConsumer consumerAuditTerminal
    terminalPkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have recognizerUnary : UnaryHistory recognizer :=
    unary_cont_closed sourceUnary valueUnary sourceValueRecognizer
  have tupleImageUnary : UnaryHistory tupleImage :=
    unary_cont_closed recognizerUnary ledgerUnary recognizerLedgerTuple
  have tupleReadbackUnary : UnaryHistory tupleReadback :=
    unary_cont_closed tupleImageUnary auditUnary tupleAuditReadback
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed tupleReadbackUnary substitutionUnary readbackSubstitutionConsumer
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed consumerUnary auditUnary consumerAuditTerminal
  have cert :
      SemanticNameCert (fun row : BHist => hsame row terminal)
          (fun row : BHist => Cont consumer audit row ∧ PkgSig bundle terminal pkg)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle terminal pkg) hsame := {
    core := {
      carrier_inhabited := Exists.intro terminal (hsame_refl terminal)
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
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨cont_result_hsame_transport consumerAuditTerminal (hsame_symm source),
          terminalPkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport terminalUnary (hsame_symm source), terminalPkg⟩
  }
  exact
    ⟨cert, recognizerUnary, tupleImageUnary, tupleReadbackUnary, consumerUnary,
      terminalUnary⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
