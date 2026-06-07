import BEDC.Derived.ClosedTermSubstitutionBoundaryUp.RecognizerNonescape

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRecognizerStrictLocalObstruction [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit recognizer tupleImage tupleReadback
      consumer terminal obstruction : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont source value recognizer ->
            Cont recognizer ledger tupleImage ->
              Cont tupleImage audit tupleReadback ->
                Cont tupleReadback substitution consumer ->
                  Cont consumer audit terminal ->
                    Cont terminal recognizer obstruction ->
                      PkgSig bundle terminal pkg ->
                        PkgSig bundle obstruction pkg ->
                          SemanticNameCert (fun row : BHist => hsame row terminal)
                              (fun row : BHist =>
                                Cont consumer audit row ∧ PkgSig bundle terminal pkg)
                              (fun row : BHist =>
                                UnaryHistory row ∧ PkgSig bundle terminal pkg)
                              hsame ∧
                            UnaryHistory obstruction ∧ Cont terminal recognizer obstruction ∧
                              PkgSig bundle obstruction pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro classifier shiftSubstitutionLedger substitutionDepthAudit sourceValueRecognizer
    recognizerLedgerTuple tupleAuditReadback readbackSubstitutionConsumer consumerAuditTerminal
    terminalRecognizerObstruction terminalPkg obstructionPkg
  obtain ⟨cert, recognizerUnary, _tupleImageUnary, _tupleReadbackUnary, _consumerUnary,
    terminalUnary⟩ :=
    ClosedTermSubstitutionBoundarySubstitutionRecognizerNonescape
      classifier shiftSubstitutionLedger substitutionDepthAudit sourceValueRecognizer
      recognizerLedgerTuple tupleAuditReadback readbackSubstitutionConsumer consumerAuditTerminal
      terminalPkg
  have obstructionUnary : UnaryHistory obstruction :=
    unary_cont_closed terminalUnary recognizerUnary terminalRecognizerObstruction
  exact
    ⟨cert, obstructionUnary, terminalRecognizerObstruction, obstructionPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
