import BEDC.Derived.ClosedTermSubstitutionBoundaryUp
import BEDC.FKernel.Sig

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryFiniteTupleReadback [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit recognizer tupleImage tupleReadback
      shiftRead substitutionRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont source value recognizer ->
            Cont recognizer ledger tupleImage ->
              Cont tupleImage audit tupleReadback ->
                Cont source value shiftRead ->
                  Cont shiftRead depth substitutionRead ->
                    Cont tupleReadback substitution consumer ->
                      PkgSig bundle consumer pkg ->
                        hsame shiftRead shift ∧ hsame substitutionRead substitution ∧
                          UnaryHistory recognizer ∧ UnaryHistory tupleImage ∧
                            UnaryHistory tupleReadback ∧ UnaryHistory consumer ∧
                              Cont tupleImage audit tupleReadback ∧
                                Cont tupleReadback substitution consumer ∧
                                  PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro classifier shiftSubstitutionLedger substitutionDepthAudit sourceValueRecognizer
    recognizerLedgerTuple tupleAuditReadback sourceValueShiftRead shiftReadDepthSubstitutionRead
    readbackSubstitutionConsumer consumerPkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary,
    sourceValueShift, shiftDepthSubstitution⟩ := classifier
  have shiftReadSame : hsame shiftRead shift :=
    cont_deterministic sourceValueShiftRead sourceValueShift
  have substitutionReadSame : hsame substitutionRead substitution :=
    cont_respects_hsame shiftReadSame (hsame_refl depth) shiftReadDepthSubstitutionRead
      shiftDepthSubstitution
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
  exact
    ⟨shiftReadSame, substitutionReadSame, recognizerUnary, tupleImageUnary,
      tupleReadbackUnary, consumerUnary, tupleAuditReadback, readbackSubstitutionConsumer,
      consumerPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
