import BEDC.Derived.ClosedtermsubstitutionboundaryUp.RouteDeterminacy

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package

theorem ClosedTermSubstitutionBoundaryContextStackNonescape [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit recognizer tupleImage tupleReadback
      shiftRead substitutionRead consumer auditReplay publicRead : BHist}
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
      Cont audit tupleReadback auditReplay ->
      Cont auditReplay consumer publicRead ->
      PkgSig bundle publicRead pkg ->
      hsame shiftRead shift ∧ hsame substitutionRead substitution ∧ UnaryHistory recognizer ∧
        UnaryHistory tupleImage ∧ UnaryHistory tupleReadback ∧ UnaryHistory consumer ∧
        UnaryHistory auditReplay ∧ UnaryHistory publicRead ∧ Cont tupleImage audit tupleReadback ∧
        Cont tupleReadback substitution consumer ∧ Cont auditReplay consumer publicRead ∧
        PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg
  intro classifier ledgerLock auditLock recognizerLock tupleImageLock tupleReadbackLock
    shiftReadLock substitutionReadLock consumerLock auditReplayLock publicReadLock publicPkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary,
    sourceValueShift, shiftDepthSubstitution⟩ := classifier
  have sameShift : hsame shiftRead shift :=
    cont_deterministic shiftReadLock sourceValueShift
  have sameSubstitution : hsame substitutionRead substitution :=
    cont_respects_hsame sameShift (hsame_refl depth) substitutionReadLock
      shiftDepthSubstitution
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary ledgerLock
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary auditLock
  have recognizerUnary : UnaryHistory recognizer :=
    unary_cont_closed sourceUnary valueUnary recognizerLock
  have tupleImageUnary : UnaryHistory tupleImage :=
    unary_cont_closed recognizerUnary ledgerUnary tupleImageLock
  have tupleReadbackUnary : UnaryHistory tupleReadback :=
    unary_cont_closed tupleImageUnary auditUnary tupleReadbackLock
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed tupleReadbackUnary substitutionUnary consumerLock
  have auditReplayUnary : UnaryHistory auditReplay :=
    unary_cont_closed auditUnary tupleReadbackUnary auditReplayLock
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed auditReplayUnary consumerUnary publicReadLock
  exact
    ⟨sameShift, sameSubstitution, recognizerUnary, tupleImageUnary, tupleReadbackUnary,
      consumerUnary, auditReplayUnary, publicReadUnary, tupleReadbackLock, consumerLock,
      publicReadLock, publicPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
