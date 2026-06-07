import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package

theorem ClosedTermSubstitutionBoundaryRouteDeterminacy [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route consumer rootRoute shiftRead
      substitutionRead operationRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont source value shiftRead ->
      Cont shiftRead depth substitutionRead ->
      Cont shift substitution ledger ->
      Cont substitution ledger audit ->
      Cont substitutionRead audit operationRead ->
      Cont ledger audit route ->
      Cont route audit consumer ->
      Cont consumer route rootRoute ->
      PkgSig bundle operationRead pkg ->
      PkgSig bundle rootRoute pkg ->
      hsame shiftRead shift ∧ hsame substitutionRead substitution ∧ UnaryHistory route ∧
        UnaryHistory consumer ∧ UnaryHistory rootRoute ∧ Cont ledger audit route ∧
        Cont route audit consumer ∧ Cont consumer route rootRoute ∧
        PkgSig bundle operationRead pkg ∧ PkgSig bundle rootRoute pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg
  intro classifier shiftReadLock substitutionReadLock ledgerLock auditLock operationReadLock
    routeLock consumerLock rootRouteLock operationPkg rootPkg
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
    unary_cont_closed substitutionUnary ledgerUnary auditLock
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary routeLock
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeUnary auditUnary consumerLock
  have rootRouteUnary : UnaryHistory rootRoute :=
    unary_cont_closed consumerUnary routeUnary rootRouteLock
  exact
    ⟨sameShift, sameSubstitution, routeUnary, consumerUnary, rootRouteUnary, routeLock,
      consumerLock, rootRouteLock, operationPkg, rootPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
