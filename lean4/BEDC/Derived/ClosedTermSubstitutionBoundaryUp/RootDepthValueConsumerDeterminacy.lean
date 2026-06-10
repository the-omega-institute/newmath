import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootDepthValueConsumerDeterminacy [AskSetup]
    [PackageSetup]
    {source value depth shift substitution ledger audit route rootRead shiftRead substitutionRead
      bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont source value shiftRead ->
        Cont shiftRead depth substitutionRead ->
          Cont shift substitution ledger ->
            Cont substitution depth audit ->
              Cont ledger audit route ->
                Cont route audit rootRead ->
                  Cont source depth bridgeRead ->
                    PkgSig bundle rootRead pkg ->
                      hsame shiftRead shift ∧ hsame substitutionRead substitution ∧
                        UnaryHistory rootRead ∧ UnaryHistory bridgeRead ∧
                          Cont source depth bridgeRead ∧ PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: ClosedTermSubstitutionBoundaryClassifier BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro classifier sourceValueShiftRead shiftReadDepthSubstitutionRead shiftSubstitutionLedger
    substitutionDepthAudit ledgerAuditRoute routeAuditRoot sourceDepthBridge rootPkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary,
    sourceValueShift, shiftDepthSubstitution⟩ := classifier
  have sameShiftRead : hsame shiftRead shift :=
    cont_deterministic sourceValueShiftRead sourceValueShift
  have sameSubstitutionRead : hsame substitutionRead substitution :=
    cont_respects_hsame sameShiftRead (hsame_refl depth) shiftReadDepthSubstitutionRead
      shiftDepthSubstitution
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary auditUnary routeAuditRoot
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed sourceUnary depthUnary sourceDepthBridge
  exact
    ⟨sameShiftRead, sameSubstitutionRead, rootUnary, bridgeUnary, sourceDepthBridge,
      rootPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
