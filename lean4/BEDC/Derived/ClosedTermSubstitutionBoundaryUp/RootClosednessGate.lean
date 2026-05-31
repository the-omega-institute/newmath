import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootClosednessGate [AskSetup] [PackageSetup]
    {source value depth shift substitution shiftRead substitutionRead ledger audit route rootRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont source value shiftRead ->
        Cont shiftRead depth substitutionRead ->
          Cont shift substitution ledger ->
            Cont substitutionRead depth audit ->
              Cont ledger audit route ->
                Cont route audit rootRead ->
                  PkgSig bundle rootRead pkg ->
                    hsame shiftRead shift ∧ hsame substitutionRead substitution ∧
                      UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                        UnaryHistory rootRead ∧ Cont shift substitution ledger ∧
                          Cont substitutionRead depth audit ∧ PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro classifier sourceValueShiftRead shiftReadDepthSubstitutionRead shiftSubstitutionLedger
    substitutionReadDepthAudit ledgerAuditRoute routeAuditRoot rootPkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary,
    sourceValueShift, shiftDepthSubstitution⟩ := classifier
  have sameShiftRead : hsame shiftRead shift :=
    cont_deterministic sourceValueShiftRead sourceValueShift
  have sameSubstitutionRead : hsame substitutionRead substitution :=
    cont_respects_hsame sameShiftRead (hsame_refl depth) shiftReadDepthSubstitutionRead
      shiftDepthSubstitution
  have shiftReadUnary : UnaryHistory shiftRead :=
    unary_cont_closed sourceUnary valueUnary sourceValueShiftRead
  have substitutionReadUnary : UnaryHistory substitutionRead :=
    unary_cont_closed shiftReadUnary depthUnary shiftReadDepthSubstitutionRead
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionReadUnary depthUnary substitutionReadDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary auditUnary routeAuditRoot
  exact
    ⟨sameShiftRead, sameSubstitutionRead, ledgerUnary, auditUnary, routeUnary,
      rootReadUnary, shiftSubstitutionLedger, substitutionReadDepthAudit, rootPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
