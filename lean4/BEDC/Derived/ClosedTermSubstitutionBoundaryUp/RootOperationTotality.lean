import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootOperationTotality [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route shiftRead substitutionRead
      rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont source value shiftRead ->
        Cont shiftRead depth substitutionRead ->
          Cont shift substitution ledger ->
            Cont substitution depth audit ->
              Cont ledger audit route ->
                Cont route audit rootRead ->
                  PkgSig bundle rootRead pkg ->
                    hsame shiftRead shift ∧ hsame substitutionRead substitution ∧
                      UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                        UnaryHistory rootRead ∧ PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory PkgSig
  intro classifier sourceValueShiftRead shiftReadDepthSubstitutionRead shiftSubstitutionLedger
    substitutionDepthAudit ledgerAuditRoute routeAuditRoot rootPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    sourceValueShift, shiftDepthSubstitution⟩ := classifier
  have sameShift : hsame shiftRead shift :=
    cont_deterministic sourceValueShiftRead sourceValueShift
  have sameSubstitution : hsame substitutionRead substitution := by
    exact cont_respects_hsame sameShift (hsame_refl depth) shiftReadDepthSubstitutionRead
      shiftDepthSubstitution
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary auditUnary routeAuditRoot
  exact
    ⟨sameShift, sameSubstitution, ledgerUnary, auditUnary, routeUnary, rootUnary, rootPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
