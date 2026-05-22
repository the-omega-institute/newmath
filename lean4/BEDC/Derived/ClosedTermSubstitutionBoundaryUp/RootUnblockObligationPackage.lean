import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootUnblockObligationPackage [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route shiftScope substitutionScope
      rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont source shift shiftScope ->
        Cont value substitution substitutionScope ->
          Cont shift substitution ledger ->
            Cont substitution depth audit ->
              Cont ledger audit route ->
                Cont route audit rootRead ->
                  PkgSig bundle rootRead pkg ->
                    UnaryHistory shiftScope /\ UnaryHistory substitutionScope /\
                      UnaryHistory ledger /\ UnaryHistory audit /\ UnaryHistory route /\
                        UnaryHistory rootRead /\ Cont shift substitution ledger /\
                          Cont substitution depth audit /\ Cont ledger audit route /\
                            Cont route audit rootRead /\ PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro classifier sourceShiftScope valueSubstitutionScope shiftSubstitutionLedger
    substitutionDepthAudit ledgerAuditRoute routeAuditRoot rootPkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have shiftScopeUnary : UnaryHistory shiftScope :=
    unary_cont_closed sourceUnary shiftUnary sourceShiftScope
  have substitutionScopeUnary : UnaryHistory substitutionScope :=
    unary_cont_closed valueUnary substitutionUnary valueSubstitutionScope
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary auditUnary routeAuditRoot
  exact
    ⟨shiftScopeUnary, substitutionScopeUnary, ledgerUnary, auditUnary, routeUnary, rootUnary,
      shiftSubstitutionLedger, substitutionDepthAudit, ledgerAuditRoute, routeAuditRoot,
      rootPkg⟩

theorem ClosedTermSubstitutionBoundaryRootShiftScope [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route shiftScope rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont source shift shiftScope ->
        Cont shift substitution ledger ->
          Cont substitution depth audit ->
            Cont ledger audit route ->
              Cont route audit rootRead ->
                PkgSig bundle rootRead pkg ->
                  UnaryHistory shiftScope ∧ UnaryHistory ledger ∧ UnaryHistory audit ∧
                    UnaryHistory route ∧ UnaryHistory rootRead ∧ Cont source shift shiftScope ∧
                      Cont shift substitution ledger ∧ Cont ledger audit route ∧
                        PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro classifier sourceShiftScope shiftSubstitutionLedger substitutionDepthAudit
    ledgerAuditRoute routeAuditRoot rootPkg
  obtain ⟨sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have shiftScopeUnary : UnaryHistory shiftScope :=
    unary_cont_closed sourceUnary shiftUnary sourceShiftScope
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary auditUnary routeAuditRoot
  exact
    ⟨shiftScopeUnary, ledgerUnary, auditUnary, routeUnary, rootUnary, sourceShiftScope,
      shiftSubstitutionLedger, ledgerAuditRoute, rootPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
