import BEDC.Derived.ClosedTermSubstitutionBoundaryUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem ClosedTermSubstitutionBoundaryRootUnblockCertificate [AskSetup] [PackageSetup]
    {source value depth shift substitution sourceClosed valueClosed ledger audit route consumer
      compilerRead unblock : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont source value sourceClosed ->
        Cont value depth valueClosed ->
          Cont sourceClosed valueClosed ledger ->
            Cont substitution depth audit ->
              Cont ledger audit route ->
                Cont route audit consumer ->
                  Cont consumer route compilerRead ->
                    Cont compilerRead audit unblock ->
                      PkgSig bundle unblock pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row unblock)
                            (fun row : BHist =>
                              Cont compilerRead audit row ∧ PkgSig bundle unblock pkg)
                            (fun row : BHist =>
                              UnaryHistory row ∧ PkgSig bundle unblock pkg)
                            hsame ∧
                          UnaryHistory sourceClosed ∧ UnaryHistory valueClosed ∧
                            UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                              UnaryHistory consumer ∧ UnaryHistory compilerRead ∧
                                UnaryHistory unblock := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro classifier sourceValueClosed valueDepthClosed closedLedger substitutionDepthAudit
    ledgerAuditRoute routeAuditConsumer consumerRouteCompiler compilerAuditUnblock
    unblockPkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, _shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have sourceClosedUnary : UnaryHistory sourceClosed :=
    unary_cont_closed sourceUnary valueUnary sourceValueClosed
  have valueClosedUnary : UnaryHistory valueClosed :=
    unary_cont_closed valueUnary depthUnary valueDepthClosed
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed sourceClosedUnary valueClosedUnary closedLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeUnary auditUnary routeAuditConsumer
  have compilerUnary : UnaryHistory compilerRead :=
    unary_cont_closed consumerUnary routeUnary consumerRouteCompiler
  have unblockUnary : UnaryHistory unblock :=
    unary_cont_closed compilerUnary auditUnary compilerAuditUnblock
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro unblock (hsame_refl unblock)
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
          ⟨cont_result_hsame_transport compilerAuditUnblock (hsame_symm source),
            unblockPkg⟩
      ledger_sound := by
        intro _row source
        exact ⟨unary_transport unblockUnary (hsame_symm source), unblockPkg⟩
    }
  · exact
      ⟨sourceClosedUnary, valueClosedUnary, ledgerUnary, auditUnary, routeUnary,
        consumerUnary, compilerUnary, unblockUnary⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
