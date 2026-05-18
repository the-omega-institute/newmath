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

theorem ClosedTermSubstitutionBoundaryCompilerScheduleLock [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route compilerRead scheduleRead
      nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit compilerRead ->
              Cont compilerRead route scheduleRead ->
                Cont scheduleRead audit nameRead ->
                  PkgSig bundle nameRead pkg ->
                    UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                      UnaryHistory compilerRead ∧ UnaryHistory scheduleRead ∧
                        UnaryHistory nameRead ∧ Cont shift substitution ledger ∧
                          Cont substitution depth audit ∧ Cont ledger audit route ∧
                            Cont route audit compilerRead ∧
                              Cont compilerRead route scheduleRead ∧
                                Cont scheduleRead audit nameRead ∧
                                  PkgSig bundle nameRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditCompilerRead compilerReadRouteSchedule scheduleReadAuditName nameReadPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have compilerReadUnary : UnaryHistory compilerRead :=
    unary_cont_closed routeUnary auditUnary routeAuditCompilerRead
  have scheduleReadUnary : UnaryHistory scheduleRead :=
    unary_cont_closed compilerReadUnary routeUnary compilerReadRouteSchedule
  have nameReadUnary : UnaryHistory nameRead :=
    unary_cont_closed scheduleReadUnary auditUnary scheduleReadAuditName
  exact
    ⟨ledgerUnary, auditUnary, routeUnary, compilerReadUnary, scheduleReadUnary,
      nameReadUnary, shiftSubstitutionLedger, substitutionDepthAudit, ledgerAuditRoute,
      routeAuditCompilerRead, compilerReadRouteSchedule, scheduleReadAuditName, nameReadPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
