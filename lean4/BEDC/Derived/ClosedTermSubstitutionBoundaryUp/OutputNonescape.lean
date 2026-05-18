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

theorem ClosedTermSubstitutionBoundaryOutputNonescape [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route recursorRead branchOutput auditRead
      outputRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit recursorRead ->
              Cont recursorRead substitution branchOutput ->
                Cont audit route auditRead ->
                  Cont branchOutput auditRead outputRead ->
                    PkgSig bundle branchOutput pkg ->
                      PkgSig bundle outputRead pkg ->
                        UnaryHistory branchOutput ∧ UnaryHistory auditRead ∧
                          UnaryHistory outputRead ∧ Cont recursorRead substitution branchOutput ∧
                            Cont audit route auditRead ∧
                              Cont branchOutput auditRead outputRead ∧
                                PkgSig bundle outputRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditRecursorRead recursorSubstitutionBranch auditRouteAuditRead branchAuditOutput
    _branchPkg outputPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have recursorUnary : UnaryHistory recursorRead :=
    unary_cont_closed routeUnary auditUnary routeAuditRecursorRead
  have branchUnary : UnaryHistory branchOutput :=
    unary_cont_closed recursorUnary substitutionUnary recursorSubstitutionBranch
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed auditUnary routeUnary auditRouteAuditRead
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed branchUnary auditReadUnary branchAuditOutput
  exact
    ⟨branchUnary, auditReadUnary, outputUnary, recursorSubstitutionBranch,
      auditRouteAuditRead, branchAuditOutput, outputPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
