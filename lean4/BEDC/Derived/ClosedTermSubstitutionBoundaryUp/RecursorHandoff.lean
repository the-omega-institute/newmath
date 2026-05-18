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

theorem ClosedTermSubstitutionBoundaryRecursorHandoff [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route recursorRead branchOutput : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit recursorRead ->
              Cont recursorRead substitution branchOutput ->
                PkgSig bundle branchOutput pkg ->
                  UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                    UnaryHistory recursorRead ∧ UnaryHistory branchOutput ∧
                      Cont shift substitution ledger ∧ Cont substitution depth audit ∧
                        Cont ledger audit route ∧ Cont route audit recursorRead ∧
                          Cont recursorRead substitution branchOutput ∧
                            PkgSig bundle branchOutput pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditRecursorRead recursorReadSubstitutionBranchOutput branchOutputPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have recursorReadUnary : UnaryHistory recursorRead :=
    unary_cont_closed routeUnary auditUnary routeAuditRecursorRead
  have branchOutputUnary : UnaryHistory branchOutput :=
    unary_cont_closed recursorReadUnary substitutionUnary recursorReadSubstitutionBranchOutput
  exact
    ⟨ledgerUnary, auditUnary, routeUnary, recursorReadUnary, branchOutputUnary,
      shiftSubstitutionLedger, substitutionDepthAudit, ledgerAuditRoute, routeAuditRecursorRead,
      recursorReadSubstitutionBranchOutput, branchOutputPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
