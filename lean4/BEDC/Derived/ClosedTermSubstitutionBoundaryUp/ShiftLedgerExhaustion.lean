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

theorem ClosedTermSubstitutionBoundaryShiftLedgerExhaustion [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route consumer shiftBudget : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit consumer ->
              Cont shift ledger shiftBudget ->
                PkgSig bundle shiftBudget pkg ->
                  PkgSig bundle consumer pkg ->
                    UnaryHistory shiftBudget ∧ Cont shift ledger shiftBudget ∧
                      UnaryHistory consumer ∧ PkgSig bundle shiftBudget pkg ∧
                        PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditConsumer shiftLedgerBudget shiftBudgetPkg consumerPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeUnary auditUnary routeAuditConsumer
  have shiftBudgetUnary : UnaryHistory shiftBudget :=
    unary_cont_closed shiftUnary ledgerUnary shiftLedgerBudget
  exact ⟨shiftBudgetUnary, shiftLedgerBudget, consumerUnary, shiftBudgetPkg, consumerPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
