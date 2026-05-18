import BEDC.Derived.ClosedTermSubstitutionBoundaryUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundarySubstitutionFreeVariableNonescape
    [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route consumer hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit consumer ->
              PkgSig bundle consumer pkg ->
                UnaryHistory substitution ∧ UnaryHistory ledger ∧ UnaryHistory audit ∧
                  UnaryHistory route ∧ UnaryHistory consumer ∧
                    Cont shift substitution ledger ∧ Cont substitution depth audit ∧
                      Cont ledger audit route ∧ Cont route audit consumer ∧
                        PkgSig bundle consumer pkg ∧
                          (Cont consumer (BHist.e0 hostTail) route -> False) ∧
                            (Cont consumer (BHist.e1 hostTail) route -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditConsumer consumerPkg
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
  exact
    ⟨substitutionUnary, ledgerUnary, auditUnary, routeUnary, consumerUnary,
      shiftSubstitutionLedger, substitutionDepthAudit, ledgerAuditRoute, routeAuditConsumer,
      consumerPkg,
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.left routeAuditConsumer hostReturn),
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.right routeAuditConsumer hostReturn)⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
