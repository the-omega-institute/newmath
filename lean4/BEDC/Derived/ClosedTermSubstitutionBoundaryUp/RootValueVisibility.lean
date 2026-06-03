import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootValueVisibility [AskSetup] [PackageSetup]
    {source value depth shift substitution sourceClosed valueClosed ledger audit route consumer :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont source value sourceClosed ->
        Cont value depth valueClosed ->
          Cont sourceClosed valueClosed ledger ->
            Cont substitution depth audit ->
              Cont ledger audit route ->
                Cont route audit consumer ->
                  PkgSig bundle consumer pkg ->
                    UnaryHistory source ∧ UnaryHistory value ∧ UnaryHistory depth ∧
                      UnaryHistory sourceClosed ∧ UnaryHistory valueClosed ∧
                        UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                          UnaryHistory consumer ∧ Cont source value sourceClosed ∧
                            Cont value depth valueClosed ∧
                              Cont sourceClosed valueClosed ledger ∧
                                Cont substitution depth audit ∧ Cont ledger audit route ∧
                                  Cont route audit consumer ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro classifier sourceValueClosed valueDepthClosed sourceClosedValueClosedLedger
    substitutionDepthAudit ledgerAuditRoute routeAuditConsumer consumerPkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, _shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have sourceClosedUnary : UnaryHistory sourceClosed :=
    unary_cont_closed sourceUnary valueUnary sourceValueClosed
  have valueClosedUnary : UnaryHistory valueClosed :=
    unary_cont_closed valueUnary depthUnary valueDepthClosed
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed sourceClosedUnary valueClosedUnary sourceClosedValueClosedLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeUnary auditUnary routeAuditConsumer
  exact
    ⟨sourceUnary, valueUnary, depthUnary, sourceClosedUnary, valueClosedUnary,
      ledgerUnary, auditUnary, routeUnary, consumerUnary, sourceValueClosed,
      valueDepthClosed, sourceClosedValueClosedLedger, substitutionDepthAudit,
      ledgerAuditRoute, routeAuditConsumer, consumerPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
