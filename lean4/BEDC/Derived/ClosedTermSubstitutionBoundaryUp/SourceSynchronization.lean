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

theorem ClosedTermSubstitutionBoundaryShiftSubstitutionSourceSynchronization
    [AskSetup] [PackageSetup]
    {source value depth sourceClosed valueClosed shift substitution ledger audit route syncRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont source depth sourceClosed ->
        Cont value depth valueClosed ->
          Cont sourceClosed shift ledger ->
            Cont sourceClosed substitution audit ->
              Cont ledger audit route ->
                Cont route valueClosed syncRead ->
                  PkgSig bundle syncRead pkg ->
                    UnaryHistory sourceClosed ∧ UnaryHistory valueClosed ∧
                      UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                        UnaryHistory syncRead ∧ Cont sourceClosed shift ledger ∧
                          Cont sourceClosed substitution audit ∧ PkgSig bundle syncRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro classifier sourceDepthClosed valueDepthClosed sourceShiftLedger sourceSubstitutionAudit
    ledgerAuditRoute routeValueSync syncPkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have sourceClosedUnary : UnaryHistory sourceClosed :=
    unary_cont_closed sourceUnary depthUnary sourceDepthClosed
  have valueClosedUnary : UnaryHistory valueClosed :=
    unary_cont_closed valueUnary depthUnary valueDepthClosed
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed sourceClosedUnary shiftUnary sourceShiftLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed sourceClosedUnary substitutionUnary sourceSubstitutionAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have syncUnary : UnaryHistory syncRead :=
    unary_cont_closed routeUnary valueClosedUnary routeValueSync
  exact
    ⟨sourceClosedUnary, valueClosedUnary, ledgerUnary, auditUnary, routeUnary, syncUnary,
      sourceShiftLedger, sourceSubstitutionAudit, syncPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
