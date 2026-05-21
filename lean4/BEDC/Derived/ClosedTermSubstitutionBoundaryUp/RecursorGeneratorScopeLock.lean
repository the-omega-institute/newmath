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

theorem ClosedTermSubstitutionBoundaryRecursorGeneratorScopeLock [AskSetup] [PackageSetup]
    {source value depth shift substitution sourceClosed valueClosed ledger audit route recursorRead
      scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont source value sourceClosed ->
        Cont value depth valueClosed ->
          Cont sourceClosed valueClosed ledger ->
            Cont shift substitution ledger ->
              Cont substitution depth audit ->
                Cont ledger audit route ->
                  Cont route audit recursorRead ->
                    Cont recursorRead ledger scopeRead ->
                      PkgSig bundle scopeRead pkg ->
                        UnaryHistory sourceClosed ∧ UnaryHistory valueClosed ∧
                          UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                            UnaryHistory recursorRead ∧ UnaryHistory scopeRead ∧
                              Cont sourceClosed valueClosed ledger ∧
                                Cont shift substitution ledger ∧ Cont substitution depth audit ∧
                                  Cont ledger audit route ∧ Cont route audit recursorRead ∧
                                    Cont recursorRead ledger scopeRead ∧
                                      PkgSig bundle scopeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro classifier sourceValueClosed valueDepthClosed sourceValueLedger shiftSubstitutionLedger
    substitutionDepthAudit ledgerAuditRoute routeAuditRecursor recursorLedgerScope scopePkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have sourceClosedUnary : UnaryHistory sourceClosed :=
    unary_cont_closed sourceUnary valueUnary sourceValueClosed
  have valueClosedUnary : UnaryHistory valueClosed :=
    unary_cont_closed valueUnary depthUnary valueDepthClosed
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed sourceClosedUnary valueClosedUnary sourceValueLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have recursorUnary : UnaryHistory recursorRead :=
    unary_cont_closed routeUnary auditUnary routeAuditRecursor
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed recursorUnary ledgerUnary recursorLedgerScope
  exact
    ⟨sourceClosedUnary, valueClosedUnary, ledgerUnary, auditUnary, routeUnary,
      recursorUnary, scopeUnary, sourceValueLedger, shiftSubstitutionLedger,
      substitutionDepthAudit, ledgerAuditRoute, routeAuditRecursor, recursorLedgerScope,
      scopePkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
