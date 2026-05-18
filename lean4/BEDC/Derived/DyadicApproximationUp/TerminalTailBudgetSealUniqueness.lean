import BEDC.Derived.DyadicApproximationUp

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_terminal_budget_seal_uniqueness
    [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance terminalPrecision terminalEndpoint terminalWindow
      terminalLedger terminalProvenance sealRow sealRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      hsame precision terminalPrecision ->
        hsame endpoint terminalEndpoint ->
          hsame ledger terminalLedger ->
            hsame provenance terminalProvenance ->
              Cont terminalPrecision terminalEndpoint terminalWindow ->
                Cont terminalWindow terminalLedger terminalProvenance ->
                  Cont terminalLedger terminalProvenance sealRow ->
                    Cont terminalLedger terminalProvenance sealRow' ->
                      PkgSig bundle sealRow pkg ->
                        PkgSig bundle sealRow' pkg ->
                          DyadicApproximationCarrier terminalPrecision terminalEndpoint
                              terminalWindow terminalLedger terminalProvenance bundle pkg ∧
                            UnaryHistory sealRow ∧ UnaryHistory sealRow' ∧
                              hsame sealRow sealRow' ∧ PkgSig bundle sealRow pkg ∧
                                PkgSig bundle sealRow' pkg := by
  intro carrier samePrecision sameEndpoint sameLedger sameProvenance
  intro terminalPrecisionEndpointWindow terminalWindowLedgerProvenance
  intro terminalLedgerProvenanceSeal terminalLedgerProvenanceSeal' sealPkg sealPkg'
  have transported :
      DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
          terminalLedger terminalProvenance bundle pkg ∧
        hsame window terminalWindow :=
    DyadicApproximationCarrier_classifier_transport carrier samePrecision sameEndpoint
      sameLedger sameProvenance terminalPrecisionEndpointWindow
      terminalWindowLedgerProvenance
  rcases transported with ⟨terminalCarrier, _sameWindow⟩
  rcases terminalCarrier with
    ⟨terminalPrecisionUnary, terminalEndpointUnary, terminalWindowUnary, terminalLedgerUnary,
      terminalProvenanceUnary, terminalPrecisionEndpointWindow',
      terminalWindowLedgerProvenance', terminalPkg⟩
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed terminalLedgerUnary terminalProvenanceUnary terminalLedgerProvenanceSeal
  have sealUnary' : UnaryHistory sealRow' :=
    unary_cont_closed terminalLedgerUnary terminalProvenanceUnary terminalLedgerProvenanceSeal'
  have sameSeal : hsame sealRow sealRow' :=
    cont_deterministic terminalLedgerProvenanceSeal terminalLedgerProvenanceSeal'
  exact
    ⟨⟨terminalPrecisionUnary, terminalEndpointUnary, terminalWindowUnary, terminalLedgerUnary,
        terminalProvenanceUnary, terminalPrecisionEndpointWindow',
        terminalWindowLedgerProvenance', terminalPkg⟩,
      sealUnary, sealUnary', sameSeal, sealPkg, sealPkg'⟩

end BEDC.Derived.DyadicApproximationUp
