import BEDC.Derived.DyadicApproximationUp

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_finite_packet_streamname_real_seal_factorization
    [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance terminalPrecision terminalEndpoint terminalWindow
      terminalLedger terminalProvenance sealRow streamWindow readback diagonalSelector
      factorizedSurface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      hsame precision terminalPrecision ->
        hsame endpoint terminalEndpoint ->
          hsame ledger terminalLedger ->
            hsame provenance terminalProvenance ->
              Cont terminalPrecision terminalEndpoint terminalWindow ->
                Cont terminalWindow terminalLedger terminalProvenance ->
                  Cont terminalLedger terminalProvenance sealRow ->
                    Cont terminalWindow terminalProvenance streamWindow ->
                      Cont streamWindow sealRow readback ->
                        Cont readback terminalProvenance diagonalSelector ->
                          Cont diagonalSelector sealRow factorizedSurface ->
                            PkgSig bundle factorizedSurface pkg ->
                              DyadicApproximationCarrier terminalPrecision terminalEndpoint
                                  terminalWindow terminalLedger terminalProvenance bundle pkg ∧
                                UnaryHistory sealRow ∧ UnaryHistory streamWindow ∧
                                  UnaryHistory readback ∧ UnaryHistory diagonalSelector ∧
                                    UnaryHistory factorizedSurface ∧
                                      hsame window terminalWindow ∧
                                        PkgSig bundle factorizedSurface pkg := by
  intro carrier samePrecision sameEndpoint sameLedger sameProvenance
  intro terminalPrecisionEndpointWindow terminalWindowLedgerProvenance
  intro terminalLedgerProvenanceSeal terminalWindowProvenanceStream
  intro streamSealReadback readbackProvenanceDiagonal diagonalSealFactorized factorizedPkg
  have transported :
      DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
          terminalLedger terminalProvenance bundle pkg ∧
        hsame window terminalWindow :=
    DyadicApproximationCarrier_classifier_transport carrier samePrecision sameEndpoint
      sameLedger sameProvenance terminalPrecisionEndpointWindow terminalWindowLedgerProvenance
  rcases transported with ⟨terminalCarrier, sameWindow⟩
  rcases terminalCarrier with
    ⟨terminalPrecisionUnary, terminalEndpointUnary, terminalWindowUnary, terminalLedgerUnary,
      terminalProvenanceUnary, terminalPrecisionEndpointWindow',
      terminalWindowLedgerProvenance', terminalPkg⟩
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed terminalLedgerUnary terminalProvenanceUnary terminalLedgerProvenanceSeal
  have streamUnary : UnaryHistory streamWindow :=
    unary_cont_closed terminalWindowUnary terminalProvenanceUnary terminalWindowProvenanceStream
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed streamUnary sealUnary streamSealReadback
  have diagonalUnary : UnaryHistory diagonalSelector :=
    unary_cont_closed readbackUnary terminalProvenanceUnary readbackProvenanceDiagonal
  have factorizedUnary : UnaryHistory factorizedSurface :=
    unary_cont_closed diagonalUnary sealUnary diagonalSealFactorized
  exact
    ⟨⟨terminalPrecisionUnary, terminalEndpointUnary, terminalWindowUnary, terminalLedgerUnary,
        terminalProvenanceUnary, terminalPrecisionEndpointWindow',
        terminalWindowLedgerProvenance', terminalPkg⟩,
      sealUnary, streamUnary, readbackUnary, diagonalUnary, factorizedUnary, sameWindow,
      factorizedPkg⟩

end BEDC.Derived.DyadicApproximationUp
