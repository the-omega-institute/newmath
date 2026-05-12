import BEDC.Derived.DyadicApproximationUp

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_terminal_diagonal_completion_handoff
    [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance terminalPrecision terminalEndpoint terminalWindow
      terminalLedger terminalProvenance diagonalSelector diagonalRead rationalRead dyadicConsumer
      diagonalConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      hsame precision terminalPrecision ->
        hsame endpoint terminalEndpoint ->
          hsame ledger terminalLedger ->
            hsame provenance terminalProvenance ->
              Cont terminalPrecision terminalEndpoint terminalWindow ->
                Cont terminalWindow terminalLedger terminalProvenance ->
                  Cont terminalWindow terminalProvenance dyadicConsumer ->
                    Cont terminalWindow terminalProvenance diagonalSelector ->
                      Cont diagonalSelector terminalWindow diagonalRead ->
                        Cont diagonalRead terminalLedger rationalRead ->
                          Cont rationalRead terminalProvenance diagonalConsumer ->
                            PkgSig bundle dyadicConsumer pkg ->
                              PkgSig bundle diagonalConsumer pkg ->
                                DyadicApproximationCarrier terminalPrecision terminalEndpoint
                                    terminalWindow terminalLedger terminalProvenance bundle pkg ∧
                                  UnaryHistory dyadicConsumer ∧ UnaryHistory diagonalSelector ∧
                                    UnaryHistory diagonalRead ∧ UnaryHistory rationalRead ∧
                                      UnaryHistory diagonalConsumer ∧ hsame window terminalWindow ∧
                                        PkgSig bundle dyadicConsumer pkg ∧
                                          PkgSig bundle diagonalConsumer pkg := by
  intro carrier samePrecision sameEndpoint sameLedger sameProvenance
  intro terminalPrecisionEndpointWindow terminalWindowLedgerProvenance
  intro terminalWindowProvenanceDyadic terminalWindowProvenanceDiagonal
  intro diagonalWindowRead readLedgerRational rationalProvenanceDiagonal
  intro dyadicPkg diagonalPkg
  have terminalCarrier :
      DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
          terminalLedger terminalProvenance bundle pkg ∧
        hsame window terminalWindow :=
    DyadicApproximationCarrier_classifier_transport carrier samePrecision sameEndpoint
      sameLedger sameProvenance terminalPrecisionEndpointWindow terminalWindowLedgerProvenance
  have terminalWindowUnary : UnaryHistory terminalWindow :=
    terminalCarrier.left.right.right.left
  have terminalLedgerUnary : UnaryHistory terminalLedger :=
    terminalCarrier.left.right.right.right.left
  have terminalProvenanceUnary : UnaryHistory terminalProvenance :=
    terminalCarrier.left.right.right.right.right.left
  have dyadicUnary : UnaryHistory dyadicConsumer :=
    unary_cont_closed terminalWindowUnary terminalProvenanceUnary terminalWindowProvenanceDyadic
  have selectorUnary : UnaryHistory diagonalSelector :=
    unary_cont_closed terminalWindowUnary terminalProvenanceUnary terminalWindowProvenanceDiagonal
  have readUnary : UnaryHistory diagonalRead :=
    unary_cont_closed selectorUnary terminalWindowUnary diagonalWindowRead
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed readUnary terminalLedgerUnary readLedgerRational
  have diagonalUnary : UnaryHistory diagonalConsumer :=
    unary_cont_closed rationalUnary terminalProvenanceUnary rationalProvenanceDiagonal
  exact
    ⟨terminalCarrier.left, dyadicUnary, selectorUnary, readUnary, rationalUnary, diagonalUnary,
      terminalCarrier.right, dyadicPkg, diagonalPkg⟩

end BEDC.Derived.DyadicApproximationUp
