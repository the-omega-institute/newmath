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
    {precision endpoint window ledger provenance terminalPrecision terminalEndpoint
      terminalWindow terminalLedger terminalProvenance diagonalPacket completionSurface :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      hsame precision terminalPrecision ->
        hsame endpoint terminalEndpoint ->
          hsame ledger terminalLedger ->
            hsame provenance terminalProvenance ->
              Cont terminalPrecision terminalEndpoint terminalWindow ->
                Cont terminalWindow terminalLedger terminalProvenance ->
                  Cont terminalWindow terminalProvenance diagonalPacket ->
                    Cont diagonalPacket terminalProvenance completionSurface ->
                      PkgSig bundle diagonalPacket pkg ->
                        PkgSig bundle completionSurface pkg ->
                          DyadicApproximationCarrier terminalPrecision terminalEndpoint
                              terminalWindow terminalLedger terminalProvenance bundle pkg ∧
                            UnaryHistory diagonalPacket ∧ UnaryHistory completionSurface ∧
                              hsame window terminalWindow ∧ PkgSig bundle diagonalPacket pkg ∧
                                PkgSig bundle completionSurface pkg := by
  intro carrier samePrecision sameEndpoint sameLedger sameProvenance terminalWindowRoute
    terminalProvenanceRoute diagonalPacketRoute completionSurfaceRoute diagonalPacketPkg
    completionSurfacePkg
  have transported :
      DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
          terminalLedger terminalProvenance bundle pkg ∧
        hsame window terminalWindow :=
    DyadicApproximationCarrier_classifier_transport carrier samePrecision sameEndpoint
      sameLedger sameProvenance terminalWindowRoute terminalProvenanceRoute
  obtain ⟨terminalCarrier, sameWindow⟩ := transported
  obtain ⟨_terminalPrecisionUnary, _terminalEndpointUnary, terminalWindowUnary,
    _terminalLedgerUnary, terminalProvenanceUnary, _terminalWindowRoute,
    _terminalProvenanceRoute, _terminalPkg⟩ := terminalCarrier
  have diagonalPacketUnary : UnaryHistory diagonalPacket :=
    unary_cont_closed terminalWindowUnary terminalProvenanceUnary diagonalPacketRoute
  have completionSurfaceUnary : UnaryHistory completionSurface :=
    unary_cont_closed diagonalPacketUnary terminalProvenanceUnary completionSurfaceRoute
  exact
    ⟨⟨_terminalPrecisionUnary, _terminalEndpointUnary, terminalWindowUnary,
        _terminalLedgerUnary, terminalProvenanceUnary, _terminalWindowRoute,
        _terminalProvenanceRoute, _terminalPkg⟩,
      diagonalPacketUnary, completionSurfaceUnary, sameWindow, diagonalPacketPkg,
      completionSurfacePkg⟩

end BEDC.Derived.DyadicApproximationUp
