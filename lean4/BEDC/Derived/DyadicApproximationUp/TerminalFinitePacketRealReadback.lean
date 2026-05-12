import BEDC.Derived.DyadicApproximationUp.FiniteMeshEnclosure

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_terminal_finite_packet_real_readback
    [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance prefixPrecision prefixEndpoint prefixWindow
      prefixLedger prefixProvenance terminalPrecision terminalEndpoint terminalWindow
      terminalLedger terminalProvenance meshCell enclosure validatedRead sealRow reread : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      hsame precision prefixPrecision ->
        hsame endpoint prefixEndpoint ->
          hsame ledger prefixLedger ->
            hsame provenance prefixProvenance ->
              Cont prefixPrecision prefixEndpoint prefixWindow ->
                Cont prefixWindow prefixLedger prefixProvenance ->
                  hsame prefixPrecision terminalPrecision ->
                    hsame prefixEndpoint terminalEndpoint ->
                      hsame prefixLedger terminalLedger ->
                        hsame prefixProvenance terminalProvenance ->
                          Cont terminalPrecision terminalEndpoint terminalWindow ->
                            Cont terminalWindow terminalLedger terminalProvenance ->
                              Cont terminalWindow terminalProvenance meshCell ->
                                Cont meshCell terminalProvenance enclosure ->
                                  Cont enclosure terminalProvenance validatedRead ->
                                    Cont terminalLedger terminalProvenance sealRow ->
                                      Cont terminalWindow terminalProvenance reread ->
                                        PkgSig bundle meshCell pkg ->
                                          PkgSig bundle enclosure pkg ->
                                            PkgSig bundle validatedRead pkg ->
                                              PkgSig bundle sealRow pkg ->
                                                DyadicApproximationCarrier terminalPrecision
                                                    terminalEndpoint terminalWindow
                                                    terminalLedger terminalProvenance bundle pkg ∧
                                                  UnaryHistory validatedRead ∧
                                                    UnaryHistory sealRow ∧ UnaryHistory reread ∧
                                                      hsame prefixWindow terminalWindow ∧
                                                        hsame window terminalWindow := by
  intro carrier samePrecisionPrefix sameEndpointPrefix sameLedgerPrefix sameProvenancePrefix
  intro prefixPrecisionEndpointWindow prefixWindowLedgerProvenance
  intro samePrefixPrecisionTerminal samePrefixEndpointTerminal samePrefixLedgerTerminal
  intro samePrefixProvenanceTerminal terminalPrecisionEndpointWindow
  intro terminalWindowLedgerProvenance terminalWindowProvenanceMesh meshProvenanceEnclosure
  intro enclosureProvenanceValidated terminalLedgerProvenanceSeal terminalWindowProvenanceReread
  intro meshPkg enclosurePkg validatedPkg sealPkg
  have prefixProjection :
      DyadicApproximationCarrier prefixPrecision prefixEndpoint prefixWindow prefixLedger
          prefixProvenance bundle pkg ∧
        DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
          terminalLedger terminalProvenance bundle pkg ∧
          UnaryHistory reread ∧ hsame prefixWindow terminalWindow :=
    DyadicApproximationCarrier_terminal_window_prefix_projection carrier samePrecisionPrefix
      sameEndpointPrefix sameLedgerPrefix sameProvenancePrefix prefixPrecisionEndpointWindow
      prefixWindowLedgerProvenance samePrefixPrecisionTerminal samePrefixEndpointTerminal
      samePrefixLedgerTerminal samePrefixProvenanceTerminal terminalPrecisionEndpointWindow
      terminalWindowLedgerProvenance terminalWindowProvenanceReread
  have samePrecisionTerminal : hsame precision terminalPrecision :=
    hsame_trans samePrecisionPrefix samePrefixPrecisionTerminal
  have sameEndpointTerminal : hsame endpoint terminalEndpoint :=
    hsame_trans sameEndpointPrefix samePrefixEndpointTerminal
  have sameLedgerTerminal : hsame ledger terminalLedger :=
    hsame_trans sameLedgerPrefix samePrefixLedgerTerminal
  have sameProvenanceTerminal : hsame provenance terminalProvenance :=
    hsame_trans sameProvenancePrefix samePrefixProvenanceTerminal
  have finiteExact :
      DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
          terminalLedger terminalProvenance bundle pkg ∧
        UnaryHistory meshCell ∧ UnaryHistory enclosure ∧ UnaryHistory validatedRead ∧
          UnaryHistory sealRow ∧ hsame window terminalWindow ∧
            PkgSig bundle validatedRead pkg :=
    DyadicApproximationCarrier_finite_mesh_enclosure_exactness carrier samePrecisionTerminal
      sameEndpointTerminal sameLedgerTerminal sameProvenanceTerminal
      terminalPrecisionEndpointWindow terminalWindowLedgerProvenance terminalWindowProvenanceMesh
      meshProvenanceEnclosure enclosureProvenanceValidated terminalLedgerProvenanceSeal meshPkg
      enclosurePkg validatedPkg sealPkg
  exact
    ⟨finiteExact.left, finiteExact.right.right.right.left,
      finiteExact.right.right.right.right.left, prefixProjection.right.right.left,
      prefixProjection.right.right.right, finiteExact.right.right.right.right.right.left⟩

end BEDC.Derived.DyadicApproximationUp
