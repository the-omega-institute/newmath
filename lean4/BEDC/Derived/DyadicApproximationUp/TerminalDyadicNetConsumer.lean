import BEDC.Derived.DyadicApproximationUp.TerminalIntervalMeshReadback

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_terminal_dyadic_net_consumption
    [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance terminalPrecision terminalEndpoint terminalWindow
      terminalLedger terminalProvenance meshCell enclosure validatedRead sealRow intervalMeshRead
      diagonalSelector consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      hsame precision terminalPrecision ->
        hsame endpoint terminalEndpoint ->
          hsame ledger terminalLedger ->
            hsame provenance terminalProvenance ->
              Cont terminalPrecision terminalEndpoint terminalWindow ->
                Cont terminalWindow terminalLedger terminalProvenance ->
                  Cont terminalWindow terminalProvenance meshCell ->
                    Cont meshCell terminalProvenance enclosure ->
                      Cont enclosure terminalProvenance validatedRead ->
                        Cont terminalLedger terminalProvenance sealRow ->
                          Cont validatedRead sealRow intervalMeshRead ->
                            Cont terminalWindow sealRow diagonalSelector ->
                              Cont diagonalSelector terminalProvenance consumer ->
                                PkgSig bundle meshCell pkg ->
                                  PkgSig bundle enclosure pkg ->
                                    PkgSig bundle validatedRead pkg ->
                                      PkgSig bundle sealRow pkg ->
                                        PkgSig bundle intervalMeshRead pkg ->
                                          PkgSig bundle diagonalSelector pkg ->
                                            PkgSig bundle consumer pkg ->
                                              DyadicApproximationCarrier terminalPrecision
                                                  terminalEndpoint terminalWindow
                                                  terminalLedger terminalProvenance bundle
                                                  pkg ∧
                                                UnaryHistory meshCell ∧
                                                  UnaryHistory enclosure ∧
                                                    UnaryHistory validatedRead ∧
                                                      UnaryHistory sealRow ∧
                                                        UnaryHistory intervalMeshRead ∧
                                                          UnaryHistory diagonalSelector ∧
                                                            UnaryHistory consumer ∧
                                                              hsame window terminalWindow ∧
                                                                PkgSig bundle consumer
                                                                  pkg := by
  intro carrier samePrecision sameEndpoint sameLedger sameProvenance
  intro terminalPrecisionEndpointWindow terminalWindowLedgerProvenance
  intro terminalWindowProvenanceMesh meshProvenanceEnclosure enclosureProvenanceValidated
  intro terminalLedgerProvenanceSeal validatedSealIntervalMesh
  intro terminalWindowSealDiagonal diagonalProvenanceConsumer
  intro meshPkg enclosurePkg validatedPkg sealPkg intervalMeshPkg _diagonalPkg consumerPkg
  have readback :
      DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
          terminalLedger terminalProvenance bundle pkg ∧
        UnaryHistory meshCell ∧ UnaryHistory enclosure ∧ UnaryHistory validatedRead ∧
          UnaryHistory sealRow ∧ UnaryHistory intervalMeshRead ∧ hsame window terminalWindow ∧
            PkgSig bundle intervalMeshRead pkg :=
    DyadicApproximationCarrier_terminal_interval_mesh_readback_totality carrier samePrecision
      sameEndpoint sameLedger sameProvenance terminalPrecisionEndpointWindow
      terminalWindowLedgerProvenance terminalWindowProvenanceMesh meshProvenanceEnclosure
      enclosureProvenanceValidated terminalLedgerProvenanceSeal validatedSealIntervalMesh
      meshPkg enclosurePkg validatedPkg sealPkg intervalMeshPkg
  rcases readback with
    ⟨terminalCarrier, meshUnary, enclosureUnary, validatedUnary, sealUnary,
      intervalMeshUnary, sameWindow, _intervalMeshPkg⟩
  rcases terminalCarrier with
    ⟨terminalPrecisionUnary, terminalEndpointUnary, terminalWindowUnary, terminalLedgerUnary,
      terminalProvenanceUnary, terminalPrecisionEndpointWindow',
      terminalWindowLedgerProvenance', terminalPkg⟩
  have diagonalUnary : UnaryHistory diagonalSelector :=
    unary_cont_closed terminalWindowUnary sealUnary terminalWindowSealDiagonal
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed diagonalUnary terminalProvenanceUnary diagonalProvenanceConsumer
  exact
    ⟨⟨terminalPrecisionUnary, terminalEndpointUnary, terminalWindowUnary, terminalLedgerUnary,
        terminalProvenanceUnary, terminalPrecisionEndpointWindow',
        terminalWindowLedgerProvenance', terminalPkg⟩,
      meshUnary, enclosureUnary, validatedUnary, sealUnary, intervalMeshUnary, diagonalUnary,
      consumerUnary, sameWindow, consumerPkg⟩

end BEDC.Derived.DyadicApproximationUp
