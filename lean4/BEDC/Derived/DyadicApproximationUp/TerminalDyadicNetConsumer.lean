import BEDC.Derived.DyadicApproximationUp.TerminalIntervalMeshReadback

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem DyadicApproximationCarrier_terminal_dyadic_net_bridge
    [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance terminalPrecision terminalEndpoint terminalWindow
      terminalLedger terminalProvenance meshCell enclosure validatedRead sealRow intervalMeshRead
      diagonalSelector consumer bridgeSurface : BHist}
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
                                Cont consumer terminalProvenance bridgeSurface ->
                                  PkgSig bundle meshCell pkg ->
                                    PkgSig bundle enclosure pkg ->
                                      PkgSig bundle validatedRead pkg ->
                                        PkgSig bundle sealRow pkg ->
                                          PkgSig bundle intervalMeshRead pkg ->
                                            PkgSig bundle diagonalSelector pkg ->
                                              PkgSig bundle consumer pkg ->
                                                PkgSig bundle bridgeSurface pkg ->
                                                  UnaryHistory bridgeSurface ∧
                                                    PkgSig bundle bridgeSurface pkg ∧
                                                      SemanticNameCert
                                                        (fun row : BHist =>
                                                          hsame row bridgeSurface ∧
                                                            UnaryHistory row ∧
                                                              PkgSig bundle row pkg)
                                                        (fun row : BHist =>
                                                          hsame row bridgeSurface ∧
                                                            UnaryHistory row)
                                                        (fun row : BHist =>
                                                          PkgSig bundle row pkg ∧
                                                            hsame row bridgeSurface)
                                                        (fun row row' : BHist =>
                                                          hsame row row') := by
  intro carrier samePrecision sameEndpoint sameLedger sameProvenance
  intro terminalPrecisionEndpointWindow terminalWindowLedgerProvenance
  intro terminalWindowProvenanceMesh meshProvenanceEnclosure enclosureProvenanceValidated
  intro terminalLedgerProvenanceSeal validatedSealIntervalMesh
  intro terminalWindowSealDiagonal diagonalProvenanceConsumer consumerProvenanceBridge
  intro meshPkg enclosurePkg validatedPkg sealPkg intervalMeshPkg diagonalPkg consumerPkg
    bridgePkg
  have consumed :
      DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
          terminalLedger terminalProvenance bundle pkg ∧
        UnaryHistory meshCell ∧ UnaryHistory enclosure ∧ UnaryHistory validatedRead ∧
          UnaryHistory sealRow ∧ UnaryHistory intervalMeshRead ∧ UnaryHistory diagonalSelector ∧
            UnaryHistory consumer ∧ hsame window terminalWindow ∧ PkgSig bundle consumer pkg :=
    DyadicApproximationCarrier_terminal_dyadic_net_consumption carrier samePrecision
      sameEndpoint sameLedger sameProvenance terminalPrecisionEndpointWindow
      terminalWindowLedgerProvenance terminalWindowProvenanceMesh meshProvenanceEnclosure
      enclosureProvenanceValidated terminalLedgerProvenanceSeal validatedSealIntervalMesh
      terminalWindowSealDiagonal diagonalProvenanceConsumer meshPkg enclosurePkg validatedPkg
      sealPkg intervalMeshPkg diagonalPkg consumerPkg
  rcases consumed with
    ⟨terminalCarrier, _meshUnary, _enclosureUnary, _validatedUnary, _sealUnary,
      _intervalMeshUnary, _diagonalUnary, consumerUnary, _sameWindow, _consumerPkg⟩
  rcases terminalCarrier with
    ⟨_terminalPrecisionUnary, _terminalEndpointUnary, _terminalWindowUnary,
      _terminalLedgerUnary, terminalProvenanceUnary, _terminalPrecisionEndpointWindow,
      _terminalWindowLedgerProvenance, _terminalPkg⟩
  have bridgeUnary : UnaryHistory bridgeSurface :=
    unary_cont_closed consumerUnary terminalProvenanceUnary consumerProvenanceBridge
  have semantic :
      SemanticNameCert
        (fun row : BHist =>
          hsame row bridgeSurface ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
        (fun row : BHist => hsame row bridgeSurface ∧ UnaryHistory row)
        (fun row : BHist => PkgSig bundle row pkg ∧ hsame row bridgeSurface)
        (fun row row' : BHist => hsame row row') := {
    core := {
      carrier_inhabited :=
        Exists.intro bridgeSurface ⟨hsame_refl bridgeSurface, bridgeUnary, bridgePkg⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' classified
        exact hsame_symm classified
      equiv_trans := by
        intro _row _row' _row'' leftClassified rightClassified
        exact hsame_trans leftClassified rightClassified
      carrier_respects_equiv := by
        intro _row _row' classified sourceRow
        cases classified
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, sourceRow.right.left⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right, sourceRow.left⟩
  }
  exact ⟨bridgeUnary, bridgePkg, semantic⟩

end BEDC.Derived.DyadicApproximationUp
