import BEDC.Derived.DyadicApproximationUp.FiniteMeshEnclosure

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_terminal_diagonal_readback_composition
    [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance terminalPrecision terminalEndpoint terminalWindow
      terminalLedger terminalProvenance meshCell enclosure validatedRead sealRow reread
      diagonalConsumer : BHist}
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
                          Cont terminalWindow terminalProvenance reread ->
                            Cont reread sealRow diagonalConsumer ->
                              PkgSig bundle meshCell pkg ->
                                PkgSig bundle enclosure pkg ->
                                  PkgSig bundle validatedRead pkg ->
                                    PkgSig bundle sealRow pkg ->
                                      PkgSig bundle diagonalConsumer pkg ->
                                        DyadicApproximationCarrier terminalPrecision
                                            terminalEndpoint terminalWindow terminalLedger
                                            terminalProvenance bundle pkg ∧
                                          UnaryHistory validatedRead ∧
                                            UnaryHistory sealRow ∧
                                              UnaryHistory reread ∧
                                                UnaryHistory diagonalConsumer ∧
                                                  hsame window terminalWindow ∧
                                                    PkgSig bundle diagonalConsumer pkg := by
  intro carrier samePrecision sameEndpoint sameLedger sameProvenance
  intro terminalPrecisionEndpointWindow terminalWindowLedgerProvenance
  intro terminalWindowProvenanceMesh meshProvenanceEnclosure enclosureProvenanceValidated
  intro terminalLedgerProvenanceSeal terminalWindowProvenanceReread
  intro rereadSealDiagonal meshPkg enclosurePkg validatedPkg sealPkg diagonalPkg
  have finiteExact :
      DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
          terminalLedger terminalProvenance bundle pkg ∧
        UnaryHistory meshCell ∧ UnaryHistory enclosure ∧ UnaryHistory validatedRead ∧
          UnaryHistory sealRow ∧ hsame window terminalWindow ∧
            PkgSig bundle validatedRead pkg :=
    DyadicApproximationCarrier_finite_mesh_enclosure_exactness carrier samePrecision
      sameEndpoint sameLedger sameProvenance terminalPrecisionEndpointWindow
      terminalWindowLedgerProvenance terminalWindowProvenanceMesh meshProvenanceEnclosure
      enclosureProvenanceValidated terminalLedgerProvenanceSeal meshPkg enclosurePkg
      validatedPkg sealPkg
  rcases finiteExact with
    ⟨terminalCarrier, _meshUnary, _enclosureUnary, validatedUnary, sealUnary, sameWindow,
      _validatedPkgOut⟩
  rcases terminalCarrier with
    ⟨terminalPrecisionUnary, terminalEndpointUnary, terminalWindowUnary, terminalLedgerUnary,
      terminalProvenanceUnary, terminalPrecisionEndpointWindow',
      terminalWindowLedgerProvenance', terminalPkg⟩
  have rereadUnary : UnaryHistory reread :=
    unary_cont_closed terminalWindowUnary terminalProvenanceUnary terminalWindowProvenanceReread
  have diagonalUnary : UnaryHistory diagonalConsumer :=
    unary_cont_closed rereadUnary sealUnary rereadSealDiagonal
  exact
    ⟨⟨terminalPrecisionUnary, terminalEndpointUnary, terminalWindowUnary, terminalLedgerUnary,
        terminalProvenanceUnary, terminalPrecisionEndpointWindow',
        terminalWindowLedgerProvenance', terminalPkg⟩,
      validatedUnary, sealUnary, rereadUnary, diagonalUnary, sameWindow, diagonalPkg⟩

end BEDC.Derived.DyadicApproximationUp
