import BEDC.Derived.DyadicApproximationUp.FiniteMeshEnclosure
import BEDC.Derived.DyadicApproximationUp.ValidatedEnclosureRoute

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_mesh_validated_real_boundary [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance terminalPrecision terminalEndpoint
      terminalWindow terminalLedger terminalProvenance meshCell enclosure validatedRead sealRow
      reread meshRead : BHist}
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
                            Cont meshCell terminalProvenance meshRead ->
                              PkgSig bundle meshCell pkg ->
                                PkgSig bundle enclosure pkg ->
                                  PkgSig bundle validatedRead pkg ->
                                    PkgSig bundle sealRow pkg ->
                                      DyadicApproximationCarrier terminalPrecision
                                          terminalEndpoint terminalWindow terminalLedger
                                          terminalProvenance bundle pkg ∧
                                        UnaryHistory meshCell ∧
                                          UnaryHistory enclosure ∧
                                            UnaryHistory validatedRead ∧
                                              UnaryHistory sealRow ∧
                                                UnaryHistory reread ∧
                                                  UnaryHistory meshRead ∧
                                                    hsame window terminalWindow ∧
                                                      SemanticNameCert
                                                        (fun row : BHist =>
                                                          hsame row enclosure ∧
                                                            UnaryHistory row ∧
                                                              PkgSig bundle row pkg)
                                                        (fun row : BHist =>
                                                          Cont meshCell terminalProvenance row ∧
                                                            hsame window terminalWindow)
                                                        (fun row : BHist =>
                                                          PkgSig bundle row pkg ∧
                                                            UnaryHistory sealRow ∧
                                                              UnaryHistory reread ∧
                                                                UnaryHistory meshRead)
                                                        (fun row row' : BHist =>
                                                          hsame row row') := by
  intro carrier samePrecision sameEndpoint sameLedger sameProvenance
  intro terminalPrecisionEndpointWindow terminalWindowLedgerProvenance
  intro terminalWindowProvenanceMesh meshProvenanceEnclosure enclosureProvenanceValidated
  intro terminalLedgerProvenanceSeal terminalWindowProvenanceReread meshProvenanceMeshRead
  intro meshPkg enclosurePkg validatedPkg sealPkg
  have readback :
      DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
          terminalLedger terminalProvenance bundle pkg ∧
        UnaryHistory meshCell ∧ UnaryHistory enclosure ∧ UnaryHistory sealRow ∧
          hsame window terminalWindow ∧ PkgSig bundle meshCell pkg ∧
            PkgSig bundle enclosure pkg ∧ PkgSig bundle sealRow pkg :=
    DyadicApproximationCarrier_terminal_validated_enclosure_readback carrier samePrecision
      sameEndpoint sameLedger sameProvenance terminalPrecisionEndpointWindow
      terminalWindowLedgerProvenance terminalWindowProvenanceMesh meshProvenanceEnclosure
      terminalLedgerProvenanceSeal meshPkg enclosurePkg sealPkg
  have exactness :
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
  have routeCert :
      SemanticNameCert
        (fun row : BHist => hsame row enclosure ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
        (fun row : BHist =>
          Cont meshCell terminalProvenance row ∧ hsame window terminalWindow)
        (fun row : BHist =>
          PkgSig bundle row pkg ∧ UnaryHistory sealRow ∧ UnaryHistory reread ∧
            UnaryHistory meshRead)
        (fun row row' : BHist => hsame row row') :=
    DyadicApproximationCarrier_validated_enclosure_route_commutation carrier samePrecision
      sameEndpoint sameLedger sameProvenance terminalPrecisionEndpointWindow
      terminalWindowLedgerProvenance terminalWindowProvenanceMesh meshProvenanceEnclosure
      terminalLedgerProvenanceSeal terminalWindowProvenanceReread meshProvenanceMeshRead
      meshPkg enclosurePkg sealPkg
  exact
    ⟨readback.left, readback.right.left, readback.right.right.left,
      exactness.right.right.right.left, readback.right.right.right.left,
      routeCert.ledger_sound ⟨hsame_refl enclosure, readback.right.right.left,
        enclosurePkg⟩ |>.right.right.left,
      routeCert.ledger_sound ⟨hsame_refl enclosure, readback.right.right.left,
        enclosurePkg⟩ |>.right.right.right,
      readback.right.right.right.right.left, routeCert⟩

end BEDC.Derived.DyadicApproximationUp
