import BEDC.Derived.DyadicApproximationUp.FiniteMeshEnclosure

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_terminal_interval_mesh_readback_totality
    [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance terminalPrecision terminalEndpoint terminalWindow
      terminalLedger terminalProvenance meshCell enclosure validatedRead sealRow intervalMeshRead :
      BHist}
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
                            PkgSig bundle meshCell pkg ->
                              PkgSig bundle enclosure pkg ->
                                PkgSig bundle validatedRead pkg ->
                                  PkgSig bundle sealRow pkg ->
                                    PkgSig bundle intervalMeshRead pkg ->
                                      DyadicApproximationCarrier terminalPrecision
                                          terminalEndpoint terminalWindow terminalLedger
                                          terminalProvenance bundle pkg ∧
                                        UnaryHistory meshCell ∧ UnaryHistory enclosure ∧
                                          UnaryHistory validatedRead ∧ UnaryHistory sealRow ∧
                                            UnaryHistory intervalMeshRead ∧
                                              hsame window terminalWindow ∧
                                                PkgSig bundle intervalMeshRead pkg := by
  intro carrier samePrecision sameEndpoint sameLedger sameProvenance
  intro terminalPrecisionEndpointWindow terminalWindowLedgerProvenance
  intro terminalWindowProvenanceMesh meshProvenanceEnclosure enclosureProvenanceValidated
  intro terminalLedgerProvenanceSeal validatedSealIntervalMesh
  intro meshPkg enclosurePkg validatedPkg sealPkg intervalMeshPkg
  have finiteExact :
      DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
          terminalLedger terminalProvenance bundle pkg ∧
        UnaryHistory meshCell ∧ UnaryHistory enclosure ∧ UnaryHistory validatedRead ∧
          UnaryHistory sealRow ∧ hsame window terminalWindow ∧
            PkgSig bundle validatedRead pkg :=
    DyadicApproximationCarrier_finite_mesh_enclosure_exactness carrier samePrecision
      sameEndpoint sameLedger sameProvenance terminalPrecisionEndpointWindow
      terminalWindowLedgerProvenance terminalWindowProvenanceMesh meshProvenanceEnclosure
      enclosureProvenanceValidated terminalLedgerProvenanceSeal meshPkg enclosurePkg validatedPkg
      sealPkg
  have intervalMeshUnary : UnaryHistory intervalMeshRead :=
    unary_cont_closed finiteExact.right.right.right.left finiteExact.right.right.right.right.left
      validatedSealIntervalMesh
  exact
    ⟨finiteExact.left, finiteExact.right.left, finiteExact.right.right.left,
      finiteExact.right.right.right.left, finiteExact.right.right.right.right.left,
      intervalMeshUnary, finiteExact.right.right.right.right.right.left, intervalMeshPkg⟩

end BEDC.Derived.DyadicApproximationUp
