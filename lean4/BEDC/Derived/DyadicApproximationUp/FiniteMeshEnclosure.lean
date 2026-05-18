import BEDC.Derived.DyadicApproximationUp

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicApproximationMeshEnclosureExactnessPacket [AskSetup] [PackageSetup]
    (precision endpoint window ledger provenance terminalPrecision terminalEndpoint terminalWindow
      terminalLedger terminalProvenance meshCell enclosure validatedRead sealRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ∧
    hsame precision terminalPrecision ∧ hsame endpoint terminalEndpoint ∧
      hsame ledger terminalLedger ∧ hsame provenance terminalProvenance ∧
        Cont terminalPrecision terminalEndpoint terminalWindow ∧
          Cont terminalWindow terminalLedger terminalProvenance ∧
            Cont terminalWindow terminalProvenance meshCell ∧
              Cont meshCell terminalProvenance enclosure ∧
                Cont enclosure terminalProvenance validatedRead ∧
                  Cont terminalLedger terminalProvenance sealRow ∧
                    PkgSig bundle meshCell pkg ∧ PkgSig bundle enclosure pkg ∧
                      PkgSig bundle validatedRead pkg ∧ PkgSig bundle sealRow pkg

theorem DyadicApproximationCarrier_finite_mesh_enclosure_exactness
    [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance terminalPrecision terminalEndpoint terminalWindow
      terminalLedger terminalProvenance meshCell enclosure validatedRead sealRow : BHist}
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
                          PkgSig bundle meshCell pkg ->
                            PkgSig bundle enclosure pkg ->
                              PkgSig bundle validatedRead pkg ->
                                PkgSig bundle sealRow pkg ->
                                  DyadicApproximationCarrier terminalPrecision terminalEndpoint
                                      terminalWindow terminalLedger terminalProvenance bundle pkg ∧
                                    UnaryHistory meshCell ∧ UnaryHistory enclosure ∧
                                      UnaryHistory validatedRead ∧ UnaryHistory sealRow ∧
                                        hsame window terminalWindow ∧
                                          PkgSig bundle validatedRead pkg := by
  intro carrier samePrecision sameEndpoint sameLedger sameProvenance
  intro terminalPrecisionEndpointWindow terminalWindowLedgerProvenance
  intro terminalWindowProvenanceMesh meshProvenanceEnclosure enclosureProvenanceValidated
  intro terminalLedgerProvenanceSeal _meshPkg _enclosurePkg validatedPkg _sealPkg
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
  have meshUnary : UnaryHistory meshCell :=
    unary_cont_closed terminalWindowUnary terminalProvenanceUnary terminalWindowProvenanceMesh
  have enclosureUnary : UnaryHistory enclosure :=
    unary_cont_closed meshUnary terminalProvenanceUnary meshProvenanceEnclosure
  have validatedUnary : UnaryHistory validatedRead :=
    unary_cont_closed enclosureUnary terminalProvenanceUnary enclosureProvenanceValidated
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed terminalLedgerUnary terminalProvenanceUnary terminalLedgerProvenanceSeal
  exact
    ⟨⟨terminalPrecisionUnary, terminalEndpointUnary, terminalWindowUnary,
        terminalLedgerUnary, terminalProvenanceUnary, terminalPrecisionEndpointWindow',
        terminalWindowLedgerProvenance', terminalPkg⟩,
      meshUnary, enclosureUnary, validatedUnary, sealUnary, sameWindow, validatedPkg⟩

theorem DyadicApproximationMeshEnclosureExactnessPacket_consumes_real_surface
    [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance terminalPrecision terminalEndpoint terminalWindow
      terminalLedger terminalProvenance meshCell enclosure validatedRead sealRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationMeshEnclosureExactnessPacket precision endpoint window ledger provenance
        terminalPrecision terminalEndpoint terminalWindow terminalLedger terminalProvenance meshCell
        enclosure validatedRead sealRow bundle pkg ->
      DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
          terminalLedger terminalProvenance bundle pkg ∧
        UnaryHistory meshCell ∧ UnaryHistory enclosure ∧ UnaryHistory validatedRead ∧
          UnaryHistory sealRow ∧ hsame window terminalWindow ∧
            PkgSig bundle validatedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet
  obtain ⟨carrier, samePrecision, sameEndpoint, sameLedger, sameProvenance,
    terminalPrecisionEndpointWindow, terminalWindowLedgerProvenance,
    terminalWindowProvenanceMesh, meshProvenanceEnclosure, enclosureProvenanceValidated,
    terminalLedgerProvenanceSeal, meshPkg, enclosurePkg, validatedPkg, sealPkg⟩ := packet
  exact
    DyadicApproximationCarrier_finite_mesh_enclosure_exactness carrier samePrecision
      sameEndpoint sameLedger sameProvenance terminalPrecisionEndpointWindow
      terminalWindowLedgerProvenance terminalWindowProvenanceMesh meshProvenanceEnclosure
      enclosureProvenanceValidated terminalLedgerProvenanceSeal meshPkg enclosurePkg
      validatedPkg sealPkg

end BEDC.Derived.DyadicApproximationUp
