import BEDC.Derived.DyadicApproximationUp

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_consumer_completeness [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance weakenedPrecision weakenedEndpoint weakenedWindow
      weakenedLedger weakenedProvenance sealRow consumer publicSurface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      hsame precision weakenedPrecision -> hsame endpoint weakenedEndpoint ->
        hsame ledger weakenedLedger -> hsame provenance weakenedProvenance ->
          Cont weakenedPrecision weakenedEndpoint weakenedWindow ->
            Cont weakenedWindow weakenedLedger weakenedProvenance ->
              Cont weakenedWindow weakenedProvenance consumer ->
                Cont weakenedLedger weakenedProvenance sealRow ->
                  Cont consumer sealRow publicSurface ->
                    PkgSig bundle consumer pkg -> PkgSig bundle sealRow pkg ->
                      PkgSig bundle publicSurface pkg ->
                        DyadicApproximationCarrier weakenedPrecision weakenedEndpoint weakenedWindow
                            weakenedLedger weakenedProvenance bundle pkg ∧
                          UnaryHistory consumer ∧ UnaryHistory sealRow ∧
                            UnaryHistory publicSurface ∧ hsame window weakenedWindow ∧
                              PkgSig bundle publicSurface pkg := by
  intro carrier samePrecision sameEndpoint sameLedger sameProvenance
  intro weakenedPrecisionEndpointWindow weakenedWindowLedgerProvenance
  intro weakenedWindowProvenanceConsumer weakenedLedgerProvenanceSeal
  intro consumerSealPublicSurface consumerPkg sealPkg publicSurfacePkg
  have transported :
      DyadicApproximationCarrier weakenedPrecision weakenedEndpoint weakenedWindow
          weakenedLedger weakenedProvenance bundle pkg ∧
        hsame window weakenedWindow :=
    DyadicApproximationCarrier_classifier_transport carrier samePrecision sameEndpoint sameLedger
      sameProvenance weakenedPrecisionEndpointWindow weakenedWindowLedgerProvenance
  have weakenedCarrierOut :
      DyadicApproximationCarrier weakenedPrecision weakenedEndpoint weakenedWindow
        weakenedLedger weakenedProvenance bundle pkg := transported.left
  have sameWindow : hsame window weakenedWindow := transported.right
  have weakenedCarrierFields := weakenedCarrierOut
  rcases weakenedCarrierFields with
    ⟨_weakenedPrecisionUnary, _weakenedEndpointUnary, weakenedWindowUnary,
      weakenedLedgerUnary, weakenedProvenanceUnary, _weakenedPrecisionEndpointWindow,
      _weakenedWindowLedgerProvenance, _weakenedPkg⟩
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed weakenedWindowUnary weakenedProvenanceUnary
      weakenedWindowProvenanceConsumer
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed weakenedLedgerUnary weakenedProvenanceUnary weakenedLedgerProvenanceSeal
  have publicSurfaceUnary : UnaryHistory publicSurface :=
    unary_cont_closed consumerUnary sealUnary consumerSealPublicSurface
  exact
    ⟨weakenedCarrierOut, consumerUnary, sealUnary, publicSurfaceUnary, sameWindow,
      publicSurfacePkg⟩

theorem DyadicApproximationCarrier_terminal_refinement_window [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance terminalPrecision terminalEndpoint terminalWindow
      terminalLedger terminalProvenance rationalContainment sealRow consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      hsame precision terminalPrecision -> hsame endpoint terminalEndpoint ->
        hsame ledger terminalLedger -> hsame provenance terminalProvenance ->
          Cont terminalPrecision terminalEndpoint terminalWindow ->
            Cont terminalWindow terminalLedger terminalProvenance ->
              Cont terminalWindow terminalProvenance rationalContainment ->
                Cont terminalLedger terminalProvenance sealRow ->
                  Cont rationalContainment sealRow consumer ->
                    PkgSig bundle rationalContainment pkg -> PkgSig bundle sealRow pkg ->
                      PkgSig bundle consumer pkg ->
                        DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
                            terminalLedger terminalProvenance bundle pkg ∧
                          UnaryHistory rationalContainment ∧ UnaryHistory sealRow ∧
                            UnaryHistory consumer ∧ hsame window terminalWindow ∧
                              PkgSig bundle consumer pkg := by
  intro carrier samePrecision sameEndpoint sameLedger sameProvenance
  intro terminalPrecisionEndpointWindow terminalWindowLedgerProvenance
  intro terminalWindowProvenanceContainment terminalLedgerProvenanceSeal
  intro containmentSealConsumer containmentPkg sealPkg consumerPkg
  have transported :
      DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
          terminalLedger terminalProvenance bundle pkg ∧
        hsame window terminalWindow :=
    DyadicApproximationCarrier_classifier_transport carrier samePrecision sameEndpoint sameLedger
      sameProvenance terminalPrecisionEndpointWindow terminalWindowLedgerProvenance
  have terminalCarrierOut :
      DyadicApproximationCarrier terminalPrecision terminalEndpoint terminalWindow
        terminalLedger terminalProvenance bundle pkg := transported.left
  have sameWindow : hsame window terminalWindow := transported.right
  have terminalCarrierFields := terminalCarrierOut
  rcases terminalCarrierFields with
    ⟨_terminalPrecisionUnary, _terminalEndpointUnary, terminalWindowUnary,
      terminalLedgerUnary, terminalProvenanceUnary, _terminalPrecisionEndpointWindow,
      _terminalWindowLedgerProvenance, _terminalPkg⟩
  have rationalContainmentUnary : UnaryHistory rationalContainment :=
    unary_cont_closed terminalWindowUnary terminalProvenanceUnary
      terminalWindowProvenanceContainment
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed terminalLedgerUnary terminalProvenanceUnary terminalLedgerProvenanceSeal
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed rationalContainmentUnary sealUnary containmentSealConsumer
  exact
    ⟨terminalCarrierOut, rationalContainmentUnary, sealUnary, consumerUnary, sameWindow,
      consumerPkg⟩

end BEDC.Derived.DyadicApproximationUp
