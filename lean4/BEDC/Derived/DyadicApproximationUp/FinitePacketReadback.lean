import BEDC.Derived.DyadicApproximationUp
import BEDC.Derived.DyadicApproximationUp.FiniteMeshEnclosure
import BEDC.FKernel.Bundle

namespace BEDC.Derived.DyadicApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicApproximationCarrier_refined_finite_packet_readback_determinacy [AskSetup]
    [PackageSetup]
    {precision endpoint window ledger provenance precision2 endpoint2 window2 ledger2
      provenance2 commonPrecision commonEndpoint commonWindow commonLedger commonProvenance
      consumer consumer2 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicApproximationCarrier precision endpoint window ledger provenance bundle pkg ->
      DyadicApproximationCarrier precision2 endpoint2 window2 ledger2 provenance2 bundle pkg ->
        hsame precision commonPrecision ->
          hsame precision2 commonPrecision ->
            hsame endpoint commonEndpoint ->
              hsame endpoint2 commonEndpoint ->
                hsame ledger commonLedger ->
                  hsame ledger2 commonLedger ->
                    hsame provenance commonProvenance ->
                      hsame provenance2 commonProvenance ->
                        Cont commonPrecision commonEndpoint commonWindow ->
                          Cont commonWindow commonLedger commonProvenance ->
                            Cont commonWindow commonProvenance consumer ->
                              Cont commonWindow commonProvenance consumer2 ->
                                PkgSig bundle consumer pkg ->
                                  PkgSig bundle consumer2 pkg ->
                                    DyadicApproximationCarrier commonPrecision commonEndpoint
                                        commonWindow commonLedger commonProvenance bundle pkg ∧
                                      hsame window commonWindow ∧ hsame window2 commonWindow ∧
                                        UnaryHistory consumer ∧ UnaryHistory consumer2 ∧
                                          hsame consumer consumer2 ∧
                                            PkgSig bundle consumer pkg ∧
                                              PkgSig bundle consumer2 pkg := by
  intro carrier carrier2 samePrecision samePrecision2 sameEndpoint sameEndpoint2 sameLedger
  intro sameLedger2 sameProvenance sameProvenance2 commonPrecisionEndpointWindow
  intro commonWindowLedgerProvenance commonWindowProvenanceConsumer
  intro commonWindowProvenanceConsumer2 consumerPkg consumer2Pkg
  have refined :
      DyadicApproximationCarrier commonPrecision commonEndpoint commonWindow commonLedger
          commonProvenance bundle pkg ∧
        hsame window commonWindow ∧ hsame window2 commonWindow :=
    DyadicApproximationCarrier_common_precision_refinement carrier carrier2 samePrecision
      samePrecision2 sameEndpoint sameEndpoint2 sameLedger sameLedger2 sameProvenance
      sameProvenance2 commonPrecisionEndpointWindow commonWindowLedgerProvenance
  rcases refined with ⟨commonCarrier, sameWindow, sameWindow2⟩
  rcases commonCarrier with
    ⟨commonPrecisionUnary, commonEndpointUnary, commonWindowUnary, commonLedgerUnary,
      commonProvenanceUnary, commonPrecisionEndpointWindow', commonWindowLedgerProvenance',
      commonPkg⟩
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed commonWindowUnary commonProvenanceUnary commonWindowProvenanceConsumer
  have consumer2Unary : UnaryHistory consumer2 :=
    unary_cont_closed commonWindowUnary commonProvenanceUnary commonWindowProvenanceConsumer2
  have sameConsumer : hsame consumer consumer2 :=
    cont_deterministic commonWindowProvenanceConsumer commonWindowProvenanceConsumer2
  exact
    ⟨⟨commonPrecisionUnary, commonEndpointUnary, commonWindowUnary, commonLedgerUnary,
        commonProvenanceUnary, commonPrecisionEndpointWindow', commonWindowLedgerProvenance',
        commonPkg⟩,
      sameWindow, sameWindow2, consumerUnary, consumer2Unary, sameConsumer, consumerPkg,
      consumer2Pkg⟩

theorem DyadicApproximationCarrier_finite_packet_readback_exhaustion
    [AskSetup] [PackageSetup]
    {precision endpoint window ledger provenance terminalPrecision terminalEndpoint
      terminalWindow terminalLedger terminalProvenance meshCell enclosure validatedRead sealRow
      reread consumer : BHist}
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
                            Cont terminalWindow terminalProvenance consumer ->
                              PkgSig bundle meshCell pkg ->
                                PkgSig bundle enclosure pkg ->
                                  PkgSig bundle validatedRead pkg ->
                                    PkgSig bundle sealRow pkg ->
                                      PkgSig bundle consumer pkg ->
                                        DyadicApproximationCarrier terminalPrecision
                                            terminalEndpoint terminalWindow terminalLedger
                                            terminalProvenance bundle pkg ∧
                                          UnaryHistory validatedRead ∧
                                            UnaryHistory sealRow ∧
                                              UnaryHistory reread ∧
                                                UnaryHistory consumer ∧
                                                  hsame reread consumer ∧
                                                    PkgSig bundle validatedRead pkg ∧
                                                      PkgSig bundle consumer pkg := by
  intro carrier samePrecision sameEndpoint sameLedger sameProvenance
  intro terminalPrecisionEndpointWindow terminalWindowLedgerProvenance
  intro terminalWindowProvenanceMesh meshProvenanceEnclosure enclosureProvenanceValidated
  intro terminalLedgerProvenanceSeal terminalWindowProvenanceReread
  intro terminalWindowProvenanceConsumer meshPkg enclosurePkg validatedPkg sealPkg consumerPkg
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
    ⟨terminalCarrier, _meshUnary, _enclosureUnary, validatedUnary, sealUnary, _sameWindow,
      validatedPkgOut⟩
  rcases terminalCarrier with
    ⟨terminalPrecisionUnary, terminalEndpointUnary, terminalWindowUnary, terminalLedgerUnary,
      terminalProvenanceUnary, terminalPrecisionEndpointWindow',
      terminalWindowLedgerProvenance', terminalPkg⟩
  have rereadUnary : UnaryHistory reread :=
    unary_cont_closed terminalWindowUnary terminalProvenanceUnary terminalWindowProvenanceReread
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed terminalWindowUnary terminalProvenanceUnary
      terminalWindowProvenanceConsumer
  have sameReadbacks : hsame reread consumer :=
    cont_deterministic terminalWindowProvenanceReread terminalWindowProvenanceConsumer
  exact
    ⟨⟨terminalPrecisionUnary, terminalEndpointUnary, terminalWindowUnary,
        terminalLedgerUnary, terminalProvenanceUnary, terminalPrecisionEndpointWindow',
        terminalWindowLedgerProvenance', terminalPkg⟩,
      validatedUnary, sealUnary, rereadUnary, consumerUnary, sameReadbacks, validatedPkgOut,
      consumerPkg⟩

end BEDC.Derived.DyadicApproximationUp
