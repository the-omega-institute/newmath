import BEDC.Derived.DyadicApproximationUp
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

end BEDC.Derived.DyadicApproximationUp
