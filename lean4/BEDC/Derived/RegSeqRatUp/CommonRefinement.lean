import BEDC.Derived.RegSeqRatUp

namespace BEDC.Derived.RegSeqRatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegSeqRatStreamCarrier_common_refinement_classifier_determinacy [AskSetup]
    [PackageSetup]
    {schedule0 index0 endpoint0 radius0 regularity0 provenance0 readback0 schedule1 index1
      endpoint1 radius1 regularity1 provenance1 readback1 unionSchedule unionIndex unionEndpoint
      unionRadius unionRegularity unionProvenance unionReadback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatStreamCarrier schedule0 index0 endpoint0 radius0 regularity0 provenance0 readback0
        bundle pkg ->
      RegSeqRatStreamCarrier schedule1 index1 endpoint1 radius1 regularity1 provenance1 readback1
          bundle pkg ->
        hsame schedule0 unionSchedule ->
          hsame index0 unionIndex ->
            hsame radius0 unionRadius ->
              hsame provenance0 unionProvenance ->
                hsame schedule1 unionSchedule ->
                  hsame index1 unionIndex ->
                    hsame radius1 unionRadius ->
                      hsame provenance1 unionProvenance ->
                        Cont unionSchedule unionIndex unionEndpoint ->
                          Cont unionEndpoint unionRadius unionRegularity ->
                            Cont unionRegularity unionProvenance unionReadback ->
                              PkgSig bundle unionReadback pkg ->
                                RegSeqRatClassifier endpoint0 radius0 regularity0 readback0
                                    unionEndpoint unionRadius unionRegularity unionReadback ∧
                                  RegSeqRatClassifier endpoint1 radius1 regularity1 readback1
                                      unionEndpoint unionRadius unionRegularity unionReadback ∧
                                    hsame readback0 unionReadback ∧
                                      hsame readback1 unionReadback := by
  intro carrier0 carrier1 sameSchedule0 sameIndex0 sameRadius0 sameProvenance0
  intro sameSchedule1 sameIndex1 sameRadius1 sameProvenance1
  intro unionEndpointRow unionRegularityRow unionReadbackRow unionPkgSig
  rcases carrier0 with
    ⟨scheduleUnary0, indexUnary0, endpointUnary0, radiusUnary0, regularityUnary0,
      provenanceUnary0, readbackUnary0, endpointRow0, regularityRow0, readbackRow0,
      _pkgSig0⟩
  rcases carrier1 with
    ⟨_scheduleUnary1, _indexUnary1, endpointUnary1, radiusUnary1, regularityUnary1,
      provenanceUnary1, readbackUnary1, endpointRow1, regularityRow1, readbackRow1,
      _pkgSig1⟩
  have unionScheduleUnary : UnaryHistory unionSchedule :=
    unary_transport scheduleUnary0 sameSchedule0
  have unionIndexUnary : UnaryHistory unionIndex :=
    unary_transport indexUnary0 sameIndex0
  have unionRadiusUnary : UnaryHistory unionRadius :=
    unary_transport radiusUnary0 sameRadius0
  have unionProvenanceUnary : UnaryHistory unionProvenance :=
    unary_transport provenanceUnary0 sameProvenance0
  have unionEndpointUnary : UnaryHistory unionEndpoint :=
    unary_cont_closed unionScheduleUnary unionIndexUnary unionEndpointRow
  have unionRegularityUnary : UnaryHistory unionRegularity :=
    unary_cont_closed unionEndpointUnary unionRadiusUnary unionRegularityRow
  have unionReadbackUnary : UnaryHistory unionReadback :=
    unary_cont_closed unionRegularityUnary unionProvenanceUnary unionReadbackRow
  have sameEndpoint0 : hsame endpoint0 unionEndpoint :=
    cont_respects_hsame sameSchedule0 sameIndex0 endpointRow0 unionEndpointRow
  have sameRegularity0 : hsame regularity0 unionRegularity :=
    cont_respects_hsame sameEndpoint0 sameRadius0 regularityRow0 unionRegularityRow
  have sameReadback0 : hsame readback0 unionReadback :=
    cont_respects_hsame sameRegularity0 sameProvenance0 readbackRow0 unionReadbackRow
  have sameEndpoint1 : hsame endpoint1 unionEndpoint :=
    cont_respects_hsame sameSchedule1 sameIndex1 endpointRow1 unionEndpointRow
  have sameRegularity1 : hsame regularity1 unionRegularity :=
    cont_respects_hsame sameEndpoint1 sameRadius1 regularityRow1 unionRegularityRow
  have sameReadback1 : hsame readback1 unionReadback :=
    cont_respects_hsame sameRegularity1 sameProvenance1 readbackRow1 unionReadbackRow
  have classifier0 :
      RegSeqRatClassifier endpoint0 radius0 regularity0 readback0 unionEndpoint unionRadius
          unionRegularity unionReadback :=
    ⟨endpointUnary0, radiusUnary0, regularityUnary0, readbackUnary0, unionEndpointUnary,
      unionRadiusUnary, unionRegularityUnary, unionReadbackUnary, sameEndpoint0, sameRadius0,
      sameRegularity0, sameReadback0⟩
  have classifier1 :
      RegSeqRatClassifier endpoint1 radius1 regularity1 readback1 unionEndpoint unionRadius
          unionRegularity unionReadback :=
    ⟨endpointUnary1, radiusUnary1, regularityUnary1, readbackUnary1, unionEndpointUnary,
      unionRadiusUnary, unionRegularityUnary, unionReadbackUnary, sameEndpoint1, sameRadius1,
      sameRegularity1, sameReadback1⟩
  exact ⟨classifier0, classifier1, sameReadback0, sameReadback1⟩

end BEDC.Derived.RegSeqRatUp
