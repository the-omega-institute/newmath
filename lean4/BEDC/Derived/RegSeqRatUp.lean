import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegSeqRatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegSeqRatStreamCarrier [AskSetup] [PackageSetup]
    (schedule index endpoint radius regularity provenance readback : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory schedule ∧ UnaryHistory index ∧ UnaryHistory endpoint ∧ UnaryHistory radius ∧
    UnaryHistory regularity ∧ UnaryHistory provenance ∧ UnaryHistory readback ∧
      Cont schedule index endpoint ∧ Cont endpoint radius regularity ∧
        Cont regularity provenance readback ∧ PkgSig bundle readback pkg

def RegSeqRatClassifier [AskSetup] [PackageSetup]
    (endpoint radius regularity readback endpoint' radius' regularity' readback' : BHist) : Prop :=
  UnaryHistory endpoint ∧ UnaryHistory radius ∧ UnaryHistory regularity ∧
    UnaryHistory readback ∧ UnaryHistory endpoint' ∧ UnaryHistory radius' ∧
      UnaryHistory regularity' ∧ UnaryHistory readback' ∧ hsame endpoint endpoint' ∧
        hsame radius radius' ∧ hsame regularity regularity' ∧ hsame readback readback'

theorem RegSeqRatClassifier_transport [AskSetup] [PackageSetup]
    {schedule index endpoint radius regularity provenance readback schedule' index' endpoint' radius'
      regularity' provenance' readback' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance readback bundle pkg ->
      RegSeqRatClassifier endpoint radius regularity readback endpoint radius regularity readback ->
        hsame schedule schedule' ->
          hsame index index' ->
            hsame radius radius' ->
              hsame provenance provenance' ->
                Cont schedule' index' endpoint' ->
                  Cont endpoint' radius' regularity' ->
                    Cont regularity' provenance' readback' ->
                      PkgSig bundle readback' pkg ->
                        RegSeqRatStreamCarrier schedule' index' endpoint' radius' regularity'
                            provenance' readback' bundle pkg ∧
                          RegSeqRatClassifier endpoint radius regularity readback endpoint' radius'
                              regularity' readback' ∧ hsame readback readback' := by
  intro carrier classifier sameSchedule sameIndex sameRadius sameProvenance
  intro scheduleIndexEndpoint' endpointRadiusRegularity' regularityProvenanceReadback' pkgReadback'
  cases carrier with
  | intro scheduleUnary carrierRest =>
      cases carrierRest with
      | intro indexUnary carrierRest =>
          cases carrierRest with
          | intro _endpointUnary carrierRest =>
              cases carrierRest with
              | intro _radiusUnary carrierRest =>
                  cases carrierRest with
                  | intro _regularityUnary carrierRest =>
                      cases carrierRest with
                      | intro provenanceUnary carrierRest =>
                          cases carrierRest with
                          | intro _readbackUnary carrierRest =>
                              cases carrierRest with
                              | intro scheduleIndexEndpoint carrierRest =>
                                  cases carrierRest with
                                  | intro endpointRadiusRegularity carrierRest =>
                                      cases carrierRest with
                                      | intro regularityProvenanceReadback _pkgReadback =>
                                          cases classifier with
                                          | intro endpointUnary classifierRest =>
                                              cases classifierRest with
                                              | intro radiusUnary classifierRest =>
                                                  cases classifierRest with
                                                  | intro regularityUnary classifierRest =>
                                                      cases classifierRest with
                                                      | intro readbackUnary _classifierRest =>
                                                          have scheduleUnary' :
                                                              UnaryHistory schedule' :=
                                                            unary_transport scheduleUnary sameSchedule
                                                          have indexUnary' : UnaryHistory index' :=
                                                            unary_transport indexUnary sameIndex
                                                          have radiusUnary' : UnaryHistory radius' :=
                                                            unary_transport radiusUnary sameRadius
                                                          have provenanceUnary' :
                                                              UnaryHistory provenance' :=
                                                            unary_transport provenanceUnary
                                                              sameProvenance
                                                          have endpointUnary' :
                                                              UnaryHistory endpoint' :=
                                                            unary_cont_closed scheduleUnary'
                                                              indexUnary' scheduleIndexEndpoint'
                                                          have regularityUnary' :
                                                              UnaryHistory regularity' :=
                                                            unary_cont_closed endpointUnary'
                                                              radiusUnary' endpointRadiusRegularity'
                                                          have readbackUnary' :
                                                              UnaryHistory readback' :=
                                                            unary_cont_closed regularityUnary'
                                                              provenanceUnary'
                                                              regularityProvenanceReadback'
                                                          have sameEndpoint :
                                                              hsame endpoint endpoint' :=
                                                            cont_respects_hsame sameSchedule
                                                              sameIndex scheduleIndexEndpoint
                                                              scheduleIndexEndpoint'
                                                          have sameRegularity :
                                                              hsame regularity regularity' :=
                                                            cont_respects_hsame sameEndpoint
                                                              sameRadius endpointRadiusRegularity
                                                              endpointRadiusRegularity'
                                                          have sameReadback :
                                                              hsame readback readback' :=
                                                            cont_respects_hsame sameRegularity
                                                              sameProvenance
                                                              regularityProvenanceReadback
                                                              regularityProvenanceReadback'
                                                          have carrier' :
                                                              RegSeqRatStreamCarrier schedule' index'
                                                                  endpoint' radius' regularity'
                                                                  provenance' readback' bundle pkg :=
                                                            ⟨scheduleUnary', indexUnary',
                                                              endpointUnary', radiusUnary',
                                                              regularityUnary', provenanceUnary',
                                                              readbackUnary', scheduleIndexEndpoint',
                                                              endpointRadiusRegularity',
                                                              regularityProvenanceReadback',
                                                              pkgReadback'⟩
                                                          have classifier' :
                                                              RegSeqRatClassifier endpoint radius
                                                                  regularity readback endpoint' radius'
                                                                  regularity' readback' :=
                                                            ⟨endpointUnary, radiusUnary,
                                                              regularityUnary, readbackUnary,
                                                              endpointUnary', radiusUnary',
                                                              regularityUnary', readbackUnary',
                                                              sameEndpoint, sameRadius,
                                                              sameRegularity, sameReadback⟩
                                                          exact ⟨carrier', classifier', sameReadback⟩

end BEDC.Derived.RegSeqRatUp
