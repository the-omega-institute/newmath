import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegSeqRatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem RegSeqRatStreamCarrier_finite_window_transport_closure [AskSetup] [PackageSetup]
    {schedule index endpoint radius regularity provenance readback schedule' index' endpoint'
      radius' regularity' provenance' readback' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance readback bundle pkg ->
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
                        hsame endpoint endpoint' ∧ hsame regularity regularity' ∧
                          hsame readback readback' := by
  intro carrier sameSchedule sameIndex sameRadius sameProvenance
  intro scheduleIndexEndpoint' endpointRadiusRegularity' regularityProvenanceReadback' pkgReadback'
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport carrier.left sameSchedule
  have indexUnary' : UnaryHistory index' :=
    unary_transport carrier.right.left sameIndex
  have radiusUnary' : UnaryHistory radius' :=
    unary_transport carrier.right.right.right.left sameRadius
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport carrier.right.right.right.right.right.left sameProvenance
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed scheduleUnary' indexUnary' scheduleIndexEndpoint'
  have regularityUnary' : UnaryHistory regularity' :=
    unary_cont_closed endpointUnary' radiusUnary' endpointRadiusRegularity'
  have readbackUnary' : UnaryHistory readback' :=
    unary_cont_closed regularityUnary' provenanceUnary' regularityProvenanceReadback'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameSchedule sameIndex
      carrier.right.right.right.right.right.right.right.left scheduleIndexEndpoint'
  have sameRegularity : hsame regularity regularity' :=
    cont_respects_hsame sameEndpoint sameRadius
      carrier.right.right.right.right.right.right.right.right.left endpointRadiusRegularity'
  have sameReadback : hsame readback readback' :=
    cont_respects_hsame sameRegularity sameProvenance
      carrier.right.right.right.right.right.right.right.right.right.left
      regularityProvenanceReadback'
  have carrier' :
      RegSeqRatStreamCarrier schedule' index' endpoint' radius' regularity' provenance'
        readback' bundle pkg :=
    ⟨scheduleUnary', indexUnary', endpointUnary', radiusUnary', regularityUnary',
      provenanceUnary', readbackUnary', scheduleIndexEndpoint', endpointRadiusRegularity',
      regularityProvenanceReadback', pkgReadback'⟩
  exact And.intro carrier'
    (And.intro sameEndpoint (And.intro sameRegularity sameReadback))

theorem RegSeqRatStreamCarrier_regularity_obligation_surface [AskSetup] [PackageSetup]
    {schedule index endpoint radius regularity provenance readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance readback
        bundle pkg ->
      SemanticNameCert
          (fun row : BHist => exists e : BHist,
            RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance e
                bundle pkg ∧ hsame row e)
          (fun row : BHist => exists e : BHist,
            RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance e
                bundle pkg ∧ hsame row e)
          (fun row : BHist => exists e : BHist,
            RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance e
                bundle pkg ∧ hsame row e)
          hsame ∧ Cont schedule index endpoint ∧ Cont endpoint radius regularity ∧
            Cont regularity provenance readback ∧ PkgSig bundle readback pkg := by
  intro carrier
  rcases carrier with
    ⟨scheduleUnary, indexUnary, endpointUnary, radiusUnary, regularityUnary, provenanceUnary,
      readbackUnary, scheduleIndexEndpoint, endpointRadiusRegularity,
      regularityProvenanceReadback, pkgSig⟩
  have carrierPacket :
      RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance readback
          bundle pkg :=
    ⟨scheduleUnary, indexUnary, endpointUnary, radiusUnary, regularityUnary, provenanceUnary,
      readbackUnary, scheduleIndexEndpoint, endpointRadiusRegularity,
      regularityProvenanceReadback, pkgSig⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => exists e : BHist,
            RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance e
                bundle pkg ∧ hsame row e)
          (fun row : BHist => exists e : BHist,
            RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance e
                bundle pkg ∧ hsame row e)
          (fun row : BHist => exists e : BHist,
            RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance e
                bundle pkg ∧ hsame row e)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro readback
            (Exists.intro readback (And.intro carrierPacket (hsame_refl readback)))
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro row row' same
          exact hsame_symm same
        equiv_trans := by
          intro row row' row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row row' same source
          cases source with
          | intro e data =>
              cases data with
              | intro packetE sameRowE =>
                  exact Exists.intro e
                    (And.intro packetE (hsame_trans (hsame_symm same) sameRowE))
      }
      pattern_sound := by
        intro _row source
        exact source
      ledger_sound := by
        intro _row source
        exact source
    }
  exact ⟨cert, scheduleIndexEndpoint, endpointRadiusRegularity, regularityProvenanceReadback, pkgSig⟩

theorem RegSeqRatStreamCarrier_real_seal_handoff [AskSetup] [PackageSetup]
    {schedule index endpoint radius regularity provenance readback endpoint' regularity'
      readback' : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance readback
        bundle pkg ->
      hsame endpoint endpoint' ->
        Cont endpoint' radius regularity' ->
          Cont regularity' provenance readback' ->
            PkgSig bundle readback' pkg ->
              RegSeqRatStreamCarrier schedule index endpoint' radius regularity' provenance
                  readback' bundle pkg ∧
                hsame regularity regularity' ∧ hsame readback readback' := by
  intro carrier sameEndpoint targetRegularity targetReadback targetPkg
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport carrier.right.right.left sameEndpoint
  have targetEndpoint : Cont schedule index endpoint' := by
    cases sameEndpoint
    exact carrier.right.right.right.right.right.right.right.left
  have sameRegularity : hsame regularity regularity' :=
    cont_respects_hsame sameEndpoint (hsame_refl radius)
      carrier.right.right.right.right.right.right.right.right.left targetRegularity
  have regularityUnary' : UnaryHistory regularity' :=
    unary_cont_closed endpointUnary' carrier.right.right.right.left targetRegularity
  have sameReadback : hsame readback readback' :=
    cont_respects_hsame sameRegularity (hsame_refl provenance)
      carrier.right.right.right.right.right.right.right.right.right.left targetReadback
  have readbackUnary' : UnaryHistory readback' :=
    unary_cont_closed regularityUnary' carrier.right.right.right.right.right.left targetReadback
  have targetCarrier :
      RegSeqRatStreamCarrier schedule index endpoint' radius regularity' provenance readback'
          bundle pkg :=
    ⟨carrier.left,
      carrier.right.left,
      endpointUnary',
      carrier.right.right.right.left,
      regularityUnary',
      carrier.right.right.right.right.right.left,
      readbackUnary',
      targetEndpoint,
      targetRegularity,
      targetReadback,
      targetPkg⟩
  exact ⟨targetCarrier, sameRegularity, sameReadback⟩

theorem RegSeqRatStreamCarrier_classifier_transport [AskSetup] [PackageSetup]
    {schedule index endpoint radius regularity provenance readback schedule' index' endpoint'
      radius' regularity' provenance' readback' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance readback
        bundle pkg ->
      hsame schedule schedule' ->
        hsame index index' ->
        hsame endpoint endpoint' ->
          hsame radius radius' ->
            hsame provenance provenance' ->
              Cont schedule' index' endpoint' ->
                Cont endpoint' radius' regularity' ->
                  Cont regularity' provenance' readback' ->
                    PkgSig bundle readback' pkg ->
                      RegSeqRatStreamCarrier schedule' index' endpoint' radius' regularity'
                          provenance' readback' bundle pkg ∧
                        hsame endpoint endpoint' ∧ hsame regularity regularity' ∧
                          hsame readback readback' := by
  intro carrier sameSchedule sameIndex sameEndpoint sameRadius sameProvenance
  intro scheduleIndexEndpoint' endpointRadiusRegularity' regularityProvenanceReadback' pkgSig'
  rcases carrier with
    ⟨scheduleUnary, indexUnary, endpointUnary, radiusUnary, regularityUnary, provenanceUnary,
      readbackUnary, scheduleIndexEndpoint, endpointRadiusRegularity,
      regularityProvenanceReadback, _pkgSig⟩
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport scheduleUnary sameSchedule
  have indexUnary' : UnaryHistory index' :=
    unary_transport indexUnary sameIndex
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport endpointUnary sameEndpoint
  have radiusUnary' : UnaryHistory radius' :=
    unary_transport radiusUnary sameRadius
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have sameRegularity : hsame regularity regularity' :=
    cont_respects_hsame sameEndpoint sameRadius endpointRadiusRegularity
      endpointRadiusRegularity'
  have sameReadback : hsame readback readback' :=
    cont_respects_hsame sameRegularity sameProvenance regularityProvenanceReadback
      regularityProvenanceReadback'
  have regularityUnary' : UnaryHistory regularity' :=
    unary_transport regularityUnary sameRegularity
  have readbackUnary' : UnaryHistory readback' :=
    unary_transport readbackUnary sameReadback
  have carrier' :
      RegSeqRatStreamCarrier schedule' index' endpoint' radius' regularity' provenance'
          readback' bundle pkg :=
    ⟨scheduleUnary', indexUnary', endpointUnary', radiusUnary', regularityUnary',
      provenanceUnary', readbackUnary', scheduleIndexEndpoint', endpointRadiusRegularity',
      regularityProvenanceReadback', pkgSig'⟩
  exact ⟨carrier', sameEndpoint, sameRegularity, sameReadback⟩

theorem RegSeqRatStreamCarrier_dyadic_radius_ledger_readback [AskSetup] [PackageSetup]
    {schedule index endpoint radius regularity provenance readback endpoint' radius' regularity'
      readback' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance readback
        bundle pkg ->
      RegSeqRatClassifier endpoint radius regularity readback endpoint' radius' regularity'
          readback' ->
        UnaryHistory radius ∧ UnaryHistory regularity ∧ UnaryHistory radius' ∧
          UnaryHistory regularity' ∧ hsame radius radius' ∧ hsame regularity regularity' ∧
            PkgSig bundle readback pkg := by
  intro carrier classifier
  obtain ⟨_scheduleUnary, _indexUnary, _endpointUnary, radiusUnary, regularityUnary,
    _provenanceUnary, _readbackUnary, _scheduleIndexEndpoint, _endpointRadiusRegularity,
    _regularityProvenanceReadback, pkgSig⟩ := carrier
  obtain ⟨_endpointUnary, _radiusUnary, _regularityUnary, _readbackUnary,
    _endpointUnary', radiusUnary', regularityUnary', _readbackUnary', _sameEndpoint,
    sameRadius, sameRegularity, _sameReadback⟩ := classifier
  exact ⟨radiusUnary, regularityUnary, radiusUnary', regularityUnary', sameRadius,
    sameRegularity, pkgSig⟩

theorem RegSeqRatStreamCarrier_finite_window_transport_obligation [AskSetup] [PackageSetup]
    {schedule index endpoint radius regularity provenance readback schedule' index' endpoint'
      radius' regularity' provenance' readback' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance readback
        bundle pkg ->
      hsame schedule schedule' ->
        hsame index index' ->
          hsame endpoint endpoint' ->
            hsame radius radius' ->
              hsame provenance provenance' ->
                Cont schedule' index' endpoint' ->
                  Cont endpoint' radius' regularity' ->
                    Cont regularity' provenance' readback' ->
                      PkgSig bundle readback' pkg ->
                        RegSeqRatStreamCarrier schedule' index' endpoint' radius' regularity'
                            provenance' readback' bundle pkg ∧
                          hsame regularity regularity' ∧ hsame readback readback' := by
  intro carrier sameSchedule sameIndex sameEndpoint sameRadius sameProvenance
  intro scheduleIndexEndpoint' endpointRadiusRegularity' regularityProvenanceReadback' pkgSig'
  rcases carrier with
    ⟨scheduleUnary, indexUnary, _endpointUnary, radiusUnary, regularityUnary, provenanceUnary,
      readbackUnary, _scheduleIndexEndpoint, endpointRadiusRegularity,
      regularityProvenanceReadback, _pkgSig⟩
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport scheduleUnary sameSchedule
  have indexUnary' : UnaryHistory index' :=
    unary_transport indexUnary sameIndex
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport _endpointUnary sameEndpoint
  have radiusUnary' : UnaryHistory radius' :=
    unary_transport radiusUnary sameRadius
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have sameRegularity : hsame regularity regularity' :=
    cont_respects_hsame sameEndpoint sameRadius endpointRadiusRegularity
      endpointRadiusRegularity'
  have sameReadback : hsame readback readback' :=
    cont_respects_hsame sameRegularity sameProvenance regularityProvenanceReadback
      regularityProvenanceReadback'
  have regularityUnary' : UnaryHistory regularity' :=
    unary_transport regularityUnary sameRegularity
  have readbackUnary' : UnaryHistory readback' :=
    unary_transport readbackUnary sameReadback
  have carrier' :
      RegSeqRatStreamCarrier schedule' index' endpoint' radius' regularity' provenance'
          readback' bundle pkg :=
    ⟨scheduleUnary', indexUnary', endpointUnary', radiusUnary', regularityUnary',
      provenanceUnary', readbackUnary', scheduleIndexEndpoint', endpointRadiusRegularity',
      regularityProvenanceReadback', pkgSig'⟩
  exact ⟨carrier', sameRegularity, sameReadback⟩

theorem RegSeqRatClassifier_dyadic_radius_observation [AskSetup] [PackageSetup]
    {endpoint radius regularity readback endpoint' radius' regularity' readback' : BHist} :
    RegSeqRatClassifier endpoint radius regularity readback endpoint' radius' regularity'
        readback' ->
      UnaryHistory endpoint ∧ UnaryHistory radius ∧ UnaryHistory endpoint' ∧
        UnaryHistory radius' ∧ hsame radius radius' ∧ hsame regularity regularity' ∧
          hsame readback readback' := by
  intro classifier
  rcases classifier with
    ⟨endpointUnary, radiusUnary, _regularityUnary, _readbackUnary, endpointUnary',
      radiusUnary', _regularityUnary', _readbackUnary', _sameEndpoint, sameRadius,
      sameRegularity, sameReadback⟩
  exact ⟨endpointUnary, radiusUnary, endpointUnary', radiusUnary', sameRadius,
    sameRegularity, sameReadback⟩

end BEDC.Derived.RegSeqRatUp
