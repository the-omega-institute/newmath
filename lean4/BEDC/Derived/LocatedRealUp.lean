import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedRealCarrierSurface [AskSetup] [PackageSetup]
    (regseq interval schedule classifier pkgrow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory regseq ∧ UnaryHistory interval ∧ UnaryHistory schedule ∧
    UnaryHistory classifier ∧ UnaryHistory pkgrow ∧ Cont regseq schedule classifier ∧
      Cont interval classifier pkgrow ∧ PkgSig bundle pkgrow pkg

theorem LocatedRealCarrierSurface_regseqrat_classifier_stability [AskSetup] [PackageSetup]
    {regseq interval schedule classifier pkgrow regseq' interval' schedule' classifier'
      pkgrow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedRealCarrierSurface regseq interval schedule classifier pkgrow bundle pkg ->
      hsame regseq regseq' ->
        hsame interval interval' ->
          hsame schedule schedule' ->
            Cont regseq' schedule' classifier' ->
              Cont interval' classifier' pkgrow' ->
                PkgSig bundle pkgrow' pkg ->
                  LocatedRealCarrierSurface regseq' interval' schedule' classifier' pkgrow'
                      bundle pkg ∧
                    hsame classifier classifier' ∧ hsame pkgrow pkgrow' := by
  intro surface sameRegseq sameInterval sameSchedule classifierRoute' pkgrowRoute' pkgrowSig'
  have sameClassifier : hsame classifier classifier' :=
    cont_respects_hsame sameRegseq sameSchedule surface.right.right.right.right.right.left
      classifierRoute'
  have samePkgrow : hsame pkgrow pkgrow' :=
    cont_respects_hsame sameInterval sameClassifier surface.right.right.right.right.right.right.left
      pkgrowRoute'
  have transported :
      LocatedRealCarrierSurface regseq' interval' schedule' classifier' pkgrow' bundle pkg :=
    ⟨unary_transport surface.left sameRegseq,
      unary_transport surface.right.left sameInterval,
      unary_transport surface.right.right.left sameSchedule,
      unary_transport surface.right.right.right.left sameClassifier,
      unary_transport surface.right.right.right.right.left samePkgrow,
      classifierRoute',
      pkgrowRoute',
      pkgrowSig'⟩
  exact And.intro transported (And.intro sameClassifier samePkgrow)

theorem LocatedRealCarrierSurface_dyadic_interval_obligation [AskSetup] [PackageSetup]
    {regseq interval schedule classifier pkgrow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedRealCarrierSurface regseq interval schedule classifier pkgrow bundle pkg ->
      UnaryHistory interval ∧ UnaryHistory schedule ∧ UnaryHistory classifier ∧
        Cont regseq schedule classifier ∧ Cont interval classifier pkgrow ∧
          hsame classifier (append regseq schedule) ∧ hsame pkgrow (append interval classifier) ∧
            PkgSig bundle pkgrow pkg := by
  intro surface
  have intervalUnary : UnaryHistory interval :=
    surface.right.left
  have scheduleUnary : UnaryHistory schedule :=
    surface.right.right.left
  have classifierUnary : UnaryHistory classifier :=
    surface.right.right.right.left
  have classifierRow : Cont regseq schedule classifier :=
    surface.right.right.right.right.right.left
  have pkgrowRow : Cont interval classifier pkgrow :=
    surface.right.right.right.right.right.right.left
  have classifierSame : hsame classifier (append regseq schedule) :=
    classifierRow
  have pkgrowSame : hsame pkgrow (append interval classifier) :=
    pkgrowRow
  have pkgSig : PkgSig bundle pkgrow pkg :=
    surface.right.right.right.right.right.right.right
  exact And.intro intervalUnary
    (And.intro scheduleUnary
      (And.intro classifierUnary
        (And.intro classifierRow
          (And.intro pkgrowRow
            (And.intro classifierSame
              (And.intro pkgrowSame pkgSig))))))

theorem LocatedRealCarrierSurface_common_refinement_tail_empty [AskSetup] [PackageSetup]
    {regseqA intervalA scheduleA classifierA pkgrowA regseqB intervalB scheduleB classifierB
      pkgrowB commonSchedule commonClassifier commonEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedRealCarrierSurface regseqA intervalA scheduleA classifierA pkgrowA bundle pkg ->
      LocatedRealCarrierSurface regseqB intervalB scheduleB classifierB pkgrowB bundle pkg ->
        Cont scheduleA scheduleB commonSchedule ->
          Cont classifierA classifierB commonClassifier ->
            Cont commonClassifier commonSchedule commonEndpoint ->
              hsame commonEndpoint (append classifierA commonSchedule) ->
                hsame classifierB BHist.Empty := by
  intro _surfaceA _surfaceB _scheduleCommon classifierCommon endpointCommon endpointSame
  have endpointExpanded :
      commonEndpoint = append (append classifierA classifierB) commonSchedule :=
    endpointCommon.trans (congrArg (fun h => append h commonSchedule) classifierCommon)
  have classifierPrefixSame : hsame (append classifierA classifierB) classifierA :=
    append_right_cancel (k := commonSchedule) (endpointExpanded.symm.trans endpointSame)
  have classifierCycle : Cont classifierA classifierB classifierA :=
    cont_intro classifierPrefixSame.symm
  exact cont_right_unit_unique classifierCycle

theorem LocatedRealCarrierSurface_metric_consumer_handoff [AskSetup] [PackageSetup]
    {regseq interval schedule classifier pkgrow consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedRealCarrierSurface regseq interval schedule classifier pkgrow bundle pkg ->
      Cont pkgrow regseq consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory regseq ∧ UnaryHistory interval ∧ UnaryHistory schedule ∧
            UnaryHistory classifier ∧ UnaryHistory pkgrow ∧ UnaryHistory consumer ∧
              Cont regseq schedule classifier ∧ Cont interval classifier pkgrow ∧
                Cont pkgrow regseq consumer ∧ hsame classifier (append regseq schedule) ∧
                  hsame pkgrow (append interval classifier) ∧
                    hsame consumer (append pkgrow regseq) ∧ PkgSig bundle consumer pkg := by
  intro surface consumerCont consumerSig
  obtain ⟨regseqUnary, intervalUnary, scheduleUnary, classifierUnary, pkgrowUnary,
    classifierCont, pkgrowCont, _surfaceSig⟩ := surface
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed pkgrowUnary regseqUnary consumerCont
  have classifierSame : hsame classifier (append regseq schedule) :=
    classifierCont
  have pkgrowSame : hsame pkgrow (append interval classifier) :=
    pkgrowCont
  have consumerSame : hsame consumer (append pkgrow regseq) :=
    consumerCont
  exact
    ⟨regseqUnary, intervalUnary, scheduleUnary, classifierUnary, pkgrowUnary, consumerUnary,
      classifierCont, pkgrowCont, consumerCont, classifierSame, pkgrowSame, consumerSame,
      consumerSig⟩

theorem LocatedRealNameCertBoundary_rows [AskSetup] [PackageSetup]
    {regseq interval schedule classifier pkgrow regseq' interval' schedule' classifier'
      pkgrow' consumerRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedRealCarrierSurface regseq interval schedule classifier pkgrow bundle pkg ->
      hsame regseq regseq' -> hsame interval interval' -> hsame schedule schedule' ->
        Cont regseq' schedule' classifier' -> Cont interval' classifier' pkgrow' ->
          PkgSig bundle pkgrow' pkg -> Cont pkgrow' classifier' consumerRow ->
            PkgSig bundle consumerRow pkg ->
              LocatedRealCarrierSurface regseq' interval' schedule' classifier' pkgrow'
                  bundle pkg ∧
                UnaryHistory interval ∧ UnaryHistory schedule ∧ UnaryHistory classifier ∧
                  Cont regseq schedule classifier ∧ Cont interval classifier pkgrow ∧
                    UnaryHistory consumerRow ∧ Cont pkgrow' classifier' consumerRow ∧
                      PkgSig bundle consumerRow pkg := by
  intro surface sameRegseq sameInterval sameSchedule classifierRow' pkgrowRow' pkgrowSig'
    consumerRowRow consumerRowSig
  have transportedData :=
    LocatedRealCarrierSurface_regseqrat_classifier_stability surface sameRegseq sameInterval
      sameSchedule classifierRow' pkgrowRow' pkgrowSig'
  have surface' :
      LocatedRealCarrierSurface regseq' interval' schedule' classifier' pkgrow' bundle pkg :=
    transportedData.left
  have obligation :=
    LocatedRealCarrierSurface_dyadic_interval_obligation surface
  have pkgrowUnary' : UnaryHistory pkgrow' :=
    surface'.right.right.right.right.left
  have classifierUnary' : UnaryHistory classifier' :=
    surface'.right.right.right.left
  have consumerRowUnary : UnaryHistory consumerRow :=
    unary_cont_closed pkgrowUnary' classifierUnary' consumerRowRow
  exact
    ⟨surface',
      obligation.left,
      obligation.right.left,
      obligation.right.right.left,
      obligation.right.right.right.left,
      obligation.right.right.right.right.left,
      consumerRowUnary,
      consumerRowRow,
      consumerRowSig⟩

def LocatedRealCarrier [AskSetup] [PackageSetup]
    (stream schedule interval location realRow transport provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory schedule ∧ UnaryHistory interval ∧
    UnaryHistory location ∧ UnaryHistory realRow ∧ UnaryHistory transport ∧
      UnaryHistory provenance ∧ UnaryHistory endpoint ∧ Cont stream schedule interval ∧
        Cont interval location realRow ∧ Cont realRow transport provenance ∧
          Cont provenance schedule endpoint ∧ PkgSig bundle endpoint pkg

theorem LocatedRealCarrier_transport [AskSetup] [PackageSetup]
    {stream stream' schedule schedule' interval interval' location location' realRow realRow'
      transport transport' provenance provenance' endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedRealCarrier stream schedule interval location realRow transport provenance endpoint
        bundle pkg ->
      hsame stream stream' ->
        hsame schedule schedule' ->
          hsame interval interval' ->
            hsame location location' ->
              hsame realRow realRow' ->
                hsame transport transport' ->
                  Cont stream' schedule' interval' ->
                    Cont interval' location' realRow' ->
                      Cont realRow' transport' provenance' ->
                        Cont provenance' schedule' endpoint' ->
                          PkgSig bundle endpoint' pkg ->
                            LocatedRealCarrier stream' schedule' interval' location' realRow'
                                transport' provenance' endpoint' bundle pkg ∧
                              hsame provenance provenance' ∧ hsame endpoint endpoint' := by
  intro carrier sameStream sameSchedule sameInterval sameLocation sameRealRow sameTransport
    streamScheduleInterval' intervalLocationRealRow' realRowTransportProvenance'
    provenanceScheduleEndpoint' endpointPkg'
  obtain ⟨streamUnary, scheduleUnary, intervalUnary, locationUnary, realRowUnary,
    transportUnary, _provenanceUnary, _endpointUnary, streamScheduleInterval,
    intervalLocationRealRow, realRowTransportProvenance, provenanceScheduleEndpoint,
    _endpointPkg⟩ := carrier
  have streamUnary' : UnaryHistory stream' :=
    unary_transport streamUnary sameStream
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport scheduleUnary sameSchedule
  have intervalUnary' : UnaryHistory interval' :=
    unary_transport intervalUnary sameInterval
  have locationUnary' : UnaryHistory location' :=
    unary_transport locationUnary sameLocation
  have realRowUnary' : UnaryHistory realRow' :=
    unary_transport realRowUnary sameRealRow
  have transportUnary' : UnaryHistory transport' :=
    unary_transport transportUnary sameTransport
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameRealRow sameTransport realRowTransportProvenance
      realRowTransportProvenance'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed realRowUnary' transportUnary' realRowTransportProvenance'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameSchedule provenanceScheduleEndpoint
      provenanceScheduleEndpoint'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed provenanceUnary' scheduleUnary' provenanceScheduleEndpoint'
  exact
    ⟨⟨streamUnary', scheduleUnary', intervalUnary', locationUnary', realRowUnary',
        transportUnary', provenanceUnary', endpointUnary', streamScheduleInterval',
        intervalLocationRealRow', realRowTransportProvenance', provenanceScheduleEndpoint',
        endpointPkg'⟩,
      sameProvenance, sameEndpoint⟩

theorem LocatedRealCarrierSurface_realup_seal_compatibility [AskSetup] [PackageSetup]
    {regseq interval schedule classifier pkgrow sealRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedRealCarrierSurface regseq interval schedule classifier pkgrow bundle pkg ->
      Cont pkgrow schedule sealRow ->
        PkgSig bundle sealRow pkg ->
          UnaryHistory regseq ∧ UnaryHistory schedule ∧ UnaryHistory sealRow ∧
            Cont regseq schedule classifier ∧ Cont interval classifier pkgrow ∧
              Cont pkgrow schedule sealRow ∧ PkgSig bundle sealRow pkg := by
  intro surface sealCont sealSig
  obtain ⟨regseqUnary, _intervalUnary, scheduleUnary, _classifierUnary, pkgrowUnary,
    classifierCont, pkgrowCont, _surfaceSig⟩ := surface
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed pkgrowUnary scheduleUnary sealCont
  exact
    ⟨regseqUnary, scheduleUnary, sealUnary, classifierCont, pkgrowCont, sealCont, sealSig⟩

theorem LocatedRealCarrierSurface_scope_carrier_transport [AskSetup] [PackageSetup]
    {regseq interval schedule classifier pkgrow regseq' interval' schedule' classifier'
      pkgrow' consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedRealCarrierSurface regseq interval schedule classifier pkgrow bundle pkg ->
      hsame regseq regseq' ->
        hsame interval interval' ->
          hsame schedule schedule' ->
            Cont regseq' schedule' classifier' ->
              Cont interval' classifier' pkgrow' ->
                PkgSig bundle pkgrow' pkg ->
                  Cont pkgrow' classifier' consumer ->
                    PkgSig bundle consumer pkg ->
                      LocatedRealCarrierSurface regseq' interval' schedule' classifier'
                          pkgrow' bundle pkg ∧
                        UnaryHistory consumer ∧ hsame classifier classifier' ∧
                          hsame pkgrow pkgrow' ∧ Cont pkgrow' classifier' consumer ∧
                            PkgSig bundle consumer pkg := by
  intro surface sameRegseq sameInterval sameSchedule classifierCont' pkgrowCont' pkgrowSig'
    consumerCont consumerSig
  have transportedData :=
    LocatedRealCarrierSurface_regseqrat_classifier_stability surface sameRegseq sameInterval
      sameSchedule classifierCont' pkgrowCont' pkgrowSig'
  have surface' :
      LocatedRealCarrierSurface regseq' interval' schedule' classifier' pkgrow' bundle pkg :=
    transportedData.left
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed surface'.right.right.right.right.left surface'.right.right.right.left
      consumerCont
  exact
    ⟨surface', consumerUnary, transportedData.right.left, transportedData.right.right,
      consumerCont, consumerSig⟩

theorem LocatedRealCarrier_realup_regseqrat_boundary [AskSetup] [PackageSetup]
    {stream schedule interval location realRow transport provenance endpoint consumerRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedRealCarrier stream schedule interval location realRow transport provenance endpoint
        bundle pkg ->
      Cont endpoint realRow consumerRow ->
        PkgSig bundle consumerRow pkg ->
          UnaryHistory stream ∧ UnaryHistory schedule ∧ UnaryHistory interval ∧
            UnaryHistory realRow ∧ UnaryHistory endpoint ∧ UnaryHistory consumerRow ∧
              Cont stream schedule interval ∧ Cont interval location realRow ∧
                Cont realRow transport provenance ∧ Cont provenance schedule endpoint ∧
                  Cont endpoint realRow consumerRow ∧ PkgSig bundle consumerRow pkg := by
  intro carrier consumerRowCont consumerRowSig
  obtain ⟨streamUnary, scheduleUnary, intervalUnary, _locationUnary, realRowUnary,
    _transportUnary, _provenanceUnary, endpointUnary, streamScheduleInterval,
    intervalLocationRealRow, realRowTransportProvenance, provenanceScheduleEndpoint,
    _endpointSig⟩ := carrier
  have consumerRowUnary : UnaryHistory consumerRow :=
    unary_cont_closed endpointUnary realRowUnary consumerRowCont
  exact
    ⟨streamUnary, scheduleUnary, intervalUnary, realRowUnary, endpointUnary, consumerRowUnary,
      streamScheduleInterval, intervalLocationRealRow, realRowTransportProvenance,
      provenanceScheduleEndpoint, consumerRowCont, consumerRowSig⟩

theorem LocatedRealCarrier_metric_consumer_empty_boundary [AskSetup] [PackageSetup]
    {stream schedule interval location realRow transport provenance endpoint consumerRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedRealCarrier stream schedule interval location realRow transport provenance endpoint
        bundle pkg ->
      Cont endpoint realRow consumerRow ->
        hsame consumerRow BHist.Empty ->
          hsame endpoint BHist.Empty ∧ hsame realRow BHist.Empty := by
  intro _carrier consumerRowCont consumerRowEmpty
  have appendedEmpty : append endpoint realRow = BHist.Empty := by
    cases consumerRowCont
    exact consumerRowEmpty
  have parts : endpoint = BHist.Empty ∧ realRow = BHist.Empty :=
    append_eq_empty_iff.mp appendedEmpty
  exact And.intro parts.left parts.right

theorem LocatedRealCarrier_metric_consumer_handoff [AskSetup] [PackageSetup]
    {stream schedule interval location realRow transport provenance endpoint consumerRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedRealCarrier stream schedule interval location realRow transport provenance endpoint
        bundle pkg ->
      Cont endpoint realRow consumerRow ->
        PkgSig bundle consumerRow pkg ->
          UnaryHistory interval ∧ UnaryHistory realRow ∧ UnaryHistory provenance ∧
            UnaryHistory endpoint ∧ UnaryHistory consumerRow ∧
              Cont stream schedule interval ∧ Cont interval location realRow ∧
                Cont realRow transport provenance ∧ Cont provenance schedule endpoint ∧
                  Cont endpoint realRow consumerRow ∧
                    hsame interval (append stream schedule) ∧
                      hsame realRow (append interval location) ∧
                        hsame provenance (append realRow transport) ∧
                          hsame endpoint (append provenance schedule) ∧
                            hsame consumerRow (append endpoint realRow) ∧
                              PkgSig bundle consumerRow pkg := by
  intro carrier consumerRowCont consumerRowSig
  obtain ⟨_streamUnary, _scheduleUnary, intervalUnary, _locationUnary, realRowUnary,
    _transportUnary, provenanceUnary, endpointUnary, streamScheduleInterval,
    intervalLocationRealRow, realRowTransportProvenance, provenanceScheduleEndpoint,
    _endpointSig⟩ := carrier
  have consumerRowUnary : UnaryHistory consumerRow :=
    unary_cont_closed endpointUnary realRowUnary consumerRowCont
  exact
    ⟨intervalUnary, realRowUnary, provenanceUnary, endpointUnary, consumerRowUnary,
      streamScheduleInterval, intervalLocationRealRow, realRowTransportProvenance,
      provenanceScheduleEndpoint, consumerRowCont, streamScheduleInterval, intervalLocationRealRow,
      realRowTransportProvenance, provenanceScheduleEndpoint, consumerRowCont, consumerRowSig⟩

theorem LocatedRealCarrier_common_refinement_gluing [AskSetup] [PackageSetup]
    {stream stream' schedule schedule' interval interval' location location' realRow realRow'
      transport transport' provenance provenance' endpoint endpoint' commonWindow commonEndpoint
      commonPkgrow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedRealCarrier stream schedule interval location realRow transport provenance endpoint
        bundle pkg ->
      LocatedRealCarrier stream' schedule' interval' location' realRow' transport' provenance'
          endpoint' bundle pkg ->
        hsame schedule commonWindow ->
          hsame schedule' commonWindow ->
            Cont provenance commonWindow commonEndpoint ->
              Cont provenance' commonWindow commonEndpoint ->
                Cont endpoint endpoint' commonPkgrow ->
                  PkgSig bundle commonPkgrow pkg ->
                    UnaryHistory commonWindow ∧ UnaryHistory commonEndpoint ∧
                      hsame commonEndpoint (append provenance commonWindow) ∧
                        hsame commonEndpoint (append provenance' commonWindow) ∧
                          UnaryHistory commonPkgrow ∧
                            hsame commonPkgrow (append endpoint endpoint') ∧
                              PkgSig bundle commonPkgrow pkg := by
  intro carrier carrier' sameSchedule sameSchedule' provenanceWindow provenanceWindow'
    endpointPair commonPkgrowSig
  obtain ⟨_streamUnary, scheduleUnary, _intervalUnary, _locationUnary, _realRowUnary,
    _transportUnary, provenanceUnary, endpointUnary, _streamScheduleInterval,
    _intervalLocationRealRow, _realRowTransportProvenance, _provenanceScheduleEndpoint,
    _endpointSig⟩ := carrier
  obtain ⟨_streamUnary', scheduleUnary', _intervalUnary', _locationUnary', _realRowUnary',
    _transportUnary', _provenanceUnary', endpointUnary', _streamScheduleInterval',
    _intervalLocationRealRow', _realRowTransportProvenance', _provenanceScheduleEndpoint',
    _endpointSig'⟩ := carrier'
  have commonWindowUnary : UnaryHistory commonWindow :=
    unary_transport scheduleUnary sameSchedule
  have _commonWindowUnary' : UnaryHistory commonWindow :=
    unary_transport scheduleUnary' sameSchedule'
  have commonEndpointUnary : UnaryHistory commonEndpoint :=
    unary_cont_closed provenanceUnary commonWindowUnary provenanceWindow
  have commonPkgrowUnary : UnaryHistory commonPkgrow :=
    unary_cont_closed endpointUnary endpointUnary' endpointPair
  exact
    ⟨commonWindowUnary, commonEndpointUnary, provenanceWindow, provenanceWindow',
      commonPkgrowUnary, endpointPair, commonPkgrowSig⟩

theorem LocatedRealCarrierSurface_scoped_source_boundary [AskSetup] [PackageSetup]
    {regseq interval schedule classifier pkgrow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedRealCarrierSurface regseq interval schedule classifier pkgrow bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            LocatedRealCarrierSurface regseq interval schedule classifier row bundle pkg)
          (fun row : BHist =>
            LocatedRealCarrierSurface regseq interval schedule classifier row bundle pkg)
          (fun row : BHist =>
            LocatedRealCarrierSurface regseq interval schedule classifier row bundle pkg)
          (fun left right : BHist =>
            LocatedRealCarrierSurface regseq interval schedule classifier left bundle pkg ∧
              LocatedRealCarrierSurface regseq interval schedule classifier right bundle pkg ∧
                hsame left right) ∧
        UnaryHistory regseq ∧ UnaryHistory interval ∧ UnaryHistory schedule ∧
          UnaryHistory classifier ∧ UnaryHistory pkgrow ∧ Cont regseq schedule classifier ∧
            Cont interval classifier pkgrow ∧ PkgSig bundle pkgrow pkg := by
  intro surface
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            LocatedRealCarrierSurface regseq interval schedule classifier row bundle pkg)
          (fun row : BHist =>
            LocatedRealCarrierSurface regseq interval schedule classifier row bundle pkg)
          (fun row : BHist =>
            LocatedRealCarrierSurface regseq interval schedule classifier row bundle pkg)
          (fun left right : BHist =>
            LocatedRealCarrierSurface regseq interval schedule classifier left bundle pkg ∧
              LocatedRealCarrierSurface regseq interval schedule classifier right bundle pkg ∧
                hsame left right) := {
    core := {
      carrier_inhabited := Exists.intro pkgrow surface
      equiv_refl := by
        intro row source
        exact And.intro source (And.intro source (hsame_refl row))
      equiv_symm := by
        intro row row' classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro row row' row'' classifiedLeft classifiedRight
        exact And.intro classifiedLeft.left
          (And.intro classifiedRight.right.left
            (hsame_trans classifiedLeft.right.right classifiedRight.right.right))
      carrier_respects_equiv := by
        intro row row' classified _source
        exact classified.right.left
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro surface.left
      (And.intro surface.right.left
        (And.intro surface.right.right.left
          (And.intro surface.right.right.right.left
            (And.intro surface.right.right.right.right.left
              (And.intro surface.right.right.right.right.right.left
                (And.intro surface.right.right.right.right.right.right.left
                  surface.right.right.right.right.right.right.right)))))))

end BEDC.Derived.LocatedRealUp
