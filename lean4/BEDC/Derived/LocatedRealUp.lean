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

theorem LocatedRealCarrierSurface_metric_consumer_handoff_certificate [AskSetup]
    [PackageSetup]
    {regseq interval schedule classifier pkgrow consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedRealCarrierSurface regseq interval schedule classifier pkgrow bundle pkg ->
      Cont classifier pkgrow consumer ->
        PkgSig bundle consumer pkg ->
          SemanticNameCert
              (fun row : BHist =>
                exists c : BHist, Cont classifier pkgrow c ∧ PkgSig bundle c pkg ∧
                  hsame row c)
              (fun row : BHist =>
                exists c : BHist, Cont classifier pkgrow c ∧ PkgSig bundle c pkg ∧
                  hsame row c)
              (fun row : BHist =>
                exists c : BHist, Cont classifier pkgrow c ∧ PkgSig bundle c pkg ∧
                  hsame row c)
              hsame ∧
            UnaryHistory consumer ∧ hsame consumer (append classifier pkgrow) ∧
              PkgSig bundle consumer pkg := by
  intro surface consumerCont consumerSig
  have classifierUnary : UnaryHistory classifier :=
    surface.right.right.right.left
  have pkgrowUnary : UnaryHistory pkgrow :=
    surface.right.right.right.right.left
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed classifierUnary pkgrowUnary consumerCont
  let Carrier := fun row : BHist =>
    exists c : BHist, Cont classifier pkgrow c ∧ PkgSig bundle c pkg ∧ hsame row c
  have consumerCarrier : Carrier consumer :=
    Exists.intro consumer
      (And.intro consumerCont (And.intro consumerSig (hsame_refl consumer)))
  have cert : SemanticNameCert Carrier Carrier Carrier hsame := {
    core := {
      carrier_inhabited := Exists.intro consumer consumerCarrier
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other sameRows rowSource
        cases rowSource with
        | intro c witness =>
            exact Exists.intro c
              (And.intro witness.left
                (And.intro witness.right.left
                  (hsame_trans (hsame_symm sameRows) witness.right.right)))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro consumerUnary (And.intro consumerCont consumerSig))

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

end BEDC.Derived.LocatedRealUp
