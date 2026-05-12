import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RationalBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RationalBallPacket [AskSetup] [PackageSetup]
    (center radius order transport containment provenance name endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory center ∧ UnaryHistory radius ∧ UnaryHistory order ∧
    UnaryHistory transport ∧ UnaryHistory containment ∧ UnaryHistory provenance ∧
      UnaryHistory name ∧ Cont center radius order ∧ Cont order containment transport ∧
        Cont transport provenance endpoint ∧ PkgSig bundle endpoint pkg

theorem RationalBallPacket_refinement_transport [AskSetup] [PackageSetup]
    {center radius order transport containment provenance name endpoint center' radius' order'
      transport' containment' provenance' name' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalBallPacket center radius order transport containment provenance name endpoint
        bundle pkg ->
      hsame center center' ->
        hsame radius radius' ->
          hsame containment containment' ->
            hsame provenance provenance' ->
              hsame name name' ->
                Cont center' radius' order' ->
                  Cont order' containment' transport' ->
                    Cont transport' provenance' endpoint' ->
                      PkgSig bundle endpoint' pkg ->
                        RationalBallPacket center' radius' order' transport' containment'
                            provenance' name' endpoint' bundle pkg ∧
                          hsame order order' ∧ hsame transport transport' ∧
                            hsame endpoint endpoint' := by
  intro packet sameCenter sameRadius sameContainment sameProvenance sameName
    centerRadiusOrder' orderContainmentTransport' transportProvenanceEndpoint' endpointPkg'
  rcases packet with
    ⟨centerUnary, radiusUnary, orderUnary, transportUnary, containmentUnary,
      provenanceUnary, nameUnary, centerRadiusOrder, orderContainmentTransport,
      transportProvenanceEndpoint, _endpointPkg⟩
  have sameOrder : hsame order order' :=
    cont_respects_hsame sameCenter sameRadius centerRadiusOrder centerRadiusOrder'
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame sameOrder sameContainment orderContainmentTransport
      orderContainmentTransport'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameTransport sameProvenance transportProvenanceEndpoint
      transportProvenanceEndpoint'
  have centerUnary' : UnaryHistory center' := unary_transport centerUnary sameCenter
  have radiusUnary' : UnaryHistory radius' := unary_transport radiusUnary sameRadius
  have orderUnary' : UnaryHistory order' := unary_transport orderUnary sameOrder
  have transportUnary' : UnaryHistory transport' :=
    unary_transport transportUnary sameTransport
  have containmentUnary' : UnaryHistory containment' :=
    unary_transport containmentUnary sameContainment
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have nameUnary' : UnaryHistory name' := unary_transport nameUnary sameName
  exact
    ⟨⟨centerUnary', radiusUnary', orderUnary', transportUnary', containmentUnary',
        provenanceUnary', nameUnary', centerRadiusOrder', orderContainmentTransport',
        transportProvenanceEndpoint', endpointPkg'⟩,
      sameOrder, sameTransport, sameEndpoint⟩

theorem RationalBallPacket_radius_refinement_transport [AskSetup] [PackageSetup]
    {center radius order transport containment provenance name endpoint radius' order'
      transport' endpoint' : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalBallPacket center radius order transport containment provenance name endpoint
        bundle pkg ->
      hsame radius radius' ->
        Cont center radius' order' ->
          Cont order' containment transport' ->
            Cont transport' provenance endpoint' ->
              PkgSig bundle endpoint' pkg ->
                RationalBallPacket center radius' order' transport' containment provenance name
                    endpoint' bundle pkg ∧
                  hsame order order' ∧ hsame transport transport' ∧
                    hsame endpoint endpoint' := by
  intro packet sameRadius centerRadiusOrder' orderContainmentTransport'
    transportProvenanceEndpoint' endpointPkg'
  obtain ⟨centerUnary, radiusUnary, _orderUnary, _transportUnary, containmentUnary,
    provenanceUnary, nameUnary, centerRadiusOrder, orderContainmentTransport,
    transportProvenanceEndpoint, _endpointPkg⟩ := packet
  have sameOrder : hsame order order' :=
    cont_respects_hsame rfl sameRadius centerRadiusOrder centerRadiusOrder'
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame sameOrder rfl orderContainmentTransport orderContainmentTransport'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameTransport rfl transportProvenanceEndpoint
      transportProvenanceEndpoint'
  have radiusUnary' : UnaryHistory radius' := unary_transport radiusUnary sameRadius
  have orderUnary' : UnaryHistory order' :=
    unary_cont_closed centerUnary radiusUnary' centerRadiusOrder'
  have transportUnary' : UnaryHistory transport' :=
    unary_cont_closed orderUnary' containmentUnary orderContainmentTransport'
  exact
    ⟨⟨centerUnary, radiusUnary', orderUnary', transportUnary', containmentUnary,
        provenanceUnary, nameUnary, centerRadiusOrder', orderContainmentTransport',
        transportProvenanceEndpoint', endpointPkg'⟩,
      sameOrder, sameTransport, sameEndpoint⟩

theorem RationalBallPacket_realup_window_handoff [AskSetup] [PackageSetup]
    {center radius order transport containment provenance name endpoint consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalBallPacket center radius order transport containment provenance name endpoint
        bundle pkg ->
      Cont containment endpoint consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory center ∧ UnaryHistory radius ∧ UnaryHistory order ∧
            UnaryHistory containment ∧ UnaryHistory endpoint ∧ UnaryHistory consumer ∧
              Cont center radius order ∧ Cont order containment transport ∧
                Cont transport provenance endpoint ∧ Cont containment endpoint consumer ∧
                  PkgSig bundle endpoint pkg ∧ PkgSig bundle consumer pkg := by
  intro packet consumerRow consumerPkg
  obtain ⟨centerUnary, radiusUnary, orderUnary, transportUnary, containmentUnary,
    provenanceUnary, _nameUnary, centerRadiusOrder, orderContainmentTransport,
    transportProvenanceEndpoint, endpointPkg⟩ := packet
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed transportUnary provenanceUnary transportProvenanceEndpoint
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed containmentUnary endpointUnary consumerRow
  exact
    ⟨centerUnary, radiusUnary, orderUnary, containmentUnary, endpointUnary, consumerUnary,
      centerRadiusOrder, orderContainmentTransport, transportProvenanceEndpoint, consumerRow,
      endpointPkg, consumerPkg⟩

theorem RationalBallPacket_ledger_exactness_certificate [AskSetup] [PackageSetup]
    {center radius order transport containment provenance name endpoint consumer ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalBallPacket center radius order transport containment provenance name endpoint
        bundle pkg ->
      Cont containment endpoint consumer ->
        Cont consumer provenance ledger ->
          PkgSig bundle ledger pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  hsame row ledger ∧ UnaryHistory row ∧ Cont consumer provenance row ∧
                    PkgSig bundle row pkg)
                (fun row : BHist =>
                  UnaryHistory consumer ∧ UnaryHistory provenance ∧ Cont consumer provenance row)
                (fun row : BHist =>
                  PkgSig bundle row pkg ∧ UnaryHistory center ∧ UnaryHistory radius ∧
                    UnaryHistory containment)
                (fun row row' : BHist => psame bundle pkg pkg ∧ hsame row row') := by
  intro packet containmentEndpointConsumer consumerProvenanceLedger ledgerPkg
  obtain ⟨centerUnary, radiusUnary, _orderUnary, transportUnary, containmentUnary,
    provenanceUnary, _nameUnary, _centerRadiusOrder, _orderContainmentTransport,
    transportProvenanceEndpoint, _endpointPkg⟩ := packet
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed transportUnary provenanceUnary transportProvenanceEndpoint
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed containmentUnary endpointUnary containmentEndpointConsumer
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed consumerUnary provenanceUnary consumerProvenanceLedger
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro ledger
          ⟨hsame_refl ledger, ledgerUnary, consumerProvenanceLedger, ledgerPkg⟩
      equiv_refl := by
        intro row sourceRow
        exact ⟨PkgSig_psame_intro sourceRow.right.right.right sourceRow.right.right.right
          (hsame_refl row), hsame_refl row⟩
      equiv_symm := by
        intro _row _row' classified
        exact ⟨classified.left, hsame_symm classified.right⟩
      equiv_trans := by
        intro _row _row' _row'' leftClassified rightClassified
        exact ⟨leftClassified.left, hsame_trans leftClassified.right rightClassified.right⟩
      carrier_respects_equiv := by
        intro _row _row' classified sourceRow
        cases classified.right
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact ⟨consumerUnary, provenanceUnary, sourceRow.right.right.left⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right.right, centerUnary, radiusUnary, containmentUnary⟩
  }

theorem RationalBallPacket_center_transport_obligation [AskSetup] [PackageSetup]
    {center radius order transport containment provenance name endpoint centerNew orderNew
      transportNew endpointNew consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalBallPacket center radius order transport containment provenance name endpoint
        bundle pkg ->
      hsame center centerNew ->
        Cont centerNew radius orderNew ->
          Cont orderNew containment transportNew ->
            Cont transportNew provenance endpointNew ->
              Cont containment endpointNew consumer ->
                PkgSig bundle endpointNew pkg ->
                  RationalBallPacket centerNew radius orderNew transportNew containment
                      provenance name endpointNew bundle pkg ∧
                    UnaryHistory consumer ∧ hsame order orderNew ∧
                      hsame transport transportNew ∧ hsame endpoint endpointNew := by
  intro packet sameCenter centerRadiusOrder orderContainmentTransport
    transportProvenanceEndpoint containmentEndpointConsumer endpointPkg
  have transported :
      RationalBallPacket centerNew radius orderNew transportNew containment provenance name
          endpointNew bundle pkg ∧
        hsame order orderNew ∧ hsame transport transportNew ∧
          hsame endpoint endpointNew :=
    RationalBallPacket_refinement_transport packet sameCenter (hsame_refl radius)
      (hsame_refl containment) (hsame_refl provenance) (hsame_refl name) centerRadiusOrder
      orderContainmentTransport transportProvenanceEndpoint endpointPkg
  rcases transported with ⟨targetPacket, sameOrder, sameTransport, sameEndpoint⟩
  rcases targetPacket with
    ⟨centerUnary, radiusUnary, orderUnary, transportUnary, containmentUnary,
      provenanceUnary, nameUnary, centerRadiusOrder', orderContainmentTransport',
      transportProvenanceEndpoint', endpointPkg'⟩
  have endpointUnary : UnaryHistory endpointNew :=
    unary_cont_closed transportUnary provenanceUnary transportProvenanceEndpoint'
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed containmentUnary endpointUnary containmentEndpointConsumer
  exact
    ⟨⟨centerUnary, radiusUnary, orderUnary, transportUnary, containmentUnary,
        provenanceUnary, nameUnary, centerRadiusOrder', orderContainmentTransport',
        transportProvenanceEndpoint', endpointPkg'⟩,
      consumerUnary, sameOrder, sameTransport, sameEndpoint⟩

end BEDC.Derived.RationalBallUp
