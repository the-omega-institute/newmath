import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyNamePacket [AskSetup] [PackageSetup]
    (schedule observation radius ledger «seal» provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory schedule ∧ UnaryHistory observation ∧ UnaryHistory radius ∧
    UnaryHistory ledger ∧ UnaryHistory «seal» ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
      PkgSig bundle provenance pkg

theorem RegularCauchyNamePacket_streamname_handoff [AskSetup] [PackageSetup]
    {schedule observation radius ledger «seal» provenance name window point handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNamePacket schedule observation radius ledger «seal» provenance name bundle pkg ->
      Cont schedule observation window -> Cont window radius point -> Cont point «seal» handoff ->
        PkgSig bundle handoff pkg ->
          UnaryHistory schedule /\ UnaryHistory observation /\ UnaryHistory radius /\
            UnaryHistory window /\ UnaryHistory point /\ UnaryHistory handoff /\
              Cont schedule observation window /\ Cont window radius point /\
                Cont point «seal» handoff /\ PkgSig bundle provenance pkg /\
                  PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist
  intro packet windowCont pointCont handoffCont handoffPkg
  have scheduleUnary : UnaryHistory schedule := packet.left
  have observationUnary : UnaryHistory observation := packet.right.left
  have radiusUnary : UnaryHistory radius := packet.right.right.left
  have sealUnary : UnaryHistory «seal» := packet.right.right.right.right.left
  have provenancePkg : PkgSig bundle provenance pkg :=
    packet.right.right.right.right.right.right.right
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary observationUnary windowCont
  have pointUnary : UnaryHistory point :=
    unary_cont_closed windowUnary radiusUnary pointCont
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed pointUnary sealUnary handoffCont
  constructor
  · exact scheduleUnary
  · constructor
    · exact observationUnary
    · constructor
      · exact radiusUnary
      · constructor
        · exact windowUnary
        · constructor
          · exact pointUnary
          · constructor
            · exact handoffUnary
            · constructor
              · exact windowCont
              · constructor
                · exact pointCont
                · constructor
                  · exact handoffCont
                  · constructor
                    · exact provenancePkg
                    · exact handoffPkg

theorem RegularCauchyNamePacket_handoff_nonempty_iff [AskSetup] [PackageSetup]
    {schedule observation radius ledger sealRow provenance name window point handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNamePacket schedule observation radius ledger sealRow provenance name bundle pkg ->
      Cont schedule observation window ->
        Cont window radius point ->
          Cont point sealRow handoff ->
            PkgSig bundle handoff pkg ->
              UnaryHistory handoff ∧
                (((hsame handoff BHist.Empty -> False) ↔
                    (hsame point BHist.Empty -> False) ∨
                      (hsame sealRow BHist.Empty -> False))) ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle handoff pkg := by
  intro packet windowCont pointCont handoffCont handoffPkg
  obtain ⟨scheduleUnary, observationUnary, radiusUnary, _ledgerUnary, sealUnary,
    _provenanceUnary, _nameUnary, provenancePkg⟩ := packet
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary observationUnary windowCont
  have pointUnary : UnaryHistory point :=
    unary_cont_closed windowUnary radiusUnary pointCont
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed pointUnary sealUnary handoffCont
  have handoffNonempty :
      ((hsame handoff BHist.Empty -> False) ↔
        (hsame point BHist.Empty -> False) ∨
          (hsame sealRow BHist.Empty -> False)) := by
    cases handoffCont
    exact append_nonempty_iff
  exact ⟨handoffUnary, handoffNonempty, provenancePkg, handoffPkg⟩

theorem RegularCauchyNamePacket_common_window_classifier_scope [AskSetup] [PackageSetup]
    {schedule observation radius ledger sealRow provenance name window window' point point' :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNamePacket schedule observation radius ledger sealRow provenance name bundle
        pkg ->
      Cont schedule observation window ->
        Cont schedule observation window' ->
          Cont window radius point ->
            Cont window' radius point' ->
              hsame window window' ∧ hsame point point' ∧ UnaryHistory window ∧
                UnaryHistory window' ∧ UnaryHistory point ∧ UnaryHistory point' ∧
                  PkgSig bundle provenance pkg := by
  intro packet windowRow windowRow' pointRow pointRow'
  obtain ⟨scheduleUnary, observationUnary, radiusUnary, _ledgerUnary, _sealUnary,
    _provenanceUnary, _nameUnary, provenancePkg⟩ := packet
  have sameWindow : hsame window window' :=
    cont_deterministic windowRow windowRow'
  have samePoint : hsame point point' :=
    cont_respects_hsame sameWindow (hsame_refl radius) pointRow pointRow'
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary observationUnary windowRow
  have windowUnary' : UnaryHistory window' :=
    unary_cont_closed scheduleUnary observationUnary windowRow'
  have pointUnary : UnaryHistory point :=
    unary_cont_closed windowUnary radiusUnary pointRow
  have pointUnary' : UnaryHistory point' :=
    unary_cont_closed windowUnary' radiusUnary pointRow'
  exact
    ⟨sameWindow, samePoint, windowUnary, windowUnary', pointUnary, pointUnary',
      provenancePkg⟩

def RegularCauchyNameCarrier [AskSetup] [PackageSetup]
    (schedule observation radius ledger sealRow provenance namecert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory schedule ∧ UnaryHistory observation ∧ UnaryHistory radius ∧
    UnaryHistory ledger ∧ UnaryHistory sealRow ∧ UnaryHistory provenance ∧
      UnaryHistory namecert ∧ Cont schedule observation radius ∧
        Cont radius ledger sealRow ∧ Cont sealRow provenance endpoint ∧
          PkgSig bundle endpoint pkg

theorem RegularCauchyNameCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {schedule observation radius ledger sealRow provenance namecert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNameCarrier schedule observation radius ledger sealRow provenance namecert
        endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          RegularCauchyNameCarrier schedule observation radius ledger sealRow provenance
            namecert endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          RegularCauchyNameCarrier schedule observation radius ledger sealRow provenance
            namecert endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          RegularCauchyNameCarrier schedule observation radius ledger sealRow provenance
            namecert endpoint bundle pkg ∧ hsame row endpoint)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro packet (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' sameRows sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem RegularCauchyNameCarrier_classifier_transport_stability [AskSetup] [PackageSetup]
    {schedule observation radius ledger sealRow provenance namecert endpoint schedule'
      observation' radius' ledger' sealRow' provenance' namecert' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNameCarrier schedule observation radius ledger sealRow provenance namecert
        endpoint bundle pkg ->
      hsame schedule schedule' ->
        hsame observation observation' ->
          hsame ledger ledger' ->
            hsame provenance provenance' ->
              hsame namecert namecert' ->
                Cont schedule' observation' radius' ->
                  Cont radius' ledger' sealRow' ->
                    Cont sealRow' provenance' endpoint' ->
                      PkgSig bundle endpoint' pkg ->
                        RegularCauchyNameCarrier schedule' observation' radius' ledger'
                            sealRow' provenance' namecert' endpoint' bundle pkg ∧
                          hsame radius radius' ∧ hsame sealRow sealRow' ∧
                            hsame endpoint endpoint' := by
  intro carrier scheduleSame observationSame ledgerSame provenanceSame namecertSame
    scheduleObservationRow radiusLedgerRow sealProvenanceRow endpointPkg
  obtain ⟨scheduleUnary, observationUnary, _radiusUnary, ledgerUnary, _sealUnary,
    provenanceUnary, namecertUnary, scheduleObservationRadius, radiusLedgerSeal,
    sealProvenanceEndpoint, _endpointPkg⟩ := carrier
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport scheduleUnary scheduleSame
  have observationUnary' : UnaryHistory observation' :=
    unary_transport observationUnary observationSame
  have radiusUnary' : UnaryHistory radius' :=
    unary_cont_closed scheduleUnary' observationUnary' scheduleObservationRow
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_transport ledgerUnary ledgerSame
  have sealUnary' : UnaryHistory sealRow' :=
    unary_cont_closed radiusUnary' ledgerUnary' radiusLedgerRow
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary provenanceSame
  have namecertUnary' : UnaryHistory namecert' :=
    unary_transport namecertUnary namecertSame
  have radiusSame : hsame radius radius' :=
    cont_respects_hsame scheduleSame observationSame scheduleObservationRadius
      scheduleObservationRow
  have sealSame : hsame sealRow sealRow' :=
    cont_respects_hsame radiusSame ledgerSame radiusLedgerSeal radiusLedgerRow
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame sealSame provenanceSame sealProvenanceEndpoint sealProvenanceRow
  exact
    ⟨⟨scheduleUnary', observationUnary', radiusUnary', ledgerUnary', sealUnary',
      provenanceUnary', namecertUnary', scheduleObservationRow, radiusLedgerRow,
      sealProvenanceRow, endpointPkg⟩, radiusSame, sealSame, endpointSame⟩

theorem RegularCauchyNameCarrier_realup_seal_boundary [AskSetup] [PackageSetup]
    {schedule observation radius ledger sealRow provenance namecert endpoint sealRow'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNameCarrier schedule observation radius ledger sealRow provenance namecert
        endpoint bundle pkg ->
      hsame sealRow sealRow' ->
        Cont radius ledger sealRow' ->
          Cont sealRow' provenance endpoint' ->
            PkgSig bundle endpoint' pkg ->
              RegularCauchyNameCarrier schedule observation radius ledger sealRow'
                provenance namecert endpoint' bundle pkg ∧ hsame endpoint endpoint' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier sameSeal radiusLedgerSeal' sealProvenanceEndpoint' endpointPkg'
  obtain ⟨scheduleUnary, observationUnary, radiusUnary, ledgerUnary, sealUnary,
    provenanceUnary, namecertUnary, scheduleObservationRadius, radiusLedgerSeal,
    sealProvenanceEndpoint, _endpointPkg⟩ := carrier
  have sealUnary' : UnaryHistory sealRow' :=
    unary_transport sealUnary sameSeal
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameSeal (hsame_refl provenance) sealProvenanceEndpoint
      sealProvenanceEndpoint'
  have transported :
      RegularCauchyNameCarrier schedule observation radius ledger sealRow' provenance
        namecert endpoint' bundle pkg := by
    exact ⟨scheduleUnary, observationUnary, radiusUnary, ledgerUnary, sealUnary',
      provenanceUnary, namecertUnary, scheduleObservationRadius, radiusLedgerSeal',
      sealProvenanceEndpoint', endpointPkg'⟩
  exact ⟨transported, sameEndpoint⟩

theorem RegularCauchyNameCarrier_seal_readback_exhaustion [AskSetup] [PackageSetup]
    {schedule observation radius ledger sealRow provenance namecert endpoint sealRow'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNameCarrier schedule observation radius ledger sealRow provenance namecert
        endpoint bundle pkg ->
      Cont radius ledger sealRow' ->
        Cont sealRow' provenance endpoint' ->
          PkgSig bundle endpoint' pkg ->
            hsame sealRow sealRow' ∧ hsame endpoint endpoint' ∧ UnaryHistory sealRow ∧
              UnaryHistory sealRow' ∧ PkgSig bundle endpoint pkg ∧
                PkgSig bundle endpoint' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier radiusLedgerSeal' sealProvenanceEndpoint' endpointPkg'
  obtain ⟨_scheduleUnary, _observationUnary, radiusUnary, ledgerUnary, sealUnary,
    _provenanceUnary, _namecertUnary, _scheduleObservationRadius, radiusLedgerSeal,
    sealProvenanceEndpoint, endpointPkg⟩ := carrier
  have sameSeal : hsame sealRow sealRow' :=
    cont_deterministic radiusLedgerSeal radiusLedgerSeal'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameSeal (hsame_refl provenance) sealProvenanceEndpoint
      sealProvenanceEndpoint'
  have sealUnary' : UnaryHistory sealRow' :=
    unary_cont_closed radiusUnary ledgerUnary radiusLedgerSeal'
  exact ⟨sameSeal, sameEndpoint, sealUnary, sealUnary', endpointPkg, endpointPkg'⟩

theorem RegularCauchyNameCarrier_schedule_radius_lock [AskSetup] [PackageSetup]
    {schedule observation radius ledger sealRow provenance namecert endpoint window
      readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNameCarrier schedule observation radius ledger sealRow provenance namecert
        endpoint bundle pkg ->
      Cont schedule observation window ->
        Cont window radius readback ->
          PkgSig bundle readback pkg ->
            hsame radius window ∧ UnaryHistory window ∧ UnaryHistory readback ∧
              Cont schedule observation window ∧ Cont window radius readback ∧
                PkgSig bundle endpoint pkg ∧ PkgSig bundle readback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier scheduleObservationWindow windowRadiusReadback readbackPkg
  obtain ⟨scheduleUnary, observationUnary, radiusUnary, _ledgerUnary, _sealUnary,
    _provenanceUnary, _namecertUnary, scheduleObservationRadius, _radiusLedgerSeal,
    _sealProvenanceEndpoint, endpointPkg⟩ := carrier
  have radiusSameWindow : hsame radius window :=
    cont_deterministic scheduleObservationRadius scheduleObservationWindow
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary observationUnary scheduleObservationWindow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed windowUnary radiusUnary windowRadiusReadback
  exact
    ⟨radiusSameWindow, windowUnary, readbackUnary, scheduleObservationWindow,
      windowRadiusReadback, endpointPkg, readbackPkg⟩

theorem RegularCauchyNameCarrier_common_window_transport_triad [AskSetup] [PackageSetup]
    {schedule observation radius ledger sealRow provenance namecert endpoint window window'
      readback readback' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNameCarrier schedule observation radius ledger sealRow provenance namecert
        endpoint bundle pkg ->
      Cont schedule observation window ->
        Cont schedule observation window' ->
          Cont window radius readback ->
            Cont window' radius readback' ->
              PkgSig bundle readback pkg ->
                PkgSig bundle readback' pkg ->
                  hsame window window' ∧ hsame readback readback' ∧
                    hsame radius window ∧ hsame radius window' ∧ UnaryHistory window ∧
                      UnaryHistory window' ∧ UnaryHistory readback ∧
                        UnaryHistory readback' ∧ PkgSig bundle endpoint pkg ∧
                          PkgSig bundle readback pkg ∧ PkgSig bundle readback' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier scheduleObservationWindow scheduleObservationWindow'
    windowRadiusReadback windowRadiusReadback' readbackPkg readbackPkg'
  obtain ⟨scheduleUnary, observationUnary, radiusUnary, _ledgerUnary, _sealUnary,
    _provenanceUnary, _namecertUnary, scheduleObservationRadius, _radiusLedgerSeal,
    _sealProvenanceEndpoint, endpointPkg⟩ := carrier
  have sameWindow : hsame window window' :=
    cont_deterministic scheduleObservationWindow scheduleObservationWindow'
  have sameReadback : hsame readback readback' :=
    cont_respects_hsame sameWindow (hsame_refl radius) windowRadiusReadback
      windowRadiusReadback'
  have radiusSameWindow : hsame radius window :=
    cont_deterministic scheduleObservationRadius scheduleObservationWindow
  have radiusSameWindow' : hsame radius window' :=
    cont_deterministic scheduleObservationRadius scheduleObservationWindow'
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary observationUnary scheduleObservationWindow
  have windowUnary' : UnaryHistory window' :=
    unary_cont_closed scheduleUnary observationUnary scheduleObservationWindow'
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed windowUnary radiusUnary windowRadiusReadback
  have readbackUnary' : UnaryHistory readback' :=
    unary_cont_closed windowUnary' radiusUnary windowRadiusReadback'
  exact
    ⟨sameWindow, sameReadback, radiusSameWindow, radiusSameWindow', windowUnary,
      windowUnary', readbackUnary, readbackUnary', endpointPkg, readbackPkg, readbackPkg'⟩

theorem RegularCauchyNameCarrier_dyadic_radius_transport_composition [AskSetup]
    [PackageSetup]
    {schedule observation radius ledger sealRow provenance namecert endpoint window
      readback endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNameCarrier schedule observation radius ledger sealRow provenance namecert
        endpoint bundle pkg ->
      Cont schedule observation window ->
        Cont window radius readback ->
          Cont sealRow provenance endpoint' ->
            PkgSig bundle readback pkg ->
              PkgSig bundle endpoint' pkg ->
                hsame radius window ∧ UnaryHistory window ∧ UnaryHistory readback ∧
                  hsame endpoint endpoint' ∧ PkgSig bundle endpoint pkg ∧
                    PkgSig bundle readback pkg ∧ PkgSig bundle endpoint' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier scheduleObservationWindow windowRadiusReadback sealProvenanceEndpoint'
    readbackPkg endpointPkg'
  obtain ⟨scheduleUnary, observationUnary, radiusUnary, _ledgerUnary, _sealUnary,
    _provenanceUnary, _namecertUnary, scheduleObservationRadius, _radiusLedgerSeal,
    sealProvenanceEndpoint, endpointPkg⟩ := carrier
  have radiusSameWindow : hsame radius window :=
    cont_deterministic scheduleObservationRadius scheduleObservationWindow
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary observationUnary scheduleObservationWindow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed windowUnary radiusUnary windowRadiusReadback
  have endpointSame : hsame endpoint endpoint' :=
    cont_deterministic sealProvenanceEndpoint sealProvenanceEndpoint'
  exact
    ⟨radiusSameWindow, windowUnary, readbackUnary, endpointSame, endpointPkg,
      readbackPkg, endpointPkg'⟩

theorem RegularCauchyNameCarrier_completion_handoff_non_escape [AskSetup] [PackageSetup]
    {schedule observation radius ledger sealRow provenance namecert endpoint hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNameCarrier schedule observation radius ledger sealRow provenance namecert
        endpoint bundle pkg ->
      (Cont endpoint (BHist.e0 hostTail) schedule -> False) ∧
        (Cont endpoint (BHist.e1 hostTail) schedule -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier
  obtain ⟨_scheduleUnary, _observationUnary, _radiusUnary, _ledgerUnary,
    _sealUnary, _provenanceUnary, _namecertUnary, scheduleObservationRadius,
    radiusLedgerSeal, sealProvenanceEndpoint, _endpointPkg⟩ := carrier
  have scheduleToSeal : Cont schedule (append observation ledger) sealRow := by
    cases scheduleObservationRadius
    cases radiusLedgerSeal
    exact append_assoc schedule observation ledger
  have scheduleToEndpoint : Cont schedule (append (append observation ledger) provenance)
      endpoint := by
    cases scheduleToSeal
    cases sealProvenanceEndpoint
    exact append_assoc schedule (append observation ledger) provenance
  constructor
  · intro hostReturn
    exact cont_mutual_extension_right_tail_absurd.left scheduleToEndpoint hostReturn
  · intro hostReturn
    exact cont_mutual_extension_right_tail_absurd.right scheduleToEndpoint hostReturn

theorem RegularCauchyNameCarrier_constant_seal_embedding [AskSetup] [PackageSetup]
    {schedule observation radius ledger sealRow provenance namecert endpoint stationary
      constantRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNameCarrier schedule observation radius ledger sealRow provenance namecert
        endpoint bundle pkg ->
      Cont schedule BHist.Empty stationary ->
        Cont stationary observation constantRead ->
          PkgSig bundle constantRead pkg ->
            UnaryHistory stationary ∧ UnaryHistory constantRead ∧
              hsame stationary (append schedule BHist.Empty) ∧
                hsame constantRead (append stationary observation) ∧
                  PkgSig bundle endpoint pkg ∧ PkgSig bundle constantRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier stationaryRow constantReadRow constantReadPkg
  obtain ⟨scheduleUnary, observationUnary, _radiusUnary, _ledgerUnary, _sealUnary,
    _provenanceUnary, _namecertUnary, _scheduleObservationRadius, _radiusLedgerSeal,
    _sealProvenanceEndpoint, endpointPkg⟩ := carrier
  have stationaryUnary : UnaryHistory stationary :=
    unary_cont_closed scheduleUnary unary_empty stationaryRow
  have constantReadUnary : UnaryHistory constantRead :=
    unary_cont_closed stationaryUnary observationUnary constantReadRow
  exact
    ⟨stationaryUnary, constantReadUnary, stationaryRow, constantReadRow, endpointPkg,
      constantReadPkg⟩

theorem RegularCauchyNameCarrier_common_window_refinement [AskSetup] [PackageSetup]
    {schedule observation radius ledger sealRow provenance namecert endpoint window readback
      readback' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNameCarrier schedule observation radius ledger sealRow provenance namecert
        endpoint bundle pkg ->
      Cont schedule observation window ->
        Cont window radius readback ->
          Cont window radius readback' ->
            Cont sealRow provenance endpoint' ->
              PkgSig bundle readback pkg ->
                PkgSig bundle readback' pkg ->
                  PkgSig bundle endpoint' pkg ->
                    hsame readback readback' ∧ hsame endpoint endpoint' ∧
                      UnaryHistory window ∧ UnaryHistory readback ∧
                        UnaryHistory readback' ∧ PkgSig bundle endpoint pkg ∧
                          PkgSig bundle readback pkg ∧ PkgSig bundle readback' pkg ∧
                            PkgSig bundle endpoint' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier scheduleObservationWindow windowRadiusReadback windowRadiusReadback'
    sealProvenanceEndpoint' readbackPkg readbackPkg' endpointPkg'
  obtain ⟨scheduleUnary, observationUnary, radiusUnary, _ledgerUnary, _sealUnary,
    _provenanceUnary, _namecertUnary, _scheduleObservationRadius, _radiusLedgerSeal,
    sealProvenanceEndpoint, endpointPkg⟩ := carrier
  have sameReadback : hsame readback readback' :=
    cont_deterministic windowRadiusReadback windowRadiusReadback'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_deterministic sealProvenanceEndpoint sealProvenanceEndpoint'
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary observationUnary scheduleObservationWindow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed windowUnary radiusUnary windowRadiusReadback
  have readbackUnary' : UnaryHistory readback' :=
    unary_cont_closed windowUnary radiusUnary windowRadiusReadback'
  exact
    ⟨sameReadback, sameEndpoint, windowUnary, readbackUnary, readbackUnary',
      endpointPkg, readbackPkg, readbackPkg', endpointPkg'⟩

theorem RegularCauchyNameCarrier_synchronized_precision_pullback [AskSetup] [PackageSetup]
    {schedule observation radius ledger sealRow provenance namecert endpoint window window'
      readback readback' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNameCarrier schedule observation radius ledger sealRow provenance namecert
        endpoint bundle pkg ->
      Cont schedule observation window ->
        Cont schedule observation window' ->
          Cont window radius readback ->
            Cont window' radius readback' ->
              PkgSig bundle readback pkg ->
                PkgSig bundle readback' pkg ->
                  hsame window window' ∧ hsame readback readback' ∧
                    UnaryHistory window ∧ UnaryHistory window' ∧ UnaryHistory readback ∧
                      UnaryHistory readback' ∧ PkgSig bundle endpoint pkg ∧
                        PkgSig bundle readback pkg ∧ PkgSig bundle readback' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier scheduleObservationWindow scheduleObservationWindow'
    windowRadiusReadback windowRadiusReadback' readbackPkg readbackPkg'
  obtain ⟨scheduleUnary, observationUnary, radiusUnary, _ledgerUnary, _sealUnary,
    _provenanceUnary, _namecertUnary, _scheduleObservationRadius, _radiusLedgerSeal,
    _sealProvenanceEndpoint, endpointPkg⟩ := carrier
  have sameWindow : hsame window window' :=
    cont_deterministic scheduleObservationWindow scheduleObservationWindow'
  have sameReadback : hsame readback readback' :=
    cont_respects_hsame sameWindow (hsame_refl radius) windowRadiusReadback
      windowRadiusReadback'
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary observationUnary scheduleObservationWindow
  have windowUnary' : UnaryHistory window' :=
    unary_cont_closed scheduleUnary observationUnary scheduleObservationWindow'
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed windowUnary radiusUnary windowRadiusReadback
  have readbackUnary' : UnaryHistory readback' :=
    unary_cont_closed windowUnary' radiusUnary windowRadiusReadback'
  exact
    ⟨sameWindow, sameReadback, windowUnary, windowUnary', readbackUnary,
      readbackUnary', endpointPkg, readbackPkg, readbackPkg'⟩

theorem RegularCauchyNameCarrier_real_seal_factorization [AskSetup] [PackageSetup]
    {schedule observation radius ledger sealRow provenance namecert endpoint sealRow'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNameCarrier schedule observation radius ledger sealRow provenance namecert
        endpoint bundle pkg ->
      Cont radius ledger sealRow' ->
        Cont sealRow' provenance endpoint' ->
          PkgSig bundle endpoint' pkg ->
            RegularCauchyNameCarrier schedule observation radius ledger sealRow'
                provenance namecert endpoint' bundle pkg ∧
              hsame sealRow sealRow' ∧ hsame endpoint endpoint' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier radiusLedgerSeal' sealProvenanceEndpoint' endpointPkg'
  obtain ⟨scheduleUnary, observationUnary, radiusUnary, ledgerUnary, _sealUnary,
    provenanceUnary, namecertUnary, scheduleObservationRadius, radiusLedgerSeal,
    sealProvenanceEndpoint, _endpointPkg⟩ := carrier
  have sameSeal : hsame sealRow sealRow' :=
    cont_deterministic radiusLedgerSeal radiusLedgerSeal'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameSeal (hsame_refl provenance) sealProvenanceEndpoint
      sealProvenanceEndpoint'
  have sealUnary' : UnaryHistory sealRow' :=
    unary_cont_closed radiusUnary ledgerUnary radiusLedgerSeal'
  exact
    ⟨⟨scheduleUnary, observationUnary, radiusUnary, ledgerUnary, sealUnary',
      provenanceUnary, namecertUnary, scheduleObservationRadius, radiusLedgerSeal',
      sealProvenanceEndpoint', endpointPkg'⟩, sameSeal, sameEndpoint⟩

theorem RegularCauchyNameCarrier_finite_window_readback_exactness [AskSetup]
    [PackageSetup]
    {schedule observation radius ledger sealRow provenance namecert endpoint window
      readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNameCarrier schedule observation radius ledger sealRow provenance namecert
        endpoint bundle pkg ->
      Cont schedule observation window ->
        Cont window radius readback ->
          PkgSig bundle readback pkg ->
            UnaryHistory schedule ∧ UnaryHistory window ∧ UnaryHistory radius ∧
              UnaryHistory readback ∧ hsame radius window ∧
                Cont schedule observation window ∧ Cont window radius readback ∧
                  PkgSig bundle endpoint pkg ∧ PkgSig bundle readback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier scheduleObservationWindow windowRadiusReadback readbackPkg
  obtain ⟨scheduleUnary, observationUnary, radiusUnary, _ledgerUnary, _sealUnary,
    _provenanceUnary, _namecertUnary, scheduleObservationRadius, _radiusLedgerSeal,
    _sealProvenanceEndpoint, endpointPkg⟩ := carrier
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary observationUnary scheduleObservationWindow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed windowUnary radiusUnary windowRadiusReadback
  have radiusSameWindow : hsame radius window :=
    cont_deterministic scheduleObservationRadius scheduleObservationWindow
  exact
    ⟨scheduleUnary, windowUnary, radiusUnary, readbackUnary, radiusSameWindow,
      scheduleObservationWindow, windowRadiusReadback, endpointPkg, readbackPkg⟩

end BEDC.Derived.RegularCauchyNameUp
