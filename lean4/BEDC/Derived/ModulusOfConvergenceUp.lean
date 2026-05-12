import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ModulusOfConvergenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ModulusOfConvergenceSemanticPacket [AskSetup] [PackageSetup]
    (precision selector modulus schedule witness ledger provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  Cont precision selector modulus ∧
    Cont modulus schedule witness ∧
      Cont witness ledger provenance ∧
        Cont provenance BHist.Empty endpoint ∧
          PkgSig bundle endpoint pkg

theorem ModulusOfConvergencePacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {precision selector modulus schedule witness ledger provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModulusOfConvergenceSemanticPacket precision selector modulus schedule witness ledger provenance
      endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          hsame row endpoint ∧
            ModulusOfConvergenceSemanticPacket precision selector modulus schedule witness ledger
              provenance endpoint bundle pkg)
        (fun row : BHist => hsame row endpoint)
        (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint (And.intro (hsame_refl endpoint) packet)
      equiv_refl := by
        intro h _source
        exact hsame_refl h
      equiv_symm := by
        intro _h _k same
        exact hsame_symm same
      equiv_trans := by
        intro _h _k _r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k same source
        exact And.intro (hsame_trans (hsame_symm same) source.left) source.right
    }
    pattern_sound := by
      intro _h source
      exact source.left
    ledger_sound := by
      intro _h source
      exact And.intro source.left source.right.right.right.right.right
  }

def ModulusOfConvergenceBHistCarrier [AskSetup] [PackageSetup]
    (precision selector modulus schedule witness ledger provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory selector ∧ UnaryHistory modulus ∧
    UnaryHistory schedule ∧ UnaryHistory witness ∧ UnaryHistory ledger ∧
      UnaryHistory provenance ∧ Cont precision selector ledger ∧
        Cont ledger provenance endpoint ∧ PkgSig bundle endpoint pkg

theorem ModulusOfConvergenceBHistCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {precision selector modulus schedule witness ledger provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModulusOfConvergenceBHistCarrier precision selector modulus schedule witness ledger provenance
        endpoint bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint) hsame ∧
        UnaryHistory precision ∧ UnaryHistory selector ∧ UnaryHistory modulus ∧
          UnaryHistory schedule ∧ UnaryHistory witness ∧ Cont precision selector ledger ∧
            Cont ledger provenance endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  obtain ⟨precisionUnary, selectorUnary, modulusUnary, scheduleUnary, witnessUnary,
    _ledgerUnary, _provenanceUnary, precisionSelectorRoute, endpointRoute, pkgRoute⟩ := carrier
  have cert :
      SemanticNameCert (fun row : BHist => hsame row endpoint)
        (fun row : BHist => hsame row endpoint)
        (fun row : BHist => hsame row endpoint) hsame :=
    {
      core := {
        carrier_inhabited := Exists.intro endpoint (hsame_refl endpoint)
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _row' _row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row row' sameRows source
          exact hsame_trans (hsame_symm sameRows) source
      }
      pattern_sound := by
        intro _row source
        exact source
      ledger_sound := by
        intro _row source
        exact source
    }
  exact
    ⟨cert, precisionUnary, selectorUnary, modulusUnary, scheduleUnary, witnessUnary,
      precisionSelectorRoute, endpointRoute, pkgRoute⟩

def ModulusOfConvergenceTransportPacket [AskSetup] [PackageSetup]
    (precision threshold modulus schedule witness ledger provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory threshold ∧ UnaryHistory modulus ∧
    UnaryHistory schedule ∧ UnaryHistory witness ∧ Cont precision threshold modulus ∧
      Cont modulus schedule witness ∧ Cont witness ledger provenance ∧ PkgSig bundle provenance pkg

theorem ModulusOfConvergencePacket_composition_stability [AskSetup] [PackageSetup]
    {precision threshold modulus schedule witness ledger provenance precision' threshold' modulus'
      schedule' witness' ledger' provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModulusOfConvergenceTransportPacket precision threshold modulus schedule witness ledger provenance
        bundle pkg ->
      hsame precision precision' ->
        hsame threshold threshold' ->
          hsame schedule schedule' ->
            hsame ledger ledger' ->
              Cont precision' threshold' modulus' ->
                Cont modulus' schedule' witness' ->
                  Cont witness' ledger' provenance' ->
                    PkgSig bundle provenance' pkg ->
                      ModulusOfConvergenceTransportPacket precision' threshold' modulus' schedule'
                          witness' ledger' provenance' bundle pkg ∧
                        hsame modulus modulus' ∧ hsame witness witness' ∧
                          hsame provenance provenance' := by
  intro packet samePrecision sameThreshold sameSchedule sameLedger modulusRow' witnessRow'
    provenanceRow' pkgSig'
  have precisionUnary : UnaryHistory precision :=
    packet.left
  have thresholdUnary : UnaryHistory threshold :=
    packet.right.left
  have scheduleUnary : UnaryHistory schedule :=
    packet.right.right.right.left
  have modulusRow : Cont precision threshold modulus :=
    packet.right.right.right.right.right.left
  have witnessRow : Cont modulus schedule witness :=
    packet.right.right.right.right.right.right.left
  have provenanceRow : Cont witness ledger provenance :=
    packet.right.right.right.right.right.right.right.left
  have precisionUnary' : UnaryHistory precision' :=
    unary_transport precisionUnary samePrecision
  have thresholdUnary' : UnaryHistory threshold' :=
    unary_transport thresholdUnary sameThreshold
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport scheduleUnary sameSchedule
  have modulusUnary' : UnaryHistory modulus' :=
    unary_cont_closed precisionUnary' thresholdUnary' modulusRow'
  have witnessUnary' : UnaryHistory witness' :=
    unary_cont_closed modulusUnary' scheduleUnary' witnessRow'
  have sameModulus : hsame modulus modulus' :=
    cont_respects_hsame samePrecision sameThreshold modulusRow modulusRow'
  have sameWitness : hsame witness witness' :=
    cont_respects_hsame sameModulus sameSchedule witnessRow witnessRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameWitness sameLedger provenanceRow provenanceRow'
  exact And.intro
    (And.intro precisionUnary'
      (And.intro thresholdUnary'
        (And.intro modulusUnary'
          (And.intro scheduleUnary'
            (And.intro witnessUnary'
              (And.intro modulusRow'
                (And.intro witnessRow'
                  (And.intro provenanceRow' pkgSig'))))))))
    (And.intro sameModulus (And.intro sameWitness sameProvenance))

def ModulusOfConvergenceNameCertPacket [AskSetup] [PackageSetup]
    (precision threshold requestWindow modulus schedule witnessWindow witness exportWindow ledger
      provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory threshold ∧ UnaryHistory modulus ∧
    UnaryHistory schedule ∧ UnaryHistory witness ∧ UnaryHistory ledger ∧
      Cont precision threshold requestWindow ∧ Cont modulus schedule witnessWindow ∧
        Cont requestWindow witness exportWindow ∧ Cont exportWindow ledger provenance ∧
          PkgSig bundle provenance pkg

theorem ModulusOfConvergencePacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {precision threshold requestWindow modulus schedule witnessWindow witness exportWindow ledger
      provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModulusOfConvergenceNameCertPacket precision threshold requestWindow modulus schedule witnessWindow
        witness exportWindow ledger provenance bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row provenance)
          (fun row : BHist => hsame row provenance)
          (fun row : BHist => hsame row provenance) hsame ∧
        Cont precision threshold requestWindow ∧ Cont modulus schedule witnessWindow ∧
          Cont requestWindow witness exportWindow ∧ Cont exportWindow ledger provenance ∧
            PkgSig bundle provenance pkg := by
  intro packet
  have requestRow : Cont precision threshold requestWindow :=
    packet.right.right.right.right.right.right.left
  have witnessRow : Cont modulus schedule witnessWindow :=
    packet.right.right.right.right.right.right.right.left
  have exportRow : Cont requestWindow witness exportWindow :=
    packet.right.right.right.right.right.right.right.right.left
  have provenanceRow : Cont exportWindow ledger provenance :=
    packet.right.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle provenance pkg :=
    packet.right.right.right.right.right.right.right.right.right.right
  have cert :
      SemanticNameCert (fun row : BHist => hsame row provenance)
          (fun row : BHist => hsame row provenance)
          (fun row : BHist => hsame row provenance) hsame := {
    core := {
      carrier_inhabited := Exists.intro provenance (hsame_refl provenance)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro requestRow
      (And.intro witnessRow
        (And.intro exportRow
          (And.intro provenanceRow pkgSig))))

def ModulusOfConvergenceCarrier [AskSetup] [PackageSetup]
    (precision selector modulus schedule witness ledger provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory selector ∧ UnaryHistory modulus ∧
    UnaryHistory schedule ∧ UnaryHistory witness ∧ UnaryHistory ledger ∧
      UnaryHistory provenance ∧ Cont precision selector modulus ∧
        Cont modulus schedule witness ∧ Cont witness ledger provenance ∧
          PkgSig bundle provenance pkg

theorem ModulusOfConvergenceStandardBridge_boundary [AskSetup] [PackageSetup]
    {precision selector modulus schedule witness ledger provenance bridge : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModulusOfConvergenceCarrier precision selector modulus schedule witness ledger provenance
        bundle pkg ->
      Cont provenance ledger bridge ->
        PkgSig bundle bridge pkg ->
          hsame modulus (append precision selector) ∧
            hsame witness (append modulus schedule) ∧
              hsame provenance (append witness ledger) ∧
                hsame bridge (append provenance ledger) ∧
                  UnaryHistory bridge ∧ PkgSig bundle bridge pkg := by
  intro carrier bridgeRoute bridgePkg
  have provenanceUnary : UnaryHistory provenance :=
    carrier.right.right.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    carrier.right.right.right.right.right.left
  have modulusRoute : Cont precision selector modulus :=
    carrier.right.right.right.right.right.right.right.left
  have witnessRoute : Cont modulus schedule witness :=
    carrier.right.right.right.right.right.right.right.right.left
  have provenanceRoute : Cont witness ledger provenance :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have bridgeUnary : UnaryHistory bridge :=
    unary_cont_closed provenanceUnary ledgerUnary bridgeRoute
  exact
    And.intro modulusRoute
      (And.intro witnessRoute
        (And.intro provenanceRoute
          (And.intro bridgeRoute
            (And.intro bridgeUnary bridgePkg))))

theorem ModulusOfConvergencePacket_tail_restriction_stability [AskSetup] [PackageSetup]
    {precision selector modulus schedule witness ledger provenance schedule' witness'
      provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModulusOfConvergenceCarrier precision selector modulus schedule witness ledger provenance
        bundle pkg ->
      hsame schedule schedule' ->
        hsame witness witness' ->
          hsame provenance provenance' ->
            Cont modulus schedule' witness' ->
              Cont witness' ledger provenance' ->
                PkgSig bundle provenance' pkg ->
                  ModulusOfConvergenceCarrier precision selector modulus schedule' witness'
                      ledger provenance' bundle pkg ∧
                    hsame witness witness' ∧ hsame provenance provenance' := by
  intro packet sameSchedule sameWitness sameProvenance restrictedWitness restrictedProvenance
    restrictedPkg
  have precisionUnary : UnaryHistory precision :=
    packet.left
  have selectorUnary : UnaryHistory selector :=
    packet.right.left
  have modulusUnary : UnaryHistory modulus :=
    packet.right.right.left
  have scheduleUnary : UnaryHistory schedule' :=
    unary_transport packet.right.right.right.left sameSchedule
  have witnessUnary : UnaryHistory witness' :=
    unary_transport packet.right.right.right.right.left sameWitness
  have ledgerUnary : UnaryHistory ledger :=
    packet.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance' :=
    unary_transport packet.right.right.right.right.right.right.left sameProvenance
  have modulusRoute : Cont precision selector modulus :=
    packet.right.right.right.right.right.right.right.left
  constructor
  · exact
      And.intro precisionUnary
        (And.intro selectorUnary
          (And.intro modulusUnary
            (And.intro scheduleUnary
              (And.intro witnessUnary
                (And.intro ledgerUnary
                  (And.intro provenanceUnary
                    (And.intro modulusRoute
                      (And.intro restrictedWitness
                        (And.intro restrictedProvenance restrictedPkg)))))))))
  · exact And.intro sameWitness sameProvenance

theorem ModulusOfConvergenceCarrier_tail_restriction_stability [AskSetup] [PackageSetup]
    {precision selector modulus schedule witness ledger provenance schedule' witness'
      provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModulusOfConvergenceCarrier precision selector modulus schedule witness ledger provenance
        bundle pkg ->
      hsame schedule schedule' ->
        hsame witness witness' ->
          hsame provenance provenance' ->
            Cont modulus schedule' witness' ->
              Cont witness' ledger provenance' ->
                PkgSig bundle provenance' pkg ->
                  ModulusOfConvergenceCarrier precision selector modulus schedule' witness'
                      ledger provenance' bundle pkg ∧
                    hsame witness witness' ∧ hsame provenance provenance' :=
  ModulusOfConvergencePacket_tail_restriction_stability

theorem ModulusOfConvergenceCarrier_threshold_ledger_completeness [AskSetup] [PackageSetup]
    {precision selector modulus schedule witness ledger provenance consumerTail exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModulusOfConvergenceCarrier precision selector modulus schedule witness ledger provenance
        bundle pkg ->
      UnaryHistory consumerTail ->
        Cont provenance consumerTail exported ->
          Cont precision selector modulus ∧ Cont modulus schedule witness ∧
            Cont witness ledger provenance ∧ Cont provenance consumerTail exported ∧
              UnaryHistory modulus ∧ UnaryHistory witness ∧ UnaryHistory provenance ∧
                UnaryHistory exported ∧ hsame exported (append provenance consumerTail) ∧
                  PkgSig bundle provenance pkg := by
  intro carrier consumerTailUnary exportedRow
  have precisionUnary : UnaryHistory precision :=
    carrier.left
  have selectorUnary : UnaryHistory selector :=
    carrier.right.left
  have scheduleUnary : UnaryHistory schedule :=
    carrier.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    carrier.right.right.right.right.right.left
  have modulusUnary : UnaryHistory modulus :=
    carrier.right.right.left
  have witnessUnary : UnaryHistory witness :=
    carrier.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    carrier.right.right.right.right.right.right.left
  have modulusRow : Cont precision selector modulus :=
    carrier.right.right.right.right.right.right.right.left
  have witnessRow : Cont modulus schedule witness :=
    carrier.right.right.right.right.right.right.right.right.left
  have provenanceRow : Cont witness ledger provenance :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle provenance pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed provenanceUnary consumerTailUnary exportedRow
  exact
    ⟨modulusRow, witnessRow, provenanceRow, exportedRow, modulusUnary, witnessUnary,
      provenanceUnary, exportedUnary, exportedRow, pkgSig⟩

theorem ModulusOfConvergenceCarrier_composition_stability [AskSetup] [PackageSetup]
    {precision selector modulus schedule witness ledger provenance precision' selector' modulus'
      schedule' witness' ledger' provenance' : BHist}
    {bundle bundle' : ProbeBundle ProbeName} {pkg pkg' : Pkg} :
    ModulusOfConvergenceCarrier precision selector modulus schedule witness ledger provenance
        bundle pkg ->
      ModulusOfConvergenceCarrier precision' selector' modulus' schedule' witness' ledger'
        provenance' bundle' pkg' ->
        exists joined : BHist, Cont provenance precision' joined ∧ UnaryHistory joined := by
  intro leftCarrier rightCarrier
  cases leftCarrier with
  | intro _precisionUnary leftRest =>
      cases leftRest with
      | intro _selectorUnary leftRest =>
          cases leftRest with
          | intro _modulusUnary leftRest =>
              cases leftRest with
              | intro _scheduleUnary leftRest =>
                  cases leftRest with
                  | intro _witnessUnary leftRest =>
                      cases leftRest with
                      | intro _ledgerUnary leftRest =>
                          cases leftRest with
                          | intro provenanceUnary _leftRows =>
                              cases rightCarrier with
                              | intro precisionUnary' _rightRest =>
                                  let joined := append provenance precision'
                                  have joinedRow : Cont provenance precision' joined := by
                                    rfl
                                  have joinedUnary : UnaryHistory joined :=
                                    unary_repetition_closed_under_continuation provenanceUnary
                                      precisionUnary' joinedRow
                                  exact ⟨joined, joinedRow, joinedUnary⟩

theorem ModulusOfConvergenceCarrier_scoped_dependency_packet [AskSetup] [PackageSetup]
    {precision selector modulus schedule witness ledger provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModulusOfConvergenceCarrier precision selector modulus schedule witness ledger provenance
        bundle pkg ->
      UnaryHistory precision ∧ UnaryHistory selector ∧ UnaryHistory modulus ∧
        UnaryHistory schedule ∧ UnaryHistory witness ∧ UnaryHistory ledger ∧
          UnaryHistory provenance ∧ Cont precision selector modulus ∧
            Cont modulus schedule witness ∧ Cont witness ledger provenance ∧
              SemanticNameCert (fun row : BHist => hsame row provenance)
                (fun row : BHist => hsame row provenance)
                (fun row : BHist => hsame row provenance) hsame := by
  intro carrier
  obtain ⟨precisionUnary, selectorUnary, modulusUnary, scheduleUnary, witnessUnary,
    ledgerUnary, provenanceUnary, precisionSelectorRoute, witnessRoute, provenanceRoute,
    _pkgRoute⟩ := carrier
  have cert :
      SemanticNameCert (fun row : BHist => hsame row provenance)
        (fun row : BHist => hsame row provenance)
        (fun row : BHist => hsame row provenance) hsame := {
    core := {
      carrier_inhabited := Exists.intro provenance (hsame_refl provenance)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact
    ⟨precisionUnary, selectorUnary, modulusUnary, scheduleUnary, witnessUnary, ledgerUnary,
      provenanceUnary, precisionSelectorRoute, witnessRoute, provenanceRoute, cert⟩

inductive ModulusOfConvergencePacket
    (precision selector modulus stream witness ledger provenance window : BHist) : Prop where
  | mk :
      hsame precision window ->
        hsame selector window ->
          Cont stream witness window ->
            Cont ledger provenance window ->
              NameCert (fun h : BHist => hsame h ledger) hsame ->
                ModulusOfConvergencePacket precision selector modulus stream witness ledger
                  provenance window

theorem ModulusOfConvergencePacket_ledger_exactness
    {precision selector modulus stream witness ledger provenance window : BHist} :
    ModulusOfConvergencePacket precision selector modulus stream witness ledger provenance
        window ->
      hsame precision window ∧ hsame selector window ∧
        Cont stream witness window ∧ Cont ledger provenance window := by
  intro packet
  cases packet with
  | mk precisionWindow selectorWindow streamRoute ledgerRoute _ledgerCert =>
      exact And.intro precisionWindow
        (And.intro selectorWindow (And.intro streamRoute ledgerRoute))

theorem ModulusOfConvergencePacket_standard_bridge
    {precision selector modulus stream witness ledger provenance window : BHist} :
    ModulusOfConvergencePacket precision selector modulus stream witness ledger provenance
        window ->
      hsame precision window ∧ hsame selector window ∧ Cont stream witness window ∧
        Cont ledger provenance window ∧ NameCert (fun h : BHist => hsame h ledger) hsame := by
  intro packet
  cases packet with
  | mk precisionWindow selectorWindow streamRoute ledgerRoute ledgerCert =>
      exact And.intro precisionWindow
        (And.intro selectorWindow
          (And.intro streamRoute (And.intro ledgerRoute ledgerCert)))

def ModulusOfConvergenceRatePacket [AskSetup] [PackageSetup]
    (precision selector modulus schedule witness ledger provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory selector ∧ UnaryHistory schedule ∧
    UnaryHistory witness ∧ UnaryHistory provenance ∧ Cont precision selector modulus ∧
      Cont schedule witness ledger ∧ Cont modulus ledger endpoint ∧
        PkgSig bundle endpoint pkg

theorem ModulusOfConvergenceRatePacket_threshold_ledger_completeness [AskSetup]
    [PackageSetup]
    {precision selector modulus schedule witness ledger provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModulusOfConvergenceRatePacket precision selector modulus schedule witness ledger provenance
        endpoint bundle pkg ->
      UnaryHistory modulus ∧ UnaryHistory ledger ∧ UnaryHistory endpoint ∧
        hsame modulus (append precision selector) ∧ hsame ledger (append schedule witness) ∧
          hsame endpoint (append modulus ledger) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have precisionUnary : UnaryHistory precision :=
    packet.left
  have selectorUnary : UnaryHistory selector :=
    packet.right.left
  have scheduleUnary : UnaryHistory schedule :=
    packet.right.right.left
  have witnessUnary : UnaryHistory witness :=
    packet.right.right.right.left
  have modulusRow : Cont precision selector modulus :=
    packet.right.right.right.right.right.left
  have ledgerRow : Cont schedule witness ledger :=
    packet.right.right.right.right.right.right.left
  have endpointRow : Cont modulus ledger endpoint :=
    packet.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right.right
  have modulusUnary : UnaryHistory modulus :=
    unary_cont_closed precisionUnary selectorUnary modulusRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed scheduleUnary witnessUnary ledgerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed modulusUnary ledgerUnary endpointRow
  exact
    ⟨modulusUnary, ledgerUnary, endpointUnary, modulusRow, ledgerRow, endpointRow, pkgSig⟩

theorem ModulusOfConvergenceRatePacket_tail_restriction_stability [AskSetup] [PackageSetup]
    {precision selector modulus schedule witness ledger provenance endpoint tail restrictedSchedule
      restrictedLedger restrictedEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModulusOfConvergenceRatePacket precision selector modulus schedule witness ledger provenance
        endpoint bundle pkg ->
      UnaryHistory tail ->
        Cont schedule tail restrictedSchedule ->
          Cont restrictedSchedule witness restrictedLedger ->
            Cont modulus restrictedLedger restrictedEndpoint ->
              PkgSig bundle restrictedEndpoint pkg ->
                ModulusOfConvergenceRatePacket precision selector modulus restrictedSchedule witness
                    restrictedLedger provenance restrictedEndpoint bundle pkg ∧
                  hsame restrictedSchedule (append schedule tail) ∧
                    hsame restrictedLedger (append restrictedSchedule witness) := by
  intro packet tailUnary restrictedScheduleRow restrictedLedgerRow restrictedEndpointRow pkgSig
  have precisionUnary : UnaryHistory precision :=
    packet.left
  have selectorUnary : UnaryHistory selector :=
    packet.right.left
  have scheduleUnary : UnaryHistory schedule :=
    packet.right.right.left
  have witnessUnary : UnaryHistory witness :=
    packet.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    packet.right.right.right.right.left
  have modulusRow : Cont precision selector modulus :=
    packet.right.right.right.right.right.left
  have modulusUnary : UnaryHistory modulus :=
    unary_cont_closed precisionUnary selectorUnary modulusRow
  have restrictedScheduleUnary : UnaryHistory restrictedSchedule :=
    unary_cont_closed scheduleUnary tailUnary restrictedScheduleRow
  have restrictedLedgerUnary : UnaryHistory restrictedLedger :=
    unary_cont_closed restrictedScheduleUnary witnessUnary restrictedLedgerRow
  have _restrictedEndpointUnary : UnaryHistory restrictedEndpoint :=
    unary_cont_closed modulusUnary restrictedLedgerUnary restrictedEndpointRow
  have restrictedPacket :
      ModulusOfConvergenceRatePacket precision selector modulus restrictedSchedule witness
        restrictedLedger provenance restrictedEndpoint bundle pkg :=
    And.intro precisionUnary
      (And.intro selectorUnary
        (And.intro restrictedScheduleUnary
          (And.intro witnessUnary
            (And.intro provenanceUnary
              (And.intro modulusRow
                (And.intro restrictedLedgerRow
                  (And.intro restrictedEndpointRow pkgSig)))))))
  exact And.intro restrictedPacket
    (And.intro restrictedScheduleRow restrictedLedgerRow)

theorem ModulusOfConvergenceRatePacket_tail_consumer_boundary [AskSetup] [PackageSetup]
    {precision selector modulus schedule witness ledger provenance endpoint tail restrictedSchedule
      restrictedLedger restrictedEndpoint exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModulusOfConvergenceRatePacket precision selector modulus schedule witness ledger provenance
        endpoint bundle pkg ->
      UnaryHistory tail ->
        Cont schedule tail restrictedSchedule ->
          Cont restrictedSchedule witness restrictedLedger ->
            Cont modulus restrictedLedger restrictedEndpoint ->
              PkgSig bundle restrictedEndpoint pkg ->
                Cont restrictedEndpoint ledger exported ->
                  PkgSig bundle exported pkg ->
                    ModulusOfConvergenceRatePacket precision selector modulus restrictedSchedule
                        witness restrictedLedger provenance restrictedEndpoint bundle pkg ∧
                      UnaryHistory exported ∧ hsame restrictedSchedule (append schedule tail) ∧
                        hsame restrictedLedger (append restrictedSchedule witness) ∧
                          hsame restrictedEndpoint (append modulus restrictedLedger) ∧
                            hsame exported (append restrictedEndpoint ledger) := by
  intro packet tailUnary restrictedScheduleRow restrictedLedgerRow restrictedEndpointRow
    restrictedPkg exportRow exportedPkg
  obtain ⟨restrictedPacket, restrictedScheduleSame, restrictedLedgerSame⟩ :=
    ModulusOfConvergenceRatePacket_tail_restriction_stability packet tailUnary
      restrictedScheduleRow restrictedLedgerRow restrictedEndpointRow restrictedPkg
  have scheduleUnary : UnaryHistory schedule :=
    packet.right.right.left
  have witnessUnary : UnaryHistory witness :=
    packet.right.right.right.left
  have precisionUnary : UnaryHistory precision :=
    packet.left
  have selectorUnary : UnaryHistory selector :=
    packet.right.left
  have modulusRow : Cont precision selector modulus :=
    packet.right.right.right.right.right.left
  have ledgerRow : Cont schedule witness ledger :=
    packet.right.right.right.right.right.right.left
  have modulusUnary : UnaryHistory modulus :=
    unary_cont_closed precisionUnary selectorUnary modulusRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed scheduleUnary witnessUnary ledgerRow
  have restrictedLedgerUnary : UnaryHistory restrictedLedger :=
    unary_cont_closed (restrictedPacket.right.right.left) witnessUnary restrictedLedgerRow
  have restrictedEndpointUnary : UnaryHistory restrictedEndpoint :=
    unary_cont_closed modulusUnary restrictedLedgerUnary restrictedEndpointRow
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed restrictedEndpointUnary ledgerUnary exportRow
  exact
    ⟨restrictedPacket, exportedUnary, restrictedScheduleSame, restrictedLedgerSame,
      restrictedEndpointRow, exportRow⟩

theorem ModulusOfConvergenceFiniteRateBridge_rows [AskSetup] [PackageSetup]
    {precision threshold modulus schedule witness ledger prov out : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory precision -> UnaryHistory threshold -> UnaryHistory schedule ->
      UnaryHistory witness -> UnaryHistory prov -> Cont precision threshold modulus ->
        Cont schedule witness ledger -> Cont modulus ledger out -> PkgSig bundle out pkg ->
          UnaryHistory modulus ∧ UnaryHistory ledger ∧ UnaryHistory out ∧
            hsame modulus (append precision threshold) ∧
              hsame ledger (append schedule witness) ∧ hsame out (append modulus ledger) ∧
                PkgSig bundle out pkg := by
  intro precisionUnary thresholdUnary scheduleUnary witnessUnary _provUnary modulusRow ledgerRow
    outRow pkgSig
  have modulusUnary : UnaryHistory modulus :=
    unary_cont_closed precisionUnary thresholdUnary modulusRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed scheduleUnary witnessUnary ledgerRow
  have outUnary : UnaryHistory out :=
    unary_cont_closed modulusUnary ledgerUnary outRow
  exact And.intro modulusUnary
    (And.intro ledgerUnary
      (And.intro outUnary
        (And.intro modulusRow
          (And.intro ledgerRow
            (And.intro outRow pkgSig)))))

theorem ModulusOfConvergenceRatePacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {precision selector modulus schedule witness ledger provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModulusOfConvergenceRatePacket precision selector modulus schedule witness ledger provenance
        endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist => hsame row endpoint ∧
          ModulusOfConvergenceRatePacket precision selector modulus schedule witness ledger
            provenance row bundle pkg)
        (fun row : BHist => UnaryHistory row ∧ hsame row (append modulus ledger))
        (fun row : BHist => PkgSig bundle row pkg ∧ Cont modulus ledger row)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint ⟨hsame_refl endpoint, packet⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      obtain ⟨precisionUnary, selectorUnary, scheduleUnary, witnessUnary, _provenanceUnary,
        modulusRow, ledgerRow, endpointRow, _pkgSig⟩ := sourceRow.right
      have modulusUnary : UnaryHistory modulus :=
        unary_cont_closed precisionUnary selectorUnary modulusRow
      have ledgerUnary : UnaryHistory ledger :=
        unary_cont_closed scheduleUnary witnessUnary ledgerRow
      have rowUnary : UnaryHistory _row :=
        unary_cont_closed modulusUnary ledgerUnary endpointRow
      exact ⟨rowUnary, endpointRow⟩
    ledger_sound := by
      intro _row sourceRow
      obtain ⟨_precisionUnary, _selectorUnary, _scheduleUnary, _witnessUnary,
        _provenanceUnary, _modulusRow, _ledgerRow, endpointRow, pkgSig⟩ := sourceRow.right
      exact ⟨pkgSig, endpointRow⟩
  }

end BEDC.Derived.ModulusOfConvergenceUp
