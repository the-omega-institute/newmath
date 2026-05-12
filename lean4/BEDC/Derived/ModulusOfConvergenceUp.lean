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

def ModulusOfConvergenceRatePacket [AskSetup] [PackageSetup]
    (precision selector modulus schedule witness ledger provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory selector ∧ UnaryHistory schedule ∧
    UnaryHistory witness ∧ UnaryHistory provenance ∧ Cont precision selector modulus ∧
      Cont schedule witness ledger ∧ Cont modulus ledger endpoint ∧
        PkgSig bundle endpoint pkg

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

end BEDC.Derived.ModulusOfConvergenceUp
