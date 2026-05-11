import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SignedDigitStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SignedDigitStreamFiniteWindowSource (row : BHist) : Prop :=
  exists schedule normalized carry hiddenTail boundary : BHist,
    Cont schedule normalized carry ∧
      Cont carry hiddenTail boundary ∧ hsame row (BHist.e1 boundary)

def SignedDigitStreamFiniteWindowPattern (row : BHist) : Prop :=
  exists schedule normalized carry boundary : BHist,
    Cont schedule normalized carry ∧ hsame row (BHist.e1 boundary)

def SignedDigitStreamWindowLedger (row : BHist) : Prop :=
  exists carry hiddenTail boundary : BHist,
    Cont carry hiddenTail boundary ∧ hsame row (BHist.e1 boundary)

theorem SignedDigitStreamPacket_namecert_obligation_surface :
    SemanticNameCert SignedDigitStreamFiniteWindowSource SignedDigitStreamFiniteWindowPattern
      SignedDigitStreamWindowLedger hsame := by
  have source : SignedDigitStreamFiniteWindowSource (BHist.e1 BHist.Empty) := by
    exact Exists.intro BHist.Empty
      (Exists.intro BHist.Empty
        (Exists.intro BHist.Empty
          (Exists.intro BHist.Empty
            (Exists.intro BHist.Empty
              (And.intro (cont_left_unit BHist.Empty)
                (And.intro (cont_left_unit BHist.Empty)
                  (hsame_refl (BHist.e1 BHist.Empty))))))))
  constructor
  · constructor
    · exact Exists.intro (BHist.e1 BHist.Empty) source
    · intro row _source
      exact hsame_refl row
    · intro left right sameRows
      exact hsame_symm sameRows
    · intro left middle right sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro left right sameRows sourceLeft
      cases sourceLeft with
      | intro schedule scheduleData =>
          cases scheduleData with
          | intro normalized normalizedData =>
              cases normalizedData with
              | intro carry carryData =>
                  cases carryData with
                  | intro hiddenTail hiddenTailData =>
                      cases hiddenTailData with
                      | intro boundary packet =>
                          exact Exists.intro schedule
                            (Exists.intro normalized
                              (Exists.intro carry
                                (Exists.intro hiddenTail
                                  (Exists.intro boundary
                                    (And.intro packet.left
                                      (And.intro packet.right.left
                                        (hsame_trans (hsame_symm sameRows)
                                          packet.right.right)))))))
  · intro row sourceRow
    cases sourceRow with
    | intro schedule scheduleData =>
        cases scheduleData with
        | intro normalized normalizedData =>
            cases normalizedData with
            | intro carry carryData =>
                cases carryData with
                | intro hiddenTail hiddenTailData =>
                    cases hiddenTailData with
                    | intro boundary packet =>
                        exact Exists.intro schedule
                          (Exists.intro normalized
                            (Exists.intro carry
                              (Exists.intro boundary
                                (And.intro packet.left packet.right.right))))
  · intro row sourceRow
    cases sourceRow with
    | intro schedule scheduleData =>
        cases scheduleData with
        | intro normalized normalizedData =>
            cases normalizedData with
            | intro carry carryData =>
                cases carryData with
                | intro hiddenTail hiddenTailData =>
                    cases hiddenTailData with
                    | intro boundary packet =>
                        exact Exists.intro carry
                          (Exists.intro hiddenTail
                            (Exists.intro boundary
                              (And.intro packet.right.left packet.right.right)))

def SignedDigitStreamPacket [AskSetup] [PackageSetup]
    (digits schedule carry provenance endpoint hidden ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory digits ∧ UnaryHistory schedule ∧ UnaryHistory provenance ∧
    UnaryHistory hidden ∧ UnaryHistory carry ∧ UnaryHistory endpoint ∧ UnaryHistory ledger ∧
      Cont digits schedule carry ∧ Cont carry provenance endpoint ∧
        Cont endpoint hidden ledger ∧ PkgSig bundle ledger pkg

theorem SignedDigitStreamPacket_window_transport [AskSetup] [PackageSetup]
    {digits schedule carry provenance endpoint hidden ledger digits' schedule' provenance' hidden'
      carry' endpoint' ledger' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SignedDigitStreamPacket digits schedule carry provenance endpoint hidden ledger bundle pkg ->
      hsame digits digits' ->
      hsame schedule schedule' ->
      hsame provenance provenance' ->
      hsame hidden hidden' ->
      Cont digits' schedule' carry' ->
      Cont carry' provenance' endpoint' ->
      Cont endpoint' hidden' ledger' ->
      PkgSig bundle ledger' pkg ->
        SignedDigitStreamPacket digits' schedule' carry' provenance' endpoint' hidden' ledger'
            bundle pkg ∧
          hsame carry carry' ∧ hsame endpoint endpoint' ∧ hsame ledger ledger' := by
  intro packet sameDigits sameSchedule sameProvenance sameHidden carryRow' endpointRow'
    ledgerRow' packageRow'
  have digitsUnary' : UnaryHistory digits' :=
    unary_transport packet.left sameDigits
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport packet.right.left sameSchedule
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport packet.right.right.left sameProvenance
  have hiddenUnary' : UnaryHistory hidden' :=
    unary_transport packet.right.right.right.left sameHidden
  have carryRow : Cont digits schedule carry :=
    packet.right.right.right.right.right.right.right.left
  have endpointRow : Cont carry provenance endpoint :=
    packet.right.right.right.right.right.right.right.right.left
  have ledgerRow : Cont endpoint hidden ledger :=
    packet.right.right.right.right.right.right.right.right.right.left
  have sameCarry : hsame carry carry' :=
    cont_respects_hsame sameDigits sameSchedule carryRow carryRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameCarry sameProvenance endpointRow endpointRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameEndpoint sameHidden ledgerRow ledgerRow'
  have carryUnary' : UnaryHistory carry' :=
    unary_cont_closed digitsUnary' scheduleUnary' carryRow'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed carryUnary' provenanceUnary' endpointRow'
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed endpointUnary' hiddenUnary' ledgerRow'
  have transported :
      SignedDigitStreamPacket digits' schedule' carry' provenance' endpoint' hidden' ledger'
        bundle pkg :=
    And.intro digitsUnary'
      (And.intro scheduleUnary'
        (And.intro provenanceUnary'
          (And.intro hiddenUnary'
            (And.intro carryUnary'
              (And.intro endpointUnary'
                (And.intro ledgerUnary'
                  (And.intro carryRow'
                    (And.intro endpointRow' (And.intro ledgerRow' packageRow')))))))))
  exact And.intro transported
    (And.intro sameCarry (And.intro sameEndpoint sameLedger))

def SignedDigitStreamClassifier [AskSetup] [PackageSetup]
    (digits schedule carry provenance endpoint hidden ledger digits' schedule' carry'
      provenance' endpoint' hidden' ledger' : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  SignedDigitStreamPacket digits schedule carry provenance endpoint hidden ledger bundle pkg ∧
    SignedDigitStreamPacket digits' schedule' carry' provenance' endpoint' hidden' ledger'
        bundle pkg ∧
      hsame digits digits' ∧ hsame schedule schedule' ∧ hsame provenance provenance' ∧
        hsame hidden hidden'

theorem SignedDigitStreamClassifier_common_window_determinacy [AskSetup] [PackageSetup]
    {digits schedule carry provenance endpoint hidden ledger digits' schedule' carry'
      provenance' endpoint' hidden' ledger' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SignedDigitStreamClassifier digits schedule carry provenance endpoint hidden ledger digits'
        schedule' carry' provenance' endpoint' hidden' ledger' bundle pkg ->
      hsame carry carry' ∧ hsame endpoint endpoint' ∧ hsame ledger ledger' := by
  intro classifier
  have leftPacket :
      SignedDigitStreamPacket digits schedule carry provenance endpoint hidden ledger bundle pkg :=
    classifier.left
  have rightPacket :
      SignedDigitStreamPacket digits' schedule' carry' provenance' endpoint' hidden' ledger'
        bundle pkg :=
    classifier.right.left
  have sameDigits : hsame digits digits' :=
    classifier.right.right.left
  have sameSchedule : hsame schedule schedule' :=
    classifier.right.right.right.left
  have sameProvenance : hsame provenance provenance' :=
    classifier.right.right.right.right.left
  have sameHidden : hsame hidden hidden' :=
    classifier.right.right.right.right.right
  have leftCarryRoute : Cont digits schedule carry :=
    leftPacket.right.right.right.right.right.right.right.left
  have rightCarryRoute : Cont digits' schedule' carry' :=
    rightPacket.right.right.right.right.right.right.right.left
  have leftEndpointRoute : Cont carry provenance endpoint :=
    leftPacket.right.right.right.right.right.right.right.right.left
  have rightEndpointRoute : Cont carry' provenance' endpoint' :=
    rightPacket.right.right.right.right.right.right.right.right.left
  have leftLedgerRoute : Cont endpoint hidden ledger :=
    leftPacket.right.right.right.right.right.right.right.right.right.left
  have rightLedgerRoute : Cont endpoint' hidden' ledger' :=
    rightPacket.right.right.right.right.right.right.right.right.right.left
  have sameCarry : hsame carry carry' :=
    cont_respects_hsame sameDigits sameSchedule leftCarryRoute rightCarryRoute
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameCarry sameProvenance leftEndpointRoute rightEndpointRoute
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameEndpoint sameHidden leftLedgerRoute rightLedgerRoute
  exact ⟨sameCarry, sameEndpoint, sameLedger⟩

theorem SignedDigitStreamPacket_prefix_truncation_stability [AskSetup] [PackageSetup]
    {digits schedule carry provenance endpoint hidden ledger prefixDigits prefixSchedule
      prefixProvenance prefixHidden prefixCarry prefixEndpoint prefixLedger radius regWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SignedDigitStreamPacket digits schedule carry provenance endpoint hidden ledger bundle pkg ->
      hsame digits prefixDigits ->
        hsame schedule prefixSchedule ->
          hsame provenance prefixProvenance ->
            hsame hidden prefixHidden ->
              Cont prefixDigits prefixSchedule prefixCarry ->
                Cont prefixCarry prefixProvenance prefixEndpoint ->
                  Cont prefixEndpoint prefixHidden prefixLedger ->
                    UnaryHistory radius ->
                      Cont prefixEndpoint radius regWindow ->
                        PkgSig bundle prefixLedger pkg ->
                          PkgSig bundle regWindow pkg ->
                            SignedDigitStreamPacket prefixDigits prefixSchedule prefixCarry
                                prefixProvenance prefixEndpoint prefixHidden prefixLedger bundle pkg ∧
                              hsame carry prefixCarry ∧ hsame endpoint prefixEndpoint ∧
                                hsame ledger prefixLedger ∧ UnaryHistory regWindow ∧
                                  hsame regWindow (append prefixEndpoint radius) := by
  intro packet sameDigits sameSchedule sameProvenance sameHidden prefixCarryRow
  intro prefixEndpointRow prefixLedgerRow radiusUnary regWindowRow prefixLedgerSig _regWindowSig
  have prefixDigitsUnary : UnaryHistory prefixDigits :=
    unary_transport packet.left sameDigits
  have prefixScheduleUnary : UnaryHistory prefixSchedule :=
    unary_transport packet.right.left sameSchedule
  have prefixProvenanceUnary : UnaryHistory prefixProvenance :=
    unary_transport packet.right.right.left sameProvenance
  have prefixHiddenUnary : UnaryHistory prefixHidden :=
    unary_transport packet.right.right.right.left sameHidden
  have originalCarryRow : Cont digits schedule carry :=
    packet.right.right.right.right.right.right.right.left
  have originalEndpointRow : Cont carry provenance endpoint :=
    packet.right.right.right.right.right.right.right.right.left
  have originalLedgerRow : Cont endpoint hidden ledger :=
    packet.right.right.right.right.right.right.right.right.right.left
  have sameCarry : hsame carry prefixCarry :=
    cont_respects_hsame sameDigits sameSchedule originalCarryRow prefixCarryRow
  have sameEndpoint : hsame endpoint prefixEndpoint :=
    cont_respects_hsame sameCarry sameProvenance originalEndpointRow prefixEndpointRow
  have sameLedger : hsame ledger prefixLedger :=
    cont_respects_hsame sameEndpoint sameHidden originalLedgerRow prefixLedgerRow
  have prefixCarryUnary : UnaryHistory prefixCarry :=
    unary_cont_closed prefixDigitsUnary prefixScheduleUnary prefixCarryRow
  have prefixEndpointUnary : UnaryHistory prefixEndpoint :=
    unary_cont_closed prefixCarryUnary prefixProvenanceUnary prefixEndpointRow
  have prefixLedgerUnary : UnaryHistory prefixLedger :=
    unary_cont_closed prefixEndpointUnary prefixHiddenUnary prefixLedgerRow
  have prefixPacket :
      SignedDigitStreamPacket prefixDigits prefixSchedule prefixCarry prefixProvenance
        prefixEndpoint prefixHidden prefixLedger bundle pkg :=
    ⟨prefixDigitsUnary, prefixScheduleUnary, prefixProvenanceUnary, prefixHiddenUnary,
      prefixCarryUnary, prefixEndpointUnary, prefixLedgerUnary, prefixCarryRow,
      prefixEndpointRow, prefixLedgerRow, prefixLedgerSig⟩
  have regWindowUnary : UnaryHistory regWindow :=
    unary_cont_closed prefixEndpointUnary radiusUnary regWindowRow
  exact ⟨prefixPacket, sameCarry, sameEndpoint, sameLedger, regWindowUnary, regWindowRow⟩

theorem SignedDigitStreamPacket_regseqrat_handoff [AskSetup] [PackageSetup]
    {digits schedule carry provenance endpoint hidden ledger radius regWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SignedDigitStreamPacket digits schedule carry provenance endpoint hidden ledger bundle pkg ->
      UnaryHistory radius ->
        Cont endpoint radius regWindow ->
          PkgSig bundle regWindow pkg ->
            UnaryHistory digits ∧ UnaryHistory schedule ∧ UnaryHistory carry ∧
              UnaryHistory endpoint ∧ UnaryHistory radius ∧ UnaryHistory regWindow ∧
                hsame carry (append digits schedule) ∧ hsame endpoint (append carry provenance) ∧
                  hsame ledger (append endpoint hidden) ∧
                    hsame regWindow (append endpoint radius) ∧ PkgSig bundle regWindow pkg := by
  intro packet radiusUnary regWindowRow regWindowSig
  obtain ⟨digitsUnary, scheduleUnary, _provenanceUnary, _hiddenUnary, carryUnary,
    endpointUnary, _ledgerUnary, carryRow, endpointRow, ledgerRow, _packageRow⟩ := packet
  have regWindowUnary : UnaryHistory regWindow :=
    unary_cont_closed endpointUnary radiusUnary regWindowRow
  exact ⟨digitsUnary, scheduleUnary, carryUnary, endpointUnary, radiusUnary, regWindowUnary,
    carryRow, endpointRow, ledgerRow, regWindowRow, regWindowSig⟩

theorem SignedDigitStreamPacket_prefix_consumer_invariance [AskSetup] [PackageSetup]
    {digits schedule carry provenance endpoint hidden ledger consumer hiddenConsumer
      consumerLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SignedDigitStreamPacket digits schedule carry provenance endpoint hidden ledger bundle pkg ->
      UnaryHistory consumer ->
        Cont hidden consumer hiddenConsumer ->
          Cont ledger consumer consumerLedger ->
            PkgSig bundle consumerLedger pkg ->
              SignedDigitStreamPacket digits schedule carry provenance endpoint hiddenConsumer
                  consumerLedger bundle pkg ∧
                hsame consumerLedger (append endpoint hiddenConsumer) ∧
                  hsame consumerLedger (append ledger consumer) := by
  intro packet consumerUnary hiddenConsumerRow consumerLedgerRow consumerLedgerSig
  obtain ⟨digitsUnary, scheduleUnary, provenanceUnary, hiddenUnary, carryUnary,
    endpointUnary, ledgerUnary, digitsScheduleRow, carryProvenanceRow, endpointHiddenRow,
    _packetSig⟩ := packet
  have hiddenConsumerUnary : UnaryHistory hiddenConsumer :=
    unary_cont_closed hiddenUnary consumerUnary hiddenConsumerRow
  have consumerLedgerUnary : UnaryHistory consumerLedger :=
    unary_cont_closed ledgerUnary consumerUnary consumerLedgerRow
  have endpointHiddenConsumerRow : Cont endpoint hiddenConsumer consumerLedger := by
    calc
      consumerLedger = append ledger consumer := consumerLedgerRow
      _ = append (append endpoint hidden) consumer := by
        rw [endpointHiddenRow]
      _ = append endpoint (append hidden consumer) := append_assoc endpoint hidden consumer
      _ = append endpoint hiddenConsumer := by
        rw [hiddenConsumerRow]
  have extendedPacket :
      SignedDigitStreamPacket digits schedule carry provenance endpoint hiddenConsumer
        consumerLedger bundle pkg :=
    ⟨digitsUnary, scheduleUnary, provenanceUnary, hiddenConsumerUnary, carryUnary,
      endpointUnary, consumerLedgerUnary, digitsScheduleRow, carryProvenanceRow,
      endpointHiddenConsumerRow, consumerLedgerSig⟩
  exact ⟨extendedPacket, endpointHiddenConsumerRow, consumerLedgerRow⟩

theorem SignedDigitStreamPacket_consumer_read_chain_unary_closed [AskSetup] [PackageSetup]
    {digits schedule carry provenance endpoint hidden ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SignedDigitStreamPacket digits schedule carry provenance endpoint hidden ledger bundle pkg ->
      forall reads : List BHist,
        (forall row : BHist, row ∈ reads -> UnaryHistory row) ->
          UnaryHistory (reads.foldl append ledger) := by
  intro packet reads
  obtain ⟨_digitsUnary, _scheduleUnary, _provenanceUnary, _hiddenUnary, _carryUnary,
    _endpointUnary, ledgerUnary, _carryRow, _endpointRow, _ledgerRow, _packageRow⟩ := packet
  have foldClosed :
      forall base : BHist,
        UnaryHistory base ->
          (forall row : BHist, row ∈ reads -> UnaryHistory row) ->
            UnaryHistory (reads.foldl append base) := by
    induction reads with
    | nil =>
        intro base baseUnary _readUnary
        exact baseUnary
    | cons read tail ih =>
        intro base baseUnary readUnary
        have readHeadUnary : UnaryHistory read :=
          readUnary read (List.Mem.head tail)
        have nextLedgerUnary : UnaryHistory (append base read) :=
          unary_append_closed baseUnary readHeadUnary
        exact ih (append base read) nextLedgerUnary
          (fun row rowInTail => readUnary row (List.Mem.tail read rowInTail))
  intro readUnary
  exact foldClosed ledger ledgerUnary readUnary

theorem SignedDigitStreamPacket_real_seal_semantic_name_certificate [AskSetup] [PackageSetup]
    {digits schedule carry provenance endpoint hidden ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SignedDigitStreamPacket digits schedule carry provenance endpoint hidden ledger bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          SignedDigitStreamPacket digits schedule carry provenance endpoint hidden ledger
            bundle pkg ∧ hsame row ledger)
        (fun row : BHist =>
          SignedDigitStreamPacket digits schedule carry provenance endpoint hidden ledger
            bundle pkg ∧ hsame row ledger)
        (fun row : BHist =>
          SignedDigitStreamPacket digits schedule carry provenance endpoint hidden ledger
            bundle pkg ∧ hsame row ledger)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro ledger (And.intro packet (hsame_refl ledger))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro left right sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro left middle right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro left right sameRows sourceLeft
        exact And.intro sourceLeft.left (hsame_trans (hsame_symm sameRows) sourceLeft.right)
    }
    pattern_sound := by
      intro row sourceRow
      exact sourceRow
    ledger_sound := by
      intro row sourceRow
      exact sourceRow
  }

theorem SignedDigitStreamPacket_public_interface_export [AskSetup] [PackageSetup]
    {digits schedule carry provenance endpoint hidden ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SignedDigitStreamPacket digits schedule carry provenance endpoint hidden ledger bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            SignedDigitStreamPacket digits schedule carry provenance endpoint hidden ledger
                bundle pkg ∧
              (hsame row carry ∨ hsame row endpoint ∨ hsame row ledger))
          (fun row : BHist =>
            SignedDigitStreamPacket digits schedule carry provenance endpoint hidden ledger
                bundle pkg ∧
              (hsame row carry ∨ hsame row endpoint ∨ hsame row ledger))
          (fun row : BHist =>
            SignedDigitStreamPacket digits schedule carry provenance endpoint hidden ledger
                bundle pkg ∧
              (hsame row carry ∨ hsame row endpoint ∨ hsame row ledger))
          hsame ∧
        UnaryHistory digits ∧ UnaryHistory schedule ∧ UnaryHistory carry ∧
          UnaryHistory provenance ∧ UnaryHistory endpoint ∧ UnaryHistory hidden ∧
            UnaryHistory ledger ∧ Cont digits schedule carry ∧ Cont carry provenance endpoint ∧
              Cont endpoint hidden ledger ∧ PkgSig bundle ledger pkg := by
  intro packet
  have sourceAtCarry :
      SignedDigitStreamPacket digits schedule carry provenance endpoint hidden ledger bundle pkg ∧
        (hsame carry carry ∨ hsame carry endpoint ∨ hsame carry ledger) :=
    ⟨packet, Or.inl (hsame_refl carry)⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            SignedDigitStreamPacket digits schedule carry provenance endpoint hidden ledger
                bundle pkg ∧
              (hsame row carry ∨ hsame row endpoint ∨ hsame row ledger))
          (fun row : BHist =>
            SignedDigitStreamPacket digits schedule carry provenance endpoint hidden ledger
                bundle pkg ∧
              (hsame row carry ∨ hsame row endpoint ∨ hsame row ledger))
          (fun row : BHist =>
            SignedDigitStreamPacket digits schedule carry provenance endpoint hidden ledger
                bundle pkg ∧
              (hsame row carry ∨ hsame row endpoint ∨ hsame row ledger))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro carry sourceAtCarry
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        refine ⟨source.left, ?_⟩
        cases source.right with
        | inl sameCarry =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameCarry)
        | inr rest =>
            cases rest with
            | inl sameEndpoint =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameEndpoint))
            | inr sameLedger =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameLedger))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  obtain ⟨digitsUnary, scheduleUnary, provenanceUnary, hiddenUnary, carryUnary, endpointUnary,
    ledgerUnary, carryRow, endpointRow, ledgerRow, packageRow⟩ := packet
  exact ⟨cert, digitsUnary, scheduleUnary, carryUnary, provenanceUnary, endpointUnary,
    hiddenUnary, ledgerUnary, carryRow, endpointRow, ledgerRow, packageRow⟩

def SignedDigitStreamWindowPacket [AskSetup] [PackageSetup]
    (digit schedule carry provenance endpoint ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory digit ∧ UnaryHistory schedule ∧ UnaryHistory carry ∧ UnaryHistory provenance ∧
    UnaryHistory endpoint ∧ UnaryHistory ledger ∧ Cont digit schedule carry ∧
      Cont carry provenance endpoint ∧ Cont endpoint schedule ledger ∧ PkgSig bundle ledger pkg

theorem SignedDigitStreamWindowPacket_window_transport [AskSetup] [PackageSetup]
    {digit schedule carry provenance endpoint ledger digit' schedule' carry' provenance' endpoint'
      ledger' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SignedDigitStreamWindowPacket digit schedule carry provenance endpoint ledger bundle pkg ->
      hsame digit digit' ->
        hsame schedule schedule' ->
          hsame provenance provenance' ->
            Cont digit' schedule' carry' ->
              Cont carry' provenance' endpoint' ->
                Cont endpoint' schedule' ledger' ->
                  PkgSig bundle ledger' pkg ->
                    SignedDigitStreamWindowPacket digit' schedule' carry' provenance' endpoint'
                        ledger' bundle pkg ∧
                      hsame carry carry' ∧ hsame endpoint endpoint' ∧ hsame ledger ledger' := by
  intro packet sameDigit sameSchedule sameProvenance digitScheduleCarry'
  intro carryProvenanceEndpoint' endpointScheduleLedger' pkgLedger'
  have digitUnary : UnaryHistory digit := packet.left
  have scheduleUnary : UnaryHistory schedule := packet.right.left
  have provenanceUnary : UnaryHistory provenance := packet.right.right.right.left
  have digitScheduleCarry : Cont digit schedule carry :=
    packet.right.right.right.right.right.right.left
  have carryProvenanceEndpoint : Cont carry provenance endpoint :=
    packet.right.right.right.right.right.right.right.left
  have endpointScheduleLedger : Cont endpoint schedule ledger :=
    packet.right.right.right.right.right.right.right.right.left
  have digitUnary' : UnaryHistory digit' := unary_transport digitUnary sameDigit
  have scheduleUnary' : UnaryHistory schedule' := unary_transport scheduleUnary sameSchedule
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have carryUnary' : UnaryHistory carry' :=
    unary_cont_closed digitUnary' scheduleUnary' digitScheduleCarry'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed carryUnary' provenanceUnary' carryProvenanceEndpoint'
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed endpointUnary' scheduleUnary' endpointScheduleLedger'
  have sameCarry : hsame carry carry' :=
    cont_respects_hsame sameDigit sameSchedule digitScheduleCarry digitScheduleCarry'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameCarry sameProvenance carryProvenanceEndpoint
      carryProvenanceEndpoint'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameEndpoint sameSchedule endpointScheduleLedger endpointScheduleLedger'
  have packet' :
      SignedDigitStreamWindowPacket digit' schedule' carry' provenance' endpoint' ledger'
        bundle pkg :=
    ⟨digitUnary', scheduleUnary', carryUnary', provenanceUnary', endpointUnary', ledgerUnary',
      digitScheduleCarry', carryProvenanceEndpoint', endpointScheduleLedger', pkgLedger'⟩
  exact ⟨packet', sameCarry, sameEndpoint, sameLedger⟩

theorem SignedDigitStreamPacket_real_regseqrat_window_correspondence [AskSetup]
    [PackageSetup]
    {digits schedule carry provenance endpoint hidden ledger radius regWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SignedDigitStreamPacket digits schedule carry provenance endpoint hidden ledger bundle pkg ->
      UnaryHistory radius ->
        Cont endpoint radius regWindow ->
          PkgSig bundle regWindow pkg ->
            SemanticNameCert
              (fun row : BHist =>
                SignedDigitStreamPacket digits schedule carry provenance endpoint hidden ledger
                    bundle pkg ∧
                  UnaryHistory radius ∧ Cont endpoint radius regWindow ∧
                  PkgSig bundle regWindow pkg ∧
                  (hsame row endpoint ∨ hsame row regWindow ∨ hsame row ledger))
              (fun row : BHist =>
                SignedDigitStreamPacket digits schedule carry provenance endpoint hidden ledger
                    bundle pkg ∧
                  UnaryHistory radius ∧ Cont endpoint radius regWindow ∧
                  PkgSig bundle regWindow pkg ∧
                  (hsame row endpoint ∨ hsame row regWindow ∨ hsame row ledger))
              (fun row : BHist =>
                SignedDigitStreamPacket digits schedule carry provenance endpoint hidden ledger
                    bundle pkg ∧
                  UnaryHistory radius ∧ Cont endpoint radius regWindow ∧
                  PkgSig bundle regWindow pkg ∧
                  (hsame row endpoint ∨ hsame row regWindow ∨ hsame row ledger))
              hsame := by
  intro packet radiusUnary regWindowRow regWindowSig
  have sourceAtEndpoint :
      SignedDigitStreamPacket digits schedule carry provenance endpoint hidden ledger bundle pkg ∧
        UnaryHistory radius ∧ Cont endpoint radius regWindow ∧
        PkgSig bundle regWindow pkg ∧
        (hsame endpoint endpoint ∨ hsame endpoint regWindow ∨ hsame endpoint ledger) :=
    ⟨packet, radiusUnary, regWindowRow, regWindowSig, Or.inl (hsame_refl endpoint)⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint sourceAtEndpoint
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        refine ⟨source.left, source.right.left, source.right.right.left,
          source.right.right.right.left, ?_⟩
        cases source.right.right.right.right with
        | inl sameEndpoint =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameEndpoint)
        | inr rest =>
            cases rest with
            | inl sameRegWindow =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameRegWindow))
            | inr sameLedger =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameLedger))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem SignedDigitStreamWindowPacket_common_window_determinacy [AskSetup] [PackageSetup]
    {digit schedule carry provenance endpoint ledger radius regWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SignedDigitStreamWindowPacket digit schedule carry provenance endpoint ledger bundle pkg ->
      UnaryHistory radius ->
        Cont endpoint radius regWindow ->
          PkgSig bundle regWindow pkg ->
            hsame carry (append digit schedule) ∧ hsame endpoint (append carry provenance) ∧
              hsame ledger (append endpoint schedule) ∧
                hsame regWindow (append endpoint radius) := by
  intro packet _radiusUnary regWindowRow _pkgRow
  obtain ⟨_digitUnary, _scheduleUnary, _carryUnary, _provenanceUnary, _endpointUnary,
    _ledgerUnary, carryRow, endpointRow, ledgerRow, _ledgerSig⟩ := packet
  exact ⟨carryRow, endpointRow, ledgerRow, regWindowRow⟩

end BEDC.Derived.SignedDigitStreamUp
