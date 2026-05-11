import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SignedDigitStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

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

end BEDC.Derived.SignedDigitStreamUp
