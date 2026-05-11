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
