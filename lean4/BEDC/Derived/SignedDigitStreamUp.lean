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
    (digits schedule carry provenance endpoint ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory digits ∧ UnaryHistory schedule ∧ UnaryHistory carry ∧
    UnaryHistory provenance ∧ UnaryHistory endpoint ∧ UnaryHistory ledger ∧
      Cont digits schedule carry ∧ Cont carry provenance endpoint ∧
        Cont endpoint provenance ledger ∧ PkgSig bundle ledger pkg

theorem SignedDigitStreamWindowPacket_finite_window_transport [AskSetup] [PackageSetup]
    {digits schedule carry provenance endpoint ledger digits' schedule' carry'
      provenance' endpoint' ledger' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SignedDigitStreamWindowPacket digits schedule carry provenance endpoint ledger bundle pkg ->
      hsame digits digits' ->
        hsame schedule schedule' ->
          hsame provenance provenance' ->
            Cont digits' schedule' carry' ->
              Cont carry' provenance' endpoint' ->
                Cont endpoint' provenance' ledger' ->
                  PkgSig bundle ledger' pkg ->
                    SignedDigitStreamWindowPacket digits' schedule' carry' provenance'
                        endpoint' ledger' bundle pkg ∧
                      hsame carry carry' ∧ hsame endpoint endpoint' ∧ hsame ledger ledger' := by
  intro packet sameDigits sameSchedule sameProvenance carryRoute' endpointRoute' ledgerRoute'
    ledgerPkg'
  obtain ⟨digitsUnary, scheduleUnary, _carryUnary, provenanceUnary, _endpointUnary,
    _ledgerUnary, carryRoute, endpointRoute, ledgerRoute, _ledgerPkg⟩ := packet
  have digitsUnary' : UnaryHistory digits' :=
    unary_transport digitsUnary sameDigits
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport scheduleUnary sameSchedule
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have carryUnary' : UnaryHistory carry' :=
    unary_cont_closed digitsUnary' scheduleUnary' carryRoute'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed carryUnary' provenanceUnary' endpointRoute'
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed endpointUnary' provenanceUnary' ledgerRoute'
  have sameCarry : hsame carry carry' :=
    cont_respects_hsame sameDigits sameSchedule carryRoute carryRoute'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameCarry sameProvenance endpointRoute endpointRoute'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameEndpoint sameProvenance ledgerRoute ledgerRoute'
  exact
    ⟨⟨digitsUnary', scheduleUnary', carryUnary', provenanceUnary', endpointUnary',
        ledgerUnary', carryRoute', endpointRoute', ledgerRoute', ledgerPkg'⟩,
      sameCarry, sameEndpoint, sameLedger⟩

end BEDC.Derived.SignedDigitStreamUp
