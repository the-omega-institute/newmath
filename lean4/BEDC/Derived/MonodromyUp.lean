import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MonodromyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MonodromyTransportPacket [AskSetup] [PackageSetup]
    (loop base localSystem returned ledger transports provenance endpoint scope : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory loop ∧ UnaryHistory base ∧ UnaryHistory localSystem ∧
    UnaryHistory transports ∧ UnaryHistory provenance ∧ Cont loop base ledger ∧
      Cont ledger localSystem returned ∧ Cont returned transports endpoint ∧
        Cont endpoint provenance scope ∧ PkgSig bundle scope pkg

theorem MonodromyTransportPacket_loop_continuation_obligation [AskSetup] [PackageSetup]
    {loop base localSystem returned ledger transports provenance endpoint scope loop' base'
      localSystem' returned' ledger' transports' provenance' endpoint' scope' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MonodromyTransportPacket loop base localSystem returned ledger transports provenance endpoint
        scope bundle pkg ->
      hsame loop loop' ->
        hsame base base' ->
          hsame localSystem localSystem' ->
            hsame transports transports' ->
              hsame provenance provenance' ->
                Cont loop' base' ledger' ->
                  Cont ledger' localSystem' returned' ->
                    Cont returned' transports' endpoint' ->
                      Cont endpoint' provenance' scope' ->
                        PkgSig bundle scope' pkg ->
                          MonodromyTransportPacket loop' base' localSystem' returned' ledger'
                              transports' provenance' endpoint' scope' bundle pkg ∧
                            hsame ledger ledger' ∧ hsame returned returned' ∧
                              hsame endpoint endpoint' ∧ hsame scope scope' := by
  intro packet sameLoop sameBase sameLocalSystem sameTransports sameProvenance ledgerRow'
    returnedRow' endpointRow' scopeRow' scopeSig'
  obtain ⟨loopUnary, baseUnary, localSystemUnary, transportsUnary, provenanceUnary, ledgerRow,
    returnedRow, endpointRow, scopeRow, _scopeSig⟩ := packet
  have loopUnary' : UnaryHistory loop' :=
    unary_transport loopUnary sameLoop
  have baseUnary' : UnaryHistory base' :=
    unary_transport baseUnary sameBase
  have localSystemUnary' : UnaryHistory localSystem' :=
    unary_transport localSystemUnary sameLocalSystem
  have transportsUnary' : UnaryHistory transports' :=
    unary_transport transportsUnary sameTransports
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed loopUnary' baseUnary' ledgerRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameLoop sameBase ledgerRow ledgerRow'
  have returnedUnary' : UnaryHistory returned' :=
    unary_cont_closed ledgerUnary' localSystemUnary' returnedRow'
  have sameReturned : hsame returned returned' :=
    cont_respects_hsame sameLedger sameLocalSystem returnedRow returnedRow'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed returnedUnary' transportsUnary' endpointRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameReturned sameTransports endpointRow endpointRow'
  have sameScope : hsame scope scope' :=
    cont_respects_hsame sameEndpoint sameProvenance scopeRow scopeRow'
  have transported :
      MonodromyTransportPacket loop' base' localSystem' returned' ledger' transports'
        provenance' endpoint' scope' bundle pkg :=
    ⟨loopUnary', baseUnary', localSystemUnary', transportsUnary', provenanceUnary',
      ledgerRow', returnedRow', endpointRow', scopeRow', scopeSig'⟩
  exact ⟨transported, sameLedger, sameReturned, sameEndpoint, sameScope⟩

end BEDC.Derived.MonodromyUp
