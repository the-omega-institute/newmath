import BEDC.Derived.CompressionDescentAuditUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompressionDescentAuditUp.TasteGate

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CompressionDescentAuditLedgerExhaustion
    {x : CompressionDescentAuditUp} {routeRead ledgerRead : BHist} :
    (∃ tower endpoint operation descent ledger failure transport provenance nameCert : BHist,
      x = CompressionDescentAuditUp.mk tower endpoint operation descent ledger failure transport
        provenance nameCert ∧
        UnaryHistory tower ∧ UnaryHistory descent ∧ UnaryHistory ledger ∧
          Cont tower descent routeRead ∧ Cont descent ledger ledgerRead) →
      ∃ tower endpoint operation descent ledger failure transport provenance nameCert : BHist,
        x = CompressionDescentAuditUp.mk tower endpoint operation descent ledger failure transport
          provenance nameCert ∧
          List.Mem (compressionDescentAuditEncodeBHist tower)
            (compressionDescentAuditToEventFlow x) ∧
            List.Mem (compressionDescentAuditEncodeBHist endpoint)
              (compressionDescentAuditToEventFlow x) ∧
              List.Mem (compressionDescentAuditEncodeBHist operation)
                (compressionDescentAuditToEventFlow x) ∧
                List.Mem (compressionDescentAuditEncodeBHist descent)
                  (compressionDescentAuditToEventFlow x) ∧
                  List.Mem (compressionDescentAuditEncodeBHist ledger)
                    (compressionDescentAuditToEventFlow x) ∧
                    List.Mem (compressionDescentAuditEncodeBHist failure)
                      (compressionDescentAuditToEventFlow x) ∧
                      UnaryHistory routeRead ∧ UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: BHist BMark Cont UnaryHistory
  intro accepted
  obtain ⟨tower, endpoint, operation, descent, ledger, failure, transport, provenance,
    nameCert, packetEq, towerUnary, descentUnary, ledgerUnary, routeCont, ledgerCont⟩ :=
    accepted
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed towerUnary descentUnary routeCont
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed descentUnary ledgerUnary ledgerCont
  subst packetEq
  have towerMem :
      List.Mem (compressionDescentAuditEncodeBHist tower)
        (compressionDescentAuditToEventFlow
          (CompressionDescentAuditUp.mk tower endpoint operation descent ledger failure
            transport provenance nameCert)) := by
    simp only [compressionDescentAuditToEventFlow]
    repeat
      first
      | exact List.Mem.head _
      | apply List.Mem.tail
  have endpointMem :
      List.Mem (compressionDescentAuditEncodeBHist endpoint)
        (compressionDescentAuditToEventFlow
          (CompressionDescentAuditUp.mk tower endpoint operation descent ledger failure
            transport provenance nameCert)) := by
    simp only [compressionDescentAuditToEventFlow]
    repeat
      first
      | exact List.Mem.head _
      | apply List.Mem.tail
  have operationMem :
      List.Mem (compressionDescentAuditEncodeBHist operation)
        (compressionDescentAuditToEventFlow
          (CompressionDescentAuditUp.mk tower endpoint operation descent ledger failure
            transport provenance nameCert)) := by
    simp only [compressionDescentAuditToEventFlow]
    repeat
      first
      | exact List.Mem.head _
      | apply List.Mem.tail
  have descentMem :
      List.Mem (compressionDescentAuditEncodeBHist descent)
        (compressionDescentAuditToEventFlow
          (CompressionDescentAuditUp.mk tower endpoint operation descent ledger failure
            transport provenance nameCert)) := by
    simp only [compressionDescentAuditToEventFlow]
    repeat
      first
      | exact List.Mem.head _
      | apply List.Mem.tail
  have ledgerMem :
      List.Mem (compressionDescentAuditEncodeBHist ledger)
        (compressionDescentAuditToEventFlow
          (CompressionDescentAuditUp.mk tower endpoint operation descent ledger failure
            transport provenance nameCert)) := by
    simp only [compressionDescentAuditToEventFlow]
    repeat
      first
      | exact List.Mem.head _
      | apply List.Mem.tail
  have failureMem :
      List.Mem (compressionDescentAuditEncodeBHist failure)
        (compressionDescentAuditToEventFlow
          (CompressionDescentAuditUp.mk tower endpoint operation descent ledger failure
            transport provenance nameCert)) := by
    simp only [compressionDescentAuditToEventFlow]
    repeat
      first
      | exact List.Mem.head _
      | apply List.Mem.tail
  exact
    ⟨tower, endpoint, operation, descent, ledger, failure, transport, provenance, nameCert,
      rfl, towerMem, endpointMem, operationMem, descentMem, ledgerMem, failureMem,
      routeReadUnary, ledgerReadUnary⟩

end BEDC.Derived.CompressionDescentAuditUp.TasteGate
