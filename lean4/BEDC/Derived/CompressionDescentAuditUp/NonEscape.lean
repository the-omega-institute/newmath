import BEDC.Derived.CompressionDescentAuditUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompressionDescentAuditUp.TasteGate

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CompressionDescentAuditNonEscape
    {x : CompressionDescentAuditUp}
    {tower endpoint operation descent ledger failure transport provenance nameCert refusalRead
      repairRead : BHist} :
    x = CompressionDescentAuditUp.mk tower endpoint operation descent ledger failure transport
        provenance nameCert ->
      UnaryHistory failure ->
        UnaryHistory transport ->
          UnaryHistory ledger ->
            Cont failure transport refusalRead ->
              Cont refusalRead ledger repairRead ->
                List.Mem (compressionDescentAuditEncodeBHist failure)
                    (compressionDescentAuditToEventFlow x) ∧
                  UnaryHistory refusalRead ∧
                    UnaryHistory repairRead ∧
                      Cont failure transport refusalRead ∧
                        Cont refusalRead ledger repairRead := by
  -- BEDC touchpoint anchor: BHist BMark Cont UnaryHistory
  intro packetEq failureUnary transportUnary ledgerUnary refusalCont repairCont
  subst packetEq
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed failureUnary transportUnary refusalCont
  have repairUnary : UnaryHistory repairRead :=
    unary_cont_closed refusalUnary ledgerUnary repairCont
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
  exact ⟨failureMem, refusalUnary, repairUnary, refusalCont, repairCont⟩

end BEDC.Derived.CompressionDescentAuditUp.TasteGate
