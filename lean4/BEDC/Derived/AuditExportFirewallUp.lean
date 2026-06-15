import BEDC.Derived.AuditExportFirewallUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.AuditExportFirewallUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem AuditExportFirewallCarrier_nonescape
    {claim positive audit failure registry consistency ledger transport replay provenance name
      conflictRead : BHist} :
    Cont positive failure conflictRead →
      UnaryHistory positive →
        UnaryHistory failure →
          auditExportFirewallFields
              (AuditExportFirewallUp.mk claim positive audit failure registry consistency ledger
                transport replay provenance name) =
            [claim, positive, audit, failure, registry, consistency, ledger, transport, replay,
              provenance, name] →
            UnaryHistory conflictRead ∧
              List.Mem positive
                (auditExportFirewallFields
                  (AuditExportFirewallUp.mk claim positive audit failure registry consistency ledger
                    transport replay provenance name)) ∧
              List.Mem failure
                (auditExportFirewallFields
                  (AuditExportFirewallUp.mk claim positive audit failure registry consistency ledger
                    transport replay provenance name)) ∧
              List.Mem ledger
                (auditExportFirewallFields
                  (AuditExportFirewallUp.mk claim positive audit failure registry consistency ledger
                    transport replay provenance name)) := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro conflictRoute positiveUnary failureUnary fieldsExact
  constructor
  · exact unary_cont_closed positiveUnary failureUnary conflictRoute
  · constructor
    · rw [fieldsExact]
      exact List.Mem.tail _ (List.Mem.head _)
    · constructor
      · rw [fieldsExact]
        exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      · rw [fieldsExact]
        exact
          List.Mem.tail _ <|
            List.Mem.tail _ <|
              List.Mem.tail _ <|
                List.Mem.tail _ <|
                  List.Mem.tail _ <|
                    List.Mem.tail _ (List.Mem.head _)

end BEDC.Derived.AuditExportFirewallUp
