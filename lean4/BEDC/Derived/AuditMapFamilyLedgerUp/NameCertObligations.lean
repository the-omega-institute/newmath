import BEDC.Derived.AuditMapFamilyLedgerUp.TasteGate

namespace BEDC.Derived.AuditMapFamilyLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

theorem AuditMapFamilyLedgerCarrier_namecert_obligations (x : AuditMapFamilyLedgerUp) :
    ∃ familyTag localAudit neighbourLinks positive conditional obstruction frontier transport
        continuation ledger provenance localName : BHist,
      x =
          AuditMapFamilyLedgerUp.mk familyTag localAudit neighbourLinks positive conditional
            obstruction frontier transport continuation ledger provenance localName ∧
        auditMapFamilyLedgerFields x =
          [familyTag, localAudit, neighbourLinks, positive, conditional, obstruction, frontier,
            transport, continuation, ledger, provenance, localName] ∧
          auditMapFamilyLedgerToEventFlow x =
            [[BMark.b0],
              auditMapFamilyLedgerEncodeBHist familyTag,
              [BMark.b1, BMark.b0],
              auditMapFamilyLedgerEncodeBHist localAudit,
              [BMark.b1, BMark.b1, BMark.b0],
              auditMapFamilyLedgerEncodeBHist neighbourLinks,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              auditMapFamilyLedgerEncodeBHist positive,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              auditMapFamilyLedgerEncodeBHist conditional,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              auditMapFamilyLedgerEncodeBHist obstruction,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              auditMapFamilyLedgerEncodeBHist frontier,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b0],
              auditMapFamilyLedgerEncodeBHist transport,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b0],
              auditMapFamilyLedgerEncodeBHist continuation,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b1, BMark.b0],
              auditMapFamilyLedgerEncodeBHist ledger,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              auditMapFamilyLedgerEncodeBHist provenance,
              [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
                BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
              auditMapFamilyLedgerEncodeBHist localName] := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk familyTag localAudit neighbourLinks positive conditional obstruction frontier transport
      continuation ledger provenance localName =>
      exact
        ⟨familyTag, localAudit, neighbourLinks, positive, conditional, obstruction, frontier,
          transport, continuation, ledger, provenance, localName, rfl, rfl, rfl⟩

end BEDC.Derived.AuditMapFamilyLedgerUp
