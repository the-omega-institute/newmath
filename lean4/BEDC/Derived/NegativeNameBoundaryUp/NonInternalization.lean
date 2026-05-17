import BEDC.Derived.NegativeNameBoundaryUp
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.NameCert

namespace BEDC.Derived.NegativeNameBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem NegativeNameBoundary_non_internalization
    {apophaticHandle socket refusalLedger auditGate transport continuation provenance localName
      auditRead consumer hostTail : BHist} :
    Cont socket refusalLedger continuation →
      Cont refusalLedger auditGate auditRead →
        Cont continuation auditRead consumer →
          SemanticNameCert
              (fun row : BHist =>
                hsame row refusalLedger ∧
                  ∃ packet : NegativeNameBoundaryUp,
                    packet = NegativeNameBoundaryUp.mk apophaticHandle socket refusalLedger
                      auditGate transport continuation provenance localName)
              (fun row : BHist =>
                hsame row socket ∨ hsame row refusalLedger ∨ hsame row auditGate)
              (fun row : BHist =>
                Cont socket refusalLedger continuation ∧
                  Cont refusalLedger auditGate auditRead ∧ hsame row refusalLedger)
              hsame ∧
            Cont continuation auditRead consumer ∧
              (Cont consumer (BHist.e0 hostTail) continuation → False) ∧
                (Cont consumer (BHist.e1 hostTail) continuation → False) := by
  -- BEDC touchpoint anchor: BHist Cont SemanticNameCert hsame
  intro socketRefusalRoute auditRoute consumerRoute
  have refusalLedgerCert :=
    NegativeNameBoundary_refusal_ledger
      (apophaticHandle := apophaticHandle)
      (socket := socket)
      (refusalLedger := refusalLedger)
      (auditGate := auditGate)
      (transport := transport)
      (continuation := continuation)
      (provenance := provenance)
      (localName := localName)
      (auditRead := auditRead)
      socketRefusalRoute auditRoute
  exact
    ⟨refusalLedgerCert, consumerRoute,
      cont_mutual_extension_right_tail_absurd.left consumerRoute,
      cont_mutual_extension_right_tail_absurd.right consumerRoute⟩

end BEDC.Derived.NegativeNameBoundaryUp
