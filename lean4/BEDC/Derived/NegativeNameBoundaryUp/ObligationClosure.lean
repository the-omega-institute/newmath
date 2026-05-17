import BEDC.Derived.NegativeNameBoundaryUp
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.NameCert

namespace BEDC.Derived.NegativeNameBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem NegativeNameBoundary_obligation_closure
    {apophaticHandle socket refusalLedger auditGate transport continuation provenance
      localName auditRead closureRead hostTail : BHist} :
    Cont socket refusalLedger continuation →
      Cont refusalLedger auditGate auditRead →
        Cont auditRead provenance closureRead →
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
            Cont auditRead provenance closureRead ∧
              (Cont closureRead (BHist.e0 hostTail) auditRead → False) ∧
                (Cont closureRead (BHist.e1 hostTail) auditRead → False) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro socketRefusalRoute auditRoute closureRoute
  have refusalLedgerCert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row refusalLedger ∧
            ∃ packet : NegativeNameBoundaryUp,
              packet = NegativeNameBoundaryUp.mk apophaticHandle socket refusalLedger
                auditGate transport continuation provenance localName)
        (fun row : BHist =>
          hsame row socket ∨ hsame row refusalLedger ∨ hsame row auditGate)
        (fun row : BHist =>
          Cont socket refusalLedger continuation ∧ Cont refusalLedger auditGate auditRead ∧
            hsame row refusalLedger)
        hsame :=
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
    ⟨refusalLedgerCert, closureRoute,
      cont_mutual_extension_right_tail_absurd.left closureRoute,
      cont_mutual_extension_right_tail_absurd.right closureRoute⟩

end BEDC.Derived.NegativeNameBoundaryUp
