import BEDC.Derived.NegativeNameBoundaryUp.NonInternalization
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.NameCert

namespace BEDC.Derived.NegativeNameBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem NegativeNameBoundary_public_export
    {apophaticHandle socket refusalLedger auditGate transport continuation provenance localName
      auditRead consumer publicRead hostTail : BHist} :
    Cont socket refusalLedger continuation →
      Cont refusalLedger auditGate auditRead →
        Cont continuation auditRead consumer →
          Cont consumer provenance publicRead →
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
                Cont consumer provenance publicRead ∧
                  (Cont publicRead (BHist.e0 hostTail) consumer → False) ∧
                    (Cont publicRead (BHist.e1 hostTail) consumer → False) := by
  -- BEDC touchpoint anchor: BHist Cont SemanticNameCert hsame
  intro socketRefusalRoute auditRoute consumerRoute publicRoute
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
    ⟨refusalLedgerCert, consumerRoute, publicRoute,
      cont_mutual_extension_right_tail_absurd.left publicRoute,
      cont_mutual_extension_right_tail_absurd.right publicRoute⟩

end BEDC.Derived.NegativeNameBoundaryUp
