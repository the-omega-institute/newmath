import BEDC.Derived.NegativeNameBoundaryUp
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.NameCert

namespace BEDC.Derived.NegativeNameBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem NegativeNameBoundary_quotient_soundness_lattice_link
    {apophaticHandle socket refusalLedger auditGate transport continuation provenance
      localName auditRead quotientRoute quotientTail : BHist}
    (socketRefusalRoute : Cont socket refusalLedger continuation)
    (auditRoute : Cont refusalLedger auditGate auditRead)
    (quotientRouteStep : Cont auditRead provenance quotientRoute) :
    SemanticNameCert
        (fun row : BHist =>
          hsame row refusalLedger ∧
            ∃ packet : NegativeNameBoundaryUp,
              packet =
                NegativeNameBoundaryUp.mk apophaticHandle socket refusalLedger auditGate
                  transport continuation provenance localName)
        (fun row : BHist =>
          hsame row socket ∨ hsame row refusalLedger ∨ hsame row auditGate)
        (fun row : BHist =>
          Cont socket refusalLedger continuation ∧ Cont refusalLedger auditGate auditRead ∧
            hsame row refusalLedger)
        hsame ∧
      Cont auditRead provenance quotientRoute ∧
        (Cont quotientRoute (BHist.e0 quotientTail) auditRead → False) ∧
          (Cont quotientRoute (BHist.e1 quotientTail) auditRead → False) := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert
  exact
    ⟨NegativeNameBoundary_refusal_ledger
        (apophaticHandle := apophaticHandle) (socket := socket)
        (refusalLedger := refusalLedger) (auditGate := auditGate)
        (transport := transport) (continuation := continuation)
        (provenance := provenance) (localName := localName) (auditRead := auditRead)
        socketRefusalRoute auditRoute,
      quotientRouteStep,
      (fun quotientReturn =>
        cont_mutual_extension_right_tail_absurd.left quotientRouteStep quotientReturn),
      (fun quotientReturn =>
        cont_mutual_extension_right_tail_absurd.right quotientRouteStep quotientReturn)⟩

end BEDC.Derived.NegativeNameBoundaryUp
