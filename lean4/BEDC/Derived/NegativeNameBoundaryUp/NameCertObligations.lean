import BEDC.Derived.NegativeNameBoundaryUp
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.NegativeNameBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem NegativeNameBoundaryNameCert_obligations
    {apophaticHandle socket refusalLedger auditGate transport continuation provenance
      localName : BHist}
    (socketRefusalRoute : Cont socket refusalLedger continuation) :
    SemanticNameCert
      (fun row : BHist =>
        hsame row apophaticHandle ∧
          ∃ packet : NegativeNameBoundaryUp,
            packet =
              NegativeNameBoundaryUp.mk apophaticHandle socket refusalLedger auditGate
                transport continuation provenance localName)
      (fun row : BHist =>
        hsame row apophaticHandle ∧ hsame socket socket ∧ hsame refusalLedger refusalLedger ∧
          hsame auditGate auditGate)
      (fun row : BHist =>
        hsame row apophaticHandle ∧ Cont socket refusalLedger continuation ∧
          hsame transport transport ∧ hsame provenance provenance ∧ hsame localName localName)
      hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  have sourceHandle :
      (fun row : BHist =>
        hsame row apophaticHandle ∧
          ∃ packet : NegativeNameBoundaryUp,
            packet =
              NegativeNameBoundaryUp.mk apophaticHandle socket refusalLedger auditGate
                transport continuation provenance localName) apophaticHandle := by
    exact
      ⟨hsame_refl apophaticHandle,
        Exists.intro
          (NegativeNameBoundaryUp.mk apophaticHandle socket refusalLedger auditGate transport
            continuation provenance localName)
          rfl⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro apophaticHandle sourceHandle
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' same source
        exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨source.left, hsame_refl socket, hsame_refl refusalLedger, hsame_refl auditGate⟩
    ledger_sound := by
      intro _row source
      exact
        ⟨source.left, socketRefusalRoute, hsame_refl transport, hsame_refl provenance,
          hsame_refl localName⟩
  }

end BEDC.Derived.NegativeNameBoundaryUp
