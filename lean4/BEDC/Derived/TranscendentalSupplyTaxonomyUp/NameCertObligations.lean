import BEDC.Derived.TranscendentalSupplyTaxonomyUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.TranscendentalSupplyTaxonomyUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TranscendentalSupplyTaxonomyNameCert_obligations
    {socketKind requestedSupply gap auditGate site transport route provenance name : BHist}
    (siteGapRoute : Cont site gap route) (gapAuditRoute : Cont gap auditGate route) :
    SemanticNameCert
      (fun row : BHist =>
        hsame row socketKind ∧
          ∃ packet : TranscendentalSupplyTaxonomyUp,
            packet =
              TranscendentalSupplyTaxonomyUp.mk socketKind requestedSupply gap auditGate site
                transport route provenance name)
      (fun row : BHist =>
        hsame row socketKind ∧ hsame requestedSupply requestedSupply ∧ hsame gap gap ∧
          hsame auditGate auditGate ∧ hsame site site)
      (fun row : BHist =>
        hsame row socketKind ∧ Cont site gap route ∧ Cont gap auditGate route ∧
          hsame transport transport ∧ hsame provenance provenance ∧ hsame name name)
      hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  have sourceSocket :
      (fun row : BHist =>
        hsame row socketKind ∧
          ∃ packet : TranscendentalSupplyTaxonomyUp,
            packet =
              TranscendentalSupplyTaxonomyUp.mk socketKind requestedSupply gap auditGate site
                transport route provenance name) socketKind := by
    exact
      ⟨hsame_refl socketKind,
        Exists.intro
          (TranscendentalSupplyTaxonomyUp.mk socketKind requestedSupply gap auditGate site
            transport route provenance name)
          rfl⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro socketKind sourceSocket
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
        ⟨source.left, hsame_refl requestedSupply, hsame_refl gap, hsame_refl auditGate,
          hsame_refl site⟩
    ledger_sound := by
      intro _row source
      exact
        ⟨source.left, siteGapRoute, gapAuditRoute, hsame_refl transport,
          hsame_refl provenance, hsame_refl name⟩
  }

end BEDC.Derived.TranscendentalSupplyTaxonomyUp
