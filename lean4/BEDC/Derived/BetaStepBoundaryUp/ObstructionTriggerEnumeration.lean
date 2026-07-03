import BEDC.Derived.BetaStepBoundaryUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BetaStepBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem BetaStepBoundaryObstructionTriggerEnumeration
    {rule conversion obstruction transport route provenance name triggerRead : BHist} :
    Cont obstruction route triggerRead ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row triggerRead ∧ hsame row (BEDC.FKernel.Cont.append obstruction route))
          (fun row : BHist =>
            hsame row obstruction ∨ hsame row route ∨ hsame row triggerRead)
          (fun row : BHist => Cont obstruction route triggerRead ∧ hsame row triggerRead)
          hsame := by
  -- BEDC touchpoint anchor: BetaStepBoundaryUp BHist Cont hsame SemanticNameCert
  intro triggerRoute
  have _ruleRow : hsame rule rule := hsame_refl rule
  have _conversionRow : hsame conversion conversion := hsame_refl conversion
  have _transportRow : hsame transport transport := hsame_refl transport
  have _provenanceRow : hsame provenance provenance := hsame_refl provenance
  have _nameRow : hsame name name := hsame_refl name
  have triggerExact : hsame triggerRead (BEDC.FKernel.Cont.append obstruction route) := by
    cases triggerRoute
    exact hsame_refl _
  exact {
    core := {
      carrier_inhabited := Exists.intro triggerRead
        ⟨hsame_refl triggerRead, triggerExact⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨triggerRoute, source.left⟩
  }

end BEDC.Derived.BetaStepBoundaryUp
