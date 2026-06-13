import BEDC.Derived.TriggerBlockerDualityUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.TriggerBlockerDualityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TriggerBlockerDualityNameCertObligations
    {source algebra lattice blocker intersections nerve transport replay provenance localName : BHist} :
    SemanticNameCert
        (fun row : BHist =>
          (hsame row source ∨ hsame row algebra ∨ hsame row lattice ∨ hsame row blocker ∨
              hsame row intersections ∨ hsame row nerve ∨ hsame row localName) ∧
            ∃ packet : TriggerBlockerDualityUp,
              packet =
                TriggerBlockerDualityUp.mk source algebra lattice blocker intersections nerve
                  transport replay provenance localName)
        (fun row : BHist =>
          hsame row source ∨ hsame row algebra ∨ hsame row lattice ∨ hsame row blocker ∨
            hsame row intersections ∨ hsame row nerve ∨ hsame row localName)
        (fun row : BHist =>
          (hsame row source ∨ hsame row algebra ∨ hsame row lattice ∨ hsame row blocker ∨
              hsame row intersections ∨ hsame row nerve ∨ hsame row localName) ∧
            hsame blocker blocker ∧ hsame nerve nerve)
        hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  refine
    { core := ?core
      pattern_sound := ?pattern_sound
      ledger_sound := ?ledger_sound }
  · refine
      { carrier_inhabited := ?carrier_inhabited
        equiv_refl := ?equiv_refl
        equiv_symm := ?equiv_symm
        equiv_trans := ?equiv_trans
        carrier_respects_equiv := ?carrier_respects_equiv }
    · exact
        ⟨localName,
          ⟨Or.inr
            (Or.inr
              (Or.inr (Or.inr (Or.inr (Or.inr (hsame_refl localName)))))),
            ⟨TriggerBlockerDualityUp.mk source algebra lattice blocker intersections nerve
                transport replay provenance localName, rfl⟩⟩⟩
    · intro row _source
      exact hsame_refl row
    · intro _row _other sameRows
      exact hsame_symm sameRows
    · intro _row _middle _other sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro row other sameRows sourceRow
      cases sameRows
      exact sourceRow
  · intro _row sourceRow
    exact sourceRow.left
  · intro _row sourceRow
    exact ⟨sourceRow.left, hsame_refl blocker, hsame_refl nerve⟩

end BEDC.Derived.TriggerBlockerDualityUp
