import BEDC.Derived.FableBranchWitnessUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.FableBranchWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert

theorem FableBranchWitnessCarrier_selector_exposure
    {h m r E A H C P N : BHist} :
    SemanticNameCert
      (fun row : BHist =>
        hsame row m ∧
          ∃ W : FableBranchWitnessUp,
            fableBranchWitnessToEventFlow W =
              fableBranchWitnessToEventFlow (FableBranchWitnessUp.mk h m r E A H C P N))
      (fun row : BHist =>
        hsame row h ∨ hsame row m ∨ hsame row r ∨ hsame row E ∨ hsame row A ∨
          hsame row C ∨ hsame row N)
      (fun row : BHist =>
        hsame row m ∧ fableBranchWitnessEncodeBHist BHist.Empty = ([] : List BMark))
      hsame := by
  -- BEDC touchpoint anchor: BHist BMark hsame SemanticNameCert
  let W := FableBranchWitnessUp.mk h m r E A H C P N
  have sourceMark :
      (fun row : BHist =>
        hsame row m ∧
          ∃ W : FableBranchWitnessUp,
            fableBranchWitnessToEventFlow W =
              fableBranchWitnessToEventFlow (FableBranchWitnessUp.mk h m r E A H C P N)) m := by
    exact ⟨hsame_refl m, Exists.intro W rfl⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro m sourceMark
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inl source.left)
    ledger_sound := by
      intro _row source
      cases source.left
      exact ⟨hsame_refl m, rfl⟩
  }

end BEDC.Derived.FableBranchWitnessUp
