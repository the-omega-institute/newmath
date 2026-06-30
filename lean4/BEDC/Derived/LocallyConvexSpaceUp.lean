import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert

namespace BEDC.Derived.LocallyConvexSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem LocallyConvexSpaceCarrier_namecert_obligations (V T S B M H C P N : BHist) :
    SemanticNameCert
        (fun row : BHist =>
          hsame row V ∨ hsame row T ∨ hsame row S ∨ hsame row B ∨ hsame row M ∨
            hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
        (fun row : BHist =>
          hsame row V ∨ hsame row T ∨ hsame row S ∨ hsame row B ∨ hsame row M ∨
            hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
        (fun row : BHist =>
          hsame row V ∨ hsame row T ∨ hsame row S ∨ hsame row B ∨ hsame row M ∨
            hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
        hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  exact {
    core := {
      carrier_inhabited := Exists.intro V (Or.inl (hsame_refl V))
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
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.LocallyConvexSpaceUp
