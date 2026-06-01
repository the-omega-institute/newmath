import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

theorem SequentialCompactBaireCylinderExposure {K B S : BHist} :
    Cont K B (append K B) ∧
      Cont (append K B) S (append (append K B) S) ∧
        SemanticNameCert
          (fun row : BHist => hsame row (append (append K B) S))
          (fun row : BHist =>
            hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row (append K B) ∨
              hsame row (append (append K B) S))
          (fun row : BHist =>
            hsame row (append (append K B) S) ∧
              Cont K B (append K B) ∧
                Cont (append K B) S (append (append K B) S))
          hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  refine ⟨rfl, rfl, ?_⟩
  refine
    { core :=
        { carrier_inhabited := ?_
          equiv_refl := ?_
          equiv_symm := ?_
          equiv_trans := ?_
          carrier_respects_equiv := ?_ }
      pattern_sound := ?_
      ledger_sound := ?_ }
  · exact ⟨append (append K B) S, hsame_refl (append (append K B) S)⟩
  · intro row _source
    exact hsame_refl row
  · intro _row _other same
    exact hsame_symm same
  · intro _row _other _third same₁ same₂
    exact hsame_trans same₁ same₂
  · intro _row _other same source
    exact hsame_trans (hsame_symm same) source
  · intro _row source
    exact Or.inr (Or.inr (Or.inr (Or.inr source)))
  · intro _row source
    exact ⟨source, rfl, rfl⟩

end BEDC.Derived.SequentialCompactUp
