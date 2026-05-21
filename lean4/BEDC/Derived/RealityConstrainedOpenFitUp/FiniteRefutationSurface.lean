import BEDC.Derived.RealityConstrainedOpenFitUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RealityConstrainedOpenFitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem RealityConstrainedOpenFitFiniteRefutationSurface
    (U : TasteGate.RealityConstrainedOpenFitUp) :
    ∃ H Pi O M F Q L R N : BHist,
      U = TasteGate.RealityConstrainedOpenFitUp.mk H Pi O M F Q L R N ∧
        SemanticNameCert
          (fun row : BHist => hsame row R)
          (fun row : BHist => hsame row F ∨ hsame row Q ∨ hsame row R)
          (fun row : BHist => hsame row R ∧ hsame Q Q ∧ hsame F F)
          hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  cases U with
  | mk H Pi O M F Q L R N =>
      refine ⟨H, Pi, O, M, F, Q, L, R, N, rfl, ?_⟩
      exact {
        core := {
          carrier_inhabited := Exists.intro R (hsame_refl R)
          equiv_refl := by
            intro row _source
            exact hsame_refl row
          equiv_symm := by
            intro _row _other same
            exact hsame_symm same
          equiv_trans := by
            intro _row _middle _other sameLeft sameRight
            exact hsame_trans sameLeft sameRight
          carrier_respects_equiv := by
            intro _row _other same source
            exact hsame_trans (hsame_symm same) source
        }
        pattern_sound := by
          intro _row source
          exact Or.inr (Or.inr source)
        ledger_sound := by
          intro _row source
          exact ⟨source, hsame_refl Q, hsame_refl F⟩
      }

end BEDC.Derived.RealityConstrainedOpenFitUp
