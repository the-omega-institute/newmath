import BEDC.Derived.RealityConstrainedOpenFitUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RealityConstrainedOpenFitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem RealityConstrainedOpenFitCarrier_namecert_obligations
    (U : TasteGate.RealityConstrainedOpenFitUp) :
    ∃ H Pi O M F Q L R N : BHist,
      U = TasteGate.RealityConstrainedOpenFitUp.mk H Pi O M F Q L R N ∧
        SemanticNameCert
          (fun row : BHist => hsame row H)
          (fun row : BHist =>
            hsame row H ∨ hsame row Pi ∨ hsame row O ∨ hsame row M ∨ hsame row F ∨
              hsame row Q ∨ hsame row L ∨ hsame row R ∨ hsame row N)
          (fun row : BHist => hsame row H)
          hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  cases U with
  | mk H Pi O M F Q L R N =>
      refine ⟨H, Pi, O, M, F, Q, L, R, N, rfl, ?_⟩
      exact {
        core := {
          carrier_inhabited := Exists.intro H (hsame_refl H)
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
          exact Or.inl source
        ledger_sound := by
          intro _row source
          exact source
      }

end BEDC.Derived.RealityConstrainedOpenFitUp
