import BEDC.Derived.CookFrontierCoordinateUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CookFrontierCoordinateUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem CookFrontierCoordinate_namecert_obligations
    {F R S A L H C P N endpoint : BHist} :
    TasteGate.cookFrontierCoordinateFields
        (TasteGate.CookFrontierCoordinateUp.mk F R S A L H C P N) =
          [F, R, S, A, L, H, C, P, N] →
      Cont F R S →
        Cont S A L →
          Cont L H C →
            Cont C P endpoint →
              SemanticNameCert
                (fun row : BHist =>
                  hsame row endpoint ∧
                    ∃ packet : TasteGate.CookFrontierCoordinateUp,
                      TasteGate.cookFrontierCoordinateFields packet =
                        [F, R, S, A, L, H, C, P, N])
                (fun row : BHist => Cont C P row)
                (fun row : BHist => hsame row endpoint)
                hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro fields _frontierRoute _sampleRoute _failureRoute endpointRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint
          ⟨hsame_refl endpoint,
            Exists.intro (TasteGate.CookFrontierCoordinateUp.mk F R S A L H C P N)
              fields⟩
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact cont_result_hsame_transport endpointRoute (hsame_symm source.left)
    ledger_sound := by
      intro _row source
      exact source.left
  }

end BEDC.Derived.CookFrontierCoordinateUp
