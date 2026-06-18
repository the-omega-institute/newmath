import BEDC.Derived.CauchyProductCompletionFusionUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyProductCompletionFusionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem CauchyProductCompletionFusion_laws :
    SemanticNameCert
      (fun row : BHist =>
        ∃ Q J S D R E H C P N : BHist,
          row = E ∧
            cauchyProductCompletionFusionFields
                (CauchyProductCompletionFusionUp.mk Q J S D R E H C P N) =
              [Q, J, S, D, R, E, H, C, P, N])
      (fun row : BHist =>
        ∃ Q J S D R E H C P N : BHist,
          List.Mem row [Q, J, S, D, R, E, H, C, P, N])
      (fun row : BHist =>
        hsame row BHist.Empty ∨
          ∃ tail : BHist, row = BHist.e0 tail ∨ row = BHist.e1 tail)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  exact {
    core := {
      carrier_inhabited := by
        exact
          Exists.intro BHist.Empty
            (Exists.intro BHist.Empty
              (Exists.intro BHist.Empty
                (Exists.intro BHist.Empty
                  (Exists.intro BHist.Empty
                    (Exists.intro BHist.Empty
                      (Exists.intro BHist.Empty
                        (Exists.intro BHist.Empty
                          (Exists.intro BHist.Empty
                            (Exists.intro BHist.Empty
                              (Exists.intro BHist.Empty ⟨rfl, rfl⟩))))))))))
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
        intro row _other sameRows source
        obtain ⟨Q, J, S, D, R, E, H, C, P, N, hrow, hfields⟩ := source
        exact
          ⟨Q, J, S, D, R, E, H, C, P, N,
            hsame_trans (hsame_symm sameRows) hrow, hfields⟩
    }
    pattern_sound := by
      intro row source
      obtain ⟨Q, J, S, D, R, E, H, C, P, N, hrow, _hfields⟩ := source
      cases hrow
      exact
        ⟨Q, J, S, D, R, row, H, C, P, N,
          List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _ (List.Mem.head _)))))⟩
    ledger_sound := by
      intro row _source
      cases row with
      | Empty =>
          exact Or.inl (hsame_refl BHist.Empty)
      | e0 tail =>
          exact Or.inr (Exists.intro tail (Or.inl rfl))
      | e1 tail =>
          exact Or.inr (Exists.intro tail (Or.inr rfl))
  }

end BEDC.Derived.CauchyProductCompletionFusionUp
