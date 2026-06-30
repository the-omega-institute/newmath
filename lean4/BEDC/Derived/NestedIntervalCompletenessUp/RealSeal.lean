import BEDC.Derived.NestedIntervalCompletenessUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.NestedIntervalCompletenessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem NestedIntervalCompleteness_real_seal :
    SemanticNameCert
      (fun row : BHist =>
        ∃ B N C W R E H T P Q : BHist,
          row = E ∧
            NestedIntervalCompletenessTasteGate_single_carrier_alignment_fields
                (NestedIntervalCompletenessUp.mk B N C W R E H T P Q) =
              [B, N, C, W, R, E, H, T, P, Q])
      (fun row : BHist =>
        ∃ B N C W R E H T P Q : BHist,
          List.Mem row [B, N, C, W, R, E, H, T, P, Q])
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
        obtain ⟨B, N, C, W, R, E, H, T, P, Q, hrow, hfields⟩ := source
        exact
          ⟨B, N, C, W, R, E, H, T, P, Q,
            hsame_trans (hsame_symm sameRows) hrow, hfields⟩
    }
    pattern_sound := by
      intro row source
      obtain ⟨B, N, C, W, R, E, H, T, P, Q, hrow, _hfields⟩ := source
      cases hrow
      exact
        ⟨B, N, C, W, R, row, H, T, P, Q,
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

end BEDC.Derived.NestedIntervalCompletenessUp
