import BEDC.Derived.ThomaeFunctionUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ThomaeFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Meta.TasteGate

theorem ThomaeFunction_namecert_obligations :
    SemanticNameCert
      (fun row : BHist =>
        ∃ Q D S R E H C P N : BHist,
          row = Q ∧
            FieldFaithful.fields (ThomaeFunctionUp.mk Q D S R E H C P N) =
              [Q, D, S, R, E, H, C, P, N])
      (fun row : BHist =>
        ∃ Q D S R E H C P N : BHist,
          List.Mem row [Q, D, S, R, E, H, C, P, N])
      (fun row : BHist =>
        hsame row BHist.Empty ∨
          ∃ tail : BHist, row = BHist.e0 tail ∨ row = BHist.e1 tail)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert FieldFaithful
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
                            (Exists.intro BHist.Empty ⟨rfl, rfl⟩)))))))))
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
        obtain ⟨Q, D, S, R, E, H, C, P, N, hrow, hfields⟩ := source
        exact
          ⟨Q, D, S, R, E, H, C, P, N,
            hsame_trans (hsame_symm sameRows) hrow, hfields⟩
    }
    pattern_sound := by
      intro row source
      obtain ⟨Q, D, S, R, E, H, C, P, N, hrow, _hfields⟩ := source
      cases hrow
      exact ⟨row, D, S, R, E, H, C, P, N, List.Mem.head _⟩
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

end BEDC.Derived.ThomaeFunctionUp
