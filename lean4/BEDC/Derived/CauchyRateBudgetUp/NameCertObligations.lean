import BEDC.Derived.CauchyRateBudgetUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyRateBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem CauchyRateBudgetCarrier_namecert_obligations
    (R W Q D E H C P N : BHist) :
    SemanticNameCert
        (fun row : BHist =>
          hsame row R ∨ hsame row W ∨ hsame row Q ∨ hsame row D ∨ hsame row E ∨
            hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
        (fun row : BHist =>
          hsame row R ∨ hsame row W ∨ hsame row Q ∨ hsame row D ∨ hsame row E ∨
            hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
        (fun row : BHist =>
          hsame row R ∨ hsame row W ∨ hsame row Q ∨ hsame row D ∨ hsame row E ∨
            hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
        hsame ∧
      cauchyRateBudgetFields (CauchyRateBudgetUp.mk R W Q D E H C P N) =
        [R, W, Q, D, E, H, C, P, N] := by
  -- BEDC touchpoint anchor: CauchyRateBudgetUp BHist hsame SemanticNameCert
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro R (Or.inl (hsame_refl R))
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
          cases source with
          | inl sameR =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameR)
          | inr rest =>
              cases rest with
              | inl sameW =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameW))
              | inr rest =>
                  cases rest with
                  | inl sameQ =>
                      exact Or.inr
                        (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameQ)))
                  | inr rest =>
                      cases rest with
                      | inl sameD =>
                          exact Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inl (hsame_trans (hsame_symm sameRows) sameD))))
                      | inr rest =>
                          cases rest with
                          | inl sameE =>
                              exact Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl
                                        (hsame_trans (hsame_symm sameRows) sameE)))))
                          | inr rest =>
                              cases rest with
                              | inl sameH =>
                                  exact Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inl
                                              (hsame_trans (hsame_symm sameRows) sameH))))))
                              | inr rest =>
                                  cases rest with
                                  | inl sameC =>
                                      exact Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inl
                                                    (hsame_trans
                                                      (hsame_symm sameRows) sameC)))))))
                                  | inr rest =>
                                      cases rest with
                                      | inl sameP =>
                                          exact Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inl
                                                          (hsame_trans
                                                            (hsame_symm sameRows)
                                                            sameP))))))))
                                      | inr sameN =>
                                          exact Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (hsame_trans
                                                            (hsame_symm sameRows)
                                                            sameN))))))))
      }
      pattern_sound := by
        intro _row source
        exact source
      ledger_sound := by
        intro _row source
        exact source
    }
  · rfl

end BEDC.Derived.CauchyRateBudgetUp
