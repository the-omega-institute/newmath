import BEDC.Derived.CauchyDifferenceCriterionUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyDifferenceCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem CauchyDifferenceCriterionCarrier_namecert_obligations
    (X Y D Z Q W T E H C P N : BHist) :
    SemanticNameCert
        (fun row : BHist =>
          hsame row X ∨ hsame row Y ∨ hsame row D ∨ hsame row Z ∨ hsame row Q ∨
            hsame row W ∨ hsame row T ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
              hsame row P ∨ hsame row N)
        (fun row : BHist =>
          hsame row X ∨ hsame row Y ∨ hsame row D ∨ hsame row Z ∨ hsame row Q ∨
            hsame row W ∨ hsame row T ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
              hsame row P ∨ hsame row N)
        (fun row : BHist =>
          hsame row X ∨ hsame row Y ∨ hsame row D ∨ hsame row Z ∨ hsame row Q ∨
            hsame row W ∨ hsame row T ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
              hsame row P ∨ hsame row N)
        hsame ∧
      cauchyDifferenceCriterionFields (CauchyDifferenceCriterionUp.mk X Y D Z Q W T E H C P N) =
        [X, Y, D, Z, Q, W, T, E, H, C, P, N] := by
  -- BEDC touchpoint anchor: CauchyDifferenceCriterionUp BHist hsame SemanticNameCert
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro X (Or.inl (hsame_refl X))
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
          | inl sameX =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameX)
          | inr rest =>
              cases rest with
              | inl sameY =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameY))
              | inr rest =>
                  cases rest with
                  | inl sameD =>
                      exact Or.inr
                        (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameD)))
                  | inr rest =>
                      cases rest with
                      | inl sameZ =>
                          exact Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inl (hsame_trans (hsame_symm sameRows) sameZ))))
                      | inr rest =>
                          cases rest with
                          | inl sameQ =>
                              exact Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl
                                        (hsame_trans (hsame_symm sameRows) sameQ)))))
                          | inr rest =>
                              cases rest with
                              | inl sameW =>
                                  exact Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inl
                                              (hsame_trans (hsame_symm sameRows) sameW))))))
                              | inr rest =>
                                  cases rest with
                                  | inl sameT =>
                                      exact Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inl
                                                    (hsame_trans
                                                      (hsame_symm sameRows) sameT)))))))
                                  | inr rest =>
                                      cases rest with
                                      | inl sameE =>
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
                                                            sameE))))))))
                                      | inr rest =>
                                          cases rest with
                                          | inl sameH =>
                                              exact Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (Or.inr
                                                            (Or.inr
                                                              (Or.inl
                                                                (hsame_trans
                                                                  (hsame_symm sameRows)
                                                                  sameH)))))))))
                                          | inr rest =>
                                              cases rest with
                                              | inl sameC =>
                                                  exact Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (Or.inr
                                                            (Or.inr
                                                              (Or.inr
                                                                (Or.inr
                                                                  (Or.inr
                                                                    (Or.inl
                                                                      (hsame_trans
                                                                        (hsame_symm sameRows)
                                                                        sameC))))))))))
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
                                                                    (Or.inr
                                                                      (Or.inr
                                                                        (Or.inr
                                                                          (Or.inl
                                                                            (hsame_trans
                                                                              (hsame_symm sameRows)
                                                                              sameP)))))))))))
                                                  | inr sameN =>
                                                      exact Or.inr
                                                        (Or.inr
                                                          (Or.inr
                                                            (Or.inr
                                                              (Or.inr
                                                                (Or.inr
                                                                  (Or.inr
                                                                    (Or.inr
                                                                      (Or.inr
                                                                        (Or.inr
                                                                          (Or.inr
                                                                            (hsame_trans
                                                                              (hsame_symm sameRows)
                                                                              sameN)))))))))))
      }
      pattern_sound := by
        intro _row source
        exact source
      ledger_sound := by
        intro _row source
        exact source
    }
  · rfl

end BEDC.Derived.CauchyDifferenceCriterionUp
