import BEDC.FKernel.NameCert

namespace BEDC.Derived.ContinuationTerminationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def ContinuationTerminationObligationRowSpec
    (s t tau u b h p n row : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame
  hsame row s ∨ hsame row t ∨ hsame row tau ∨ hsame row u ∨
    hsame row b ∨ hsame row h ∨ hsame row p ∨ hsame row n

theorem ContinuationTerminationCarrier_namecert_obligations
    (s t tau u b h p n : BHist) :
    SemanticNameCert
      (ContinuationTerminationObligationRowSpec s t tau u b h p n)
      (ContinuationTerminationObligationRowSpec s t tau u b h p n)
      (ContinuationTerminationObligationRowSpec s t tau u b h p n)
      hsame ∧
      ContinuationTerminationObligationRowSpec s t tau u b h p n s ∧
        ContinuationTerminationObligationRowSpec s t tau u b h p n t ∧
          ContinuationTerminationObligationRowSpec s t tau u b h p n tau := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  constructor
  · exact
      {
        core := {
          carrier_inhabited := Exists.intro s (Or.inl (hsame_refl s))
          equiv_refl := by
            intro row _source
            exact hsame_refl row
          equiv_symm := by
            intro row col same
            exact hsame_symm same
          equiv_trans := by
            intro row col target sameLeft sameRight
            exact hsame_trans sameLeft sameRight
          carrier_respects_equiv := by
            intro row col same source
            cases source with
            | inl sourceS =>
                exact Or.inl (hsame_trans (hsame_symm same) sourceS)
            | inr rest =>
                cases rest with
                | inl sourceT =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm same) sourceT))
                | inr rest =>
                    cases rest with
                    | inl sourceTau =>
                        exact Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm same) sourceTau)))
                    | inr rest =>
                        cases rest with
                        | inl sourceU =>
                            exact Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inl (hsame_trans (hsame_symm same) sourceU))))
                        | inr rest =>
                            cases rest with
                            | inl sourceB =>
                                exact Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inl (hsame_trans (hsame_symm same) sourceB)))))
                            | inr rest =>
                                cases rest with
                                | inl sourceH =>
                                    exact Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inl
                                                (hsame_trans (hsame_symm same) sourceH))))))
                                | inr rest =>
                                    cases rest with
                                    | inl sourceP =>
                                        exact Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inl
                                                      (hsame_trans (hsame_symm same)
                                                        sourceP)))))))
                                    | inr sourceN =>
                                        exact Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (hsame_trans (hsame_symm same)
                                                        sourceN)))))))
        }
        pattern_sound := by
          intro _row source
          exact source
        ledger_sound := by
          intro _row source
          exact source
      }
  · constructor
    · exact Or.inl (hsame_refl s)
    · constructor
      · exact Or.inr (Or.inl (hsame_refl t))
      · exact Or.inr (Or.inr (Or.inl (hsame_refl tau)))

end BEDC.Derived.ContinuationTerminationUp
