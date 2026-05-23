import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert

namespace BEDC.Derived.SeparatedCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem SeparatedCompletionCarrier_semantic_name_certificate
    (M D C Z U H R T P N : BHist) :
    SemanticNameCert
      (fun row : BHist =>
        hsame row M ∨ hsame row D ∨ hsame row C ∨ hsame row Z ∨ hsame row U ∨
          hsame row H ∨ hsame row R ∨ hsame row T ∨ hsame row P ∨ hsame row N)
      (fun row : BHist =>
        hsame row M ∨ hsame row D ∨ hsame row C ∨ hsame row Z ∨ hsame row U ∨
          hsame row H ∨ hsame row R ∨ hsame row T ∨ hsame row P ∨ hsame row N)
      (fun row : BHist =>
        hsame row M ∨ hsame row D ∨ hsame row C ∨ hsame row Z ∨ hsame row U ∨
          hsame row H ∨ hsame row R ∨ hsame row T ∨ hsame row P ∨ hsame row N)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  exact {
    core := {
      carrier_inhabited := Exists.intro M (Or.inl (hsame_refl M))
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
        intro row other sameRows source
        cases source with
        | inl sameM =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameM)
        | inr rest =>
            cases rest with
            | inl sameD =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameD))
            | inr rest =>
                cases rest with
                | inl sameC =>
                    exact Or.inr (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameC)))
                | inr rest =>
                    cases rest with
                    | inl sameZ =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameZ))))
                    | inr rest =>
                        cases rest with
                        | inl sameU =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl (hsame_trans (hsame_symm sameRows) sameU)))))
                        | inr rest =>
                            cases rest with
                            | inl sameH =>
                                exact
                                  Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inl
                                              (hsame_trans (hsame_symm sameRows) sameH))))))
                            | inr rest =>
                                cases rest with
                                | inl sameR =>
                                    exact
                                      Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inl
                                                    (hsame_trans
                                                      (hsame_symm sameRows) sameR)))))))
                                | inr rest =>
                                    cases rest with
                                    | inl sameT =>
                                        exact
                                          Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inl
                                                          (hsame_trans
                                                            (hsame_symm sameRows) sameT))))))))
                                    | inr rest =>
                                        cases rest with
                                        | inl sameP =>
                                            exact
                                              Or.inr
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
                                                                  sameP)))))))))
                                        | inr sameN =>
                                            exact
                                              Or.inr
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
                                                                  sameN)))))))))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.SeparatedCompletionUp
