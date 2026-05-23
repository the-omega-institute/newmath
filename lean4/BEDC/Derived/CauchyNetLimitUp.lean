import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyNetLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem CauchyNetLimitCarrier_semantic_name_certificate
    (K W R D A H C P N : BHist) :
    SemanticNameCert
      (fun row : BHist =>
        hsame row K ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨ hsame row A ∨
          hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
      (fun row : BHist =>
        hsame row K ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨ hsame row A ∨
          hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
      (fun row : BHist =>
        hsame row K ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨ hsame row A ∨
          hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  exact {
    core := {
      carrier_inhabited := Exists.intro K (Or.inl (hsame_refl K))
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
        | inl sameK =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameK)
        | inr rest =>
            cases rest with
            | inl sameW =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameW))
            | inr rest =>
                cases rest with
                | inl sameR =>
                    exact Or.inr (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameR)))
                | inr rest =>
                    cases rest with
                    | inl sameD =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameD))))
                    | inr rest =>
                        cases rest with
                        | inl sameA =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl (hsame_trans (hsame_symm sameRows) sameA)))))
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
                                | inl sameC =>
                                    exact
                                      Or.inr
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
                                                            (hsame_symm sameRows) sameP))))))))
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
                                                          (hsame_trans
                                                            (hsame_symm sameRows) sameN))))))))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.CauchyNetLimitUp
