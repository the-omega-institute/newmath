import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RegularCauchyAbsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem RegularCauchyAbsCarrier_namecert_obligations
    (X W D V R E H C P N : BHist) :
    SemanticNameCert
      (fun row : BHist =>
        hsame row X ∨ hsame row W ∨ hsame row D ∨ hsame row V ∨ hsame row R ∨
          hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
      (fun row : BHist =>
        hsame row X ∨ hsame row W ∨ hsame row D ∨ hsame row V ∨ hsame row R ∨
          hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
      (fun row : BHist =>
        hsame row X ∨ hsame row W ∨ hsame row D ∨ hsame row V ∨ hsame row R ∨
          hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro X (Or.inl (hsame_refl X))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        cases source with
        | inl sameX =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameX)
        | inr tailW =>
            cases tailW with
            | inl sameW =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameW))
            | inr tailD =>
                cases tailD with
                | inl sameD =>
                    exact Or.inr (Or.inr
                      (Or.inl (hsame_trans (hsame_symm sameRows) sameD)))
                | inr tailV =>
                    cases tailV with
                    | inl sameV =>
                        exact Or.inr (Or.inr (Or.inr
                          (Or.inl (hsame_trans (hsame_symm sameRows) sameV))))
                    | inr tailR =>
                        cases tailR with
                        | inl sameR =>
                            exact Or.inr (Or.inr (Or.inr (Or.inr
                              (Or.inl (hsame_trans (hsame_symm sameRows) sameR)))))
                        | inr tailE =>
                            cases tailE with
                            | inl sameE =>
                                exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                  (Or.inl (hsame_trans (hsame_symm sameRows) sameE))))))
                            | inr tailH =>
                                cases tailH with
                                | inl sameH =>
                                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                      (Or.inr
                                        (Or.inl
                                          (hsame_trans (hsame_symm sameRows) sameH)))))))
                                | inr tailC =>
                                    cases tailC with
                                    | inl sameC =>
                                        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                          (Or.inr (Or.inr
                                            (Or.inl
                                              (hsame_trans (hsame_symm sameRows) sameC))))))))
                                    | inr tailP =>
                                        cases tailP with
                                        | inl sameP =>
                                            exact Or.inr (Or.inr (Or.inr (Or.inr
                                              (Or.inr (Or.inr (Or.inr (Or.inr
                                                (Or.inl
                                                  (hsame_trans (hsame_symm sameRows)
                                                    sameP)))))))))
                                        | inr sameN =>
                                            exact Or.inr (Or.inr (Or.inr (Or.inr
                                              (Or.inr (Or.inr (Or.inr (Or.inr
                                                (Or.inr
                                                  (hsame_trans (hsame_symm sameRows)
                                                    sameN)))))))))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.RegularCauchyAbsUp
