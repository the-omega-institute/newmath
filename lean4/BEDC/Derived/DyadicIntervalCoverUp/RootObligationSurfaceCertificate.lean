import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverRootObligationSurface_semantic_name_certificate
    [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            (hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨
              hsame row V ∨ hsame row W ∨ hsame row Q ∨ hsame row A ∨
                hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨
              hsame row V ∨ hsame row W ∨ hsame row Q ∨ hsame row A ∨
                hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro surface
  have lUnary : UnaryHistory L := surface.left
  have pPkg : PkgSig bundle P pkg :=
    surface.right.right.right.right.right.right.right.right.right.right.right.right.left
  have nPkg : PkgSig bundle N pkg :=
    surface.right.right.right.right.right.right.right.right.right.right.right.right.right
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨
              hsame row V ∨ hsame row W ∨ hsame row Q ∨ hsame row A ∨
                hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨
              hsame row V ∨ hsame row W ∨ hsame row Q ∨ hsame row A ∨
                hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro L ⟨Or.inl (hsame_refl L), lUnary⟩
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
        have carry :
            hsame _other L ∨ hsame _other U ∨ hsame _other M ∨ hsame _other R ∨
              hsame _other V ∨ hsame _other W ∨ hsame _other Q ∨ hsame _other A ∨
                hsame _other H ∨ hsame _other C ∨ hsame _other P ∨ hsame _other N := by
          cases source.left with
          | inl sameL =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameL)
          | inr rest =>
              cases rest with
              | inl sameU =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameU))
              | inr rest =>
                  cases rest with
                  | inl sameM =>
                      exact
                        Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameM)))
                  | inr rest =>
                      cases rest with
                      | inl sameR =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameR))))
                      | inr rest =>
                          cases rest with
                          | inl sameV =>
                              exact
                                Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inl
                                          (hsame_trans (hsame_symm sameRows) sameV)))))
                          | inr rest =>
                              cases rest with
                              | inl sameW =>
                                  exact
                                    Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inl
                                                (hsame_trans (hsame_symm sameRows) sameW))))))
                              | inr rest =>
                                  cases rest with
                                  | inl sameQ =>
                                      exact
                                        Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inl
                                                      (hsame_trans
                                                        (hsame_symm sameRows) sameQ)))))))
                                  | inr rest =>
                                      cases rest with
                                      | inl sameA =>
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
                                                              (hsame_symm sameRows)
                                                              sameA))))))))
                                      | inr rest =>
                                          cases rest with
                                          | inl sameH =>
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
                                                                    sameH)))))))))
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
                                                                          (Or.inr
                                                                            (Or.inl
                                                                              (hsame_trans
                                                                                (hsame_symm sameRows)
                                                                                sameP)))))))))))
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
                                                                          (Or.inr
                                                                            (Or.inr
                                                                              (hsame_trans
                                                                                (hsame_symm sameRows)
                                                                                sameN)))))))))))
        exact ⟨carry, unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pPkg, nPkg⟩
  }
  exact cert

end BEDC.Derived.DyadicIntervalCoverUp
