import BEDC.Derived.ClosedNormalConfluenceSealUp.NormalSource

namespace BEDC.Derived.ClosedNormalConfluenceSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedNormalConfluenceSealJoinWindowInversion [AskSetup] [PackageSetup]
    {source normal routeLeft routeRight join transports continuations provenance nameCert :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source →
      UnaryHistory normal →
        UnaryHistory routeRight →
          Cont source normal routeLeft →
            Cont routeLeft routeRight join →
              PkgSig bundle provenance pkg →
                PkgSig bundle nameCert pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row source ∨ hsame row normal ∨ hsame row routeLeft ∨
                            hsame row routeRight ∨ hsame row join) ∧
                          UnaryHistory row)
                      (fun row : BHist =>
                        hsame row source ∨ hsame row normal ∨ hsame row routeLeft ∨
                          hsame row routeRight ∨ hsame row join ∨ hsame row transports ∨
                            hsame row continuations ∨ hsame row provenance ∨ hsame row nameCert)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont source normal routeLeft ∧
                          Cont routeLeft routeRight join ∧ PkgSig bundle provenance pkg ∧
                            PkgSig bundle nameCert pkg)
                      hsame ∧
                    UnaryHistory routeLeft ∧ UnaryHistory join := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro sourceUnary normalUnary routeRightUnary sourceNormalRoute routeJoin provenancePkg
    nameCertPkg
  have routeLeftUnary : UnaryHistory routeLeft :=
    unary_cont_closed sourceUnary normalUnary sourceNormalRoute
  have joinUnary : UnaryHistory join :=
    unary_cont_closed routeLeftUnary routeRightUnary routeJoin
  have joinSource :
      (fun row : BHist =>
        (hsame row source ∨ hsame row normal ∨ hsame row routeLeft ∨ hsame row routeRight ∨
            hsame row join) ∧
          UnaryHistory row) join := by
    exact
      ⟨Or.inr (Or.inr (Or.inr (Or.inr (hsame_refl join)))), joinUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row source ∨ hsame row normal ∨ hsame row routeLeft ∨
                hsame row routeRight ∨ hsame row join) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row normal ∨ hsame row routeLeft ∨
              hsame row routeRight ∨ hsame row join ∨ hsame row transports ∨
                hsame row continuations ∨ hsame row provenance ∨ hsame row nameCert)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source normal routeLeft ∧
              Cont routeLeft routeRight join ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle nameCert pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro join joinSource
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
        intro _row _other sameRows sourceRow
        have transportedUnary : UnaryHistory _ :=
          unary_transport sourceRow.right sameRows
        cases sourceRow.left with
        | inl sameSource =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameSource), transportedUnary⟩
        | inr rest₁ =>
            cases rest₁ with
            | inl sameNormal =>
                exact
                  ⟨Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameNormal)),
                    transportedUnary⟩
            | inr rest₂ =>
                cases rest₂ with
                | inl sameRouteLeft =>
                    exact
                      ⟨Or.inr
                          (Or.inr
                            (Or.inl (hsame_trans (hsame_symm sameRows) sameRouteLeft))),
                        transportedUnary⟩
                | inr rest₃ =>
                    cases rest₃ with
                    | inl sameRouteRight =>
                        exact
                          ⟨Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inl
                                    (hsame_trans (hsame_symm sameRows) sameRouteRight)))),
                            transportedUnary⟩
                    | inr sameJoin =>
                        exact
                          ⟨Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr (hsame_trans (hsame_symm sameRows) sameJoin)))),
                            transportedUnary⟩
    }
    pattern_sound := by
      intro _row sourceRow
      cases sourceRow.left with
      | inl sameSource =>
          exact Or.inl sameSource
      | inr rest₁ =>
          cases rest₁ with
          | inl sameNormal =>
              exact Or.inr (Or.inl sameNormal)
          | inr rest₂ =>
              cases rest₂ with
              | inl sameRouteLeft =>
                  exact Or.inr (Or.inr (Or.inl sameRouteLeft))
              | inr rest₃ =>
                  cases rest₃ with
                  | inl sameRouteRight =>
                      exact Or.inr (Or.inr (Or.inr (Or.inl sameRouteRight)))
                  | inr sameJoin =>
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameJoin))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, sourceNormalRoute, routeJoin, provenancePkg, nameCertPkg⟩
  }
  exact ⟨cert, routeLeftUnary, joinUnary⟩

end BEDC.Derived.ClosedNormalConfluenceSealUp
