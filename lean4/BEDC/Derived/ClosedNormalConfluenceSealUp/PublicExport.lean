import BEDC.Derived.ClosedNormalConfluenceSealUp.NormalSource

namespace BEDC.Derived.ClosedNormalConfluenceSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedNormalConfluenceSealPublicExport [AskSetup] [PackageSetup]
    {source normal routeLeft routeRight join transports continuations provenance nameCert exportRead
      boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source →
      UnaryHistory normal →
        UnaryHistory routeRight →
          UnaryHistory transports →
            Cont source normal routeLeft →
              Cont routeLeft routeRight join →
                Cont join transports exportRead →
                  Cont join transports boundaryRead →
                    PkgSig bundle provenance pkg →
                      PkgSig bundle exportRead pkg →
                        PkgSig bundle boundaryRead pkg →
                          SemanticNameCert
                              (fun row : BHist =>
                                (hsame row source ∨ hsame row normal ∨ hsame row routeLeft ∨
                                    hsame row routeRight ∨ hsame row join ∨
                                      hsame row exportRead) ∧
                                  UnaryHistory row)
                              (fun row : BHist =>
                                hsame row source ∨ hsame row normal ∨ hsame row routeLeft ∨
                                  hsame row routeRight ∨ hsame row join ∨ hsame row transports ∨
                                    hsame row continuations ∨ hsame row provenance ∨
                                      hsame row nameCert ∨ hsame row exportRead ∨
                                        hsame row boundaryRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont source normal routeLeft ∧
                                  Cont routeLeft routeRight join ∧
                                    Cont join transports exportRead ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle exportRead pkg)
                              hsame ∧
                            UnaryHistory routeLeft ∧ UnaryHistory join ∧
                              UnaryHistory exportRead ∧ hsame boundaryRead boundaryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro sourceUnary normalUnary routeRightUnary transportsUnary sourceNormalRoute routeJoin
    exportRoute boundaryRoute provenancePkg exportPkg _boundaryPkg
  have routeLeftUnary : UnaryHistory routeLeft :=
    unary_cont_closed sourceUnary normalUnary sourceNormalRoute
  have joinUnary : UnaryHistory join :=
    unary_cont_closed routeLeftUnary routeRightUnary routeJoin
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed joinUnary transportsUnary exportRoute
  have exportSource :
      (fun row : BHist =>
        (hsame row source ∨ hsame row normal ∨ hsame row routeLeft ∨
            hsame row routeRight ∨ hsame row join ∨ hsame row exportRead) ∧
          UnaryHistory row) exportRead := by
    exact
      ⟨Or.inr
          (Or.inr
            (Or.inr
              (Or.inr (Or.inr (hsame_refl exportRead))))),
        exportUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row source ∨ hsame row normal ∨ hsame row routeLeft ∨
                hsame row routeRight ∨ hsame row join ∨ hsame row exportRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row normal ∨ hsame row routeLeft ∨
              hsame row routeRight ∨ hsame row join ∨ hsame row transports ∨
                hsame row continuations ∨ hsame row provenance ∨ hsame row nameCert ∨
                  hsame row exportRead ∨ hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source normal routeLeft ∧
              Cont routeLeft routeRight join ∧ Cont join transports exportRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle exportRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exportRead exportSource
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
                    | inr rest₄ =>
                        cases rest₄ with
                        | inl sameJoin =>
                            exact
                              ⟨Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inl
                                          (hsame_trans (hsame_symm sameRows) sameJoin))))),
                                transportedUnary⟩
                        | inr sameExport =>
                            exact
                              ⟨Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (hsame_trans (hsame_symm sameRows) sameExport))))),
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
                  | inr rest₄ =>
                      cases rest₄ with
                      | inl sameJoin =>
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameJoin))))
                      | inr sameExport =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr (Or.inl sameExport)))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, sourceNormalRoute, routeJoin, exportRoute, provenancePkg,
          exportPkg⟩
  }
  have boundarySame : hsame boundaryRead boundaryRead :=
    cont_deterministic boundaryRoute boundaryRoute
  exact ⟨cert, routeLeftUnary, joinUnary, exportUnary, boundarySame⟩

end BEDC.Derived.ClosedNormalConfluenceSealUp
