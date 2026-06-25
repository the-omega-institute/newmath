import BEDC.Derived.ClosedNormalConfluenceSealUp.NormalSource

namespace BEDC.Derived.ClosedNormalConfluenceSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedNormalConfluenceSealCarrierAdmissionLedger [AskSetup] [PackageSetup]
    {source normal routeLeft routeRight join transports continuations provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source →
      UnaryHistory normal →
        UnaryHistory routeLeft →
          UnaryHistory routeRight →
            UnaryHistory join →
              UnaryHistory transports →
                UnaryHistory continuations →
                  UnaryHistory provenance →
                    UnaryHistory nameCert →
                      PkgSig bundle provenance pkg →
                        PkgSig bundle nameCert pkg →
                          SemanticNameCert
                              (fun row : BHist =>
                                (hsame row source ∨ hsame row normal ∨ hsame row routeLeft ∨
                                    hsame row routeRight ∨ hsame row join ∨
                                      hsame row transports ∨ hsame row continuations ∨
                                        hsame row provenance ∨ hsame row nameCert) ∧
                                  UnaryHistory row)
                              (fun row : BHist =>
                                hsame row source ∨ hsame row normal ∨ hsame row routeLeft ∨
                                  hsame row routeRight ∨ hsame row join ∨
                                    hsame row transports ∨ hsame row continuations ∨
                                      hsame row provenance ∨ hsame row nameCert)
                              (fun row : BHist =>
                                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                  PkgSig bundle nameCert pkg)
                              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro sourceUnary normalUnary routeLeftUnary routeRightUnary joinUnary transportsUnary
    continuationsUnary provenanceUnary nameCertUnary provenancePkg nameCertPkg
  have nameCertSource :
      (fun row : BHist =>
        (hsame row source ∨ hsame row normal ∨ hsame row routeLeft ∨ hsame row routeRight ∨
            hsame row join ∨ hsame row transports ∨ hsame row continuations ∨
              hsame row provenance ∨ hsame row nameCert) ∧
          UnaryHistory row) nameCert := by
    exact
      ⟨Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr (Or.inr (Or.inr (hsame_refl nameCert)))))))),
        nameCertUnary⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro nameCert nameCertSource
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
                        | inr rest₅ =>
                            cases rest₅ with
                            | inl sameTransports =>
                                exact
                                  ⟨Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inl
                                                (hsame_trans (hsame_symm sameRows)
                                                  sameTransports)))))),
                                    transportedUnary⟩
                            | inr rest₆ =>
                                cases rest₆ with
                                | inl sameContinuations =>
                                    exact
                                      ⟨Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inl
                                                      (hsame_trans (hsame_symm sameRows)
                                                        sameContinuations))))))),
                                        transportedUnary⟩
                                | inr rest₇ =>
                                    cases rest₇ with
                                    | inl sameProvenance =>
                                        exact
                                          ⟨Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (Or.inl
                                                            (hsame_trans (hsame_symm sameRows)
                                                              sameProvenance)))))))),
                                            transportedUnary⟩
                                    | inr sameNameCert =>
                                        exact
                                          ⟨Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (Or.inr
                                                            (hsame_trans (hsame_symm sameRows)
                                                              sameNameCert)))))))),
                                            transportedUnary⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, provenancePkg, nameCertPkg⟩
  }

end BEDC.Derived.ClosedNormalConfluenceSealUp
