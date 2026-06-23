import BEDC.Derived.RealModulusPurityBoundaryUp.ScopePackage

namespace BEDC.Derived.RealModulusPurityBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealModulusPurityBoundaryTailBudgetExhaustion [AskSetup] [PackageSetup]
    {x : RealModulusPurityBoundaryUp}
    {D S R0 L B H C P N routeRL routeLB predicted consumer tailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    realModulusPurityBoundaryFields x = [D, S, R0, L, B, H, C, P, N] →
      Cont D S R0 →
        Cont R0 L routeRL →
          Cont routeRL B routeLB →
            Cont routeLB H predicted →
              Cont routeLB N consumer →
                Cont consumer B tailRead →
                  UnaryHistory D →
                    UnaryHistory S →
                      UnaryHistory L →
                        UnaryHistory B →
                          UnaryHistory H →
                            UnaryHistory N →
                              PkgSig bundle P pkg →
                                PkgSig bundle N pkg →
                                  PkgSig bundle predicted pkg →
                                    PkgSig bundle tailRead pkg →
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            (hsame row predicted ∨ hsame row consumer ∨
                                                hsame row tailRead) ∧
                                              UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row D ∨ hsame row S ∨ hsame row R0 ∨
                                              hsame row L ∨ hsame row B ∨ hsame row H ∨
                                                hsame row N ∨ hsame row predicted ∨
                                                  hsame row consumer ∨ hsame row tailRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont D S R0 ∧
                                              Cont R0 L routeRL ∧
                                                Cont routeRL B routeLB ∧
                                                  Cont routeLB H predicted ∧
                                                    Cont routeLB N consumer ∧
                                                      Cont consumer B tailRead ∧
                                                        PkgSig bundle P pkg)
                                          hsame ∧
                                        UnaryHistory tailRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro fields routeR0 routeRLCont routeLBCont predictedCont consumerCont consumerTail
    unaryD unaryS unaryL unaryB unaryH unaryN provenancePkg namePkg predictedPkg _tailPkg
  have scopeResult :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row predicted ∨ hsame row consumer) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row S ∨ hsame row R0 ∨ hsame row L ∨ hsame row B ∨
              hsame row H ∨ hsame row N ∨ hsame row predicted ∨ hsame row consumer)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D S R0 ∧ Cont R0 L routeRL ∧
              Cont routeRL B routeLB ∧ Cont routeLB H predicted ∧
                Cont routeLB N consumer ∧ PkgSig bundle P pkg)
          hsame ∧
        UnaryHistory routeRL ∧ UnaryHistory routeLB ∧ UnaryHistory predicted ∧
          UnaryHistory consumer :=
    RealModulusPurityBoundaryScopePackage
      fields routeR0 routeRLCont routeLBCont predictedCont consumerCont unaryD unaryS
      unaryL unaryB unaryH unaryN provenancePkg namePkg predictedPkg
  have predictedUnary : UnaryHistory predicted := scopeResult.right.right.right.left
  have consumerUnary : UnaryHistory consumer := scopeResult.right.right.right.right
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed consumerUnary unaryB consumerTail
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row predicted ∨ hsame row consumer ∨ hsame row tailRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row S ∨ hsame row R0 ∨ hsame row L ∨ hsame row B ∨
              hsame row H ∨ hsame row N ∨ hsame row predicted ∨ hsame row consumer ∨
                hsame row tailRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D S R0 ∧ Cont R0 L routeRL ∧
              Cont routeRL B routeLB ∧ Cont routeLB H predicted ∧
                Cont routeLB N consumer ∧ Cont consumer B tailRead ∧
                  PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro tailRead
        ⟨Or.inr (Or.inr (hsame_refl tailRead)), tailUnary⟩
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
        constructor
        · cases source.left with
          | inl predictedSame =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) predictedSame)
          | inr rest =>
              cases rest with
              | inl consumerSame =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) consumerSame))
              | inr tailSame =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) tailSame))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl predictedSame =>
          exact
            Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inl predictedSame)))))))
      | inr rest =>
          cases rest with
          | inl consumerSame =>
              exact
                Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inl consumerSame))))))))
          | inr tailSame =>
              exact
                Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr tailSame))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, routeR0, routeRLCont, routeLBCont, predictedCont, consumerCont,
          consumerTail, provenancePkg⟩
  }
  exact ⟨cert, tailUnary⟩

end BEDC.Derived.RealModulusPurityBoundaryUp
