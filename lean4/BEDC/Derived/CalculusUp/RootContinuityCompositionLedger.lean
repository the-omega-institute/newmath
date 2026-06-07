import BEDC.Derived.CalculusUp.CompletionSourceEnvelopeObligations

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusRootContinuityCompositionLedger [AskSetup] [PackageSetup]
    {C D I L R Q Y H T P N derivativeRead integralRead limitRead dyadicRead realRead
      derivativePublic integralPublic limitPublic : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory C →
      UnaryHistory D →
        UnaryHistory I →
          UnaryHistory L →
            UnaryHistory Q →
              UnaryHistory Y →
                UnaryHistory R →
                  UnaryHistory N →
                    Cont C D derivativeRead →
                      Cont C I integralRead →
                        Cont C L limitRead →
                          Cont Q Y dyadicRead →
                            Cont dyadicRead R realRead →
                              Cont realRead N derivativePublic →
                                Cont realRead N integralPublic →
                                  Cont realRead N limitPublic →
                                    PkgSig bundle P pkg →
                                      PkgSig bundle derivativePublic pkg →
                                        PkgSig bundle integralPublic pkg →
                                          PkgSig bundle limitPublic pkg →
                                            SemanticNameCert
                                                (fun row : BHist =>
                                                  (hsame row derivativePublic ∨
                                                      hsame row integralPublic ∨
                                                        hsame row limitPublic) ∧
                                                    UnaryHistory row)
                                                (fun row : BHist =>
                                                  hsame row C ∨ hsame row D ∨
                                                    hsame row I ∨ hsame row L ∨
                                                      hsame row Q ∨ hsame row Y ∨
                                                        hsame row R ∨
                                                          hsame row derivativePublic ∨
                                                            hsame row integralPublic ∨
                                                              hsame row limitPublic)
                                                (fun row : BHist =>
                                                  UnaryHistory row ∧
                                                    Cont C D derivativeRead ∧
                                                      Cont C I integralRead ∧
                                                        Cont C L limitRead ∧
                                                          Cont Q Y dyadicRead ∧
                                                            Cont dyadicRead R realRead ∧
                                                              PkgSig bundle P pkg)
                                                hsame ∧
                                              UnaryHistory derivativeRead ∧
                                                UnaryHistory integralRead ∧
                                                  UnaryHistory limitRead ∧
                                                    UnaryHistory dyadicRead ∧
                                                      UnaryHistory realRead ∧
                                                        UnaryHistory derivativePublic ∧
                                                          UnaryHistory integralPublic ∧
                                                            UnaryHistory limitPublic := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro cUnary dUnary iUnary lUnary qUnary yUnary rUnary nUnary derivativeRoute
    integralRoute limitRoute dyadicRoute realRoute derivativePublicRoute
    integralPublicRoute limitPublicRoute provenancePkg _derivativePkg _integralPkg _limitPkg
  have derivativeUnary : UnaryHistory derivativeRead :=
    unary_cont_closed cUnary dUnary derivativeRoute
  have integralUnary : UnaryHistory integralRead :=
    unary_cont_closed cUnary iUnary integralRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed cUnary lUnary limitRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed qUnary yUnary dyadicRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed dyadicUnary rUnary realRoute
  have derivativePublicUnary : UnaryHistory derivativePublic :=
    unary_cont_closed realUnary nUnary derivativePublicRoute
  have integralPublicUnary : UnaryHistory integralPublic :=
    unary_cont_closed realUnary nUnary integralPublicRoute
  have limitPublicUnary : UnaryHistory limitPublic :=
    unary_cont_closed realUnary nUnary limitPublicRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro derivativePublic
            ⟨Or.inl (hsame_refl derivativePublic), derivativePublicUnary⟩
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
          obtain ⟨sourceEndpoint, sourceUnary⟩ := source
          constructor
          · cases sourceEndpoint with
            | inl derivativeSame =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) derivativeSame)
            | inr remaining =>
                cases remaining with
                | inl integralSame =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) integralSame))
                | inr limitSame =>
                    exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) limitSame))
          · exact unary_transport sourceUnary sameRows
      }
      pattern_sound := by
        intro _row source
        cases source.left with
        | inl derivativeSame =>
            exact
              Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr (Or.inl derivativeSame)))))))
        | inr remaining =>
            cases remaining with
            | inl integralSame =>
                exact
                  Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (Or.inr (Or.inl integralSame))))))))
            | inr limitSame =>
                exact
                  Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (Or.inr (Or.inr limitSame))))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, derivativeRoute, integralRoute, limitRoute, dyadicRoute, realRoute,
            provenancePkg⟩
    }
  · exact
      ⟨derivativeUnary, integralUnary, limitUnary, dyadicUnary, realUnary,
        derivativePublicUnary, integralPublicUnary, limitPublicUnary⟩

end BEDC.Derived.CalculusUp
