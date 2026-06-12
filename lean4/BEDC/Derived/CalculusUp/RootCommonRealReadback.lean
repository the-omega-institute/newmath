import BEDC.Derived.CalculusUp.RootContinuityCompositionLedger

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusRootCommonRealReadback [AskSetup] [PackageSetup]
    {C D I L Q Y R H T P N derivativeRead integralRead limitRead derivativeDyadic
      integralDyadic limitDyadic derivativeSeal integralSeal limitSeal structuralRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory C →
      UnaryHistory D →
        UnaryHistory I →
          UnaryHistory L →
            UnaryHistory Q →
              UnaryHistory Y →
                UnaryHistory R →
                  UnaryHistory H →
                    UnaryHistory T →
                      UnaryHistory N →
                        Cont C D derivativeRead →
                          Cont C I integralRead →
                            Cont C L limitRead →
                              Cont derivativeRead Q derivativeDyadic →
                                Cont integralRead Q integralDyadic →
                                  Cont limitRead Q limitDyadic →
                                    Cont derivativeDyadic R derivativeSeal →
                                      Cont integralDyadic R integralSeal →
                                        Cont limitDyadic R limitSeal →
                                          Cont H T structuralRead →
                                            Cont limitSeal N namedRead →
                                              PkgSig bundle P pkg →
                                                PkgSig bundle N pkg →
                                                  SemanticNameCert
                                                      (fun row : BHist =>
                                                        (hsame row derivativeSeal ∨
                                                            hsame row integralSeal ∨
                                                              hsame row limitSeal ∨
                                                                hsame row namedRead) ∧
                                                          UnaryHistory row)
                                                      (fun row : BHist =>
                                                        hsame row derivativeSeal ∨
                                                          hsame row integralSeal ∨
                                                            hsame row limitSeal ∨
                                                              hsame row namedRead ∨
                                                                hsame row C ∨ hsame row D ∨
                                                                  hsame row I ∨ hsame row L ∨
                                                                    hsame row Q ∨
                                                                      hsame row Y ∨
                                                                        hsame row R ∨
                                                                          hsame row H ∨
                                                                            hsame row T ∨
                                                                              hsame row N ∨
                                                                                hsame row
                                                                                  structuralRead)
                                                      (fun row : BHist =>
                                                        UnaryHistory row ∧
                                                          Cont C D derivativeRead ∧
                                                            Cont C I integralRead ∧
                                                              Cont C L limitRead ∧
                                                                Cont derivativeRead Q
                                                                    derivativeDyadic ∧
                                                                  Cont integralRead Q
                                                                      integralDyadic ∧
                                                                    Cont limitRead Q
                                                                        limitDyadic ∧
                                                                      Cont derivativeDyadic R
                                                                          derivativeSeal ∧
                                                                        Cont integralDyadic R
                                                                            integralSeal ∧
                                                                          Cont limitDyadic R
                                                                              limitSeal ∧
                                                                            Cont H T
                                                                                structuralRead ∧
                                                                              Cont limitSeal N
                                                                                  namedRead ∧
                                                                                PkgSig bundle P
                                                                                    pkg ∧
                                                                                  PkgSig bundle N
                                                                                      pkg)
                                                      hsame ∧
                                                    UnaryHistory derivativeSeal ∧
                                                      UnaryHistory integralSeal ∧
                                                        UnaryHistory limitSeal ∧
                                                          UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro cUnary dUnary iUnary lUnary qUnary _yUnary rUnary hUnary tUnary nUnary
    derivativeRoute integralRoute limitRoute derivativeDyadicRoute integralDyadicRoute
    limitDyadicRoute derivativeSealRoute integralSealRoute limitSealRoute structuralRoute
    namedRoute provenancePkg namedPkg
  have derivativeReadUnary : UnaryHistory derivativeRead :=
    unary_cont_closed cUnary dUnary derivativeRoute
  have integralReadUnary : UnaryHistory integralRead :=
    unary_cont_closed cUnary iUnary integralRoute
  have limitReadUnary : UnaryHistory limitRead :=
    unary_cont_closed cUnary lUnary limitRoute
  have derivativeDyadicUnary : UnaryHistory derivativeDyadic :=
    unary_cont_closed derivativeReadUnary qUnary derivativeDyadicRoute
  have integralDyadicUnary : UnaryHistory integralDyadic :=
    unary_cont_closed integralReadUnary qUnary integralDyadicRoute
  have limitDyadicUnary : UnaryHistory limitDyadic :=
    unary_cont_closed limitReadUnary qUnary limitDyadicRoute
  have derivativeSealUnary : UnaryHistory derivativeSeal :=
    unary_cont_closed derivativeDyadicUnary rUnary derivativeSealRoute
  have integralSealUnary : UnaryHistory integralSeal :=
    unary_cont_closed integralDyadicUnary rUnary integralSealRoute
  have limitSealUnary : UnaryHistory limitSeal :=
    unary_cont_closed limitDyadicUnary rUnary limitSealRoute
  have _structuralUnary : UnaryHistory structuralRead :=
    unary_cont_closed hUnary tUnary structuralRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed limitSealUnary nUnary namedRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro namedRead
            ⟨Or.inr (Or.inr (Or.inr (hsame_refl namedRead))), namedUnary⟩
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
            | inl derivativeSame =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) derivativeSame)
            | inr rest =>
                cases rest with
                | inl integralSame =>
                    exact Or.inr
                      (Or.inl (hsame_trans (hsame_symm sameRows) integralSame))
                | inr rest =>
                    cases rest with
                    | inl limitSame =>
                        exact Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) limitSame)))
                    | inr namedSame =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr (hsame_trans (hsame_symm sameRows) namedSame)))
          · exact unary_transport source.right sameRows
      }
      pattern_sound := by
        intro _row source
        cases source.left with
        | inl derivativeSame =>
            exact Or.inl derivativeSame
        | inr rest =>
            cases rest with
            | inl integralSame =>
                exact Or.inr (Or.inl integralSame)
            | inr rest =>
                cases rest with
                | inl limitSame =>
                    exact Or.inr (Or.inr (Or.inl limitSame))
                | inr namedSame =>
                    exact Or.inr (Or.inr (Or.inr (Or.inl namedSame)))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, derivativeRoute, integralRoute, limitRoute, derivativeDyadicRoute,
            integralDyadicRoute, limitDyadicRoute, derivativeSealRoute, integralSealRoute,
            limitSealRoute, structuralRoute, namedRoute, provenancePkg, namedPkg⟩
    }
  · exact ⟨derivativeSealUnary, integralSealUnary, limitSealUnary, namedUnary⟩

end BEDC.Derived.CalculusUp
